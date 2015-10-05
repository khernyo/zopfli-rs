/*!
 * Bounded package merge algorithm, based on the paper
 * "A Fast and Space-Economical Algorithm for Length-Limited Coding
 * Jyrki Katajainen, Alistair Moffat, Andrew Turpin".
 */

use std::mem;
use std::ptr::{null, null_mut};

use libc::{c_void, size_t};
use libc::funcs::c95::stdlib::{free, malloc};

/// Nodes forming chains. Also used to represent leaves.
struct Node {
    /// Total weight (symbol count) of this chain.
    weight: usize,
    /// Previous node(s) of this chain, or 0 if none.
    tail: *mut Node,
    /// Leaf symbol index, or number of leaves before this chain.
    count: i32,
    /// Tracking for garbage collection.
    in_use: bool,
}

/// Memory pool for nodes.
struct NodePool {
    /// The pool.
    nodes: *mut Node,
    /// Pointer to a possibly free node in the pool.
    next: *mut Node,
    /// Size of the memory pool.
    size: u32,
}

/// Initializes a chain node with the given values and marks it as in use.
unsafe fn init_node(weight: usize, count: i32, tail: *mut Node, node: *mut Node) {
    (*node).weight = weight;
    (*node).count = count;
    (*node).tail = tail;
    (*node).in_use = true;
}

/**
 * Finds a free location in the memory pool. Performs garbage collection if needed.
 * lists: If given, used to mark in-use nodes during garbage collection.
 * maxbits: Size of lists.
 * pool: Memory pool to get free node from.
 */
unsafe fn get_free_node(lists: *const *mut *mut Node, maxbits: i32, pool: *mut NodePool) -> *mut Node {
    loop {
        if (*pool).next >= (*pool).nodes.offset((*pool).size as isize) {
            // Garbage collection
            for i in 0..(*pool).size {
                (*(*pool).nodes.offset(i as isize)).in_use = false;
            }
            if lists != null_mut() {
                for i in 0..maxbits*2 {
                    let mut node = *(*lists.offset((i / 2) as isize)).offset((i % 2) as isize);
                    while (node != null_mut()) {
                        (*node).in_use = true;
                        node = (*node).tail;
                    }
                }
            }
            (*pool).next = (*pool).nodes;
        }
        if (*(*pool).next).in_use {
            break;
        }
        (*pool).next = (*pool).next.offset(1);
    }
    let free_node = (*pool).next;
    (*pool).next = (*pool).next.offset(1);
    free_node
}

/**
 * Performs a Boundary Package-Merge step. Puts a new chain in the given list. The
 * new chain is, depending on the weights, a leaf or a combination of two chains
 * from the previous list.
 * lists: The lists of chains.
 * maxbits: Number of lists.
 * leaves: The leaves, one per symbol.
 * numsymbols: Number of leaves.
 * pool: the node memory pool.
 * index: The index of the list in which a new chain or leaf is required.
 * final: Whether this is the last time this function is called. If it is then it
 *   is no more needed to recursively call self.
 */
unsafe fn boundary_pm(lists: *const *mut *mut Node, maxbits: i32, leaves: *const Node, numsymbols: i32, pool: *mut NodePool,
                      index: i32, is_final: bool) {
    let lastcount = (**(*lists.offset(index as isize)).offset(1)).count; // Count of last chain of list.

    if index == 0 && lastcount >= numsymbols {
        return;
    }

    let newchain = get_free_node(lists, maxbits, pool);
    let oldchain = *(*lists.offset(index as isize)).offset(1);

    // These are set up before the recursive calls below, so that there is a list
    // pointing to the new node, to let the garbage collection know it's in use.
    *(*lists.offset(index as isize)).offset(0) = oldchain;
    *(*lists.offset(index as isize)).offset(1) = newchain;

    if index == 0 {
        //New leaf node in list 0.
        init_node((*leaves.offset(lastcount as isize)).weight, lastcount + 1, null_mut(), newchain);
    } else {
        let sum = (**(*lists.offset((index - 1) as isize)).offset(0)).weight + (**(*lists.offset((index - 1) as isize)).offset(0)).weight;
        if lastcount < numsymbols && sum > (*leaves.offset(lastcount as isize)).weight {
            // New leaf inserted in list, so count is incremented.
            init_node((*leaves.offset(lastcount as isize)).weight, lastcount + 1, (*oldchain).tail, newchain);
        } else {
            init_node(sum, lastcount, *(*lists.offset((index - 1) as isize)).offset(1), newchain);
            if (!is_final) {
                // Two lookahead chains of previous list used up, create new ones.
                boundary_pm(lists, maxbits, leaves, numsymbols, pool, index - 1, false);
                boundary_pm(lists, maxbits, leaves, numsymbols, pool, index - 1, false);
            }
        }
    }
}

/// Initializes each list with as lookahead chains the two leaves with lowest weights.
unsafe fn init_lists(pool: *mut NodePool, leaves: *const Node, maxbits: i32, lists: *const *mut *mut Node) {
    let node0 = get_free_node(null(), maxbits, pool);
    let node1 = get_free_node(null(), maxbits, pool);
    init_node((*leaves.offset(0)).weight, 1, null_mut(), node0);
    init_node((*leaves.offset(1)).weight, 2, null_mut(), node1);
    for i in 0..maxbits {
        *(*lists.offset(i as isize)).offset(0) = node0;
        *(*lists.offset(i as isize)).offset(1) = node1;
    }
}

/**
 * Converts result of boundary package-merge to the bitlengths. The result in the
 * last chain of the last list contains the amount of active leaves in each list.
 * chain: Chain to extract the bit length from (last chain from last list).
 */
unsafe fn extract_bit_lengths(chain: *const Node, leaves: *const Node, bitlengths: *mut u32) {
    let mut node = chain;
    while node != null() {
        for i in 0..(*node).count {
            *bitlengths.offset((*leaves.offset(i as isize)).count as isize) = *bitlengths.offset((*leaves.offset(i as isize)).count as isize) + 1;
        }
        node = (*node).tail;
    }
}

/// Comparator for sorting the leaves. Has the function signature for qsort.
unsafe fn leaf_comparator(a: *const c_void, b: *const c_void) -> i32 {
    let node_a: *const Node = mem::transmute(a);
    let node_b: *const Node = mem::transmute(b);
    (*node_a).weight as i32 - (*node_b).weight as i32
}

#[link(name="c")]
extern {
    fn qsort(base: *mut c_void, nmemb: size_t, size: size_t, compar: extern fn(*const c_void, *const c_void, *const c_void) -> i32);
}

unsafe fn zopfli_length_limited_code_lengths(frequencies: *const usize, n: i32, maxbits: i32, bitlengths: *mut u32) -> i32 {
    // Amount of symbols with frequency > 0.
    let mut numsymbols = 0;

    // One leaf per symbol. Only numsymbols leaves will be used.
    let leaves: *mut Node = mem::transmute(malloc((n as usize * mem::size_of::<Node>()) as size_t));

    // Initialize all bitlengths at 0.
    for i in 0..n {
        *bitlengths.offset(i as isize) = 0;
    }

    // Count used symbols and place them in the leaves.
    for i in 0..n {
        if *frequencies.offset(i as isize) != 0 {
            (*leaves.offset(numsymbols)).weight = *frequencies.offset(i as isize);
            (*leaves.offset(numsymbols)).count = i;
            numsymbols = numsymbols + 1;
        }
    }

    // Check special cases and error conditions.
    if (1 << maxbits) < numsymbols {
        free(mem::transmute(leaves));
        return 1; // Error, too few maxbits to represent symbols.
    }
    if numsymbols == 0 {
        free(mem::transmute(leaves));
        return 0; // No symbols at all. OK.
    }
    if numsymbols == 1 {
        *bitlengths.offset((*leaves.offset(0)).count as isize) = 1;
        free(mem::transmute(leaves));
        return 0; // Only one symbol, give it bitlength 1, not 0. OK.
    }

    // Sort the leaves from lightest to heaviest.
    qsort(mem::transmute(leaves), numsymbols as size_t, mem::size_of::<Node>() as size_t, mem::transmute(&leaf_comparator));

    // Initialize node memory pool.
    let pool_size = 2 * maxbits * (maxbits + 1);
    let pool_nodes = mem::transmute(malloc((pool_size as usize * mem::size_of::<Node>()) as size_t));
    let mut pool = NodePool { size: pool_size as u32, nodes: pool_nodes, next: pool_nodes };
    for i in 0..pool.size {
        (*pool.nodes.offset(i as isize)).in_use = false;
    }

    // Array of lists of chains. Each list requires only two lookahead chains at
    // a time, so each list is a array of two Node*'s.
    let lists: *const *mut *mut Node = mem::transmute(malloc((maxbits as usize * mem::size_of::<*const *const Node>()) as size_t));
    init_lists(&mut pool, leaves, maxbits, lists);

    // In the last list, 2 * numsymbols - 2 active chains need to be created. Two
    // are already created in the initialization. Each BoundaryPM run creates one.
    let num_boundary_pm_runs = 2 * numsymbols - 4;
    for i in 0..num_boundary_pm_runs {
        let is_final = i == num_boundary_pm_runs - 1;
        boundary_pm(lists, maxbits, leaves, numsymbols as i32, &mut pool, maxbits - 1, is_final);
    }

    extract_bit_lengths(*(*lists.offset(maxbits as isize - 1)).offset(1), leaves, bitlengths);

    free(mem::transmute(lists));
    free(mem::transmute(leaves));
    free(mem::transmute(pool.nodes));
    0
}
