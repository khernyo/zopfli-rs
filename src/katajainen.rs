//! Bounded package merge algorithm, based on the paper
//! "A Fast and Space-Economical Algorithm for Length-Limited Coding
//! Jyrki Katajainen, Alistair Moffat, Andrew Turpin".

use std::cell::RefCell;
use std::mem;
use std::rc::Rc;

use libc::{c_void, size_t};

/// Nodes forming chains. Also used to represent leaves.
struct Node {
    /// Total weight (symbol count) of this chain.
    weight: usize,
    /// Previous node(s) of this chain, or 0 if none.
    tail: Option<Rc<RefCell<Node>>>,
    /// Leaf symbol index, or number of leaves before this chain.
    count: i32,
    /// Tracking for garbage collection.
    in_use: bool,
}

/// Memory pool for nodes.
struct NodePool {
    /// The pool.
    nodes: Vec<Rc<RefCell<Node>>>,
    /// Index of a possibly free node in the pool.
    next: u32,
    /// Size of the memory pool.
    size: u32,
}

impl NodePool {
    fn new(pool_size: u32) -> NodePool {
        NodePool {
            nodes: (0..pool_size).map(|_| {
                let node = Node {
                    weight: 0,
                    tail: None,
                    count: 0,
                    in_use: false,
                };
                Rc::new(RefCell::new(node))
            }).collect(),
            next: 0,
            size: pool_size,
        }
    }
}

/// Initializes a chain node with the given values and marks it as in use.
fn init_node(weight: usize, count: i32, tail: Option<Rc<RefCell<Node>>>, node: Rc<RefCell<Node>>) {
    let mut node = node.borrow_mut();
    node.weight = weight;
    node.count = count;
    node.tail = tail;
    node.in_use = true;
}

/**
 * Finds a free location in the memory pool. Performs garbage collection if needed.
 * lists: If given, used to mark in-use nodes during garbage collection.
 * maxbits: Size of lists.
 * pool: Memory pool to get free node from.
 */
fn get_free_node(lists: Option<&Vec<[Option<Rc<RefCell<Node>>>; 2]>>,
                 maxbits: i32,
                 pool: &mut NodePool)
                 -> Rc<RefCell<Node>> {
    loop {
        if pool.next >= pool.size {
            // Garbage collection
            for i in 0..pool.size {
                pool.nodes[i as usize].borrow_mut().in_use = false;
            }
            if let Some(lists) = lists {
                for i in 0..maxbits * 2 {
                    let mut node = lists[(i / 2) as usize][(i % 2) as usize].clone();
                    while let Some(n) = node {
                        let mut n = n.borrow_mut();
                        n.in_use = true;
                        node = n.tail.clone();
                    }
                }
            }
            pool.next = 0;
        }
        if !pool.nodes[pool.next as usize].borrow().in_use {
            break;
        }
        pool.next += 1;
    }
    let free_node = pool.nodes[pool.next as usize].clone();

    pool.next += 1;
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
fn boundary_pm(lists: &mut Vec<[Option<Rc<RefCell<Node>>>; 2]>,
               maxbits: i32,
               leaves: &[Node],
               numsymbols: i32,
               pool: &mut NodePool,
               index: i32,
               is_final: bool) {
    let lastcount = lists[index as usize][1].as_ref().unwrap().borrow().count; // Count of last chain of list.

    if index == 0 && lastcount >= numsymbols {
        return;
    }

    let newchain = get_free_node(Some(&lists), maxbits, pool);
    let oldchain = lists[index as usize][1].clone();

    // These are set up before the recursive calls below, so that there is a list
    // pointing to the new node, to let the garbage collection know it's in use.
    lists[index as usize][0] = oldchain.clone();
    lists[index as usize][1] = Some(newchain.clone());

    if index == 0 {
        // New leaf node in list 0.
        init_node(leaves[lastcount as usize].weight,
                  lastcount + 1,
                  None,
                  newchain);
    } else {
        let sum = lists[(index - 1) as usize][0].as_ref().unwrap().borrow().weight +
                  lists[(index - 1) as usize][1].as_ref().unwrap().borrow().weight;
        if lastcount < numsymbols && sum > leaves[lastcount as usize].weight {
            // New leaf inserted in list, so count is incremented.
            init_node(leaves[lastcount as usize].weight,
                      lastcount + 1,
                      oldchain.as_ref().unwrap().borrow().tail.clone(),
                      newchain);
        } else {
            init_node(sum,
                      lastcount,
                      lists[(index - 1) as usize][1].clone(),
                      newchain);
            if !is_final {
                // Two lookahead chains of previous list used up, create new ones.
                boundary_pm(lists, maxbits, leaves, numsymbols, pool, index - 1, false);
                boundary_pm(lists, maxbits, leaves, numsymbols, pool, index - 1, false);
            }
        }
    }
}

/// Initializes each list with as lookahead chains the two leaves with lowest weights.
fn init_lists(pool: &mut NodePool,
              leaves: &[Node],
              maxbits: i32) -> Vec<[Option<Rc<RefCell<Node>>>; 2]> {
    let node0 = get_free_node(None, maxbits, pool);
    let node1 = get_free_node(None, maxbits, pool);
    init_node(leaves[0].weight, 1, None, node0.clone());
    init_node(leaves[1].weight, 2, None, node1.clone());
    let mut result = Vec::new();
    for _ in 0..maxbits {
        result.push([Some(node0.clone()), Some(node1.clone())]);
    }
    result
}

/**
 * Converts result of boundary package-merge to the bitlengths. The result in the
 * last chain of the last list contains the amount of active leaves in each list.
 * chain: Chain to extract the bit length from (last chain from last list).
 */
fn extract_bit_lengths(chain: Option<Rc<RefCell<Node>>>, leaves: &[Node], bitlengths: &mut [u32]) {
    let mut node = chain;
    while let Some(n) = node {
        for i in 0..n.borrow().count {
            bitlengths[leaves[i as usize].count as usize] =
                bitlengths[leaves[i as usize].count as usize] + 1;
        }
        node = n.borrow().tail.clone();
    }
}

/// Comparator for sorting the leaves. Has the function signature for qsort.
extern "C" fn leaf_comparator(a: *const c_void, b: *const c_void) -> i32 {
    unsafe {
        let node_a: *const Node = a as *const Node;
        let node_b: *const Node = b as *const Node;
        (*node_a).weight as i32 - (*node_b).weight as i32
    }
}

#[link(name="c")]
extern {
    fn qsort(base: *mut c_void,
             nmemb: size_t,
             size: size_t,
             compar: extern "C" fn(*const c_void, *const c_void) -> i32);
}

pub fn length_limited_code_lengths(frequencies: &[usize],
                                   n: i32,
                                   maxbits: i32,
                                   bitlengths: &mut [u32])
                                   -> bool {
    // One leaf per symbol. Only numsymbols leaves will be used.
    let mut leaves: Vec<Node> = Vec::with_capacity(n as usize);

    // Initialize all bitlengths at 0.
    for i in 0..n {
        bitlengths[i as usize] = 0;
    }

    // Count used symbols and place them in the leaves.
    for i in 0..n {
        if frequencies[i as usize] != 0 {
            leaves.push(Node {
                weight: frequencies[i as usize],
                count: i, // Index of symbol this leaf represents.
                tail: None,
                in_use: false,
            });
        }
    }
    // Amount of symbols with frequency > 0.
    let numsymbols = leaves.len();

    // Check special cases and error conditions.
    if (1 << maxbits) < numsymbols {
        return true; // Error, too few maxbits to represent symbols.
    }
    if numsymbols == 0 {
        return false; // No symbols at all. OK.
    }
    if numsymbols == 1 {
        bitlengths[leaves[0].count as usize] = 1;
        return false; // Only one symbol, give it bitlength 1, not 0. OK.
    }

    // Sort the leaves from lightest to heaviest.
    unsafe {
        qsort(leaves.as_mut_ptr() as *mut c_void,
            numsymbols as size_t,
            mem::size_of::<Node>() as size_t,
            leaf_comparator);
    }

    // Initialize node memory pool.
    let mut pool = NodePool::new(2 * maxbits as u32 * (maxbits as u32 + 1));

    // Array of lists of chains. Each list requires only two lookahead chains at
    // a time, so each list is a array of two Node*'s.
    let mut lists: Vec<[Option<Rc<RefCell<Node>>>; 2]> = init_lists(&mut pool, &leaves, maxbits);

    // In the last list, 2 * numsymbols - 2 active chains need to be created. Two
    // are already created in the initialization. Each BoundaryPM run creates one.
    let num_boundary_pm_runs = 2 * numsymbols - 4;
    for i in 0..num_boundary_pm_runs {
        let is_final = i == num_boundary_pm_runs - 1;
        boundary_pm(&mut lists,
                    maxbits,
                    &leaves,
                    numsymbols as i32,
                    &mut pool,
                    maxbits - 1,
                    is_final);
    }

    extract_bit_lengths(lists[maxbits as usize - 1][1].clone(), &leaves, bitlengths);
    false // OK.
}

#[cfg(test)]
mod tests {
    use std::mem::size_of;
    use libc::{c_void, size_t};

    use super::qsort;

    extern "C" fn comparator(a: *const c_void, b: *const c_void) -> i32 {
        unsafe { *(a as *const i32) - *(b as *const i32) }
    }

    #[test]
    fn test_qsort() {
        unsafe {
            let mut a: [i32; 5] = [3, 2, 4, 1, 5];
            qsort(a.as_mut_ptr() as *mut c_void,
                  a.len() as size_t,
                  size_of::<i32>() as size_t,
                  comparator);
            assert_eq!(a, [1, 2, 3, 4, 5]);
        }
    }
}
