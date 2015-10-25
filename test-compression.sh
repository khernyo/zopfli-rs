#!/bin/bash

set -e

MAX_SIZE=50c
BASE_PATH=.

[ -z $1 -o -z $2 ] && { echo "Usage: $0 <path-to-zopfli> <path-to-zopfli-rs>"; exit 1; }

ZOPFLI=$1
ZOPFLI_RS=$2

TMP_DIR=`mktemp -d zopfli-compression-test-XXXX`


echo "Using temp dir: $TMP_DIR"

function compare_compression() {
    FILE=$1
    echo $FILE

    for format in deflate zlib gzip; do
        F1=$TMP_DIR/`basename $i`.zopfli.$format
        F2=$TMP_DIR/`basename $i`.zopfli-rs.$format
        $ZOPFLI -c $i >$F1
        $ZOPFLI_RS -c $i >$F2
        cmp $F1 $F2 || { echo "$format differs for file $FILE (find outputs in $TMP_DIR)"; exit 1; }
        rm $F1 $F2
    done
}

for i in `find $BASE_PATH -type f -size -$MAX_SIZE -size +0c -readable 2>/dev/null`; do
    compare_compression $i
done
