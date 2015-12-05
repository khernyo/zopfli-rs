#!/bin/bash

set -e

[ -z $1 ] && { echo "Usage: $0 <path-to-zopfli>"; exit 1; }

ZOPFLI=$1
ZOPFLI_RS_DEBUG=./target/debug/examples/zopfli
ZOPFLI_RS_RELEASE=./target/release/examples/zopfli

cargo build
cargo build --release
cargo test
cargo test --release

./test-compression.sh $ZOPFLI $ZOPFLI_RS_DEBUG
./test-compression.sh $ZOPFLI $ZOPFLI_RS_RELEASE

valgrind $ZOPFLI -c LICENSE.txt >/dev/null
valgrind $ZOPFLI_RS_RELEASE -c LICENSE.txt >/dev/null

time $ZOPFLI -c ./target/debug/zopfli-* >/dev/null
time $ZOPFLI_RS_RELEASE -c ./target/debug/zopfli-* >/dev/null
