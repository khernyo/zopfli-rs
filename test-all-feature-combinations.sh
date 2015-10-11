#!/bin/bash

set -e

export RUST_BACKTRACE=1

ALL_FEATURES=(longest-match-cache hash-same hash-same-hash shortcut-long-repetitions lazy-matching)

(( LIMIT = (1 << ${#ALL_FEATURES[@]}) - 1))
for i in `seq 0 $LIMIT`; do
    unset FEATURES
    declare -a FEATURES
    for f in `seq 0 $(expr ${#ALL_FEATURES[@]} - 1)`; do
        (( USE = ($i & (1 << $f)) )) || true
        if [ $USE -gt 0 ]; then
            FEATURES+=(${ALL_FEATURES[$f]})
        fi
    done
    echo "Using features: ${FEATURES[@]}"
    echo "=============="
    cargo build --verbose --no-default-features --features "`echo ${FEATURES[@]}`"
    cargo test --verbose --no-default-features --features "`echo ${FEATURES[@]}`"
done
