#!/bin/bash

# directory setup
DIR=$(pwd)
TMPDIR=$(mktemp -d)
trap "{ rm -rf $TMPDIR; }" EXIT
cp . "$TMPDIR" -r

# patch for musl, make and copy binaries
(cd "$TMPDIR" &&
make STATIC=1 &&
cp ceta "$DIR"
)
