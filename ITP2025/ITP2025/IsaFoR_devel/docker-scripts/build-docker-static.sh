#!/bin/bash

#config
DOCKERIMAGE="alpine:ceta-build"
SCRIPTDIR=$(dirname "$0")

# User and group ID of current user
if [ "$SUDO_USER" ]; then
    real_user=$SUDO_USER
else
    real_user=$(whoami)
fi
ID=$(id -u "$real_user")
GID=$(id -g "$real_user")

# Build in docker image
docker run --rm \
	-v "$(pwd):/src" \
	-w /src \
	-u "$ID:$GID" \
	"$DOCKERIMAGE" \
	sh "$SCRIPTDIR/build.sh"
