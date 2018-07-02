#!/bin/bash

set -e

if test -z "$DEBIAN_VERSION"; then
    DEBIAN_VERSION="stable"
fi

autoconf && (automake --add-missing 2> /dev/null || true)
if test "$DEBIAN_VERSION" != "stable" -o -n "$DEBIAN_PACKAGES" -o -n "$OPAM_PACKAGES"; then
  IMAGE=bench-image-$COMPILER--"$DEBIAN_VERSION"--$(echo $DEBIAN_PACKAGES | sed -e 's/ /--/g')--$(echo $OPAM_PACKAGES | sed -e 's/ /--/g')
else
  IMAGE=bench-image-$COMPILER
fi

docker build -t $IMAGE --force-rm -f misc/Dockerfile.init --build-arg debian_version="$DEBIAN_VERSION" --build-arg compiler=$COMPILER --build-arg debian_packages="$DEBIAN_PACKAGES" --build-arg opam_packages="$OPAM_PACKAGES" .
CID=$(docker create --rm -i -w /home/why3/why3 $IMAGE /bin/sh)
docker start $CID
docker cp . $CID:/home/why3/why3
docker exec -u root $CID chown -R why3:why3 /home/why3/why3
docker attach $CID <<EOF
exec $@
EOF
