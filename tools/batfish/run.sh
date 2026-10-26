#!/bin/sh
# (Re)start the Batfish service from the image built by tools/batfish/build.sh.
set -eu
docker rm -f lean-batfish-bf >/dev/null 2>&1 || true
docker run -d --name lean-batfish-bf -p 9996:9996 -p 9997:9997 lean-batfish/allinone:dev
