#!/bin/sh
# Build Batfish from external/batfish and package it as the Docker image
# lean-batfish/allinone:dev. Then (re)start the service with tools/batfish/run.sh.
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
bf="$root/external/batfish"
(cd "$bf" && bazel build //projects/allinone:allinone_main_deploy.jar)
ctx=$(mktemp -d)
trap 'rm -rf "$ctx"' EXIT
cp "$bf/bazel-bin/projects/allinone/allinone_main_deploy.jar" "$ctx/allinone-bundle.jar"
mkdir "$ctx/questions"
cp -R "$bf/questions/stable" "$bf/questions/experimental" "$ctx/questions/"
cp "$root/tools/batfish/Dockerfile" "$ctx/"
docker build -t lean-batfish/allinone:dev "$ctx"
