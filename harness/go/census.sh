#!/usr/bin/env bash
# census.sh — build harness/go/construct_census.go, then run it.
#
# The build is not a convenience: `go run` swallows the program's exit
# code (it prints "exit status N" and itself exits 1), and this
# instrument carries its entire refusal taxonomy in that code — 2 no
# such path, 3 does not parse, 4 zero nodes, 5 --compare differs. Under
# `go run` all four would read as 1, which is exactly the kind of silent
# wrong answer the exit-code convention exists to prevent.
#
# Usage: harness/go/census.sh [args...]   (args go straight to the tool)
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bin="$(mktemp -d)/go_construct_census"
trap 'rm -rf "$(dirname "$bin")"' EXIT

go build -o "$bin" "$here/construct_census.go"
"$bin" "$@"
