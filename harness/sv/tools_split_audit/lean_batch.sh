#!/bin/bash
# runs run2 (runner2.lean) on every audit case, ONE slot acquisition for the whole batch
WT=$1; A=$2; shift 2
cd $WT
for c in "$@"; do
  echo "@@@CASE $c"
  if [ -f $A/ext/$c.json ]; then
    timeout 600 lake env lean --run harness/sv/runner2.lean $A/ext/$c.json $A/lean_cases.json $c src 2>&1 | head -40
    echo "@@@RC ${PIPESTATUS[0]}"
  else
    echo "@@@RC noenvelope"
  fi
done
