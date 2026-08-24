#!/usr/bin/env bash
# c_torture_gate.sh — inch 6's gate, as ONE command.
#
# The pieces (verify the pin offline, run the driver, score the log) are
# three programs with a temp file between them, and a `--gates` string is
# `;`-separated and shell-quoted.  Putting the pipeline in a script rather
# than in the gate string is the same reasoning `tools/triad.sh` uses for
# itself: the protocol is code, not prose a caller retypes.
#
# DEGRADES BY DESIGN.  On a machine with no corpus cache the offline pass
# marks every test `absent`, the driver reports `not-fetched 300`, and the
# number is `0/300` — which is a DIFFERENT zero from "the model refused
# 300", and the summary says which.  That is the point of the state split,
# so the gate is green either way and the LOG carries the distinction.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CACHE="${LS_C_CORPUS_CACHE:-${TMPDIR:-/tmp}/ls-c-torture}"
REV="$(python3 -c "import json;print(json.load(open('$ROOT/docs/c23-suite-census.json'))['corpora']['gcc-torture-exec']['rev'])")"
MANIFEST="$CACHE/$REV/manifest.json"
LOG="${LS_C_TORTURE_LOG:-${TMPDIR:-/tmp}/c-torture-run.log}"
FUEL="${LS_C_TORTURE_FUEL:-64}"

echo "c_torture_gate: pin $REV  cache $CACHE"
python3 "$ROOT/tools/c_corpus_fetch.py" --selftest || exit 1
python3 "$ROOT/harness/c_torture_score.py" --selftest || exit 1
# --offline: verifies every cached file's sha256 against docs/c-torture-pin.json
# and writes the manifest.  No network in a gate, ever.
python3 "$ROOT/tools/c_corpus_fetch.py" --offline --manifest "$MANIFEST" || exit 1
( cd "$ROOT" && lake exe c-torture-run "$MANIFEST" "$FUEL" ) > "$LOG" || exit 1
python3 "$ROOT/harness/c_torture_score.py" "$LOG" || exit 1
echo "c_torture_gate: full log $LOG"
