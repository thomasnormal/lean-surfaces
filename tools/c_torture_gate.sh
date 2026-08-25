#!/usr/bin/env bash
# c_torture_gate.sh — inch 6's gate, as ONE command.
#
# The pieces (verify the pin offline, run the driver, score the log) are
# several programs with a temp file between them, and a `--gates` string is
# `;`-separated and shell-quoted.  Putting the pipeline in a script rather
# than in the gate string is the same reasoning `tools/triad.sh` uses for
# itself: the protocol is code, not prose a caller retypes.
#
# DEGRADES BY DESIGN.  On a machine with no corpus cache the offline pass
# marks every test `absent`, the driver reports `not-fetched 300`, and the
# number is `0/300` — which is a DIFFERENT zero from "the model refused
# 300", and the summary says which.  That is the point of the state split,
# so the gate is green either way and the LOG carries the distinction.
#
# THE DIVERGENCE REGISTER RUNS HERE, and it should have from the start.
# `harness/divergence_register.py` was in other tiers' floors and not in
# this lane's, so no C tenure could ever contradict the C rows — and two
# malformed ones reached master and went red on everybody else's floor
# (2026-08-25-c-24).  That is this lane's own corpus law arriving one layer
# up: A GATE CAN ONLY CONTRADICT THE FILES IT RUNS ON.  It is checked
# before the expensive half, so a malformed row costs seconds, not a build.
# It is kept even though the C tier declares NO LIVE divergence: this lane
# broke the fleet once by not running a shared checker, and "we have no rows
# today" is exactly the reasoning that let it happen.  The tier's own probe
# runs beside it, and with zero live rows its `rc` comes entirely from the
# RETIRED-ROW REGRESSION ALARM — a divergence coming back is the only thing
# it can report, which is the whole job of an archive that is still watched
# (2026-08-26-c-27).
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CACHE="${LS_C_CORPUS_CACHE:-${TMPDIR:-/tmp}/ls-c-torture}"
REV="$(python3 -c "import json;print(json.load(open('$ROOT/docs/c23-suite-census.json'))['corpora']['gcc-torture-exec']['rev'])")"
MANIFEST="$CACHE/$REV/manifest.json"
LOG="${LS_C_TORTURE_LOG:-${TMPDIR:-/tmp}/c-torture-run.log}"
FUEL="${LS_C_TORTURE_FUEL:-64}"
SB="$ROOT/docs/c-torture-scoreboard.json"
FRESH="${TMPDIR:-/tmp}/c-torture-scoreboard.fresh.json"

echo "c_torture_gate: pin $REV  cache $CACHE"
python3 "$ROOT/tools/c_corpus_fetch.py" --selftest || exit 1
python3 "$ROOT/harness/c_torture_score.py" --selftest || exit 1
python3 "$ROOT/extractors/c/extract.py" --selftest || exit 1
python3 "$ROOT/harness/divergence_register.py" || exit 1
python3 "$ROOT/harness/c_divergence_probe.py" || exit 1
# --offline: verifies every cached file's sha256 against docs/c-torture-pin.json
# and writes the manifest.  No network in a gate, ever.
python3 "$ROOT/tools/c_corpus_fetch.py" --offline --manifest "$MANIFEST" || exit 1
( cd "$ROOT" && lake exe c-torture-run "$MANIFEST" "$FUEL" ) > "$LOG" || exit 1
python3 "$ROOT/harness/c_torture_score.py" "$LOG" --emit "$FRESH" || exit 1

# THE PUBLISHED NUMBER IS A SECOND ARTIFACT (qol-21's law).  Correcting the
# instrument corrects the NEXT run; the committed figure is corrected where
# it was published, or it stands and is wrong.  Compared only when this
# machine actually HAS the corpus — on a bare machine the fresh run is all
# `not-fetched`, and failing there would punish a lane for not holding a
# GPL cache it is forbidden to vendor.
python3 - "$SB" "$FRESH" <<'PY' || exit 1
import json, sys
sb, fresh = (json.load(open(p)) for p in sys.argv[1:3])
if fresh["counts"]["not-fetched"] == fresh["total"]:
    print("c_torture_gate: no corpus on this machine — committed scoreboard NOT compared "
          "(all %d not-fetched, which is the designed degradation)" % fresh["total"])
    raise SystemExit(0)
if sb.get("counts") != fresh.get("counts") or sb.get("failed_tests") != fresh.get("failed_tests"):
    print("c_torture_gate: THE COMMITTED SCOREBOARD IS STALE.\n"
          "  committed: %s failed=%s\n  fresh:     %s failed=%s\n"
          "  Re-emit it (c_torture_score.py <log> --emit docs/c-torture-scoreboard.json) "
          "and say in the landing what moved. A number published in docs is a second "
          "artifact and is corrected where it was published." %
          (sb.get("counts"), sb.get("failed_tests"),
           fresh.get("counts"), fresh.get("failed_tests")), file=sys.stderr)
    raise SystemExit(1)
print("c_torture_gate: committed scoreboard matches this run (%d/%d scored)"
      % (fresh["scored"], fresh["total"]))
PY
# AND THE MEMBERSHIP OF `oracle-tests-compiler` IS PINNED HERE.  The state is
# not a divergence -- it is part of what the number MEANS -- so it is gated by
# the tenure rather than by the divergence register, which would file a
# permanent property as a debt.  Two locks: this list, and the declare-call-
# define SHAPE that LeanModels/C/Torture.lean re-derives per test.
python3 - "$ROOT/docs/c-torture-pin.json" "$FRESH" <<'PY' || exit 1
import json, sys
pin, fresh = (json.load(open(p)) for p in sys.argv[1:3])
if fresh["counts"]["not-fetched"] == fresh["total"]:
    raise SystemExit(0)
want = sorted((pin.get("oracle_tests_compiler") or {}).keys())
got = sorted(fresh.get("oracle_tests_compiler_tests") or [])
if want != got:
    print("c_torture_gate: THE oracle-tests-compiler MEMBERSHIP MOVED.\n"
          "  pinned: %r\n  scored: %r\n"
          "  Membership is by NAME in tools/c_corpus_fetch.py with a citation, and the "
          "SHAPE is re-derived per test by LeanModels/C/Torture.lean. A test entering or "
          "leaving this state without the pin changing is the state being used to move a "
          "number, which is the failure the named state exists to prevent."
          % (want, got), file=sys.stderr)
    raise SystemExit(1)
print("c_torture_gate: oracle-tests-compiler membership matches the pin: %r" % got)
PY
echo "c_torture_gate: full log $LOG"
