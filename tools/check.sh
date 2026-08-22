#!/usr/bin/env bash
# tools/check.sh — ONE file, elaborated against a WARM clone's oleans.
#
# WHY THIS FILE EXISTS.  The edit-check loop is the proof writer's inner loop,
# and the only cheap way to run it is `lake env lean` on a single file against
# oleans somebody else already built.  §7.1 rule 3 allows exactly that — and
# then amends itself, because a lane got it wrong in the obvious way:
#
#   "AND ONLY IN A WARM CLONE — THE EXEMPTION IS A PROPERTY OF THE CLONE, NOT
#    OF THE FILE.  `lake env lean` on a dependency-free scratch file is cheap
#    only where the dependencies are already resolved; in a COLD clone the
#    same command resolves and downloads them, which is Lean execution
#    outside the lock (A11) and a GB-scale download instead of CoW seeding
#    (A13).  This lane made exactly that mistake, reading rule 3 as being
#    about the file when it is about the clone."
#
# A rule whose precondition cannot be seen is a rule that gets guessed.  So
# this script does not ask the lane to know whether the clone is warm: it
# CHECKS, names the case it found, and refuses when the case is not one rule 3
# covers.  Three cases, and the script always says which one it is in:
#
#   TENURE    — the build lock's owner pid is US or one of our ancestors.
#               Anything goes; we are inside a ticket (A11).
#   SCRATCH   — the target is outside every lake library glob AND every
#               project import already has an olean.  Rule 3's exemption,
#               with its warm-clone amendment CHECKED rather than assumed.
#   REFUSE    — anything else, and it says which: a library-glob file (that
#               is the build's own graph — take a ticket), or a cold clone
#               (seed first per A13, then probe).
#
# The lake libraries are READ FROM lakefile.toml, not hardcoded here — a
# hardcoded glob is a second copy of the lakefile that goes stale silently.
#
# USAGE
#   tools/check.sh path/to/file.lean        # decide, then elaborate
#   tools/check.sh --explain path/to/f.lean # decide and PRINT, run nothing
#   tools/check.sh --self-test              # every refusal path RUN, no Lean
#
# EXIT  0 elaborated clean (or --explain)   1 Lean reported errors
#       2 REFUSED — nothing was run
#
# Core modules (`Init`, `Std`, `Lean`, `Lake`) ship with the toolchain and are
# NOT olean-checked here; probing them would mean starting a Lean process to
# ask where they live, and that is the thing this script exists to gate.

set -u

CLONE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOCK="${LS_LOCK:-/tmp/ls-build.lock}"
NICE="${LS_NICE:-19}"
EXPLAIN=0
SELF_TEST=0
TARGET=""

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
die()   { echo "check.sh: $*" >&2; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --dir)       CLONE="${2:-}"; shift 2 ;;
    --explain)   EXPLAIN=1; shift ;;
    --self-test) SELF_TEST=1; shift ;;
    -h|--help)   usage ;;
    -*)          die "unknown argument '$1'" ;;
    *)           TARGET="$1"; shift ;;
  esac
done

# ------------------------------------------------------------- the lakefile
# "Check, don't assume" — the library roots come from lakefile.toml.
lake_lib_roots() {              # -> one library/exe root name per line
  local f="$CLONE/lakefile.toml"
  [ -f "$f" ] || return 0
  awk '
    /^\[\[lean_lib\]\]/  { sec = "lib"; next }
    /^\[\[lean_exe\]\]/  { sec = "exe"; next }
    /^\[\[/              { sec = "";    next }
    sec == "lib" && /^[ \t]*name[ \t]*=/ { print val($0); next }
    sec == "exe" && /^[ \t]*root[ \t]*=/ { print val($0); next }
    function val(l) { sub(/^[^=]*=[ \t]*/, "", l); gsub(/["\047 \t\r]/, "", l); return l }
  ' "$f"
}

glob_class() {                  # repo-relative path -> library | scratch
  local p="$1" root top
  for root in $(lake_lib_roots); do
    top="${root%%.*}"           # `LeanModels.Circuit.DCRunner` -> `LeanModels`
    [ -n "$top" ] || continue
    case "$p" in
      "$top".lean|"$top"/*) echo library; return 0 ;;
    esac
  done
  echo scratch
}

# ---------------------------------------------------------------- imports
imports_of() {                  # file -> imported module names, one per line
  sed -n 's/^[ \t]*import[ \t][ \t]*\([A-Za-z0-9_.«»]*\).*/\1/p' "$1"
}

is_core_module() {              # toolchain-provided: not our olean to check
  case "${1%%.*}" in Init|Std|Lean|Lake) return 0 ;; *) return 1 ;; esac
}

olean_for() {                   # module -> olean path, or '' when absent
  local rel c
  rel="$(printf '%s' "$1" | sed 's/[«»]//g' | tr '.' '/')"
  for c in "$CLONE/.lake/build/lib/lean/$rel.olean" \
           "$CLONE"/.lake/packages/*/.lake/build/lib/lean/"$rel".olean; do
    [ -f "$c" ] && { echo "$c"; return 0; }
  done
  echo ""; return 1
}

missing_oleans() {              # file -> project imports with no olean
  local m
  for m in $(imports_of "$1"); do
    is_core_module "$m" && continue
    [ -n "$(olean_for "$m")" ] || echo "$m"
  done
}

# ------------------------------------------------------------ the tenure
# A5: the owner file is `<lane> <pid>`, pid LAST.  A4's corollary: the owner
# is a HINT and the process tree is the truth — so ownership is decided by
# ANCESTRY, not by matching a lane tag a stale file could be lying about.
lock_is_ours() {
  local owner pid p guard=0
  owner="$(cat "$LOCK/owner" 2>/dev/null)" || return 1
  [ -n "$owner" ] || return 1
  pid="$(printf '%s' "$owner" | awk '{print $NF}')"
  case "$pid" in ''|*[!0-9]*) return 1 ;; esac
  p=$$
  while [ -n "$p" ] && [ "$p" != "0" ] && [ "$p" != "1" ]; do
    [ "$p" = "$pid" ] && return 0
    guard=$((guard + 1)); [ "$guard" -gt 64 ] && return 1
    p="$(ps -o ppid= -p "$p" 2>/dev/null | tr -d ' ')"
  done
  return 1
}

# ------------------------------------------------------------- the verdict
# Sets VERDICT (tenure|scratch|refuse-library|refuse-cold) and WHY.
VERDICT=""; WHY=""; MISSING=""
decide() {                      # decide <repo-relative-path>
  local cls
  VERDICT=""; WHY=""; MISSING=""
  if lock_is_ours; then
    VERDICT="tenure"
    WHY="the build lock's owner pid ($(awk '{print $NF}' "$LOCK/owner" 2>/dev/null)) is us or an ancestor — we are inside a ticket (A11)"
    return 0
  fi
  cls="$(glob_class "$1")"
  if [ "$cls" = "library" ]; then
    VERDICT="refuse-library"
    WHY="'$1' is inside a lake library glob — that is the build's own graph, not a scratch file. Rule 3's exemption does not cover it: take a ticket (tools/triad.sh --lane <you>)"
    return 0
  fi
  MISSING="$(missing_oleans "$CLONE/$1" 2>/dev/null || true)"
  if [ -n "$MISSING" ]; then
    VERDICT="refuse-cold"
    WHY="this clone is COLD for $(printf '%s\n' "$MISSING" | grep -c .) of the file's imports. Running it here would RESOLVE AND DOWNLOAD them — Lean execution outside the lock (A11) and a GB-scale download instead of CoW seeding (A13). Seed first (A13), then probe"
    return 0
  fi
  VERDICT="scratch"
  WHY="'$1' is outside every lake library glob and every project import already has an olean — rule 3's exemption, warm-clone amendment CHECKED"
  return 0
}

# --------------------------------------------------------------- self-test
# §5.4's law: every refusal path RUN, not admired.  NO LEAN IS EXECUTED here
# — the whole point of the script is the decision, and the decision is pure.
if [ "$SELF_TEST" = "1" ]; then
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/check-selftest.XXXXXX")" || die "no temp dir"
  trap 'rm -rf "$tmp"' EXIT
  ok=0; bad=0
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; \
            else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }

  # A clone with the same SHAPE as the real one: a lakefile naming two libs
  # and an exe root, a build tree with one olean, and files in both classes.
  fake="$tmp/clone"
  mkdir -p "$fake/LeanModels/Core" "$fake/Examples/python/x" "$fake/scratch" \
           "$fake/.lake/build/lib/lean/LeanModels/Core" \
           "$fake/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib"
  cat > "$fake/lakefile.toml" <<'TOML'
name = "lean-models"
defaultTargets = ["LeanModels", "Examples"]
[[lean_lib]]
name = "LeanModels"
[[lean_lib]]
name = "Examples"
globs = ["Examples.+"]
[[lean_exe]]
name = "leanmodels-run"
root = "Main"
TOML
  : > "$fake/.lake/build/lib/lean/LeanModels/Core/Basic.olean"
  : > "$fake/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
  printf 'import LeanModels.Core.Basic\nimport Std.Do.Triple\n' > "$fake/scratch/warm.lean"
  printf 'import LeanModels.Core.Basic\nimport LeanModels.Python.Semantics\n' > "$fake/scratch/cold.lean"
  printf 'import Mathlib.Tactic\n' > "$fake/scratch/pkg.lean"
  printf 'import LeanModels.Core.Basic\n' > "$fake/LeanModels/Core/New.lean"
  printf 'import LeanModels.Core.Basic\n' > "$fake/Examples/python/x/proof.lean"
  CLONE="$fake"
  export LS_LOCK="$tmp/lock"; LOCK="$LS_LOCK"

  check "the lakefile's libs are READ, not hardcoded" \
        "$(lake_lib_roots | tr '\n' ' ' | sed 's/ *$//')" "LeanModels Examples Main"
  check "a LeanModels path is library-class"  "$(glob_class LeanModels/Core/New.lean)" "library"
  check "an Examples path is library-class"   "$(glob_class Examples/python/x/proof.lean)" "library"
  check "the exe root is library-class"       "$(glob_class Main.lean)" "library"
  check "a scratch path is scratch-class"     "$(glob_class scratch/warm.lean)" "scratch"
  check "and so is a doc's .lean"             "$(glob_class docs/mvcgen-pilot.lean)" "scratch"

  check "imports are parsed"        "$(imports_of "$fake/scratch/warm.lean" | tr '\n' ' ' | sed 's/ *$//')" "LeanModels.Core.Basic Std.Do.Triple"
  check "a core import is core"     "$(is_core_module Std.Do.Triple && echo core)" "core"
  check "a project import is not"   "$(is_core_module LeanModels.Core.Basic && echo core)" ""
  check "a present olean resolves"  "$(olean_for LeanModels.Core.Basic | sed "s|$fake/||")" ".lake/build/lib/lean/LeanModels/Core/Basic.olean"
  check "a package olean resolves"  "$(olean_for Mathlib.Tactic | sed "s|$fake/||")" ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
  check "an absent olean does not"  "$(olean_for LeanModels.Python.Semantics)" ""
  check "guillemets are stripped"   "$(printf '%s' 'Examples.«system-verilog».t' | sed 's/[«»]//g' | tr '.' '/')" "Examples/system-verilog/t"
  check "core imports are not required to have oleans" \
        "$(missing_oleans "$fake/scratch/warm.lean")" ""

  decide scratch/warm.lean
  check "WARM scratch file -> scratch"        "$VERDICT" "scratch"
  decide scratch/pkg.lean
  check "a package import counts as warm"     "$VERDICT" "scratch"
  decide scratch/cold.lean
  check "a MISSING olean -> refuse-cold"      "$VERDICT" "refuse-cold"
  check "  ...and it names A13"               "$(printf '%s' "$WHY" | grep -c 'A13')" "1"
  decide LeanModels/Core/New.lean
  check "a LIBRARY file -> refuse-library"    "$VERDICT" "refuse-library"
  check "  ...and it says take a ticket"      "$(printf '%s' "$WHY" | grep -c 'take a ticket')" "1"
  decide Examples/python/x/proof.lean
  check "an Examples file -> refuse-library"  "$VERDICT" "refuse-library"

  # The tenure case: a lock whose owner pid IS us outranks every refusal.
  mkdir -p "$LOCK"; printf 'qol %s\n' "$$" > "$LOCK/owner"
  decide LeanModels/Core/New.lean
  check "under OUR tenure a library file is fine" "$VERDICT" "tenure"
  decide scratch/cold.lean
  check "under OUR tenure a cold clone is fine"   "$VERDICT" "tenure"
  printf 'other 999999\n' > "$LOCK/owner"
  decide scratch/cold.lean
  check "ANOTHER lane's lock is not our tenure"   "$VERDICT" "refuse-cold"
  printf 'go-lane lake pid 43341 (cwd /x/lean-go)\n' > "$LOCK/owner"
  decide scratch/warm.lean
  check "an UNPARSEABLE owner is not our tenure"  "$VERDICT" "scratch"
  rm -rf "$LOCK"
  decide scratch/warm.lean
  check "no lock at all is not our tenure"        "$VERDICT" "scratch"

  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

# ------------------------------------------------------------------- main
[ -n "$TARGET" ] || die "a .lean file is required (or --self-test)"
[ -d "$CLONE" ] || die "--dir '$CLONE' is not a directory"
case "$TARGET" in *.lean) ;; *) die "'$TARGET' is not a .lean file" ;; esac

# Normalise to a repo-relative path, so the glob test means what it says.
ABS="$TARGET"
case "$ABS" in /*) ;; *) ABS="$(pwd)/$TARGET" ;; esac
[ -f "$ABS" ] || die "no such file: $TARGET"
REL="${ABS#"$CLONE"/}"
case "$REL" in /*) die "'$TARGET' is outside the clone '$CLONE'" ;; esac

decide "$REL"
CMD="nice -n $NICE lake env lean $REL"
echo "check.sh: $REL"
echo "  CASE   $VERDICT"
echo "  WHY    $WHY"
case "$VERDICT" in
  refuse-library|refuse-cold)
    [ -n "$MISSING" ] && printf '  MISSING %s\n' "$(printf '%s' "$MISSING" | tr '\n' ' ')"
    echo "  REFUSED — nothing was run."
    exit 2 ;;
esac
echo "  RUN    $CMD"
if [ "$EXPLAIN" = "1" ]; then
  echo "  --explain: nothing was run."
  exit 0
fi
cd "$CLONE" || die "cannot cd '$CLONE'"
# shellcheck disable=SC2086
nice -n "$NICE" lake env lean "$REL"
