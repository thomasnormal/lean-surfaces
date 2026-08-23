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
# --iterate — THE PROOF-ITERATION CASE, AND IT IS A COURTESY PROTOCOL.
#
# Read this before using it.  `--iterate` runs Lean OUTSIDE the build lock.
# Everything it does to stay polite — the load line, the swap line, the
# machine-wide single-slot, yielding to the owner's workloads — is COURTESY:
# checked at the moment it starts, and not enforced by anything afterwards.
# Another lane can take a tenure a second later, the machine can fill up, and
# nothing will stop this process.  THE ONLY GUARANTEE THIS MODE MAKES IS THE
# RSS CEILING: 3 GB on its own chain, and it KILLS rather than pauses, because
# nothing else is watching an unticketed process.  Everything else is a
# promise about the moment of starting.
#
# WHY IT EXISTS.  Paying a TENURE PER COMPILE makes proof iteration
# unaffordable: the C lane measured ~85 MINUTES PER COMPILE for a 300-line
# proof, which is not a slow loop, it is no loop at all.
#
# Permitted only while all of these hold, CHECKED ON EVERY RUN:
#
#   1. ONE iterate MACHINE-WIDE — not one per lane.  A shared directory
#      (/tmp/ls-iterate/), one live entry total, staleness by the TWO-PART
#      test.  Two lanes iterating is the shape that took the box down at
#      load 29, just smaller.
#   2. load average below 10          — refused by number, not by feel
#   3. swap below 50%                 — likewise
#   4. every project import already has an olean (the warm-clone rule again)
#
# And the STOP condition MIRRORS THE START, on both axes: the same function
# decides both, so a loop whose machine degrades mid-flight is refused its
# NEXT run, by number.  (Load and swap never kill a run in progress — only the
# RSS ceiling does that.)
#
# A11 is not being weakened.  The lock exists because concurrent BUILDS took
# the machine down at load 29, and a single-file elaboration on a quiet
# machine is not that.  This is the one exemption A11's own rationale allows,
# made CONDITIONAL AND MEASURED rather than asserted — and A11's priority
# clause is unchanged and printed on every run: THOMAS'S OWN PROCESSES HAVE
# ABSOLUTE PRIORITY, and this mode yields to owner workloads.
#
# USAGE
#   tools/check.sh path/to/file.lean        # decide, then elaborate
#   tools/check.sh --explain path/to/f.lean # decide and PRINT, run nothing
#   tools/check.sh --iterate --lane <you> path/to/file.lean
#   tools/check.sh --axioms 'Foo.bar,Foo.baz' path/to/file.lean
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
AXIOMS=""
TARGET=""
ITERATE=0
LANE=""
ITER_DIR="${LS_ITERATE_DIR:-/tmp/ls-iterate}"    # MACHINE-WIDE, one live entry
MAX_LOAD="${LS_ITERATE_MAX_LOAD:-10}"
MAX_SWAP_PCT="${LS_ITERATE_MAX_SWAP_PCT:-50}"
# 3 GB, and deliberately STRICTER than A16's 5 GB per-process tenure line: a
# tenure has a watchdog and a lock behind it, an unticketed iterate has only
# this.  It kills, it does not pause.
ITER_RSS_LIMIT_KB="${LS_ITERATE_RSS_LIMIT_KB:-3145728}"
THREADS="${LEAN_NUM_THREADS:-2}"

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
die()   { echo "check.sh: $*" >&2; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --dir)       CLONE="${2:-}"; shift 2 ;;
    --explain)   EXPLAIN=1; shift ;;
    --iterate)   ITERATE=1; shift ;;
    --axioms)    AXIOMS="${2:-}"; shift 2 ;;
    --lane)      LANE="${2:-}"; shift 2 ;;
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

# ------------------------------------------- IS THIS RUN A MEASUREMENT?
# From the successor lane's instrumented proof run, which counted "0 open
# arms" TWICE while (a) looping in `simp` until the heartbeat timeout and
# (b) erroring inside a `first` chain — `split` fails HARD, escapes the chain,
# and never reaches the fallback the counter counts.
#
#   > A counter that counts goals reaching a fallback reads an ERROR as a
#   > SUCCESS.
#
# It is the same shape as `#print axioms` on a failed statement: a success
# signal that SURVIVES the failure it should report.  So a run is not a
# measurement until its exit code, its warning classes and its two known
# runaway modes have been read — and this says so in one line, because a
# report nobody reads at a glance is a report that gets skipped at 2am.
warning_classes() {             # output -> the distinct NON-sorry warnings
  grep -E 'warning:' "$1" 2>/dev/null \
    | grep -v "declaration uses 'sorry'" \
    | sed 's/^.*warning: *//' | cut -c1-72 | sort -u
}

# rc, output -> the report on stdout, and the one-line verdict LAST.
run_verdict() {
  local rc="$1" f="$2" nerr nsorry nwarn nother hb mrd reasons="" cls
  [ -f "$f" ] || { echo "    (no output captured)"; echo "  VERDICT  NOT A MEASUREMENT: no output was captured"; return 1; }
  nerr="$(grep -cE '^error|error:' "$f" 2>/dev/null || true)"
  nsorry="$(grep -c "declaration uses 'sorry'" "$f" 2>/dev/null || true)"
  nwarn="$(grep -cE 'warning:' "$f" 2>/dev/null || true)"
  nother=$((nwarn - nsorry))
  hb="$(grep -cE 'maximum number of heartbeats|\(deterministic\) timeout' "$f" 2>/dev/null || true)"
  mrd="$(grep -cE 'maxRecDepth|maximum recursion depth' "$f" 2>/dev/null || true)"

  printf '    exit code      %s\n' "$rc"
  printf '    warnings       %s total — %s sorry, %s other\n' "$nwarn" "$nsorry" "$nother"
  if [ "$nother" -gt 0 ]; then
    warning_classes "$f" | sed 's/^/      other: /'
  fi
  # The two runaway modes get their own lines whether or not they fired: an
  # absent line is information too, and "heartbeats none" is what lets a lane
  # trust the run without re-reading the log.
  if [ "$hb" -gt 0 ]; then
    printf '    heartbeats     %s line(s) — THE RUN DID NOT FINISH THINKING:\n' "$hb"
    grep -E 'maximum number of heartbeats|\(deterministic\) timeout' "$f" | head -3 | cut -c1-96 | sed 's/^/      /'
  else
    printf '    heartbeats     none\n'
  fi
  if [ "$mrd" -gt 0 ]; then
    printf '    maxRecDepth    %s line(s) — see tools/diagnose.sh --explain max-rec-depth (THREE causes):\n' "$mrd"
    grep -E 'maxRecDepth|maximum recursion depth' "$f" | head -3 | cut -c1-96 | sed 's/^/      /'
  else
    printf '    maxRecDepth    none\n'
  fi

  [ "$rc" != "0" ]    && reasons="${reasons:+$reasons; }exit $rc"
  [ "$nerr" -gt 0 ]   && reasons="${reasons:+$reasons; }$nerr error line(s)"
  [ "$hb" -gt 0 ]     && reasons="${reasons:+$reasons; }heartbeat timeout"
  [ "$mrd" -gt 0 ]    && reasons="${reasons:+$reasons; }maxRecDepth"
  if [ "$nother" -gt 0 ]; then
    cls="$(warning_classes "$f" | head -1)"
    reasons="${reasons:+$reasons; }$nother non-sorry warning(s): ${cls:-unknown}"
  fi

  if [ -n "$reasons" ]; then
    printf '  VERDICT  NOT A MEASUREMENT: %s\n' "$reasons"
    return 1
  fi
  printf '  VERDICT  TRUSTWORTHY: exit 0, sorry-only warnings\n'
  return 0
}

# §0.1 II(a): a declaration whose STATEMENT failed prints "does not depend on
# any axioms" — CLEANER than the truth.  So the axiom lines are reported only
# from a run that was a measurement, and otherwise refused BY NAME.
axiom_report() {                # output, trustworthy(0/1)
  local f="$1" ok="$2"
  grep -qE "depend.* on|does not depend on any axioms" "$f" 2>/dev/null || return 0
  if [ "$ok" != "0" ]; then
    printf '    axioms         NOT REPORTED — this run was not a measurement, and a failed\n'
    printf '                   STATEMENT prints "does not depend on any axioms" (§0.1 II(a))\n'
    return 0
  fi
  printf '    axioms         (from a clean elaboration):\n'
  grep -E "depends on axioms|does not depend on any axioms" "$f" | cut -c1-96 | sed 's/^/      /'
}

# ------------------------------------------------- the machine, measured
# Every reader is MOCKABLE, because a guard whose refusal path cannot be
# executed is a guard nobody has tested.  The self-test drives all three.
read_load() {                   # 1-minute load average
  [ -n "${LS_MOCK_LOAD:-}" ] && { printf '%s\n' "$LS_MOCK_LOAD"; return 0; }
  if [ -r /proc/loadavg ]; then awk '{print $1}' /proc/loadavg; return 0; fi
  sysctl -n vm.loadavg 2>/dev/null | awk '{ gsub(/[{}]/, ""); print $1 }'
}

read_swap_pct() {               # swap in use, as a percentage of total
  [ -n "${LS_MOCK_SWAP:-}" ] && { printf '%s\n' "$LS_MOCK_SWAP"; return 0; }
  if [ -r /proc/meminfo ]; then
    awk '/^SwapTotal:/{t=$2} /^SwapFree:/{f=$2}
         END{ if (t+0 <= 0) print 0; else printf "%.1f", (t-f)*100/t }' /proc/meminfo
    return 0
  fi
  sysctl -n vm.swapusage 2>/dev/null | awk '{
      for (i = 1; i <= NF; i++) {
        if ($i == "total") { v = $(i+2); gsub(/[^0-9.]/, "", v); t = v }
        if ($i == "used")  { v = $(i+2); gsub(/[^0-9.]/, "", v); u = v }
      }
      if (t+0 <= 0) print 0; else printf "%.1f", u*100/t }'
}

over() {                        # over A B -> 0 when A > B, in floating point
  awk -v a="$1" -v b="$2" 'BEGIN { exit !(a+0 > b+0) }'
}

descendants() {                 # BFS over ps, never `pgrep -P` (A12's lesson)
  ps -eo pid,ppid 2>/dev/null | awk -v root="$1" '
    NR > 1 { child[$2] = child[$2] " " $1 }
    END { n = 1; q[1] = root
          for (i = 1; i <= n; i++) {
            split(child[q[i]], kids, " ")
            for (k in kids) if (kids[k] != "") { n++; q[n] = kids[k]; print kids[k] } } }'
}

has_lean_descendant() {
  [ -n "${LS_MOCK_LEAN_CHILD:-}" ] && { [ "$LS_MOCK_LEAN_CHILD" = "1" ]; return $?; }
  local kid
  for kid in $(descendants "$1"); do
    case "$(ps -o comm= -p "$kid" 2>/dev/null)" in *lean*|*lake*) return 0 ;; esac
  done
  return 1
}

# THE SLOT IS MACHINE-WIDE.  One live entry in a shared directory, whatever
# lane it belongs to: two lanes iterating at once is the shape that took the
# box down at load 29, only smaller.  Entry filename IS the pid; its contents
# are `<lane> <pid>`, A5's format, so a human reading the directory sees who.
iterate_entry() { printf '%s/%s\n' "$ITER_DIR" "$$"; }

# The TWO-PART test again (§7.1 rule 5), and the failure direction is the same:
# an unparseable entry is treated as LIVE, so a bad file refuses a new iterate
# rather than reclaiming one that is running.
iterate_entry_live() {          # entry file -> 0 when its holder is alive
  local f="$1" owner pid
  [ -f "$f" ] || return 1
  owner="$(cat "$f" 2>/dev/null)"; [ -n "$owner" ] || return 1
  pid="$(printf '%s' "$owner" | awk '{print $NF}')"     # A5: pid LAST
  case "$pid" in ''|*[!0-9]*) return 0 ;; esac          # unparseable => live
  kill -0 "$pid" 2>/dev/null || return 1                # part 1: dead => stale
  has_lean_descendant "$pid" || return 1                # part 2: no Lean => stale
  return 0
}

iterate_live_holder() {         # -> the contents of the live entry, or ''
  local f
  [ -d "$ITER_DIR" ] || return 1
  for f in "$ITER_DIR"/*; do
    [ -f "$f" ] || continue
    case "$f" in *"/$$") continue ;; esac               # never ourselves
    if iterate_entry_live "$f"; then
      cat "$f" 2>/dev/null
      return 0
    fi
    rm -f "$f" 2>/dev/null                              # stale: reaped, quietly
  done
  return 1
}

# ONE function decides START and STOP, so "the stop mirrors the start" is true
# by construction rather than by two lists agreeing.
machine_is_quiet() {            # -> '' when quiet, else the reason, by number
  local l s
  l="$(read_load)"; s="$(read_swap_pct)"
  ITER_LOAD="$l"; ITER_SWAP="$s"
  if over "$l" "$MAX_LOAD"; then
    echo "load average is $l, over the line of $MAX_LOAD"; return 0
  fi
  if over "$s" "$MAX_SWAP_PCT"; then
    echo "swap is ${s}% in use, over the line of ${MAX_SWAP_PCT}%"; return 0
  fi
  echo ""
}

# The one guarantee this mode makes.  Pure, so both directions are testable.
iterate_rss_verdict() {         # limit_kb  < "<pid> <rss_kb>" rows
  awk -v lim="$1" '
    { total += $2; if ($2 > worst) { worst = $2; wpid = $1 } }
    END { if (total > lim) printf "kill %s %d\n", (wpid == "" ? "-" : wpid), total
          else print "ok" }'
}

# The citation checks itself, and "present" is not "adopted": A17 landed in
# §7.1a as a DRAFT row while this was being written, which would have silently
# turned the honest note off.  Three states, three messages.
a17_status() {                  # -> absent | draft | adopted
  local doc="$CLONE/docs/family-architecture.md" row
  [ -f "$doc" ] || { echo absent; return 0; }
  row="$(grep -m1 '^| 17 ' "$doc" 2>/dev/null)"
  if [ -z "$row" ]; then
    grep -q 'AMENDMENT 17' "$doc" 2>/dev/null || { echo absent; return 0; }
    row="$(grep -m1 'AMENDMENT 17' "$doc")"
  fi
  case "$row" in *DRAFT*|*draft*) echo draft ;; *) echo adopted ;; esac
}

ITER_LOAD=""; ITER_SWAP=""
decide_iterate() {              # sets VERDICT / WHY / MISSING, and the numbers
  local holder reason
  VERDICT=""; WHY=""; MISSING=""
  ITER_LOAD="$(read_load)"; ITER_SWAP="$(read_swap_pct)"
  if holder="$(iterate_live_holder)"; then
    VERDICT="refuse-concurrent"
    WHY="an iterate is already running MACHINE-WIDE ($holder). One slot total, whatever lane holds it: two single-file elaborations are the shape that took the machine down at load 29, just smaller"
    return 0
  fi
  reason="$(machine_is_quiet)"
  if [ -n "$reason" ]; then
    case "$reason" in
      load*) VERDICT="refuse-load"
             WHY="$reason. Lock-free iteration is a courtesy permitted on a QUIET machine, and this one is not quiet" ;;
      *)     VERDICT="refuse-swap"
             WHY="$reason. A swapping machine turns one elaboration into everybody's slowdown" ;;
    esac
    return 0
  fi
  MISSING="$(missing_oleans "$CLONE/$1" 2>/dev/null || true)"
  if [ -n "$MISSING" ]; then
    VERDICT="refuse-cold"
    WHY="this clone is COLD for $(printf '%s\n' "$MISSING" | grep -c .) of the file's imports — resolving them here is Lean execution outside the lock (A11) and a GB-scale download (A13). Seed first, then iterate"
    return 0
  fi
  VERDICT="iterate"
  WHY="conditions met — lock-free per A17: load $ITER_LOAD < $MAX_LOAD, swap ${ITER_SWAP}% < ${MAX_SWAP_PCT}%, imports warm, the machine-wide iterate slot is free. COURTESY ONLY — yields to owner workloads (Thomas's own processes have absolute priority, A11), and the sole guarantee is the $((ITER_RSS_LIMIT_KB / 1048576)) GB RSS ceiling, which KILLS"
  return 0
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

  # ---- --iterate: the tightened A17 spec, every refusal EXECUTED
  echo "  -- iterate"
  ITER_DIR="$tmp/iter"; mkdir -p "$ITER_DIR"
  LANE="testlane"; ITERATE=1
  export LS_MOCK_LOAD=1.0 LS_MOCK_SWAP=5.0

  decide_iterate LeanModels/Core/New.lean
  check "a quiet machine + warm clone -> iterate" "$VERDICT" "iterate"
  check "  ...and the WHY cites A17"              "$(printf '%s' "$WHY" | grep -c 'lock-free per A17')" "1"
  check "  ...names the priority clause"          "$(printf '%s' "$WHY" | grep -c 'yields to owner workloads')" "1"
  check "  ...and says COURTESY ONLY"             "$(printf '%s' "$WHY" | grep -c 'COURTESY ONLY')" "1"
  check "  ...naming the RSS ceiling as the guarantee" "$(printf '%s' "$WHY" | grep -c '3 GB RSS ceiling')" "1"
  check "  ...on a LIBRARY file the ticket path refuses" \
        "$(decide LeanModels/Core/New.lean; echo "$VERDICT")" "refuse-library"

  # THE STOP MIRRORS THE START: one function, asserted on both axes.
  check "quiet machine -> no stop reason"         "$(machine_is_quiet)" ""
  check "stop mirrors start on LOAD"              "$(LS_MOCK_LOAD=42.5 machine_is_quiet)" \
        "load average is 42.5, over the line of 10"
  check "stop mirrors start on SWAP"              "$(LS_MOCK_SWAP=87.3 machine_is_quiet)" \
        "swap is 87.3% in use, over the line of 50%"
  LS_MOCK_LOAD=42.5 decide_iterate LeanModels/Core/New.lean
  check "high load refuses"                       "$VERDICT" "refuse-load"
  check "  ...with the STOP function's own words" "$(printf '%s' "$WHY" | grep -c 'load average is 42.5, over the line of 10')" "1"
  LS_MOCK_LOAD=10 decide_iterate LeanModels/Core/New.lean
  check "load exactly AT the line is allowed"     "$VERDICT" "iterate"
  LS_MOCK_SWAP=87.3 decide_iterate LeanModels/Core/New.lean
  check "high swap refuses"                       "$VERDICT" "refuse-swap"
  check "  ...naming the NUMBER"                  "$(printf '%s' "$WHY" | grep -c '87.3')" "1"

  decide_iterate scratch/cold.lean
  check "a cold clone refuses"                    "$VERDICT" "refuse-cold"
  check "  ...naming A13"                         "$(printf '%s' "$WHY" | grep -c 'A13')" "1"

  # THE SLOT IS MACHINE-WIDE.  A real foreign pid, from a DIFFERENT lane.
  sleep 120 & other=$!
  printf 'some-other-lane %s\n' "$other" > "$ITER_DIR/$other"
  LS_MOCK_LEAN_CHILD=1 decide_iterate LeanModels/Core/New.lean
  check "a SECOND iterate refuses ACROSS LANES"   "$VERDICT" "refuse-concurrent"
  check "  ...naming the holder's lane"           "$(printf '%s' "$WHY" | grep -c 'some-other-lane')" "1"
  check "  ...and it outranks the load check"     "$(LS_MOCK_LOAD=99 LS_MOCK_LEAN_CHILD=1 decide_iterate LeanModels/Core/New.lean; echo "$VERDICT")" "refuse-concurrent"
  LS_MOCK_LEAN_CHILD=0 decide_iterate LeanModels/Core/New.lean
  check "part 2: a live pid with no Lean is STALE" "$VERDICT" "iterate"
  check "  ...and the stale entry was REAPED"      "$(ls "$ITER_DIR" | grep -c "^$other\$")" "0"
  kill "$other" 2>/dev/null; wait "$other" 2>/dev/null

  printf 'dead-lane 999999\n' > "$ITER_DIR/999999"
  LS_MOCK_LEAN_CHILD=1 decide_iterate LeanModels/Core/New.lean
  check "part 1: a DEAD holder is reclaimed"      "$VERDICT" "iterate"
  printf 'go-lane lake pid 43341 (cwd /x)\n' > "$ITER_DIR/bogus"
  decide_iterate LeanModels/Core/New.lean
  check "an UNPARSEABLE holder is never reclaimed" "$VERDICT" "refuse-concurrent"
  rm -f "$ITER_DIR"/*
  check "our OWN entry never blocks us" \
        "$(printf 'testlane %s\n' "$$" > "$ITER_DIR/$$"; LS_MOCK_LEAN_CHILD=1 decide_iterate LeanModels/Core/New.lean; echo "$VERDICT")" "iterate"
  rm -f "$ITER_DIR"/*

  # The self-updating citation, in all three states.
  a17dir="$tmp/a17"; mkdir -p "$a17dir/docs"
  saved_clone="$CLONE"; CLONE="$a17dir"
  check "no doc at all -> absent"          "$(a17_status)" "absent"
  printf '# doc\n| 16 | something | new |\n' > "$a17dir/docs/family-architecture.md"
  check "no A17 row -> absent"             "$(a17_status)" "absent"
  printf '| 17 | the iteration loop | **DRAFT — five tightenings** |\n' >> "$a17dir/docs/family-architecture.md"
  check "a DRAFT row -> draft, not adopted" "$(a17_status)" "draft"
  printf '# doc\n| 17 | the iteration loop | **carried** |\n' > "$a17dir/docs/family-architecture.md"
  check "a carried row -> adopted"          "$(a17_status)" "adopted"
  CLONE="$saved_clone"

  # THE ONE GUARANTEE: the RSS ceiling, asserted in BOTH directions.
  check "a chain under the ceiling survives" \
        "$(printf '10 1000000\n11 1000000\n' | iterate_rss_verdict 3145728)" "ok"
  check "a chain over the ceiling is KILLED" \
        "$(printf '10 2000000\n11 2000000\n' | iterate_rss_verdict 3145728 | awk '{print $1}')" "kill"
  check "  ...naming the worst offender"  \
        "$(printf '10 500000\n11 3000000\n' | iterate_rss_verdict 3145728 | awk '{print $2}')" "11"
  check "the ceiling is 3 GB, stricter than A16's tenure line" \
        "$ITER_RSS_LIMIT_KB" "3145728"

  # ---- IS THIS RUN A MEASUREMENT?  (the successor lane's "0 open arms")
  echo "  -- run verdict"
  v="$tmp/verdict"; mkdir -p "$v"

  printf 'info: elaborated\n' > "$v/clean.out"
  check "clean run -> TRUSTWORTHY" \
        "$(run_verdict 0 "$v/clean.out" | grep -c 'VERDICT  TRUSTWORTHY: exit 0, sorry-only warnings')" "1"
  check "  ...and both runaway modes read 'none'" \
        "$(run_verdict 0 "$v/clean.out" | grep -cE 'heartbeats     none|maxRecDepth    none')" "2"

  printf "f.lean:3:0: warning: declaration uses 'sorry'\nf.lean:9:0: warning: declaration uses 'sorry'\n" > "$v/sorry.out"
  check "sorry-only warnings stay TRUSTWORTHY" \
        "$(run_verdict 0 "$v/sorry.out" | grep -c 'TRUSTWORTHY')" "1"
  check "  ...and the sorries are COUNTED"  \
        "$(run_verdict 0 "$v/sorry.out" | grep -c 'warnings       2 total — 2 sorry, 0 other')" "1"

  check "a nonzero exit is NOT A MEASUREMENT" \
        "$(run_verdict 1 "$v/clean.out" | grep -c 'NOT A MEASUREMENT: exit 1')" "1"

  # THE CASE THAT MINTED THIS: an error inside a `first` chain, where a
  # fallback-counting instrument read the error as a success.
  printf 'f.lean:12:2: error: tactic split failed\ninfo: done\n' > "$v/escaped.out"
  check "an ERROR with exit 0 is still NOT A MEASUREMENT" \
        "$(run_verdict 0 "$v/escaped.out" | grep -c 'NOT A MEASUREMENT: 1 error line')" "1"

  printf 'f.lean:1:1: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\n' > "$v/hb.out"
  check "a heartbeat timeout is CALLED OUT" \
        "$(run_verdict 1 "$v/hb.out" | grep -c 'THE RUN DID NOT FINISH THINKING')" "1"
  check "  ...and named in the verdict"    \
        "$(run_verdict 1 "$v/hb.out" | grep -c 'heartbeat timeout')" "1"

  printf 'f.lean:2:2: error: maximum recursion depth has been reached\n' > "$v/mrd.out"
  check "maxRecDepth is CALLED OUT"        \
        "$(run_verdict 1 "$v/mrd.out" | grep -c 'maxRecDepth    1 line')" "1"
  check "  ...pointing at its THREE causes" \
        "$(run_verdict 1 "$v/mrd.out" | grep -c 'THREE causes')" "1"

  printf "f.lean:4:0: warning: declaration uses 'sorry'\nf.lean:7:9: warning: unused variable 'fuel'\n" > "$v/other.out"
  check "a NON-sorry warning voids the measurement" \
        "$(run_verdict 0 "$v/other.out" | grep -c 'NOT A MEASUREMENT: 1 non-sorry warning')" "1"
  check "  ...and its class is LISTED"     \
        "$(run_verdict 0 "$v/other.out" | grep -c 'other: unused variable')" "1"

  check "no output at all is NOT A MEASUREMENT" \
        "$(run_verdict 0 "$v/does-not-exist" | grep -c 'no output was captured')" "1"

  # §0.1 II(a): the axiom line is the one that reads CLEANER than the truth.
  printf "'thm' does not depend on any axioms\nf.lean:1:1: error: unknown identifier\n" > "$v/ax-bad.out"
  run_verdict 0 "$v/ax-bad.out" >/dev/null; vok=$?
  check "a failed run REFUSES to report axioms" \
        "$(axiom_report "$v/ax-bad.out" "$vok" | grep -c 'NOT REPORTED')" "1"
  check "  ...citing the mode table"       \
        "$(axiom_report "$v/ax-bad.out" "$vok" | grep -c '§0.1 II(a)')" "1"
  printf "'thm' depends on axioms: [propext, Classical.choice, Quot.sound]\n" > "$v/ax-ok.out"
  run_verdict 0 "$v/ax-ok.out" >/dev/null; vok=$?
  check "a clean run DOES report them"     \
        "$(axiom_report "$v/ax-ok.out" "$vok" | grep -c 'propext')" "1"

  unset LS_MOCK_LOAD LS_MOCK_SWAP LS_MOCK_LEAN_CHILD
  ITERATE=0; LANE=""

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

if [ "$ITERATE" = "1" ]; then
  [ -n "$LANE" ] || die "--iterate requires --lane <name>: the one-per-lane slot is a pidfile keyed by it"
  case "$LANE" in *[!A-Za-z0-9_.]*) die "--lane must be [A-Za-z0-9_.]+" ;; esac
  decide_iterate "$REL"
else
  decide "$REL"
fi

CMD="nice -n $NICE lake env lean $REL"
echo "check.sh: $REL"
if [ "$VERDICT" = "iterate" ]; then
  echo "  CASE   iterate: conditions met — lock-free per A17"
else
  echo "  CASE   $VERDICT"
fi
echo "  WHY    $WHY"
# §5.4a: the numbers this run was PERMITTED BY ride the run.
[ "$ITERATE" = "1" ] && printf '  STATE  load %s (line %s), swap %s%% (line %s%%), lane %s\n' \
  "$ITER_LOAD" "$MAX_LOAD" "$ITER_SWAP" "$MAX_SWAP_PCT" "$LANE"
case "$VERDICT" in
  refuse-*)
    [ -n "$MISSING" ] && printf '  MISSING %s\n' "$(printf '%s' "$MISSING" | tr '\n' ' ')"
    echo "  REFUSED — nothing was run."
    exit 2 ;;
esac
# The citation checks itself: A17 is being drafted, and a pointer to a rule
# that is not yet written is the thing this repository keeps paying for.
if [ "$ITERATE" = "1" ]; then
  case "$(a17_status)" in
    absent)
      echo "  NOTE   A17 has NO ROW in §7.1a. This run's permission rests on the"
      echo "         conditions above, which were CHECKED, not on the register." ;;
    draft)
      echo "  NOTE   A17 is in §7.1a but marked DRAFT. Present is not adopted: this"
      echo "         run's permission rests on the conditions above, which were"
      echo "         CHECKED. The note clears when the row does." ;;
  esac
fi
echo "  RUN    $CMD"
if [ "$EXPLAIN" = "1" ]; then
  echo "  --explain: nothing was run."
  exit 0
fi
cd "$CLONE" || die "cannot cd '$CLONE'"
ITER_WATCHDOG=""
ENTRY=""
cleanup_iterate() {
  [ -n "$ITER_WATCHDOG" ] && kill "$ITER_WATCHDOG" 2>/dev/null
  [ -n "$ENTRY" ] && rm -f "$ENTRY" "$ENTRY.guard" 2>/dev/null
  return 0
}
if [ "$ITERATE" = "1" ]; then
  # A5's format, and the pid SPANS the run (A10's shape at a smaller scale).
  mkdir -p "$ITER_DIR" 2>/dev/null || die "cannot create '$ITER_DIR'"
  ENTRY="$(iterate_entry)"
  printf '%s %s\n' "$LANE" "$$" > "$ENTRY" || die "cannot write '$ENTRY'"
  trap 'cleanup_iterate' EXIT INT TERM
  export LEAN_NUM_THREADS="$THREADS"
  echo "  RUN    LEAN_NUM_THREADS=$THREADS $CMD"
  # THE ONLY GUARANTEE THIS MODE MAKES.  It KILLS rather than pauses, because
  # nothing else is watching an unticketed process.  A16's lesson applies at
  # this scale too: the guard is NOT in its own kill set.
  (
    while kill -0 $$ 2>/dev/null; do
      sleep 10
      g="$(cat "$ENTRY.guard" 2>/dev/null)"
      case "$g" in ''|*[!0-9]*) g=0 ;; esac
      excl=" $g $(descendants "$g" 2>/dev/null | tr '\n' ' ') "
      rows=""
      for pp in $(descendants $$); do
        case "$excl" in *" $pp "*) continue ;; esac
        rr="$(ps -o rss= -p "$pp" 2>/dev/null | tr -d ' ')"
        case "$rr" in ''|*[!0-9]*) continue ;; esac
        rows="$rows$pp $rr
"
      done
      case "$(printf '%s' "$rows" | iterate_rss_verdict "$ITER_RSS_LIMIT_KB")" in
        kill\ *)
          tot="$(printf '%s' "$rows" | awk '{t += $2} END {print t+0}')"
          echo "ITERATE RSS CEILING: chain at $((tot / 1024)) MB > $((ITER_RSS_LIMIT_KB / 1024)) MB — KILLING (this mode's only guarantee)" >&2
          for pp in $(descendants $$); do
            case "$excl" in *" $pp "*) continue ;; esac
            kill -9 "$pp" 2>/dev/null
          done ;;
      esac
    done
  ) & ITER_WATCHDOG=$!
  printf '%s\n' "$ITER_WATCHDOG" > "$ENTRY.guard" 2>/dev/null
fi
# --axioms runs a TEMP COPY with `#print axioms` appended, so the axiom lines
# come from the SAME elaboration whose exit code and warnings are being read —
# an axiom print from a different run is a number without its state (§5.4a).
RUN_TARGET="$REL"
AXCOPY=""
if [ -n "$AXIOMS" ]; then
  AXCOPY="$(mktemp "${TMPDIR:-/tmp}/check-axioms.XXXXXX.lean")" || die "no temp file"
  cat "$CLONE/$REL" > "$AXCOPY" || die "cannot copy '$REL'"
  printf '\n' >> "$AXCOPY"
  printf '%s' "$AXIOMS" | tr ',' '\n' | while IFS= read -r d; do
    [ -n "$d" ] || continue
    printf '#print axioms %s\n' "$d" >> "$AXCOPY"
  done
  RUN_TARGET="$AXCOPY"
  echo "  AXIOMS   appended #print axioms for: $AXIOMS (run from a temp copy, so"
  echo "           error paths below name that copy rather than $REL)"
fi

RUN_LOG="$(mktemp "${TMPDIR:-/tmp}/check-run.XXXXXX")" || die "no temp file"
# shellcheck disable=SC2086
nice -n "$NICE" lake env lean "$RUN_TARGET" 2>&1 | tee "$RUN_LOG"
RUN_RC="${PIPESTATUS[0]}"

# A RUN IS NOT A MEASUREMENT UNTIL IT HAS BEEN READ.
echo
run_verdict "$RUN_RC" "$RUN_LOG"
VERDICT_OK=$?
[ -n "$AXIOMS" ] && axiom_report "$RUN_LOG" "$VERDICT_OK"
[ -n "$AXCOPY" ] && rm -f "$AXCOPY"
rm -f "$RUN_LOG"

if [ "$ITERATE" = "1" ]; then
  cleanup_iterate
  # THE STOP MIRRORS THE START: the same function, the same numbers.
  stop_reason="$(machine_is_quiet)"
  if [ -n "$stop_reason" ]; then
    echo "  STOP   $stop_reason — the NEXT run will refuse (the stop mirrors the start)"
  else
    echo "  STOP   conditions still hold (load $ITER_LOAD, swap ${ITER_SWAP}%) — another run is permitted"
  fi
fi
exit "$RUN_RC"
