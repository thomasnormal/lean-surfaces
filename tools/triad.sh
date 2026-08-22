#!/usr/bin/env bash
# tools/triad.sh — ONE locked triad, and the build protocol AS CODE.
#
# WHY THIS FILE EXISTS.  docs/family-architecture.md §7 is the build lock's
# only durable home, and §7.1a says so in as many words.  A prose home stops
# a purge from erasing the protocol; it does not stop a lane from
# implementing it wrongly.  Six lane-private triad scripts were measured on
# 2026-08-22 (docs/duplication-audit.md §2): 382 lines, 24 amendment
# violations across 63 applicable cells, two RSS guards that watch a process
# that can never be the build, one owner file whose last field is
# `lean4lean)` — the exact parse defect §7.1 rule 5 names — and one owner
# pid that is a child stage's, the exact defect amendment 10 names.  Every
# one of those was written by a lane that had read the protocol.
#
# So: the doc DESCRIBES, this script IS.  An amendment becomes a commit here
# and every lane gets it by rebase.
#
# AMENDMENTS IMPLEMENTED (docs/family-architecture.md §7.1, §7.1a):
#   base 1  one build at a time, machine-wide, via an mkdir lock
#   base 2  release is `rm -rf` with a CHECKED status; exit 143/137 is a
#           resource kill, not a red build; no `-j` (an argument error on
#           this lake — throttle with LEAN_NUM_THREADS)
#   base 4  batch: ONE triad per landing, never per edit
#   base 5  a stale lock is cleared only on the TWO-PART test
#   base 6  never kill another lane's processes — kills by PARENTAGE only
#   A4      owner written ONCE under `set -C`; owner is a hint, the process
#           tree is the truth
#   A5      owner file is exactly `<lane> <pid>`, pid LAST
#   A6      never fetch-rebase while a build runs in the same clone
#   A7      the release trap is OWNERSHIP-CHECKED
#   A8      a staleness verdict comes from ONE atomic re-read immediately
#           before the removal, never from an earlier read
#   A9      FIFO ticket queue — only the OLDEST ticket attempts the mkdir
#   A10     the owner pid SPANS THE TENURE: it is this script's pid, never
#           a child stage's
#   A11     the lock covers ALL Lean execution; LEAN_NUM_THREADS=2, nice 19,
#           and a 3 GB RSS kill line over THIS SCRIPT'S OWN descendants
#   A12     traps kill descendants RECURSIVELY — a BFS over `ps -eo pid,ppid`,
#           never `pkill -P`, which misses grandchildren
#   A16     the RSS line is PER-PROCESS (5 GB) with a CHAIN line (10 GB) as a
#           secondary; the guard EXCLUDES ITSELF from the kill set and is
#           RESTARTED PER ATTEMPT.  A11's single 3 GB chain cap killed honest
#           builds — one worker was measured at 3251 MB — and, because the
#           kill set included the guard, the guard died with the chain it
#           reaped and ATTEMPT 2 RAN UNGUARDED.
#
# THE BANNER.  Every run prints the protocol level it implements.  Audit #2
# found TWO DRIFTED COPIES of this script in /tmp: lanes copy before editing
# because bash reads a script INCREMENTALLY and editing a running script
# corrupts it.  That is legitimate staging — but a copy whose diffs never land
# is a private script again, at 38% violation density.  A banner makes the
# drift visible in the log.
#
# NOT YET WIRED INTO ANY LANE'S FLOW.  Adoption is per-lane, on dispatch.
#
# --classify — THE SCOPE OF A GREEN, AND WHAT IT COVERS (§5.4a, §7.1 rule 4).
# base rule 4 says one triad per landing; it does not say every landing owes
# the same triad.  A docs-only landing that pays for a full build is paying
# a tenure the machine does not owe it, and — worse — a SCOPED green that
# does not say what it covers is exactly §5.4a's failure mode: a number
# quoted without the state it was taken in.  So `--classify` reads the
# landing's own diff, picks the smallest build that can still convict it,
# and PRINTS the coverage statement alongside the verdict.
#
#   docs   nothing in the diff can change elaboration -> `tools/docs_check.py`
#          only, and NO TENURE: docs_check shells out to nothing, so there is
#          no Lean execution for A11's lock to cover.
#   tier   LeanModels/<tier>/ and its Examples/ -> a SCOPED `lake build` of
#          the touched modules (plus the tier root module where one exists).
#          A NON-LEAN fixture under Examples/ is tier-local only when it is
#          REACHABLE — see the reachability probe below.
#   spine  LeanModels.lean, LeanModels/Core/, the shared harness, the
#          lakefile -> the full build.  Anything UNRECOGNIZED lands here too.
#
# The classification is a FLOOR, never a ceiling: a lane that passes its own
# --gates keeps them and keeps the tenure, because this script cannot know
# whether a lane's gate runs Lean.  A lane can always run more.
#
# USAGE
#   tools/triad.sh --lane <name> [--dir <clone>] [--gates "cmd; cmd"] [...]
#   tools/triad.sh --self-test          # exercises the queue logic, NO Lean
#   tools/triad.sh --lane x --dry-run   # takes a real tenure, runs no Lean
#   tools/triad.sh --lane x --classify  # scope the triad from the diff
#   tools/triad.sh --lane x --gates "a; b"   # YOUR gates, and no default warning
#
# GATES.  Without --gates the default set is `docs_check; diff_test`, which is
# NARROWER than some retired lane scripts.  A run that did not choose its own
# gates SAYS WHICH ONES IT IS RUNNING — see the notice by `gate_notice` below.
#   tools/triad.sh --classify-only      # print the classification, run nothing
#   tools/triad.sh --classify --against <ref>    # default: github/master
#
# The lock and queue paths are overridable (LS_LOCK / LS_QUEUE) so the logic
# can be exercised in a sandbox.  A live run always uses the real paths.

set -u

# ---------------------------------------------------------------- settings
LANE=""
CLONE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOCK="${LS_LOCK:-/tmp/ls-build.lock}"
QUEUE="${LS_QUEUE:-/tmp/ls-build-queue}"
# A16.  Two lines, and the PER-PROCESS one is the real guard: a single honest
# `lean` worker was measured at 3251 MB, so a 3 GB CHAIN cap convicted a build
# that was behaving.  The chain line stays as a secondary, at a height no
# healthy tenure reaches.
RSS_PROC_LIMIT_KB="${LS_RSS_PROC_LIMIT_KB:-5242880}"    # 5 GB, per process
RSS_CHAIN_LIMIT_KB="${LS_RSS_LIMIT_KB:-10485760}"       # 10 GB, whole chain
THREADS="${LEAN_NUM_THREADS:-2}"               # amendment 11
NICE="${LS_NICE:-19}"                          # amendment 11
MAX_WAIT="${LS_MAX_WAIT:-14400}"               # 4 h, then give up LOUDLY
STALE_AFTER="${LS_STALE_AFTER:-1800}"          # only then consider a reclaim
DRY_RUN=0
SELF_TEST=0
GATES=""
CLASSIFY=0
CLASSIFY_ONLY=0
AGAINST=""                                     # merge target; default below

# The header IS the usage text, so print it whole — a `sed -n '1,60p'` goes
# stale the first time somebody documents a flag.
# The protocol level this file implements.  Bump it in the same commit as the
# amendment, so a /tmp copy that predates one is identifiable from its output.
TRIAD_PROTOCOL="base 1-6 + A4-A13 + A16"
TRIAD_PROTOCOL_DATE="2026-08-22"

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
banner() { echo "tools/triad.sh — protocol $TRIAD_PROTOCOL ($TRIAD_PROTOCOL_DATE), \
$( (git -C "$CLONE" rev-parse --short HEAD 2>/dev/null) || echo 'no git' )"; }

while [ $# -gt 0 ]; do
  case "$1" in
    --lane)      LANE="${2:-}"; shift 2 ;;
    --dir)       CLONE="${2:-}"; shift 2 ;;
    --gates)     GATES="${2:-}"; shift 2 ;;
    --rss-limit)      RSS_CHAIN_LIMIT_KB="${2:-}"; shift 2 ;;
    --rss-proc-limit) RSS_PROC_LIMIT_KB="${2:-}"; shift 2 ;;
    --version)        banner; exit 0 ;;
    --dry-run)   DRY_RUN=1; shift ;;
    --self-test) SELF_TEST=1; shift ;;
    --classify)  CLASSIFY=1; shift ;;
    --classify-only) CLASSIFY=1; CLASSIFY_ONLY=1; shift ;;
    --against)   AGAINST="${2:-}"; shift 2 ;;
    -h|--help)   usage ;;
    *)           echo "triad.sh: unknown argument '$1'" >&2; usage ;;
  esac
done

LANE_GATES="$GATES"                            # what the LANE asked for, kept

say() { echo "[$(date +%H:%M:%S)] $*"; }
die() { echo "triad.sh: $*" >&2; exit 2; }

# ------------------------------------------------------- ticket timestamps
# Tickets sort LEXICOGRAPHICALLY, so the timestamp must be fixed width.  BSD
# `date` has no %N and prints a literal N; a lane that does not notice gets a
# queue that does not order.  Normalise to 19 digits from whatever source
# works, and refuse rather than enqueue an unsortable ticket.
now_ns() {
  local t
  t="$(date +%s%N 2>/dev/null)"
  case "$t" in
    ''|*[!0-9]*) t="$(python3 -c 'import time;print(time.time_ns())' 2>/dev/null)" ;;
  esac
  case "$t" in
    ''|*[!0-9]*) t="$(date +%s 2>/dev/null)000000000" ;;
  esac
  case "$t" in
    ''|*[!0-9]*) return 1 ;;
  esac
  printf '%019d\n' "$t"
}

# ------------------------------------------------------------- parentage
# base rule 6: kills by PARENTAGE only.  `ps -eo pid,ppid` once, then a
# breadth-first walk — so a lane never touches a sibling lane's chain, and
# never misses a grandchild the way `pgrep -P <pid>` does.
descendants() {                       # descendants <root-pid>  -> pids, one per line
  local root="$1"
  ps -eo pid,ppid 2>/dev/null | awk -v root="$root" '
    NR > 1 { child[$2] = child[$2] " " $1 }
    END {
      n = 1; q[1] = root
      for (i = 1; i <= n; i++) {
        split(child[q[i]], kids, " ")
        for (k in kids) if (kids[k] != "") { n++; q[n] = kids[k]; print kids[k] }
      }
    }'
}

rss_rows() {                          # -> "<pid> <rss_kb>" for our descendants
  local p r
  for p in $(descendants $$); do
    r="$(ps -o rss= -p "$p" 2>/dev/null | tr -d ' ')"
    case "$r" in ''|*[!0-9]*) continue ;; esac
    echo "$p $r"
  done
}

# A16, and the reason it is a FUNCTION: the old guard's decision lived inside
# a background subshell, where it could not be tested and was wrong in three
# ways at once.  This is pure — rows on stdin, a verdict on stdout — so
# `--self-test` exercises the exact code the tenure runs.
rss_verdict() {                       # proc_limit chain_limit " excl pids "  < rows
  awk -v pl="$1" -v cl="$2" -v excl="$3" '
    { if (index(excl, " " $1 " ") > 0) next          # never judge ourselves
      total += $2
      if ($2 > worst) { worst = $2; wpid = $1 } }
    END {
      if (worst > pl) { printf "proc %s %d\n", wpid, worst; exit }
      if (total > cl) { printf "chain %d\n", total; exit }
      print "ok" }'
}

WATCHDOG=""
GUARD_PIDFILE=""
watchdog_stop() {
  [ -n "$WATCHDOG" ] || return 0
  kill "$WATCHDOG" 2>/dev/null
  WATCHDOG=""
}

# A16: RESTARTED PER ATTEMPT.  The old guard was single-shot — it killed the
# chain INCLUDING ITSELF, so a resource kill left attempt 2 running with no
# guard at all.
watchdog_start() {
  watchdog_stop
  (
    while kill -0 $$ 2>/dev/null; do
      sleep 20
      self="$(cat "$GUARD_PIDFILE" 2>/dev/null)"
      case "$self" in ''|*[!0-9]*) self=0 ;; esac
      excl=" $self $(descendants "$self" 2>/dev/null | tr '\n' ' ') "
      verdict="$(rss_rows | rss_verdict "$RSS_PROC_LIMIT_KB" "$RSS_CHAIN_LIMIT_KB" "$excl")"
      case "$verdict" in
        proc\ *)
          vp="$(printf '%s' "$verdict" | awk '{print $2}')"
          vr="$(printf '%s' "$verdict" | awk '{print $3}')"
          echo "RSS KILL LINE (A16, per-process): pid $vp at $((vr / 1024)) MB > $((RSS_PROC_LIMIT_KB / 1024)) MB — killing THAT process" >&2
          kill -9 "$vp" 2>/dev/null ;;
        chain\ *)
          vt="$(printf '%s' "$verdict" | awk '{print $2}')"
          echo "RSS KILL LINE (A16, chain): own chain at $((vt / 1024)) MB > $((RSS_CHAIN_LIMIT_KB / 1024)) MB — killing OUR chain" >&2
          for p in $(descendants $$); do
            case "$excl" in *" $p "*) continue ;; esac
            kill -9 "$p" 2>/dev/null
          done ;;
      esac
    done
  ) & WATCHDOG=$!
  printf '%s\n' "$WATCHDOG" > "$GUARD_PIDFILE" 2>/dev/null
}

kill_own_chain() {                    # SIGTERM then SIGKILL, ours only
  local sig="${1:-TERM}" p
  for p in $(descendants $$); do kill "-$sig" "$p" 2>/dev/null; done
}

# -------------------------------------------------- two-part staleness test
# §7.1 rule 5: the owner pid is alive AND a live Lean job descends from it.
# BOTH parts, always.  The failure direction is what makes this a rule — a
# broken liveness check does not fall back to caution, it falls forward into
# reclaiming a lock somebody is holding.  So: unparseable owner => NOT stale.
lock_is_stale() {                     # 0 = stale (reclaimable), 1 = live/unknown
  local owner pid kid
  owner="$(cat "$LOCK/owner" 2>/dev/null)" || return 1
  [ -n "$owner" ] || return 1
  pid="$(printf '%s' "$owner" | awk '{print $NF}')"      # A5: pid LAST
  case "$pid" in ''|*[!0-9]*) return 1 ;; esac           # unparseable => live
  kill -0 "$pid" 2>/dev/null && return 1                 # part 1: pid alive
  for kid in $(descendants "$pid"); do                   # part 2: a live Lean job
    case "$(ps -o comm= -p "$kid" 2>/dev/null)" in
      *lean*|*lake*|*gprbuild*) return 1 ;;
    esac
  done
  return 0
}

sweep_stale_tickets() {
  # A8: the verdict comes from ONE atomic re-read immediately before the rm.
  local t p
  for t in $(ls "$QUEUE" 2>/dev/null); do
    p="$(printf '%s' "$t" | cut -d- -f2)"
    case "$p" in ''|*[!0-9]*) continue ;; esac
    kill -0 "$p" 2>/dev/null && continue
    # Re-read NOW: the ticket may have been removed, or the pid recycled,
    # since the listing above.  Both parts again, immediately before the rm.
    [ -e "$QUEUE/$t" ] || continue
    kill -0 "$p" 2>/dev/null && continue
    rm -f "$QUEUE/$t" && say "reaped stale ticket $t (pid $p dead)"
  done
}

# =================================================== THE DIFF CLASSIFIER
# Pure functions over PATHS — no git, no filesystem except the two lookups
# `tier_targets` and the Examples reachability probe need — so `--self-test`
# exercises every branch without a repository and without Lean.
#
# The direction of every doubt is fixed: an unrecognized path ESCALATES.  A
# classifier that guesses "probably docs" and is wrong ships an unbuilt
# landing; one that guesses "probably spine" and is wrong costs a build.
# Those are not symmetric, and lean-tier's own corner table minted the rule
# the expensive way: a path-based classifier filed all seven `TrProj.*`
# lemmas as "other" because they lived in a generically-named file, and the
# census's largest cluster went invisible in its own summary
# (docs/backlog/lean-tier.md 2026-08-22-lean-tier-2).  A path rule that does
# not recognize something must SAY SO, not absorb it into a bucket.

CLASS_RANK=0            # 1 docs, 2 tier, 3 spine — the MAX over the diff
CLASS_TIERS=""          # tier keys touched, normalised across the two trees
CLASS_UNKNOWN=""        # paths no rule matched (escalated to spine, listed)
CLASS_NOTES=""          # one line per thing the lane should know
BUILD_TARGETS=""        # empty == full `lake build` (every default target)

class_name() {          # rank -> word
  case "${1:-0}" in
    3) echo spine ;;
    2) echo tier ;;
    1) echo docs ;;
    *) echo none ;;
  esac
}

add_build_target() {    # UNION, never replace — a lane can always build more
  local t
  for t in $BUILD_TARGETS; do [ "$t" = "$1" ] && return 0; done
  BUILD_TARGETS="${BUILD_TARGETS:+$BUILD_TARGETS }$1"
}

add_note() { case "$CLASS_NOTES" in *"$1"*) ;; *) CLASS_NOTES="${CLASS_NOTES}${1}
" ;; esac; }

# ---- what can change elaboration, and what cannot
classify_path() {       # path -> docs | tier | spine
  case "$1" in
    # The spine: everything that invalidates the whole graph.
    LeanModels.lean|Main.lean|lakefile.toml|lake-manifest.json|lean-toolchain) echo spine ;;
    LeanModels/Core/*|vendor/*)                     echo spine ;;
    # The SHARED harness — the differential every tier is judged by.
    harness/diff_test.py|harness/cases.json)        echo spine ;;
    # Tier-local: a model directory, or the Examples that exercise it.
    LeanModels/*|Examples/*)                        echo tier ;;
    # Prose, instruments and tooling: none of it reaches the elaborator.
    docs/*|notebooks/*|tools/*|harness/*|.github/*) echo docs ;;
    .gitignore|*.md)                                echo docs ;;
    # A `.lean` file that belongs to no library still is not nothing.
    *.lean)                                         echo spine ;;
    # UNRECOGNIZED.  Escalate and name it; never absorb it.
    *)                                              echo spine ;;
  esac
}

is_recognized() {       # 0 when a rule (not the catch-all) matched the path
  case "$1" in
    LeanModels.lean|Main.lean|lakefile.toml|lake-manifest.json|lean-toolchain) return 0 ;;
    LeanModels/*|Examples/*|vendor/*|docs/*|notebooks/*|tools/*|harness/*) return 0 ;;
    .github/*|.gitignore|*.md|*.lean) return 0 ;;
    *) return 1 ;;
  esac
}

# `Examples/<dir>` and `LeanModels/<Tier>` are two names for one tier, and the
# classifier must not report them as two.  The map is explicit because it is
# not derivable: `system-verilog` -> `Sv`, and `mixed-signal` spans two tiers
# (its proofs import both `LeanModels.Circuit.MixedSignal` and
# `LeanModels.Python.Surface`).
example_dir_tiers() {   # Examples/<dir> -> zero or more LeanModels tier keys
  case "$1" in
    ada)            echo Ada ;;
    c)              echo C ;;
    es)             echo Es ;;
    python)         echo Python ;;
    spice)          echo Spice ;;
    system-verilog) echo Sv ;;
    verilog-a)      echo VerilogA ;;
    mixed-signal)   echo Circuit Python ;;
    *)              echo "" ;;        # a corpus with no model tier yet (go)
  esac
}

tiers_of() {            # path -> the tier keys it belongs to ('' = not tier-local)
  local d
  case "$1" in
    LeanModels/Core/*) echo "" ;;
    LeanModels/*/*)    d="${1#LeanModels/}"; echo "${d%%/*}" ;;
    LeanModels/*.lean) d="${1#LeanModels/}"; echo "${d%.lean}" ;;
    Examples/*/*)      d="${1#Examples/}";  example_dir_tiers "${d%%/*}" ;;
    *)                 echo "" ;;
  esac
}

module_of() {           # path.lean -> dotted module, or '' if any component
                        # is not a plain Lean identifier (`«mixed-signal»`
                        # needs guillemets, and this script does not guess a
                        # target spelling it cannot verify without Lean).
  local p="${1%.lean}" c out=""
  local oldifs="$IFS"; IFS=/
  for c in $p; do
    IFS="$oldifs"
    case "$c" in
      ''|*[!A-Za-z0-9_]*) echo ""; return 1 ;;
      [0-9]*)             echo ""; return 1 ;;
    esac
    out="${out:+$out.}$c"
    IFS=/
  done
  IFS="$oldifs"
  echo "$out"
}

# ---- REACHABILITY, for the non-Lean fixtures under `Examples/`
# The Go lane measured the hole in the first cut of this rule: their
# `Examples/go/<case>/<case>.go` classified `tier` although it is PROVABLY
# invisible to lake — nothing imports it, the Examples glob matches Lean
# MODULE names, and a `.go` file has none.  The distinguishing property is
# not the extension: `Examples/c/sunfish/sunfish.json` must STAY tier-local,
# because a `.lean` ingests it.  The property is REACHABILITY.
#
# And reachability is not "reachable from a Lean module" either, which is
# where this lane's own first cut would have been wrong.  Measured over the
# 200 non-Lean fixtures in the tree: grepping `*.lean` alone leaves 79
# unreferenced — but 40 of those are `Examples/python/**` fixtures named by
# `harness/cases.json`, which is precisely what `harness/diff_test.py` reads.
# Downgrading them to `docs` would have SKIPPED THE DIFFERENTIAL for a change
# that is an input to it.  So the referencing set is what runs UNDER THE
# TENURE: the Lean modules AND the gate corpora.  With both, 160 fixtures are
# reachable and 40 are provably invisible — the `.go` case among them.
#
# The probe is an approximation (a bare basename can collide), and its errors
# are steered: a false hit keeps a file tier-local, which costs a build; a
# false miss would skip one.  So ANY DOUBT resolves to REACHABLE.
#
# And the doubt test is STRUCTURAL, not an exit code.  The self-test caught
# this: pointed at an unreadable root, this grep exits **1 — "not found" —
# where the same grep exits 2 for a bare missing operand, so "the probe could
# not run" is INDISTINGUISHABLE from "nothing references it" by status alone.
# Trusting the code would have silently downgraded every fixture whenever the
# root was wrong.  So the root is checked before any status is believed —
# §7.1 rule 5's lesson in another costume: a broken liveness check does not
# fall back to caution, it falls FORWARD.
example_fixture_is_reachable() {   # path -> 0 reachable, 1 provably invisible
  local p="$1" base root rc
  root="${LS_GREP_ROOT:-$CLONE}"
  base="${p##*/}"
  # DOUBT, structurally: no readable root means no probe, and no probe means
  # reachable.  Never infer "unreferenced" from a search that did not happen.
  [ -d "$root" ] && [ -r "$root" ] || return 0
  if git -C "$root" rev-parse --git-dir >/dev/null 2>&1; then
    git -C "$root" grep -q -I -F --untracked -e "$p" -e "$base" \
        -- '*.lean' 'harness/*.json' >/dev/null 2>&1
    rc=$?
  else
    grep -rqI -F --include='*.lean' -e "$p" -e "$base" "$root" 2>/dev/null
    rc=$?
    if [ "$rc" != "0" ] && [ -d "$root/harness" ]; then
      grep -rqI -F --include='*.json' -e "$p" -e "$base" "$root/harness" 2>/dev/null
      rc=$?
    fi
  fi
  case "$rc" in
    0) return 0 ;;                  # a Lean module or a gate corpus names it
    1) return 1 ;;                  # nothing under the tenure can see it
    *) return 0 ;;                  # a status we cannot read: DOUBT -> reachable
  esac
}

is_example_fixture() {  # a non-Lean Examples file the LAKEFILE does not name
  case "$1" in
    Examples/*.lean)                                   return 1 ;;
    Examples/spice/*.cir)                              return 1 ;;
    Examples/verilog-a/*.va|Examples/verilog-a/*.json) return 1 ;;
    Examples/*/*)                                      return 0 ;;
    *)                                                 return 1 ;;
  esac
}

path_targets() {        # path -> build targets it makes owed ('' = none)
  local m
  case "$1" in
    LeanModels/*.lean)
      m="$(module_of "$1")"
      if [ -n "$m" ]; then echo "$m"; else echo "__ESCALATE__"; fi ;;
    Examples/*.lean)
      m="$(module_of "$1")"
      # A hyphenated example directory is a real module with a real name —
      # `Examples.«system-verilog».toggle.proof` — but this script would be
      # GUESSING the CLI spelling, and A11 forbids running Lean to find out.
      # Widen to the library instead: less scope, zero invention.
      if [ -n "$m" ]; then echo "$m"; else echo "Examples"; fi ;;
    # `[[input_dir]]` in lakefile.toml: these files ARE build inputs, and
    # that is a fact of the lakefile rather than a heuristic — no probe.
    Examples/spice/*.cir)                       echo "Examples" ;;
    Examples/verilog-a/*.va|Examples/verilog-a/*.json) echo "Examples" ;;
    # Any OTHER Examples fixture only reaches here once the probe has found
    # it reachable, and the library that reads it must rebuild to see it.
    Examples/*)                                 echo "Examples" ;;
    *) echo "" ;;
  esac
}

tier_targets() {        # tier key -> its root module, when the tier has one
  [ -f "$CLONE/LeanModels/$1.lean" ] && echo "LeanModels.$1"
  return 0
}

classify_list() {       # reads paths on stdin; sets the CLASS_* globals
  CLASS_RANK=0; CLASS_TIERS=""; CLASS_UNKNOWN=""; CLASS_NOTES=""; BUILD_TARGETS=""
  local p c rank t tt seen
  while IFS= read -r p; do
    [ -n "$p" ] || continue
    c="$(classify_path "$p")"
    # A non-Lean fixture under Examples/ is tier-local only if something that
    # RUNS UNDER THE TENURE can see it.  The line SAYS SO when it is not, so
    # the coverage statement carries the reasoning and not just the verdict.
    if [ "$c" = "tier" ] && is_example_fixture "$p"; then
      if ! example_fixture_is_reachable "$p"; then
        c="docs"
        add_note "'$p' is a non-Lean fixture, unreferenced by any Lean module or gate corpus — invisible to lake, classified docs"
      fi
    fi
    case "$c" in spine) rank=3 ;; tier) rank=2 ;; *) rank=1 ;; esac
    [ "$rank" -gt "$CLASS_RANK" ] && CLASS_RANK="$rank"
    is_recognized "$p" || CLASS_UNKNOWN="${CLASS_UNKNOWN:+$CLASS_UNKNOWN }$p"
    # A path classified `docs` contributes no tier and no target — including
    # one the probe just downgraded.  Otherwise the scope would still carry a
    # file nothing under the tenure reads.
    if [ "$c" != "docs" ]; then
    for t in $(tiers_of "$p"); do
      seen=0
      for tt in $CLASS_TIERS; do [ "$tt" = "$t" ] && seen=1; done
      [ "$seen" = "0" ] && CLASS_TIERS="${CLASS_TIERS:+$CLASS_TIERS }$t"
    done
    for t in $(path_targets "$p"); do
      if [ "$t" = "__ESCALATE__" ]; then
        CLASS_RANK=3
        add_note "a module name could not be derived from '$p' — escalated to a FULL build"
      else
        add_build_target "$t"
      fi
    done
    fi
    case "$p" in
      docs/*.lean|harness/*.lean|tools/*.lean)
        add_note "'$p' is Lean but no lake target — running it is still Lean execution (A11): pass --gates" ;;
    esac
  done
  # A tier's root module imports its submodules, so building it covers the
  # tier's DEPENDENTS as well as the touched module's dependencies.  Tiers
  # without a root (`Sv`, `Rv`, `Core`) have no such module and get none.
  for t in $CLASS_TIERS; do
    for tt in $(tier_targets "$t"); do add_build_target "$tt"; done
  done
  [ "$CLASS_RANK" = "3" ] && BUILD_TARGETS=""    # spine == every default target
  return 0
}

gate_floor() {          # class -> the gates this landing owes at minimum
  case "$1" in
    docs) echo 'python3 tools/docs_check.py' ;;
    *)    echo 'python3 tools/docs_check.py; python3 harness/diff_test.py' ;;
  esac
}

# ---- THE DEFAULT GATE SET IS NARROWER THAN SOME RETIRED LANE SCRIPTS
# The ES lane found this by READING ITS OWN LOG rather than trusting it: this
# script's default gates are `docs_check; diff_test`, and `script_corpus` is
# not among them — though the `es-build.sh` it retired ran all three.  The
# default is not wrong (gates are a lane's business, and the script takes
# `--gates`), but a lane migrating to the shared wrapper INHERITS A NARROWER
# GATE SET SILENTLY, and the failure mode is a landing that reads green
# against fewer checks than the one before it.  In that lane's own words:
# "which no amount of care at the build itself would catch."
#
# So it is not caught, it is ANNOUNCED — every run that did not choose its
# own gates says which ones it is about to run, and names the trap.
# (docs/backlog/es.md 2026-08-22-es-1.)
GATE_NOTICE_DONE=0

gate_names() {          # a gate list -> the script names in it, for reading
  printf '%s' "$1" | awk -F';' '{
    out = ""
    for (i = 1; i <= NF; i++) {
      n = split($i, w, /[ \t]+/)
      for (j = 1; j <= n; j++) if (w[j] ~ /\.(py|sh)$/) {
        m = split(w[j], parts, "/"); b = parts[m]
        sub(/\.(py|sh)$/, "", b)
        out = out (out == "" ? "" : ", ") b
      }
    }
    print (out == "" ? $0 : out)
  }'
}

gate_notice() {         # $1 = the gate list in use, $2 = the lane's own --gates
  [ -n "$2" ] && return 0        # the lane chose its gates; it needs no warning
  [ "$GATE_NOTICE_DONE" = "1" ] && return 0
  GATE_NOTICE_DONE=1
  echo ""
  echo "  !! DEFAULT GATES: $(gate_names "$1") (minimal).  A lane migrating from a"
  echo "     private script should pass --gates matching what it RETIRED."
  echo "     es-build.sh also ran script_corpus; a lane that retires its script and"
  echo "     takes this default lands GREEN AGAINST FEWER CHECKS THAN THE ONE"
  echo "     BEFORE IT — which no amount of care at the build itself would catch."
  echo "     (docs/backlog/es.md 2026-08-22-es-1)"
  echo ""
}

tenure_needed() {       # class, lane's own --gates -> yes | no
  # A11: the lock covers ALL Lean execution.  docs_check runs none — it
  # shells out to nothing — so a docs-only landing owes no tenure.  A lane
  # that brought its OWN gates keeps the tenure, because this script cannot
  # know whether one of them starts a Lean process.  Never downgrade.
  case "$1" in
    docs) if [ -n "$2" ]; then echo yes; else echo no; fi ;;
    *)    echo yes ;;
  esac
}

coverage_statement() {  # class -> what a green from this run is EVIDENCE OF
  case "$1" in
    docs) echo "docs-only: NO Lean was elaborated, so a green here is evidence about the prose, its citations and its paths — and about NOTHING in the model." ;;
    tier) echo "scoped: a green covers the modules named above and everything they IMPORT. It does NOT cover modules that import THEM, nor any untouched tier, and it is not evidence about master beyond that scope." ;;
    spine) echo "full: a green covers every default target at this sha." ;;
    *)    echo "no files classified — this run measured nothing." ;;
  esac
}

# --------------------------------------------------------------- self-test
# §5.4's law, pointed at this script: every refusal path RUN, not admired.
# No Lean, no lock, no queue outside the temp dir it creates.
if [ "$SELF_TEST" = "1" ]; then
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/triad-selftest.XXXXXX")" || die "no temp dir"
  trap 'rm -rf "$tmp"' EXIT
  ok=0; bad=0
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; \
            else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }

  t1="$(now_ns)"; t2="$(now_ns)"
  check "ticket stamps are 19 digits"        "${#t1}" "19"
  mono=no; if [ "$t2" -ge "$t1" ]; then mono=yes; fi
  check "ticket stamps are non-decreasing"   "$mono" "yes"
  # The width matters more than the clock: `sort` on the queue is
  # lexicographic, so a 10-digit fallback mixed with a 19-digit stamp would
  # order the queue backwards.  Both sources go through printf %019d.
  check "stamps sort lexicographically"      "$(printf '%s\n%s\n' "$t2" "$t1" | sort | head -1)" "$t1"

  export LS_LOCK="$tmp/lock" LS_QUEUE="$tmp/queue"
  LOCK="$LS_LOCK"; QUEUE="$LS_QUEUE"; mkdir -p "$QUEUE"

  mkdir "$LOCK"
  printf 'other-lane %s\n' "999999" > "$LOCK/owner"
  check "a dead owner with no Lean child IS stale" "$(lock_is_stale && echo stale)" "stale"
  printf 'go-lane lake pid 43341 (cwd /x/lean-go)\n' > "$LOCK/owner"
  check "an UNPARSEABLE owner is never stale"      "$(lock_is_stale && echo stale)" ""
  printf 'me %s\n' "$$" > "$LOCK/owner"
  check "a live owner is never stale"              "$(lock_is_stale && echo stale)" ""

  if ( set -C; printf 'second %s\n' "$$" > "$LOCK/owner" ) 2>/dev/null; then
    second_write=wrote
  else
    second_write=refused
  fi
  check "A4: a second owner write FAILS" "$second_write" "refused"
  check "A4: the first owner survived"   "$(awk '{print $1}' "$LOCK/owner")" "me"

  check "A5: pid is the LAST field"    "$(awk '{print $NF}' "$LOCK/owner")" "$$"
  rm -rf "$LOCK"

  : > "$QUEUE/00000000000000000001-999999-dead"
  : > "$QUEUE/00000000000000000002-$$-live"
  sweep_stale_tickets
  check "a dead lane's ticket is reaped" "$(ls "$QUEUE" | wc -l | tr -d ' ')" "1"
  check "a live lane's ticket survives"  "$(ls "$QUEUE")" "00000000000000000002-$$-live"

  check "descendants(self) excludes self" "$(descendants $$ | grep -c "^$$\$")" "0"

  # ---- A16: the RSS lines, and the three properties the old guard lacked
  echo "  -- rss guard (A16)"
  # THE REGRESSION THAT MINTED THE AMENDMENT.  One honest `lean` worker was
  # measured at 3251 MB.  Under A11's single 3 GB CHAIN cap that build was
  # killed for behaving; under A16 it survives, and this row is the test.
  check "a 3251 MB honest worker SURVIVES" \
        "$(printf '4242 3329024\n' | rss_verdict "$RSS_PROC_LIMIT_KB" "$RSS_CHAIN_LIMIT_KB" " ")" "ok"
  check "  ...and would have died under the old 3 GB chain cap" \
        "$(printf '4242 3329024\n' | rss_verdict 3145728 3145728 " " | awk '{print $1}')" "proc"

  # PROPERTY 1 — the line is PER-PROCESS.
  check "one process over 5 GB is killed BY ITSELF" \
        "$(printf '10 1000\n11 5242881\n12 2000\n' | rss_verdict "$RSS_PROC_LIMIT_KB" "$RSS_CHAIN_LIMIT_KB" " ")" "proc 11 5242881"
  check "a process exactly AT the line is not over it" \
        "$(printf '11 5242880\n' | rss_verdict "$RSS_PROC_LIMIT_KB" "$RSS_CHAIN_LIMIT_KB" " ")" "ok"

  # PROPERTY 2 — the CHAIN line is the secondary, and it still fires.
  check "four honest workers over 10 GB trip the chain" \
        "$(printf '10 3000000\n11 3000000\n12 3000000\n13 3000000\n' | rss_verdict "$RSS_PROC_LIMIT_KB" "$RSS_CHAIN_LIMIT_KB" " ")" "chain 12000000"
  check "three of the same do NOT" \
        "$(printf '10 3000000\n11 3000000\n12 3000000\n' | rss_verdict "$RSS_PROC_LIMIT_KB" "$RSS_CHAIN_LIMIT_KB" " ")" "ok"
  check "per-process outranks chain when both trip" \
        "$(printf '10 9000000\n11 9000000\n' | rss_verdict "$RSS_PROC_LIMIT_KB" "$RSS_CHAIN_LIMIT_KB" " " | awk '{print $1}')" "proc"

  # PROPERTY 3 — THE GUARD IS NOT IN ITS OWN KILL SET.  The old guard killed
  # the chain including itself, so attempt 2 ran unguarded.
  check "an EXCLUDED pid is never the victim" \
        "$(printf '99 9999999\n' | rss_verdict "$RSS_PROC_LIMIT_KB" "$RSS_CHAIN_LIMIT_KB" " 99 ")" "ok"
  check "an excluded pid does not count toward the chain" \
        "$(printf '99 9999999\n10 100\n' | rss_verdict "$RSS_PROC_LIMIT_KB" "$RSS_CHAIN_LIMIT_KB" " 99 ")" "ok"
  check "but its SIBLINGS are still judged" \
        "$(printf '99 9999999\n10 5242881\n' | rss_verdict "$RSS_PROC_LIMIT_KB" "$RSS_CHAIN_LIMIT_KB" " 99 ")" "proc 10 5242881"

  # PROPERTY 3b — restartability, and the pidfile the exclusion reads.
  GUARD_PIDFILE="$tmp/guard.pid"
  RSS_PROC_LIMIT_KB=999999999 RSS_CHAIN_LIMIT_KB=999999999 watchdog_start
  w1="$WATCHDOG"
  check "watchdog_start yields a live pid"  "$(kill -0 "$w1" 2>/dev/null && echo live)" "live"
  check "  ...published for its own exclusion" "$(cat "$GUARD_PIDFILE")" "$w1"
  RSS_PROC_LIMIT_KB=999999999 RSS_CHAIN_LIMIT_KB=999999999 watchdog_start
  w2="$WATCHDOG"
  check "a RESTART replaces the guard"      "$( [ "$w1" != "$w2" ] && echo new)" "new"
  check "  ...and the old one is gone"      "$(kill -0 "$w1" 2>/dev/null && echo live)" ""
  watchdog_stop
  check "watchdog_stop clears it"           "$WATCHDOG" ""
  check "  ...and the process is gone"      "$(sleep 1; kill -0 "$w2" 2>/dev/null && echo live)" ""

  check "the banner names the protocol level" \
        "$(banner | grep -c 'protocol base 1-6 + A4-A13 + A16')" "1"

  # ------------------------------------------------- the diff classifier
  # Every class EXECUTED against a real path list, not described.  These run
  # in THIS shell (never under `$( )`), because `classify_list` reports
  # through globals and a subshell would swallow them.
  echo "  -- classifier"
  cls() { classify_list <<< "$(printf '%s\n' "$@")"; }

  cls docs/backlog/qol.md README.md tools/diagnose.sh
  check "docs-only diff -> docs"            "$(class_name "$CLASS_RANK")" "docs"
  check "docs-only builds nothing"          "$BUILD_TARGETS" ""
  check "docs-only owes NO tenure"          "$(tenure_needed docs "")" "no"
  check "docs-only gates: docs_check alone" "$(gate_floor docs)" "python3 tools/docs_check.py"

  cls LeanModels/Sv/Obs.lean Examples/system-verilog/toggle/proof.lean
  check "tier-local diff -> tier"           "$(class_name "$CLASS_RANK")" "tier"
  check "the two trees name ONE tier"       "$CLASS_TIERS" "Sv"
  check "the touched module is a target"    "$BUILD_TARGETS" "LeanModels.Sv.Obs Examples"
  check "a rootless tier adds no root"      "$(tier_targets Sv)" ""
  check "tier owes a tenure"                "$(tenure_needed tier "")" "yes"

  cls LeanModels/Python/Surface.lean
  check "a tier WITH a root adds it"        "$BUILD_TARGETS" "LeanModels.Python.Surface LeanModels.Python"

  cls LeanModels/Core/Basic.lean
  check "Core -> spine"                     "$(class_name "$CLASS_RANK")" "spine"
  check "spine builds EVERY default target" "$BUILD_TARGETS" ""
  check "Core belongs to no tier"           "$CLASS_TIERS" ""

  cls harness/diff_test.py
  check "the SHARED harness -> spine"       "$(class_name "$CLASS_RANK")" "spine"
  cls harness/wasm_sorry_census.py
  check "a lane instrument -> docs"         "$(class_name "$CLASS_RANK")" "docs"
  cls lakefile.toml
  check "the lakefile -> spine"             "$(class_name "$CLASS_RANK")" "spine"

  cls docs/family-architecture.md LeanModels/C/Eval.lean
  check "MIXED docs+tier -> tier"           "$(class_name "$CLASS_RANK")" "tier"
  cls docs/family-architecture.md LeanModels/C/Eval.lean LeanModels.lean
  check "MIXED docs+tier+spine -> spine"    "$(class_name "$CLASS_RANK")" "spine"

  cls LeanModels/C/Eval.lean LeanModels/Ada/Eval.lean
  check "two tiers stay tier"               "$(class_name "$CLASS_RANK")" "tier"
  check "two tiers, both in scope"          "$CLASS_TIERS" "C Ada"

  cls Makefile
  check "an UNRECOGNIZED path -> spine"     "$(class_name "$CLASS_RANK")" "spine"
  check "and it is NAMED, not absorbed"     "$CLASS_UNKNOWN" "Makefile"

  cls Examples/spice/rc/net.cir
  check "an input_dir file is a build input" "$BUILD_TARGETS" "Examples LeanModels.Spice"

  check "module_of refuses a hyphen"        "$(module_of Examples/system-verilog/x.lean)" ""
  check "module_of derives a plain path"    "$(module_of LeanModels/Sv/Obs.lean)" "LeanModels.Sv.Obs"
  cls LeanModels/Py-thon/x.lean
  check "an underivable module escalates"   "$(class_name "$CLASS_RANK")" "spine"

  cls docs/mvcgen-pilot.lean
  check "a doc's .lean is still docs"       "$(class_name "$CLASS_RANK")" "docs"
  case "$CLASS_NOTES" in *A11*) n=said ;; *) n=silent ;; esac
  check "  ...but A11 is said out loud"     "$n" "said"

  # ---- the Examples reachability probe (the Go lane's measurement)
  # A fixture TREE, so both directions are exercised for real: a `.lean` that
  # names one fixture, a gate corpus that names another, and one file that
  # nothing names at all.
  fx="$tmp/fixroot"
  mkdir -p "$fx/Examples/c/sunfish" "$fx/Examples/go/rung1" \
           "$fx/Examples/python/exc_lab" "$fx/harness"
  printf 'import LeanModels.C\n-- ingests Examples/c/sunfish/sunfish.json\n' \
         > "$fx/Examples/c/sunfish/guards.lean"
  : > "$fx/Examples/c/sunfish/sunfish.json"
  : > "$fx/Examples/go/rung1/rung1.go"
  : > "$fx/Examples/python/exc_lab/exc_lab.py"
  printf '{"cases": [{"file": "Examples/python/exc_lab/exc_lab.py"}]}\n' \
         > "$fx/harness/cases.json"
  LS_GREP_ROOT="$fx"

  cls Examples/c/sunfish/sunfish.json
  check "a REFERENCED fixture (.lean names it) -> tier" "$(class_name "$CLASS_RANK")" "tier"
  check "  ...and it owes the Examples library"         "$BUILD_TARGETS" "Examples LeanModels.C"

  cls Examples/python/exc_lab/exc_lab.py
  check "a GATE-CORPUS fixture -> tier"                 "$(class_name "$CLASS_RANK")" "tier"

  cls Examples/go/rung1/rung1.go
  check "an UNREFERENCED fixture -> docs"               "$(class_name "$CLASS_RANK")" "docs"
  check "  ...contributing no tier"                     "$CLASS_TIERS" ""
  check "  ...and no build target"                      "$BUILD_TARGETS" ""
  case "$CLASS_NOTES" in *"unreferenced by any Lean module or gate corpus"*) n=said ;; *) n=silent ;; esac
  check "  ...and the line SAYS WHY"                    "$n" "said"

  cls Examples/c/sunfish/guards.lean
  check "a .lean under Examples is tier, no probe"      "$(class_name "$CLASS_RANK")" "tier"
  cls Examples/spice/rc/net.cir
  check "an input_dir fixture is tier without a probe"  "$(class_name "$CLASS_RANK")" "tier"

  cls Examples/go/rung1/rung1.go Examples/c/sunfish/sunfish.json
  check "MIXED invisible+reachable -> tier"             "$(class_name "$CLASS_RANK")" "tier"
  check "  ...scoped to the reachable one's tier"       "$CLASS_TIERS" "C"

  LS_GREP_ROOT="$tmp/does-not-exist"
  cls Examples/go/rung1/rung1.go
  check "DOUBT (no tree to probe) -> stays tier"        "$(class_name "$CLASS_RANK")" "tier"
  LS_GREP_ROOT=""

  # ---- the default-gate-set notice (the ES lane's migration finding)
  check "gate names read as script names" "$(gate_names "$(gate_floor tier)")" "docs_check, diff_test"
  check "the docs floor names one gate"   "$(gate_names "$(gate_floor docs)")" "docs_check"
  GATE_NOTICE_DONE=0
  check "a DEFAULT invocation warns"      "$(gate_notice "$(gate_floor tier)" "" | grep -c 'DEFAULT GATES')" "1"
  GATE_NOTICE_DONE=0
  check "  ...and names what to do"       "$(gate_notice "$(gate_floor tier)" "" | grep -c -- '--gates matching what it RETIRED')" "1"
  GATE_NOTICE_DONE=0
  check "  ...and cites the incident"     "$(gate_notice "$(gate_floor tier)" "" | grep -c '2026-08-22-es-1')" "1"
  GATE_NOTICE_DONE=0
  check "a lane's OWN --gates does not warn" "$(gate_notice "$(gate_floor tier)" 'python3 harness/script_corpus.py')" ""
  GATE_NOTICE_DONE=0
  gate_notice "$(gate_floor tier)" "" > /dev/null
  check "the notice is printed ONCE per run" "$(gate_notice "$(gate_floor tier)" "" | grep -c 'DEFAULT GATES')" "0"
  GATE_NOTICE_DONE=0

  check "NEVER DOWNGRADE: lane gates keep the tenure" "$(tenure_needed docs 'python3 x.py')" "yes"
  check "tier gates include the differential" \
        "$(gate_floor tier)" "python3 tools/docs_check.py; python3 harness/diff_test.py"

  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

# ------------------------------------------------------------ preconditions
# --classify-only takes no tenure and writes no owner file, so it needs no
# lane tag.  Everything else does.
if [ "$CLASSIFY_ONLY" = "0" ]; then
  [ -n "$LANE" ] || die "--lane <name> is required (it goes in the owner file)"
fi
case "$LANE" in *[!A-Za-z0-9_.]*) die "--lane must be [A-Za-z0-9_.]+ — '-' would break the ticket parse" ;; esac
[ -d "$CLONE" ] || die "--dir '$CLONE' is not a directory"
cd "$CLONE" || die "cannot cd '$CLONE'"

# A6 / §7.2: the order is stage -> build -> rebase, or rebase -> build.  A
# build reading rebased files against a pre-rebase graph dies with spurious
# `Unknown constant` errors that look exactly like a broken master, and a red
# from a torn tree is not evidence of anything.  Refuse to start in one.
for d in .git/rebase-merge .git/rebase-apply .git/MERGE_HEAD .git/CHERRY_PICK_HEAD; do
  [ -e "$d" ] && die "a rebase/merge is in progress ($d) — finish it BEFORE the build (A6, §7.2)"
done

# ------------------------------------------------------- run the gate list
# Factored out because the docs-only path runs gates WITHOUT a tenure and the
# normal path runs them INSIDE one.  One implementation, two callers.
rc=0
run_gates() {                         # "cmd; cmd" -> sets rc
  local g old_ifs
  old_ifs="$IFS"; IFS=';'
  for g in $1; do
    IFS="$old_ifs"
    g="$(printf '%s' "$g" | sed -e 's/^ *//' -e 's/ *$//')"
    [ -n "$g" ] || { IFS=';'; continue; }
    say "=== gate: $g ==="
    nice -n "$NICE" sh -c "$g" || { rc=1; say "  GATE FAILED: $g"; }
    IFS=';'
  done
  IFS="$old_ifs"
}

# ------------------------------------------------------- --classify (§5.4a)
merge_target_ref() {
  # THE A13 CAVEAT, and it has caught four lanes: a seeded clone inherits the
  # peer's REMOTES, so `origin` can be a stale local bundle and
  # `origin/master` reads days back while `git rev-list HEAD..origin/master`
  # cheerfully reports 0.  Prefer `github/master`; either way, SAY which ref
  # the classification was taken against.
  local r
  for r in github/master origin/master; do
    if git rev-parse --verify --quiet "$r" >/dev/null 2>&1; then echo "$r"; return 0; fi
  done
  echo ""
}

CLASS=""
if [ "$CLASSIFY" = "1" ]; then
  BASE="$AGAINST"
  [ -n "$BASE" ] || BASE="$(merge_target_ref)"
  [ -n "$BASE" ] || die "no merge target (neither github/master nor origin/master) — pass --against <ref>"
  git rev-parse --verify --quiet "$BASE" >/dev/null 2>&1 || die "--against '$BASE' is not a ref in this clone"
  BASE_SHA="$(git rev-parse --short "$BASE" 2>/dev/null || echo unknown)"
  BASE_REMOTE="${BASE%%/*}"
  BASE_URL="$(git remote get-url "$BASE_REMOTE" 2>/dev/null || echo "")"
  case "$BASE_URL" in
    /*|file:*|*.bundle)
      echo "A13 WARNING: remote '$BASE_REMOTE' is a LOCAL path ($BASE_URL) — a seeded clone's" >&2
      echo "             origin is a stale bundle, and comparing against it reads days back." >&2
      echo "             Add the real remote and re-run with --against github/master." >&2 ;;
  esac

  CHANGED="$( { git diff --name-only "$BASE...HEAD" 2>/dev/null
                git diff --name-only --cached 2>/dev/null; } | sort -u )"
  N_CHANGED="$(printf '%s' "$CHANGED" | grep -c . || true)"
  N_UNSTAGED_LEAN="$(git diff --name-only 2>/dev/null | grep -c '\.lean$' || true)"

  classify_list <<< "$CHANGED"
  CLASS="$(class_name "$CLASS_RANK")"

  # A census with nothing to say must not be answered quietly.  An empty diff
  # is not a docs-only landing; it is a classification that MEASURED NOTHING,
  # and the safe direction is the full build.
  if [ "$N_CHANGED" = "0" ]; then
    echo "CLASSIFY: NOTHING STAGED OR COMMITTED against $BASE — this measured nothing." >&2
    [ "$CLASSIFY_ONLY" = "1" ] || { CLASS="spine"; BUILD_TARGETS=""; echo "          falling back to the FULL build (never downgrade)." >&2; }
  fi

  say "CLASSIFICATION: $CLASS"
  printf '  base      %s @ %s%s\n' "$BASE" "$BASE_SHA" "${BASE_URL:+  ($BASE_REMOTE -> $BASE_URL)}"
  printf '  files     %s staged/committed%s\n' "$N_CHANGED" \
         "$( [ "$N_UNSTAGED_LEAN" = "0" ] || printf ' (+%s UNSTAGED .lean NOT classified — stage them or they are not in this green)' "$N_UNSTAGED_LEAN" )"
  printf '  tiers     %s\n' "${CLASS_TIERS:-none}"
  case "$CLASS" in
    docs) printf '  build     none (no Lean)\n' ;;
    none) printf '  build     n/a — nothing was classified\n' ;;
    *)    printf '  build     lake build %s\n' "${BUILD_TARGETS:-<all default targets>}" ;;
  esac
  [ -n "$CLASS_UNKNOWN" ] && printf '  UNKNOWN   %s  <- no path rule matched; escalated, not absorbed\n' "$CLASS_UNKNOWN"
  printf '%s' "$CLASS_NOTES" | while IFS= read -r n; do [ -n "$n" ] && printf '  note      %s\n' "$n"; done

  FLOOR="$(gate_floor "$CLASS")"
  if [ -n "$LANE_GATES" ]; then GATES="$FLOOR; $LANE_GATES"; else GATES="$FLOOR"; fi
  printf '  gates     %s\n' "$GATES"
  printf '  gate set  %s   (the CLASS FLOOR for `%s`)\n' "$(gate_names "$FLOOR")" "$CLASS"
  [ -n "$LANE_GATES" ] && printf '  %s\n' "(the floor, then the lane's own --gates: a classification never REMOVES a gate)"
  printf '  COVERAGE (§5.4a)  %s\n' "$(coverage_statement "$CLASS")"
  gate_notice "$GATES" "$LANE_GATES"

  if [ "$CLASSIFY_ONLY" = "1" ]; then exit 0; fi

  if [ "$(tenure_needed "$CLASS" "$LANE_GATES")" = "no" ]; then
    say "docs-only: NO TENURE TAKEN — nothing here starts a Lean process (A11)"
    gate_notice "$GATES" "$LANE_GATES"
    run_gates "$GATES"
    say "TRIAD DONE (docs-only, no build; gates $( [ "$rc" = 0 ] && echo green || echo RED ))"
    say "COVERAGE (§5.4a): $(coverage_statement "$CLASS")"
    exit "$rc"
  fi
fi

# ------------------------------------------------------------------ enqueue
mkdir -p "$QUEUE" || die "cannot create the queue at $QUEUE"
TS="$(now_ns)" || die "no usable nanosecond clock — tickets would not sort"
TICKET="$TS-$$-$LANE"
OWNER_TAG="$LANE $$"                  # A5 (pid LAST) + A10 (spans the tenure)
HELD=0
WATCHDOG=""

release() {
  local status=$?
  [ -n "$WATCHDOG" ] && kill "$WATCHDOG" 2>/dev/null
  kill_own_chain TERM                 # base rule 6: parentage only, recursive
  sleep 1
  kill_own_chain KILL
  rm -f "$QUEUE/$TICKET" 2>/dev/null
  [ -n "$GUARD_PIDFILE" ] && rm -f "$GUARD_PIDFILE" 2>/dev/null
  if [ "$HELD" = "1" ]; then
    # A7: verify the lock is still OURS before removing anything.  A
    # surviving detached trap pointed at a RE-CREATED lock would delete an
    # active holder's lock and stampede the queue.
    if [ "$(cat "$LOCK/owner" 2>/dev/null)" = "$OWNER_TAG" ]; then
      rm -rf "$LOCK" || echo "LOCK RELEASE FAILED" >&2   # base 2: rm -rf, checked
      say "LOCK RELEASED (mine)"
    else
      echo "LOCK NOT MINE — left alone (owner: $(cat "$LOCK/owner" 2>/dev/null || echo none))" >&2
    fi
  fi
  exit $status
}
trap release EXIT INT TERM

: > "$QUEUE/$TICKET" || die "cannot write a ticket into $QUEUE"
say "enqueued $TICKET (queue depth $(ls "$QUEUE" | wc -l | tr -d ' '))"

# --------------------------------------------------------------- wait: FIFO
# A9: only the OLDEST ticket attempts the mkdir.  A plain spinlock starves —
# a lane that releases and immediately re-acquires beats a poller every time,
# and one lane lost five consecutive handoffs while queued first.
waited=0
while :; do
  sweep_stale_tickets
  OLDEST="$(ls "$QUEUE" 2>/dev/null | sort | head -1)"
  if [ "$OLDEST" = "$TICKET" ]; then
    if mkdir "$LOCK" 2>/dev/null; then
      HELD=1
      # A4: written ONCE, under noclobber.  A racing writer fails LOUDLY
      # instead of silently taking over the identity.
      if ( set -C; printf '%s\n' "$OWNER_TAG" > "$LOCK/owner" ) 2>/dev/null; then
        rm -f "$QUEUE/$TICKET"
        say "LOCK ACQUIRED after ${waited}s as '$OWNER_TAG'"
        break
      fi
      echo "OWNER RACE — someone wrote into a lock we just created; backing off" >&2
      rm -rf "$LOCK" || echo "LOCK RELEASE FAILED" >&2
      HELD=0
    fi
    # Lost the mkdir to a departing holder: harmless, re-loop (A9).
    if [ "$waited" -ge "$STALE_AFTER" ] && lock_is_stale; then
      say "STALE LOCK: owner '$(cat "$LOCK/owner" 2>/dev/null)' has no live pid and no live Lean descendant"
      # A8 again: re-read and re-verify immediately before the removal.
      if lock_is_stale; then
        rm -rf "$LOCK" && say "reclaimed a stale lock (noted, per base rule 5)"
      fi
    fi
  fi
  s=$(( (RANDOM % 4) + 2 ))           # jittered, so releases are not synchronised
  sleep "$s"; waited=$((waited + s))
  [ $((waited % 300)) -lt 6 ] && say "queued ${waited}s; head=${OLDEST:-none}; owner=$(cat "$LOCK/owner" 2>/dev/null || echo free)"
  if [ "$waited" -ge "$MAX_WAIT" ]; then
    echo "GAVE UP after ${waited}s without reaching the front — NOT a build failure" >&2
    exit 9
  fi
done

# ---------------------------------------------------------- RSS kill line
# A11 and base rule 6: OUR descendants only, recursively — a guard rooted at a
# pipeline's last stage (`pgrep -P $!` where $! is `tail`) can never see the
# build, and two of the six measured scripts shipped exactly that.  A16 adds
# the three properties the single-shot version got wrong: the line is
# PER-PROCESS, the guard is NOT IN ITS OWN KILL SET, and it is restarted for
# every attempt.  `watchdog_start` is called inside the build loop.
GUARD_PIDFILE="$(mktemp "${TMPDIR:-/tmp}/triad-guard.XXXXXX")" || die "no temp dir for the guard pid"

# ----------------------------------------------------------------- the work
export LEAN_NUM_THREADS="$THREADS"    # A11.  NEVER `-j` — base rule 2.
banner
say "tenure open: LEAN_NUM_THREADS=$THREADS nice -n $NICE rss<=$((RSS_PROC_LIMIT_KB / 1024))MB/proc, $((RSS_CHAIN_LIMIT_KB / 1024))MB/chain dir=$CLONE"

if [ "$DRY_RUN" = "1" ]; then
  say "DRY RUN: tenure taken, no Lean executed, releasing"
  exit 0
fi

BUILD_LOG="$(mktemp "${TMPDIR:-/tmp}/triad-build.XXXXXX")"
BUILD_EXIT=1
for attempt in 1 2; do
  say "=== lake build ${BUILD_TARGETS:-<all default targets>} (attempt $attempt) ==="
  watchdog_start                      # A16: a fresh guard for EVERY attempt
  # UNQUOTED on purpose: BUILD_TARGETS is a target LIST, and every element was
  # validated as a plain Lean identifier path before it got here.  Empty means
  # the full build, which is exactly `lake build` with no arguments.
  # shellcheck disable=SC2086
  nice -n "$NICE" lake build $BUILD_TARGETS > "$BUILD_LOG" 2>&1
  BUILD_EXIT=$?
  watchdog_stop
  say "build exit=$BUILD_EXIT"
  # base rule 2: 143/137 is the OS terminating an oversubscribed job.  It is
  # a resource kill, never a red build, and must never be recorded as one.
  if [ "$BUILD_EXIT" -eq 143 ] || [ "$BUILD_EXIT" -eq 137 ]; then
    say "exit $BUILD_EXIT = RESOURCE KILL, not a red build — re-running once"
    continue
  fi
  break
done

# Assert success POSITIVELY.  An argument error and a resource kill both emit
# no line the failure greps look for, and "no error found" must never read as
# "the build happened".
if grep -q 'Build completed successfully' "$BUILD_LOG"; then
  say "BUILD GREEN"
else
  say "BUILD DID NOT COMPLETE (exit $BUILD_EXIT) — first failures:"
  grep -E '^error|✖' "$BUILD_LOG" | sort -u | head -8
  say "full log: $BUILD_LOG"
  exit 1
fi

# The gates.  Default is this repo's triad (AGENTS.md); a lane overrides with
# --gates to add its own, INSIDE the same tenure — batching is base rule 4,
# and under A11 a second Lean invocation outside the tenure is a violation.
if [ -z "$GATES" ]; then
  GATES='python3 tools/docs_check.py; python3 harness/diff_test.py'
fi
gate_notice "$GATES" "$LANE_GATES"
run_gates "$GATES"

say "TRIAD DONE (build exit $BUILD_EXIT, gates $( [ "$rc" = 0 ] && echo green || echo RED ))"
# §5.4a: the verdict carries the state it was taken in.  A scoped green that
# does not say what it covers is a number without its state.
[ -n "$CLASS" ] && say "COVERAGE (§5.4a): $(coverage_statement "$CLASS")"
exit "$rc"
