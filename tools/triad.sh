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
# --gates ADDS; --gates-only REPLACES.  The Ada lane paid a 78-MINUTE TENURE
# for the old spelling, in which `--gates` silently REPLACED the default set:
# `--gates "docs_check"` dropped the differential, and the run went green
# against fewer checks than the default it thought it was extending.  That is
# the exact mirror of the narrower-default trap the ES lane found, and it has
# the same shape — a gate set that shrinks without saying so.  So the additive
# reading is the DEFAULT, replacement is a flag you have to type, and
# --gates-only ANNOUNCES which floor gates it is skipping.  --foreign implies
# --gates-only, because there is no applicable floor in a foreign checkout.
#
# USAGE
#   tools/triad.sh --lane <name> [--dir <clone>] [--gates "cmd; cmd"] [...]
#   tools/triad.sh --self-test          # exercises the queue logic, NO Lean
#   tools/triad.sh --lane x --dry-run   # takes a real tenure, runs no Lean
#   tools/triad.sh --lane x --classify  # scope the triad from the diff
#   tools/triad.sh --lane x --build-target "LeanModels leanmodels-run"
#
# --build-target — NAME the lake targets explicitly (repeatable, or space
#   separated).  It UNIONs with whatever `--classify` derived, because the
#   classification is a floor and never a ceiling: a lane can always build
#   more, never less.  Use it when the lane knows something the diff does not
#   — e.g. a loaded machine where amendment 14 makes a full build a
#   quiet-machine-only operation — and then the lane OWES the coverage
#   statement §5.4a asks for.
#   tools/triad.sh --lane x --build-current-tree   # accept a tree edited while queued
#   tools/triad.sh --lane x --gates "a; b"      # the floor PLUS your gates
#   tools/triad.sh --lane x --gates-only "a; b" # your gates INSTEAD of the floor
#   tools/triad.sh --lane x --foreign --gates "..."   # a FOREIGN checkout
#
# --foreign — A CHECKOUT THAT IS NOT THIS REPOSITORY.  The Lean tier works in
# `lean4lean`; the Wasm lane works in a `spectec` fork.  Both need the tenure
# — the lock, the ticket, the RSS discipline are about THE MACHINE, not about
# the repository — and neither can use anything else this script assumes.
# §7.1a says why in as many words: `--classify` is OUR-REPO-ONLY BY
# CONSTRUCTION, and a lane pointing it at a foreign checkout gets a confident
# wrong answer rather than an error, because the class floor hard-wires our
# gates and classification diffs against `github/master`.  So --foreign takes
# the tenure, runs ONLY the lane's --gates, skips classification entirely, and
# says what its green covers.  It REFUSES without --gates: there would be
# nothing to run.
#
# GATES.  Without --gates the floor is, by class (§7 surface — this comment
# and `gate_floor` are the same statement, and `DEFAULT_FLOOR` is the one
# spelling both the classified and unclassified paths read):
#
#   docs      docs_check
#   anything  docs_check; diff_test; refusal_census --whitelist --no-build
#   else
#
# REFUSAL_CENSUS JOINED THE FLOOR on 2026-08-23, by ruling.  Its §5.2
# invariants — every interpreter refusal carries a class, and NO row is
# undefined — used to fire only when a lane happened to pass --gates, and an
# unexercised gate is not a gate, it is a claim.  It is the no-UB claim's only
# external check.  `--no-build` is not optional in that line: the tenure
# prebuilds `leanmodels-run` in the gate phase, and a gate that builds turns a
# build defect into a gate failure (see the gate-phase build below).
#
# The floor is NARROWER than some retired lane scripts.  A run that did not
# choose its own gates SAYS WHICH ONES IT IS RUNNING — see `gate_notice`, and
# the `gates:` line every tenure prints at open.
#   tools/triad.sh --classify-only      # print the classification, run nothing
#   tools/triad.sh --classify --against <ref>    # default: github/master
#   tools/triad.sh --classify --since <sha>      # price the INCREMENT (§5.4a-i)
#
# INCREMENT GREENS (§5.4a-i).  `--classify` diffs the whole BRANCH against
# github/master, so a two-file docs commit stacked on a freshly-green branch
# re-elaborates work certified an hour earlier — the pyc lane withdrew such a
# ticket and proved its increment's class by hand.  `--since <sha>` prices the
# increment instead, and the green it produces is evidence about THE INCREMENT
# ON TOP OF THE NAMED GREEN, never about the branch alone.
#
#   * A GREEN CERTIFIES A TREE, NOT A COMMIT.  The stamp is `git write-tree`
#     (the INDEX tree) + HEAD, so a green can certify content that is not any
#     commit.  Such a green is recorded `citable=no` and cannot be a base: the
#     sha would name something the green did not certify.
#   * CLASSIFICATION IS AGAINST THE CHAIN ROOT, NEVER THE PARENT.  Two
#     increments priced against their predecessors can be `tier A` and
#     `tier B` with neither build covering their interaction.  Naming any
#     recorded green is allowed; the diff is taken against its ROOT, and the
#     line says so when the two differ.
#   * THE MERGE BAR: an increment green satisfies it iff the chain root is a
#     FULL (spine) green.  A scoped root does not, and the coverage line says
#     which case it is.
#   * THE LEDGER is `.git/triad-greens` — untracked (it can never conflict),
#     inside the git dir (it survives rebase), and PER WORKING DIRECTORY,
#     because `.lake` is.  A green recorded elsewhere is not verifiable here.
#     Evidence does not travel by assumption.
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
# THE CLASS FLOOR, NAMED ONCE.  It was a literal inside the gate phase, which
# is fine until something ELSE has to say what will run — and then the two
# spellings can drift, and an announcement that drifts lies in the reassuring
# direction.  One constant, read by the announcement, by the phase, AND by
# `gate_floor` — which had its own second copy of the same list, so a floor
# change had to be made twice or the classified and unclassified paths would
# have run different gates.
SINCE=""                # --since <sha>: price the INCREMENT (§5.4a-i)
SINCE_ROOT=""           # the chain root the increment is actually diffed against
SINCE_LINE=""           # the base green's ledger line, kept for the coverage line
DOCS_FLOOR='python3 tools/docs_check.py'
DEFAULT_FLOOR='python3 tools/docs_check.py; python3 harness/diff_test.py; python3 harness/refusal_census.py --whitelist --no-build'
# The label the announcement carries, so the first lane to see a new gate line
# reads WHY rather than filing a bug against its own tenure.
FLOOR_LABEL='floor of 2026-08-23: + refusal_census --whitelist (§5.2 — every refusal carries a class; no row undefined)'
CLASSIFY=0
CLASSIFY_ONLY=0
FOREIGN=0
BUILD_CURRENT_TREE=0
GATES_ONLY=0
AGAINST=""                                     # merge target; default below

# The header IS the usage text, so print it whole — a `sed -n '1,60p'` goes
# stale the first time somebody documents a flag.
# The protocol level this file implements.  Bump it in the same commit as the
# amendment, so a /tmp copy that predates one is identifiable from its output.
TRIAD_PROTOCOL="base 1-6 + A4-A13 + A16"
TRIAD_PROTOCOL_DATE="2026-08-22"

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
banner() { echo "tools/triad.sh — protocol $TRIAD_PROTOCOL ($TRIAD_PROTOCOL_DATE)\
$( [ "${FOREIGN:-0}" = "1" ] && printf ' [FOREIGN]' ), \
$( (git -C "$CLONE" rev-parse --short HEAD 2>/dev/null) || echo 'no git' )"; }

foreign_remote() {      # the checkout's identity, for the coverage statement
  git -C "$CLONE" remote get-url origin 2>/dev/null \
    || git -C "$CLONE" remote -v 2>/dev/null | awk 'NR==1{print $2}' \
    || echo 'no remote'
}
foreign_coverage() {
  echo "foreign checkout $(foreign_remote); gates as given; class floor not applicable — this green is evidence about THAT tree and those gates, and about nothing in this repository."
}

. "$(dirname "${BASH_SOURCE[0]}")/argv.sh"   # the value-flag guard (a flag written last used to SPIN)
while [ $# -gt 0 ]; do
  case "$1" in
    --lane)      need_val "$#" "$1"; LANE="$2"; shift 2 ;;
    --dir)       need_val "$#" "$1"; CLONE="$2"; shift 2 ;;
    --gates)      need_val "$#" "$1"; GATES="$2"; shift 2 ;;
    --gates-only) need_val "$#" "$1"; GATES="$2"; GATES_ONLY=1; shift 2 ;;
    --rss-limit)      need_val "$#" "$1"; RSS_CHAIN_LIMIT_KB="$2"; shift 2 ;;
    --rss-proc-limit) need_val "$#" "$1"; RSS_PROC_LIMIT_KB="$2"; shift 2 ;;
    --version)        banner; exit 0 ;;
    --dry-run)   DRY_RUN=1; shift ;;
    --self-test) SELF_TEST=1; shift ;;
    --build-target) need_val "$#" "$1"; BUILD_TARGET_ARGS="${BUILD_TARGET_ARGS:+$BUILD_TARGET_ARGS }$2"; shift 2 ;;
    --classify)  CLASSIFY=1; shift ;;
    --foreign)   FOREIGN=1; shift ;;
    --build-current-tree) BUILD_CURRENT_TREE=1; shift ;;
    --classify-only) CLASSIFY=1; CLASSIFY_ONLY=1; shift ;;
    --against)   need_val "$#" "$1"; AGAINST="$2"; shift 2 ;;
    --since)     need_val "$#" "$1"; SINCE="$2"; shift 2 ;;
    -h|--help)   usage ;;
    *)           echo "triad.sh: unknown argument '$1'" >&2; usage ;;
  esac
done

LANE_GATES="$GATES"                            # what the LANE asked for, kept

# The lakefile reader is SHARED with check.sh.  The two disagreed about a
# repo-root `.lean` — check.sh read the lakefile and said scratch (correct:
# `Examples.+` does not match a root module), triad.sh hard-coded
# `LeanModels/*|Examples/*` and warned about it.  One source now.
LAKEINFO="$(dirname "${BASH_SOURCE[0]}")/lakeinfo.sh"
[ -r "$LAKEINFO" ] || { echo "triad.sh: missing $LAKEINFO" >&2; exit 2; }
# shellcheck source=/dev/null
. "$LAKEINFO"

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
# --build-target's raw arguments.  They cannot be UNIONed at parse time because
# `add_build_target` is not defined yet, so they are collected here and applied
# after classification — which is also the right ORDER: the classifier is a
# floor, and an explicit target can only ever add to it.
BUILD_TARGET_ARGS=""

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
    # Tier-local: whatever the LAKEFILE calls a library — asked, not assumed.
    *) if [ "$(lake_glob_class "$CLONE" "$1")" = "library" ]; then echo tier
       else
         case "$1" in
           docs/*|notebooks/*|tools/*|harness/*|.github/*) echo docs ;;
           .gitignore|*.md)                                echo docs ;;
           *.lean)                                         echo spine ;;
           *)                                              echo spine ;;
         esac
       fi ;;
    esac
    return 0
}

_classify_path_unused() {
  case "$1" in
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
# DERIVED FIRST, hand-map second.  The map's header claimed it "is not
# derivable"; for `go` it plainly is — `Examples/go/**/*.lean` all say
# `import LeanModels.Go`, and `LeanModels/Go/` is 1,129 lines.  A hand-written
# claim that the tree contradicts is the identifier law wearing a comment.
example_dir_tiers() {   # Examples/<dir> -> zero or more LeanModels tier keys
  local derived
  derived="$(grep -rhoE '^[ \t]*import[ \t]+LeanModels\.[A-Za-z0-9_]+' \
               "${LS_GREP_ROOT:-$CLONE}/Examples/$1" --include='*.lean' 2>/dev/null \
             | sed 's/.*LeanModels\.//' | sort -u | tr '\n' ' ' | sed 's/ *$//')"
  if [ -n "$derived" ]; then printf '%s\n' "$derived"; return 0; fi
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
# A PROSE MENTION IS NOT A REFERENCE.  The Go lane vendored `bitlen.go` beside
# its model and cited it in the docstring — the only mention of it in any
# `.lean` — and the tenure went from 91 SECONDS TO 37 MINUTES, because a
# reachable non-Lean fixture widens the target to the whole `Examples` library.
# They worked around it by deleting the sibling and quoting the source; the
# real fix is here.  An attribution header is exactly what makes a lane name
# the file in prose, so the rule and the convention would otherwise fight.
#
# Strip Lean comments before looking for the path — the same discipline
# `harness/wasm_sorry_census.py` needed for `sorry` and `tools/sites.sh` for
# constructor sites.  (Third copy of the comment walker in this tree; a shared
# helper is owed, and `tools/dupes.sh` counts `.py` only, so it will not see
# it — recorded rather than left for someone to notice.)
code_mentions() {               # needle, file -> 0 when it appears OUTSIDE comments
  awk -v NEEDLE="$1" '
    { line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        two = substr(line, i, 2)
        if (depth == 0 && two == "--") break
        if (two == "/-") { depth++; i += 2; continue }
        if (two == "-/") { if (depth > 0) depth--; i += 2; continue }
        if (depth == 0) out = out substr(line, i, 1)
        i++ }
      if (index(out, NEEDLE) > 0) { found = 1; exit } }
    END { exit(found ? 0 : 1) }' "$2"
}

example_fixture_is_reachable() {   # path -> 0 reachable, 1 provably invisible
  # `hit` is LOCAL and deliberately not named `c`: the caller holds its verdict
  # in `c`, and the first cut looped `for c in $(git grep -l …)`, silently
  # overwriting "tier" with a filename — which then fell through the caller's
  # `case` to `docs`.  A referenced fixture read as invisible, from a variable
  # name.  Every loop variable in here is local.
  local p="$1" base root rc hit
  root="${LS_GREP_ROOT:-$CLONE}"
  base="${p##*/}"
  # DOUBT, structurally: no readable root means no probe, and no probe means
  # reachable.  Never infer "unreferenced" from a search that did not happen.
  [ -d "$root" ] && [ -r "$root" ] || return 0
  if git -C "$root" rev-parse --git-dir >/dev/null 2>&1; then
    # The gate corpora are JSON and carry no Lean comments, so a plain grep is
    # right there; only the `.lean` side needs the comment walk.
    if git -C "$root" grep -q -I -F --untracked -e "$p" -e "$base" \
        -- 'harness/*.json' >/dev/null 2>&1; then
      rc=0
    else
      rc=1
      for hit in $(git -C "$root" grep -l -I -F --untracked -e "$p" -e "$base" \
                   -- '*.lean' 2>/dev/null); do
        if code_mentions "$base" "$root/$hit" || code_mentions "$p" "$root/$hit"; then
          rc=0; break
        fi
      done
    fi
  else
    # THE FALLBACK BRANCH MUST BE COMMENT-AWARE TOO.  The first cut fixed only
    # the git-grep path, so a clone without git — and every self-test fixture —
    # still counted a docstring mention as a reference.  A rule enforced on one
    # of two paths is a rule with a hole exactly where nobody looks.
    rc=1
    for hit in $(grep -rlI -F --include='*.lean' -e "$p" -e "$base" "$root" 2>/dev/null); do
      if code_mentions "$base" "$hit" || code_mentions "$p" "$hit"; then rc=0; break; fi
    done
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
    # ASKED OF THE LAKEFILE, NOT OF A DIRECTORY LIST.  This was
    # `docs/*.lean|harness/*.lean|tools/*.lean` — three hard-coded prefixes,
    # which is the hard-coding lakeinfo.sh exists to end: a `.lean` under
    # `probes/`, or at the repo root, is equally outside every declared root
    # and got no note at all.
    case "$p" in
      *.lean)
        if [ "$(lake_glob_class "$CLONE" "$p")" != "library" ]; then
          # THE REBASE LAW, from the Go lane: a file outside every lean_lib
          # root is never compiled by `lake build`, so a rebase that touches
          # only such files owes NO re-gate.  The A11 half still holds and is
          # kept in the same breath — not compiled is not the same as not run.
          add_note "'$p' is OUTSIDE ALL lean_lib ROOTS ($(lake_lib_roots "$CLONE" | tr '\n' ' ' | sed 's/  *$//')) — \`lake build\` never compiles it, so a rebase touching only it owes no re-gate; but RUNNING it is still Lean execution (A11): pass --gates"
        fi ;;
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

# ---- UNSTAGED LEAN, AND LEAN NOTHING IMPORTS
# The Ada lane spent a 78-minute tenure on a tree whose `Value.lean` was
# UNTRACKED and UNIMPORTED — so the build was green about a file it never
# compiled, twice over.  Two different checks, and they fail differently:
#   * unstaged Lean under a lake glob is a REFUSAL.  A tenure verifies the
#     STAGED tree; spending one on a tree whose Lean is not staged verifies
#     something nobody is landing.
#   * Lean that NOTHING IMPORTS is a loud line.  The `LeanModels` library has
#     no `globs` in the lakefile, so only `LeanModels.lean` and its transitive
#     imports are built: a new module nobody imports is not compiled at all,
#     and a green that never touched it is green about nothing.
# `Examples` is exempt from the second check BY THE LAKEFILE — it declares
# `globs = ["Examples.+"]`, so every module under it is a target whether or
# not anything imports it.
lean_glob_offenders() { # stdin: paths -> the .lean ones inside a lake glob
  local p
  while IFS= read -r p; do
    [ -n "$p" ] || continue
    case "$p" in *.lean) ;; *) continue ;; esac
    # ASK THE LAKEFILE, not the class.  "Not docs" included a repo-root
    # `.lean`, which is scratch by the lakefile's own globs — and check.sh said
    # so while this warned about it.  The warning names a lake glob, so the
    # lakefile is what decides.
    [ "$(lake_glob_class "$CLONE" "$p")" = "library" ] || continue
    echo "$p"
  done
}

module_is_imported() {  # module -> 0 when some .lean in the tree imports it
  local m="$1" root esc rc
  root="${LS_GREP_ROOT:-$CLONE}"
  [ -d "$root" ] || return 0          # nothing to search: stay quiet, say nothing
  esc="$(printf '%s' "$m" | sed 's/\./\\./g')"
  if git -C "$root" rev-parse --git-dir >/dev/null 2>&1; then
    git -C "$root" grep -qE --untracked "^[[:space:]]*import[[:space:]]+$esc([[:space:]]|\$)" \
        -- '*.lean' >/dev/null 2>&1
    rc=$?
  else
    grep -rqE "^[[:space:]]*import[[:space:]]+$esc([[:space:]]|\$)" --include='*.lean' "$root" 2>/dev/null
    rc=$?
  fi
  [ "$rc" = "0" ]
}

unimported_new_modules() {  # stdin: changed paths -> LeanModels modules nobody imports
  local p m
  while IFS= read -r p; do
    case "$p" in
      LeanModels.lean)   continue ;;    # the library ROOT, imported by nothing BY DESIGN
      LeanModels/*.lean) ;;
      *) continue ;;
    esac
    m="$(module_of "$p")"
    [ -n "$m" ] || continue
    module_is_imported "$m" || echo "$p"
  done
}

# ---- A STALE GENERATED INDEX, refused BEFORE the ticket
# `docs/backlog/INDEX.md` is generated (§9.5).  `.gitattributes` marks it
# `merge=ours` so a rebase resolves without a conflict — which means the
# post-rebase index is routinely STALE-BUT-VALID, by design.  Something has to
# force the regeneration, or the driver just makes staleness quiet.
#
# That check belongs HERE and not at the docs_check gate.  Base rule 4 makes a
# triad ONE PER LANDING, so a red at gate 2 costs the whole tenure; a refusal
# before the ticket costs one command.  Same refusal, one tenure cheaper — and
# this lane has watched a tenure cost 78 minutes.
index_is_stale() {      # [clone] -> 0 when the generated index is stale
  local root="${1:-$CLONE}" gen
  gen="$root/tools/backlog-index.sh"
  [ -x "$gen" ] || return 1           # no generator: nothing to be stale about
  "$gen" --dir "$root" --check >/dev/null 2>&1 && return 1
  return 0
}

gate_floor() {          # class -> the gates this landing owes at minimum
  # ONE SPELLING.  This used to carry its own copy of the list, so the
  # classified path and the unclassified path could run different floors and
  # nothing would say so.
  case "$1" in
    docs) printf '%s\n' "$DOCS_FLOOR" ;;
    *)    printf '%s\n' "$DEFAULT_FLOOR" ;;
  esac
}

# ---- THE GATE PHASE BUILDS TOO, AND THAT DEFEATED THE NARROWING
# Found by the R-track running a narrowed build: `harness/diff_test.py` runs
# an UNCONDITIONAL `lake build` before its cases, and every runner-driven gate
# (`diff_test`, `script_corpus`) invokes
# `lake exe leanmodels-run`, which BUILDS.  So a narrowed tenure got a full
# build anyway — inside the GATE phase, where it is accounted as a gate.
#
# Two costs, and the second is the one that matters.  The build/gate
# accounting is misleading; and an unrelated build failure surfaces as a GATE
# failure, which makes the coverage statement false IN THE FLATTERING
# DIRECTION (§5.4a).  A narrowed run that says "scoped: covers these modules"
# while having quietly built the tree is claiming less than it did — and a
# tree failure it caused is filed against a gate that was innocent.
#
# So the tenure builds what the gates need, EXPLICITLY, before invoking them,
# and NAMES it in the coverage statement.  Then it tells the gates the runner
# is ready: `--no-build` for `diff_test` (its own documented flag), and
# `LS_RUNNER_PREBUILT=1` in the environment for every other harness.
lake_exe_names() {      # -> the [[lean_exe]] names, read from the lakefile
  local f="$CLONE/lakefile.toml"
  [ -f "$f" ] || return 0
  awk '
    /^\[\[lean_exe\]\]/ { sec = 1; next }
    /^\[\[/               { sec = 0; next }
    sec && /^[ \t]*name[ \t]*=/ {
      sub(/^[^=]*=[ \t]*/, ""); gsub(/["\047 \t\r]/, ""); print }
  ' "$f"
}

gate_runner_targets() { # gate list -> the exe targets those gates will invoke
  local g="$1" e out=""
  for e in $(lake_exe_names); do
    case "$g" in *"$e"*) out="${out:+$out }$e" ;; esac
  done
  # These harnesses take the runner from a DEFAULT, so the name never appears
  # in the gate string: `diff_test`'s is `lake exe leanmodels-run`.
  if [ -z "$out" ]; then
    case "$g" in
      # `refusal_census` takes `--runner "lake exe leanmodels-run"` from its
      # own default, so the exe name never appears in the gate string either.
      # It joined the floor beside diff_test, which alone would have kept the
      # prebuild working BY ACCIDENT — a lane running the census through
      # --gates-only would have reached `--no-build` with nothing built, and
      # read a missing runner as a census failure.
      *diff_test*|*script_corpus*|*refusal_census*|*"lake exe"*)
        out="$(lake_exe_names | head -1)" ;;
    esac
  fi
  echo "$out"
}

announce_prebuilt() {   # gate list -> the same list, told the runner is ready
  # ONLY `diff_test`'s own documented flag is added.  Another harness gets the
  # environment variable instead — inventing a flag it does not have would
  # turn a build defect into a gate crash.
  # Idempotent: a lane that already passes --no-build must not get it twice.
  printf '%s' "$1" \
    | sed 's|harness/diff_test\.py|harness/diff_test.py --no-build|g' \
    | sed 's|--no-build  *--no-build|--no-build|g'
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

gates_compose() {       # floor, lane's gates, gates_only -> the list to run
  # ADDITIVE BY DEFAULT.  A lane that types --gates is asking for MORE, and
  # this script cannot tell the difference between "also run mine" and
  # "instead of yours" — so it takes the reading that cannot silently shrink
  # a gate set, and makes the other one explicit.
  if [ "$3" = "1" ]; then printf '%s' "$2"; return 0; fi
  if [ -n "$2" ]; then printf '%s; %s' "$1" "$2"; else printf '%s' "$1"; fi
}

# WHAT WILL ACTUALLY RUN, SAID AT TENURE OPEN.  The spin this lane just fixed
# had a NEAR-MISS twin that is worse: a run whose `--gates` value went missing
# still completed and reported green — on the DEFAULT FLOOR, which is less
# coverage than the lane believed it had bought, with nothing in the log to
# say so.  The die-guard closes the path that produced it; this closes the
# READING of it, because a log should not need a guard to be honest about its
# own scope.  Composed by the SAME function the gate phase uses, so the line
# cannot promise a set the phase does not run.
gates_planned() {       # -> the gate list this tenure will run
  # A foreign tree and a classify-only pass both run the gates AS GIVEN: there
  # is no floor to add, because the floor is a claim about THIS repository.
  if [ "$FOREIGN" = "1" ] || [ "$CLASSIFY" = "1" ]; then printf '%s' "$GATES"; return 0; fi
  gates_compose "$DEFAULT_FLOOR" "$LANE_GATES" "$GATES_ONLY"
}

gates_only_notice() {   # floor, gates_only -> announce what is NOT running
  [ "$2" = "1" ] || return 0
  echo ""
  echo "  !! --gates-only: THE CLASS FLOOR IS NOT RUNNING.  Skipped: $(gate_names "$1")."
  echo "     Replacement is the spelling you typed; --gates would have ADDED to"
  echo "     the floor instead.  The Ada lane paid a 78-minute tenure for the"
  echo "     old semantics, in which --gates replaced silently."
  echo ""
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

# THE INCREMENT'S COVERAGE, COMPOSED (§5.4a-i).  The pyc lane stated this by
# hand and the coordinator accepted it; this makes it mechanical instead of
# artisanal.  Both shas are named because either one alone is a claim nobody
# can check: the increment without its base says nothing about what is under
# it, and the base without the increment is last hour's verdict.
increment_coverage() {  # class -> the composed statement, ending in the clause
  local named root_class root_full n
  named="$(git -C "$CLONE" rev-parse --short "${SINCE}^{commit}" 2>/dev/null || echo unknown)"
  root_class="$(ledger_field "$SINCE_LINE" class)"
  root_full="$(ledger_field "$SINCE_LINE" full)"
  n="$(printf '%s' "$CHANGED" | grep -c . || true)"
  printf 'INCREMENT green.\n'
  printf '  increment  %s..%s  (%s file(s), class %s)\n' "$BASE_SHA" "$(git -C "$CLONE" rev-parse --short HEAD 2>/dev/null || echo unknown)" "$n" "$1"
  printf '  on top of  the green at %s (class %s, targets %s, recorded %s)\n' \
         "$named" "$root_class" "$(ledger_field "$SINCE_LINE" targets)" "$(ledger_field "$SINCE_LINE" at)"
  printf '  root       %s (%s)\n' "$BASE_SHA" \
         "$( [ "$root_full" = "yes" ] && echo 'FULL build' || echo 'scoped — see the merge bar below' )"
  printf '  %s\n' "$(coverage_statement "$1")"
  # THE CLAUSE IS UNCONDITIONAL, including when the base was a full build:
  # what it guards against is the READING, not the base.
  printf '  This green is evidence about THE INCREMENT ON TOP OF THAT GREEN and nothing\n'
  printf '  else. It is NOT evidence that the branch is green as a whole, and it inherits\n'
  printf '  every limit of the green it rests on.\n'
  if [ "$root_full" = "yes" ]; then
    printf '  MERGE BAR: SATISFIED — the chain root is a FULL green and this increment was\n'
    printf '             classified against that root (§5.4a-i).\n'
  else
    printf '  MERGE BAR: NOT SATISFIED — the chain root is SCOPED, so no green in this chain\n'
    printf '             covers what a scoped build leaves out. Take one full green.\n'
  fi
}

coverage_statement() {  # class -> what a green from this run is EVIDENCE OF
  case "$1" in
    docs) echo "docs-only: NO Lean was elaborated, so a green here is evidence about the prose, its citations and its paths — and about NOTHING in the model." ;;
    tier) echo "scoped: a green covers the modules named above and everything they IMPORT. It does NOT cover modules that import THEM, nor any untouched tier, and it is not evidence about master beyond that scope." ;;
    spine) echo "full: a green covers every default target at this sha." ;;
    *)    echo "no files classified — this run measured nothing." ;;
  esac
}

# THE IN-FILE `#print axioms` EVIDENCE IS THE HOUSE STANDARD for library
# files — in the tree, under a tenure, and immune to `check.sh --axioms` by
# design.  The build log is NOT deleted (there is no `rm` of it anywhere here);
# a green tenure merely stops REFERENCING it, which is enough to lose it:
# measured 2026-08-23, 56 `triad-build.*` files coexist in one TMPDIR, from
# many lanes and many runs.
#
# So the fix is small — NAME THE PATH on green as well as on red — and the
# axiom lines are echoed too, because they are the half a lane quotes.
# The pointer a green tenure owes its reader.  It carries the WARNING with it,
# because the advice is only needed by someone who no longer has the line.
# A BUILD LOG MUST SAY WHOSE IT IS.  `triad-build.*` carried ONLY lake output
# — no ticket, no lane, no branch, no tree — so when the C successor lost its
# transcript it grepped 68 of them for its lane tag and matched NOTHING.  The
# logs were all still there; not one could be attributed.  The pointer above
# recovers a log BY PATH, and by content when the path is gone; neither helps
# when the content itself is anonymous, and "the only path from a lost
# transcript to a verdict is the lane's own log".
#
# WRITTEN PER ATTEMPT, because the build redirect TRUNCATES: a header written
# once at open would be erased by attempt 1 and again by the resource-kill
# retry.  Each attempt re-stamps into a freshly truncated file, so the
# one-attempt-per-log semantics every failure report assumes is unchanged.
#
# The fields are the ones a grep is run for: the ticket (unique per tenure),
# the lane, the branch, the enqueue tree, HEAD, the clone, the attempt.  No
# hostname — tracked files and shared logs carry none.
build_log_header() {            # attempt -> the identifying first line
  printf 'triad.sh ticket=%s lane=%s branch=%s tree=%s head=%s dir=%s attempt=%s at=%s\n' \
    "$TICKET" "$LANE" \
    "$(git -C "$CLONE" rev-parse --abbrev-ref HEAD 2>/dev/null || echo none)" \
    "$(short_tree "${ENQ_STAMP:-unstampable}")" \
    "$(git -C "$CLONE" rev-parse --short HEAD 2>/dev/null || echo none)" \
    "$CLONE" "$1" "$(date '+%Y-%m-%dT%H:%M:%S')"
}

build_log_pointer() {           # log -> the line naming it, and the caveat
  printf 'full log: %s  (kept, not deleted — recover by THIS PATH; failing that by CONTENT, grep -l for a symbol only this build printed; NEVER by clock — %s other triad-build logs share this TMPDIR and three can land within 90s of one tenure)' \
    "$1" "$(( $(ls "$(dirname "$1")"/triad-build.* 2>/dev/null | grep -c . || echo 1) - 1 ))"
}

# THE DECLARED STANDARD SET (AGENTS.md § House rules: `#print axioms` of every
# @[spec] theorem shows only the three).  Named here so a lane disputes the
# LIST rather than the verdict.
AXIOM_STANDARD='propext Classical.choice Quot.sound'

# A LEDGER THAT CANNOT FAIL IS A LEDGER NOBODY NEEDS TO READ.  The first cut
# grepped, echoed, and returned 0 whenever any axiom line existed — so
# `[sorryAx]` and `[Lean.ofReduceBool]` printed identically to the standard
# three and the tenure still said gates green.  That is this lane's own law
# (a success signal that survives the failure it should report) for the third
# time, now in the guard built to carry the evidence.
axiom_ledger() {                # log -> lines, labelled; 1 none; 2 OFF-STANDARD
  local lines bad
  lines="$(grep -E 'depends on axioms|does not depend on any axioms' "$1" 2>/dev/null || true)"
  [ -n "$lines" ] || return 1
  echo "axiom ledger, from this build:"
  printf '%s\n' "$lines" | sed 's/^/    /'
  # Each line's bracketed list, minus the standard set: whatever remains is an
  # axiom nobody declared, and `sorryAx` is the one that matters most.
  bad="$(printf '%s\n' "$lines" | awk -v STD="$AXIOM_STANDARD" '
      BEGIN { n = split(STD, a, " "); for (i = 1; i <= n; i++) ok[a[i]] = 1 }
      /depends on axioms/ {
        decl = $0; sub(/^[^\x27]*\x27/, "", decl); sub(/\x27.*$/, "", decl)
        list = $0; sub(/^.*\[/, "", list); sub(/\].*$/, "", list)
        gsub(/,/, " ", list)
        m = split(list, ax, " ")
        for (i = 1; i <= m; i++) if (ax[i] != "" && !(ax[i] in ok))
          printf "%s (%s)\n", ax[i], decl
      }' | sort -u)"
  if [ -n "$bad" ]; then
    echo "AXIOMS OFF THE DECLARED STANDARD ($AXIOM_STANDARD):"
    printf '%s\n' "$bad" | sed 's/^/    /'
    echo "A build carrying these is not a green tenure — read them before quoting it."
    return 2
  fi
  return 0
}

# ------------------------------------------- THE RED-BUILD REPORT (§7)
# The old block was `grep -E '^error|✖' | sort -u | head -8`, and a lane
# reported "one error in 839 targets" off it — a number that then travelled up
# the chain.  Three things were wrong at once, and only the third is obvious:
# the preview is DEDUPLICATED, it is TRUNCATED AT EIGHT, and `lake` STOPS AT
# THE FIRST FAILING MODULE, so the log being summarised is already partial.
#
#   > The triad summary LOCATES; the full log COUNTS.  (§7)
#
# So the wrapper now says what it knows: counts taken from the WHOLE log, the
# preview labelled with how much of the pool it is showing, and the gap
# between total and distinct error lines named as AMPLIFICATION, because that
# gap is exactly what turns one root cause into a scary number (or a
# comforting one).
build_failure_report() {              # log -> counts, then a FAITHFUL preview
  # THE SAMPLE MUST BE THE SAMPLE IT CLAIMS TO BE (pyc3, 2026-08-24).
  #
  # This said "first 8 of 46" and showed `spec.lean:102-139`, while the log's
  # FIRST error was `spec.lean:24` — a maximum-recursion-depth failure, a
  # DIFFERENT CLASS, whose cascade the other ~44 lines were.  The one line
  # naming the causal class was the one line dropped, and the lane spent a
  # diagnosis cycle hunting `noncomputable` before opening the full log.
  #
  # THE CAUSE WAS `sort -u`.  It deduplicated by SORTING ALPHABETICALLY, so
  # `head -8` took the first eight IN STRING ORDER while the label promised
  # log order — and `spec.lean:102` sorts before `spec.lean:24` because `1`
  # precedes `2`.  The higher line numbers were not merely a different sample;
  # they were the ones that sorted first.
  #
  # > "Truncation would have been harmless; a labelled-but-unfaithful sample is
  # > not, because what survives is a coherent wrong story."  (pyc3)
  #
  # So: the FIRST error is printed verbatim and unconditionally, and the rest
  # is deduplicated IN LOG ORDER (`awk !seen[$0]++`, never `sort -u`).  If a
  # line says "first N", it is the first N as the build emitted them.
  local log="$1" n_mod n_tot n_dis pool m shown amp built first rest nrest
  [ -f "$log" ] || { echo "    (no log at '$log')"; return 0; }
  n_mod="$(grep -c '✖' "$log" 2>/dev/null || true)"
  n_tot="$(grep -cE '^error|error:' "$log" 2>/dev/null || true)"
  n_dis="$(grep -E '^error|error:' "$log" 2>/dev/null | sort -u | grep -c . || true)"
  # ORDER-PRESERVING dedup: first occurrence wins, and the order is the log's.
  pool="$(grep -E '^error|✖' "$log" 2>/dev/null | awk '!seen[$0]++' || true)"
  m="$(printf '%s' "$pool" | grep -c . || true)"
  built="$(grep -oE '\[[0-9]+/[0-9]+\]' "$log" 2>/dev/null \
           | tr -d '[]' \
           | awk -F/ '{ if ($1+0 > k) { k = $1+0; n = $2+0 } } END { if (n) printf "%d of %d", k, n }')"
  printf '    failed modules   %s   (✖ lines)\n' "$n_mod"
  amp=""
  if [ "$n_dis" -gt 0 ] && [ "$n_tot" -gt "$n_dis" ]; then
    amp="$(awk -v a="$n_tot" -v b="$n_dis" 'BEGIN { printf "  — AMPLIFIED %.1fx: one root cause prints many lines", a/b }')"
  fi
  printf '    error lines      %s total, %s distinct%s\n' "$n_tot" "$n_dis" "$amp"
  printf '    targets          %s when lake stopped — and lake stops at the FIRST failing module\n' \
         "${built:-unknown}"
  # THE FIRST ERROR, ALWAYS, VERBATIM.  Everything after it may be a cascade
  # of it, so it is the one line a summary may never drop.
  first="$(grep -m1 -E '^error|error:' "$log" 2>/dev/null || true)"
  if [ -n "$first" ]; then
    printf '    FIRST error (verbatim — later lines may be its cascade):\n'
    printf '      %s\n' "$first"
  fi
  rest="$(printf '%s\n' "$pool" | grep -v '^$' | grep -vxF "$first" || true)"
  nrest="$(printf '%s' "$rest" | grep -c . || true)"
  shown="$nrest"; [ "$shown" -gt 7 ] && shown=7
  if [ "$nrest" -gt 0 ]; then
    printf '    next %s of %s more distinct, IN LOG ORDER (summary LOCATES; the full log COUNTS):\n' \
           "$shown" "$nrest"
    printf '%s\n' "$rest" | head -7 | sed 's/^/      /'
  fi
  printf '    These counts say how far the build GOT, not how much of the tree is broken.\n'
  return 0
}

# A red build short-circuits the tenure, so a red triad is not a triad result
# with one part failing — it is an ABORTED triad.  Saying so is the difference
# between "1 failure" and "two gates that never executed" (§7, §5.4a).
build_red_report() {                  # log, headline -> the whole red block
  say "$2"
  build_failure_report "$1"
  say "GATES NOT RUN (build red — aborted triad)"
  say "full log: $1"
  return 0
}

# ------------------------------- THE TREE MUST NOT MOVE WHILE YOU QUEUE
# A queued tenure reads the source at BUILD time, not at enqueue time, so an
# edit made while waiting silently changes what the verdict is about.  Measured
# this morning: the Lean tier nearly reported "instN green" for a run that
# would have built instN AND weak' — the queue wait was long enough for the
# tree to move underneath the ticket.
#
# The stamp is the INDEX's tree (`git write-tree`) plus HEAD, taken at enqueue
# and written into the ticket so a human reading the queue can see it, and
# re-taken at acquire.  A6 is being amended to say "never change the tree
# between enqueue and release"; this is the gate that enforces it, because a
# fix that lives only in a rule is a rule, and fixes live in gates.
# THE STAMP MUST HASH WHAT LAKE READS (the wasm lane, 2026-08-24).
#
# `git write-tree` hashes the INDEX.  `lake` compiles the WORKING TREE.  So an
# uncommitted, unstaged edit made between enqueue and acquire moved exactly the
# files lean reads while leaving the stamp IDENTICAL — the guard passed, the
# tenure ran, and the green certified a tree the gate never saw.  That is the
# Ada wrong-tree hazard mechanized into the tool that exists to prevent it.
# Measured in this clone while writing the fix: index `2fd6962...`, working
# tree `112a516...` — the guard had been comparing the wrong one.
#
# A TEMPORARY INDEX, never the real one: `git add -A` against a throwaway
# GIT_INDEX_FILE hashes the working tree without touching the lane's staging
# area.  `add -A` includes UNTRACKED files (a new `.lean` is exactly what must
# not slip in) and honours `.gitignore` (so `.lake` output churning during a
# build cannot defeat the stamp).  Cost measured here: 0.31s cold against
# 0.015s for the index — twice per tenure, which is free.
STAMP_VERSION="v2"
worktree_tree() {                     # -> the WORKING TREE's hash, or ''
  local idx t
  idx="$(mktemp "${TMPDIR:-/tmp}/triad-index.XXXXXX")" || return 1
  rm -f "$idx"                        # git creates it; mktemp only reserves the name
  GIT_INDEX_FILE="$idx" git -C "$CLONE" add -A >/dev/null 2>&1 || { rm -f "$idx"; return 1; }
  t="$(GIT_INDEX_FILE="$idx" git -C "$CLONE" write-tree 2>/dev/null)"
  rm -f "$idx"
  [ -n "$t" ] || return 1
  printf '%s' "$t"
}
tree_stamp() {                        # -> "v2 <tree> <head>", or '' when unstampable
  local t h
  t="$(worktree_tree)" || return 1
  [ -n "$t" ] || return 1
  h="$(git -C "$CLONE" rev-parse HEAD 2>/dev/null || echo none)"
  printf '%s %s %s\n' "$STAMP_VERSION" "$t" "$h"
}
# A STAMP CARRIES ITS OWN VERSION, so a ticket enqueued by the OLD code is not
# read as a changed tree.  Eight tenures were live when this landed; comparing
# an index stamp against a working-tree stamp would have refused every one of
# them for a defect that is the tool's, not theirs.
stamp_tag() {  case "$1" in v[0-9]*) printf '%s' "${1%% *}" ;; *) printf 'v1' ;; esac; }
stamp_tree() { local r; case "$1" in v[0-9]*) r="${1#* }"; printf '%s' "${r%% *}" ;;
                                     *) printf '%s' "${1%% *}" ;; esac; }

tree_verdict() {                      # enq, now -> same | changed | unknown | unversioned
  if [ -z "$1" ] || [ -z "$2" ]; then echo unknown; return 0; fi
  # DIFFERENT STAMP VERSIONS ARE NOT A DIFFERENT TREE.  They are answers to two
  # different QUESTIONS — one asked of the index, one of the working tree — and
  # an answer to one is not evidence about the other.
  if [ "$(stamp_tag "$1")" != "$(stamp_tag "$2")" ]; then echo unversioned; return 0; fi
  if [ "$1" = "$2" ]; then echo same; else echo changed; fi
}

short_tree() { printf '%s' "$(stamp_tree "$1")" | cut -c1-12; }

# Prints the line in both directions — refusing and overriding say the SAME
# thing, because the point is that the run is ABOUT a different tree, and that
# is true whether or not the lane chose it.
tree_change_report() {                # enq, now, override -> 0 proceed / 1 refuse
  case "$(tree_verdict "$1" "$2")" in
    same) return 0 ;;
    unknown)
      echo "TREE STAMP UNAVAILABLE — this run cannot verify the tree is the one it queued for" >&2
      return 0 ;;
    unversioned)
      # ACCEPT AND LOG, never refuse: the ticket predates the working-tree
      # stamp, so the two numbers answer different questions.  Refusing here
      # would strand a queue full of tenures for a defect that was the tool's.
      echo "TREE STAMP VERSION CHANGED since this ticket was enqueued ($(stamp_tag "$1") -> $(stamp_tag "$2"))." >&2
      echo "  The old stamp hashed the INDEX; this one hashes the WORKING TREE, so they cannot be" >&2
      echo "  compared. PROCEEDING — and this run's tree is NOT verified against its enqueue." >&2
      return 0 ;;
    changed)
      echo "TREE CHANGED SINCE ENQUEUE ($(short_tree "$1") → $(short_tree "$2"))" >&2
      if [ "$3" = "1" ]; then
        echo "  --build-current-tree: proceeding anyway. The verdict is about the CURRENT tree," >&2
        echo "  not the one that queued, and the coverage statement is about what built NOW." >&2
        return 0
      fi
      echo "  A queued tenure reads the source at BUILD time, so this run would verify a" >&2
      echo "  tree nobody asked it to. Re-enqueue, or pass --build-current-tree if you" >&2
      echo "  batched the edit deliberately." >&2
      return 1 ;;
  esac
}

# --------------------------------------------------------------- self-test
# §5.4's law, pointed at this script: every refusal path RUN, not admired.
# No Lean, no lock, no queue outside the temp dir it creates.
# ------------------------------------------------------- --classify (§5.4a)
# ---------------------------------------------- the green ledger (§5.4a-i)
#
# NOTHING RECORDED GREENS BEFORE THIS.  Only the lock and the queue persisted,
# both in /tmp and both ephemeral, so "the branch was green an hour ago" was a
# memory rather than evidence — and an increment cannot rest on a memory.
#
# PER WORKING DIRECTORY, not per repository: `--git-dir` rather than
# `--git-common-dir`, because a linked worktree has its OWN `.lake`, and the
# build cache is part of what produced the green.  Untracked, so it can never
# conflict on a rebase (the INDEX.md scar); inside the git dir, so it survives
# rebase and checkout.  A green recorded elsewhere is not VERIFIABLE here, and
# its absence here is honest: evidence does not travel by assumption.
green_ledger_path() {           # -> the ledger path, or '' when there is no git dir
  local d
  d="$(git -C "$CLONE" rev-parse --git-dir 2>/dev/null)" || return 1
  [ -n "$d" ] || return 1
  case "$d" in /*) ;; *) d="$CLONE/$d" ;; esac
  printf '%s/triad-greens' "$d"
}

# EVERY FIELD IS SPACE-FREE, so a line parses by splitting on spaces and needs
# no quoting rules.  Target and gate lists are comma-joined for that reason.
ledger_field() {                # line, key -> value
  printf '%s' "$1" | tr ' ' '\n' \
    | awk -F= -v k="$2" '$1 == k { print substr($0, length(k) + 2); exit }'
}

ledger_lookup() {               # full-sha -> the NEWEST green line for it
  local f; f="$(green_ledger_path)" || return 1
  [ -f "$f" ] || return 1
  grep "^green $1 " "$f" 2>/dev/null | tail -1
}

# A GREEN IS RECORDED ONLY WHEN THE WHOLE TRIAD WAS GREEN.  A red writes
# nothing: a ledger that recorded attempts would be a log, and a log is not
# evidence of a verdict.
record_green() {                # class, full(yes|no), root, depth, targets
  local f tree head citable tg
  f="$(green_ledger_path)" || return 0
  head="$(git -C "$CLONE" rev-parse HEAD 2>/dev/null)" || return 0
  # THE SAME BLINDNESS, ONE LEVEL DOWN.  This read `git write-tree` too, so a
  # green taken with an unstaged edit in the working tree recorded the INDEX's
  # hash and could be judged citable while the elaborated content was
  # something else.  One source: whatever lake read is what gets recorded.
  tree="$(worktree_tree 2>/dev/null || echo none)"
  # CITABLE IS THE TREE/COMMIT QUESTION.  The tenure certified the WORKING
  # TREE; if that is not the commit's tree, the sha names something the green
  # did not certify, and citing it as a base would over-claim.
  if [ "$tree" = "$(git -C "$CLONE" rev-parse HEAD^{tree} 2>/dev/null)" ]; then
    citable=yes
  else
    citable=no
  fi
  # EVERY FIELD MUST HAVE A VALUE.  An empty target list means the FULL build,
  # and `targets=` read back as the empty string — which the coverage line then
  # printed as a blank where the most important word belonged.  `sed s/^$/all/`
  # does not fire on empty INPUT: there is no line for it to match.
  tg="$(printf '%s' "${5:-}" | tr ' ' ',')"; [ -n "$tg" ] || tg="all"
  printf 'green %s tree=%s class=%s citable=%s full=%s root=%s depth=%s targets=%s gates=%s lane=%s ticket=%s at=%s\n' \
    "$head" "$tree" "$1" "$citable" "$2" "$3" "$4" "$tg" \
    "$(gate_names "$GATES" | tr -d ' ')" \
    "$LANE" "${TICKET:-none}" "$(date '+%Y-%m-%dT%H:%M:%S')" >> "$f" 2>/dev/null || true
}

# THE FIVE REFUSALS, all before a ticket is written.  A refusal costs one
# command; a wrong base costs a tenure AND publishes a coverage line nobody
# can check.
since_resolve() {               # uses SINCE; sets SINCE_ROOT/SINCE_LINE; 1 + reason on refusal
  local sha line root
  if [ "$SINCE" = "auto" ]; then
    echo "--since auto is not built yet (§5.4a-i phase 2). Name the sha of a recorded green:" >&2
    echo "  the ledger is $(green_ledger_path 2>/dev/null || echo '<no git dir>')" >&2
    return 1
  fi
  sha="$(git -C "$CLONE" rev-parse --verify --quiet "${SINCE}^{commit}" 2>/dev/null)"
  [ -n "$sha" ] || { echo "--since '$SINCE' is not a commit in this clone" >&2; return 1; }
  # AN INCREMENT MUST BE ON TOP OF ITS BASE.  This is also what makes a rebase
  # safe: a rebase writes NEW shas, so a green recorded before it stops being
  # an ancestor and is refused instead of silently naming rewritten content.
  git -C "$CLONE" merge-base --is-ancestor "$sha" HEAD 2>/dev/null || {
    echo "--since $(printf '%.12s' "$sha") is NOT AN ANCESTOR of HEAD, so this would not be an increment" >&2
    echo "  on top of it. (A rebase rewrites shas: a green from before one can never be cited.)" >&2
    return 1; }
  line="$(ledger_lookup "$sha")" || true
  [ -n "$line" ] || {
    echo "no green is RECORDED for $(printf '%.12s' "$sha") in $(green_ledger_path)" >&2
    echo "  A green is evidence, not a memory — and this clone holds no record of that one." >&2
    return 1; }
  [ "$(ledger_field "$line" citable)" = "yes" ] || {
    echo "the green at $(printf '%.12s' "$sha") is NOT CITABLE: it certified an INDEX tree that is not" >&2
    echo "  that commit's tree, so it covered staged work that was never committed." >&2
    return 1; }
  root="$(ledger_field "$line" root)"
  case "$root" in
    self) root="$sha" ;;
    ""|unknown)
      echo "the green at $(printf '%.12s' "$sha") has NO RESOLVABLE ROOT: it was itself a scoped green" >&2
      echo "  with no full build under it, so there is nothing sound to classify the increment" >&2
      echo "  against (§5.4a-i: against the ROOT, never the parent). Take one full green first." >&2
      return 1 ;;
  esac
  SINCE_ROOT="$root"; SINCE_LINE="$line"
  return 0
}

merge_target_ref() {
  # THE A13 CAVEAT, and it has caught four lanes: a seeded clone inherits the
  # peer's REMOTES, so `origin` can be a stale local bundle and
  # `origin/master` reads days back while `git rev-list HEAD..origin/master`
  # cheerfully reports 0.  Prefer `github/master`; either way, SAY which ref
  # the classification was taken against.
  local r rem h
  for r in github/master origin/master; do
    if git -C "$CLONE" rev-parse --verify --quiet "$r" >/dev/null 2>&1; then echo "$r"; return 0; fi
  done
  # `master` IS NOT A UNIVERSAL NAME.  The wasm fork's default branch is not
  # called master, so this returned nothing and the tenure fell back to a FULL
  # build — conservative, and therefore silent, which is how a heuristic stays
  # broken.  The remote itself records which branch is its head; ask it rather
  # than guessing a name.  Order is still a preference, not an assumption.
  for rem in github origin $(git -C "$CLONE" remote 2>/dev/null); do
    h="$(git -C "$CLONE" symbolic-ref --quiet "refs/remotes/$rem/HEAD" 2>/dev/null)" || continue
    [ -n "$h" ] || continue
    h="${h#refs/remotes/}"
    git -C "$CLONE" rev-parse --verify --quiet "$h" >/dev/null 2>&1 || continue
    echo "$h"; return 0
  done
  echo ""
}
# --------------------------------------------- what this diff WOULD classify
# `--classify` is OPT-IN, so a plain `--lane X` on a docs-only diff queues a
# FULL tenure — and the fuelMono lane's earlier tickets built far more than
# their floor without ever knowing there was a floor.  The fix could go two
# ways and the choice is not close:
#
#   (a) classify by DEFAULT, with --no-classify to opt out.  Rejected.
#       Classification NARROWS the build, so this makes narrowing the default:
#       every lane's coverage would then depend on the classifier being right,
#       with nobody having asked it to.  That is the exact reading the --gates
#       ruling rejected ("it takes the reading that cannot silently shrink a
#       gate set, and makes the other one explicit").  It also turns WORKING
#       runs into REFUSALS: --classify dies without a merge target, refuses on
#       unstaged Lean under a lake glob, and CONTRADICTS --foreign by design —
#       three hard stops imposed on invocations that asked for none of them.
#
#   (b) keep it opt-in and SAY, at enqueue, what the diff would classify as.
#       Chosen.  It is the note-explains-never-downgrades shape: the tenure
#       runs exactly as it always has, and the lane learns what it could have
#       taken instead — in the log, in time to act on the next one.
#
# ONE LINE, ALWAYS, INCLUDING WHEN IT CANNOT TELL.  Silence would be
# ambiguous between "your tenure is right-sized" and "the probe did not run".
#
# AND IT RUNS IN A SUBSHELL.  `classify_list` sets CLASS_RANK, CLASS_TIERS and
# BUILD_TARGETS; an advisory that leaked those would NARROW THE VERY BUILD IT
# is only supposed to describe.  `$( … )` cannot leak a variable — the trap
# this lane has been bitten by three times is, for once, precisely the tool.
# ------------------------------------ the delta a tenure is ABOUT (Ada, 2026-08)
#
# A VERDICT CERTIFIES A TREE, NEVER A TITLE.  The Ada adoption tenure went
# green on a tree that contained no adoption: the branch was docs-only, and the
# ONLY visible tell was that the build took four seconds.  A title is a claim
# about intent; the tree is what was elaborated, and when they disagree the
# green is about the tree.  So the tree is stated in the log's first lines,
# where a mismatch is self-evident before anyone waits for a build.
#
# PURE GIT, at enqueue only: no lake, no tenure, nothing that can fail a run.
#
# THE ABSENCE FAMILY.  `master` is not reachable from every tenure — a foreign
# checkout has its own unrelated master, and a seeded clone may have neither
# ref.  Each of those is a DIFFERENT absence and none of them may take the
# success path: "0 files" is a measurement (this branch IS master), "n/a" is
# the admission that nothing was measured, and the two must never print alike.
delta_vs_master() {             # -> the one-line summary; never fails a run
  local base mb files lean f nondocs=""
  # A foreign checkout's `origin/master` is a DIFFERENT PROJECT's master, so
  # this is refused rather than attempted: a number computed against the wrong
  # master is worse than no number (§7.1a).
  [ "$FOREIGN" = "1" ] && { printf 'n/a (foreign tree)'; return 0; }
  base="$(merge_target_ref)"
  [ -n "$base" ] || { printf 'n/a (no github/master or origin/master in this clone)'; return 0; }
  mb="$(git -C "$CLONE" merge-base "$base" HEAD 2>/dev/null)"
  [ -n "$mb" ] || { printf 'n/a (no merge base with %s — unrelated histories)' "$base"; return 0; }
  files="$(git -C "$CLONE" diff --name-only "$mb..HEAD" 2>/dev/null | grep -c . || true)"
  [ "$files" = "0" ] && { printf '0 files (HEAD is at %s)' "$base"; return 0; }
  lean="$(git -C "$CLONE" diff --name-only "$mb..HEAD" 2>/dev/null | grep -c '\.lean$' || true)"
  printf '%s file(s), %s .lean' "$files" "$lean"
  [ "$lean" != "0" ] && return 0
  # NO `.lean` IS NOT THE SAME AS DOCS-ONLY, and labelling it so would repeat
  # the incident one level down: `lakefile.toml`, `lean-toolchain` and
  # `lake-manifest.json` carry no `.lean` and invalidate the WHOLE graph.  The
  # label is asked of the classifier that already answers this question.
  for f in $(git -C "$CLONE" diff --name-only "$mb..HEAD" 2>/dev/null); do
    [ "$(classify_path "$f")" = "docs" ] || { nondocs="$f"; break; }
  done
  if [ -n "$nondocs" ]; then printf ' — NOT docs-only (%s)' "$nondocs"
  else printf ' — DOCS-ONLY'; fi
}

# ------------------------------- was this ticket's base ever green? (pyc, 2026-08-24)
#
# THE PYC LANE PAID 116 MINUTES FOR THIS: 4852s queued plus 2083s building, to
# rediscover a defect that was ALREADY FIXED on master three minutes into its
# own build.  Its base was red for a full build when committed, and nothing
# checked whether master had moved past it — least of all during a queue wait
# hours deep, which is precisely when the fix lands.
#
# WARN, NEVER REFUSE.  A pinned base is legitimate: the SV lane declined a
# rebase the same day for tree-certification reasons, and a guard that refused
# would have been wrong about that lane while being right about this one.  A
# wrong warning costs a line; a wrong refusal costs a tenure.
#
# READ-ONLY, AND IT DOES NOT MOVE THE LANE'S REFS.  Measured while writing
# this: `git fetch origin master:refs/triad/tip` DOES advance `origin/master`,
# because git updates remote-tracking refs OPPORTUNISTICALLY for any fetched
# ref that maps to one.  Fetching by URL has no configured mapping, so nothing
# is opportunistically updated.  A diagnostic must not move the state the lane
# is about to be judged against.
TIP_REF="refs/triad/tip"
# A SUBSHELL CANNOT SET A PARENT'S VARIABLE.  The first cut returned the sha on
# stdout and the REASON in a global, so every caller — all of which use
# `$( … )` — read an empty reason and printed `n/a ()`.  That is this lane's
# fourth encounter with the same trap, so the answer is carried the only way
# that survives a subshell: IN THE VALUE.  A leading `!` marks a reason.
# The cache is a FILE for the same reason, the way laws.sh --budget writes its
# PARTIAL verdict to one.
TIP_CACHE_FILE="${TMPDIR:-/tmp}/triad-tip.$$"
remote_tip() {                  # [fresh] -> "<sha>" | "!<reason>"
  local base rem br url sha
  [ "${1:-}" = "fresh" ] && rm -f "$TIP_CACHE_FILE"
  if [ -s "$TIP_CACHE_FILE" ]; then cat "$TIP_CACHE_FILE"; return 0; fi
  base="$(merge_target_ref)"
  [ -n "$base" ] || { printf '!no github/master or origin/master in this clone' | tee "$TIP_CACHE_FILE"; return 0; }
  rem="${base%%/*}"; br="${base#*/}"
  url="$(git -C "$CLONE" remote get-url "$rem" 2>/dev/null || true)"
  [ -n "$url" ] || { printf "!remote '%s' has no URL" "$rem" | tee "$TIP_CACHE_FILE"; return 0; }
  git -C "$CLONE" update-ref -d "$TIP_REF" 2>/dev/null || true
  # BOUNDED AND NON-INTERACTIVE.  An enqueue must never block on a network
  # hang or an auth prompt: a diagnostic that can stall the thing it describes
  # is worse than no diagnostic.
  if ! timeout 25 env GIT_TERMINAL_PROMPT=0 GIT_SSH_COMMAND="ssh -oBatchMode=yes" \
       git -C "$CLONE" fetch -q --no-tags "$url" "$br:$TIP_REF" >/dev/null 2>&1; then
    printf '!could not reach %s (offline, or it declined)' "$rem" | tee "$TIP_CACHE_FILE"; return 0
  fi
  sha="$(git -C "$CLONE" rev-parse "$TIP_REF" 2>/dev/null)"
  [ -n "$sha" ] || { printf '!fetched nothing from %s' "$rem" | tee "$TIP_CACHE_FILE"; return 0; }
  printf '%s' "$sha" | tee "$TIP_CACHE_FILE"
}

base_staleness() {              # [fresh] -> the line; never fails a run
  local tip base rem url mb behind note=""
  [ "$FOREIGN" = "1" ] && { printf 'n/a (foreign tree)'; return 0; }
  tip="$(remote_tip "${1:-}")"
  case "$tip" in !*) printf 'n/a (%s)' "${tip#!}"; return 0 ;; esac
  base="$(merge_target_ref)"; rem="${base%%/*}"
  url="$(git -C "$CLONE" remote get-url "$rem" 2>/dev/null || true)"
  # A13 AGAIN, and here it would make the check LIE: a seeded clone's origin
  # can be a local bundle, whose tip is days behind github's and would report
  # a stale base as current.  The check still runs; the line says what it is.
  case "$url" in /*|file:*|*.bundle) note=" [A13: '$rem' is a LOCAL path — its tip may not be github's]" ;; esac
  mb="$(git -C "$CLONE" merge-base "$tip" HEAD 2>/dev/null)"
  [ -n "$mb" ] || { printf 'n/a (no merge base with %s — unrelated histories)' "$base"; return 0; }
  behind="$(git -C "$CLONE" rev-list --count "$mb..$tip" 2>/dev/null || echo 0)"
  if [ "$behind" = "0" ]; then
    printf 'base %s is AT the %s tip%s' "$(git -C "$CLONE" rev-parse --short "$mb" 2>/dev/null)" "$base" "$note"
  else
    printf 'BASE STALE: %s commit(s) behind %s tip %s (this ticket branches from %s) — consider rebasing before it runs%s' \
      "$behind" "$base" "$(git -C "$CLONE" rev-parse --short "$tip" 2>/dev/null)" \
      "$(git -C "$CLONE" rev-parse --short "$mb" 2>/dev/null)" "$note"
  fi
}

# THE ONE REFUSAL IN THIS FAMILY, and it is narrow by construction: a NEW
# enqueue from a worktree whose triad.sh predates master's stamp version.
#
# The leantier successor created a fresh ticket under a pre-rebase v1
# triad.sh with an unstaged rewrite; accept-and-log is for tickets ALREADY IN
# FLIGHT, never for new ones, and the distinction is the whole reason this can
# refuse where the staleness line only warns.  It fires only on an un-rebased
# worktree, it is local once the tip is fetched, and an ABSENT answer is never
# a refusal — not knowing master's version is not evidence that ours is old.
stamp_version_guard() {
  local tip theirs
  [ "$FOREIGN" = "1" ] && return 0
  tip="$(remote_tip)"
  case "$tip" in !*) return 0 ;; esac      # an absent answer is never a refusal
  theirs="$(git -C "$CLONE" show "$tip:tools/triad.sh" 2>/dev/null \
            | awk -F'"' '/^STAMP_VERSION=/ { print $2; exit }')"
  [ -n "$theirs" ] || return 0
  case "${theirs#v}${STAMP_VERSION#v}" in *[!0-9]*) return 0 ;; esac
  [ "${theirs#v}" -gt "${STAMP_VERSION#v}" ] || return 0
  local tipshort; tipshort="$(git -C "$CLONE" rev-parse --short "$tip" 2>/dev/null)"
  die "this worktree's triad.sh stamps $STAMP_VERSION but master's stamps $theirs.
  A ticket enqueued here would be judged by an OLDER rule than the one master enforces —
  which is how a fresh ticket gets an unstaged rewrite past the guard.
  Commit or stash, rebase onto $tipshort, and re-run.
  (A ticket already IN FLIGHT is accepted-and-logged; a NEW one is not.)"
}

class_hint() {                  # -> the advisory text; never refuses, never narrows
  local base changed cls
  base="$AGAINST"; [ -n "$base" ] || base="$(merge_target_ref)"
  [ -n "$base" ] || { printf 'not computed (no merge target: neither github/master nor origin/master) — the tenure is FULL'; return 0; }
  changed="$( { git -C "$CLONE" diff --name-only "$base...HEAD" 2>/dev/null
                git -C "$CLONE" diff --name-only --cached 2>/dev/null; } | sort -u )"
  # An empty diff is not a docs-only landing; it is a measurement of nothing,
  # and the full tenure is the safe reading — the same rule --classify uses.
  [ -n "$changed" ] || { printf 'not computed (nothing staged or committed against %s) — the tenure is FULL' "$base"; return 0; }
  classify_list <<< "$changed"
  cls="$(class_name "$CLASS_RANK")"
  case "$cls" in
    docs)  printf 'this diff classifies DOCS against %s — a FULL tenure was queued anyway. --classify takes the floor, and a docs-only landing owes NO TENURE AT ALL' "$base" ;;
    spine) printf 'this diff classifies SPINE against %s — a full tenure is what it owes' "$base" ;;
    *)     printf 'this diff classifies %s against %s (tiers: %s) — a FULL tenure was queued anyway; --classify would build `lake build %s`' \
                  "$cls" "$base" "${CLASS_TIERS:-none}" "${BUILD_TARGETS:-<all default targets>}" ;;
  esac
}

# ------------------------------- a gate spec is CODE (the ES lane, 2026-08-24)
#
# `--gates` was split with `IFS=';'`, which is shell WORD SPLITTING and knows
# nothing about quotes.  ES's
#
#     python3 -c "import json; d=json.load(...); assert ...; print(...)"
#
# became FIVE fragments, each run as its own gate, each failing: a green build
# with five GATE FAILED lines nominally about a JSON file, and NOT ONE OF THEM
# READ THE FILE.
#
# > "A red that looks like diligence is worse than no gate, because the natural
# > repair is to make the red go away — which would have left the register
# > permanently unchecked."  (ES)
#
# That is the whole reason this refuses rather than repairs quietly: the
# fragments were not a broken gate, they were a CONVINCING one.
#
# THE SEPARATOR IS AN UNQUOTED `;`.  A quoted one belongs to the command, and
# the scanner below is what tells them apart — the same scan is needed either
# way, so splitting correctly and refusing precisely cost the same.
gate_split() {          # "a; b" -> one gate per line, splitting on UNQUOTED ';'
  printf '%s' "$1" | awk '
    {
      n = length($0); out = ""; sq = 0; dq = 0
      for (i = 1; i <= n; i++) {
        c = substr($0, i, 1)
        # A backslash inside double quotes escapes the next character, so a
        # `\"` does not close the string and a `\;` is not a separator.
        if (c == "\\" && dq && i < n) { out = out c substr($0, i + 1, 1); i++; continue }
        if (c == "\047" && !dq) { sq = !sq; out = out c; continue }
        if (c == "\"" && !sq)   { dq = !dq; out = out c; continue }
        if (c == ";" && !sq && !dq) { print out; out = ""; continue }
        out = out c
      }
      print out
    }'
}

# Does this ONE gate carry a `;` inside its quotes?  That is the ES shape, and
# it is refused rather than run, because a gate list that stays one command per
# entry is one a lane can read, grep and reason about — and inline
# multi-statement code in a gate list is how the fragmenting happened at all.
gate_has_quoted_semicolon() {   # gate -> 0 when a ';' sits inside quotes
  printf '%s' "$1" | awk '
    { n = length($0); sq = 0; dq = 0
      for (i = 1; i <= n; i++) {
        c = substr($0, i, 1)
        if (c == "\\" && dq && i < n) { i++; continue }
        if (c == "\047" && !dq) { sq = !sq; continue }
        if (c == "\"" && !sq)   { dq = !dq; continue }
        if (c == ";" && (sq || dq)) { found = 1 }
      }
    }
    END { exit(found ? 0 : 1) }'
}

# THE REFUSAL, computed before a ticket exists.  Two shapes, both silent today:
# a quoted `;` (fragmented into a convincing red), and a STRAY separator that
# yields an EMPTY gate — `a;; b` or a trailing `a;` — which `run_gates` used to
# swallow with `[ -n "$g" ] || continue`.  A gate list that silently contains
# nothing where a gate was meant is the same defect one step earlier.
gate_spec_refusal() {   # gate list -> a reason on stdout, or nothing
  local g i=0
  while IFS= read -r g; do
    i=$((i + 1))
    if gate_has_quoted_semicolon "$g"; then
      printf "gate %s contains an internal ';' inside quotes — ONE COMMAND PER GATE.\n" "$i"
      printf "    %s\n" "$(printf '%s' "$g" | cut -c1-96)"
      printf "  Splitting it would fragment one command into several, each failing on its own\n"
      printf "  and none doing the check (the ES lane got five false GATE FAILED lines this way).\n"
      printf "  Put the body in a script and name the script here.\n"
      return 0
    fi
    case "$(printf '%s' "$g" | tr -d ' \t')" in
      "") printf "gate %s is EMPTY — a stray ';' in the gate list.\n" "$i"
          printf "  An empty gate was silently skipped, so a mistyped separator removed a check\n"
          printf "  without removing a line from the list.\n"
          return 0 ;;
    esac
  done <<EOF
$(gate_split "$1")
EOF
  return 1
}

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

  # ---- the gate phase's own build (the R-track's finding)
  echo "  -- gate-phase build"
  check "exe names are READ from the lakefile" \
        "$(lake_exe_names | tr '\n' ' ' | sed 's/ *$//')" "leanmodels-run circuit-dc-runner"
  check "the tier floor needs the runner"      "$(gate_runner_targets "$(gate_floor tier)")" "leanmodels-run"
  check "the docs floor needs NO runner"       "$(gate_runner_targets "$(gate_floor docs)")" ""
  check "script_corpus needs it too"           "$(gate_runner_targets 'python3 harness/script_corpus.py')" "leanmodels-run"
  check "a NAMED exe is taken literally"       "$(gate_runner_targets 'sh -c "lake exe circuit-dc-runner"')" "circuit-dc-runner"
  check "an unrelated gate needs nothing"      "$(gate_runner_targets 'python3 tools/docs_check.py')" ""
  # PROPERTY: after the gate-phase build, the gates must not build the tree.
  # `--no-build` is diff_test's own documented flag, and it is the mechanism
  # by which a narrowed run's log carries NO full-build lines from the gates.
  check "diff_test is told the runner is ready" \
        "$(announce_prebuilt "$(gate_floor tier)")" \
        "$(printf '%s' "$DEFAULT_FLOOR" | sed 's|harness/diff_test.py|harness/diff_test.py --no-build|')"
  # COUNTED ON diff_test's OWN SEGMENT.  A bare count of `--no-build` across
  # the floor started reading 2 the moment refusal_census joined it carrying
  # its own — which says nothing about the flag this function adds.
  check "  ...and it is said exactly once"     \
        "$(announce_prebuilt "$(gate_floor tier)" | grep -o -- 'diff_test.py --no-build' | grep -c .)" "1"
  check "  ...idempotently"                    \
        "$(announce_prebuilt "$(announce_prebuilt "$(gate_floor tier)")" | grep -o -- 'diff_test.py --no-build' | grep -c .)" "1"
  check "  ...and the census keeps its own"    \
        "$(announce_prebuilt "$(gate_floor tier)" | grep -o -- 'refusal_census.py --whitelist --no-build' | grep -c .)" "1"
  check "a non-diff_test gate is left ALONE"   \
        "$(announce_prebuilt 'python3 harness/script_corpus.py')" "python3 harness/script_corpus.py"

  # ---- a stale generated index (§9.5's collision, moved off the §-numbers)
  echo "  -- stale index"
  idx="$tmp/idxclone"
  mkdir -p "$idx/tools" "$idx/docs/backlog"
  cp "$CLONE/tools/backlog-index.sh" "$idx/tools/" 2>/dev/null
  printf '# a lane\n\n## 2026-08-23-a-1 — first\n' > "$idx/docs/backlog/a.md"
  "$idx/tools/backlog-index.sh" --dir "$idx" >/dev/null 2>&1
  check "a freshly generated index is not stale" "$(index_is_stale "$idx" && echo stale)" ""
  printf '\n## 2026-08-23-a-2 — appended, not regenerated\n' >> "$idx/docs/backlog/a.md"
  check "an un-regenerated index IS stale"       "$(index_is_stale "$idx" && echo stale)" "stale"
  "$idx/tools/backlog-index.sh" --dir "$idx" >/dev/null 2>&1
  check "regenerating clears it"                 "$(index_is_stale "$idx" && echo stale)" ""
  check "no generator means nothing to be stale about" \
        "$(index_is_stale "$tmp/nonexistent" && echo stale)" ""

  # ---- --gates ADDS, --gates-only REPLACES (the Ada lane's 78-minute tenure)
  echo "  -- gate composition"
  fl='python3 tools/docs_check.py; python3 harness/diff_test.py'
  check "no lane gates -> the floor alone" "$(gates_compose "$fl" "" 0)" "$fl"
  check "--gates ADDS to the floor"        "$(gates_compose "$fl" 'python3 harness/script_corpus.py' 0)" \
        "$fl; python3 harness/script_corpus.py"
  check "  ...so the differential SURVIVES" \
        "$(gates_compose "$fl" 'python3 tools/docs_check.py' 0 | grep -c diff_test)" "1"
  check "--gates-only REPLACES"            "$(gates_compose "$fl" 'python3 tools/docs_check.py' 1)" \
        "python3 tools/docs_check.py"
  check "  ...and it is ANNOUNCED"         "$(gates_only_notice "$fl" 1 | grep -c 'THE CLASS FLOOR IS NOT RUNNING')" "1"
  check "  ...naming what is skipped"      "$(gates_only_notice "$fl" 1 | grep -c 'docs_check, diff_test')" "1"
  check "additive mode announces nothing"  "$(gates_only_notice "$fl" 0)" ""

  # ---- THE FLOOR'S COMPOSITION (the 2026-08-23 ruling)
  echo "  -- floor composition"
  check "the non-docs floor carries the census" \
        "$(gate_floor tier | grep -c 'refusal_census.py --whitelist --no-build')" "1"
  check "  ...and so does spine"               "$(gate_floor spine | grep -c 'refusal_census')" "1"
  # A DOCS LANDING OWES NO LEAN, so a gate that runs the model has no place in
  # its floor — that is the whole reason the docs class exists.
  check "the DOCS floor does not"              "$(gate_floor docs | grep -c 'refusal_census')" "0"
  check "  ...and is docs_check alone"         "$(gate_floor docs)" "python3 tools/docs_check.py"
  # ONE SPELLING: the classified path (gate_floor) and the unclassified path
  # (DEFAULT_FLOOR) must not be able to run different gates.
  check "both paths read ONE floor"            "$(gate_floor tier)" "$DEFAULT_FLOOR"
  # `--no-build` is part of the line, not an afterthought: the tenure prebuilds
  # the runner, and a gate that builds turns a build defect into a gate failure.
  check "the census never builds inside a gate" \
        "$(gate_floor tier | grep -c 'refusal_census.py --whitelist --no-build')" "1"
  # ...which only works if the tenure KNOWS to prebuild the runner for it.
  check "a census-only gate list still prebuilds" \
        "$(gate_runner_targets 'python3 harness/refusal_census.py --whitelist --no-build')" "leanmodels-run"
  check "  ...and the floor as a whole does"   "$(gate_runner_targets "$DEFAULT_FLOOR")" "leanmodels-run"
  check "the label says WHY the gate appeared" "$(printf '%s' "$FLOOR_LABEL" | grep -c 'refusal_census')" "1"
  check "  ...and names the invariant"         "$(printf '%s' "$FLOOR_LABEL" | grep -c '§5.2')" "1"

  # ---- THE CLASS ADVISORY (the fuelMono lane's full tenures on docs diffs)
  echo "  -- class advisory"
  ch="$tmp/classhint"; mkdir -p "$ch/docs" "$ch/LeanModels/Core"
  git init -q "$ch" 2>/dev/null
  git -C "$ch" config user.email qol@example; git -C "$ch" config user.name qol
  printf 'name = "x"\n[[lean_lib]]\nname = "LeanModels"\n' > "$ch/lakefile.toml"
  printf '# d\n' > "$ch/docs/a.md"; printf -- '-- m\n' > "$ch/LeanModels/M.lean"
  git -C "$ch" add -A; git -C "$ch" commit -qm base
  git -C "$ch" update-ref refs/remotes/origin/master HEAD
  saved_cl="$CLONE"; saved_ag="${AGAINST:-}"; CLONE="$ch"; AGAINST=""

  # A repo with a merge target but NOTHING against it: an empty diff measured
  # nothing, and the full tenure is the safe reading — never "docs-only".
  check "an empty diff is not a docs landing" "$(class_hint | grep -c 'nothing staged or committed')" "1"
  check "  ...and says the tenure is FULL"    "$(class_hint | grep -c 'the tenure is FULL')" "1"

  printf '# more\n' >> "$ch/docs/a.md"; git -C "$ch" add -A; git -C "$ch" commit -qm docs
  out="$(class_hint)"
  check "a docs-only diff classifies DOCS"    "$(printf '%s' "$out" | grep -c 'classifies DOCS')" "1"
  check "  ...naming what was queued anyway"  "$(printf '%s' "$out" | grep -c 'a FULL tenure was queued anyway')" "1"
  check "  ...and that it owes no tenure"     "$(printf '%s' "$out" | grep -c 'owes NO TENURE AT ALL')" "1"

  # THE ROW THIS FEATURE LIVES OR DIES BY.  classify_list sets BUILD_TARGETS;
  # an advisory that leaked it would NARROW the very build it only describes.
  BUILD_TARGETS="SENTINEL"; CLASS_RANK=0
  out="$(class_hint)"
  check "the advisory cannot narrow the build" "$BUILD_TARGETS" "SENTINEL"
  check "  ...nor move the class rank"         "$CLASS_RANK" "0"
  BUILD_TARGETS=""

  printf -- '-- edit\n' >> "$ch/LeanModels/M.lean"; git -C "$ch" add -A; git -C "$ch" commit -qm tier
  check "a Lean diff does NOT say docs"       "$(class_hint | grep -c 'classifies DOCS')" "0"
  printf 'name2 = "x2"\n' >> "$ch/lakefile.toml"; git -C "$ch" add -A; git -C "$ch" commit -qm spine
  check "a lakefile change is SPINE"          "$(class_hint | grep -c 'classifies SPINE')" "1"
  check "  ...and a full tenure is right"     "$(class_hint | grep -c 'is what it owes')" "1"

  # NO MERGE TARGET IS NOT A REFUSAL.  `--classify` dies here, and that is
  # correct for a lane that ASKED to classify; an advisory that died would
  # turn every plain tenure in such a clone into a hard stop.
  nb="$tmp/nobase"; mkdir -p "$nb"; git init -q "$nb" 2>/dev/null
  git -C "$nb" config user.email qol@example; git -C "$nb" config user.name qol
  printf 'x\n' > "$nb/a.txt"; git -C "$nb" add -A; git -C "$nb" commit -qm base
  CLONE="$nb"
  check "no merge target is NOT fatal"        "$(class_hint >/dev/null 2>&1; echo $?)" "0"
  check "  ...and it says so, naming both refs" "$(class_hint | grep -c 'neither github/master nor origin/master')" "1"
  CLONE="$saved_cl"; AGAINST="$saved_ag"

  # ---- THE STAMP HASHES WHAT LAKE READS (the wasm lane's integrity hole)
  echo "  -- working-tree stamp"
  ws="$tmp/wstamp"; mkdir -p "$ws"; git init -q "$ws" 2>/dev/null
  git -C "$ws" config user.email qol@example; git -C "$ws" config user.name qol
  printf 'one\n' > "$ws/f.lean"; git -C "$ws" add -A; git -C "$ws" commit -qm base
  saved_cl="$CLONE"; CLONE="$ws"
  enq2="$(tree_stamp)"
  check "the stamp carries its version"       "$(stamp_tag "$enq2")" "v2"
  check "  ...and its tree is still readable" "$(short_tree "$enq2")" "$(git -C "$ws" rev-parse HEAD^{tree} | cut -c1-12)"

  # (a) A WORKING-TREE-ONLY EDIT: unstaged, uncommitted.  `lake` compiles THIS
  # file, so the stamp MUST move.  Under the index stamp it did not — that is
  # the hole, and the second row is its regression test: the old number is
  # provably unmoved by the same edit.
  printf 'two\n' > "$ws/f.lean"
  check "an UNSTAGED edit IS a changed tree"  "$(tree_verdict "$enq2" "$(tree_stamp)")" "changed"
  check "  ...and the INDEX stamp misses it"  \
        "$( [ "$(git -C "$ws" write-tree)" = "$(stamp_tree "$enq2")" ] && echo unmoved || echo moved )" "unmoved"
  printf 'one\n' > "$ws/f.lean"
  check "restoring it restores the stamp"     "$(tree_verdict "$enq2" "$(tree_stamp)")" "same"

  # (c) AN UNTRACKED FILE.  A new `.lean` that nothing staged is exactly what
  # must not slip into a tenure: lake will happily compile it.
  printf 'new\n' > "$ws/g.lean"
  check "an UNTRACKED file IS a changed tree" "$(tree_verdict "$enq2" "$(tree_stamp)")" "changed"
  rm -f "$ws/g.lean"

  # (b) AN INDEX-ONLY EDIT: staged, then the working tree put back.  THE STAMP
  # ACCEPTS IT, and that is the correct reading — `lake` reads the working
  # tree, so content that exists only in the index will not be elaborated and
  # is not part of what this tenure certifies.  The old index stamp REFUSED
  # this case, which was a false alarm in the opposite direction.
  printf 'staged\n' > "$ws/f.lean"; git -C "$ws" add f.lean; printf 'one\n' > "$ws/f.lean"
  check "an INDEX-only edit is NOT a change"  "$(tree_verdict "$enq2" "$(tree_stamp)")" "same"
  check "  ...though the index stamp moved"   \
        "$( [ "$(git -C "$ws" write-tree)" = "$(stamp_tree "$enq2")" ] && echo unmoved || echo moved )" "moved"
  git -C "$ws" reset -q

  # IGNORED BUILD OUTPUT MUST NOT DEFEAT THE STAMP: `.lake` churns during every
  # build, and a stamp that moved with it would refuse every second attempt.
  printf '.lake/\n' > "$ws/.gitignore"; git -C "$ws" add -A; git -C "$ws" commit -qm ignore
  enq3="$(tree_stamp)"
  mkdir -p "$ws/.lake"; printf 'artifact\n' > "$ws/.lake/out"
  check "ignored output does not move it"     "$(tree_verdict "$enq3" "$(tree_stamp)")" "same"

  # A SYMLINKED CLONE PATH still stamps the same tree (`git -C` resolves it).
  ln -sf "$ws" "$tmp/wslink"
  CLONE="$tmp/wslink"
  check "a symlinked clone stamps alike"      "$(stamp_tree "$(tree_stamp)")" "$(stamp_tree "$enq3")"
  CLONE="$ws"

  # OLD TICKETS ARE NOT STRANDED.  Eight tenures were live when this landed;
  # their stamps hashed the index, and comparing the two would have refused
  # every one of them for a defect that was the tool's.
  check "a v1 stamp is UNVERSIONED, not changed" "$(tree_verdict "abc123 HEAD1" "$(tree_stamp)")" "unversioned"
  out="$(tree_change_report "abc123 HEAD1" "$(tree_stamp)" 0 2>&1)"; rc=$?
  check "  ...and it PROCEEDS"                "$rc" "0"
  check "  ...saying the tree is NOT verified" "$(printf '%s' "$out" | grep -c 'NOT verified against its enqueue')" "1"
  check "  ...naming both questions"          "$(printf '%s' "$out" | grep -c 'INDEX.*WORKING TREE')" "1"
  check "a v1 stamp still shortens"           "$(short_tree 'abc123def4567890 HEAD1')" "abc123def456"
  CLONE="$saved_cl"

  # ---- THE DELTA A TENURE IS ABOUT (the Ada wrong-tree incident)
  echo "  -- delta vs master"
  dv="$tmp/delta"; mkdir -p "$dv/docs" "$dv/LeanModels"; git init -q "$dv" 2>/dev/null
  git -C "$dv" config user.email qol@example; git -C "$dv" config user.name qol
  printf 'name = "x"\n[[lean_lib]]\nname = "LeanModels"\n' > "$dv/lakefile.toml"
  printf '# d\n' > "$dv/docs/a.md"; printf -- '-- m\n' > "$dv/LeanModels/M.lean"
  git -C "$dv" add -A; git -C "$dv" commit -qm base
  git -C "$dv" update-ref refs/remotes/origin/master HEAD
  saved_cl="$CLONE"; saved_fg="$FOREIGN"; CLONE="$dv"; FOREIGN=0

  # A branch that IS master measured 0 — a measurement, not an absence.
  check "no delta says so as a MEASUREMENT" "$(delta_vs_master)" "0 files (HEAD is at origin/master)"
  # THE INCIDENT'S OWN SHAPE: a docs-only tree under any title at all.
  printf '# more\n' >> "$dv/docs/a.md"; git -C "$dv" add -A; git -C "$dv" commit -qm docs
  check "a docs-only delta is LABELLED"     "$(delta_vs_master)" "1 file(s), 0 .lean — DOCS-ONLY"
  # ...and the direction that would repeat it one level down: no `.lean` is
  # NOT docs-only when the lakefile moved.
  printf 'extra = 1\n' >> "$dv/lakefile.toml"; git -C "$dv" add -A; git -C "$dv" commit -qm lakefile
  check "0 .lean is NOT docs-only alone"    "$(delta_vs_master)" "2 file(s), 0 .lean — NOT docs-only (lakefile.toml)"
  printf -- '-- edit\n' >> "$dv/LeanModels/M.lean"; git -C "$dv" add -A; git -C "$dv" commit -qm lean
  check "a Lean delta counts the .lean"     "$(delta_vs_master)" "3 file(s), 1 .lean"

  # THE ABSENCE FAMILY: three different absences, none of them "0 files".
  FOREIGN=1
  check "a foreign tree refuses to compare" "$(delta_vs_master)" "n/a (foreign tree)"
  FOREIGN=0
  nm="$tmp/nomaster"; mkdir -p "$nm"; git init -q "$nm" 2>/dev/null
  git -C "$nm" config user.email qol@example; git -C "$nm" config user.name qol
  printf 'x\n' > "$nm/a.txt"; git -C "$nm" add -A; git -C "$nm" commit -qm base
  # CAPTURED, never named: `git init`'s default branch is `master` on some
  # versions and `main` on others, and a fixture that assumes one silently
  # skips its own case on the other — the first cut asserted the WRONG absence
  # because `rev-parse master` failed and no ref was ever created.
  nm_first="$(git -C "$nm" rev-parse HEAD)"
  CLONE="$nm"
  check "no merge target is NAMED, not zero" "$(delta_vs_master)" "n/a (no github/master or origin/master in this clone)"

  # A FORK WHOSE DEFAULT BRANCH IS NOT `master` (the wasm lane).  The remote
  # RECORDS its head; asking it beats guessing a name, and guessing failed
  # CONSERVATIVELY — a full tenure every time, which is why nobody noticed.
  git -C "$nm" update-ref refs/remotes/upstream/main "$nm_first"
  git -C "$nm" symbolic-ref refs/remotes/upstream/HEAD refs/remotes/upstream/main
  git -C "$nm" remote add upstream /dev/null 2>/dev/null || true
  check "a fork's HEAD ref is the fallback"  "$(merge_target_ref)" "upstream/main"
  check "  ...and the delta uses it"         "$(delta_vs_master | grep -c 'upstream/main')" "1"
  git -C "$nm" symbolic-ref -d refs/remotes/upstream/HEAD 2>/dev/null
  git -C "$nm" update-ref -d refs/remotes/upstream/main 2>/dev/null
  git -C "$nm" remote remove upstream 2>/dev/null || true
  check "with neither, it is still empty"    "$(merge_target_ref)" ""
  # An unrelated history has the ref but no merge base — a THIRD absence.
  git -C "$nm" checkout -q --orphan other; printf 'y\n' > "$nm/b.txt"
  git -C "$nm" add -A; git -C "$nm" commit -qm orphan
  git -C "$nm" update-ref refs/remotes/origin/master "$nm_first"
  check "unrelated histories are their own n/a" \
        "$(delta_vs_master)" "n/a (no merge base with origin/master — unrelated histories)"
  CLONE="$saved_cl"; FOREIGN="$saved_fg"

  # ---- A GATE SPEC IS CODE (the ES lane's five false GATE FAILED lines)
  echo "  -- gate spec quoting"
  es='python3 -c "import json; d=json.load(open(\"r.json\")); assert d; print(1)"'
  # THE DEFECT, reproduced: `IFS=';'` is word splitting and knows no quotes.
  oi="$IFS"; IFS=';'; nfrag=0; for _f in $es; do nfrag=$((nfrag+1)); done; IFS="$oi"
  check "IFS splitting FRAGMENTS one command"  "$( [ "$nfrag" -gt 1 ] && echo fragmented)" "fragmented"
  check "  ...while gate_split keeps it whole" "$(gate_split "$es" | grep -c .)" "1"
  # ...and it is REFUSED, at the cheap end, naming the gate and the reason.
  out="$(gate_spec_refusal "$es")"
  check "a quoted ';' is REFUSED"              "$(printf '%s' "$out" | grep -c "internal ';' inside quotes")" "1"
  check "  ...naming ONE COMMAND PER GATE"     "$(printf '%s' "$out" | grep -c 'ONE COMMAND PER GATE')" "1"
  check "  ...and saying what to do instead"   "$(printf '%s' "$out" | grep -c 'Put the body in a script')" "1"
  # A STRAY SEPARATOR yields an EMPTY gate, which run_gates used to swallow —
  # a mistyped ';' removed a CHECK without removing a LINE.
  check "a stray ';' is REFUSED"               "$(gate_spec_refusal 'python3 a.py;; python3 b.py' | grep -c 'is EMPTY')" "1"
  # A TRAILING ';' IS DIFFERENT, and the difference is measured rather than
  # assumed: command substitution STRIPS trailing newlines, so the empty
  # fragment after a final ';' never reaches the reader and no gate is lost.
  # The interior case above is the one that can hide a deleted check.
  check "  ...while a TRAILING ';' loses nothing" "$(gate_split 'python3 a.py;' | grep -c .)" "1"
  check "  ...so it is accepted"               "$(gate_spec_refusal 'python3 a.py;' >/dev/null && echo refused || echo accepted)" "accepted"

  # THE EXISTING SPECS ARE UNCHANGED, which is the half that must not regress:
  # every unquoted ';' is still a separator, including the floor's own two.
  check "the floor still splits into three"    "$(gate_split "$DEFAULT_FLOOR" | grep -c .)" "3"
  check "  ...and is NOT refused"              "$(gate_spec_refusal "$DEFAULT_FLOOR" >/dev/null && echo refused || echo accepted)" "accepted"
  check "a single command is one gate"         "$(gate_split 'python3 tools/docs_check.py' | grep -c .)" "1"
  check "  ...and is not refused"              "$(gate_spec_refusal 'python3 tools/docs_check.py' >/dev/null && echo refused || echo accepted)" "accepted"
  # A QUOTED ARGUMENT WITHOUT a semicolon was always fine and must stay fine:
  # refusing on the mere presence of quotes would break working gate specs.
  check "a quoted argument is untouched"       "$(gate_split 'python3 x.py --msg "hello world"' | grep -c .)" "1"
  check "  ...and not refused"                 "$(gate_spec_refusal 'python3 x.py --msg "hello world"' >/dev/null && echo refused || echo accepted)" "accepted"
  check "single quotes hide a ';' too"         "$(gate_split "python3 -c 'a; b'" | grep -c .)" "1"
  check "  ...an ESCAPED quote does not close" "$(gate_split 'python3 -c "a \" b; c"' | grep -c .)" "1"

  # NOTHING IS SILENTLY FRAGMENTED, asserted where the guarantee lives:
  # `run_gates` consumes `gate_split`, so a spec that splits into one command
  # reaches the shell as one command.  (`run_gates` itself is defined after
  # this block and is deliberately NOT moved — moving it is what broke a
  # self-test into a REAL tenure while this row was being written.)
  check "the ES spec is ONE command to run"    "$(gate_split "$es" | grep -c .)" "1"
  check "  ...and two real gates stay two"     "$(gate_split 'python3 a.py; python3 b.py' | grep -c .)" "2"

  # ---- WAS THE BASE EVER GREEN? (the pyc lane's 116 minutes)
  echo "  -- base staleness"
  up="$tmp/upstream.git"; sd="$tmp/seed"; wk="$tmp/work"
  git init -q --bare "$up" 2>/dev/null
  mkdir -p "$sd"; git init -q "$sd" 2>/dev/null
  git -C "$sd" config user.email qol@example; git -C "$sd" config user.name qol
  printf 'name = "x"\n[[lean_lib]]\nname = "LeanModels"\n' > "$sd/lakefile.toml"
  mkdir -p "$sd/tools"; printf 'STAMP_VERSION="v2"\n' > "$sd/tools/triad.sh"
  git -C "$sd" add -A; git -C "$sd" commit -qm base
  git -C "$sd" branch -M master 2>/dev/null
  git -C "$sd" remote add origin "$up" 2>/dev/null; git -C "$sd" push -q origin master 2>/dev/null
  # THE BARE REPO'S HEAD, SET EXPLICITLY.  `git init --bare` points HEAD at
  # `refs/heads/main` on current git, so a clone whose only branch is `master`
  # checks out NOTHING — no HEAD, hence no merge-base, and every row below
  # measured the "unrelated histories" path instead of the one it named.
  git -C "$up" symbolic-ref HEAD refs/heads/master 2>/dev/null
  git clone -q "$up" "$wk" 2>/dev/null
  git -C "$wk" config user.email qol@example; git -C "$wk" config user.name qol
  saved_cl="$CLONE"; saved_fg="$FOREIGN"; CLONE="$wk"; FOREIGN=0; rm -f "$TIP_CACHE_FILE"

  check "a base AT the tip says so"          "$(base_staleness fresh | grep -c 'is AT the origin/master tip')" "1"
  # A13: the remote is a local path here, and a local remote's tip can be days
  # behind github's — the check still runs, and the LINE says what it is.
  check "  ...and a LOCAL remote is flagged" "$(base_staleness fresh | grep -c 'A13.*LOCAL path')" "1"

  # MASTER MOVES while this clone sits still — the pyc lane's exact shape.
  printf 'fix\n' > "$sd/fix.txt"; git -C "$sd" add -A; git -C "$sd" commit -qm fix
  printf 'fix2\n' > "$sd/fix2.txt"; git -C "$sd" add -A; git -C "$sd" commit -qm fix2
  git -C "$sd" push -q origin master 2>/dev/null
  out="$(base_staleness fresh)"
  check "a moved master is LOUD"             "$(printf '%s' "$out" | grep -c 'BASE STALE:')" "1"
  check "  ...counting the commits behind"   "$(printf '%s' "$out" | grep -c '2 commit(s) behind')" "1"
  check "  ...naming the tip sha"            "$(printf '%s' "$out" | grep -c "$(git -C "$sd" rev-parse --short HEAD)")" "1"
  check "  ...and what to do about it"       "$(printf '%s' "$out" | grep -c 'consider rebasing')" "1"
  # WARN, NEVER REFUSE: a pinned base is legitimate (SV declined a rebase the
  # same day), so this must stay a line and never a verdict.
  check "  ...but it is only a WARNING"      "$(base_staleness fresh >/dev/null 2>&1; echo $?)" "0"

  # THE FETCH MUST NOT MOVE THE LANE'S OWN REFS.  Measured: a refspec fetch by
  # REMOTE NAME advances origin/master opportunistically; by URL it does not.
  before="$(git -C "$wk" rev-parse origin/master)"
  base_staleness fresh >/dev/null 2>&1
  check "the check does not move origin/master" "$(git -C "$wk" rev-parse origin/master)" "$before"

  # THE ABSENCE FAMILY, and none of these may read like "at the tip".
  FOREIGN=1; rm -f "$TIP_CACHE_FILE"
  check "a foreign tree is n/a"              "$(base_staleness fresh)" "n/a (foreign tree)"
  FOREIGN=0; rm -f "$TIP_CACHE_FILE"
  git -C "$wk" remote set-url origin "$tmp/nope.git"
  check "an unreachable remote is n/a"       "$(base_staleness fresh | grep -c 'n/a (could not reach')" "1"
  check "  ...and still not a refusal"       "$(base_staleness fresh >/dev/null 2>&1; echo $?)" "0"
  git -C "$wk" remote set-url origin "$up"; rm -f "$TIP_CACHE_FILE"

  # ---- THE ONE REFUSAL: a NEW ticket from a pre-rebase worktree
  # `accept-and-log` is for tickets ALREADY IN FLIGHT; a new one is refused.
  check "an equal stamp version passes"      "$( ( stamp_version_guard ) >/dev/null 2>&1; echo $?)" "0"
  printf 'STAMP_VERSION="v3"\n' > "$sd/tools/triad.sh"
  git -C "$sd" add -A; git -C "$sd" commit -qm bump; git -C "$sd" push -q origin master 2>/dev/null
  rm -f "$TIP_CACHE_FILE"
  out="$( ( stamp_version_guard ) 2>&1 )"; rc=$?
  check "an OLDER local stamp REFUSES"       "$rc" "2"
  check "  ...naming both versions"          "$(printf '%s' "$out" | grep -c 'stamps v2 but master.*stamps v3')" "1"
  check "  ...and the in-flight distinction" "$(printf '%s' "$out" | grep -c 'IN FLIGHT is')" "1"
  # AN ABSENT ANSWER IS NEVER A REFUSAL: not knowing master's version is not
  # evidence that ours is old.
  git -C "$wk" remote set-url origin "$tmp/nope.git"; rm -f "$TIP_CACHE_FILE"
  check "an unreachable remote never refuses" "$( ( stamp_version_guard ) >/dev/null 2>&1; echo $?)" "0"
  git -C "$wk" remote set-url origin "$up"; rm -f "$TIP_CACHE_FILE"
  CLONE="$saved_cl"; FOREIGN="$saved_fg"; rm -f "$TIP_CACHE_FILE"

  # ---- THE GREEN LEDGER AND --since (§5.4a-i, the pyc lane's withdrawn ticket)
  echo "  -- increment greens"
  gl="$tmp/ledger"; mkdir -p "$gl"; git init -q "$gl" 2>/dev/null
  git -C "$gl" config user.email qol@example; git -C "$gl" config user.name qol
  printf 'name = "x"\n[[lean_lib]]\nname = "LeanModels"\n' > "$gl/lakefile.toml"
  mkdir -p "$gl/docs"; printf '# d\n' > "$gl/docs/a.md"
  git -C "$gl" add -A; git -C "$gl" commit -qm root
  R_SHA="$(git -C "$gl" rev-parse HEAD)"
  printf '# more\n' >> "$gl/docs/a.md"; git -C "$gl" add -A; git -C "$gl" commit -qm inc
  H_SHA="$(git -C "$gl" rev-parse HEAD)"
  saved_cl="$CLONE"; saved_sn="$SINCE"; saved_lane="$LANE"; saved_g="$GATES"
  CLONE="$gl"; LANE="qol"; GATES="python3 tools/docs_check.py"

  # THE LEDGER LIVES IN THE GIT DIR, per working directory (a linked worktree
  # has its own .lake, and the cache is part of what produced the green).
  check "the ledger is inside the git dir"    "$(green_ledger_path)" "$gl/.git/triad-greens"

  # A CLEAN TREE IS CITABLE; a tree carrying staged work is not, because the
  # green then certified content that is not that commit.
  ( cd "$gl" && record_green spine yes self 0 "" )
  check "a green is recorded"                 "$(grep -c "^green $H_SHA " "$gl/.git/triad-greens")" "1"
  check "  ...as citable on a clean tree"     "$(ledger_field "$(ledger_lookup "$H_SHA")" citable)" "yes"
  check "  ...naming itself as the root"      "$(ledger_field "$(ledger_lookup "$H_SHA")" root)" "self"
  check "  ...and every field parses"         "$(ledger_field "$(ledger_lookup "$H_SHA")" class)" "spine"
  check "  ...including the gate names"       "$(ledger_field "$(ledger_lookup "$H_SHA")" gates)" "docs_check"
  # A FULL build has an EMPTY target list, and the field must still say what
  # that MEANS: `targets=` printed a blank where the word `all` belonged.
  check "  ...and a full build says targets=all" "$(ledger_field "$(ledger_lookup "$H_SHA")" targets)" "all"
  printf 'staged\n' > "$gl/docs/b.md"; git -C "$gl" add -A
  ( cd "$gl" && record_green spine yes self 0 "" )
  check "staged work makes a green UNCITABLE" "$(ledger_field "$(ledger_lookup "$H_SHA")" citable)" "no"
  git -C "$gl" reset -q --hard HEAD; rm -f "$gl/docs/b.md"

  # THE FIVE REFUSALS.  Each names its own cause: a refusal nobody can read is
  # a refusal that gets worked around.
  SINCE="not-a-sha"
  check "a non-commit --since refuses"        "$(since_resolve 2>&1 >/dev/null | grep -c 'is not a commit')" "1"
  # A SIBLING, not an ancestor: the shape a rebase leaves behind.
  git -C "$gl" checkout -q -b side "$R_SHA"; printf 'x\n' > "$gl/docs/c.md"
  git -C "$gl" add -A; git -C "$gl" commit -qm side
  S_SHA="$(git -C "$gl" rev-parse HEAD)"; git -C "$gl" checkout -q master 2>/dev/null || git -C "$gl" checkout -q -
  SINCE="$S_SHA"
  out="$(since_resolve 2>&1 >/dev/null)"
  check "a non-ancestor refuses"              "$(printf '%s' "$out" | grep -c 'NOT AN ANCESTOR')" "1"
  check "  ...naming why a rebase can't be cited" "$(printf '%s' "$out" | grep -c 'rebase rewrites shas')" "1"
  SINCE="$R_SHA"
  out="$(since_resolve 2>&1 >/dev/null)"
  check "an UNRECORDED green refuses"         "$(printf '%s' "$out" | grep -c 'no green is RECORDED')" "1"
  check "  ...saying evidence is not memory"  "$(printf '%s' "$out" | grep -c 'evidence, not a memory')" "1"

  # Now record shapes for the remaining two refusals and the happy paths.
  lf="$gl/.git/triad-greens"; : > "$lf"
  T_R="$(git -C "$gl" rev-parse "$R_SHA^{tree}")"
  printf 'green %s tree=%s class=spine citable=no full=yes root=self depth=0 targets=all gates=g lane=l ticket=t at=now\n' "$R_SHA" "$T_R" > "$lf"
  check "an UNCITABLE base refuses"           "$(since_resolve 2>&1 >/dev/null | grep -c 'NOT CITABLE')" "1"
  printf 'green %s tree=%s class=tier citable=yes full=no root=unknown depth=0 targets=LeanModels.A gates=g lane=l ticket=t at=now\n' "$R_SHA" "$T_R" > "$lf"
  out="$(since_resolve 2>&1 >/dev/null)"
  check "a rootless scoped base refuses"      "$(printf '%s' "$out" | grep -c 'NO RESOLVABLE ROOT')" "1"
  check "  ...naming the root rule"           "$(printf '%s' "$out" | grep -c 'against the ROOT, never the parent')" "1"

  # THE HAPPY PATH, and the one that makes the root rule visible.
  printf 'green %s tree=%s class=spine citable=yes full=yes root=self depth=0 targets=all gates=docs_check at=2026-08-23T10:00:00 lane=l ticket=t\n' "$R_SHA" "$T_R" > "$lf"
  SINCE_ROOT=""; SINCE_LINE=""
  check "a full green resolves to itself"     "$(since_resolve >/dev/null 2>&1; printf '%s' "$SINCE_ROOT")" "$R_SHA"
  # A CHAIN: the named green is an increment whose root is the full green, so
  # classification is taken against the ROOT, not against what was named.
  M_SHA="$H_SHA"
  printf 'green %s tree=%s class=docs citable=yes full=no root=%s depth=1 targets=all gates=docs_check at=2026-08-23T11:00:00 lane=l ticket=t\n' "$M_SHA" "$(git -C "$gl" rev-parse "$M_SHA^{tree}")" "$R_SHA" >> "$lf"
  SINCE="$M_SHA"; SINCE_ROOT=""
  check "a chained green resolves to its ROOT" "$(since_resolve >/dev/null 2>&1; printf '%s' "$SINCE_ROOT")" "$R_SHA"
  check "  ...which is NOT the named sha"      "$( [ "$SINCE_ROOT" = "$M_SHA" ] && echo named || echo root )" "root"

  # THE COMPOSED COVERAGE LINE.  Both shas, the clause verbatim, the bar.
  SINCE="$R_SHA"; since_resolve >/dev/null 2>&1
  BASE_SHA="$(git -C "$gl" rev-parse --short "$R_SHA")"; CHANGED="docs/a.md"
  out="$(increment_coverage docs)"
  check "the coverage names the increment"    "$(printf '%s' "$out" | grep -c 'increment  ')" "1"
  check "  ...and the green it rests on"      "$(printf '%s' "$out" | grep -c 'on top of  the green at')" "1"
  check "  ...and the resolved root"          "$(printf '%s' "$out" | grep -c '^  root       ')" "1"
  check "  ...the clause, verbatim"           "$(printf '%s' "$out" | grep -c 'INCREMENT ON TOP OF THAT GREEN and nothing')" "1"
  check "  ...that it is NOT a branch green"  "$(printf '%s' "$out" | grep -c 'NOT evidence that the branch is green as a whole')" "1"
  check "  ...and that limits are inherited"  "$(printf '%s' "$out" | grep -c 'inherits')" "1"
  check "a FULL root SATISFIES the merge bar" "$(printf '%s' "$out" | grep -c 'MERGE BAR: SATISFIED')" "1"
  # ...and the direction that must never read as satisfied.
  printf 'green %s tree=%s class=tier citable=yes full=no root=self depth=0 targets=LeanModels.A gates=g at=now lane=l ticket=t\n' "$R_SHA" "$T_R" > "$lf"
  SINCE_LINE=""; since_resolve >/dev/null 2>&1
  out="$(increment_coverage docs)"
  check "a SCOPED root does NOT satisfy it"   "$(printf '%s' "$out" | grep -c 'MERGE BAR: NOT SATISFIED')" "1"
  check "  ...and says to take a full green"  "$(printf '%s' "$out" | grep -c 'Take one full green')" "1"

  CLONE="$saved_cl"; SINCE="$saved_sn"; LANE="$saved_lane"; GATES="$saved_g"
  SINCE_ROOT=""; SINCE_LINE=""; CHANGED=""

  # ---- WHAT WILL RUN, SAID AT TENURE OPEN, and by the SAME composer
  saved_lg="$LANE_GATES"; saved_go="$GATES_ONLY"; saved_fg="$FOREIGN"
  saved_cl="$CLASSIFY"; saved_g="$GATES"
  LANE_GATES=""; GATES_ONLY=0; FOREIGN=0; CLASSIFY=0
  check "the announced set IS the floor"   "$(gates_planned)" "$DEFAULT_FLOOR"
  check "  ...and matches the phase's own composer" \
        "$(gates_planned)" "$(gates_compose "$DEFAULT_FLOOR" "" 0)"
  LANE_GATES='python3 harness/script_corpus.py'
  check "a lane's gates are ADDED, and said" \
        "$(gates_planned)" "$DEFAULT_FLOOR; python3 harness/script_corpus.py"
  GATES_ONLY=1
  check "--gates-only is announced as REPLACING" "$(gates_planned)" "python3 harness/script_corpus.py"
  GATES_ONLY=0; FOREIGN=1; GATES='python3 x.py'
  check "a foreign tree announces its gates AS GIVEN" "$(gates_planned)" "python3 x.py"
  FOREIGN=0; CLASSIFY=1
  check "  ...and so does a classify pass"  "$(gates_planned)" "python3 x.py"
  LANE_GATES="$saved_lg"; GATES_ONLY="$saved_go"; FOREIGN="$saved_fg"
  CLASSIFY="$saved_cl"; GATES="$saved_g"

  # ---- A VALUE-TAKING FLAG WRITTEN LAST (the Go lane's 31 silent minutes)
  echo "  -- argv guards"
  # BOUNDED, because the bug under test is an INFINITE LOOP: an unguarded
  # tool would hang this self-test instead of failing it.
  out="$(timeout 10 bash "$0" --gates 2>&1)"; rc=$?
  check "a value flag written last REFUSES"  "$rc" "2"
  check "  ...rather than spinning forever"  "$([ "$rc" = "124" ] && echo spun || echo bounded)" "bounded"
  check "  ...and NAMES the flag"            "$(printf '%s' "$out" | grep -c -- '--gates needs a value')" "1"
  out="$(timeout 10 bash "$0" --lane 2>&1)"; rc=$?
  check "every value flag is guarded, not just --gates" "$rc" "2"
  # The POSITIVE control: the guard must not refuse a flag that HAS its value.
  out="$(timeout 20 bash "$0" --lane t --gates 'python3 x.py' --dry-run --classify-only --against HEAD 2>&1)"; rc=$?
  # Counted unconditionally: an `&&` here short-circuited to the empty string
  # whenever the run did not exit 2, so the row measured nothing and said so
  # only because the expected value happened not to be empty.
  check "a flag WITH a value still parses"   "$(printf '%s' "$out" | grep -c 'needs a value')" "0"

  # ---- unstaged Lean, and Lean nothing imports (the Ada lane's Value.lean)
  echo "  -- unstaged / unimported Lean"
  offend="$(printf 'docs/mvcgen-pilot.lean\nLeanModels/Ada/Value.lean\nExamples/python/x/proof.lean\ntools/x.sh\nREADME.md\n' | lean_glob_offenders | tr '\n' ' ' | sed 's/ *$//')"
  check "lake-glob Lean is an offender"    "$offend" "LeanModels/Ada/Value.lean Examples/python/x/proof.lean"
  check "a doc's .lean is NOT"             "$(printf 'docs/mvcgen-pilot.lean\n' | lean_glob_offenders)" ""
  # THE DISAGREEMENT: check.sh reads the lakefile and calls a repo-root `.lean`
  # SCRATCH (`Examples.+` matches no root module); this warned about it.
  check "a REPO-ROOT .lean is not under a glob" "$(printf 'Foo.lean\n' | lean_glob_offenders)" ""
  check "  ...and both tools now agree"          "$(lake_glob_class "$CLONE" Foo.lean)" "scratch"
  check "  ...while a real library file IS"      "$(printf 'LeanModels/Core/Basic.lean\n' | lean_glob_offenders)" "LeanModels/Core/Basic.lean"
  check "a non-.lean path is NOT"          "$(printf 'LeanModels/Ada/notes.md\n' | lean_glob_offenders)" ""

  imp="$tmp/improot"
  mkdir -p "$imp/LeanModels/Ada" "$imp/Examples/python/x"
  printf 'import LeanModels.Ada.Used\n' > "$imp/LeanModels.lean"
  : > "$imp/LeanModels/Ada/Used.lean"
  : > "$imp/LeanModels/Ada/Value.lean"
  : > "$imp/Examples/python/x/proof.lean"
  LS_GREP_ROOT="$imp"
  check "an imported module is imported"   "$(module_is_imported LeanModels.Ada.Used && echo yes)" "yes"
  check "an orphan module is NOT"          "$(module_is_imported LeanModels.Ada.Value && echo yes)" ""
  check "the orphan is REPORTED"           "$(printf 'LeanModels/Ada/Value.lean\n' | unimported_new_modules)" "LeanModels/Ada/Value.lean"
  check "the imported one is not"          "$(printf 'LeanModels/Ada/Used.lean\n' | unimported_new_modules)" ""
  check "the library ROOT is never flagged" "$(printf 'LeanModels.lean\n' | unimported_new_modules)" ""
  check "Examples is exempt (lakefile globs)" "$(printf 'Examples/python/x/proof.lean\n' | unimported_new_modules)" ""
  LS_GREP_ROOT=""

  # ---- --foreign (the Lean tier's lean4lean, the Wasm lane's spectec fork)
  echo "  -- foreign checkouts"
  SELF="${BASH_SOURCE[0]}"
  fdir="$tmp/foreign"; mkdir -p "$fdir"
  out="$(bash "$SELF" --lane x --foreign --dir "$fdir" 2>&1)"; rc=$?
  check "--foreign WITHOUT --gates refuses"      "$rc" "2"
  check "  ...saying there is nothing to run"    "$(printf '%s' "$out" | grep -c 'requires --gates')" "1"
  out="$(bash "$SELF" --lane x --foreign --classify --gates 'true' --dir "$fdir" 2>&1)"; rc=$?
  check "--foreign + --classify is an error"     "$rc" "2"
  check "  ...and the contradiction is STATED"   "$(printf '%s' "$out" | grep -c 'CONTRADICT')" "1"
  # Accepted: it must get PAST the preconditions and take a tenure.  Sandboxed
  # lock and queue, and --dry-run, so no real ticket and no Lean.
  out="$(LS_LOCK="$tmp/flock" LS_QUEUE="$tmp/fqueue" \
         bash "$SELF" --lane x --foreign --gates 'true' --dir "$fdir" --dry-run 2>&1)"; rc=$?
  check "--foreign WITH --gates is accepted"     "$rc" "0"
  check "  ...and it takes the full tenure"      "$(printf '%s' "$out" | grep -c 'tenure taken')" "1"
  check "  ...marked FOREIGN in the banner"      "$(printf '%s' "$out" | grep -c '\[FOREIGN\]')" "1"
  check "  ...leaving no ticket behind"          "$(ls "$tmp/fqueue" 2>/dev/null | grep -c .)" "0"
  FOREIGN=1
  check "the coverage says the floor is N/A"     "$(foreign_coverage | grep -c 'class floor not applicable')" "1"
  check "  ...and claims nothing about US"       "$(foreign_coverage | grep -c 'about nothing in this repository')" "1"
  FOREIGN=0

  # ---- the red-build report: the instrument that reports the other instruments
  echo "  -- red-build report (§7)"
  rl="$tmp/red-many.log"
  { echo "info: [1/839] Building LeanModels.A"
    echo "info: [312/839] Building LeanModels.B"
    i=1
    while [ "$i" -le 12 ]; do
      echo "error: LeanModels/A.lean:$i:1: unknown constant 'X$i'"
      i=$((i + 1))
    done
    echo "✖ [500/839] Building LeanModels.M1"
    echo "✖ [501/839] Building LeanModels.M2"
    echo "✖ [502/839] Building LeanModels.M3"
  } > "$rl"
  out="$(build_failure_report "$rl")"
  check "failed modules counted from the FULL log" "$(printf '%s' "$out" | grep -c 'failed modules   3')" "1"
  check "error lines: total AND distinct"          "$(printf '%s' "$out" | grep -c 'error lines      12 total, 12 distinct')" "1"
  check "how far lake GOT is reported"             "$(printf '%s' "$out" | grep -c '502 of 839')" "1"
  check "  ...with lake's stop-at-first named"     "$(printf '%s' "$out" | grep -c 'FIRST failing module')" "1"
  # This row used to assert the label `first 8 of 15` — the exact promise the
  # sample broke, since `sort -u` reordered before `head`.  It now asserts the
  # promise the summary can keep.
  check "the preview leads with the FIRST error"   "$(printf '%s' "$out" | grep -c 'FIRST error (verbatim')" "1"
  check "  ...and the remainder says LOG ORDER"    "$(printf '%s' "$out" | grep -c 'IN LOG ORDER')" "1"
  check "  ...and says which one counts"           "$(printf '%s' "$out" | grep -c 'summary LOCATES; the full log COUNTS')" "1"
  check "the preview really is 8 lines"            "$(printf '%s' "$out" | grep -c '^      ')" "8"
  check "no amplification claimed when there is none" "$(printf '%s' "$out" | grep -c 'AMPLIFIED')" "0"
  check "the 'how far' caveat is stated"           "$(printf '%s' "$out" | grep -c 'how far the build GOT')" "1"

  # AMPLIFICATION: one root cause, forty lines.  This is the shape that turned
  # into "one error in 839 targets" when read off a deduplicated preview.
  rl2="$tmp/red-amp.log"
  { echo "info: [7/9] Building Examples.X"
    i=1
    while [ "$i" -le 40 ]; do
      echo "error: Examples/x/proof.lean:3:5: unknown identifier 'foo'"
      i=$((i + 1))
    done
    echo "✖ [8/9] Building Examples.X"
  } > "$rl2"
  out2="$(build_failure_report "$rl2")"
  check "amplification: 40 total, 1 distinct"      "$(printf '%s' "$out2" | grep -c '40 total, 1 distinct')" "1"
  check "  ...and the ratio is NAMED"              "$(printf '%s' "$out2" | grep -c 'AMPLIFIED 40.0x')" "1"
  check "  ...the deduped pool still dedups"       "$(printf '%s' "$out2" | grep -c 'next 1 of 1 more distinct')" "1"

  printf 'error: boom\n' > "$tmp/red-bare.log"

  # ---- THE FIRST ERROR IS NEVER DROPPED (pyc3's attempt-2 diagnosis cycle)
  # A class-A error at line 24, then 40 class-B cascade errors at 102-141 —
  # the shape that misled, INCLUDING the lexicographic trap: `spec.lean:102`
  # sorts BEFORE `spec.lean:24`, because `1` precedes `2`.
  cas="$tmp/cascade.log"
  {
    echo "info: [1/500] Building LeanModels.Pyc.Spec"
    echo "error: LeanModels/Pyc/spec.lean:24:2: maximum recursion depth has been reached"
    i=102; while [ "$i" -le 141 ]; do
      echo "error: LeanModels/Pyc/spec.lean:$i:8: failed to synthesize Decidable (cascade)"
      i=$((i + 1))
    done
    echo "✖ [37/500] Building LeanModels.Pyc.Spec"
  } > "$cas"
  out="$(build_failure_report "$cas")"
  check "the FIRST error is printed verbatim"  "$(printf '%s' "$out" | grep -c 'FIRST error (verbatim')" "1"
  check "  ...and it is the log's first line"  \
        "$(printf '%s' "$out" | grep -A1 'FIRST error' | tail -1 | sed 's/^ *//')" \
        "error: LeanModels/Pyc/spec.lean:24:2: maximum recursion depth has been reached"
  check "  ...the CAUSAL class, not the cascade" \
        "$(printf '%s' "$out" | grep -c 'maximum recursion depth')" "1"
  # THE TRAP, ASSERTED: the old `sort -u` sample really did drop it, so this
  # fixture exercises the defect rather than merely resembling it.
  check "  ...which a SORTED sample would drop" \
        "$(grep -E '^error|✖' "$cas" | sort -u | head -8 | grep -c 'spec.lean:24')" "0"
  check "  ...while log order puts it first"   \
        "$(grep -E '^error|✖' "$cas" | awk '!seen[$0]++' | head -1 | grep -c 'spec.lean:24')" "1"
  # AND THE REST IS IN LOG ORDER, so "next N" is the next N as emitted.
  check "the sample continues in LOG ORDER"    \
        "$(printf '%s' "$out" | grep -c 'IN LOG ORDER')" "1"
  check "  ...beginning at the first cascade line" \
        "$(printf '%s' "$out" | grep -A1 'IN LOG ORDER' | tail -1 | grep -c 'spec.lean:102')" "1"
  check "  ...and no line claims to be sorted" "$(printf '%s' "$out" | grep -c 'first 8 of')" "0"

  # ONE error and NO error: neither may invent a section.
  printf 'error: only one thing went wrong\n' > "$tmp/one.log"
  check "a single error still leads"           "$(build_failure_report "$tmp/one.log" | grep -c 'FIRST error')" "1"
  check "  ...with no empty 'next' section"    "$(build_failure_report "$tmp/one.log" | grep -c 'IN LOG ORDER')" "0"
  printf '✖ [3/9] Building X\n' > "$tmp/noerr.log"
  check "a log with no error line invents none" "$(build_failure_report "$tmp/noerr.log" | grep -c 'FIRST error')" "0"

  check "no progress lines -> targets unknown"     "$(build_failure_report "$tmp/red-bare.log" | grep -c 'targets          unknown')" "1"
  check "a missing log refuses honestly"           "$(build_failure_report "$tmp/no-such.log" | grep -c 'no log at')" "1"

  # A RED BUILD IS AN ABORTED TRIAD, not a triad with one part failing.
  out3="$(build_red_report "$rl2" "BUILD DID NOT COMPLETE (exit 1)")"
  check "the red block says GATES NOT RUN"         "$(printf '%s' "$out3" | grep -c 'GATES NOT RUN (build red — aborted triad)')" "1"
  check "  ...carries the headline it was given"   "$(printf '%s' "$out3" | grep -c 'BUILD DID NOT COMPLETE (exit 1)')" "1"
  check "  ...and names the full log"              "$(printf '%s' "$out3" | grep -c 'full log:')" "1"
  check "  ...and still carries the counts"        "$(printf '%s' "$out3" | grep -c '40 total, 1 distinct')" "1"

  # The deleted harness (master eeeb1fd) is no longer matched.
  check "the deleted monadic_gate is not matched"  "$(gate_runner_targets 'python3 harness/monadic_gate.py')" ""
  check "  ...while the live harnesses still are"  "$(gate_runner_targets 'python3 harness/script_corpus.py')" "leanmodels-run"

  # ---- the tree must not move while you queue (measured: the Lean tier
  # nearly reported "instN green" for a run that would have built instN + weak')
  echo "  -- enqueue-tree stamp"
  check "identical stamps are the same tree"  "$(tree_verdict 'aaa HEAD1' 'aaa HEAD1')" "same"
  check "a moved tree is CHANGED"             "$(tree_verdict 'aaa HEAD1' 'bbb HEAD1')" "changed"
  check "a moved HEAD is CHANGED too"         "$(tree_verdict 'aaa HEAD1' 'aaa HEAD2')" "changed"
  check "an unstampable side is UNKNOWN"      "$(tree_verdict '' 'bbb HEAD1')" "unknown"

  # A REAL repository: stamp, edit, re-stamp.
  tr="$tmp/treerepo"; mkdir -p "$tr" && git init -q "$tr" 2>/dev/null
  git -C "$tr" config user.email qol@example; git -C "$tr" config user.name qol
  printf 'one\n' > "$tr/a.txt"; git -C "$tr" add -A; git -C "$tr" commit -qm base
  saved="$CLONE"; CLONE="$tr"
  enq="$(tree_stamp)"
  check "a real tree stamps"                  "$( [ -n "$enq" ] && echo stamped)" "stamped"
  # FROM A FOREIGN CWD: the stamp must read the repo it was TOLD about, not the
  # one the shell happens to be sitting in.  A stamp read from the wrong repo
  # prints a MISMATCH — or, with coincidentally-equal trees, a FALSE MATCH.
  foreign="$( cd / && tree_stamp )"
  check "the stamp ignores the inherited cwd"  "$foreign" "$enq"
  check "  ...and is not the outer repo's"     "$( [ "$foreign" != "$(git -C "$saved" rev-parse HEAD 2>/dev/null)" ] && echo distinct)" "distinct"
  check "no edit -> same"                     "$(tree_verdict "$enq" "$(tree_stamp)")" "same"
  printf 'two\n' >> "$tr/a.txt"; git -C "$tr" add -A
  now="$(tree_stamp)"
  check "an edit while queued -> changed"     "$(tree_verdict "$enq" "$now")" "changed"

  # The refusal, and the override, and the line they SHARE.
  out="$(tree_change_report "$enq" "$now" 0 2>&1)"; rc=$?
  check "enqueue, edit, acquire -> REFUSE"    "$rc" "1"
  check "  ...and the line names both trees"  "$(printf '%s' "$out" | grep -c 'TREE CHANGED SINCE ENQUEUE (')" "1"
  check "  ...and says what to do"            "$(printf '%s' "$out" | grep -c 'Re-enqueue')" "1"
  out="$(tree_change_report "$enq" "$now" 1 2>&1)"; rc=$?
  check "--build-current-tree -> PROCEED"     "$rc" "0"
  check "  ...printing the SAME line"         "$(printf '%s' "$out" | grep -c 'TREE CHANGED SINCE ENQUEUE (')" "1"
  out="$(tree_change_report "$enq" "$enq" 0 2>&1)"; rc=$?
  check "enqueue, no edit -> PROCEED silently" "$rc:$(printf '%s' "$out" | grep -c .)" "0:0"
  out="$(tree_change_report "" "$now" 0 2>&1)"; rc=$?
  check "unstampable -> proceed, but LOUDLY"  "$rc:$(printf '%s' "$out" | grep -c 'TREE STAMP UNAVAILABLE')" "0:1"
  CLONE="$saved"

  # ---- the axiom ledger, salvaged from a GREEN build's log
  echo "  -- axiom ledger"
  printf 'info: building\n%s\n%s\nBuild completed successfully.\n' \
    "'thm' depends on axioms: [propext, Classical.choice, Quot.sound]" \
    "'other' does not depend on any axioms" > "$tmp/green.log"
  check "a green log yields its axiom lines"  "$(axiom_ledger "$tmp/green.log" | grep -c 'propext')" "1"
  check "  ...both of them"                   "$(axiom_ledger "$tmp/green.log" | grep -c 'axioms')" "2"
  check "  ...under a label naming the build" "$(axiom_ledger "$tmp/green.log" | head -1)" "axiom ledger, from this build:"
  printf 'info: building\nBuild completed successfully.\n' > "$tmp/plain.log"
  check "a log with no axiom line says nothing" "$(axiom_ledger "$tmp/plain.log")" ""

  # THE LEDGER MUST BE ABLE TO FAIL.  [sorryAx] printed identically to the
  # standard three and the tenure still said gates green.
  printf "'thm' depends on axioms: [propext, sorryAx]\n" > "$tmp/sorry.log"
  check "an OFF-STANDARD axiom returns 2"     "$(axiom_ledger "$tmp/sorry.log" >/dev/null; echo $?)" "2"
  check "  ...naming the axiom and the decl"  "$(axiom_ledger "$tmp/sorry.log" | grep -c 'sorryAx (thm)')" "1"
  check "  ...and saying the tenure is not green" "$(axiom_ledger "$tmp/sorry.log" | grep -c 'not a green tenure')" "1"
  printf "'ok1' depends on axioms: [propext, Classical.choice, Quot.sound]\n" > "$tmp/std.log"
  check "the declared three pass"             "$(axiom_ledger "$tmp/std.log" >/dev/null; echo $?)" "0"
  printf "'r' depends on axioms: [Lean.ofReduceBool]\n" > "$tmp/rb.log"
  check "ofReduceBool is off-standard too"    "$(axiom_ledger "$tmp/rb.log" >/dev/null; echo $?)" "2"
  bl="$tmp/bl"; mkdir -p "$bl"
  : > "$bl/triad-build.aaa"; : > "$bl/triad-build.bbb"; : > "$bl/triad-build.ccc"
  check "a green tenure NAMES its log"        "$(build_log_pointer "$bl/triad-build.aaa" | grep -c 'full log:')" "1"
  check "  ...saying it was kept, not deleted" "$(build_log_pointer "$bl/triad-build.aaa" | grep -c 'kept, not deleted')" "1"
  check "  ...counting the OTHER logs beside it" "$(build_log_pointer "$bl/triad-build.aaa" | grep -c '2 other')" "1"
  check "  ...and warning off the CLOCK"       "$(build_log_pointer "$bl/triad-build.aaa" | grep -c 'NEVER by clock')" "1"
  check "  ...naming CONTENT as the fallback"  "$(build_log_pointer "$bl/triad-build.aaa" | grep -c 'by CONTENT, grep -l for a symbol')" "1"
  check "  ...and why the window is unsafe"    "$(build_log_pointer "$bl/triad-build.aaa" | grep -c 'within 90s of one tenure')" "1"
  check "  ...and reports that it found none"   "$(axiom_ledger "$tmp/plain.log" >/dev/null; echo $?)" "1"

  # ---- A BUILD LOG SAYS WHOSE IT IS (the C successor grepped 68 and matched none)
  saved_tk="${TICKET:-}"; saved_ln="$LANE"; saved_es="${ENQ_STAMP:-}"
  TICKET="1787500000000000000-999-ctwin"; LANE="ctwin"
  ENQ_STAMP="0123456789abcdef0123456789abcdef01234567 deadbeef"
  hdr="$(build_log_header 1)"
  check "the header names the TICKET"         "$(printf '%s' "$hdr" | grep -c 'ticket=1787500000000000000-999-ctwin')" "1"
  check "  ...the LANE, which is what is grepped" "$(printf '%s' "$hdr" | grep -c 'lane=ctwin')" "1"
  check "  ...the BRANCH"                     "$(printf '%s' "$hdr" | grep -c 'branch=')" "1"
  check "  ...the enqueue TREE"               "$(printf '%s' "$hdr" | grep -c 'tree=0123456789ab')" "1"
  check "  ...the attempt, since each one re-stamps" "$(build_log_header 2 | grep -c 'attempt=2')" "1"
  check "  ...and it is ONE line"             "$(printf '%s\n' "$hdr" | grep -c .)" "1"
  # THE HEADER MUST BE INERT.  It rides in the same file the failure reports
  # count, so it is checked against every consumer rather than reasoned about:
  # a header that added one error line would inflate every red report.
  hl="$tmp/hdr.log"
  build_log_header 1 > "$hl"; cat "$rl" >> "$hl"
  check "the header is the FIRST line"        "$(head -1 "$hl" | grep -c '^triad.sh ticket=')" "1"
  check "  ...and changes no failure count"   "$(build_failure_report "$hl" | grep 'error lines')" \
        "$(build_failure_report "$rl" | grep 'error lines')"
  check "  ...nor the failed-module count"    "$(build_failure_report "$hl" | grep 'failed modules')" \
        "$(build_failure_report "$rl" | grep 'failed modules')"
  check "  ...nor the axiom ledger's verdict" "$(axiom_ledger "$hl" >/dev/null; echo $?)" \
        "$(axiom_ledger "$rl" >/dev/null; echo $?)"
  check "  ...and carries no hostname"        "$(printf '%s' "$hdr" | grep -cE "$(uname -n | cut -d. -f1)")" "0"
  TICKET="$saved_tk"; LANE="$saved_ln"; ENQ_STAMP="$saved_es"

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

  # The tier map is DERIVED from imports now, so this row declares the imports
  # it means instead of inheriting whatever the live tree happens to have.
  mkdir -p "$tmp/tiermap/Examples/spice/rc"
  printf 'import LeanModels.Spice\n' > "$tmp/tiermap/Examples/spice/rc/proof.lean"
  LS_GREP_ROOT="$tmp/tiermap"
  cls Examples/spice/rc/net.cir
  check "an input_dir file is a build input" "$BUILD_TARGETS" "Examples LeanModels.Spice"
  LS_GREP_ROOT=

  check "module_of refuses a hyphen"        "$(module_of Examples/system-verilog/x.lean)" ""
  check "module_of derives a plain path"    "$(module_of LeanModels/Sv/Obs.lean)" "LeanModels.Sv.Obs"
  cls LeanModels/Py-thon/x.lean
  check "an underivable module escalates"   "$(class_name "$CLASS_RANK")" "spine"

  cls docs/mvcgen-pilot.lean
  check "a doc's .lean is still docs"       "$(class_name "$CLASS_RANK")" "docs"
  case "$CLASS_NOTES" in *A11*) n=said ;; *) n=silent ;; esac
  check "  ...but A11 is said out loud"     "$n" "said"
  # THE REBASE LAW (Go lane): outside every lean_lib root, so `lake build`
  # never compiles it, so a rebase touching only it owes no re-gate.
  case "$CLASS_NOTES" in *"OUTSIDE ALL lean_lib ROOTS"*) n=said ;; *) n=silent ;; esac
  check "  ...and WHY: outside all lean_lib roots" "$n" "said"
  case "$CLASS_NOTES" in *"owes no re-gate"*) n=said ;; *) n=silent ;; esac
  check "  ...with the consequence spelled out"    "$n" "said"
  # ASKED OF THE LAKEFILE, not of a directory list: a `.lean` under a prefix
  # the old hard-coded case never listed gets the same note.
  cls probes/probe_es_unblock.lean
  check "an unlisted prefix gets the note too" \
        "$(case "$CLASS_NOTES" in *"OUTSIDE ALL lean_lib ROOTS"*) echo said ;; *) echo silent ;; esac)" "said"
  # ...and a real library file does NOT, which is the direction that would
  # quietly excuse a re-gate that IS owed.
  cls LeanModels/Sv/Obs.lean
  check "a library .lean is NOT excused"    \
        "$(case "$CLASS_NOTES" in *"OUTSIDE ALL lean_lib ROOTS"*) echo said ;; *) echo silent ;; esac)" "silent"

  # ---- the Examples reachability probe (the Go lane's measurement)
  # A fixture TREE, so both directions are exercised for real: a `.lean` that
  # names one fixture, a gate corpus that names another, and one file that
  # nothing names at all.
  fx="$tmp/fixroot"
  mkdir -p "$fx/Examples/c/sunfish" "$fx/Examples/go/rung1" \
           "$fx/Examples/python/exc_lab" "$fx/harness"
  # A CODE reference, matching the real tree: `guards.lean` ingests the fixture
  # with `load_c_program … from "…/sunfish.json"`.  The first version wrote the
  # reference as a `--` COMMENT, and once the probe learned to skip comments
  # that fixture was asserting the opposite of the tree it stood for.
  printf 'import LeanModels.C\nload_c_program sunfishC from "Examples/c/sunfish/sunfish.json"\n' \
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

  # A VENDORED SOURCE BESIDE THE MODEL — the shape every language lane wants.
  # The Go lane's tenure went 91s -> 37 MINUTES on exactly this, because the
  # fixture was named in the model's docstring and a prose mention read as a
  # reference.
  : > "$fx/Examples/go/rung1/rung1.go"
  printf 'import LeanModels.Go\n/-- Source: Examples/go/rung1/rung1.go, BSD-3. -/\ndef g := 1\n' \
    > "$fx/Examples/go/rung1/guards.lean"
  cls Examples/go/rung1/rung1.go
  check "a vendored .go beside a .lean -> docs"         "$(class_name "$CLASS_RANK")" "docs"
  check "  ...and it does NOT widen the build"          "$BUILD_TARGETS" ""
  check "  ...even though the docstring NAMES it"       "$(code_mentions rung1.go "$fx/Examples/go/rung1/guards.lean" && echo code)" ""
  printf 'def d := include_str "Examples/go/rung1/rung1.go"\n' >> "$fx/Examples/go/rung1/guards.lean"
  check "but a CODE reference is still reachable"       "$(code_mentions rung1.go "$fx/Examples/go/rung1/guards.lean" && echo code)" "code"

  cls Examples/c/sunfish/guards.lean
  check "a .lean under Examples is tier, no probe"      "$(class_name "$CLASS_RANK")" "tier"
  cls Examples/spice/rc/net.cir
  check "an input_dir fixture is tier without a probe"  "$(class_name "$CLASS_RANK")" "tier"

  cls Examples/go/rung1/rung1.go Examples/c/sunfish/sunfish.json
  check "MIXED invisible+reachable -> tier"             "$(class_name "$CLASS_RANK")" "tier"
  # `Go` appears because the map is DERIVED and `Examples/go/**` really does
  # `import LeanModels.Go` — the hand map claimed go had no tier, and the tree
  # says otherwise.  The audit's LOW row is this, and the assertion follows the
  # tree rather than the comment.
  check "  ...scoped to the tiers the imports declare"  "$CLASS_TIERS" "Go C"

  LS_GREP_ROOT="$tmp/does-not-exist"
  cls Examples/go/rung1/rung1.go
  check "DOUBT (no tree to probe) -> stays tier"        "$(class_name "$CLASS_RANK")" "tier"
  LS_GREP_ROOT=""

  # ---- the default-gate-set notice (the ES lane's migration finding)
  check "gate names read as script names" "$(gate_names "$(gate_floor tier)")" "docs_check, diff_test, refusal_census"
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
        "$(gate_floor tier)" "$DEFAULT_FLOOR"

  # --- --build-target: UNION with the classifier's floor, never replacement ---
  BUILD_TARGETS=""
  add_build_target "LeanModels"; add_build_target "leanmodels-run"
  check "--build-target accumulates in order" "$BUILD_TARGETS" "LeanModels leanmodels-run"
  add_build_target "LeanModels"
  check "add_build_target is a UNION (no duplicate)" "$BUILD_TARGETS" "LeanModels leanmodels-run"
  # The floor rule: an explicit target ADDS to what --classify derived.
  BUILD_TARGETS="LeanModels.Python"
  for _t in leanmodels-run; do add_build_target "$_t"; done
  check "explicit target unions ONTO the classifier floor" "$BUILD_TARGETS" "LeanModels.Python leanmodels-run"
  # And an EMPTY target list still means the full build, which is the default.
  BUILD_TARGETS=""
  _n=0; for _t in $BUILD_TARGETS; do _n=$((_n+1)); done
  check "empty targets == one FULL build" "$_n" "0"
  BUILD_TARGETS=""

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

# --foreign's two refusals, stated before a ticket is ever written.
if [ "$FOREIGN" = "1" ]; then
  if [ "$CLASSIFY" = "1" ]; then
    die "--foreign and --classify CONTRADICT: classification diffs against github/master and its class floor names OUR gates (docs_check, diff_test), neither of which means anything in a foreign checkout (§7.1a). Pick one."
  fi
  [ -n "$LANE_GATES" ] || \
    die "--foreign requires --gates: the class floor is not applicable in a foreign checkout, so without your own gates there would be NOTHING TO RUN. Naming a gate that does not exist there is the failure this refusal prevents."
  GATES_ONLY=1            # there is no applicable floor to add to
fi
# --since's two contradictions, stated before a ticket is ever written.
if [ -n "$SINCE" ]; then
  # NOT IMPLIED.  --since only means something with --classify, but implying a
  # flag CHANGES BEHAVIOUR SILENTLY, and the precedent in this file is the
  # other way (--foreign REQUIRES --gates).  A refusal costs one command.
  [ "$CLASSIFY" = "1" ] || die "--since requires --classify: it prices the INCREMENT the classifier measures (§5.4a-i)"
  [ -z "$AGAINST" ] || die "--since and --against CONTRADICT: --against names the branch's merge target, --since names the green this increment rests ON. Pick one."
  [ "$FOREIGN" = "0" ] || die "--foreign and --since CONTRADICT: a foreign checkout has no ledger of OUR greens (§7.1a)."
fi
# A GATE SPEC IS CODE, checked before a ticket exists: a fragmenting gate list
# costs a whole tenure and produces a RED THAT LOOKS LIKE DILIGENCE.
gate_reason="$(gate_spec_refusal "$(gates_planned)")" && die "$gate_reason"
stamp_version_guard      # a NEW ticket from a pre-rebase worktree is refused here
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

# docs/backlog/INDEX.md is GENERATED and committed, so it conflicts on every
# lane's rebase — measured at two conflicts in one day for one lane, and every
# lane pays it.  A merge driver is declared in .gitattributes, but git does not
# ship `ours`-style drivers and CONFIG IS PER-CLONE, so nobody had one.  A fix
# that needs a human to type it is not a fix: FIXES LIVE IN GATES.
[ -x "$CLONE/tools/backlog-index.sh" ] && \
  "$CLONE/tools/backlog-index.sh" --dir "$CLONE" --ensure-driver 2>/dev/null || true

# ------------------------------------------------------- run the gate list
# Factored out because the docs-only path runs gates WITHOUT a tenure and the
# normal path runs them INSIDE one.  One implementation, two callers.
rc=0
run_gates() {                         # "cmd; cmd" -> sets rc
  # READ FROM gate_split, never from IFS word splitting: `IFS=';'` knows
  # nothing about quotes, which is how ONE command became five gates.
  local g
  while IFS= read -r g; do
    g="$(printf '%s' "$g" | sed -e 's/^ *//' -e 's/ *$//')"
    [ -n "$g" ] || continue        # refused at enqueue; belt for a direct caller
    say "=== gate: $g ==="
    nice -n "$NICE" sh -c "$g" || { rc=1; say "  GATE FAILED: $g"; }
  done <<EOF
$(gate_split "$1")
EOF
}


CLASS=""
FLOOR_USED=""
if [ "$CLASSIFY" = "1" ]; then
  if [ -n "$SINCE" ]; then
    # THE INCREMENT'S BASE IS THE CHAIN ROOT, NEVER THE NAMED GREEN (§5.4a-i).
    # Naming any recorded green is allowed; what the diff is taken against is
    # its root, and the line below says so whenever the two differ.
    since_resolve || die "--since refused (see above) — nothing was queued"
    BASE="$SINCE_ROOT"
    BASE_SHA="$(git -C "$CLONE" rev-parse --short "$BASE" 2>/dev/null || echo unknown)"
    BASE_URL=""; BASE_REMOTE=""
    SINCE_SHA="$(git -C "$CLONE" rev-parse --short "$(git -C "$CLONE" rev-parse "${SINCE}^{commit}")" 2>/dev/null || echo unknown)"
    if [ "$SINCE_ROOT" != "$(git -C "$CLONE" rev-parse "${SINCE}^{commit}" 2>/dev/null)" ]; then
      say "INCREMENT: you named the green at $SINCE_SHA; classifying against its ROOT $BASE_SHA instead"
      say "           (§5.4a-i: against the root, never the parent — two increments priced against"
      say "            their predecessors can be tier A and tier B with neither build covering both)"
    else
      say "INCREMENT: classifying against the green at $BASE_SHA (which is its own chain root)"
    fi
  else
    BASE="$AGAINST"
    [ -n "$BASE" ] || BASE="$(merge_target_ref)"
    [ -n "$BASE" ] || die "no merge target (neither github/master nor origin/master) — pass --against <ref>"
    git -C "$CLONE" rev-parse --verify --quiet "$BASE" >/dev/null 2>&1 || die "--against '$BASE' is not a ref in this clone"
    BASE_SHA="$(git -C "$CLONE" rev-parse --short "$BASE" 2>/dev/null || echo unknown)"
    BASE_REMOTE="${BASE%%/*}"
    BASE_URL="$(git remote get-url "$BASE_REMOTE" 2>/dev/null || echo "")"
    case "$BASE_URL" in
      /*|file:*|*.bundle)
        echo "A13 WARNING: remote '$BASE_REMOTE' is a LOCAL path ($BASE_URL) — a seeded clone's" >&2
        echo "             origin is a stale bundle, and comparing against it reads days back." >&2
        echo "             Add the real remote and re-run with --against github/master." >&2 ;;
    esac
  fi

  # EXPLICIT ROOT, never inherited cwd.  The R-track lane measured the cost:
  # `cd X && nohup Y … &` backgrounds the WHOLE conjunction, so a follow-up
  # `git write-tree` ran in the WRONG repository and printed another repo's
  # HEAD as a MISMATCH — and with coincidentally-equal trees the same bug
  # yields a FALSE MATCH, a lane confirming a stamp it never checked.  In agent
  # threads cwd does not persist between calls at all.
  CHANGED="$( { git -C "$CLONE" diff --name-only "$BASE...HEAD" 2>/dev/null
                git -C "$CLONE" diff --name-only --cached 2>/dev/null; } | sort -u )"
  N_CHANGED="$(printf '%s' "$CHANGED" | grep -c . || true)"
  UNSTAGED_ALL="$( { git -C "$CLONE" diff --name-only 2>/dev/null
                     git -C "$CLONE" ls-files --others --exclude-standard 2>/dev/null; } | sort -u )"
  N_UNSTAGED_LEAN="$(printf '%s\n' "$UNSTAGED_ALL" | grep -c '\.lean$' || true)"
  UNSTAGED_LEAN_GLOB="$(printf '%s\n' "$UNSTAGED_ALL" | lean_glob_offenders)"
  UNIMPORTED_NEW="$(printf '%s\n' "$CHANGED" | unimported_new_modules)"

  classify_list <<< "$CHANGED"
  CLASS="$(class_name "$CLASS_RANK")"

  # A census with nothing to say must not be answered quietly.  An empty diff
  # is not a docs-only landing; it is a classification that MEASURED NOTHING,
  # and the safe direction is the full build.
  if [ "$N_CHANGED" = "0" ] && [ -n "$SINCE" ]; then
    # AN EMPTY INCREMENT IS NOT A CHEAP ONE.  The branch-diff path falls back
    # to the full build here, which is the safe reading of "measured nothing";
    # but a lane that asked to price an INCREMENT asked about something that
    # does not exist, and the honest answer is to say so before the ticket.
    die "the increment $BASE_SHA..HEAD is EMPTY — there is nothing on top of that green to price"
  fi
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
  FLOOR_USED="$FLOOR"
  GATES="$(gates_compose "$FLOOR" "$LANE_GATES" "$GATES_ONLY")"
  printf '  gates     %s\n' "$GATES"
  printf '  gate set  %s   (the CLASS FLOOR for `%s`)\n' "$(gate_names "$FLOOR")" "$CLASS"
  [ -n "$LANE_GATES" ] && [ "$GATES_ONLY" = "0" ] && printf '  %s\n' "(the floor, then the lane's own --gates: --gates ADDS, it never replaces)"
  gates_only_notice "$FLOOR" "$GATES_ONLY"
  printf '  COVERAGE (§5.4a)  %s\n' "$(coverage_statement "$CLASS")"
  gate_notice "$GATES" "$LANE_GATES"

  # Lean nothing imports: LOUD, but not a refusal — the file may be landing
  # together with the import that will reach it.
  if [ -n "$UNIMPORTED_NEW" ]; then
    echo "  !! IMPORTED BY NOTHING — these are in the diff and in no import graph:" >&2
    printf '%s\n' "$UNIMPORTED_NEW" | sed 's/^/       /' >&2
    echo "     The LeanModels library has no globs in lakefile.toml, so lake builds" >&2
    echo "     LeanModels.lean and its transitive imports ONLY.  A green build never" >&2
    echo "     compiled these, and is green about nothing where they are concerned." >&2
    echo "     Add the import in this landing, or say why it is deliberate." >&2
  fi

  # A stale generated index, when THIS landing touches the backlog.  Scoped to
  # the landing on purpose: another lane's stale index is not this lane's
  # refusal to eat.
  if printf '%s\n' "$CHANGED" | grep -q '^docs/backlog/.*\.md$' && index_is_stale; then
    echo "  STALE GENERATED INDEX: docs/backlog/INDEX.md" >&2
    if [ "$CLASSIFY_ONLY" = "1" ]; then
      echo "     (--classify-only: reported, not refused — no tenure is being taken)" >&2
    else
      die "this landing touches docs/backlog/ and the generated index is stale. Run tools/backlog-index.sh and re-stage. Refused HERE rather than at the docs_check gate because base rule 4 makes a triad one-per-landing: a red at the gate would cost the whole tenure, this costs one command. (A rebase leaves the index stale BY DESIGN — .gitattributes resolves it to one side rather than merging a generated file.)"
    fi
  fi

  # Unstaged Lean inside a lake glob: a REFUSAL when a tenure is at stake.
  if [ -n "$UNSTAGED_LEAN_GLOB" ]; then
    echo "  UNSTAGED LEAN UNDER A LAKE GLOB:" >&2
    printf '%s\n' "$UNSTAGED_LEAN_GLOB" | sed 's/^/       /' >&2
    if [ "$CLASSIFY_ONLY" = "1" ]; then
      echo "     (--classify-only: reported, not refused — no tenure is being taken)" >&2
    else
      die "REFUSING to spend a tenure on a tree whose Lean is not staged. A tenure verifies the STAGED tree, so these files would be compiled but not landed — or landed but not compiled. Stage them, or stash them, then re-run. (The Ada lane spent 78 minutes on exactly this.)"
    fi
  fi

  if [ "$CLASSIFY_ONLY" = "1" ]; then exit 0; fi

  if [ "$(tenure_needed "$CLASS" "$LANE_GATES")" = "no" ]; then
    say "docs-only: NO TENURE TAKEN — nothing here starts a Lean process (A11)"
    gates_only_notice "$FLOOR_USED" "$GATES_ONLY"
    gate_notice "$GATES" "$LANE_GATES"
    run_gates "$GATES"
    say "TRIAD DONE (docs-only, no build; gates $( [ "$rc" = 0 ] && echo green || echo RED ))"
    if [ -n "$SINCE" ]; then
      increment_coverage "$CLASS" | while IFS= read -r _l; do say "COVERAGE (§5.4a-i): $_l"; done
    else
      say "COVERAGE (§5.4a): $(coverage_statement "$CLASS")"
    fi
    # A DOCS GREEN ELABORATED NOTHING, so it is never a chain ROOT.  It can
    # still be a link IN a chain: a docs increment on top of a full green
    # carries that root forward, which is why `root` is a field and not a
    # boolean.
    if [ "$rc" = "0" ]; then
      if [ -n "$SINCE" ]; then
        record_green docs no "$SINCE_ROOT" "$(( $(ledger_field "$SINCE_LINE" depth) + 1 ))" ""
      else
        record_green docs no unknown 0 ""
      fi
      say "green recorded in $(green_ledger_path)"
    fi
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
  rm -f "$TIP_CACHE_FILE" 2>/dev/null
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

ENQ_STAMP="$(tree_stamp || true)"
printf '%s\n' "${ENQ_STAMP:-unstampable}" > "$QUEUE/$TICKET" \
  || die "cannot write a ticket into $QUEUE"
say "enqueued $TICKET (queue depth $(ls "$QUEUE" | wc -l | tr -d ' '))"
[ -n "$ENQ_STAMP" ] && say "tree at enqueue: $(short_tree "$ENQ_STAMP")"
say "delta vs master: $(delta_vs_master)"
say "base: $(base_staleness)"
# BOTH HALVES, so the transcript answers "did it run what I asked for?" without
# anyone reconstructing the composition rules from the flags.
say "gates: $(gates_planned)"
# THE LABEL RIDES WITH THE LINE.  A floor that grows shows up as a new gate in
# every lane's tenure at once; without a reason beside it the first lane to
# see it files a bug against its own run.
if [ "$GATES_ONLY" = "0" ] && [ "$FOREIGN" = "0" ] && [ "$CLASSIFY" = "0" ]; then
  say "  ($FLOOR_LABEL)"
fi
if [ -n "$LANE_GATES" ]; then
  say "gates asked by the lane: $LANE_GATES ($([ "$GATES_ONLY" = "1" ] && echo "--gates-only: REPLACES the floor" || echo "--gates: ADDS to the floor"))"
else
  say "gates asked by the lane: (none — the class floor only)"
fi
# Not when --classify already ran (it printed the real classification, and a
# second opinion from the same code is noise), and not for --foreign, where
# this repository's classes and floor do not apply at all (§7.1a).
if [ "$CLASSIFY" = "0" ] && [ "$FOREIGN" = "0" ]; then
  say "class: $(class_hint 2>/dev/null || printf 'not computed (the probe failed) — the tenure is FULL')"
fi

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

# ------------------------------------------- the tree, re-checked at ACQUIRE
NOW_STAMP="$(tree_stamp || true)"
if ! tree_change_report "$ENQ_STAMP" "$NOW_STAMP" "$BUILD_CURRENT_TREE"; then
  exit 2
fi

# AND THE BASE, RE-CHECKED HERE TOO.  The enqueue line is read by whoever
# typed the command; THIS one lands in the log beside the verdict, and the
# queue is hours deep — which is exactly when the fix lands, as it did for the
# pyc lane three minutes into its own build.  `fresh` because a cached answer
# from four hours ago is the very thing being warned about.
say "base at acquire: $(base_staleness fresh)"

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
# Explicit targets UNION onto the classifier's floor (never replace it).
# (the header is written per attempt, just below — the redirect truncates)
for _bt in $BUILD_TARGET_ARGS; do add_build_target "$_bt"; done
[ -n "$BUILD_TARGET_ARGS" ] && say "explicit --build-target: $BUILD_TARGET_ARGS (unioned; lane owes the coverage statement)"

BUILD_EXIT=1
for attempt in 1 2; do
  say "=== lake build ${BUILD_TARGETS:-<all default targets>} (attempt $attempt) ==="
  watchdog_start                      # A16: a fresh guard for EVERY attempt
  # UNQUOTED on purpose: BUILD_TARGETS is a target LIST, and every element was
  # validated as a plain Lean identifier path before it got here.  Empty means
  # the full build, which is exactly `lake build` with no arguments.
  build_log_header "$attempt" > "$BUILD_LOG"
  # shellcheck disable=SC2086
  nice -n "$NICE" lake build $BUILD_TARGETS >> "$BUILD_LOG" 2>&1
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
  build_red_report "$BUILD_LOG" "BUILD DID NOT COMPLETE (exit $BUILD_EXIT)"
  exit 1
fi

# The gates.  Default is this repo's triad (AGENTS.md); a lane overrides with
# --gates to add its own, INSIDE the same tenure — batching is base rule 4,
# and under A11 a second Lean invocation outside the tenure is a violation.
if [ "$FOREIGN" = "1" ]; then
  [ -n "$GATES" ] || die "--foreign with no gates reached the gate phase — a bug in triad.sh's own preconditions"
elif [ "$CLASSIFY" = "0" ]; then
  # THE ADA TRAP.  This used to be `if [ -z "$GATES" ]; then GATES=default; fi`,
  # under which `--gates "docs_check"` REPLACED the default and silently
  # dropped the differential.  --gates adds; --gates-only replaces, loudly.
  FLOOR_USED="$DEFAULT_FLOOR"
  GATES="$(gates_compose "$FLOOR_USED" "$LANE_GATES" "$GATES_ONLY")"
fi

# The gate phase's own build, paid HERE so it is accounted as a build.  Only a
# NARROWED tenure needs it: after a full build the runner is already up to
# date, and the gates' own `lake build` is a no-op that cannot fail.
GATE_BUILT=""
if [ -n "$BUILD_TARGETS" ]; then
  GATE_TARGETS="$(gate_runner_targets "$GATES")"
  if [ -n "$GATE_TARGETS" ]; then
    say "=== gate-phase build: $GATE_TARGETS (the gates invoke it; built HERE, not inside a gate) ==="
    # shellcheck disable=SC2086
    nice -n "$NICE" lake build $GATE_TARGETS >> "$BUILD_LOG" 2>&1
    gate_build_exit=$?
    if [ "$gate_build_exit" -ne 0 ]; then
      # This is a BUILD failure.  Letting it reach the gates is exactly the
      # misattribution this block exists to stop.
      build_red_report "$BUILD_LOG" \
        "GATE-PHASE BUILD FAILED (exit $gate_build_exit) — this is a BUILD failure, NOT a gate failure"
      exit 1
    fi
    GATE_BUILT="$GATE_TARGETS"
    export LS_RUNNER_PREBUILT=1
    GATES="$(announce_prebuilt "$GATES")"
    say "gate-phase build done; LS_RUNNER_PREBUILT=1 and diff_test gets --no-build"
  fi
fi

gates_only_notice "$FLOOR_USED" "$GATES_ONLY"
gate_notice "$GATES" "$LANE_GATES"
run_gates "$GATES"

# A GREEN TENURE MUST NAME ITS LOG TOO.  The file persists either way; what a
# lane loses is the PATH, and with 56 of them in one TMPDIR the newest is very
# likely somebody else's.
led="$(axiom_ledger "$BUILD_LOG")"; led_rc=$?
[ "$led_rc" != "1" ] && printf '%s\n' "$led" | while IFS= read -r l; do say "$l"; done
if [ "$led_rc" = "2" ]; then
  say "AXIOM LEDGER RED — the build compiled, and its axioms are not the declared set"
  rc=1
fi
say "$(build_log_pointer "$BUILD_LOG")"

say "TRIAD DONE (build exit $BUILD_EXIT, gates $( [ "$rc" = 0 ] && echo green || echo RED ))"
# §5.4a: the verdict carries the state it was taken in.  A scoped green that
# does not say what it covers is a number without its state.
[ "$FOREIGN" = "1" ] && say "COVERAGE (§5.4a): $(foreign_coverage)"
if [ -n "$SINCE" ]; then
  increment_coverage "$CLASS" | while IFS= read -r _l; do say "COVERAGE (§5.4a-i): $_l"; done
elif [ -n "$CLASS" ]; then
  say "COVERAGE (§5.4a): $(coverage_statement "$CLASS")"
fi
[ -n "$GATE_BUILT" ] && say "COVERAGE (§5.4a): gate phase additionally built: $GATE_BUILT"

# THE LEDGER IS WRITTEN LAST, and only on a GREEN triad: a red records
# nothing, because a ledger of attempts is a log, and a log is not evidence of
# a verdict.  `root=self` requires a FULL build — a narrowed green cannot be
# the root of a chain, which is what the merge bar above rests on.
if [ "$rc" = "0" ] && [ "$BUILD_EXIT" = "0" ] && [ "$FOREIGN" = "0" ]; then
  # A FULL BUILD IS ITS OWN ROOT, however it was reached.  This test comes
  # FIRST: an increment run whose build was NOT narrowed (a docs class that
  # kept its tenure builds every default target) elaborated everything, so
  # recording it as depth=1 under an older root would send the next lane's
  # increment back to a base it no longer needs — conservative, but wrong, and
  # the merge bar is stated in terms of what the root BUILT.
  if [ -z "$BUILD_TARGETS" ]; then
    record_green "${CLASS:-spine}" yes self 0 ""
  elif [ -n "$SINCE" ]; then
    record_green "${CLASS:-tier}" no "$SINCE_ROOT" "$(( $(ledger_field "$SINCE_LINE" depth) + 1 ))" "$BUILD_TARGETS"
  else
    record_green "${CLASS:-tier}" no unknown 0 "$BUILD_TARGETS"
  fi
  say "green recorded in $(green_ledger_path) — citable as an increment base with --since $(git -C "$CLONE" rev-parse --short HEAD 2>/dev/null)"
fi
exit "$rc"
