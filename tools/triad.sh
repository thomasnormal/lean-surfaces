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
#
# NOT YET WIRED INTO ANY LANE'S FLOW.  Adoption is per-lane, on dispatch.
#
# USAGE
#   tools/triad.sh --lane <name> [--dir <clone>] [--gates "cmd; cmd"] [...]
#   tools/triad.sh --self-test          # exercises the queue logic, NO Lean
#   tools/triad.sh --lane x --dry-run   # takes a real tenure, runs no Lean
#
# The lock and queue paths are overridable (LS_LOCK / LS_QUEUE) so the logic
# can be exercised in a sandbox.  A live run always uses the real paths.

set -u

# ---------------------------------------------------------------- settings
LANE=""
CLONE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOCK="${LS_LOCK:-/tmp/ls-build.lock}"
QUEUE="${LS_QUEUE:-/tmp/ls-build-queue}"
RSS_LIMIT_KB="${LS_RSS_LIMIT_KB:-3145728}"     # 3 GB, amendment 11
THREADS="${LEAN_NUM_THREADS:-2}"               # amendment 11
NICE="${LS_NICE:-19}"                          # amendment 11
MAX_WAIT="${LS_MAX_WAIT:-14400}"               # 4 h, then give up LOUDLY
STALE_AFTER="${LS_STALE_AFTER:-1800}"          # only then consider a reclaim
DRY_RUN=0
SELF_TEST=0
GATES=""

usage() { sed -n '1,60p' "${BASH_SOURCE[0]}" >&2; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --lane)      LANE="${2:-}"; shift 2 ;;
    --dir)       CLONE="${2:-}"; shift 2 ;;
    --gates)     GATES="${2:-}"; shift 2 ;;
    --rss-limit) RSS_LIMIT_KB="${2:-}"; shift 2 ;;
    --dry-run)   DRY_RUN=1; shift ;;
    --self-test) SELF_TEST=1; shift ;;
    -h|--help)   usage ;;
    *)           echo "triad.sh: unknown argument '$1'" >&2; usage ;;
  esac
done

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

own_rss_kb() {                        # summed RSS of this script's descendants
  local pids total=0 r
  pids="$(descendants $$)"
  for p in $pids; do
    r="$(ps -o rss= -p "$p" 2>/dev/null | tr -d ' ')"
    case "$r" in ''|*[!0-9]*) continue ;; esac
    total=$((total + r))
  done
  echo "$total"
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

  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

# ------------------------------------------------------------ preconditions
[ -n "$LANE" ] || die "--lane <name> is required (it goes in the owner file)"
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
# A11, and base rule 6: OUR descendants only, recursively.  A guard rooted at
# a pipeline's last stage (`pgrep -P $!` where $! is `tail`) can never see the
# build — two of the six measured scripts shipped exactly that.
(
  while kill -0 $$ 2>/dev/null; do
    sleep 20
    tot="$(own_rss_kb)"
    if [ "$tot" -gt "$RSS_LIMIT_KB" ]; then
      echo "RSS KILL LINE: own chain at $((tot / 1024)) MB > $((RSS_LIMIT_KB / 1024)) MB — killing OUR chain" >&2
      for p in $(descendants $$); do kill -9 "$p" 2>/dev/null; done
    fi
  done
) & WATCHDOG=$!

# ----------------------------------------------------------------- the work
export LEAN_NUM_THREADS="$THREADS"    # A11.  NEVER `-j` — base rule 2.
say "tenure open: LEAN_NUM_THREADS=$THREADS nice -n $NICE rss<=$((RSS_LIMIT_KB / 1024))MB dir=$CLONE"

if [ "$DRY_RUN" = "1" ]; then
  say "DRY RUN: tenure taken, no Lean executed, releasing"
  exit 0
fi

BUILD_LOG="$(mktemp "${TMPDIR:-/tmp}/triad-build.XXXXXX")"
BUILD_EXIT=1
for attempt in 1 2; do
  say "=== lake build (attempt $attempt) ==="
  nice -n "$NICE" lake build > "$BUILD_LOG" 2>&1
  BUILD_EXIT=$?
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
rc=0
old_ifs="$IFS"; IFS=';'
for g in $GATES; do
  g="$(printf '%s' "$g" | sed -e 's/^ *//' -e 's/ *$//')"
  [ -n "$g" ] || continue
  say "=== gate: $g ==="
  nice -n "$NICE" sh -c "$g" || { rc=1; say "  GATE FAILED: $g"; }
done
IFS="$old_ifs"

say "TRIAD DONE (build exit $BUILD_EXIT, gates $( [ "$rc" = 0 ] && echo green || echo RED ))"
exit "$rc"
