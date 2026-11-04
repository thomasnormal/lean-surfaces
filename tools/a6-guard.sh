#!/usr/bin/env bash
# tools/a6-guard.sh — THE OTHER HALF OF AMENDMENT 6.
#
# A6: never fetch-rebase (or merge) while a build runs in the same clone.
# `tools/triad.sh` already guards ONE direction — it refuses to BUILD while a
# rebase/merge is in progress (`.git/rebase-merge` &c.).  Nothing guarded the
# REVERSE, and on 2026-08-22 the rebuild lane merged while another lane's
# `lake build` had its clone as cwd.
#
# THE DEFECT WORTH NAMING is not that the check was missing — the lane HAD a
# check.  It was written as
#
#     [ "$d" = "$PWD" ] && echo "BUILD IN MY CLONE — STOP"
#
# which PRINTS and returns success, so the `&&` chain's caller sailed on and
# the merge ran anyway.  `set -e` does not help: the left side succeeded.
# **A check that only prints is not a guard.**  A guard exits.
#
# AND THE SAME DEFECT HAD A SECOND HALF, found by the 2026-08-23 audit: the
# guard FAILED OPEN.  `lsof` absent, failing, or denied sent every candidate
# down `continue`, left `found=0`, and exited 0 — "the tree may be rewritten".
# A guard that cannot read the machine must REFUSE, not wave through: silence
# from a probe is not evidence of absence, and this file already carries the
# sentence for it one paragraph up.
#
#   usage:  tools/a6-guard.sh [clone-dir]   # default: this script's repo
#           tools/a6-guard.sh --self-test   # every path, with mocked readers
#   exit 0  no Lean build has this clone as its cwd — the tree may be rewritten
#   exit 1  a build is live here — DO NOT rebase/merge/checkout
#   exit 2  CANNOT TELL — the probe is unavailable, so the answer is refusal
set -u
CLONE="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
# `pwd -P`, NOT `pwd`: lsof reports the PHYSICAL cwd, and on macOS /tmp is a
# symlink to /private/tmp.  With the logical path this comparison silently never
# matches — a guard that always says "clear" is worse than no guard, because it
# is trusted.  Found by testing the POSITIVE case; the negative case passed
# throughout and proved nothing.
CLONE="$(cd "$CLONE" && pwd -P)"

# Both readers are MOCKABLE, because a guard whose refusal path cannot be
# executed is a guard nobody has tested — and this one's could not be.
build_pids() {                  # -> candidate pids, one per line
  if [ -n "${LS_MOCK_PIDS+x}" ]; then printf '%s\n' $LS_MOCK_PIDS; return 0; fi
  { pgrep -f "bin/lake build" 2>/dev/null; pgrep -f "bin/lean " 2>/dev/null; }
}

cwd_of() {                      # pid -> its physical cwd; nonzero when unknown
  if [ -n "${LS_MOCK_CWD+x}" ]; then
    [ -n "$LS_MOCK_CWD" ] || return 1
    printf '%s\n' "$LS_MOCK_CWD"; return 0
  fi
  local d
  d="$(lsof -a -p "$1" -d cwd -Fn 2>/dev/null | grep '^n' | sed 's/^n//')" || return 1
  [ -n "$d" ] || return 1
  printf '%s\n' "$d"
}

probes_available() {            # 0 when the machine can actually be read
  [ -n "${LS_MOCK_PIDS+x}" ] && return 0
  command -v pgrep >/dev/null 2>&1 || return 1
  command -v lsof  >/dev/null 2>&1 || return 1
  return 0
}

if [ "${1:-}" = "--self-test" ]; then
  ok=0; bad=0
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; \
            else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }
  here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
  self="${BASH_SOURCE[0]}"
  # THE POSITIVE CASE, which is the one that was never driven.
  out="$(LS_MOCK_PIDS=4242 LS_MOCK_CWD="$here" bash "$self" "$here" 2>&1)"; rc=$?
  check "a build in THIS clone refuses"        "$rc" "1"
  check "  ...naming the pid and the clone"    "$(printf '%s' "$out" | grep -c 'pid 4242 is building')" "1"
  rc=0; LS_MOCK_PIDS=4242 LS_MOCK_CWD="/somewhere/else" bash "$self" "$here" >/dev/null 2>&1 || rc=$?
  check "a build ELSEWHERE is allowed"         "$rc" "0"
  rc=0; LS_MOCK_PIDS="" bash "$self" "$here" >/dev/null 2>&1 || rc=$?
  check "no builds at all is allowed"          "$rc" "0"
  # THE FAIL-OPEN, which the audit found: an unreadable cwd is NOT absence.
  out="$(LS_MOCK_PIDS=4242 LS_MOCK_CWD="" bash "$self" "$here" 2>&1)"; rc=$?
  check "an UNREADABLE cwd refuses, not skips" "$rc" "2"
  check "  ...saying it cannot tell"           "$(printf '%s' "$out" | grep -c 'CANNOT TELL')" "1"
  # An ABSOLUTE bash: `PATH=/nonexistent bash …` cannot find bash itself, and
  # the first cut measured 127 (command-not-found) while believing it had
  # measured the guard's refusal.
  out="$(PATH=/nonexistent "$BASH" "$self" "$here" 2>&1)"; rc=$?
  check "a missing probe refuses"              "$rc" "2"
  check "  ...rather than waving the tree through" "$(printf '%s' "$out" | grep -c 'CANNOT TELL')" "1"
  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

if ! probes_available; then
  echo "A6: CANNOT TELL — pgrep or lsof is unavailable, so whether a build holds" >&2
  echo "    $CLONE cannot be established. Refusing: silence from a probe is not" >&2
  echo "    evidence of absence." >&2
  exit 2
fi

found=0
for p in $(build_pids); do
  case "$p" in ''|*[!0-9]*) continue ;; esac
  if ! d="$(cwd_of "$p")"; then
    echo "A6: CANNOT TELL — pid $p is a Lean process whose cwd could not be read" >&2
    echo "    (lsof denied or failed). Refusing rather than assuming it is elsewhere." >&2
    exit 2
  fi
  if [ "$d" = "$CLONE" ]; then
    echo "A6: pid $p is building in $CLONE — do NOT rewrite the tree" >&2
    found=1
  fi
done
[ "$found" = "0" ] || exit 1
exit 0
