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
#   usage:  tools/a6-guard.sh [clone-dir]   # default: this script's repo
#   exit 0  no Lean build has this clone as its cwd — the tree may be rewritten
#   exit 1  a build is live here — DO NOT rebase/merge/checkout
set -u
CLONE="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
# `pwd -P`, NOT `pwd`: lsof reports the PHYSICAL cwd, and on macOS /tmp is a
# symlink to /private/tmp.  With the logical path this comparison silently never
# matches — a guard that always says "clear" is worse than no guard, because it
# is trusted.  Found by testing the POSITIVE case; the negative case passed
# throughout and proved nothing.
CLONE="$(cd "$CLONE" && pwd -P)"

found=0
for p in $(pgrep -f "bin/lake build" 2>/dev/null; pgrep -f "bin/lean " 2>/dev/null); do
  case "$p" in ''|*[!0-9]*) continue ;; esac
  d="$(lsof -a -p "$p" -d cwd -Fn 2>/dev/null | grep '^n' | sed 's/^n//')"
  [ -n "$d" ] || continue
  if [ "$d" = "$CLONE" ]; then
    echo "A6: pid $p is building in $CLONE — do NOT rewrite the tree" >&2
    found=1
  fi
done
[ "$found" = "0" ] || exit 1
exit 0
