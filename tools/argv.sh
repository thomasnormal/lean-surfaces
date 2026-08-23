#!/usr/bin/env bash
# Shared argv guard for this lane's tools.  Sourced, never executed.
#
# A VALUE-TAKING FLAG WRITTEN LAST USED TO SPIN FOREVER, SILENTLY.  The arm
#
#     --gates) GATES="${2:-}"; shift 2 ;;
#
# has three tolerant parts that compose into a hang: `${2:-}` accepts the
# missing value, `shift 2` then FAILS because only one argument is left (and
# without `set -e` a failed shift is not fatal), and `while [ $# -gt 0 ]`
# re-enters on the SAME argument.  The loop never advances.  There is no
# output, no lock is taken, and nothing distinguishes it from waiting in the
# build queue — so the natural response is to wait longer.  It cost the Go
# lane 31 minutes across two runs before anyone suspected the parser.
#
# THE NEAR-MISS IS WORSE THAN THE SPIN.  A spin is at least visible as "it
# never finished".  A run that merely LOST its value would complete and report
# green on a DEFAULT scope — less coverage than the lane believes it bought,
# with nothing in the log to say so.  A green whose scope silently shrank is
# the failure this lane exists to prevent (§5.3: a vacuous run must not read
# as agreement).  So this REFUSES; it never defaults, and it never warns and
# continues.
#
# The check is on the COUNT, not on the next argument's shape: `--lane --dir`
# is a missing value too, but so is `--out -3`, and a tool may legitimately
# take a value that starts with a dash.  Counting is the only test that does
# not have to guess.
need_val() {                    # need_val "$#" "$1"  -> dies unless a value follows
  [ "${1:-0}" -ge 2 ] && return 0
  echo "${0##*/}: flag ${2:-?} needs a value" >&2
  echo "  (it was written last, with nothing after it)" >&2
  exit 2
}
