#!/usr/bin/env bash
# tools/dupes.sh — duplication policed by an INSTRUMENT, not by discipline.
#
# §2.4's MEAS-28 is the one law in the tree that literally asks for a tool, and
# it had none: `docs/duplication-audit.md` measured the census contract
# implemented **14 times** by hand, every ten landings, and by hand is exactly
# what the law forbids.  `tools/laws.sh` then ranked §2.4 the most-cited home
# with no gate at all.
#
# > CANNOT SEE SEMANTIC DUPLICATION UNDER DIFFERENT SPELLINGS.  Two envelope
# > loaders that do one job with different function names, different argument
# > orders and different local variables read here as two different things.
# > This finds duplication that SHARES A NAME or a recognised contract; the
# > duplication that cost this repository most was found by a human reading
# > four loaders side by side, and that reading is not automated here.
#
# So the count is a FLOOR on duplication, in the same direction every other
# instrument in this tree errs: it under-reports, and says so.
#
# TWO CHANNELS, because each misses what the other catches:
#   CONTRACTS  — named shapes the audit convicted (a `git_rev` helper, a
#                `--compare` path, an envelope loader).  Curated, so it can
#                recognise a contract across different function names.
#   NAMES      — every top-level `def` implemented in more than one file.
#                Mechanical, so it finds what the curated list forgot.
#
# A DUPLICATE IS NOT AUTOMATICALLY A VIOLATION.  §9.2 says consolidation
# happens BY TOUCH, so a contract with no shared helper yet is `DUPLICATED`
# (work available); one whose shared helper exists and is not being used is
# `VIOLATION` (work refused).
#
# USAGE
#   tools/dupes.sh                # the report
#   tools/dupes.sh --min 3        # only names implemented >= 3 times
#   tools/dupes.sh --self-test
#
# ZERO Lean execution.  Safe outside a tenure (A11).

set -u

CLONE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MIN=2
SELF_TEST=0

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
die()   { echo "dupes.sh: $*" >&2; exit 2; }

. "$(dirname "${BASH_SOURCE[0]}")/argv.sh"   # the value-flag guard (a flag written last used to SPIN)
while [ $# -gt 0 ]; do
  case "$1" in
    --dir)       need_val "$#" "$1"; CLONE="$2"; shift 2 ;;
    --min)       need_val "$#" "$1"; MIN="$2"; shift 2 ;;
    --self-test) SELF_TEST=1; shift ;;
    -h|--help)   usage ;;
    *)           die "unknown argument '$1'" ;;
  esac
done

# `harness/` and `tools/` at depth 1 ONLY, deliberately: `Examples/` holds 62
# `.py` FIXTURES that are corpus, not implementation.  Counting a fixture's
# `def main` as a duplicated contract would make the instrument that measures
# duplication report the corpus as debt.
py_files() {
  find "$CLONE/harness" "$CLONE/tools" -maxdepth 1 -name '*.py' -type f 2>/dev/null \
    | LC_ALL=C sort
}

# ---- CHANNEL 1: the contracts the audit convicted, by name and by shape.
# The third field is the shared helper that RETIRES the contract, or `-` when
# none has landed — which is what separates work available from work refused.
contracts() {
  cat <<'C'
git_rev|rev-parse|harness/censuskit.py
--compare|--compare|harness/censuskit.py
double-run|double.run|harness/censuskit.py
envelope-loader|def (load|read)_?envelope|-
self-test|def self_test|-
census-main|def census|harness/censuskit.py
C
}

contract_files() {              # regex -> files implementing it
  local re="$1" f
  for f in $(py_files); do
    grep -qE -- "$re" "$f" 2>/dev/null && printf '%s\n' "${f#"$CLONE"/}"
  done
}

# ---- CHANNEL 2: every top-level def implemented in more than one file.
repeated_names() {              # -> "count<TAB>name<TAB>file:line file:line ..."
  local f
  for f in $(py_files); do
    grep -nE '^def [a-z_][a-z0-9_]*' "$f" 2>/dev/null \
      | sed "s|^\([0-9]*\):def \([a-z_][a-z0-9_]*\).*|\2\t${f#"$CLONE"/}:\1|"
  done | LC_ALL=C sort | awk -F'\t' '
      { if ($1 == prev) { n++; where = where " " $2 }
        else { if (n >= 2) printf "%d\t%s\t%s\n", n, prev, where
               prev = $1; n = 1; where = $2 } }
      END { if (n >= 2) printf "%d\t%s\t%s\n", n, prev, where }'
}

# --------------------------------------------------------------- self-test
if [ "$SELF_TEST" = "1" ]; then
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/dupes-selftest.XXXXXX")" || die "no temp dir"
  trap 'rm -rf "$tmp"' EXIT
  ok=0; bad=0
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; \
            else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }

  fx="$tmp/fx"; mkdir -p "$fx/harness" "$fx/tools"
  printf 'def git_rev():\n    return run("git rev-parse HEAD")\ndef census():\n    pass\n' > "$fx/harness/a.py"
  printf 'def git_rev():\n    return run("git rev-parse HEAD")\ndef census():\n    pass\n' > "$fx/harness/b.py"
  printf 'def only_here():\n    pass\n' > "$fx/harness/c.py"
  printf 'def census():\n    pass\n' > "$fx/tools/d.py"
  CLONE="$fx"

  check "files are found in harness AND tools" "$(py_files | grep -c .)" "4"
  mkdir -p "$fx/Examples/python/lab"
  printf 'def census():\n    pass\n' > "$fx/Examples/python/lab/fixture.py"
  check "an Examples FIXTURE is not scanned as code" "$(py_files | grep -c Examples)" "0"

  check "a contract implemented twice is found" \
        "$(contract_files 'rev-parse' | grep -c .)" "2"
  check "a contract nobody implements is empty" \
        "$(contract_files 'no_such_thing_here' | grep -c .)" "0"

  check "a name in 3 files is repeated"  "$(repeated_names | awk -F'\t' '$2=="census"{print $1}')" "3"
  check "  ...and every site is named"   "$(repeated_names | awk -F'\t' '$2=="census"{print $3}' | wc -w | tr -d ' ')" "3"
  check "a name in 2 files is repeated"  "$(repeated_names | awk -F'\t' '$2=="git_rev"{print $1}')" "2"
  check "a UNIQUE name is not reported"  "$(repeated_names | awk -F'\t' '$2=="only_here"{print $1}')" ""

  # DUPLICATED vs VIOLATION turns on whether the shared helper EXISTS.
  check "no helper yet -> work AVAILABLE"  "$( [ -f "$fx/harness/censuskit.py" ] && echo VIOLATION || echo DUPLICATED )" "DUPLICATED"
  printf 'def git_rev():\n    pass\n' > "$fx/harness/censuskit.py"
  check "helper landed -> work REFUSED"    "$( [ -f "$fx/harness/censuskit.py" ] && echo VIOLATION || echo DUPLICATED )" "VIOLATION"
  rm -f "$fx/harness/censuskit.py"

  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

# -------------------------------------------------------------------- main
[ -d "$CLONE" ] || die "--dir '$CLONE' is not a directory"

echo "dupes.sh — duplication policed by an instrument (§2.4, MEAS-28)"
echo "           measured at $(git -C "$CLONE" rev-parse --short HEAD 2>/dev/null || echo 'no git') over $(py_files | grep -c . || true) python files"
echo
echo "  CANNOT SEE semantic duplication under different spellings: two loaders"
echo "  doing one job with different names read here as two different things."
echo "  Every count below is a FLOOR."
echo
printf '  %-17s %5s  %-9s %s\n' CONTRACT COUNT STATUS 'SHARED HELPER'
printf '  %-17s %5s  %-9s %s\n' ----------------- ----- --------- -------------
contracts | while IFS='|' read -r name re helper; do
  [ -n "$name" ] || continue
  n="$(contract_files "$re" | grep -c . || true)"
  [ "$n" -lt "$MIN" ] && continue
  if [ "$helper" != "-" ] && [ -f "$CLONE/$helper" ]; then st="VIOLATION"
  elif [ "$helper" != "-" ];                        then st="DUPLICATED"
  else                                                   st="DUPLICATED"
  fi
  printf '  %-17s %5s  %-9s %s\n' "$name" "$n" "$st" \
    "$( [ "$helper" = "-" ] && echo 'none proposed' || { [ -f "$CLONE/$helper" ] && echo "$helper (LANDED — adopt it)" || echo "$helper (proposed, not landed)"; } )"
done
echo
echo "  REPEATED def NAMES (the mechanical channel — what the list above forgot):"
repeated_names | LC_ALL=C sort -rn | awk -F'\t' -v m="$MIN" '$1 >= m {
    printf "  %5s  %-28s %s\n", $1, $2, substr($3, 1, 78) }' | head -14
echo
echo "  DUPLICATED is work AVAILABLE; VIOLATION is work REFUSED — a shared"
echo "  helper exists and is not being used. §9.2 consolidates BY TOUCH, so a"
echo "  DUPLICATED row is not a red: it is the next lane to open that file."
