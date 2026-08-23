#!/usr/bin/env bash
# tools/analogues.sh — how many PROVED analogues does this shape have, and
# how long were they?
#
# WHY THIS FILE EXISTS.  The Lean tier's M2 census picked its first proof
# target on evidence that had nothing to do with the subject's difficulty and
# everything to do with its NEIGHBOURHOOD: `isDefEqUnitLike.WF` was chosen as
# a "9-line subject, no proj dependency, one waiting consumer in the same
# file, 26 PROVED ANALOGUES AROUND IT AT A MEDIAN OF 15 LINES"
# (docs/backlog/lean-tier.md 2026-08-22-lean-tier-2).
#
# That is a tractability estimate you can take in seconds, and it is the
# cheapest one available: a shape with 26 neighbours at 15 lines is routine
# work; the same shape with 2 neighbours at 200 lines is a research project
# wearing a theorem's clothes.  The estimate is also the honest way to price
# an inch BEFORE committing to it — §8's "no step's claim is real until an
# instrument re-derives it", pointed at your own plan.
#
# WHAT IT MEASURES, precisely.  Declarations whose STATEMENT matches the
# shape, and the LINE COUNT of each declaration's block.  It is a proxy: a
# 15-line proof of a hard lemma exists, and so does a 200-line one that is all
# bookkeeping.  Quote it as what it is — a neighbourhood size, not a
# difficulty — and note that a count WITHOUT a median is not evidence at all.
#
# USAGE
#   tools/analogues.sh <shape>            # a named shape, or any ERE
#   tools/analogues.sh --list             # the named shapes
#   tools/analogues.sh <shape> --top 12   # how many exemplars to print
#   tools/analogues.sh --self-test
#
# ZERO Lean execution: this greps text.  Safe outside a tenure (A11).

set -u

CLONE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOP=8
SHAPE=""
SELF_TEST=0

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
die()   { echo "analogues.sh: $*" >&2; exit 2; }

# The named shapes ARE the cookbook's entries, so a lane that read one can
# measure it without inventing a regex.
shape_regex() {
  case "$1" in
    determinism) echo 'Deterministic|_det\b|obs .*=.*obs |cycleOf' ;;
    membership)  echo '∈ *(permitted|allowed)|permitted|Outcome.*∈' ;;
    fuel)        echo '\(F *:|∀ *F|fuel|Fuel' ;;
    frame)       echo 'PstAt|Frame\b|\.update_ne' ;;   # NOT `.push`: too generic
    fold)        echo 'FoldInv|Inv\b.*rounds|RoundOK|invariant' ;;
    triple)      echo '⦃' ;;
    spec)        echo '@\[spec\]' ;;
    inversion)   echo '\.exhausts|\.uncons|inversion|_inv\b' ;;
    refusal)     echo 'refuse|Halt|REFUSE|unsupported' ;;
    mono)        echo 'fuelMono|[Mm]ono\b|monotone' ;;
    refinement)  echo '\.map .*=|refine|simulat' ;;
    threshold)   echo '∃ *t.*∀ *F|≥ *t' ;;
    *)           echo "" ;;
  esac
}
SHAPE_NAMES="determinism membership fuel frame fold triple spec inversion refusal mono refinement threshold"

# ---- the scanner.  One awk pass per file: find declarations, measure blocks.
# A declaration's block runs from its own line to the line before the next
# top-level construct.  That over-counts a decl followed by trailing comments
# and under-counts nothing, which is the direction to err in for a COST
# estimate.
# `awk -v` STRIPS ONE BACKSLASH LEVEL before the string is used as a dynamic
# regex — the third time this tree has met it (sites.sh's literal dot, the
# declaration walk, now here).  Here it did not merely mis-match: `\(` became a
# group-open and awk DIED with "syntax error in regular expression", so the
# `fuel` shape returned nothing at all and looked like an empty neighbourhood.
awk_re() { printf '%s' "$1" | sed 's/\\/\\\\/g'; }

scan_tree() {                   # scan_tree <root> <ere>  -> "len<TAB>file:line<TAB>name"
  local root="$1" re="$2" f
  find "$root" -name '*.lean' -type f 2>/dev/null | LC_ALL=C sort | while IFS= read -r f; do
    awk -v FN="${f#"$root"/}" -v RE="$(awk_re "$re")" '
      # The block ENDS at its last non-blank line.  Counting to the next
      # construct instead adds the trailing blank lines to every entry — a
      # constant bias the self-test caught by predicting 2.5 and getting 3.5.
      function flush() {
        if (start > 0 && stmt ~ RE)
          printf "%d\t%s:%d\t%s\n", lastnb - start + 1, FN, start, name
        start = 0; stmt = ""; name = ""
      }
      # A new top-level construct closes the previous block.
      /^(@\[|theorem |lemma |def |abbrev |instance |structure |inductive |example |end |namespace |section |open |import |universe |variable |\/-)/ {
        flush()
      }
      /^(@\[[^]]*\][ \t]*)?(private[ \t]+)?(theorem|lemma)[ \t]+[^ \t(:{]+/ {
        start = NR
        name = $0
        sub(/^(@\[[^]]*\][ \t]*)?(private[ \t]+)?(theorem|lemma)[ \t]+/, "", name)
        sub(/[ \t(:{].*$/, "", name)
        instmt = 1
      }
      # The STATEMENT is everything up to the proof marker.
      start > 0 && instmt { stmt = stmt " " $0; if ($0 ~ /:=/) instmt = 0 }
      $0 !~ /^[ \t]*$/ { lastnb = NR }
      END { if (start > 0 && stmt ~ RE) printf "%d\t%s:%d\t%s\n", lastnb - start + 1, FN, start, name }
    ' "$f"
  done
}

stats() {                       # stdin: rows -> "count median min max"
  LC_ALL=C sort -n | awk '
    { len[NR] = $1 }
    END {
      n = NR
      if (n == 0) { print "0 - - -"; exit }
      if (n % 2) med = len[(n + 1) / 2]
      else { s = (len[n/2] + len[n/2 + 1]) / 2; med = (s == int(s)) ? int(s) : s }
      print n, med, len[1], len[n]
    }'
}

# --------------------------------------------------------------- self-test
if [ "${1:-}" = "--self-test" ]; then
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/analogues-selftest.XXXXXX")" || die "no temp dir"
  trap 'rm -rf "$tmp"' EXIT
  ok=0; bad=0
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; \
            else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }

  mkdir -p "$tmp/t"
  cat > "$tmp/t/a.lean" <<'LEAN'
import Foo

theorem one_liner (h : PstAt w) : True := by
  trivial

theorem three_liner (h : PstAt w) : True := by
  have x := h
  trivial

theorem unrelated (n : Nat) : n = n := by
  rfl

@[spec]
theorem attributed (h : PstAt w) : True := by
  trivial
LEAN
  cat > "$tmp/t/b.lean" <<'LEAN'
theorem five_liner (h : PstAt w) :
    True := by
  have a := h
  have b := a
  trivial
LEAN

  out="$(scan_tree "$tmp/t" 'PstAt')"
  check "it finds the matching statements"   "$(printf '%s\n' "$out" | grep -c .)" "4"
  check "it ignores the non-matching one"    "$(printf '%s' "$out" | grep -c unrelated)" "0"
  check "an @[spec] decl is found"           "$(printf '%s' "$out" | grep -c attributed)" "1"
  check "a MULTI-LINE statement is matched"  "$(printf '%s' "$out" | grep -c five_liner)" "1"
  check "the file:line is reported"          "$(printf '%s' "$out" | grep -c 'a.lean:3')" "1"

  # lengths: one_liner 2, three_liner 3, attributed 2 (block starts at @[spec]
  # -> the decl line), five_liner 5.  Sorted: 2 2 3 5 -> median 2.5
  set -- $(printf '%s\n' "$out" | stats)
  check "the COUNT is right"     "$1" "4"
  check "the MEDIAN is right"    "$2" "2.5"
  check "the MIN is right"       "$3" "2"
  check "the MAX is right"       "$4" "5"

  set -- $(scan_tree "$tmp/t" 'NoSuchThingAnywhere' | stats)
  check "an EMPTY result counts 0, not an error" "$1" "0"
  check "  ...and reports no median"             "$2" "-"

  set -- $(scan_tree "$tmp/does-not-exist" 'PstAt' | stats)
  check "a missing tree yields 0, loudly upstream" "$1" "0"

  # EVERY NAMED SHAPE MUST MATCH A KNOWN INSTANCE.  Without this row the
  # `fuel` shape shipped a regex that made awk exit with a syntax error, and an
  # empty result is indistinguishable from a small neighbourhood.
  sh="$tmp/shapes"; mkdir -p "$sh"
  cat > "$sh/S.lean" <<'LEAN'
theorem d1 (d : Design) : Deterministic d := by trivial
theorem m1 : obs r ∈ permitted site := by trivial
theorem f1 (F : Nat) : execFuel F = x := by trivial
theorem fr1 (w : W) : PstAt w := by trivial
theorem fo1 (rs : List R) : FoldInv g v b rs := by trivial
theorem t1 : ⦃P⦄ prog ⦃⇓ r => Q r⦄ := by trivial
@[spec] theorem sp1 : True := by trivial
theorem iv1 : Judgment.exhausts x := by trivial
theorem rf1 : refuse c m = Halt.unsupported c m := by trivial
theorem mo1 : fuelMono a b := by trivial
theorem rn1 : (run d).map cycleOf = x := by trivial
theorem th1 : ∃ t, ∀ F ≥ t, P F := by trivial
LEAN
  for shp in $SHAPE_NAMES; do
    n="$(scan_tree "$sh" "$(shape_regex "$shp")" 2>/dev/null | grep -c . || true)"
    check "shape '$shp' matches a known instance" "$( [ "$n" -ge 1 ] && echo yes )" "yes"
  done

  check "a named shape resolves"      "$(shape_regex triple)" "⦃"
  check "an unknown name resolves to nothing" "$(shape_regex nope)" ""
  check "--list has twelve shapes"    "$(for s in $SHAPE_NAMES; do echo "$s"; done | grep -c .)" "12"

  # DOUBLE-RUN BYTE-IDENTICAL (§5.4), on the instrument itself.
  check "double run is byte-identical" \
        "$( [ "$(scan_tree "$tmp/t" 'PstAt' | md5 2>/dev/null || scan_tree "$tmp/t" 'PstAt' | md5sum)" \
           = "$(scan_tree "$tmp/t" 'PstAt' | md5 2>/dev/null || scan_tree "$tmp/t" 'PstAt' | md5sum)" ] && echo same)" "same"

  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

if [ "${1:-}" = "--list" ]; then
  for s in $SHAPE_NAMES; do printf '%-12s %s\n' "$s" "$(shape_regex "$s")"; done
  echo
  echo "Any other argument is used as an ERE over the statement text."
  exit 0
fi

while [ $# -gt 0 ]; do
  case "$1" in
    --dir) CLONE="${2:-}"; shift 2 ;;
    --top) TOP="${2:-}"; shift 2 ;;
    -h|--help) usage ;;
    -*)    die "unknown argument '$1'" ;;
    *)     SHAPE="$1"; shift ;;
  esac
done
[ -n "$SHAPE" ] || usage
[ -d "$CLONE" ] || die "--dir '$CLONE' is not a directory"

RE="$(shape_regex "$SHAPE")"
KIND="named shape"
if [ -z "$RE" ]; then RE="$SHAPE"; KIND="ERE"; fi

ROWS="$(scan_tree "$CLONE" "$RE")"
set -- $(printf '%s\n' "$ROWS" | stats)
COUNT="$1"; MED="$2"; MIN="$3"; MAX="$4"
NFILES="$(find "$CLONE" -name '*.lean' -type f 2>/dev/null | grep -c .)"
SHA="$(git -C "$CLONE" rev-parse --short HEAD 2>/dev/null || echo 'not a git tree')"

echo "analogues.sh — $KIND \`$SHAPE\`  (/$RE/)"
# MEAS-10: a number carries the state it was measured in.  Quote both.
echo "  measured  $NFILES .lean files at $SHA"
if [ "$COUNT" = "0" ]; then
  echo "  ANALOGUES 0"
  echo "  A zero here is a finding about the SHAPE OR THE REGEX, not evidence"
  echo "  that the proof is hard.  Check the pattern against one known"
  echo "  instance before concluding anything (§5.4: an empty result is an"
  echo "  instrument fault until shown otherwise)."
  exit 0
fi
echo "  ANALOGUES $COUNT"
echo "  MEDIAN    $MED lines        RANGE $MIN .. $MAX"
echo "  the $TOP shortest:"
printf '%s\n' "$ROWS" | LC_ALL=C sort -n | head -n "$TOP" \
  | awk -F'\t' '{ printf "    %4s  %-52s %s\n", $1, $2, $3 }'
echo
echo "  Quote this as a NEIGHBOURHOOD SIZE, never as a difficulty: a count"
echo "  without a median is not tractability evidence, and a median without"
echo "  the count is not either."
