#!/usr/bin/env bash
# tools/laws.sh — which laws have a GATE, and which are only prose.
#
# WHY THIS FILE EXISTS.  §9.7's audit cadence has been doing this by hand, and
# the standing rule it serves is blunt:
#
#   > FIXES LIVE IN GATES.  A law whose only enforcement is prose is a law
#   > that gets guessed — measured at a 38% violation density across the
#   > applicable protocol cells, by lanes that had read the protocol.
#
# So this walks `docs/law-index.md`, §7.1a's amendment register and §7's tools
# list, and reports for each law the tool that CITES its durable home — or
# `NO GATE`.  The NO GATE list is then sorted by how many lane ledgers cite the
# law, so the next inch is chosen by MEASURED DEMAND rather than by whoever
# remembers it at the time.
#
# WHAT "ENFORCED" CAN HONESTLY MEAN HERE, and the direction of the error.
# This greps text; it cannot tell a gate from a comment.  A tool that MENTIONS
# §7.1a in a header is evidence of intent, not of enforcement — so the
# `CITED BY` column is a PROXY, and it errs by over-crediting.  Therefore:
#
#   > The NO GATE list is a LOWER BOUND on the unenforced set. The real one is
#   > larger, and no number here should be quoted as coverage.
#
# That is the same shape as the destructure count in §5.4a: a bound you can
# act on, not a census you can report.
#
# USAGE
#   tools/laws.sh                 # the report
#   tools/laws.sh --top 5         # just the NO GATE head
#   tools/laws.sh --verbose       # every law, with its citing tools
#   tools/laws.sh --self-test
#
# ZERO Lean execution.  Safe outside a tenure (A11).

set -u

CLONE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOP=10
VERBOSE=0
SELF_TEST=0

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
die()   { echo "laws.sh: $*" >&2; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --dir)       CLONE="${2:-}"; shift 2 ;;
    --top)       TOP="${2:-}"; shift 2 ;;
    --verbose)   VERBOSE=1; shift ;;
    --self-test) SELF_TEST=1; shift ;;
    -h|--help)   usage ;;
    *)           die "unknown argument '$1'" ;;
  esac
done

INDEX="$CLONE/docs/law-index.md"
FAMILY="$CLONE/docs/family-architecture.md"
LEDGERS="$CLONE/docs/backlog"

# ---- the laws.  One row per law: "id<TAB>hook<TAB>home".
law_rows() {
  [ -f "$INDEX" ] || return 0
  awk -F'|' '
    /^\| (MEAS|STMT|PROOF|OPS|CLONE)-[0-9]+ \|/ {
      id = $2; hook = $3; home = $4
      gsub(/^[ \t]+|[ \t]+$/, "", id)
      gsub(/^[ \t]+|[ \t]+$/, "", hook)
      gsub(/^[ \t]+|[ \t]+$/, "", home)
      printf "%s\t%s\t%s\n", id, hook, home
    }' "$INDEX"
}

# ---- the amendment register (§7.1a).  Its ids are `A<n>`, and a LOST row is
# reported as such rather than counted as enforced — an amendment with no text
# cannot have a gate.
amendment_rows() {
  [ -f "$FAMILY" ] || return 0
  awk -F'|' '
    /^\| [0-9]+ \| / {
      n = $2; rule = $3; status = $4
      gsub(/^[ \t]+|[ \t]+$/, "", n)
      gsub(/^[ \t]+|[ \t]+$/, "", rule)
      gsub(/^[ \t]+|[ \t]+$/, "", status)
      if (n ~ /^[0-9]+$/) printf "A%s\t%s\t%s\n", n, rule, status
    }' "$FAMILY"
}

# ---- the tools list in §7, which is the universe of candidate gates.
tools_list() {
  [ -f "$FAMILY" ] || return 0
  awk -F'|' '/^\| `tools\// { t = $2; gsub(/[ `\t]/, "", t); print t }' "$FAMILY"
}

gate_files() {                  # every file that could BE a gate
  find "$CLONE/tools" "$CLONE/harness" -maxdepth 1 -type f \
       \( -name '*.sh' -o -name '*.py' \) 2>/dev/null | LC_ALL=C sort
}

# ---- the tokens a law is recognised by: its durable home, tokenised.
home_tokens() {                 # id, home -> one token per line
  local id="$1" home="$2"
  case "$id" in A[0-9]*) printf '%s\n' "$id" "amendment ${id#A}" ;; esac
  # THE FULL DOTTED SECTION, not two levels.  Capping at two turned a law
  # homed at §3.4.1 into the token `§3.4` — which, once tok_regex appended a
  # boundary excluding a following '.', could NEVER match the citation it came
  # from, while matching every unrelated sibling that spells the two-level
  # form.  STMT-22 was credited 32 citations that belong to §3.4.
  #
  # No parent token is emitted.  A law homed at §3.4.1 is gated by a tool that
  # cites §3.4.1; crediting it for a §3.4 mention is the over-crediting this
  # boundary work exists to remove, and the strict reading is the one that can
  # be checked.
  printf '%s' "$home" | grep -oE '§[0-9]+(\.[0-9]+)*[a-z]?' | sort -u
  printf '%s' "$home" | grep -oE '(tools|harness)/[A-Za-z0-9_.-]+\.(sh|py)' | sort -u
  printf '%s' "$home" | grep -oE '[0-9]{4}-[0-9]{2}-[0-9]{2}-[a-z-]+-[0-9]+' | sort -u
}

# A TOKEN MUST MATCH AS A WHOLE TOKEN.  `grep -F "§9"` matches `§9.5`, `§9.7`
# and `§9.2`, so a law homed at §9 was credited to every tool that mentions any
# §9.x — seven tools for one law, including `ada_round_trip.py`.  That is the
# identifier law failing inside the instrument that measures enforcement, which
# is the third time this lane has met it (sites.sh's `.unsupportedDevice`,
# arms_of's first-hit-per-file, and now this).  Same fix as sites.sh: require a
# boundary, and let the direction of the error be stated rather than hidden.
tok_regex() {                   # token -> an ERE that matches it WHOLE
  printf '%s' "$1" | sed -e 's/[][\.*^$(){}?+|/]/\\&/g' -e 's/$/([^0-9.A-Za-z]|$)/'
}

cited_by() {                    # tokens on stdin -> the gate files for a law
  local toks f hit out=""
  toks="$(cat)"
  [ -n "$toks" ] || { echo ""; return 0; }
  # ONE regex per token, built ONCE.  Building it inside the file loop cost a
  # `sed` per token per file and doubled the run (50s -> 1m51s) — the tool that
  # prices enforcement has to be priced too, the same lesson sites.sh took.
  local res=""
  while IFS= read -r t; do
    [ -n "$t" ] || continue
    res="$res$(tok_regex "$t")
"
  done <<PRE
$toks
PRE
  # A law whose HOME IS A SCRIPT is gated BY IDENTITY, not by citation — that
  # file does not cite its own path, and the first version of this rule filed
  # every such law as NO GATE.  The register's own entries (`tools/triad.sh`
  # is the canonical wrapper) are exactly this shape.
  while IFS= read -r t; do
    case "$t" in
      tools/*|harness/*)
        [ -f "$CLONE/$t" ] && out="${out:+$out }$(basename "$t")" ;;
    esac
  done <<IDENT
$toks
IDENT
  for f in $(gate_files); do
    hit=0
    while IFS= read -r r; do
      [ -n "$r" ] || continue
      if grep -qE -- "$r" "$f" 2>/dev/null; then hit=1; break; fi
    done <<TOKS
$res
TOKS
    if [ "$hit" = "1" ]; then
      case " $out " in *" $(basename "$f") "*) ;; *) out="${out:+$out }$(basename "$f")" ;; esac
    fi
  done
  echo "$out"
}

ledger_citations() {            # tokens on stdin -> how many ledger LINES cite them
  local toks n=0 t
  toks="$(cat)"
  [ -d "$LEDGERS" ] || { echo 0; return 0; }
  while IFS= read -r t; do
    [ -n "$t" ] || continue
    n=$((n + $(grep -rhE -- "$(tok_regex "$t")" "$LEDGERS"/*.md 2>/dev/null | grep -c . || true)))
  done <<TOKS
$toks
TOKS
  echo "$n"
}

# --------------------------------------------------------------- self-test
if [ "$SELF_TEST" = "1" ]; then
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/laws-selftest.XXXXXX")" || die "no temp dir"
  trap 'rm -rf "$tmp"' EXIT
  ok=0; bad=0
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; \
            else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }

  fx="$tmp/fx"; mkdir -p "$fx/docs/backlog" "$fx/tools" "$fx/harness"
  cat > "$fx/docs/law-index.md" <<'MD'
# index
| id | hook | home |
| --- | --- | --- |
| MEAS-1 | a gated law | `docs/family-architecture.md §5.4` |
| MEAS-2 | an ungated law | `docs/family-architecture.md §9.9` |
| OPS-1 | a scripted law | `tools/gated.sh` |
| CLONE-1 | a ledger-famous ungated law | `docs/family-architecture.md §8.8` |
| NOTALAW | ignored | nowhere |
MD
  cat > "$fx/docs/family-architecture.md" <<'MD'
| # | rule | status |
| 1 | — | **LOST** |
| 9 | a FIFO ticket queue | **new** |
| 99 | an amendment nobody implemented | **new** |
| `tools/gated.sh` | does a thing | §5.4 |
MD
  printf 'set -u\n# implements §5.4 and A9\n' > "$fx/tools/gated.sh"
  printf 'set -u\n# cites nothing in particular\n' > "$fx/tools/other.sh"
  printf '## entry\nsee §9.9 here\nand §9.9 again\nand §9.9 a third time\n' > "$fx/docs/backlog/a.md"
  printf '## entry\n§8.8 once\n§9.9 a fourth time\n' > "$fx/docs/backlog/b.md"
  CLONE="$fx"; INDEX="$fx/docs/law-index.md"; FAMILY="$fx/docs/family-architecture.md"
  LEDGERS="$fx/docs/backlog"

  check "law rows are parsed"          "$(law_rows | grep -c .)" "4"
  check "  ...and a non-id row is skipped" "$(law_rows | grep -c NOTALAW)" "0"
  check "amendment rows are parsed"    "$(amendment_rows | grep -c .)" "3"
  check "the tools list is read"       "$(tools_list | tr '\n' ' ' | sed 's/ *$//')" "tools/gated.sh"

  check "a § home tokenises"           "$(home_tokens MEAS-1 'docs/family-architecture.md §5.4' | tr '\n' ' ' | sed 's/ *$//')" "§5.4"
  check "a script home tokenises"      "$(home_tokens OPS-1 'tools/gated.sh' | tr '\n' ' ' | sed 's/ *$//')" "tools/gated.sh"
  check "an amendment tokenises to A<n> AND prose" \
        "$(home_tokens A9 'x' | tr '\n' ' ' | sed 's/ *$//')" "A9 amendment 9"

  check "a cited law names its tool"   "$(home_tokens MEAS-1 '§5.4' | cited_by)" "gated.sh"
  check "an UNCITED law is NO GATE"    "$(home_tokens MEAS-2 '§9.9' | cited_by)" ""
  check "a law homed IN a script is cited" "$(home_tokens OPS-1 'tools/gated.sh' | cited_by)" "gated.sh"
  check "A9 is cited by the script"    "$(home_tokens A9 'x' | cited_by)" "gated.sh"
  check "A99 is not"                   "$(home_tokens A99 'x' | cited_by)" ""

  check "ledger citations are COUNTED" "$(home_tokens MEAS-2 '§9.9' | ledger_citations)" "4"
  check "  ...across ledger files"     "$(home_tokens CLONE-1 '§8.8' | ledger_citations)" "1"
  check "an uncited law counts zero"   "$(home_tokens MEAS-1 '§5.4' | ledger_citations)" "0"

  # The whole point: the NO GATE list ordered by MEASURED DEMAND.
  rank="$(for r in 'MEAS-2	§9.9' 'CLONE-1	§8.8'; do
            i="${r%%	*}"; h="${r##*	}"
            printf '%s %s\n' "$(home_tokens "$i" "$h" | ledger_citations)" "$i"
          done | sort -rn)"
  check "NO GATE sorts by citation count" "$(printf '%s' "$rank" | head -1)" "4 MEAS-2"
  check "  ...the less-cited one second"  "$(printf '%s' "$rank" | tail -1)" "1 CLONE-1"

  # ---- tokens match WHOLE, or a law homed at §9 is credited to every tool
  # that mentions §9.5.
  printf 'set -u\n# implements §9.5 and nothing else\n' > "$fx/tools/nine5.sh"
  check "a THREE-level section survives tokenising" \
        "$(home_tokens STMT-22 'docs/family-architecture.md §3.4.1' | tr '\n' ' ' | sed 's/ *$//')" "§3.4.1"
  check "  ...and is not truncated to its parent" \
        "$(home_tokens STMT-22 'docs/family-architecture.md §3.4.1' | grep -cx '§3.4')" "0"
  printf 'set -u\n# implements §3.4.1 exactly\n' > "$fx/tools/three.sh"
  check "  ...so it matches its OWN home"        "$(printf '§3.4.1\n' | cited_by | grep -c three)" "1"
  printf 'set -u\n# mentions only §3.4 here\n' > "$fx/tools/two.sh"
  check "  ...and a §3.4 tool does not credit it" "$(printf '§3.4.1\n' | cited_by | grep -c two)" "0"
  rm -f "$fx/tools/three.sh" "$fx/tools/two.sh"

  check "§9 does NOT match §9.5"        "$(printf '§9\n' | cited_by | grep -c nine5)" "0"
  check "§9.5 DOES match §9.5"          "$(printf '§9.5\n' | cited_by | grep -c nine5)" "1"
  printf 'set -u\n# implements 2026-08-22-qol-10\n' > "$fx/tools/q10.sh"
  check "a dated id does not match its longer sibling" \
        "$(printf '2026-08-22-qol-1\n' | cited_by | grep -c q10)" "0"
  rm -f "$fx/tools/nine5.sh" "$fx/tools/q10.sh"

  # ---- a law the index marks ungateable is not debt
  cat >> "$fx/docs/law-index.md" <<'MD'
| PROOF-99 | a law no script can check | `docs/family-architecture.md §9.9` — ungateable: cost is a judgement |
MD
  check "an ungateable row is recognised" \
        "$(law_rows | grep -c 'ungateable:')" "1"
  check "  ...and carries its reason"     \
        "$(law_rows | grep -c 'cost is a judgement')" "1"

  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

# -------------------------------------------------------------------- main
[ -f "$INDEX" ]  || die "no law index at '$INDEX'"
[ -f "$FAMILY" ] || die "no family doc at '$FAMILY'"

# A law the index marks `ungateable: <reason>` is not debt — it is a decided
# question, and re-surfacing it every audit is how a settled finding gets
# re-litigated.  PROOF-40 is the first.
UNGATEABLE="$({ law_rows; amendment_rows; } | grep -i 'ungateable:' || true)"
N_UNGATEABLE="$(printf '%s' "$UNGATEABLE" | grep -c . || true)"

ROWS="$(
  { law_rows; amendment_rows; } | while IFS="$(printf '\t')" read -r id hook home; do
      [ -n "$id" ] || continue
      case "$home" in *[Uu]ngateable:*) continue ;; esac
      toks="$(home_tokens "$id" "$home")"
      printf '%s\t%s\t%s\t%s\t%s\n' \
        "$(printf '%s' "$toks" | ledger_citations)" \
        "$id" "$(printf '%s' "$toks" | cited_by)" "$hook" "$home"
    done
)"

NLAW="$(printf '%s' "$ROWS" | grep -c . || true)"
GATED="$(printf '%s' "$ROWS" | awk -F'\t' '$3 != ""' | grep -c . || true)"
NOGATE="$(printf '%s' "$ROWS" | awk -F'\t' '$3 == ""' || true)"
NNO="$(printf '%s' "$NOGATE" | grep -c . || true)"

echo "laws.sh — $NLAW laws (index + register), $(tools_list | grep -c . || true) tools in §7's list"
echo "          measured at $(git -C "$CLONE" rev-parse --short HEAD 2>/dev/null || echo 'no git')"
echo
printf '  CITED BY A TOOL   %s\n' "$GATED"
printf '  UNGATEABLE        %s   (recorded with a reason; not debt)\n' "$N_UNGATEABLE"
printf '  NO GATE           %s   <- a LOWER BOUND: citation over-credits, so the\n' "$NNO"
printf '                        real unenforced set is LARGER than this.\n'
echo
printf '  The %s most-cited NO GATE laws — the next inch, by measured demand:\n' "$TOP"
printf '%s\n' "$NOGATE" | grep -v '^$' | sort -rn \
  | head -n "$TOP" \
  | awk -F'\t' '{ printf "    %4s  %-9s %-58s %s\n", $1, $2, substr($4, 1, 58), $5 }'
echo
# THE UNIT BEING RANKED IS THE HOME, NOT THE LAW.  Laws that share a § share
# every token, so they share a count and tie — which is information, not noise:
# it says the SECTION is what the ledgers keep reaching for.  Grouping makes
# that legible instead of looking like five separate findings.
echo "  ...and the same list BY HOME, which is the unit the count actually ranks:"
printf '%s\n' "$NOGATE" | grep -v '^$' \
  | awk -F'\t' '{ key = $5; c[key] = $1; n[key]++; ids[key] = ids[key] " " $2 }
      END { for (k in c) printf "%s\t%s\t%s\t%s\n", c[k], n[k], k, ids[k] }' \
  | sort -rn | head -n "$TOP" \
  | awk -F'\t' '{ printf "    %4s citations  %2s ungated law(s)  %s\n              %s\n", $1, $2, $3, $4 }'
echo
if [ "$VERBOSE" = "1" ]; then
  echo "  EVERY law, with the tools citing its home:"
  printf '%s\n' "$ROWS" | grep -v '^$' | sort -rn \
    | awk -F'\t' '{ printf "    %4s  %-9s %-34s %s\n", $1, $2, ($3 == "" ? "NO GATE" : $3), substr($4, 1, 52) }'
  echo
fi
if [ "$N_UNGATEABLE" != "0" ]; then
  echo "  RECORDED UNGATEABLE:"
  printf '%s\n' "$UNGATEABLE" | awk -F'\t' '{ printf "    %-9s %s\n", $1, substr($3, 1, 92) }'
  echo
fi
echo "  Citation is a PROXY for enforcement and it over-credits: a tool that"
echo "  mentions a law in a comment is counted. Read this as a bound, never as"
echo "  coverage — §5.4a on the instrument that audits the instruments."
