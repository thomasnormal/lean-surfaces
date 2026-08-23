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
#   tools/laws.sh --budget 30     # seconds; PARTIAL past it, counts are FLOORS
#   tools/laws.sh --gate-set      # §5.4b: what each gate is POINTED AT, + orphans
#   tools/laws.sh --self-test
#
# ZERO Lean execution.  Safe outside a tenure (A11).

set -u

CLONE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOP=10
VERBOSE=0
SELF_TEST=0
GATE_SET=0
# A TOOL THAT PRICES ENFORCEMENT MUST ITSELF BE PRICED — and a two-minute audit
# instrument stops being run, which is how audit instruments die.
BUDGET="${LS_LAWS_BUDGET:-120}"
PROGRESS_EVERY="${LS_LAWS_PROGRESS:-50}"

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
die()   { echo "laws.sh: $*" >&2; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --dir)       CLONE="${2:-}"; shift 2 ;;
    --top)       TOP="${2:-}"; shift 2 ;;
    --verbose)   VERBOSE=1; shift ;;
    --budget)    BUDGET="${2:-}"; shift 2 ;;
    --gate-set)  GATE_SET=1; shift ;;
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
  # ONE awk for all three shapes.  Profiled first (the stripper-vs-spawn
  # precedent): the ROWS loop was everything, the same work over a pre-read
  # file took 13s, and the difference was ~8000 PROCESS SPAWNS whose latency
  # scales with machine load — so this instrument's runtime was a function of
  # OTHER LANES' builds (54s -> 83s -> 115s -> past 120s as load grew).  A
  # number that moves with somebody else's load is §5.4a's own subject.
  printf '%s' "$home" | awk '
    function emit(t) { if (!(t in seen)) { seen[t] = 1; print t } }
    {
      line = $0
      while (match(line, /§[0-9]+(\.[0-9]+)*[a-z]?/)) {
        emit(substr(line, RSTART, RLENGTH)); line = substr(line, RSTART + RLENGTH)
      }
      line = $0
      while (match(line, /(tools|harness)\/[A-Za-z0-9_.-]+\.(sh|py)/)) {
        emit(substr(line, RSTART, RLENGTH)); line = substr(line, RSTART + RLENGTH)
      }
      line = $0
      while (match(line, /[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]-[a-z-]+-[0-9]+/)) {
        emit(substr(line, RSTART, RLENGTH)); line = substr(line, RSTART + RLENGTH)
      }
    }'
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

# A FIXTURE IS NOT ENFORCEMENT.  Adding a self-test row that names `A15` made
# `laws.sh` credit ITSELF as A15's gate — the instrument that measures
# enforcement counting its own test data as enforcement, which is the same
# self-selection defect the 2026-08-23 audit found elsewhere and which my own
# fix re-created within the hour.  The self-test region is stripped before any
# attribution grep: every tool here opens one recognisably and closes it with
# the "self-test: $ok ok" summary.
# CACHED PER FILE, not per (law x file).  Stripping inside the attribution loop
# ran an awk for every law against every tool — ~6000 spawns, and the run went
# past two minutes.  The stripped text is the same for every law, so it is
# computed once.  (A tool that prices enforcement has to be priced too, for the
# third time in this file's history.)
ENF_CACHE=""
enforcement_cache_init() {
  ENF_CACHE="$(mktemp -d "${TMPDIR:-/tmp}/laws-enf.XXXXXX")" || return 1
  local f
  local f
  for f in $(gate_files); do
    enforcement_text "$f" > "$ENF_CACHE/${f##*/}" 2>/dev/null
  done
  # ONE corpus of every tool's enforcement text.  Most laws are cited by
  # NOTHING, and asking 18 files one at a time is 18 greps to learn that; the
  # corpus answers it in one, and only a HIT pays for the per-file loop.
  cat "$ENF_CACHE"/* > "$ENF_CACHE/.all" 2>/dev/null
  cat "$LEDGERS"/*.md > "$ENF_CACHE/.ledger" 2>/dev/null
}
enforcement_cache_clear() { [ -n "$ENF_CACHE" ] && rm -rf "$ENF_CACHE"; ENF_CACHE=""; }

enforcement_text() {            # file -> its text MINUS the self-test region
  awk '
    /SELF_TEST" = "1"|"--self-test"\)|= "--self-test"/ { inst = 1 }
    inst && /self-test: \$ok ok/ { inst = 0; next }
    !inst { print }' "$1"
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
  # THE CORPUS, AFTER IDENTITY.  Placed before it, this returned "" for a law
  # whose home IS a script and which nothing cites — silently dropping the
  # identity attribution that MEAS-60 and OPS-46 depend on.  The self-test did
  # not catch it, because it never initialises the cache: the fast path was
  # untested, which is how a fast path usually breaks.
  if [ -n "$ENF_CACHE" ] && [ -r "$ENF_CACHE/.all" ]; then
    local any=0
    while IFS= read -r r; do
      [ -n "$r" ] || continue
      if grep -qE -- "$r" "$ENF_CACHE/.all" 2>/dev/null; then any=1; break; fi
    done <<ANY
$res
ANY
    if [ "$any" = "0" ]; then
      # Identity attribution can still apply even when nothing cites it.
      [ -n "$out" ] && { echo "$out"; return 0; }
      echo ""; return 0
    fi
  fi

  for f in $(gate_files); do
    hit=0
    while IFS= read -r r; do
      [ -n "$r" ] || continue
      # The cache when it exists, the live strip otherwise — so the function
      # is still correct when called directly (the self-test does).
      if [ -n "$ENF_CACHE" ] && [ -r "$ENF_CACHE/${f##*/}" ]; then
        if grep -qE -- "$r" "$ENF_CACHE/${f##*/}" 2>/dev/null; then hit=1; break; fi
      elif enforcement_text "$f" | grep -qE -- "$r" 2>/dev/null; then hit=1; break; fi
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
  local toks corpus tmpc=""
  toks="$(cat)"
  [ -d "$LEDGERS" ] || { echo 0; return 0; }
  [ -n "$toks" ] || { echo 0; return 0; }
  # ONE pass for ALL of a law's tokens over a corpus concatenated once, instead
  # of a recursive grep per token over fifteen files.  THE BOUNDARY IS KEPT —
  # awk escapes each token and anchors it, because dropping that is how `§9`
  # came to match `§9.5`.
  if [ -n "$ENF_CACHE" ] && [ -r "$ENF_CACHE/.ledger" ]; then
    corpus="$ENF_CACHE/.ledger"
  else
    tmpc="$(mktemp "${TMPDIR:-/tmp}/laws-ledger.XXXXXX")" || { echo 0; return 0; }
    cat "$LEDGERS"/*.md > "$tmpc" 2>/dev/null
    corpus="$tmpc"
  fi
  printf '%s\n' "$toks" | awk -v C="$corpus" '
    function esc(t,   o) { o = t; gsub(/[][(){}.*+?^$|\\\/]/, "\\\\&", o); return o }
    NF { pats[++n] = "(^|[^0-9.A-Za-z])" esc($0) "([^0-9.A-Za-z]|$)" }
    END {
      while ((getline line < C) > 0)
        for (i = 1; i <= n; i++)
          if (line ~ pats[i]) { hits++; break }
      print hits + 0
    }'
  [ -n "$tmpc" ] && rm -f "$tmpc"
  return 0
}

# ============================ §5.4b GATE TOPOLOGY ============================
# "A gate set is a set of POINTERS, and coverage is what they point AT."  The
# lane that shipped a rotted transcription was not running without gates: it
# had FOUR, all green throughout, and none was pointed at the claim that had
# rotted.  Four gates, four elsewheres.
#
# > ENUMERATION READS DECLARATIONS.  A gate whose target is computed at
# > runtime — a variable command, a glob built from a flag, a step that shells
# > out to something this cannot see — is listed UNRESOLVED.  It is NOT
# > guessed, because a guessed pointer is worse than a missing one: it makes a
# > claim look covered.  And §5.4b's own rule applies to this tool: a gate set
# > is audited by ENUMERATION, never by execution, so nothing here runs a gate.
#
# The pointer of a gate is taken from its DECLARATION and, where the gate
# states its own scope, from the gate's own words — "a gate that documents its
# scope has already done half the enumeration".

# What each gate names, as a file-kind pointer: the extensions and directories
# its declaration mentions.  Anything else it may touch is not declared.
gate_pointer() {                # command-text -> the kinds/paths it names
  printf '%s' "$1" | awk '
    function emit(t) { if (!(t in s)) { s[t] = 1; printf "%s ", t } }
    {
      line = $0
      while (match(line, /\*\.[A-Za-z0-9]+|[A-Za-z0-9_.\/-]+\.(lean|md|py|json|sh|cir|va|sv)/)) {
        emit(substr(line, RSTART, RLENGTH)); line = substr(line, RSTART + RLENGTH)
      }
    }
    END { print "" }'
}

# A gate whose declared verdict is "expected to fail" is the weakest row in any
# set: its verdict is INVARIANT under everything else the artifact says
# (MEAS-68).  Detected from the declaration's own words.
gate_is_expected_fail() {
  case "$1" in
    *xpected*rror*|*xpected*fail*|*EXPECTED\ TO\ ERROR*|*must\ fail*) return 0 ;;
  esac
  return 1
}

# The declared gate sets: ci.sh's steps, and the triad's class floors.  Both
# are DECLARATIONS; neither is executed.
gate_rows() {                   # -> "set<TAB>name<TAB>pointer<TAB>flag<TAB>decl"
  local ci="$CLONE/tools/ci.sh" tr="$CLONE/tools/triad.sh"
  if [ -r "$ci" ]; then
    # ANCHORED AT COLUMN 0, THIS MISSED EVERY WRAPPED GATE.  `lake-build` — the
    # most consequential row in the file — is declared INSIDE lake_build_step()
    # because it is host-gated, so it is indented, so the enumeration omitted
    # it: an auditor reading this list would conclude CI does not gate the
    # build.  The same shape hid the sv round-trip gate.  Leading whitespace is
    # indentation, not evidence.
    #
    # But a FIXTURE IS NOT ENFORCEMENT (the rule enforcement_text already
    # applies to citations): --verify-guards drives these same functions with
    # stubs, so its rows must not be enumerated as gates.  That region is cut
    # here rather than in enforcement_text, which keys on the self-test
    # spelling and whose citation counts are not this inch's to move.
    awk 'BEGIN { fixture = 0 }
         /VERIFY_GUARDS" = "1"/ { fixture = 1 }
         fixture && /verify-guards: \$vok ok/ { fixture = 0; next }
         fixture { next }
         /^[ \t]*(step|maybe|maybe_lean) +"/ {
           n = $0; sub(/^[ \t]*[a-z_]+ +"/, "", n); sub(/".*/, "", n)
           d = $0; sub(/^[ \t]*[a-z_]+ +"[^"]*" */, "", d)
           printf "ci.sh\t%s\t%s\n", n, d
         }' "$ci"
  fi
  if [ -r "$tr" ]; then
    awk '/^gate_floor\(\)/,/^}/ {
           if ($0 ~ /echo .python3/) {
             c = $0; sub(/^[^\x27]*\x27/, "", c); sub(/\x27.*$/, "", c)
             k = $0; sub(/^ *\)? */, "", k); sub(/\).*/, "", k)
             printf "triad-floor\t%s\t%s\n", k, c
           }
         }' "$tr"
  fi
}

# THE ORPHAN LIST.  A file KIND present in the tree that no gate's declared
# pointer names is ungated, however green the neighbourhood.  Kind is the unit
# because the incident's claim was a KIND — a transcription inside a `.lean`
# COMMENT — that every gate's pointer missed.
tree_kinds() {
  find "$CLONE" -type f -name '*.*' 2>/dev/null \
    | grep -vE '/\.lake/|/\.git/|/node_modules/' \
    | sed 's/.*\.//' | sort | uniq -c | sort -rn \
    | awk '$1 >= 5 { print $2 }'
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

  # THE CACHED FAST PATH, exercised — it is the one the live run uses.
  enforcement_cache_init
  check "cached: a cited law still names its tool" "$(printf '§5.4\n' | cited_by)" "gated.sh"
  check "cached: an uncited law is still NO GATE"  "$(printf '§9.9\n' | cited_by)" ""
  check "cached: IDENTITY survives the corpus short-circuit" \
        "$(printf 'tools/gated.sh\n' | cited_by)" "gated.sh"
  enforcement_cache_clear

  check "a cited law names its tool"   "$(home_tokens MEAS-1 '§5.4' | cited_by)" "gated.sh"
  check "an UNCITED law is NO GATE"    "$(home_tokens MEAS-2 '§9.9' | cited_by)" ""
  check "a law homed IN a script is cited" "$(home_tokens OPS-1 'tools/gated.sh' | cited_by)" "gated.sh"
  check "A9 is cited by the script"    "$(home_tokens A9 'x' | cited_by)" "gated.sh"
  check "A99 is not"                   "$(home_tokens A99 'x' | cited_by)" ""

  # THE REWRITE'S OWN RISK: counting by `index()` would have dropped the
  # boundary, which is exactly how §9 came to match §9.5.
  printf '## e\nsee §9.5 twice\n§9.5 again\n' > "$fx/docs/backlog/c.md"
  check "ledger counting keeps the BOUNDARY" "$(printf '§9\n' | ledger_citations)" "0"
  check "  ...while the exact section counts" "$(printf '§9.5\n' | ledger_citations)" "2"
  rm -f "$fx/docs/backlog/c.md"

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
  # An amendment's third column is its STATUS; the display must not print it
  # where a home belongs, and the TOKENS must not gain §7.1a from the fix.
  # A tool must not gate a law it only NAMES IN ITS OWN TEST.
  printf 'set -u\n# real: implements §9.9\nif [ "$SELF_TEST" = "1" ]; then\n  check "x" "$(f A77)" "y"\n  echo "self-test: $ok ok, $bad failed"\nfi\n' > "$fx/tools/fixture.sh"
  check "a token in the SELF-TEST is not enforcement" "$(printf 'A77\n' | cited_by | grep -c fixture)" "0"
  check "  ...while one outside it still is"          "$(printf '§9.9\n' | cited_by | grep -c fixture)" "1"
  rm -f "$fx/tools/fixture.sh"

  check "an amendment keeps its id tokens only" \
        "$(home_tokens A15 '**new** (superseded by 16)' | tr '\n' ' ' | sed 's/ *$//')" "A15 amendment 15"
  check "  ...and gains no section token"       \
        "$(home_tokens A15 '**new** (superseded by 16)' | grep -c '§')" "0"

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

  # ---- §5.4b GATE TOPOLOGY, calibrated on the incident's own table: four
  # gates, four elsewheres, all green, and the rotted claim inside a .lean
  # COMMENT that none of them pointed at.
  gs="$tmp/gs"; mkdir -p "$gs/tools" "$gs/docs" "$gs/LeanModels"
  cat > "$gs/tools/ci.sh" <<'CISH'
step  "docs"        python3 tools/docs_check.py
step  "probe"       lake env lean probes/probe_es_unblock.lean   # EXPECTED TO ERROR
step  "computed"    run_the_thing
wrapped_step() {
  step "wrapped" python3 tools/wrapped_gate.py
}
if [ "$VERIFY_GUARDS" = "1" ]; then
  step "fixture-row" python3 tools/never_a_gate.py
  echo "verify-guards: $vok ok, $vbad failed"
fi
CISH
  printf '# Scans README.md, AGENTS.md, and docs/**/*.md for marked blocks.\n' \
    > "$gs/tools/docs_check.py"
  i=1; while [ "$i" -le 6 ]; do printf -- '-- a comment\n' > "$gs/LeanModels/M$i.lean"; i=$((i+1)); done
  i=1; while [ "$i" -le 6 ]; do printf '# d\n' > "$gs/docs/d$i.md"; i=$((i+1)); done
  saved_cl="$CLONE"; CLONE="$gs"

  check "gates are read from DECLARATIONS"  "$(gate_rows | grep -c .)" "4"
  # A HOST-GATED gate lives inside a function, so it is indented; anchoring at
  # column 0 dropped `lake-build` and 27 others from the enumeration.
  check "an INDENTED gate is still a gate"  "$(gate_rows | grep -c 'wrapped')" "1"
  # ...but a fixture that DRIVES the gates is not one of them (the rule
  # enforcement_text applies to citations, applied here to declarations).
  check "  ...a --verify-guards row is not" "$(gate_rows | grep -c 'fixture-row')" "0"
  check "a declared script is a pointer"    "$(gate_pointer 'python3 tools/docs_check.py' | tr -d ' ')" "tools/docs_check.py"
  check "the gate's OWN words extend it"    "$(gate_pointer "$(cat "$gs/tools/docs_check.py")" | grep -c 'README.md')" "1"
  check "an EXPECTED-TO-ERROR gate is the weakest row" \
        "$(gate_is_expected_fail 'lake env lean probes/p.lean   # EXPECTED TO ERROR' && echo weak)" "weak"
  check "  ...and an ordinary gate is not"  "$(gate_is_expected_fail 'python3 tools/docs_check.py' && echo weak)" ""
  check "a runtime target is UNRESOLVED, not guessed" \
        "$(gate_pointer 'run_the_thing' | tr -d ' ')" ""
  check "the incident's shape: .lean is a tree kind" \
        "$(tree_kinds | grep -c '^lean$')" "1"
  check "  ...and so is .md"                "$(tree_kinds | grep -c '^md$')" "1"
  CLONE="$saved_cl"

  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

# -------------------------------------------------------------------- main
if [ "$GATE_SET" = "1" ]; then
  echo "laws.sh --gate-set — §5.4b: a gate set is a set of POINTERS"
  echo "                    measured at $(git -C "$CLONE" rev-parse --short HEAD 2>/dev/null || echo 'no git')"
  echo
  echo "  ENUMERATION READS DECLARATIONS.  A gate whose target is computed at"
  echo "  runtime is listed UNRESOLVED, never guessed — a guessed pointer is"
  echo "  worse than a missing one, because it makes a claim look covered."
  echo "  Nothing here is executed: a gate set is audited by ENUMERATION."
  echo
  printf '  %-12s %-30s %-30s %s\n' SET GATE 'POINTED AT (declared)' FLAG
  printf '  %-12s %-30s %-30s %s\n' ------------ ------------------------------ ------------------------------ ----
  n_unres=0; n_weak=0; n_gates=0
  covered=""
  # THREE fields, not five with empty placeholders: TAB is whitespace, so bash
  # COLLAPSES consecutive tabs into one delimiter and the declaration landed in
  # the wrong variable — every gate then read UNRESOLVED, which made every file
  # kind look orphaned.  A padding field you cannot see is a padding field that
  # is not there.
  while IFS="$(printf '\t')" read -r set name decl; do
    [ -n "$name" ] || continue
    n_gates=$((n_gates + 1))
    ptr="$(gate_pointer "$decl")"
    # AND THE GATE'S OWN WORDS.  §5.4b: "a gate that documents its scope has
    # already done half the enumeration."  A step declared as
    # `python3 tools/docs_check.py` names only the script; the SCOPE is in that
    # script's header ("Scans README.md, AGENTS.md, and docs/**/*.md"), and
    # without reading it `.md` looked orphaned while docs_check was pointed
    # squarely at it.
    for tgt in $ptr; do
      case "$tgt" in
        *.sh|*.py)
          [ -r "$CLONE/$tgt" ] && ptr="$ptr $(head -40 "$CLONE/$tgt" | gate_pointer "$(cat)" 2>/dev/null)" ;;
      esac
    done
    ptr="$(printf '%s' "$ptr" | tr ' ' '\n' | sort -u | tr '\n' ' ' | sed 's/ *$//')"
    flag=""
    if gate_is_expected_fail "$decl"; then flag="WEAKEST(MEAS-68)"; n_weak=$((n_weak + 1)); fi
    if [ -z "$ptr" ]; then ptr="UNRESOLVED — computed at runtime"; n_unres=$((n_unres + 1))
    else covered="$covered $ptr"; fi
    printf '  %-12s %-30s %-30s %s\n' "$set" "$(printf '%s' "$name" | cut -c1-30)" "$(printf '%s' "$ptr" | cut -c1-30)" "$flag"
  done <<GATES
$(gate_rows)
GATES
  echo
  printf '  %s gate(s) declared; %s UNRESOLVED; %s expected-to-fail\n' "$n_gates" "$n_unres" "$n_weak"
  echo
  echo "  ORPHAN KINDS — present in the tree, named by NO gate's declared pointer:"
  orph=0
  for k in $(tree_kinds); do
    case " $covered " in
      *".$k"*) ;;
      *) printf '    .%-8s  no declared pointer names it\n' "$k"; orph=$((orph + 1)) ;;
    esac
  done
  [ "$orph" = "0" ] && echo "    (none)"
  echo
  echo "  A KIND is the unit because the incident's rotted claim WAS a kind: a"
  echo "  transcription inside a .lean COMMENT, which docs_check (.md only) and"
  echo "  two probes (their own rows only) all pointed elsewhere from.  Four"
  echo "  gates, four elsewheres, all green.  An orphan here is not a defect —"
  echo "  it is a claim nobody has pointed a gate at."
  exit 0
fi

[ -f "$INDEX" ]  || die "no law index at '$INDEX'"
[ -f "$FAMILY" ] || die "no family doc at '$FAMILY'"

# A law the index marks `ungateable: <reason>` is not debt — it is a decided
# question, and re-surfacing it every audit is how a settled finding gets
# re-litigated.  PROOF-40 is the first.
UNGATEABLE="$({ law_rows; amendment_rows; } | grep -i 'ungateable:' || true)"
N_UNGATEABLE="$(printf '%s' "$UNGATEABLE" | grep -c . || true)"

enforcement_cache_init
ROWS="$(
  started="$(date +%s)"; scanned=0
  { law_rows; amendment_rows; } | while IFS="$(printf '\t')" read -r id hook home; do
      [ -n "$id" ] || continue
      case "$home" in *[Uu]ngateable:*) continue ;; esac
      scanned=$((scanned + 1))
      [ $((scanned % PROGRESS_EVERY)) = 0 ] && printf '  law %s...\r' "$scanned" >&2
      if [ $(( $(date +%s) - started )) -ge "$BUDGET" ]; then
        # The subshell cannot set a variable the parent will read, so the
        # verdict is left as a FILE — the same reason triad.sh's guard writes
        # its pid rather than exporting it.
        printf 'stopped after %ss at law %s\n' "$BUDGET" "$scanned" > "$ENF_CACHE/.partial"
        break
      fi
      toks="$(home_tokens "$id" "$home")"
      printf '%s\t%s\t%s\t%s\t%s\n' \
        "$(printf '%s' "$toks" | ledger_citations)" \
        "$id" "$(printf '%s' "$toks" | cited_by)" "$hook" "$home"
    done
)"

LAWS_PARTIAL=""
[ -n "$ENF_CACHE" ] && [ -r "$ENF_CACHE/.partial" ] && LAWS_PARTIAL="$(cat "$ENF_CACHE/.partial")"
enforcement_cache_clear
NLAW="$(printf '%s' "$ROWS" | grep -c . || true)"
GATED="$(printf '%s' "$ROWS" | awk -F'\t' '$3 != ""' | grep -c . || true)"
NOGATE="$(printf '%s' "$ROWS" | awk -F'\t' '$3 == ""' || true)"
NNO="$(printf '%s' "$NOGATE" | grep -c . || true)"

echo "laws.sh — $NLAW laws (index + register), $(tools_list | grep -c . || true) tools in §7's list"
echo "          measured at $(git -C "$CLONE" rev-parse --short HEAD 2>/dev/null || echo 'no git')"
echo
if [ -n "$LAWS_PARTIAL" ]; then
  echo "  PARTIAL — $LAWS_PARTIAL.  Every count below is a FLOOR, not a total."
  echo "            Raise --budget and re-run before quoting any of it."
fi
printf '  CITED BY A TOOL   %s\n' "$GATED"
printf '  UNGATEABLE        %s   (recorded with a reason; not debt)\n' "$N_UNGATEABLE"
printf '  NO GATE           %s   <- a LOWER BOUND: citation over-credits, so the\n' "$NNO"
printf '                        real unenforced set is LARGER than this.\n'
echo
printf '  The %s most-cited NO GATE laws — the next inch, by measured demand:\n' "$TOP"
printf '%s\n' "$NOGATE" | grep -v '^$' | sort -rn \
  | head -n "$TOP" \
  | awk -F'\t' '{ home = ($2 ~ /^A[0-9]+$/) \
        ? "docs/family-architecture.md §7.1a register — " $5 : $5
      printf "    %4s  %-9s %-58s %s\n", $1, $2, substr($4, 1, 58), substr(home, 1, 76) }'
echo
# THE UNIT BEING RANKED IS THE HOME, NOT THE LAW.  Laws that share a § share
# every token, so they share a count and tie — which is information, not noise:
# it says the SECTION is what the ledgers keep reaching for.  Grouping makes
# that legible instead of looking like five separate findings.
echo "  ...and the same list BY HOME, which is the unit the count actually ranks:"
printf '%s\n' "$NOGATE" | grep -v '^$' \
  | awk -F'\t' '{ key = ($2 ~ /^A[0-9]+$/) \
        ? "docs/family-architecture.md §7.1a register" : $5
      c[key] = $1; n[key]++; ids[key] = ids[key] " " $2 }
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
