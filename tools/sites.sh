#!/usr/bin/env bash
# tools/sites.sh — price a constructor change by the sites that DESTRUCTURE it.
#
# WHY THIS FILE EXISTS.  Three lanes priced one constructor change three
# different wrong ways in a week, and the family doc §5.4a records the
# calibration — five units on ONE change:
#
#   direct importers of the module ......  2   not a bound at all
#   transitive reachers ................ 128   true, and useless
#   sites that DESTRUCTURE it ..........  11   THE RIGHT UNIT (upper bound)
#   actually broken ....................   1   what it cost
#   build-reported .....................   6   five #guards from ONE cause
#
# > The blast radius of a constructor change is bounded by the sites that
# > DESTRUCTURE it.  Grep the PATTERN POSITION, not imports, and not the
# > API's identifiers.
#
# And the law was amended, because the naive grep MIS-COUNTS IN BOTH
# DIRECTIONS:
#
#   * `.error (.unsupported` returns ZERO in a tier that moved refusal out of
#     the error channel into `Halt` — an UNDER-count that reads as "no work",
#     which is the worst direction;
#   * a bare `.unsupported` OVER-counts — this tree has 8 prefix-collision
#     names (`.unsupportedDevice`, `.unsupportedConstruct`, …) and three
#     unrelated types in `LeanModels/C/Ast.lean` sharing the constructor name.
#
# > The pattern position is the CONSTRUCTOR OF THE TYPE BEING CHANGED,
# > WHEREVER THAT TYPE RIDES.  Name the type first, then grep its
# > constructor's pattern.
#
# So this tool takes the TYPE, finds where that type rides (the error channel,
# `Halt`/`Loud` directly, a tier wrapper, or a qualified spelling), and reports
# THREE buckets: CONSTRUCT sites, DESTRUCTURE sites, and the LOOK-ALIKES it
# excluded WITH THE REASON — because an exclusion nobody can audit is just a
# smaller wrong number.
#
# USAGE
#   tools/sites.sh <Type> <ctor>              # e.g. sites.sh Outcome unsupported
#   tools/sites.sh <Type> <ctor> --channel 'foo (\.'   # add a tier wrapper
#   tools/sites.sh --arms <fn>                # how many arms does it destructure?
#   tools/sites.sh <Type> <ctor> --budget 30  # seconds; PARTIAL past it
#   tools/sites.sh --self-test
#
# ZERO Lean execution: this greps text.  Safe outside a tenure (A11).

set -u

CLONE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TYPE=""; CTOR=""; EXTRA_CHANNELS=""; SELF_TEST=0; VERBOSE=0
ARMS_FN=""
BUDGET="${LS_SITES_BUDGET:-60}"      # seconds; a tool that prices must be priced
PROGRESS_EVERY="${LS_SITES_PROGRESS:-40}"

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
die()   { echo "sites.sh: $*" >&2; exit 2; }

. "$(dirname "${BASH_SOURCE[0]}")/argv.sh"   # the value-flag guard (a flag written last used to SPIN)
while [ $# -gt 0 ]; do
  case "$1" in
    --dir)       need_val "$#" "$1"; CLONE="$2"; shift 2 ;;
    --channel)   need_val "$#" "$1"; EXTRA_CHANNELS="${EXTRA_CHANNELS}$2
"; shift 2 ;;
    --verbose)   VERBOSE=1; shift ;;
    --arms)      need_val "$#" "$1"; ARMS_FN="$2"; shift 2 ;;
    --budget)    need_val "$#" "$1"; BUDGET="$2"; shift 2 ;;
    --self-test) SELF_TEST=1; shift ;;
    -h|--help)   usage ;;
    -*)          die "unknown argument '$1'" ;;
    *)           if [ -z "$TYPE" ]; then TYPE="$1"; else CTOR="$1"; fi; shift ;;
  esac
done

# ---------------------------------------------------------------- helpers
# LEAN ONLY, and the filter is the point rather than an accident: every
# language lane vendors a source fixture beside its model (`rung1.go`,
# `sunfish.json`), and reading a `.go` file as Lean would count a Go
# constructor as one of ours — a confident wrong number, which is the
# failure this whole tool exists to prevent.
lean_files() { find "$CLONE" -name '*.lean' -type f 2>/dev/null | LC_ALL=C sort; }

# WHICH TYPES DECLARE THIS CONSTRUCTOR.  This is what makes a look-alike
# NAMEABLE instead of merely excluded: the same constructor name on a
# different inductive is the exact defect the identifier law re-imports.
declaring_types() {             # ctor -> "file:line<TAB>Type"
  local f
  for f in $(lean_files); do
    awk -v C="$CTOR" -v FN="${f#"$CLONE"/}" '
      /^[ \t]*(inductive|structure)[ \t]+/ {
        t = $0
        sub(/^[ \t]*(inductive|structure)[ \t]+/, "", t)
        sub(/[ \t(:{<].*$/, "", t)
        cur = t; next
      }
      # LEAVING the inductive block ends the declaration run.  Without this,
      # a `| unsupported` MATCH ARM inside a later `def` is attributed to the
      # last inductive seen — the live tree reported `Run` five times and
      # `Hands` three, which is the identifier law failing inside the tool
      # that exists to prevent it.
      /^(def|theorem|lemma|abbrev|instance|example|end|namespace|section|open|@\[|#|\/-)/ { cur = ""; next }
      /^[ \t]*\|[ \t]*[A-Za-z_]/ {
        c = $0
        sub(/^[ \t]*\|[ \t]*/, "", c)
        sub(/[ \t(:{].*$/, "", c)
        if (c == C && cur != "") printf "%s:%d\t%s\n", FN, NR, cur
      }' "$f"
  done
}

# The positions the constructor rides in.  Defaults cover the error channel,
# Halt/Loud directly, and the qualified spelling; --channel adds a tier's own
# wrapper, because a grep hard-coded to one channel has a tier's design baked
# into it.
channels() {
  printf '%s\n' \
    "\\.error \\(\\.$CTOR" \
    "\\.halt \\(\\.$CTOR" \
    "\\.loud \\(\\.$CTOR" \
    "Halt\\.$CTOR" \
    "Loud\\.$CTOR" \
    "$TYPE\\.$CTOR"
  printf '%s' "$EXTRA_CHANNELS" | grep -v '^$' || true
}

# A hit is CONSTRUCT or DESTRUCTURE by POSITION, not by keyword: in a match
# arm the constructor stands to the LEFT of the arrow; in a construction it
# stands to the right of `=>`, `:=` or `return`.  A `#guard`/`rfl`/`decide`
# line pins the SHAPE, so it destructures even without an arrow.
classify_hit() {                # line -> construct | destructure | both
  local line="$1" left right pat="\\.$CTOR([^A-Za-z0-9_']|\$)"
  case "$line" in
    *'#guard'*|*'#eval'*) echo destructure; return 0 ;;
  esac
  if printf '%s' "$line" | grep -q '=>'; then
    left="${line%%=>*}"; right="${line#*=>}"
    local l=0 r=0
    printf '%s' "$left"  | grep -qE "$pat" && l=1
    printf '%s' "$right" | grep -qE "$pat" && r=1
    if [ "$l" = "1" ] && [ "$r" = "1" ]; then echo both; return 0; fi
    if [ "$l" = "1" ]; then echo destructure; return 0; fi
    echo construct; return 0
  fi
  case "$line" in
    *'| .'*|*'|.'*) echo destructure; return 0 ;;
  esac
  echo construct
}

# COMMENTS ARE NOT SITES.  The first live run counted six doc-comment
# mentions as CONSTRUCT sites — prose about `Halt.unsupported` inside `/-- -/`,
# and a markdown table in `Core/Outcome.lean`.  A pricing tool that counts
# prose over-states the work, which is the same class of defect as counting
# identifiers.  `harness/wasm_sorry_census.py` already had to learn this
# (docs/backlog/wasm.md 2026-08-22-wasm-1): strip Lean comments BEFORE looking
# for the token, and report the delta as the finding.
#
# Lean block comments NEST, so this tracks depth rather than matching a pair.
# The approximation is `--` inside a string literal; it errs toward excluding,
# which is stated rather than hidden because for a BOUND the dangerous
# direction is under-counting.
code_hits() {                   # file, ere -> "lineno:code" for non-comment hits
  awk -v RE="$2" '
    {
      line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        two = substr(line, i, 2)
        if (depth == 0 && two == "--") break
        if (two == "/-") { depth++; i += 2; continue }
        if (two == "-/") { if (depth > 0) depth--; i += 2; continue }
        if (depth == 0) out = out substr(line, i, 1)
        i++
      }
      if (out ~ RE) printf "%d:%s\n", NR, out
    }' "$1"
}

# A TOOL THAT PRICES A CHANGE MUST ITSELF BE PRICED.  A pricing run that never
# returns is worse than a slow one, because the lane cannot tell "expensive"
# from "hung" — and it then gets killed, which yields NO number at all.  So the
# scan carries a time budget and, past it, stops and says PARTIAL.  A partial
# answer that SAYS SO beats a silent truncation, which is the whole of §5.4a.
PARTIAL=""
scan_sites() {
  local f rel line n chan hits pat started now scanned=0 total
  SITES=""; LOOKALIKES=""
  pat="$(channels | paste -sd'|' -)"
  started="$(date +%s)"
  total="$(lean_files | grep -c . || true)"
  PARTIAL=""
  for f in $(lean_files); do
    scanned=$((scanned + 1))
    if [ $((scanned % PROGRESS_EVERY)) = 0 ]; then
      printf '  scanning %s/%s...\r' "$scanned" "$total" >&2
    fi
    now="$(date +%s)"
    if [ $((now - started)) -ge "$BUDGET" ]; then
      PARTIAL="stopped after ${BUDGET}s at file $scanned of $total"
      break
    fi
    rel="${f#"$CLONE"/}"
    # Every occurrence of the bare name, then judged.  Collecting the WIDE set
    # first is what lets the exclusions be reported rather than silently
    # never-matched.
    while IFS= read -r hits; do
      # A file with NO hits still sends one EMPTY line through the heredoc,
      # and the first version filed every such file as a look-alike — ~300
      # phantom exclusions on the real tree, each one an exclusion nobody
      # could audit.  §5.4's law on its own instrument: a zero-row read is an
      # instrument fault, not a finding.
      [ -n "$hits" ] || continue
      n="${hits%%:*}"; line="${hits#*:}"
      # PREFIX COLLISION: `.unsupportedDevice` is not `.unsupported`.
      if ! printf '%s' "$line" | grep -qE "\\.$CTOR([^A-Za-z0-9_']|\$)"; then
        LOOKALIKES="${LOOKALIKES}$rel:$n	prefix	$(printf '%s' "$line" | grep -oE "\\.$CTOR[A-Za-z0-9_']+" | head -1)
"
        continue
      fi
      # POSITION: does it ride a channel this TYPE actually uses?
      if printf '%s' "$line" | grep -qE "$pat"; then
        SITES="${SITES}$rel:$n	$(classify_hit "$line")	$(printf '%s' "$line" | sed 's/^[ \t]*//' | cut -c1-96)
"
      else
        LOOKALIKES="${LOOKALIKES}$rel:$n	position	no channel position for $TYPE on this line
"
      fi
    done <<EOF
$(code_hits "$f" "\\\\.$CTOR" 2>/dev/null || true)
EOF
  done
}

count_of() { printf '%s' "$1" | grep -c . || true; }

# ---- --arms: how many arms does ONE function destructure?
# The other pricing question lanes keep answering by hand — the successor lane
# hand-counted `iterValues` at 7 and `applyCallPlan` at 9 before touching
# either.  Arms are where a constructor change lands, so this is the per-
# function form of the same law the site census implements per type.
# Comments are stripped first, for the reason the site census learned: prose
# about an arm is not an arm.
arms_of() {                     # fn -> "file:line arms ite lines"
  local fn="$1" f
  for f in $(lean_files); do
    awk -v FN="${f#"$CLONE"/}" -v FN2="$fn" '
      function strip(line,   out, i, n, two) {
        out = ""; i = 1; n = length(line)
        while (i <= n) {
          two = substr(line, i, 2)
          if (depth == 0 && two == "--") break
          if (two == "/-") { depth++; i += 2; continue }
          if (two == "-/") { if (depth > 0) depth--; i += 2; continue }
          if (depth == 0) out = out substr(line, i, 1)
          i++
        }
        return out
      }
      { orig = $0; code = strip($0) }
      code ~ ("^[ \t]*(private[ \t]+)?(def|partial def)[ \t]+" FN2 "[ \t(:]") && !inblk {
        inblk = 1; start = NR; arms = 0; ite = 0; elif = 0; top = 0; minind = 0
        matches = 0; firstctl = ""; delete scrn; next
      }
      inblk && code ~ /^(def|partial def|theorem|lemma|abbrev|instance|structure|inductive|example|end|namespace|section|open|@\[|#)/ {
        # NO `exit`: a name can resolve MORE THAN ONCE, and reporting the
        # first hit is the identifier law failing inside the tool again.
        bestn = 0; best = "-"; for (k in scrn) if (scrn[k] > bestn) { bestn = scrn[k]; best = k }; printf "%s:%d %d %d %d %d %d %s %d %s %d\n", FN, start, top, arms, ite, elif, NR - start, (firstctl == "" ? "none" : firstctl), matches, best, bestn
        inblk = 0
      }
      inblk {
        # TOP-LEVEL arms and TOTAL arms are different numbers, and the hand
        # counts this was calibrated against are the top-level ones: the
        # principal dispatch.  Nested matches inside an arm destructure too,
        # so BOTH are reported — an arm count without its depth is the same
        # ambiguity laws.sh hit between a law and its home.
        # (No apostrophes in here: this awk program is single-quoted.)
        # THE PRINCIPAL DISPATCH IS WHICHEVER CONSTRUCT COMES FIRST, not
        # whichever is more numerous.  applyBuiltin opens with an if-chain and
        # carries 45 match arms INSIDE its branches; counting alone called it a
        # match, and the successor lane, READING it, called it an if-chain.
        # Reading beat counting, so the tool now records the order.
        if (firstctl == "" && code ~ /(^|[^A-Za-z0-9_])if([^A-Za-z0-9_]|$)/) firstctl = "if"
        if (firstctl == "" && code ~ /^[ \t]*\|/) firstctl = "match"
        if (code ~ /^[ \t]*\|/) {
          arms++
          ind = match(code, /\|/) - 1
          if (minind == 0 || ind < minind) { minind = ind; top = 0 }
          if (ind == minind) top++
        }
        # `then` sits at END OF LINE in an if-chain, and the first version
        # required a trailing character — so a 210-line if/else-if chain
        # reported ZERO if/then.  Anchor both edges.
        n = gsub(/(^|[^A-Za-z0-9_])then([^A-Za-z0-9_]|$)/, " then ", code); ite += n
        n = gsub(/(^|[^A-Za-z0-9_])else[ \t]+if([^A-Za-z0-9_]|$)/, " elif ", code); elif += n
        # `match ... with` BLOCKS, not their arms: the successor lane reads
        # applyBuiltin as 15 nested matches carrying 45 arms, and a report that
        # gives only an arm count cannot be checked against that.
        n = gsub(/(^|[^A-Za-z0-9_])match([^A-Za-z0-9_]|$)/, " match ", code); matches += n
        # AND the ones on the SAME SCRUTINEE, which is the unit a reader counts:
        # applyBuiltin has 30 match tokens in all, and the 15 that matter are
        # `match vs with` — the branches that re-destructure the dispatch
        # argument.  Total and dominant-scrutinee are different questions.
        if (match(orig, /match[ \t]+[A-Za-z_][A-Za-z0-9_.]*[ \t]+with/)) {
          scr = substr(orig, RSTART, RLENGTH)
          sub(/^match[ \t]+/, "", scr); sub(/[ \t]+with$/, "", scr)
          scrn[scr]++
        }
      }
      END { if (inblk) { bestn = 0; best = "-"; for (k in scrn) if (scrn[k] > bestn) { bestn = scrn[k]; best = k }; printf "%s:%d %d %d %d %d %d %s %d %s %d\n", FN, start, top, arms, ite, elif, NR - start, (firstctl == "" ? "none" : firstctl), matches, best, bestn } }' "$f"
  done
}

# --------------------------------------------------------------- self-test
if [ "$SELF_TEST" = "1" ]; then
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/sites-selftest.XXXXXX")" || die "no temp dir"
  trap 'rm -rf "$tmp"' EXIT
  ok=0; bad=0
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; \
            else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }

  # ---- CASE 1: the ES shape.  §5.4a records 5 destructure + 2 construct,
  # honest total 7, with 3 name collisions excluded — and it records WHY the
  # number needed two greps: the construction sites match a different pattern.
  es="$tmp/es"; mkdir -p "$es/LeanModels/Es" "$es/LeanModels/Core"
  cat > "$es/LeanModels/Core/Outcome.lean" <<'LEAN'
inductive Cause where
  | unsupported (m : String)
  | other
LEAN
  cat > "$es/LeanModels/Es/Refuses.lean" <<'LEAN'
def refusesA (r : Res) : Bool :=
  match r with
  | .error (.unsupported _ m _) => true
  | _ => false
def refusesB (r : Res) : Bool :=
  match r with
  | .error (.unsupported _ _ _) => true
  | _ => false
def refusesC (r : Res) : Option String :=
  match r with
  | .error (.unsupported _ m _) => some m
  | _ => none
def refusesD (r : Res) : Bool :=
  match r with
  | .error (.unsupported _ _ _) => true
  | _ => false
def refusesE (r : Res) : Bool :=
  match r with
  | .error (.unsupported _ _ _) => true
  | _ => false
def mkA : Res := .error (.unsupported .none "a" none)
def mkB : Res := .error (.unsupported .none "b" none)
LEAN
  cat > "$es/LeanModels/Es/Lookalikes.lean" <<'LEAN'
inductive Node where
  | unsupported (k : String)
  | leaf
inductive Kind where
  | unsupported (k : String)
  | known
def nodeIs (n : Node) : Bool :=
  match n with
  | .unsupported _ => true
  | .leaf => false
def kindIs (k : Kind) : Bool :=
  match k with
  | .unsupported _ => true
  | .known => false
def dev : Res := .error (.unsupportedDevice 3)
LEAN
  CLONE="$es"; TYPE="Outcome"; CTOR="unsupported"; EXTRA_CHANNELS=""
  scan_sites
  d="$(printf '%s' "$SITES" | awk -F'\t' '$2=="destructure"||$2=="both"' | grep -c . || true)"
  c="$(printf '%s' "$SITES" | awk -F'\t' '$2=="construct"||$2=="both"' | grep -c . || true)"
  check "ES: 5 DESTRUCTURE sites"          "$d" "5"
  check "ES: 2 CONSTRUCT sites"            "$c" "2"
  check "ES: honest total is 7, not 5"     "$((d + c))" "7"
  check "ES: 3 look-alikes excluded"       "$(count_of "$LOOKALIKES")" "3"
  # "No single grep produced the number" (§5.4a).  The destructure pattern
  # alone says 5; the construction sites match a DIFFERENT pattern; only both
  # give the honest 7.  The doc also records a raw grep of 8 — its exact
  # pattern is not recorded, so this asserts the decomposition it DOES record
  # rather than a number whose provenance cannot be reconstructed.
  check "ES: no SINGLE grep produces the total" \
        "$( [ "$d" != "$((d + c))" ] && echo confirmed )" "confirmed"
  check "ES: the prefix collision is named" \
        "$(printf '%s' "$LOOKALIKES" | grep -c 'prefix')" "1"
  check "ES: the other TYPES' arms are excluded by POSITION" \
        "$(printf '%s' "$LOOKALIKES" | grep -c 'position')" "2"
  check "ES: a file with NO hits contributes NO look-alike" \
        "$(printf '%s' "$LOOKALIKES" | grep -c 'Core/Outcome.lean')" "0"
  check "ES: every declaring type is named" \
        "$(declaring_types | awk -F'\t' '{print $2}' | sort -u | tr '\n' ' ' | sed 's/ *$//')" "Cause Kind Node"

  # ---- CASE 2: the C shape.  §5.4a records 8 construct + 8 destructure with
  # 53 of 64 touch points INSULATED — the insulation is the finding, and it is
  # the callers of a named primitive, which are not touch points at all.
  cq="$tmp/c"; mkdir -p "$cq/LeanModels/C"
  {
    echo 'inductive Halt where'
    echo '  | unsupported (m : String)'
    echo '  | timeout'
    i=1; while [ "$i" -le 8 ]; do
      echo "def mk$i : R := .halt (.unsupported \"m$i\")"; i=$((i + 1))
    done
    i=1; while [ "$i" -le 8 ]; do
      echo "def see$i (r : R) : Bool := match r with"
      echo "  | .halt (.unsupported _) => true"
      echo "  | _ => false"
      i=$((i + 1))
    done
  } > "$cq/LeanModels/C/Refusal.lean"
  # The three unrelated Ast types that share the constructor NAME.
  cat > "$cq/LeanModels/C/Ast.lean" <<'LEAN'
inductive Expr where
  | unsupported (cKind : String) (text : String)
  | lit
inductive Stmt where
  | unsupported (cKind : String) (text : String)
  | skip
inductive Decl where
  | unsupported (cKind : String) (text : String)
  | fn
def kindOf (e : Expr) : String :=
  match e with
  | .unsupported k _ => k
  | .lit => ""
LEAN
  CLONE="$cq"; TYPE="Halt"; CTOR="unsupported"
  scan_sites
  d="$(printf '%s' "$SITES" | awk -F'\t' '$2=="destructure"||$2=="both"' | grep -c . || true)"
  c="$(printf '%s' "$SITES" | awk -F'\t' '$2=="construct"||$2=="both"' | grep -c . || true)"
  check "C: 8 CONSTRUCT sites"             "$c" "8"
  check "C: 8 DESTRUCTURE sites"           "$d" "8"
  check "C: the Halt channel is found where error would return ZERO" \
        "$(printf '%s' "$SITES" | grep -c '\.halt (\.unsupported')" "16"
  check "C: three unrelated Ast types are DECLARED" \
        "$(declaring_types | awk -F'\t' '{print $2}' | sort -u | grep -cE 'Expr|Stmt|Decl')" "3"
  check "C: and their arm is excluded by POSITION" \
        "$(printf '%s' "$LOOKALIKES" | grep -c 'Ast.lean')" "1"

  # ---- CASE 3: the CONVICTING case — a destructurer that names no Core
  # symbol at all, which is why the importer count (2) was not a bound.
  go="$tmp/go"; mkdir -p "$go/Examples/go/rung1"
  cat > "$go/Examples/go/rung1/guards.lean" <<'LEAN'
def refusalOf (stmts : List Stmt) : Option String :=
  match (execSeq 64 stmts) ({} : GoWorld) with
  | .error (.unsupported _ m _) => some m
  | _ => none
LEAN
  CLONE="$go"; TYPE="Outcome"; CTOR="unsupported"
  scan_sites
  check "Go: refusalOf's destructure is FOUND"  \
        "$(printf '%s' "$SITES" | grep -c 'guards.lean')" "1"
  check "  ...and it imports NOTHING from Core" \
        "$(grep -c 'import' "$go/Examples/go/rung1/guards.lean")" "0"
  check "  ...so an importer count would MISS it" \
        "$(printf '%s' "$SITES" | awk -F'\t' '$2=="destructure"' | grep -c .)" "1"

  # ---- the classifier itself, on the real shapes it must tell apart
  CTOR="unsupported"
  check "an arm destructures"      "$(classify_hit '  | .error (.unsupported _ m _) => some m')" "destructure"
  check "a right-hand side constructs" "$(classify_hit '  fun _ => .error (.unsupported c m none)')" "construct"
  check "one line can do BOTH"     "$(classify_hit '  | .unsupported m => .error (.unsupported (.unsupported ()) m none)')" "both"
  check "a #guard pins the SHAPE"  "$(classify_hit '#guard refusalOf x == some (.unsupported 1)')" "destructure"
  # COMMENTS ARE NOT SITES — the defect the first live run exposed.
  cm="$tmp/comments"; mkdir -p "$cm"
  cat > "$cm/Doc.lean" <<'LEAN'
/-- This doc comment mentions Halt.unsupported and must NOT be a site. -/
def real : R := .halt (.unsupported "yes")
-- a line comment about .halt (.unsupported "no")
/- a block
   comment with .halt (.unsupported "no") inside
   /- and a NESTED one, .halt (.unsupported "no") -/
   still inside -/
def real2 : R := .halt (.unsupported "yes")
LEAN
  # Vendored fixtures are SKIPPED, not scanned as code.
  vf="$tmp/vendored"; mkdir -p "$vf/Examples/go/rung1"
  printf 'package main\nfunc unsupported() {}\n' > "$vf/Examples/go/rung1/rung1.go"
  printf 'def real : R := .halt (.unsupported "m")\n' > "$vf/Examples/go/rung1/guards.lean"
  saved_cl="$CLONE"; CLONE="$vf"
  check "a vendored .go is not in the scan set" "$(lean_files | grep -c '[.]go$')" "0"
  check "  ...while its .lean sibling is"       "$(lean_files | grep -c 'guards[.]lean')" "1"
  CLONE="$saved_cl"

  check "comments are not sites"        "$(code_hits "$cm/Doc.lean" '\\.unsupported' | grep -c .)" "2"
  check "  ...and the real ones ARE"    "$(code_hits "$cm/Doc.lean" '\\.unsupported' | cut -d: -f1 | tr '\n' ' ' | sed 's/ *$//')" "2 8"
  # `awk -v` strips ONE backslash level: passing `\.` made the dot a WILDCARD,
  # so `| unsupported (m : String)` — a DECLARATION — was counted as a use.
  check "the dot is literal, not a wildcard" \
        "$(printf 'x unsupported\ny .unsupported\n' > "$cm/W.lean"; code_hits "$cm/W.lean" '\\.unsupported' | grep -c .)" "1"

  check "a prefix name is not the ctor" \
        "$(printf '%s' '.error (.unsupportedDevice id)' | grep -cE "\\.unsupported([^A-Za-z0-9_']|\$)")" "0"

  # ---- the BUDGET: a tool that prices a change must itself be priced.
  echo "  -- budget"
  big="$tmp/big"; mkdir -p "$big"
  i=1; while [ "$i" -le 12 ]; do
    printf 'def f%s : R := .halt (.unsupported "m")\n' "$i" > "$big/F$i.lean"
    i=$((i + 1))
  done
  CLONE="$big"; TYPE="Halt"; CTOR="unsupported"; EXTRA_CHANNELS=""
  BUDGET=600; scan_sites
  check "inside the budget there is no PARTIAL" "$PARTIAL" ""
  check "  ...and every file was scanned"       "$(printf '%s' "$SITES" | grep -c .)" "12"
  BUDGET=0; scan_sites
  check "past the budget it stops"              "$( [ -n "$PARTIAL" ] && echo partial)" "partial"
  check "  ...saying WHERE it stopped"          "$(printf '%s' "$PARTIAL" | grep -c 'file 1 of 12')" "1"
  check "  ...and it is never silent"           "$(printf '%s' "$PARTIAL" | grep -c 'stopped after')" "1"
  BUDGET=600

  # ---- --arms, calibrated against hand counts on the live tree.
  echo "  -- arms"
  am="$tmp/arms"; mkdir -p "$am"
  cat > "$am/A.lean" <<'LEAN'
def dispatch (x : T) : R :=
  match x with
  | .a => 1
  | .b =>
      match y with
      | .p => 2
      | .q => 3
  | .c => if z then 4 else 5
def other : Nat := 0
LEAN
  CLONE="$am"
  set -- $(arms_of dispatch)
  check "TOP-LEVEL arms are the dispatch width" "$2" "3"
  check "  ...total counts the NESTED ones too" "$3" "5"
  check "  ...and if/then is counted apart"     "$4" "1"
  check "the block ends at the next top-level"  "$6" "8"
  check "the SHAPE is read from what comes first" "$7" "match"
  check "a missing function reports nothing"    "$(arms_of nosuchfn)" ""
  cat > "$am/B.lean" <<'LEAN'
/-- A doc comment with | a fake arm inside -/
def commented (x : T) : R :=
  match x with
  | .a => 1
def z : Nat := 0
LEAN
  set -- $(arms_of commented)
  check "prose about an arm is not an arm"      "$2" "1"

  # THE applyBuiltin CALIBRATION ROW.  The successor lane read the real
  # function verbatim: a 19-deep `if fname == … then … else if` chain on a
  # STRING, with 15 nested `match vs with` blocks carrying 45 arms.  The tool
  # first reported "45 top-level arms, 0 if/then" — inverting ite and match.
  # That is not a cosmetic error: a shape report that says `match` sends a
  # prover to `cases`, and `cases` on a String cannot apply.  The shape is
  # reproduced here so the inversion cannot come back.
  cal="$tmp/cal"; mkdir -p "$cal"
  {
    echo 'def applyBuiltinLike (K : Kont) (m : Module) (fname : String) (vs : List RVal) :'
    echo '    SemF RVal := do'
    i=1
    while [ "$i" -le 19 ]; do
      if [ "$i" = "1" ]; then echo "  if fname == \"b$i\" then"
      else echo "  else if fname == \"b$i\" then"; fi
      if [ "$i" -le 15 ]; then
        echo '    match vs with'
        echo '    | [v] => one v'
        echo '    | [] => none'
        echo '    | _ => many'
      else
        echo '    plain'
      fi
      i=$((i + 1))
    done
    echo '  else raisePy .nameError'
    echo 'def after : Nat := 0'
  } > "$cal/Cal.lean"
  CLONE="$cal"
  set -- $(arms_of applyBuiltinLike)
  check "CALIBRATION: the shape is an if-chain, not a match" "$7" "if"
  check "  ...19 deep (1 if + 18 else-if)"     "$(( $5 + 1 ))" "19"
  check "  ...15 match blocks on the dispatch arg" "${10}" "15"
  check "  ...and the arg it dispatches on"     "$9" "vs"
  check "  ...carrying 45 nested arms"          "$2" "45"

  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

# -------------------------------------------------------------------- main
if [ -n "$ARMS_FN" ]; then
  [ -d "$CLONE" ] || die "--dir '$CLONE' is not a directory"
  found="$(arms_of "$ARMS_FN")"
  if [ -z "$found" ]; then
    echo "sites.sh --arms $ARMS_FN: no such def found under $CLONE"
    exit 1
  fi
  echo "sites.sh --arms $ARMS_FN   (measured at $(git -C "$CLONE" rev-parse --short HEAD 2>/dev/null || echo 'no git'))"
  n_defs="$(printf '%s\n' "$found" | grep -c .)"
  [ "$n_defs" -gt 1 ] && printf '  %s DEFINITIONS resolve to this name — all of them:\n' "$n_defs"
  printf '%s\n' "$found" | while read -r at top arms ite elif lines firstctl matches scr scrn; do
    # An if/else-if CHAIN is 1 + the else-ifs.  The raw `then` count is higher,
    # because nested ifs inside the branches also carry one.
    depth=$((elif + 1))
    case "$firstctl" in
      if)    shape="if/else-if chain" ;;
      match) shape="match dispatch" ;;
      *)     shape="straight-line" ;;
    esac
    if [ "$firstctl" = "if" ]; then
      printf '  %-40s %-17s %3s deep (1 if + %s else-if), %s then-tokens in all,\n' "$at" "$shape" "$depth" "$elif" "$ite"
      printf '  %-40s %19s %3s on `%s` of %s match block(s), %s nested arm(s), %s lines\n' \
        "" "" "$scrn" "$scr" "$matches" "$top" "$lines"
    else
      printf '  %-40s %-17s %3s top-level arm(s), %3s total,\n' "$at" "$shape" "$top" "$arms"
      printf '  %-40s %19s %3s if/then, %3s else-if, %s lines\n' "" "" "$ite" "$elif" "$lines"
    fi
  done
  echo
  echo "  Arms are where a constructor change LANDS: this is the per-function"
  echo "  form of what the site census does per type. Comments are stripped —"
  echo "  prose about an arm is not an arm."
  exit 0
fi

[ -n "$TYPE" ] && [ -n "$CTOR" ] || usage
[ -d "$CLONE" ] || die "--dir '$CLONE' is not a directory"

scan_sites
DECL="$(declaring_types)"
D_LINES="$(printf '%s' "$SITES" | awk -F'\t' '$2=="destructure"||$2=="both"' || true)"
C_LINES="$(printf '%s' "$SITES" | awk -F'\t' '$2=="construct"||$2=="both"' || true)"
nd="$(count_of "$D_LINES")"; nc="$(count_of "$C_LINES")"; nl="$(count_of "$LOOKALIKES")"

echo "sites.sh — $TYPE.$CTOR   (measured at $(git -C "$CLONE" rev-parse --short HEAD 2>/dev/null || echo 'no git'))"
if [ -n "$PARTIAL" ]; then
  echo "  PARTIAL — $PARTIAL. Every count below is a FLOOR, not a bound."
  echo "            Raise --budget, or narrow --dir, and re-run before quoting it."
fi
echo
printf '  DECLARED BY  %s type(s) using the name `%s` — every one of them a\n' \
       "$(printf '%s' "$DECL" | awk -F'\t' '{print $2}' | sort -u | grep -c . || true)" "$CTOR"
printf '               look-alike unless it IS the type you named:\n'
printf '%s\n' "$DECL" | grep -v '^$' \
  | awk -F'\t' '!seen[$2]++ { printf "    %-46s %s%s\n", $1, $2, ($2 == T ? "   <- the type you named" : "") }' T="$TYPE"
echo
printf '  DESTRUCTURE  %s site(s)  <- THE BOUND on breakage (an upper bound)\n' "$nd"
printf '%s\n' "$D_LINES" | grep -v '^$' | awk -F'\t' '{ printf "    %-46s %s\n", $1, $3 }'
echo
printf '  CONSTRUCT    %s site(s)  (a different pattern — no single grep finds both)\n' "$nc"
printf '%s\n' "$C_LINES" | grep -v '^$' | awk -F'\t' '{ printf "    %-46s %s\n", $1, $3 }'
echo
printf '  LOOK-ALIKES  %s excluded, with the reason:\n' "$nl"
if [ "$VERBOSE" = "1" ]; then
  printf '%s\n' "$LOOKALIKES" | grep -v '^$' | awk -F'\t' '{ printf "    %-46s %-9s %s\n", $1, $2, $3 }'
else
  printf '%s\n' "$LOOKALIKES" | grep -v '^$' | awk -F'\t' '{ c[$2]++ } END { for (k in c) printf "    %-9s %s site(s)   (--verbose to list)\n", k, c[k] }'
fi
echo
echo "  The DESTRUCTURE count bounds the work; the build log LOCATES it. Neither"
echo "  is a count of causes — see docs/family-architecture.md §5.4a, and"
echo "  tools/diagnose.sh --explain for what a red build's numbers mean."
