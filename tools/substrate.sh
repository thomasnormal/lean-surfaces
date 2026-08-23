#!/usr/bin/env bash
# tools/substrate.sh — §3.4's gate: the substrate contract, per tier, BY SHAPE.
#
# WHY THIS FILE EXISTS.  `tools/laws.sh` measured §3.4 as the most-cited
# section in the tree with NO GATE at all — nine laws (STMT-14..STMT-22) at 21
# ledger citations, more than any other unenforced home.  §3.4 is the contract
# every tier's refusal vocabulary is built on, and it was prose.
#
# The laws this makes checkable, and each is checked BY SHAPE rather than by
# spelling, because §3.4 says so in as many words — *adopted by SHAPE, not by
# spelling* (STMT-21):
#
#   STMT-19  the uncatchability invariant is TYPE-level, never lemma-level
#   STMT-20  the monad layer ORDER is load-bearing
#   STMT-21  adopted by SHAPE, not by spelling
#   STMT-22  THE FIT BOUNDARY — "does this tier HAVE a run?" (§3.4.1)
#   STMT-67  a second semantics owes an ADEQUACY theorem (§8.5)
#
# WHAT IT REPORTS, per tier directory under LeanModels/:
#   MONAD    ADOPTED  — built on Core's `SemMWith`/`HaltWith`/`SemM`
#            BY-SHAPE — a LOCAL type of the same shape, `ExceptT ρ (StateT W
#                       Halt)`; named with its file:line, because the shape is
#                       the claim and the name is not
#            OWN      — its own verdict type
#            NONE     — no evaluator yet (ingestion-only)
#   REFUSALS Core-channel constructor sites vs locally-declared ones
#   UNCATCH  a statement applying the tier's catch over a Loud — by PATTERN
#   RUN      a `run`/`toRun` returning the family verdict type (STMT-22)
#   ADEQUACY two defs sharing a SIGNATURE across files = two semantics; then
#            a theorem naming both, or OWED (STMT-67)
#
# THE BOUND, stated before the numbers.  This greps text.  It cannot elaborate,
# so `BY-SHAPE` is a claim about syntax and `ADOPTED` about an identifier, not
# about a type-checked equality.  It over-credits in the same direction
# `laws.sh` does: read a green row as *"nothing here contradicts §3.4"*, never
# as *"§3.4 holds here."*
#
# USAGE
#   tools/substrate.sh              # the table
#   tools/substrate.sh --tier C     # one tier, with the evidence lines
#   tools/substrate.sh --self-test
#
# ZERO Lean execution.  Safe outside a tenure (A11).

set -u

CLONE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ONLY=""
SELF_TEST=0

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
die()   { echo "substrate.sh: $*" >&2; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --dir)       CLONE="${2:-}"; shift 2 ;;
    --tier)      ONLY="${2:-}"; shift 2 ;;
    --self-test) SELF_TEST=1; shift ;;
    -h|--help)   usage ;;
    *)           die "unknown argument '$1'" ;;
  esac
done

MODELS="$CLONE/LeanModels"

tiers() {
  [ -d "$MODELS" ] || return 0
  find "$MODELS" -maxdepth 1 -mindepth 1 -type d 2>/dev/null \
    | sed "s|.*/||" | grep -v '^Core$' | LC_ALL=C sort
}

tier_lean() { find "$MODELS/$1" -name '*.lean' -type f 2>/dev/null | LC_ALL=C sort; }

# Declared HERE?  The whole ADOPTED/BY-SHAPE distinction turns on this: the ES
# tier defines its own `SemM` with Core's name, and a grep for the NAME would
# call that adoption.  The shape is the claim; the name is not.
defines_locally() {             # tier, name -> 0 when the tier declares it
  local f
  for f in $(tier_lean "$1"); do
    grep -qE "^[ \t]*(abbrev|def|inductive|structure)[ \t]+$2[ \t(:]" "$f" 2>/dev/null && return 0
  done
  return 1
}

# (a) THE MONAD.
MONAD_KIND=""; MONAD_AT=""; MONAD_TEXT=""
tier_monad() {
  local tier="$1" f hit
  MONAD_KIND="NONE"; MONAD_AT=""; MONAD_TEXT=""
  for f in $(tier_lean "$tier"); do
    # NOT `[^:=]*` before the `:=`: a binder like `(σ : Type)` contains a
    # colon, so that spelling could never match a PARAMETERISED abbrev — and
    # Python's `abbrev PyM (σ : Type) := SemM σ PyErr` read as OWN.
    hit="$(grep -nE '^[ \t]*abbrev[ \t]+[A-Za-z_][A-Za-z0-9_]*.*:=.*(SemMWith|HaltWith|SemM )' "$f" 2>/dev/null | head -1)"
    if [ -n "$hit" ]; then
      # Core's name, but is it Core's DEFINITION?
      if printf '%s' "$hit" | grep -q 'SemMWith\|HaltWith'; then
        defines_locally "$tier" "SemMWith" || defines_locally "$tier" "HaltWith" || {
          MONAD_KIND="ADOPTED"; MONAD_AT="${f#"$CLONE"/}:${hit%%:*}"
          MONAD_TEXT="$(printf '%s' "$hit" | cut -d: -f2- | sed 's/^[ \t]*//' | cut -c1-70)"; return 0; }
      elif ! defines_locally "$tier" "SemM"; then
        MONAD_KIND="ADOPTED"; MONAD_AT="${f#"$CLONE"/}:${hit%%:*}"
        MONAD_TEXT="$(printf '%s' "$hit" | cut -d: -f2- | sed 's/^[ \t]*//' | cut -c1-70)"; return 0
      fi
    fi
  done
  for f in $(tier_lean "$tier"); do
    hit="$(grep -nE '^[ \t]*abbrev[ \t]+.*:=.*ExceptT.*StateT.*(Halt|Except)' "$f" 2>/dev/null | head -1)"
    if [ -n "$hit" ]; then
      MONAD_KIND="BY-SHAPE"; MONAD_AT="${f#"$CLONE"/}:${hit%%:*}"
      MONAD_TEXT="$(printf '%s' "$hit" | cut -d: -f2- | sed 's/^[ \t]*//' | cut -c1-70)"; return 0
    fi
  done
  for f in $(tier_lean "$tier"); do
    hit="$(grep -nE '^[ \t]*inductive[ \t]+(Res|Outcome|Result)[ \t(]' "$f" 2>/dev/null | head -1)"
    if [ -n "$hit" ]; then
      MONAD_KIND="OWN"; MONAD_AT="${f#"$CLONE"/}:${hit%%:*}"
      MONAD_TEXT="$(printf '%s' "$hit" | cut -d: -f2- | sed 's/^[ \t]*//' | cut -c1-70)"; return 0
    fi
  done
  return 0
}

# (b) REFUSAL SITES: Core's channel vs a local constructor.
REF_CORE=0; REF_LOCAL=0
tier_refusals() {
  local tier="$1" f
  REF_CORE=0; REF_LOCAL=0
  for f in $(tier_lean "$tier"); do
    REF_CORE=$((REF_CORE + $(grep -cE '\.(error|halt|loud) \(\.unsupported([^A-Za-z0-9_]|$)|(Halt|Loud)\.unsupported([^A-Za-z0-9_]|$)' "$f" 2>/dev/null || true)))
    REF_LOCAL=$((REF_LOCAL + $(grep -cE '^[ \t]*\|[ \t]*unsupported[ \t(]' "$f" 2>/dev/null || true)))
  done
}

# (c) UNCATCHABILITY, BY PATTERN: a statement that applies the catch over a
# Loud/Halt.  STMT-19 says the invariant is TYPE-level — so what this looks for
# is a STATEMENT exercising it, not a lemma name.
tier_uncatch() {
  local tier="$1" f
  for f in $(tier_lean "$tier"); do
    if grep -nE '(theorem|example|lemma|#guard)' "$f" 2>/dev/null \
         | grep -qE 'tryCatch|catchIn|\.catch'; then
      printf '%s\n' "${f#"$CLONE"/}"; return 0
    fi
    # Context in BOTH directions: the sentence that says what the catch must
    # not swallow sits after the call as often as before it.
    if grep -C2 -nE 'tryCatch' "$f" 2>/dev/null | grep -qE 'Loud|Halt|unsupported'; then
      printf '%s\n' "${f#"$CLONE"/}"; return 0
    fi
  done
  echo ""
}

# (d) THE FIT BOUNDARY (STMT-22): does the tier HAVE a run?
tier_run() {
  local tier="$1" f hit
  for f in $(tier_lean "$tier"); do
    hit="$(grep -nE '^[ \t]*(private[ \t]+)?def[ \t]+(toRun|run)[ \t(]' "$f" 2>/dev/null | head -1)"
    [ -n "$hit" ] && { printf '%s:%s\n' "${f#"$CLONE"/}" "${hit%%:*}"; return 0; }
  done
  echo ""
}

# (e) TWO SEMANTICS (STMT-67): two defs sharing a SIGNATURE across files.  The
# signature — the parameter types and nothing else — is the shape that makes
# two functions rival evaluators; the names never match, which is why a
# name-based rule finds nothing.  Python's `callIn` / `callInMono` are the
# recorded case, and their sharing a type is stated in the source as the point.
tier_twins() {
  local tier="$1" f
  for f in $(tier_lean "$tier"); do
    # A SIGNATURE SPANS LINES, and the return type is usually on the SECOND
    # one — `callIn`'s `: Run World RVal` is.  The first version compared
    # single lines, so it never saw a return type at all and paired anything
    # whose BINDERS happened to match: `alloc / allocZeroed` came back as two
    # semantics.  Accumulate from `def` to the `:=` that ends the signature.
    awk -v FN="${f#"$CLONE"/}" '
      /^[ \t]*def[ \t]+[A-Za-z_][A-Za-z0-9_]*[ \t]*\(/ && !collecting {
        collecting = 1; startln = NR; buf = $0
        if (buf ~ /:=/) { emit(); collecting = 0 }
        next
      }
      collecting {
        buf = buf " " $0
        if (buf ~ /:=/ || NR - startln > 6) { emit(); collecting = 0 }
      }
      function emit(   rest, name, sig, np) {
        rest = buf; sub(/^[ \t]*def[ \t]+/, "", rest)
        name = rest; sub(/[ \t(].*$/, "", name)
        sig = rest; sub(/^[^ \t(]*/, "", sig)
        sub(/:=.*$/, "", sig)
        gsub(/[A-Za-z_][A-Za-z0-9_.]*[ \t]*:/, ":", sig)
        gsub(/[ \t]+/, "", sig)
        np = gsub(/\(:/, "(:", sig)
        # THREE typed binders and a RETURN TYPE.  Two rival evaluators over one
        # AST take at least the program, the fuel and the world.
        if (np >= 3 && sig ~ /\):/) printf "%s\t%s\t%s\n", sig, name, FN ":" startln
      }' "$f"
  done | LC_ALL=C sort | awk -F'\t' '
      { if ($1 == prev && $3 != prevfile) print prevname " / " $2 "\t" prevfile " / " $3
        prev = $1; prevname = $2; prevfile = $3 }' | head -3
}

# SIGNATURE IDENTITY IS NECESSARY, NOT SUFFICIENT.  Two functions can share a
# signature and be siblings rather than rivals — `alloc / allocZeroed` and
# `envCreateImmutableBinding / envCreateMutableBinding` both came back as "two
# semantics" from signature alone.  So the tool separates what it KNOWS from
# what it merely SUSPECTS:
#
#   OWED   — the pair also carries a second-implementation MARKER, the naming
#            this repository actually uses for a rebuild twin (`callInMono`
#            beside `callIn`).  Direct evidence of one function implemented
#            twice.
#   TWINS? — same signature, no marker: a CANDIDATE for a human, not a finding.
#
# The marker list is a convention, not a law, and it will need extending.  It
# is named here rather than buried, so the next lane can see what the verdict
# rests on.
SECOND_IMPL_MARKERS='Mono Monadic V2 Alt Rebuild'
is_second_impl_pair() {         # "a / b" -> 0 when one name is the other + marker
  local a b m
  a="$(printf '%s' "$1" | sed 's| */.*||' | tr -d ' ')"
  b="$(printf '%s' "$1" | sed 's|.*/ *||' | tr -d ' ')"
  [ -n "$a" ] && [ -n "$b" ] || return 1
  for m in $SECOND_IMPL_MARKERS; do
    [ "$b" = "$a$m" ] && return 0
    [ "$a" = "$b$m" ] && return 0
  done
  return 1
}

adequacy_for() {                # tier, "a / b" -> a theorem naming both, or ''
  local tier="$1" a b f
  a="${2%% /*}"; b="${2##*/ }"; b="$(printf '%s' "$b" | tr -d ' ')"
  [ -n "$a" ] && [ -n "$b" ] || { echo ""; return 0; }
  for f in $(tier_lean "$tier"); do
    grep -nE '^[ \t]*(theorem|lemma)' "$f" 2>/dev/null | grep -q "$a" \
      && grep -nE '^[ \t]*(theorem|lemma)' "$f" 2>/dev/null | grep -q "$b" \
      && { printf '%s\n' "${f#"$CLONE"/}"; return 0; }
  done
  echo ""
}

# --------------------------------------------------------------- self-test
if [ "$SELF_TEST" = "1" ]; then
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/substrate-selftest.XXXXXX")" || die "no temp dir"
  trap 'rm -rf "$tmp"' EXIT
  ok=0; bad=0
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; \
            else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }

  fx="$tmp/fx"; MODELS="$fx/LeanModels"; CLONE="$fx"
  mkdir -p "$MODELS/Adoptr" "$MODELS/Shaper" "$MODELS/Owner" "$MODELS/Empty" \
           "$MODELS/Twins" "$MODELS/Core"
  printf 'abbrev TM := SemMWith TWorld Err Ref Unit\ndef toRun (x : TM α) : Run α := x\n' \
    > "$MODELS/Adoptr/M.lean"
  # Core's NAME, but the tier's own DEFINITION — the ES trap.
  printf 'abbrev SemM (W : Type) (r : Type) := ExceptT r (StateT W Halt)\nabbrev EM (W) := SemM W Ab\n' \
    > "$MODELS/Shaper/M.lean"
  printf 'inductive Res (a : Type) where\n  | ok (v : a)\n  | bad\n' > "$MODELS/Owner/S.lean"
  printf 'inductive Ast where\n  | lit\n' > "$MODELS/Empty/A.lean"
  printf 'def evalA (m : Mod) (fuel : Nat) (w : World) : Out := x\n' > "$MODELS/Twins/A.lean"
  printf 'def evalB (m : Mod) (fuel : Nat) (w : World) : Out := y\n' > "$MODELS/Twins/B.lean"

  check "tiers exclude Core"          "$(tiers | tr '\n' ' ' | sed 's/ *$//')" "Adoptr Empty Owner Shaper Twins"

  tier_monad Adoptr
  check "Core's SemMWith -> ADOPTED"  "$MONAD_KIND" "ADOPTED"
  check "  ...with a file:line"       "$(printf '%s' "$MONAD_AT" | grep -c 'Adoptr/M.lean:1')" "1"
  tier_monad Shaper
  check "a LOCAL SemM -> BY-SHAPE, not adopted" "$MONAD_KIND" "BY-SHAPE"
  check "  ...because the tier DEFINES the name" "$(defines_locally Shaper SemM && echo yes)" "yes"
  tier_monad Owner
  check "an own verdict type -> OWN"  "$MONAD_KIND" "OWN"
  tier_monad Empty
  check "no evaluator -> NONE"        "$MONAD_KIND" "NONE"

  check "the fit boundary: a run is found"  "$(tier_run Adoptr | grep -c 'M.lean:2')" "1"
  check "  ...and its absence is reported"  "$(tier_run Owner)" ""

  check "two defs sharing a SIGNATURE are twins" \
        "$(tier_twins Twins | awk -F'\t' '{print $1}')" "evalA / evalB"
  check "  ...and with no theorem naming both, adequacy is OWED" \
        "$(adequacy_for Twins "$(tier_twins Twins | awk -F'\t' '{print $1}')")" ""
  printf 'theorem agree : evalA = evalB := rfl\n' >> "$MODELS/Twins/B.lean"
  check "  ...but a theorem naming both is FOUND" \
        "$(adequacy_for Twins 'evalA / evalB' | grep -c 'Twins/B.lean')" "1"
  check "a MARKED second implementation is a real pair" \
        "$(is_second_impl_pair 'callIn / callInMono' && echo yes)" "yes"
  check "  ...an unmarked pair is only a CANDIDATE" \
        "$(is_second_impl_pair 'alloc / allocZeroed' && echo yes)" ""
  check "  ...and siblings are not a pair either" \
        "$(is_second_impl_pair 'envCreateImmutableBinding / envCreateMutableBinding' && echo yes)" ""
  check "a lone def is not a twin"    "$(tier_twins Adoptr)" ""

  printf 'def f (x : TM α) := tryCatch x (fun e => throw e)\n-- Loud must survive\n' \
    > "$MODELS/Adoptr/C.lean"
  check "uncatchability is found BY PATTERN" "$(tier_uncatch Adoptr | grep -c 'Adoptr')" "1"
  check "  ...and its absence reported"      "$(tier_uncatch Owner)" ""

  printf 'def r : X := .halt (.unsupported "m")\n' > "$MODELS/Adoptr/R.lean"
  tier_refusals Adoptr
  check "Core-channel refusals counted"      "$REF_CORE" "1"
  tier_refusals Owner
  check "a tier with none counts zero"       "$REF_CORE" "0"

  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

# -------------------------------------------------------------------- main
[ -d "$MODELS" ] || die "no LeanModels/ under '$CLONE'"

echo "substrate.sh — §3.4's contract, per tier, BY SHAPE"
echo "               measured at $(git -C "$CLONE" rev-parse --short HEAD 2>/dev/null || echo 'no git')"
echo
printf '  %-11s %-9s %-7s %-7s %-6s %s\n' TIER MONAD REFUSALS UNCATCH RUN ADEQUACY
printf '  %-11s %-9s %-7s %-7s %-6s %s\n' ----------- --------- ------- ------- ------ --------
for t in $(tiers); do
  [ -n "$ONLY" ] && [ "$t" != "$ONLY" ] && continue
  tier_monad "$t"; tier_refusals "$t"
  unc="$(tier_uncatch "$t")"; run="$(tier_run "$t")"
  tw="$(tier_twins "$t" | head -1 | awk -F'\t' '{print $1}')"
  if [ -n "$tw" ]; then
    if [ -n "$(adequacy_for "$t" "$tw")" ]; then
      adq="yes"
    elif is_second_impl_pair "$tw"; then
      adq="OWED ($tw)"
    else
      adq="TWINS? ($tw)"
    fi
  else
    adq="—"
  fi
  printf '  %-11s %-9s %2s/%-4s %-7s %-6s %s\n' \
    "$t" "$MONAD_KIND" "$REF_CORE" "$REF_LOCAL" \
    "$( [ -n "$unc" ] && echo yes || echo no )" \
    "$( [ -n "$run" ] && echo yes || echo NO )" "$adq"
  if [ -n "$ONLY" ]; then
    echo
    printf '    monad     %s\n' "${MONAD_AT:-none}"
    [ -n "$MONAD_TEXT" ] && printf '              %s\n' "$MONAD_TEXT"
    printf '    refusals  %s Core-channel site(s), %s local constructor(s)\n' "$REF_CORE" "$REF_LOCAL"
    printf '    uncatch   %s\n' "${unc:-no statement found}"
    printf '    run       %s\n' "${run:-NONE — the fit boundary (STMT-22) says say so}"
  fi
done
echo
echo "  REFUSALS is Core-channel sites / locally-declared constructors."
echo "  A row is evidence that nothing CONTRADICTS §3.4 here — never that §3.4"
echo "  holds. This greps text: BY-SHAPE is a claim about syntax and ADOPTED"
echo "  about an identifier, neither about a type-checked equality."
