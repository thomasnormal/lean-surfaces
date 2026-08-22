#!/usr/bin/env bash
# tools/new-proof.sh — a proof SCAFFOLD, with the laws that shape it inline.
#
# WHY THIS FILE EXISTS.  Four shapes recur, and each has a trap that a lane
# rediscovers the expensive way.  `BoundRefines` was REFUTED at every depth
# for every value function because a premise quantified over what the shipped
# code constrains (docs/backlog.md §L26).  A fuel NUMERAL in a hypothesis made
# a whole chain vacuous, twice over (§L24).  A joined FoldInv was nearly
# shipped as a headline while being about 3.5% of cuts
# (docs/backlog/sunfish-rtrack.md 2026-08-22-sunfish-rtrack-4).  None of those
# announced themselves: §0.1 II(a) is why — a failed STATEMENT prints "does
# not depend on any axioms", cleaner than the truth.
#
# So the laws travel WITH the shape, at the moment the statement is written,
# which is the only moment they are cheap.  The prose lives in
# docs/statement-cookbook.md; these are its four most-used entries as
# something you can paste.
#
# THE PLACEHOLDER IS AN UNKNOWN TACTIC ON PURPOSE.  `sorry` is forbidden
# outright (AGENTS.md § Never), and a scaffold that ELABORATES is a scaffold
# that can be committed unfinished.  `proof_goes_here` fails loudly, which is
# the failure direction this repo asks for everywhere else.
#
# USAGE
#   tools/new-proof.sh <kind> <name>        # to stdout
#   tools/new-proof.sh <kind> <name> --out FILE
#   tools/new-proof.sh --list
#   tools/new-proof.sh --self-test
#
# ZERO Lean execution: this prints text.  Safe outside a tenure (A11).

set -u

KINDS="gate altitude frame fold"
OUT=""
usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
die()   { echo "new-proof.sh: $*" >&2; exit 2; }

kind_blurb() {
  case "$1" in
    gate)     echo "a GATE — one program point, fuel threaded, premises in the residue's spelling" ;;
    altitude) echo "an ALTITUDE / @[spec] lemma — output-determined, named refusals, chosen by operand cost" ;;
    frame)    echo "a FRAME PREDICATE — name what the WORLD contributes, with stability lemmas" ;;
    fold)     echo "a FOLD / ROUND INVARIANT — one direction of a boundary, never both" ;;
    *)        echo "" ;;
  esac
}

template() {
  local name="$2"
  case "$1" in

  gate) cat <<TPL
/-! A GATE for \`$name\`.

    THE EXIT LAW (docs/backlog.md §L24; cookbook §5).  Fuel is a PARAMETER of
    the statement and the worlds are THREADED.  A fuel NUMERAL in a hypothesis
    does not say "some fuel", it says "five is enough" — and five was not.
      * MEASURE BEFORE YOU PREMISE (§L25 items 1-2): run the expression on the
        fixture and compare heap sizes FIRST; measure the minimum fuel before
        writing any numeral.  Eight seconds each, before a premise exists.
      * Prefer SYMBOLIC fuel in compositions (\`Fg + 3 + 2\`, not \`Fg + 6\`):
        an off-by-one then fails as an application type error naming both
        sides, instead of as a multi-minute \`whnf\` storm
        (tools/diagnose.sh --explain whnf-timeout).
      * A premise is NOT PAID until something DISCHARGES it (§L25 item 3).
        LAND THE CONSUMER IN THE SAME COMMIT, or the next pass inherits a
        theorem that may say nothing.
      * Conclude with the COMPUTED heap and spell each premise the way the
        tactic's residue leaves it, not the way the source reads (§L20).
      * If this gate is discharged through mvcgen: RECORD THE jp SETTING with
        the numbers, both ways.  A bare \`⊢ False\` in an unreachable branch is
        the splitter dropping the discriminant, and \`+jp\` is core's more
        conservative but slightly lossy encoding — it may be the SOURCE of the
        loss rather than its cure (docs/backlog/research.md
        2026-08-22-research-1).
-/
-- mvcgen config used: jp := <true|false>   -- and the VC count for each
theorem $name
    (F : Nat)                       -- fuel: a PARAMETER, never a hypothesis
    (w : <World>)                   -- the world is a FREE VARIABLE (§L26)
    (hw : <Frame> w)                -- what the world contributes, NAMED
    (hpre : <premise in the RESIDUE's spelling>) :
    ∃ w', <run> (F + <measured slack>) w <prog> = .ok w' <value> ∧ <Frame> w' := by
  proof_goes_here   -- REPLACE.  Unknown on purpose: this must not elaborate.

-- OWED IN THIS SAME COMMIT: the consumer that discharges \`hpre\`.
-- Until it exists, this gate is a premise nobody has paid.
TPL
  ;;

  altitude) cat <<TPL
/-! An ALTITUDE lemma for \`$name\`, registered with @[spec].

    WHY ALTITUDE (docs/backlog.md §L48 finding 2; §L61).  In a long chain the
    missing thing is an altitude lemma, and THE BUDGET KNOB IS THE WRONG KNOB:
    at 10x heartbeats one goal reported \`timeout at simp\` in 15 s and then
    \`timeout at whnf\` after two minutes; six altitude lemmas made it
    elaborate in under two seconds.

    WHICH OPERAND (the selection rule).  Lift the EXPENSIVE operand — the one
    whose residue the tactic would otherwise walk.  Altitude lemmas persist
    across a re-founding when their STATEMENT does not mention the
    interpreter; \`@[spec]\` is their registry (§L61, origin §L17).

    OUTPUT-DETERMINED, ALWAYS (docs/mvcgen-pilot.md §3.3, §5.2; cookbook §7).
    Bind the answer in the RESULT; never take it as an input the caller
    supplies.  With the answer as a parameter, mvcgen unified it against the
    LOOP ACCUMULATOR — wrong, type-correct, and it poisons every downstream
    VC.  Measured twice: 23 dependent-metavariable VCs became 12, and a second
    gate's went to 3, purely by moving the answer into the result binder.

    READ-ONLY?  \`Triple\` DOES NOT FRAME THE STATE (cookbook §16).  Assume
    \`st = st0\` and conclude \`... ∧ st = st0\`, or the read-only-ness you
    assumed is simply not in the statement.

    REFUSALS ARE NAMED (docs/mvcgen-pilot.md §1.4; cookbook §8).  Never a bare
    polymorphic \`throw\`: at this pin it leaves universe metavariables and the
    declaration is REJECTED OUTRIGHT.  Route through \`refuse\` / \`liftRes\`,
    each with its own @[spec] lemma.
-/
@[spec]
theorem $name (<args>) (<well-formedness, as a named structure>) :
    ⦃<precondition>⦄
      <primitive> <args>
    ⦃⇓ r => ⌜<the answer, BOUND IN THE RESULT> = r⌝⦄ := by
  proof_goes_here   -- REPLACE.  Unknown on purpose: this must not elaborate.

-- CHECK BEFORE LANDING: #print axioms $name  — and read the ERRORS first.
-- A failed STATEMENT prints "does not depend on any axioms" (§0.1 II(a)).
TPL
  ;;

  frame) cat <<TPL
/-! A FRAME PREDICATE for \`$name\`, in the \`PstAt\` shape.

    NAME WHAT THE WORLD CONTRIBUTES (docs/backlog/sunfish-rtrack.md
    2026-08-22-sunfish-rtrack-1 §1; cookbook §9).  One named predicate
    collecting exactly what the world supplies, plus a stability lemma per
    shape a step leaves.  It converts "does the value survive this step?" into
    "does the frame survive this step?" — a question about the HEAP rather
    than about the interpreter.

    RE-FOUNDING-PROOF vs INLINED.  Inlining the same world fact into each gate
    is provable, works, and DOES NOT TRANSPORT: an altitude lemma that names
    what the world contributes survives a definition swap, and a gate that
    inlines the same fact does not (Class 2 of 2026-08-22-sunfish-rtrack-3).
    Measured: before the frame, the residue obligation could not be stated
    without unfolding four theorem signatures; after, it is one line in the
    consumer's own vocabulary.

    THE WORLD IS A FREE VARIABLE (§L26; cookbook §11).  Do not pin an initial
    world, and do not hide it in an \`∃\`.  Quantifying over what the shipped
    code CONSTRAINS is how \`BoundRefines\` became false at every depth.
-/
def $name (w : <World>) : Prop :=
  <exactly what the world contributes — no more, no less>

-- One stability lemma per shape a step leaves.  @[spec] so they compose.
@[spec] theorem ${name}.push    : proof_goes_here
@[spec] theorem ${name}.append  : proof_goes_here
@[spec] theorem ${name}.update_ne : proof_goes_here

-- #guard the predicate SATISFIABLE on the shipped code before proving with it
-- (AGENTS.md § House rules: non-vacuity FIRST).
TPL
  ;;

  fold) cat <<TPL
/-! A FOLD / ROUND INVARIANT for \`$name\`, in the \`FoldInv\` shape.

    NEVER BAKE IN BOTH DIRECTIONS OF A BOUNDARY (docs/backlog/sunfish-rtrack.md
    2026-08-22-sunfish-rtrack-4; cookbook §4).  The fail-low arm needs
    \`value ≤ sc\`; the fail-high arm needs the exact converse.  Supplying BOTH
    asserts calmness — a real finding — but DEGENERATES the cut arm: under
    both premises a cut forces the stand-pat to have met the window unaided,
    which is 3.5% of cuts, never the 84% that cut on a searched move.  The
    joined theorem is true and about almost nothing, and it was nearly shipped
    as a headline.

    THE LAYERING.  A per-round PRIMITIVE, the accumulator fact DERIVED from
    it, and the schedule-level invariant stated over the primitive.  The
    invariant carries the ROUND obligation only; each exit's corollary takes
    the direction it needs.

    SHAPE (AGENTS.md § Failure modes; cookbook §20).  A top-level FLAT
    ∧-chain, so the loop tactic splits it into named hypotheses — \`grind\`
    e-matches from ATOMIC facts, not from conjunctions, so never re-conjoin
    what the splitter separated.  Append new conjuncts LAST, so existing
    projection paths survive.
-/
structure $name (<params>) (rounds : List <Round>) : Prop where
  sound  : <the accumulator fact, DERIVED>
  rounds : ∀ r ∈ rounds, <RoundOK> <params> r    -- the per-round PRIMITIVE
  attain : <the witness the exits need>

-- ONE direction per corollary — never both in the invariant.
theorem ${name}.fail_low  : proof_goes_here
theorem ${name}.fail_high : proof_goes_here
TPL
  ;;
  esac
}

# --------------------------------------------------------------- self-test
if [ "${1:-}" = "--self-test" ]; then
  ok=0; bad=0
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; \
            else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }
  # PRESENCE, not a line count: `grep -c` counts matching LINES, and this
  # test's first version failed three templates for containing a law TWICE.
  has() { if printf '%s' "$2" | grep -qF "$3"; then echo 1; else echo 0; fi; }

  for k in $KINDS; do
    t="$(template "$k" demo_name)"
    check "$k emits a template"            "$([ -n "$t" ] && echo yes)" "yes"
    check "$k names the subject"           "$(has x "$t" 'demo_name')" "1"
    check "$k carries a citation"          "$(printf '%s' "$t" | grep -qE 'docs/(backlog|mvcgen-pilot|sunfish-rtrack)|AGENTS\.md' && echo 1 || echo 0)" "1"
    check "$k has the loud placeholder"    "$(has x "$t" 'proof_goes_here')" "1"
    check "$k contains NO sorry"           "$(printf '%s' "$t" | grep -c 'sorry')" "0"
  done

  # The four laws the dispatch named, each present in the right template.
  check "gate: measure before premise"  "$(has x "$(template gate g)" 'MEASURE BEFORE YOU PREMISE')" "1"
  check "gate: same-commit consumer"    "$(has x "$(template gate g)" 'SAME COMMIT')" "1"
  check "gate: the jp setting recorded" "$(has x "$(template gate g)" 'RECORD THE jp SETTING')" "1"
  check "altitude: output-determined"   "$(has x "$(template altitude a)" 'OUTPUT-DETERMINED')" "1"
  check "altitude: named refusals"      "$(has x "$(template altitude a)" 'REFUSALS ARE NAMED')" "1"
  check "altitude: operand selection"   "$(has x "$(template altitude a)" 'WHICH OPERAND')" "1"
  check "frame: names the world's part"  "$(has x "$(template frame f)" 'NAME WHAT THE WORLD CONTRIBUTES')" "1"
  check "frame: stability lemmas @[spec]" "$(has x "$(template frame f)" '@[spec] theorem')" "1"
  check "fold: never both directions"   "$(has x "$(template fold d)" 'NEVER BAKE IN BOTH DIRECTIONS')" "1"

  check "an unknown kind emits nothing" "$(template nope n)" ""
  check "--list names four kinds"       "$(for k in $KINDS; do echo "$k"; done | grep -c .)" "4"
  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

if [ "${1:-}" = "--list" ]; then
  for k in $KINDS; do printf '%-10s %s\n' "$k" "$(kind_blurb "$k")"; done
  exit 0
fi

[ $# -ge 2 ] || usage
KIND="$1"; NAME="$2"; shift 2
while [ $# -gt 0 ]; do
  case "$1" in
    --out) OUT="${2:-}"; shift 2 ;;
    *)     die "unknown argument '$1'" ;;
  esac
done
[ -n "$(kind_blurb "$KIND")" ] || die "no kind '$KIND' — try --list"
case "$NAME" in ''|*[!A-Za-z0-9_.]*) die "a name must be [A-Za-z0-9_.]+" ;; esac

if [ -n "$OUT" ]; then
  [ -e "$OUT" ] && die "refusing to overwrite '$OUT'"
  template "$KIND" "$NAME" > "$OUT" || die "cannot write '$OUT'"
  echo "new-proof.sh: wrote $OUT ($KIND)"
else
  template "$KIND" "$NAME"
fi
