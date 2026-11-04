import Examples.«system-verilog».ripple_add.comb_view
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic

/-!
# `sv_equations`: refusals, with the mathematical content that is missing

* the settled-state hypotheses (`CombEqs`, `StateShape`) and the structural proofs (`CombDesign`,
  `Acyclic`) are the tactic's input: a missing one is named;
* a design outside the fragment of `PDesign.summary` (here a dynamic write, `comb_view.badDyn`) is
  refused with the site;
* a right-hand side outside the fragment of `sv_equations` (here an `x` literal: `x` would make the
  Boolean equations false) is refused at the decidable check;
* a design with a 2-state (`bit`) declaration is outside the four-state fragment of the comb proof
  layer (`CombDesign.inFourState`, `CombView.declOf?`) and is refused by both tactics, naming the
  declaration: `neg/two_state_and.sv` (all ports `bit`), `neg/two_state_out.sv` (four-state inputs,
  the output `bit`, so the assign carries a `Squash2`).
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».ripple_add.gen
open Examples.«system-verilog».ripple_add.comb_view (badDyn)

namespace Examples.«system-verilog».ripple_add.comb_errors

/--
error: sv_equations: no hypothesis `CombEqs (X.sem N) st` in the context (the settled state: use `Models2.of_comb_pointwise` and `intro st heqs hsh …`)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (st : SvState) : True := by
  sv_equations
  trivial

/--
error: sv_equations: no hypothesis `Acyclic (X.sem N)` in the context (prove it with `sv_structure (rank := …)`)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (st : SvState) (heqs : CombEqs (ripple_add.sem N) st)
    (hsh : StateShape (ripple_add.sem N) st) (hc : CombDesign (ripple_add.sem N)) : True := by
  sv_equations
  trivial

/--
error: sv_equations: outside the supported fragment — site `g_bit#0`: write to `s[…]` has a non-affine (dynamic) index: the driven window cannot be determined
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (st : SvState)
    (heqs : CombEqs (badDyn.instantiateGD2 [(N : Int)]) st)
    (hsh : StateShape (badDyn.instantiateGD2 [(N : Int)]) st)
    (hc : CombDesign (badDyn.instantiateGD2 [(N : Int)]))
    (ha : Acyclic (badDyn.instantiateGD2 [(N : Int)])) : True := by
  sv_equations
  trivial

/-- The sum cell XORs with an `x` literal. -/
def sumX : PProcess :=
  .assignL (.bitSel "s" (.genvarRef "i"))
    (.binary (.m0 .xor) (.bitSel (.ident "a") (.genvarRef "i")) (.lit ⟨#[Logic.lx]⟩))

def badX : PDesign :=
  { ripple_add.pdesign with generates :=
    [.genFor (some "g_bit") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
      (.unary .inc (.genvarRef "i")) (some 4) ([sumX, carryT].map GenItem.process)] }

-- (the refusal message names the fragment; the decidable check's own report is long, so only
-- the failure is pinned)
example (N : Nat) (hN : 1 ≤ N) (st : SvState)
    (heqs : CombEqs (badX.instantiateGD2 [(N : Int)]) st)
    (hsh : StateShape (badX.instantiateGD2 [(N : Int)]) st)
    (hc : CombDesign (badX.instantiateGD2 [(N : Int)]))
    (ha : Acyclic (badX.instantiateGD2 [(N : Int)])) : True := by
  fail_if_success sv_equations
  trivial

/-! ## A 2-state declaration is outside the four-state fragment -/

load_design_sv2 two_state_and from "Examples/system-verilog/ripple_add/neg/two_state_and.sv.json"
load_design_sv2 two_state_out from "Examples/system-verilog/ripple_add/neg/two_state_out.sv.json"

/--
error: sv_structure: outside the supported fragment — declaration `a` is signed or 2-state (outside the v1 fragment: the summary's declarations are unsigned 4-state)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (two_state_and.sem N) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — declaration `y` is signed or 2-state (outside the v1 fragment: the summary's declarations are unsigned 4-state)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (two_state_out.sem N) := by
  sv_structure

/--
error: sv_equations: outside the supported fragment — declaration `a` is signed or 2-state (outside the v1 fragment: the summary's declarations are unsigned 4-state)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (st : SvState)
    (heqs : CombEqs (two_state_and.sem N) st) (hsh : StateShape (two_state_and.sem N) st)
    (hc : CombDesign (two_state_and.sem N)) (ha : Acyclic (two_state_and.sem N)) : True := by
  sv_equations
  trivial

/--
error: sv_equations: outside the supported fragment — declaration `y` is signed or 2-state (outside the v1 fragment: the summary's declarations are unsigned 4-state)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (st : SvState)
    (heqs : CombEqs (two_state_out.sem N) st) (hsh : StateShape (two_state_out.sem N) st)
    (hc : CombDesign (two_state_out.sem N)) (ha : Acyclic (two_state_out.sem N)) : True := by
  sv_equations
  trivial

end Examples.«system-verilog».ripple_add.comb_errors
