/-
Examples/system-verilog/sem2/concat_add — the differential fixture of the
concatenated-target adder (`harness/sv/cases2.json` rows `concat_add`,
`concat_add_n1`, `concat_add_n8`: `run2` of THIS envelope against Icarus),
tied to the hand-built design family `caddDesign N` that
`LeanModels/Sv/Comb2ConcatExample.lean` proves correct for every `N`.

  concat_add.sv      — `assign {cout, s} = a + b + cin;` with `parameter N`
  concat_add.sv.json — generated envelope (extractors/sv/extract.py --top)
  agree.lean         — THIS FILE: the instantiated design IS `caddDesign N`
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Comb2ConcatExample
import LeanModels.Sv.Hier2Gen

/-!
# The SV source instantiates to the proved design

`load_design_sv2` turns the envelope into the family `concat_add.sem N`. At
every width checked below, its declarations are exactly `caddDesign N`'s and
its one process is exactly `.assign caddTarget (caddRhs N)` — the target
`{cout, s}` (`Lhs2.concat [.ident "cout", .ident "s"]`) and the right-hand
side `a + b + cin` with each operand zero-extended to the context width
`N + 1`. So the `∀ N` theorems of `Comb2ConcatExample` (`cadd_correct`,
`cadd_terminates`, …) are theorems about what this SV file instantiates to
at those widths, and the differential rows check the same design against a
real simulator.

These are `#guard` evaluations at concrete widths (`N = 1, 2, 4, 8, 32`), not
a symbolic-`N` instantiation theorem: the symbolic route
(`Gen2.lean`'s `PDesign.instantiate2_of_ok` recipe, as in
`Examples/system-verilog/ripple_add/gen.lean`) is the next step.
-/

namespace Examples.«system-verilog».sem2.concat_add.agree

open LeanModels.Sv LeanModels.Sv.Comb2ConcatExample

load_design_sv2 concat_add from "Examples/system-verilog/sem2/concat_add/concat_add.sv.json"

/-- The instantiated process list at width `N` is the proved design's one
assign. -/
def sameProcesses (N : Nat) : Bool :=
  match (concat_add.sem N).processes.toList with
  | [.assign t e] => t == caddTarget && e == caddRhs N
  | _ => false

/-- The instantiated declarations at width `N` are the proved design's. -/
def sameDecls (N : Nat) : Bool :=
  (concat_add.sem N).decls.toList == (caddDesign N).decls.toList

#guard [1, 2, 4, 8, 32].all fun N => sameProcesses N && sameDecls N

/-- **The one-driver rule from the comb profile** (`Hier2Gen.lean`,
`driversOk_of_combDesign`, 2026-10-28 WP2): the proved design
`caddDesign N` passes the guard `concat_add.sem` applies at every
parameter point (`PDesign.instantiateGD2`), for every `N ≥ 1`, straight
from `cadd_comb` — the comb profile's disjointness IS the rule, so no window
arithmetic is redone. With a symbolic instantiation theorem
(`concat_add.pdesign.instantiate2 [N] _ = .ok m`), the same bridge
(`PDesign.instantiateGD2_of_combDesign`) would give `concat_add.sem N = m`. -/
theorem cadd_driversOk (N : Nat) (hN : 1 ≤ N) :
    driversOk concat_add.pdesign.declNames concat_add.pdesign.inputNames
      (caddDesign N).processes.toList = true := by
  apply driversOk_of_combDesign (cadd_comb N)
  · intro i n lo w h
    rcases (cadd_writes.mp h).2 with h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  · have hin : concat_add.pdesign.inputNames = ["a", "b", "cin"] := rfl
    intro n hn
    rw [hin] at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;> simp [Design2.inputNames, caddDesign]

#print axioms cadd_driversOk

end Examples.«system-verilog».sem2.concat_add.agree
