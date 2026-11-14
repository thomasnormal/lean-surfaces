import Examples.«system-verilog».ripple_add.gen
import LeanModels.Sv.Kernel.ArrayFast

/-!
# Kernel-cheap E receipt for the ripple adder

The source-shaped ripple vocabulary from `gen.lean` is instantiated at N=8
without unrolling the family definition.  `fastRun` keeps flat continuous
assignment cells in an array while retaining the same E expression evaluator;
this receipt checks the full-carry row in the kernel and records its expected
sum/carry observation.
-/

namespace Examples.«system-verilog».ripple_add.array_fast

open LeanModels.Sv
open LeanModels.Sv.Kernel
open Examples.«system-verilog».ripple_add.gen

private def d : Design2 :=
  { name := "ripple_add_fast"
    decls := (rippleDecls 8).toArray
    processes := (rippleProcs 8).toArray }

private def E : Elab := Elab.ofDesign2 d

private def stimulus : List SvState :=
  [[("a", .ofNat 8 255), ("b", .ofNat 8 1), ("cin", .ofNat 1 0)]]

private def observed : Bool :=
  match fastRun E σ_src 1000 stimulus with
  | .ok [row] =>
      let view := E.view row.store
      SvState.showSignal view "s" == "00000000" &&
        SvState.showSignal view "cout" == "1"
  | _ => false

#guard observed

/-! A source-order fold is included only as a kernel-cost probe.  It is not
the E scheduler and is not exposed as a semantic runner; the exact E route
above remains `fastRun`.  The fold gives the N=8 store benchmark a cheap
kernel check while the schedule-independent refinement is still pending. -/

private def sourcePass : List ProcId → FastConfig → Res FastConfig
  | [], c => .ok c
  | p :: ps, c =>
      match E.procs[p]? with
      | some (.assign t e) => do
          let cells ← fastActivateAssign E c t e
          sourcePass ps { c with cells, active := [] }
      | _ => .unsupported "source-order probe requires continuous assignments"

private def sourceRounds : Nat → FastConfig → Res FastConfig
  | 0, c => .ok c
  | n + 1, c =>
      match sourcePass (List.range E.procs.size) c with
      | .ok c' => sourceRounds n c'
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

private def sourceObserved : Bool :=
  match stimulus with
  | entry :: _ =>
      match sourceRounds 12 (FastConfig.ofConfig E (Config.start E entry)) with
      | .ok c =>
          let view := E.view c.store
          SvState.showSignal view "s" == "00000000" &&
            SvState.showSignal view "cout" == "1"
      | _ => false
  | [] => false

example : sourceObserved = true := by decide +kernel

end Examples.«system-verilog».ripple_add.array_fast
