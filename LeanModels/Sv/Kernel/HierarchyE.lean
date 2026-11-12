import LeanModels.Sv.Kernel.Core0E
import LeanModels.Sv.Hier2

/-!
# Hierarchical designs at the E boundary

`PDesign.instantiateH` performs the IEEE module-elaboration step: parameter
overrides are evaluated at the instance, child declarations and processes keep
their source names under the instance prefix, and port connections remain the
continuous assignments prescribed by §23.3.3.  This file is the E entry for
that already source-shaped elaboration.  It executes the resulting
`Design2` through `Elab`/`Core0E`; it does not call `run2` or the memory route,
and it adds no statement constructor or lowering pass.

The wrapper is deliberately a small boundary adapter.  E's existing slot
executor remains the semantics and retains its process-atomic schedule and
four-state net initialization.  A hierarchy is admitted only when the normal
hierarchical elaborator returns a design whose E processes all execute; a
refusal remains loud and fuel exhaustion remains a timeout.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

private def closeE (E : Elab) (fuel : Nat) (c : Config) : Res Config :=
  match exec E σ_src fuel c with
  | .closed c' => .ok c'
  | .outOfBudget _ => .timeout
  | .refused r => .unsupported (LeanModels.Loud.observable r).2

private def rowsE (E : Elab) (fuel : Nat) : Config → List SvState → Res (List SvState)
  | c, [] => .ok []
  | c, input :: rest => do
      let c' ← closeE E fuel (Config.nextSlot E c input)
      let tail ← rowsE E fuel c' rest
      .ok (E.view c'.store :: tail)
termination_by _ rest => rest.length

/-- Run a source-shaped hierarchical design through canonical E.  The first
    row opens time zero; subsequent rows are input events for the next slot.
    The returned rows are E's complete name-keyed state after each closed
    slot, including instance-prefixed child signals. -/
def runHierarchyE (d : PDesign) (lib : List PDesign) (args : List Int)
    (fuel : Nat) (inputs : List SvState) : Res (List SvState) := do
  let d2 ← d.instantiateH lib args (PDesign.surfaceFuel args)
  let E := Elab.ofDesign2 d2
  match inputs with
  | [] => .ok []
  | first :: rest =>
      let c ← closeE E fuel (Config.start E first)
      let tail ← rowsE E fuel c rest
      .ok (E.view c.store :: tail)

end LeanModels.Sv.Kernel
