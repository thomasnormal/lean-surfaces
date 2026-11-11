import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.Core1Elab
import LeanModels.Sv.Kernel.Core1Obs

/-!
F2 seed over the actual loaded `clk_cnt` RTL.  The invariant here is the
E-state typing invariant: every declaration keeps its declared width,
signedness, and 4-state boundary after every closed process-atomic slot.  It
is deliberately stated over `Elab1`/`Config1`, rather than over a hand-written
counter, so the source envelope and E edge executor are in the theorem's
trusted path.  A value-level occupancy/property invariant can build on this
same slot theorem once the observation contract for the target is selected.
-/

namespace Examples.«system-verilog».sem2.clk_cnt_e.proof

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

load_design_sv2 clkCnt from
  "Examples/system-verilog/sem2/clk_cnt/clk_cnt.sv.json"

local macro "normalize_clk_cnt" : tactic => `(tactic|
  simp only [clkCnt.sem,
    PDesign.instantiateGDAlias2, PDesign.instantiateGD2, PDesign.instantiateG2,
    PDesign.instantiate2, PDesign.instantiate2From,
    clkCnt.pdesign, expandList2, List.map, instProcess2, instStmt2,
    instStmts2, fitExpr2.eq_def, instExpr2.eq_def, caseWidth2,
    List.foldl, selfWidth2, rigidMax2, Design2.aliasGuard,
    Array.toList_map])

def requireEdge (d : Design2) : Elab1 :=
  match Elab1.ofEdgeDesign2 d with
  | .ok E => E
  | .error msg =>
      { decls := d.decls, name := d.name,
        procs := #[FF.mk "" (none : Option String)
          (.unsupported "edge elaboration" msg) .posedge .alwaysFF] }

def edge : Elab1 := requireEdge (clkCnt.sem 4)

#guard match Elab1.ofEdgeDesign2 (clkCnt.sem 4) with
  | .ok _ => true
  | .error _ => false
#guard edge.procs.size == 1
#guard edge.okB && edge.oneWriterB && edge.noEdgeB
#guard (edge.decls.toList.map Decl.name).Nodup

theorem edge_profile : EdgeProfile edge := by
  apply EdgeProfile.ofChecks
  all_goals
    try unfold AllFour
    unfold edge requireEdge
    normalize_clk_cnt
    decide +kernel

theorem reset_base : edge.base.Typed (Config1.init edge).store := by
  change edge.base.Typed edge.base.initStore
  exact Elab.typed_initStore edge.base

/- Every closed E slot preserves the invariant from any typed predecessor.
   `Steps1.typed` is the inductive one-cycle preservation theorem, and the
   profile supplies progress for every legal Choice. -/
theorem typed_after_closed_slot {ch : Choice} {s : Store} {entry : SvState}
    {c' : Config1} (hT : edge.base.Typed s)
    (h : SlotCloses1 edge ch (Config1.nextSlot edge
      { store := s, active := [], nba := [], k := 0 } entry) c') :
    edge.base.Typed c'.store := by
  exact h.1.typed (hT.applyInputs entry)

theorem typed_after_any_profile_slot {ch : Choice} {s : Store} {entry : SvState}
    (hT : edge.base.Typed s) :
    ∃ c', SlotCloses1 edge ch
      (Config1.nextSlot edge { store := s, active := [], nba := [], k := 0 } entry) c' ∧
      edge.base.Typed c'.store := by
  exact closes1 edge_profile ch hT entry

end Examples.«system-verilog».sem2.clk_cnt_e.proof
