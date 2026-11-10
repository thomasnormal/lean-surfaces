import LeanModels.Sv.Kernel.RunE
import LeanModels.Sv.Kernel.RunE1
import LeanModels.Sv.Kernel.Core0ObsWin
import LeanModels.Refine.RvfiE
import LeanModels.Refine.RvfiPorts

/-!
Regression for the single E core and observation interface. The standalone
E0 executor, clocked E1 executor, legacy transport proofs, and retirement
bridge must import together. Formerly this failed on duplicated declarations.
No source execution or real-core invariant is asserted by these typechecks.
-/

open LeanModels.Sv.Kernel LeanModels.Sv.Observe LeanModels.Refine

#check E0
#check E1
#check runE0_sound
#check runE1_sound
#check RvfiE.safe_of_invariant E0 (decode := RvfiPorts.decodePost "rvfi_")
#check RvfiE.safe_of_invariant (E1 "clk") (decode := RvfiPorts.decodePost "rvfi_")

-- The port helpers used by the former E0 copy reduce to the canonical ones.
example (d : LeanModels.Sv.Design2) : inputSigsE d = inputSigs d := rfl
example (d : LeanModels.Sv.Design2) : outputSigsE d = outputSigs d := rfl
example (e : Elab) : E0.iface e = ⟨inputSigs e.toDesign2, outputSigs e.toDesign2⟩ := rfl

#print axioms LeanModels.Refine.RvfiE.safe_of_invariant
#print axioms LeanModels.Sv.Kernel.exec_sound
#print axioms LeanModels.Sv.Kernel.exec1_sound
