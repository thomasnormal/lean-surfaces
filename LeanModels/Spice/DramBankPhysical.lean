import LeanModels.Spice.DramBankDeck

/-!
# Source-projected 2x2 DRAM profile

The 2x2 deck has a specialized source-layout projection because it predates
the dimension-generic bank loader. Its circuit behavior is intentionally not
defined here: both the 2x2 and 256x32 examples use `DramBankCore`, so there is
only one physical read/write semantics and no topology-specific endpoint
contract in which a specification can be embedded.
-/

namespace LeanModels.Spice

noncomputable def DramBank2x2NominalProfile
    (layout : DramBank2x2Layout) : Prop :=
  ∀ row column,
    layout.array.cellInstance row column =
      { threshold := 1
        beta := 1 / 10000
        storageCapacitance := 3 / 100000000000000
        bitlineCapacitance := 3 / 10000000000000 }

noncomputable def DramBank2x2PeripheralProfile
    (layout : DramBank2x2Layout) : Prop :=
  layout.pThreshold = 1 ∧
    layout.pBeta = 1 / 20000 ∧
    layout.sensePThreshold = 1 ∧
    layout.sensePBeta = 1 / 10000

noncomputable def DramBank2x2FullProfile
    (layout : DramBank2x2Layout) : Prop :=
  DramBank2x2NominalProfile layout ∧
    DramBank2x2PeripheralProfile layout

end LeanModels.Spice
