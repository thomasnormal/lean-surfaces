import LeanModels.Spice.Surface
import LeanModels.Spice.Cmos
import LeanModels.Spice.Mos1Logic

namespace Examples.spice.and_gate.proof

open LeanModels.Spice

load_netlist andGateDeck from "Examples/spice/and_gate/and_gate.json"

/-- A reusable AND-block theorem derived only from the six MOS switch laws. -/
theorem cmos_and_from_device_laws
    {left right nand series output vdd ground : Bool}
    (hlaws : CmosAndDeviceLaws left right nand series output vdd ground)
    (hvdd : vdd = true) (hground : ground = false) :
    output = Bool.and left right := by
  rcases left with _ | _ <;> rcases right with _ | _ <;>
    simp [CmosAndDeviceLaws] at hlaws ⊢ <;> grind

/-- A satisfying internal-node assignment for each Boolean input vector. -/
private def andState (left right : Bool) : LogicState :=
  { level := fun node =>
      if node == "vdd" then true
      else if node == "a" then left
      else if node == "b" then right
      else if node == "nand" then !(left && right)
      else if node == "nseries" then left && !right
      else if node == "out" then left && right
      else false }

private theorem andGateDeviceLaws (state : LogicState)
    (hsatisfies : SwitchSatisfies andGateDeck state) :
    CmosAndDeviceLaws
      (state.level "a") (state.level "b")
      (state.level "nand") (state.level "nseries")
      (state.level "out") (state.level "vdd") (state.level "0") := by
  simpa [SwitchSatisfies, flattenSwitch, flattenSwitchCards, flattenBudget,
    SwitchCardsSatisfy, SwitchCardLaw, MosfetSwitchLaw,
    Netlist.findMosModel, andGateDeck, renameElement, renameMosfet,
    renameNode, lookupRename, qualify, CmosAndDeviceLaws] using hsatisfies

/-- The extracted six-transistor CMOS network implements Boolean AND under
the ideal-switch MOS semantics. -/
theorem cmos_and_correct :
    BinaryGateContract andGateDeck "a" "b" "out" (· && ·) := by
  intro left right
  constructor
  · intro state hsatisfies hdrives
    have hout := cmos_and_from_device_laws
      (andGateDeviceLaws state hsatisfies) hdrives.2.1 hdrives.1
    simpa [hdrives.2.2.1, hdrives.2.2.2] using hout
  · refine ⟨andState left right, ?_, ?_⟩
    · rcases left with _ | _ <;> rcases right with _ | _ <;>
        simp [SwitchSatisfies, flattenSwitch, flattenSwitchCards,
          flattenBudget, SwitchCardLaw, MosfetSwitchLaw,
          SwitchCardsSatisfy, Netlist.findMosModel, andGateDeck, andState,
          renameElement, renameMosfet, renameNode, lookupRename, qualify]
    · simp [DrivesTwo, andState]

/-! ## Ngspice MOS Level 1 proof -/

private def andMos1Flat : Netlist :=
  { andGateDeck with cards := andGateDeck.cards.pop }

private theorem andMos1_flatten :
    flattenSwitch andGateDeck = .ok andMos1Flat := by
  rfl

private theorem andMos1_cards :
    andMos1Flat.cards.toList = andGateDeck.cards.toList.dropLast := by
  rfl

private noncomputable def nCurrent (vgs vds : ℝ) : ℝ :=
  mos1ForwardCurrent
    { polarity := .nmos, threshold := 1, beta := 1 / 10000, lambda := 0 }
    vgs vds

private noncomputable def pCurrent (vsg vsd : ℝ) : ℝ :=
  mos1ForwardCurrent
    { polarity := .pmos, threshold := 1, beta := 1 / 20000, lambda := 0 }
    vsg vsd

/-- KCL at the three internal nodes, reduced from the literal extracted deck.
The coefficients come from its exact `KP`, `VTO`, and `LAMBDA` parameters. -/
private theorem andMos1_equations (state : Mos1CircuitState)
    (hs : Mos1Satisfies andGateDeck state)
    (hb : Mos1WithinSupply andGateDeck state) :
    (0 ≤ state.voltage "nand" ∧ state.voltage "nand" ≤ 5) ∧
    (0 ≤ state.voltage "nseries" ∧ state.voltage "nseries" ≤ 5) ∧
    (0 ≤ state.voltage "out" ∧ state.voltage "out" ≤ 5) ∧
    (-pCurrent (state.voltage "vdd" - state.voltage "a")
          (state.voltage "vdd" - state.voltage "nand") +
        -pCurrent (state.voltage "vdd" - state.voltage "b")
          (state.voltage "vdd" - state.voltage "nand") +
        nCurrent (state.voltage "a" - state.voltage "nseries")
          (state.voltage "nand" - state.voltage "nseries") = 0) ∧
    (-nCurrent (state.voltage "a" - state.voltage "nseries")
          (state.voltage "nand" - state.voltage "nseries") +
        nCurrent (state.voltage "b" - state.voltage "0")
          (state.voltage "nseries" - state.voltage "0") = 0) ∧
    (-pCurrent (state.voltage "vdd" - state.voltage "nand")
          (state.voltage "vdd" - state.voltage "out") +
        nCurrent (state.voltage "nand" - state.voltage "0")
          (state.voltage "out" - state.voltage "0") = 0) := by
  unfold Mos1Satisfies at hs
  unfold Mos1WithinSupply at hb
  rw [andMos1_flatten] at hs hb
  rcases hs with ⟨_, _, hkcl⟩
  have hnand := hkcl "nand" (by decide) (by decide)
  have hnseries := hkcl "nseries" (by decide) (by decide)
  have hout := hkcl "out" (by decide) (by decide)
  have bnand := hb "nand" (by decide)
  have bnseries := hb "nseries" (by decide)
  have bout := hb "out" (by decide)
  unfold mos1Kcl at hnand hnseries hout
  rw [andMos1_cards] at hnand hnseries hout
  simp [andGateDeck, mos1CardCurrentLeaving, mos1DrainCurrent] at hnand hnseries hout
  simp [andMos1Flat, andGateDeck, Netlist.findMosModelCard,
    Mos1Params.ofModel?, MosModel.parameter?, List.findSome?] at hnand hnseries hout
  exact ⟨bnand, bnseries, bout,
    by simpa [nCurrent, pCurrent] using hnand,
    by simpa [nCurrent] using hnseries,
    by simpa [nCurrent, pCurrent] using hout⟩

/-- The extracted six-transistor deck implements AND directly from the
ngspice Level-1 channel equations, voltage-source laws, and KCL. The supply
envelope is an explicit premise rather than an unproved device abstraction. -/
theorem cmos_and_mos1_correct :
    Mos1BinaryGateContract andGateDeck "a" "b" "out" (· && ·) := by
  intro left right state hs hb hd
  rcases andMos1_equations state hs hb with
    ⟨bnand, bnseries, bout, hnand, hnseries, hout⟩
  rcases hd with ⟨hground, hvdd, hleft, hright⟩
  simp only [hground, hvdd, hleft, hright] at hnand hnseries hout
  apply mos1_and_from_equations
  exact ⟨bnand, bnseries,
    ⟨bout, by
      simpa [nCurrent, pCurrent, mos1NCurrent, mos1PCurrent] using hout⟩,
    by simpa [nCurrent, pCurrent, mos1NCurrent, mos1PCurrent] using hnand,
    by simpa [nCurrent, mos1NCurrent] using hnseries⟩

end Examples.spice.and_gate.proof
