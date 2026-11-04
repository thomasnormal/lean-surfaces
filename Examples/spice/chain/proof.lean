import LeanModels.Circuit
import LeanModels.Python.Surface

namespace Examples.spice.chain.proof

open LeanModels.Circuit

load_circuit chainDeck from "Examples/spice/chain/chain.cir"

private abbrev p0 : Fin 2 := ⟨0, by decide⟩
private abbrev p1 : Fin 2 := ⟨1, by decide⟩

/-- Checked leaf block obtained from the parsed `.subckt attn`, not re-entered
as Lean circuit data. -/
def attn : DCBlock := subcircuit! chainDeck "attn"

theorem attn_is_extracted :
    attn.name = "attn" ∧ attn.portNames = #["a", "b"] := by
  exact ⟨rfl, rfl⟩

/-- Exact two-port admittance of the L-section. -/
def attnContract : PortContract 2 :=
  { Y := fun row col =>
      if row = p0 then
        if col = p0 then 1 / 1000 else -1 / 1000
      else if col = p0 then -1 / 1000 else 7 / 6000
    J := fun _ => 0 }

private def attnAssignment (voltage : Vec 2) : DCAssignment :=
  { voltages := #[voltage p0, voltage p1, 0]
    currents := #[
      (voltage p0 - voltage p1) / 1000,
      voltage p1 / 6000] }

private theorem vec2_ext {left right : Vec 2}
    (h0 : left p0 = right p0) (h1 : left p1 = right p1) : left = right := by
  funext i
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with hi | hi
  · have : i = p0 := by apply Fin.ext; exact hi
    subst i
    exact h0
  · have : i = p1 := by apply Fin.ext; exact hi
    subst i
    exact h1

/-- The section contract follows from the two resistor laws and boundary KCL
of the checked source block. -/
theorem section_contract :
    HasExactContract attn.PortBehavior attnContract := by
  constructor
  · intro voltage current behavior
    rcases behavior with
      ⟨_, _, assignment, _, _, hground, hdevices, _, hports, hkcl⟩
    have hr1 := hdevices
      (.resistor ⟨0⟩ ⟨0⟩ ⟨1⟩ 1000) (by simp [attn])
    have hr2 := hdevices
      (.resistor ⟨1⟩ ⟨1⟩ ⟨2⟩ 6000) (by simp [attn])
    have hv0 := hports p0
    have hv1 := hports p1
    have hi0 := hkcl p0
    have hi1 := hkcl p1
    simp [attn, DCBlock.portNode,
      DCCircuit.kcl, DCDevice.currentLeaving, DCDevice.positive,
      DCDevice.negative, DCDevice.id, DCDevice.lawHolds,
      DCAssignment.voltage, DCAssignment.current] at hground hr1 hr2 hv0 hv1 hi0 hi1
    apply vec2_ext
    · simp [attnContract, PortContract.apply, matVec, dot]
      grind
    · simp [attnContract, PortContract.apply, matVec, dot]
      grind
  · intro voltage current hcurrent
    refine ⟨by rfl, ?_, attnAssignment voltage,
      by rfl, by rfl, ?_, ?_, ?_, ?_, ?_⟩
    · unfold attn
      simp [DCCircuit.isValid, DCDevice.id,
        DCDevice.positive, DCDevice.negative]
    · simp [attn, attnAssignment, DCAssignment.voltage]
    · intro device hmember
      simp [attn] at hmember
      rcases hmember with rfl | rfl <;>
        simp [attnAssignment, DCDevice.lawHolds,
          DCAssignment.voltage, DCAssignment.current]
    · intro node hnode hinternal
      rcases node with ⟨index⟩
      simp [attn, DCCircuit.nodes] at hnode
      simp [DCBlock.IsInternalNode, attn] at hinternal
      interval_cases index <;> simp_all
    · intro i
      have hi : i = p0 ∨ i = p1 := by
        have : i.val = 0 ∨ i.val = 1 := by omega
        rcases this with h | h
        · left; apply Fin.ext; exact h
        · right; apply Fin.ext; exact h
      rcases hi with rfl | rfl <;>
        simp [attn, DCBlock.portNode,
          attnAssignment, DCAssignment.voltage]
    · intro i
      have hc := congrFun hcurrent i
      have hi : i = p0 ∨ i = p1 := by
        have : i.val = 0 ∨ i.val = 1 := by omega
        rcases this with h | h
        · left; apply Fin.ext; exact h
        · right; apply Fin.ext; exact h
      rcases hi with rfl | rfl
      · simp [attn, DCBlock.portNode,
          attnAssignment, DCCircuit.kcl, DCDevice.currentLeaving,
          DCDevice.positive, DCDevice.negative, DCDevice.id,
          DCAssignment.current, attnContract, PortContract.apply,
          matVec, dot] at hc ⊢
        grind
      · simp [attn, DCBlock.portNode,
          attnAssignment, DCCircuit.kcl, DCDevice.currentLeaving,
          DCDevice.positive, DCDevice.negative, DCDevice.id,
          DCAssignment.current, attnContract, PortContract.apply,
          matVec, dot] at hc ⊢
        grind

/-- Generic contract composition eliminates the shared node without reopening
either section implementation. -/
theorem two_section_contract :
    HasExactContract
      (CascadeRelation attn.PortBehavior attn.PortBehavior)
      (cascade attnContract attnContract) := by
  apply compose_contracts section_contract section_contract
  norm_num [cascadeDenominator, attnContract]

/-- Two-component vector constructor used at a cascade boundary. -/
def pair2 (first second : Rat) : Vec 2
  | i => if i = p0 then first else second

/-- Exact boundary behavior of `sections` attenuators followed by the matched
3k termination. The recursive clause wires adjacent ports with equal voltage
and opposite currents; no internal assignment escapes the section contract. -/
def LoadedChain : Nat → Rat → Rat → Rat → Prop
  | 0, input, output, inputCurrent =>
      output = input ∧ inputCurrent = input / 3000
  | sections + 1, input, output, inputCurrent =>
      ∃ shared outputCurrent,
        attn.PortBehavior (pair2 input shared)
          (pair2 inputCurrent outputCurrent) ∧
        LoadedChain sections shared output (-outputCurrent)

/-- Contract of an arbitrary matched cascade. This is the compositional
showpiece: one local `section_contract` proof is consumed at every induction
step, while the conclusion mentions only boundary voltage/current. -/
theorem chain_contract (sections : Nat) (input output inputCurrent : Rat) :
    LoadedChain sections input output inputCurrent ↔
      output = (2 / 3 : Rat) ^ sections * input ∧ inputCurrent = input / 3000 := by
  induction sections generalizing input output inputCurrent with
  | zero => simp [LoadedChain]
  | succ sections ih =>
      constructor
      · rintro ⟨shared, outputCurrent, hsection, htail⟩
        have hs := section_contract.sound _ _ hsection
        have hs0 := congrFun hs p0
        have hs1 := congrFun hs p1
        have ht := (ih shared output (-outputCurrent)).mp htail
        rcases ht with ⟨hout, hload⟩
        constructor
        · simp [pair2, attnContract, PortContract.apply, matVec, dot] at hs0 hs1
          rw [hout]
          simp [Rat.pow_succ]
          grind
        · simp [pair2, attnContract, PortContract.apply, matVec, dot] at hs0 hs1
          grind
      · rintro ⟨hout, hin⟩
        let shared : Rat := (2 / 3) * input
        let outputCurrent : Rat := -(shared / 3000)
        have hcurr : pair2 inputCurrent outputCurrent =
            attnContract.apply (pair2 input shared) := by
          apply vec2_ext
          · simp [pair2, attnContract, PortContract.apply, matVec, dot,
              shared, outputCurrent]
            grind
          · simp [pair2, attnContract, PortContract.apply, matVec, dot,
              shared, outputCurrent]
            grind
        refine ⟨shared, outputCurrent,
          section_contract.realize _ _ hcurr, (ih shared output (-outputCurrent)).mpr ?_⟩
        constructor
        · simp [shared, Rat.pow_succ] at hout ⊢
          grind
        · simp [outputCurrent, shared]

/-- At 5V drive, every N-section matched chain has exact `(2/3)^N`
attenuation. -/
theorem chain_attenuates (sections : Nat) (output inputCurrent : Rat)
    (h : LoadedChain sections 5 output inputCurrent) :
    output = (2 / 3 : Rat) ^ sections * 5 :=
  (chain_contract sections 5 output inputCurrent).mp h |>.1

/-! An error-bounded reduced view uses the same compositional discipline but
does not pretend its nominal gain is exact. -/

noncomputable def ApproxAttenuatorContract : ScalarErrorContract :=
  {
    gain := 2 / 3
    bias := 0
    error := 1 / 100
    error_nonnegative := by norm_num }

noncomputable def ApproxAttenuatorBehavior : ScalarPortRelation :=
  ApproxAttenuatorContract.Admits

theorem approx_attenuator_contract :
    HasErrorBoundedContract ApproxAttenuatorBehavior
      ApproxAttenuatorContract := by
  constructor
  · intro input output h
    exact h
  · intro input
    refine ⟨ApproxAttenuatorContract.apply input, ?_⟩
    simp [ApproxAttenuatorBehavior, ScalarErrorContract.Admits,
      ApproxAttenuatorContract]

theorem two_approx_attenuators_contract :
    HasErrorBoundedContract
      (SerialScalarRelation ApproxAttenuatorBehavior
        ApproxAttenuatorBehavior)
      (composeErrorContracts ApproxAttenuatorContract
        ApproxAttenuatorContract) :=
  compose_error_bounded_contracts approx_attenuator_contract
    approx_attenuator_contract

theorem two_approx_attenuators_error :
    (composeErrorContracts ApproxAttenuatorContract
      ApproxAttenuatorContract).error = (1 / 60 : ℝ) := by
  norm_num [composeErrorContracts, ApproxAttenuatorContract, abs_of_nonneg]

end Examples.spice.chain.proof
