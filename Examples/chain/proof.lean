import LeanModels.Spice.Compose
import LeanModels.Spice.Surface

namespace Examples.chain.proof

open LeanModels.Spice

load_netlist chainDeck from "Examples/chain/chain.json"

private abbrev p0 : Fin 2 := ⟨0, by decide⟩
private abbrev p1 : Fin 2 := ⟨1, by decide⟩

/-- The extracted `attn` definition, named explicitly for contract proofs. -/
def attn : Subckt :=
  { span := ⟨29, 32⟩, name := "attn", ports := #["a", "b"],
    body := #[
      .element ⟨.resistor, ⟨30, 30⟩, "r1", "a", "b", 1000⟩,
      .element ⟨.resistor, ⟨31, 31⟩, "r2", "b", "0", 6000⟩] }

theorem attn_is_extracted : chainDeck.subckts[0]? = some (.definition attn) := by
  rfl

/-- Boundary node after a given number of sections. -/
def chainNode : Nat → String
  | 0 => "in"
  | index + 1 => "out" ++ toString (index + 1)

private def chainInstance (index : Nat) : Card :=
  .xInstance
    { span := ⟨0, 0⟩
      name := "x" ++ toString (index + 1)
      subckt := "attn"
      connections := #[chainNode index, chainNode (index + 1)] }

/-- An actual hierarchical SPICE AST family, built from `sections` instances
of the one extracted `attn` definition and its matched 3k termination. -/
def chain (sections : Nat) : Netlist :=
  let instances := (List.range sections).map chainInstance |>.toArray
  { title := "matched attenuator chain"
    subckts := #[.definition attn]
    cards :=
      #[.element ⟨.vsource, ⟨0, 0⟩, "v1", "in", "0", 5⟩] ++
      instances ++
      #[.element ⟨.resistor, ⟨0, 0⟩, "rterm", chainNode sections, "0", 3000⟩,
        .op ⟨0, 0⟩] }

/-- Exact two-port admittance of the L-section. -/
def attnContract : PortContract 2 :=
  { Y := fun row col =>
      if row = p0 then
        if col = p0 then 1 / 1000 else -1 / 1000
      else if col = p0 then -1 / 1000 else 7 / 6000
    J := fun _ => 0 }

private def attnAssignment (voltage : Vec 2) : Assignment :=
  { volt := fun node =>
      if node == "a" then voltage p0 else if node == "b" then voltage p1 else 0
    cur := fun _ => 0 }

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

/-- The section is proved once, independently of any surrounding chain. -/
theorem section_contract : HasContract attn attnContract := by
  constructor
  · intro voltage current behavior
    rcases behavior with ⟨_, flat, hflat, assignment, _, hports, _, _, hkcl⟩
    simp [attn, flattenLeafSubckt] at hflat
    change Except.ok { elements := #[
      ⟨.resistor, ⟨30, 30⟩, "r1", "a", "b", 1000⟩,
      ⟨.resistor, ⟨31, 31⟩, "r2", "b", "0", 6000⟩] } = .ok flat at hflat
    cases hflat
    have hv0 := hports p0
    have hv1 := hports p1
    have hi0 := hkcl p0
    have hi1 := hkcl p1
    simp [attn, Subckt.portName, kclSum, currentInto] at hv0 hv1 hi0 hi1
    apply vec2_ext
    · simp [attnContract, PortContract.apply, matVec, dot]
      grind
    · simp [attnContract, PortContract.apply, matVec, dot]
      grind
  · intro voltage current hcurrent
    refine ⟨by rfl, { elements := #[
        ⟨.resistor, ⟨30, 30⟩, "r1", "a", "b", 1000⟩,
        ⟨.resistor, ⟨31, 31⟩, "r2", "b", "0", 6000⟩] }, by rfl,
      attnAssignment voltage, ?_, ?_, ?_, ?_, ?_⟩
    · simp [attnAssignment]
    · intro i
      have hi : i = p0 ∨ i = p1 := by
        have : i.val = 0 ∨ i.val = 1 := by omega
        rcases this with h | h
        · left; apply Fin.ext; exact h
        · right; apply Fin.ext; exact h
      rcases hi with rfl | rfl <;> simp [attn, Subckt.portName, attnAssignment]
    · intro element hmem
      simp at hmem
      rcases hmem with rfl | rfl <;> trivial
    · intro node hinternal
      simp [IsInternalNode, attn, FlatNetlist.nodes] at hinternal
      rcases hinternal.1 with rfl | rfl | rfl <;> simp_all
    · intro i
      have hc := congrFun hcurrent i
      have hi : i = p0 ∨ i = p1 := by
        have : i.val = 0 ∨ i.val = 1 := by omega
        rcases this with h | h
        · left; apply Fin.ext; exact h
        · right; apply Fin.ext; exact h
      rcases hi with rfl | rfl
      · simp [attn, Subckt.portName, attnAssignment, kclSum, currentInto,
          attnContract, PortContract.apply, matVec, dot] at hc ⊢
        grind
      · simp [attn, Subckt.portName, attnAssignment, kclSum, currentInto,
          attnContract, PortContract.apply, matVec, dot] at hc ⊢
        grind

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
        PortBehavior attn (pair2 input shared) (pair2 inputCurrent outputCurrent) ∧
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

end Examples.chain.proof
