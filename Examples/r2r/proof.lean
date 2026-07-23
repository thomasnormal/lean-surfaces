import LeanModels.Spice.Surface

namespace Examples.r2r.proof

open LeanModels.Spice

load_netlist r2rDeck from "Examples/r2r/r2r.json"

private abbrev b0 : Fin 4 := ⟨0, by decide⟩
private abbrev b1 : Fin 4 := ⟨1, by decide⟩
private abbrev b2 : Fin 4 := ⟨2, by decide⟩
private abbrev b3 : Fin 4 := ⟨3, by decide⟩

def r2rBlock : Subckt :=
  { span := ⟨21, 30⟩, name := "r2r", ports := #["b3", "b2", "b1", "b0", "out"],
    body := #[
      .element ⟨.resistor, ⟨22, 22⟩, "rterm", "n0", "0", 2000⟩,
      .element ⟨.resistor, ⟨23, 23⟩, "rb0", "b0", "n0", 2000⟩,
      .element ⟨.resistor, ⟨24, 24⟩, "r01", "n0", "n1", 1000⟩,
      .element ⟨.resistor, ⟨25, 25⟩, "rb1", "b1", "n1", 2000⟩,
      .element ⟨.resistor, ⟨26, 26⟩, "r12", "n1", "n2", 1000⟩,
      .element ⟨.resistor, ⟨27, 27⟩, "rb2", "b2", "n2", 2000⟩,
      .element ⟨.resistor, ⟨28, 28⟩, "r23", "n2", "out", 1000⟩,
      .element ⟨.resistor, ⟨29, 29⟩, "rb3", "b3", "out", 2000⟩] }

theorem r2r_is_extracted : r2rDeck.subckts[0]? = some (.definition r2rBlock) := by
  rfl

def drive (bit : Bool) : Rat := if bit then 5 else 0

def binVal (bits : Fin 4 → Bool) : Rat :=
  (if bits b3 then 8 else 0) + (if bits b2 then 4 else 0) +
  (if bits b1 then 2 else 0) + (if bits b0 then 1 else 0)

def r2rCircuit (bits : Fin 4 → Bool) : Netlist :=
  { title := "parameterized extracted R-2R topology"
    subckts := #[.definition r2rBlock]
    cards := #[
      .element ⟨.vsource, ⟨31, 31⟩, "vb3", "d3", "0", drive (bits b3)⟩,
      .element ⟨.vsource, ⟨32, 32⟩, "vb2", "d2", "0", drive (bits b2)⟩,
      .element ⟨.vsource, ⟨33, 33⟩, "vb1", "d1", "0", drive (bits b1)⟩,
      .element ⟨.vsource, ⟨34, 34⟩, "vb0", "d0", "0", drive (bits b0)⟩,
      .xInstance ⟨⟨35, 35⟩, "x1", "r2r", #["d3", "d2", "d1", "d0", "out"]⟩,
      .op ⟨36, 36⟩] }

private def r2rFlat (bits : Fin 4 → Bool) : FlatNetlist :=
  { elements := #[
      ⟨.vsource, ⟨31, 31⟩, "vb3", "d3", "0", drive (bits b3)⟩,
      ⟨.vsource, ⟨32, 32⟩, "vb2", "d2", "0", drive (bits b2)⟩,
      ⟨.vsource, ⟨33, 33⟩, "vb1", "d1", "0", drive (bits b1)⟩,
      ⟨.vsource, ⟨34, 34⟩, "vb0", "d0", "0", drive (bits b0)⟩,
      ⟨.resistor, ⟨22, 22⟩, "x1.rterm", "x1.n0", "0", 2000⟩,
      ⟨.resistor, ⟨23, 23⟩, "x1.rb0", "d0", "x1.n0", 2000⟩,
      ⟨.resistor, ⟨24, 24⟩, "x1.r01", "x1.n0", "x1.n1", 1000⟩,
      ⟨.resistor, ⟨25, 25⟩, "x1.rb1", "d1", "x1.n1", 2000⟩,
      ⟨.resistor, ⟨26, 26⟩, "x1.r12", "x1.n1", "x1.n2", 1000⟩,
      ⟨.resistor, ⟨27, 27⟩, "x1.rb2", "d2", "x1.n2", 2000⟩,
      ⟨.resistor, ⟨28, 28⟩, "x1.r23", "x1.n2", "out", 1000⟩,
      ⟨.resistor, ⟨29, 29⟩, "x1.rb3", "d3", "out", 2000⟩] }

private theorem r2r_flatten (bits : Fin 4 → Bool) :
    flatten (r2rCircuit bits) = .ok (r2rFlat bits) := by
  rfl

/-- All sixteen drive vectors satisfy the exact DAC transfer formula. -/
theorem r2r_guarantee (bits : Fin 4 → Bool) :
    r2rCircuit bits ⊨dc { v, _i => v "out" = 5 * binVal bits / 16 } := by
  intro assignment h
  unfold SatisfiesNetlist at h
  rw [r2r_flatten] at h
  simp [Satisfies, r2rFlat, FlatNetlist.nodes, kclSum, currentInto,
    deviceLawHolds, drive] at h
  cases h0 : bits b0 <;> cases h1 : bits b1 <;>
    cases h2 : bits b2 <;> cases h3 : bits b3 <;>
    simp [binVal, h0, h1, h2, h3] at * <;> grind

end Examples.r2r.proof
