import LeanModels.Circuit

namespace Examples.spice.r2r.proof

open LeanModels.Circuit

load_circuit r2rDeck from "Examples/spice/r2r/r2r.cir"

set_option maxHeartbeats 2000000

private abbrev b0 : Fin 4 := ⟨0, by decide⟩
private abbrev b1 : Fin 4 := ⟨1, by decide⟩
private abbrev b2 : Fin 4 := ⟨2, by decide⟩
private abbrev b3 : Fin 4 := ⟨3, by decide⟩

abbrev d3Node := (node! r2rDeck "d3").id
abbrev groundNode := (node! r2rDeck "0").id
abbrev d2Node := (node! r2rDeck "d2").id
abbrev d1Node := (node! r2rDeck "d1").id
abbrev d0Node := (node! r2rDeck "d0").id
abbrev n0Node := (node! r2rDeck "x1.n0").id
abbrev n1Node := (node! r2rDeck "x1.n1").id
abbrev n2Node := (node! r2rDeck "x1.n2").id
abbrev outputNode := (node! r2rDeck "out").id

abbrev vb3 := (device! r2rDeck "vb3").id
abbrev vb2 := (device! r2rDeck "vb2").id
abbrev vb1 := (device! r2rDeck "vb1").id
abbrev vb0 := (device! r2rDeck "vb0").id
abbrev rterm := (device! r2rDeck "x1.rterm").id
abbrev rb0 := (device! r2rDeck "x1.rb0").id
abbrev r01 := (device! r2rDeck "x1.r01").id
abbrev rb1 := (device! r2rDeck "x1.rb1").id
abbrev r12 := (device! r2rDeck "x1.r12").id
abbrev rb2 := (device! r2rDeck "x1.rb2").id
abbrev r23 := (device! r2rDeck "x1.r23").id
abbrev rb3 := (device! r2rDeck "x1.rb3").id

def drive (bit : Bool) : ℝ := if bit then 5 else 0

def binVal (bits : Fin 4 → Bool) : ℝ :=
  (if bits b3 then 8 else 0) + (if bits b2 then 4 else 0) +
  (if bits b1 then 2 else 0) + (if bits b0 then 1 else 0)

/-- The literal deck supplies topology and nominal resistor values. Input
drivers are run-environment values, so one component supports all vectors. -/
noncomputable def r2rWorld (bits : Fin 4 → Bool) : DCRunWorld :=
  let nominal := r2rDeck_dc.rawNominalWorld
  { fabricated := nominal.fabricated
    environment := {
      sourceVoltage := fun id =>
        if id = vb3 then drive (bits b3)
        else if id = vb2 then drive (bits b2)
        else if id = vb1 then drive (bits b1)
        else if id = vb0 then drive (bits b0)
        else nominal.environment.sourceVoltage id }
    noise := ()
    discrepancy := () }

@[simp] theorem r2rWorld_vb3 (bits : Fin 4 → Bool) :
    (r2rWorld bits).environment.sourceVoltage ⟨0⟩ = drive (bits b3) := by
  simp [r2rWorld]

@[simp] theorem r2rWorld_vb2 (bits : Fin 4 → Bool) :
    (r2rWorld bits).environment.sourceVoltage ⟨1⟩ = drive (bits b2) := by
  simp [r2rWorld, vb3, vb2]

@[simp] theorem r2rWorld_vb1 (bits : Fin 4 → Bool) :
    (r2rWorld bits).environment.sourceVoltage ⟨2⟩ = drive (bits b1) := by
  simp [r2rWorld, vb3, vb2, vb1]

@[simp] theorem r2rWorld_vb0 (bits : Fin 4 → Bool) :
    (r2rWorld bits).environment.sourceVoltage ⟨3⟩ = drive (bits b0) := by
  simp [r2rWorld, vb3, vb2, vb1, vb0]

@[simp] theorem r2rWorld_rterm (bits : Fin 4 → Bool) :
    (r2rWorld bits).fabricated.resistance ⟨4⟩ = 2000 := by
  circuit_reduce

@[simp] theorem r2rWorld_rb0 (bits : Fin 4 → Bool) :
    (r2rWorld bits).fabricated.resistance ⟨5⟩ = 2000 := by
  circuit_reduce

@[simp] theorem r2rWorld_r01 (bits : Fin 4 → Bool) :
    (r2rWorld bits).fabricated.resistance ⟨6⟩ = 1000 := by
  circuit_reduce

@[simp] theorem r2rWorld_rb1 (bits : Fin 4 → Bool) :
    (r2rWorld bits).fabricated.resistance ⟨7⟩ = 2000 := by
  circuit_reduce

@[simp] theorem r2rWorld_r12 (bits : Fin 4 → Bool) :
    (r2rWorld bits).fabricated.resistance ⟨8⟩ = 1000 := by
  circuit_reduce

@[simp] theorem r2rWorld_rb2 (bits : Fin 4 → Bool) :
    (r2rWorld bits).fabricated.resistance ⟨9⟩ = 2000 := by
  circuit_reduce

@[simp] theorem r2rWorld_r23 (bits : Fin 4 → Bool) :
    (r2rWorld bits).fabricated.resistance ⟨10⟩ = 1000 := by
  circuit_reduce

@[simp] theorem r2rWorld_rb3 (bits : Fin 4 → Bool) :
    (r2rWorld bits).fabricated.resistance ⟨11⟩ = 2000 := by
  circuit_reduce

private noncomputable def n0Voltage (bits : Fin 4 → Bool) : ℝ :=
  43 * drive (bits b0) / 128 + 11 * drive (bits b1) / 64 +
    3 * drive (bits b2) / 32 + drive (bits b3) / 16

private noncomputable def n1Voltage (bits : Fin 4 → Bool) : ℝ :=
  11 * drive (bits b0) / 64 + 11 * drive (bits b1) / 32 +
    3 * drive (bits b2) / 16 + drive (bits b3) / 8

private noncomputable def n2Voltage (bits : Fin 4 → Bool) : ℝ :=
  3 * drive (bits b0) / 32 + 3 * drive (bits b1) / 16 +
    3 * drive (bits b2) / 8 + drive (bits b3) / 4

private noncomputable def outVoltage (bits : Fin 4 → Bool) : ℝ :=
  drive (bits b0) / 16 + drive (bits b1) / 8 +
    drive (bits b2) / 4 + drive (bits b3) / 2

/-- Exact closed-form operating point used only to establish non-vacuity.
Its equations are checked against the source-derived circuit below. -/
private noncomputable def r2rWitness
    (bits : Fin 4 → Bool) : RealDCAssignment :=
  let d0 := drive (bits b0)
  let d1 := drive (bits b1)
  let d2 := drive (bits b2)
  let d3 := drive (bits b3)
  let n0 := n0Voltage bits
  let n1 := n1Voltage bits
  let n2 := n2Voltage bits
  let out := outVoltage bits
  { voltage := fun id =>
      if id = d3Node then d3
      else if id = d2Node then d2
      else if id = d1Node then d1
      else if id = d0Node then d0
      else if id = n0Node then n0
      else if id = n1Node then n1
      else if id = n2Node then n2
      else if id = outputNode then out
      else 0
    current := fun id =>
      if id = vb3 then -(d3 - out) / 2000
      else if id = vb2 then -(d2 - n2) / 2000
      else if id = vb1 then -(d1 - n1) / 2000
      else if id = vb0 then -(d0 - n0) / 2000
      else if id = rterm then n0 / 2000
      else if id = rb0 then (d0 - n0) / 2000
      else if id = r01 then (n0 - n1) / 1000
      else if id = rb1 then (d1 - n1) / 2000
      else if id = r12 then (n1 - n2) / 1000
      else if id = rb2 then (d2 - n2) / 2000
      else if id = r23 then (n2 - out) / 1000
      else if id = rb3 then (d3 - out) / 2000
      else 0 }

/-- Every four-bit environment has an actual operating point, so the
universal DAC theorem is not vacuous. -/
theorem r2r_realizable (bits : Fin 4 → Bool) :
    ∃ assignment, RealDCSatisfies r2rDeck (r2rWorld bits) assignment := by
  refine ⟨r2rWitness bits, ?_⟩
  change RawRealDCSatisfies r2rDeck_dc (r2rWorld bits) (r2rWitness bits)
  constructor
  · exact r2rDeck_solution_satisfies.valid
  constructor
  · simp [r2rWitness, r2rDeck_dc, groundNode, d3Node, d2Node, d1Node,
      d0Node, n0Node, n1Node, n2Node, outputNode]
  constructor
  · intro device membership
    simp [r2rDeck_dc] at membership
    rcases membership with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [DCDevice.realLaw]
    all_goals
      simp [r2rWitness, vb3, vb2, vb1, vb0, rterm, rb0, r01, rb1,
        r12, rb2, r23, rb3, d3Node, d2Node, d1Node, d0Node, n0Node,
        n1Node, n2Node, outputNode, groundNode]
  · intro node membership nonground
    rcases node with ⟨index⟩
    simp [r2rDeck_dc, DCCircuit.nodes] at membership
    interval_cases index
    all_goals
      simp [r2rDeck_dc, DCCircuit.realKcl, DCDevice.realCurrentLeaving,
        DCDevice.positive, DCDevice.negative, DCDevice.id, r2rWitness,
        n0Voltage, n1Voltage, n2Voltage, outVoltage, vb3, vb2, vb1,
        vb0, rterm, rb0, r01, rb1, r12, rb2, r23, rb3, d3Node, d2Node,
        d1Node, d0Node, n0Node, n1Node, n2Node, outputNode, groundNode]
        at nonground ⊢
    all_goals ring

/-- All sixteen environment drive vectors satisfy the exact DAC transfer
formula. The circuit topology and values come only from `r2r.cir`. -/
theorem r2r_guarantee (bits : Fin 4 → Bool)
    (assignment : RealDCAssignment)
    (h : RealDCSatisfies r2rDeck (r2rWorld bits) assignment) :
    assignment.voltage outputNode = 5 * binVal bits / 16 := by
  change RawRealDCSatisfies r2rDeck_dc (r2rWorld bits) assignment at h
  have hlaws := h.2.2.1
  have hkcl := h.2.2.2
  have hground := h.2.1
  change assignment.voltage groundNode = 0 at hground
  have hd3 := hlaws
    (.voltageSource vb3 d3Node groundNode 5)
    (by simp [r2rDeck_dc, vb3, d3Node, groundNode])
  have hd2 := hlaws
    (.voltageSource vb2 d2Node groundNode 0)
    (by simp [r2rDeck_dc, vb2, d2Node, groundNode])
  have hd1 := hlaws
    (.voltageSource vb1 d1Node groundNode 5)
    (by simp [r2rDeck_dc, vb1, d1Node, groundNode])
  have hd0 := hlaws
    (.voltageSource vb0 d0Node groundNode 0)
    (by simp [r2rDeck_dc, vb0, d0Node, groundNode])
  have hrterm := hlaws
    (.resistor rterm n0Node groundNode 2000)
    (by simp [r2rDeck_dc, rterm, n0Node, groundNode])
  have hrb0 := hlaws
    (.resistor rb0 d0Node n0Node 2000)
    (by simp [r2rDeck_dc, rb0, d0Node, n0Node])
  have hr01 := hlaws
    (.resistor r01 n0Node n1Node 1000)
    (by simp [r2rDeck_dc, r01, n0Node, n1Node])
  have hrb1 := hlaws
    (.resistor rb1 d1Node n1Node 2000)
    (by simp [r2rDeck_dc, rb1, d1Node, n1Node])
  have hr12 := hlaws
    (.resistor r12 n1Node n2Node 1000)
    (by simp [r2rDeck_dc, r12, n1Node, n2Node])
  have hrb2 := hlaws
    (.resistor rb2 d2Node n2Node 2000)
    (by simp [r2rDeck_dc, rb2, d2Node, n2Node])
  have hr23 := hlaws
    (.resistor r23 n2Node outputNode 1000)
    (by simp [r2rDeck_dc, r23, n2Node, outputNode])
  have hrb3 := hlaws
    (.resistor rb3 d3Node outputNode 2000)
    (by simp [r2rDeck_dc, rb3, d3Node, outputNode])
  have hn0 := hkcl n0Node
    (by simp [r2rDeck_dc, DCCircuit.nodes, n0Node]) (by decide)
  have hn1 := hkcl n1Node
    (by simp [r2rDeck_dc, DCCircuit.nodes, n1Node]) (by decide)
  have hn2 := hkcl n2Node
    (by simp [r2rDeck_dc, DCCircuit.nodes, n2Node]) (by decide)
  have hout := hkcl outputNode
    (by simp [r2rDeck_dc, DCCircuit.nodes, outputNode]) (by decide)
  simp [DCDevice.realLaw] at hd3 hd2 hd1 hd0 hrterm hrb0 hr01 hrb1 hr12 hrb2 hr23 hrb3
  simp [r2rDeck_dc, DCCircuit.realKcl, DCDevice.realCurrentLeaving,
    DCDevice.positive, DCDevice.negative, DCDevice.id, n0Node, n1Node,
    n2Node, outputNode] at hn0 hn1 hn2 hout
  dsimp [vb3, vb2, vb1, vb0, rterm, rb0, r01, rb1, r12, rb2, r23, rb3,
    d3Node, d2Node, d1Node, d0Node, n0Node, n1Node, n2Node,
    outputNode, groundNode] at hd3 hd2 hd1 hd0 hrterm hrb0 hr01 hrb1 hr12 hrb2 hr23 hrb3
  dsimp [vb3, vb2, vb1, vb0, rterm, rb0, r01, rb1, r12, rb2, r23, rb3,
    d3Node, d2Node, d1Node, d0Node, n0Node, n1Node, n2Node,
    outputNode, groundNode] at hn0 hn1 hn2 hout hground ⊢
  rw [hground] at hd3 hd2 hd1 hd0
  cases h0 : bits b0 <;> cases h1 : bits b1 <;>
    cases h2 : bits b2 <;> cases h3 : bits b3 <;>
    simp_all [drive, binVal, b0, b1, b2, b3] <;>
    norm_num at * <;> linarith

end Examples.spice.r2r.proof
