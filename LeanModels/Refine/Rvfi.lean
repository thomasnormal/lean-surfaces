import LeanModels.Refine.Cycle

/-!
# RVFI-shaped retirement observations

The commit interface stores architectural effects in a semantic form.  Real
cores commonly expose the same information as the packed signals of the
RISC-V Formal Interface (RVFI): one valid bit, a pc/instruction pair, an
optional register write, and byte masks for a data-memory read or write.

`RvfiObservation` is the RV32 machine-mode slice used by this lane.  The
adapter is deliberately partial: malformed masks, a simultaneous read and
write, or inconsistent trap flags produce no retirement.  A core proof must
therefore establish `wellFormed` before using `toRetirement?`; it cannot turn
an unrecognised wire pattern into a guessed architectural effect.

The RVFI `order`, source-register, mode, and XLEN fields are retained so that
the boundary matches the hardware-facing shape.  The semantic `Retirement`
does not need them: order is supplied by the trace position, source operands
are checked by the ISA relation, and this adapter is scoped to machine-mode
RV32 (`mode = 3`, `ixl = 1`).
-/

namespace LeanModels.Refine

open LeanModels.Rv

abbrev ByteMask := BitVec 4

/-! ## Masks and memory effects -/

/-- RVFI's canonical byte masks for the three RV32 data widths. -/
def maskOfWidth : MemW → ByteMask
  | .byte => 0b0001
  | .half => 0b0011
  | .word => 0b1111

/-- Decode the canonical masks.  A mask outside this inventory is refused. -/
def widthOfMask (mask : ByteMask) : Option MemW :=
  if mask = maskOfWidth .byte then some .byte
  else if mask = maskOfWidth .half then some .half
  else if mask = maskOfWidth .word then some .word
  else none

@[simp] theorem widthOfMask_byte : widthOfMask (maskOfWidth .byte) = some .byte := by
  simp [widthOfMask, maskOfWidth]

@[simp] theorem widthOfMask_half : widthOfMask (maskOfWidth .half) = some .half := by
  simp [widthOfMask, maskOfWidth]

@[simp] theorem widthOfMask_word : widthOfMask (maskOfWidth .word) = some .word := by
  simp [widthOfMask, maskOfWidth]

def validMaskB (mask : ByteMask) : Bool :=
  mask == 0 || mask == maskOfWidth .byte ||
    mask == maskOfWidth .half || mask == maskOfWidth .word

/-! ## The packed observation -/

/-- The RV32 machine-mode subset of an RVFI retirement record.

`cause` is a proof-side annotation: standard RVFI carries the `trap` and
`intr` bits, while the architectural adapter also needs the model's precise
`Cause` to compare against `Retirement.trap`.  A real core supplies it from
the same trap/cause contract used in its refinement relation; inconsistent
annotations are rejected by `wellFormed`.
-/
structure RvfiObservation where
  valid : Bool := true
  order : Nat := 0
  insn : Word
  pcRdata : Word
  pcWdata : Word
  trap : Bool := false
  intr : Bool := false
  mode : BitVec 2 := 3
  ixl : BitVec 2 := 1
  rs1Addr : Reg := 0
  rs1Rdata : Word := 0
  rs2Addr : Reg := 0
  rs2Rdata : Word := 0
  rdAddr : Reg := 0
  rdWdata : Word := 0
  rdWdataValid : Bool := false
  memAddr : Word := 0
  memRmask : ByteMask := 0
  memWmask : ByteMask := 0
  memRdata : Word := 0
  memWdata : Word := 0
  cause : Option Cause := none
  deriving DecidableEq, Repr

def causeWellFormedB (o : RvfiObservation) : Bool :=
  match o.cause with
  | none => !o.trap && !o.intr
  | some c => o.trap && (o.intr == c.isInterrupt)

def RvfiObservation.wellFormedB (o : RvfiObservation) : Bool :=
  (o.mode == 3) && (o.ixl == 1) &&
  validMaskB o.memRmask && validMaskB o.memWmask &&
  (o.memRmask == 0 || o.memWmask == 0) &&
  causeWellFormedB o

def RvfiObservation.wellFormed (o : RvfiObservation) : Prop :=
  o.wellFormedB = true

def RvfiObservation.memoryEffect? (o : RvfiObservation) : Option MemoryEffect :=
  match widthOfMask o.memRmask, widthOfMask o.memWmask with
  | some width, none => some (.read o.memAddr width o.memRdata)
  | none, some width => some (.write o.memAddr width o.memWdata)
  | _, _ => none

def RvfiObservation.toRetirement (o : RvfiObservation) : Retirement :=
  { pc := o.pcRdata
    instr := o.insn
    nextPc := o.pcWdata
    writes := if o.rdWdataValid && o.rdAddr != 0 then
      [(o.rdAddr, o.rdWdata)] else []
    memory := o.memoryEffect?
    trap := o.cause }

/-- Decode a packed record only when it is a valid, well-formed retirement. -/
def RvfiObservation.toRetirement? (o : RvfiObservation) : Option Retirement :=
  if o.valid && o.wellFormedB then some o.toRetirement else none

theorem RvfiObservation.toRetirement?_eq_some (o : RvfiObservation)
    (hvalid : o.valid = true) (hwell : o.wellFormed) :
    o.toRetirement? = some o.toRetirement := by
  simp [RvfiObservation.toRetirement?, hvalid]
  exact hwell

theorem RvfiObservation.wellFormed_of_toRetirement?_eq_some
    (o : RvfiObservation) {retirement : Retirement}
    (hvalid : o.valid = true)
    (hretirement : o.toRetirement? = some retirement) :
    o.wellFormed := by
  cases hvalue : o.wellFormedB with
  | false =>
      have hnone : o.toRetirement? = none := by
        simp [RvfiObservation.toRetirement?, hvalid, hvalue]
      rw [hnone] at hretirement
      cases hretirement
  | true => exact hvalue

theorem RvfiObservation.toRetirement?_eq_some_iff
    (o : RvfiObservation) {retirement : Retirement} :
    o.toRetirement? = some retirement ↔
      o.valid = true ∧ o.wellFormed ∧ retirement = o.toRetirement := by
  constructor
  · intro hretirement
    have hvalid : o.valid = true := by
      cases hvalue : o.valid with
      | false =>
          have hnone : o.toRetirement? = none := by
            simp [RvfiObservation.toRetirement?, hvalue]
          rw [hnone] at hretirement
          cases hretirement
      | true => exact rfl
    have hwell : o.wellFormed :=
      o.wellFormed_of_toRetirement?_eq_some hvalid hretirement
    have hsome : o.toRetirement? = some o.toRetirement :=
      o.toRetirement?_eq_some hvalid hwell
    have hdecoded : o.toRetirement = retirement :=
      Option.some.inj (hsome.symm.trans hretirement)
    exact ⟨hvalid, hwell, hdecoded.symm⟩
  · rintro ⟨hvalid, hwell, rfl⟩
    exact o.toRetirement?_eq_some hvalid hwell

theorem RvfiObservation.toRetirement?_eq_none_iff
    (o : RvfiObservation) :
    o.toRetirement? = none ↔ o.valid = false ∨ ¬ o.wellFormed := by
  constructor
  · intro hnone
    cases hvalid : o.valid with
    | false => exact Or.inl rfl
    | true =>
        right
        intro hwell
        have hsome := o.toRetirement?_eq_some hvalid hwell
        rw [hnone] at hsome
        cases hsome
  · intro hbad
    rcases hbad with hvalid | hwell
    · simp [RvfiObservation.toRetirement?, hvalid]
    · cases hvalid : o.valid with
      | false => simp [RvfiObservation.toRetirement?, hvalid]
      | true =>
          have hnot : o.wellFormedB ≠ true := by
            intro hvalue
            apply hwell
            exact hvalue
          simp [RvfiObservation.toRetirement?, hvalid, hnot]

/-! ## Finite RVFI traces and retirement order -/

/-- A finite packed trace certificate.  Invalid RVFI cycles are bubbles and do
not advance the retirement order.  A valid cycle must carry the next order
number and must normalize to a semantic retirement; a malformed valid record
therefore cannot be silently dropped.  The start parameter permits a caller
to continue a trace whose order began before the finite window. -/
inductive RvfiTraceRefines : Nat → List RvfiObservation → List Retirement → Prop where
  | nil (start : Nat) : RvfiTraceRefines start [] []
  | bubble {start : Nat} {observation : RvfiObservation}
      {observations : List RvfiObservation} {retirements : List Retirement}
      (hvalid : observation.valid = false)
      (htail : RvfiTraceRefines start observations retirements) :
      RvfiTraceRefines start (observation :: observations) retirements
  | retire {start : Nat} {observation : RvfiObservation}
      {observations : List RvfiObservation} {retirement : Retirement}
      {retirements : List Retirement}
      (hvalid : observation.valid = true)
      (horder : observation.order = start)
      (hretirement : observation.toRetirement? = some retirement)
      (htail : RvfiTraceRefines (start + 1) observations retirements) :
      RvfiTraceRefines start (observation :: observations)
        (retirement :: retirements)

/-- Check a packed finite trace while retaining its architectural order. -/
def normalizeRvfiTrace? (start : Nat) : List RvfiObservation → Option (List Retirement)
  | [] => some []
  | observation :: observations =>
      if observation.valid then
        if observation.order == start then
          match observation.toRetirement?, normalizeRvfiTrace? (start + 1) observations with
          | some retirement, some retirements => some (retirement :: retirements)
          | _, _ => none
        else none
      else normalizeRvfiTrace? start observations

/-- The executable trace checker and the proof-facing certificate agree. -/
theorem normalizeRvfiTrace?_iff {start : Nat} {observations : List RvfiObservation}
    {retirements : List Retirement} :
    normalizeRvfiTrace? start observations = some retirements ↔
      RvfiTraceRefines start observations retirements := by
  constructor
  · intro h
    induction observations generalizing start retirements with
    | nil =>
        simp [normalizeRvfiTrace?] at h
        subst retirements
        exact .nil _
    | cons observation observations ih =>
        by_cases hv : observation.valid = true
        · simp [normalizeRvfiTrace?, hv] at h
          by_cases ho : observation.order = start
          · simp [ho] at h
            cases hret : observation.toRetirement? with
            | none => simp [hret] at h
            | some retirement =>
                cases htail : normalizeRvfiTrace? (start + 1) observations with
                | none => simp [hret, htail] at h
                | some retirements =>
                    simp [hret, htail] at h
                    cases h
                    refine .retire hv ho hret ?_
                    exact ih htail
          · simp [ho] at h
        · have hv' : observation.valid = false := by
            cases hval : observation.valid with
            | false => exact rfl
            | true => exact False.elim (hv hval)
          simp [normalizeRvfiTrace?, hv'] at h
          exact .bubble hv' (ih h)
  · intro h
    induction h with
    | nil start => rfl
    | bubble hvalid htail ih =>
        simp [normalizeRvfiTrace?, hvalid, ih]
    | retire hvalid horder hretirement htail ih =>
        simp [normalizeRvfiTrace?, hvalid, horder, hretirement, ih]

/-- A failed executable normalization has no proof-facing retirement-order
certificate.  This keeps malformed valid rows and order gaps loud instead of
allowing a caller to treat `none` as an empty retirement stream. -/
theorem normalizeRvfiTrace?_eq_none_iff {start : Nat}
    {observations : List RvfiObservation} :
    normalizeRvfiTrace? start observations = none ↔
      ¬ ∃ retirements, RvfiTraceRefines start observations retirements := by
  constructor
  · intro hnone ⟨retirements, htrace⟩
    have hsome := (normalizeRvfiTrace?_iff).2 htrace
    rw [hnone] at hsome
    cases hsome
  · intro hno
    cases hnorm : normalizeRvfiTrace? start observations with
    | none => simpa using hnorm
    | some retirements =>
        exact False.elim (hno ⟨retirements, (normalizeRvfiTrace?_iff).1 hnorm⟩)

/-! A successful normalization classifies every raw row: invalid rows are
explicit bubbles, while every valid row is well formed.  This is proved
directly from the executable checker rather than through the certificate
equivalence, whose existential direction is intentionally more general. -/
theorem normalizeRvfiTrace?_wellFormed {start : Nat}
    {observations : List RvfiObservation} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start observations = some retirements) :
    ∀ observation, observation ∈ observations →
      observation.valid = false ∨ observation.wellFormed := by
  induction observations generalizing start retirements with
  | nil =>
      simp [normalizeRvfiTrace?] at h
      cases h
      intro observation hmem
      simp at hmem
  | cons observation observations ih =>
      by_cases hv : observation.valid = true
      · simp [normalizeRvfiTrace?, hv] at h
        by_cases ho : observation.order = start
        · simp [ho] at h
          cases hret : observation.toRetirement? with
          | none => simp [hret] at h
          | some retirement =>
              cases htail : normalizeRvfiTrace? (start + 1) observations with
              | none => simp [hret, htail] at h
              | some tail =>
                  simp [hret, htail] at h
                  cases h
                  have hwell :=
                    observation.wellFormed_of_toRetirement?_eq_some hv hret
                  intro candidate hmem
                  simp only [List.mem_cons] at hmem
                  rcases hmem with rfl | hmem
                  · exact Or.inr hwell
                  · exact ih htail candidate hmem
        · simp [ho] at h
      · have hv' : observation.valid = false := by
          cases hvalue : observation.valid with
          | false => exact rfl
          | true => exact False.elim (hv hvalue)
        simp [normalizeRvfiTrace?, hv'] at h
        intro candidate hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact Or.inl hv'
        · exact ih h candidate hmem

/-- Normalization is compositional across finite observation windows.  The
second window starts after the number of retirements in the first, so bubbles
do not affect the order carried into the next chunk. -/
theorem normalizeRvfiTrace?_append (start : Nat)
    (first second : List RvfiObservation) :
    normalizeRvfiTrace? start (first ++ second) =
      match normalizeRvfiTrace? start first with
      | none => none
      | some retirements =>
          (normalizeRvfiTrace? (start + retirements.length) second).map
            (fun tail => retirements ++ tail) := by
  induction first generalizing start with
  | nil =>
      simp [normalizeRvfiTrace?]
  | cons observation observations ih =>
      by_cases hv : observation.valid = true
      · simp [normalizeRvfiTrace?, hv]
        by_cases ho : observation.order = start
        · simp [ho]
          cases hret : observation.toRetirement? with
          | none => simp
          | some retirement =>
              cases htail : normalizeRvfiTrace? (start + 1) observations with
              | none =>
                  rw [ih (start := start + 1), htail]
              | some tail =>
                  rw [ih (start := start + 1)]
                  simp only [htail]
                  simp only [List.length_cons]
                  have hindex : start + 1 + tail.length =
                      start + (tail.length + 1) := by omega
                  rw [hindex]
                  cases h2 : normalizeRvfiTrace?
                      (start + (tail.length + 1)) second with
                  | none => simp
                  | some tail2 => simp
        · simp [ho]
      · have hv' : observation.valid = false := by
          cases hval : observation.valid with
          | false => exact rfl
          | true => exact False.elim (hv hval)
        simp [normalizeRvfiTrace?, hv', ih]

/-- A successful normalization contains exactly the decoded retirements in
the observation stream.  This projection is useful for packet adapters,
which first filter each channel's rows and then expose the resulting commit
entries.  The order and validity checks still come from the normalization
certificate; this theorem does not accept an unchecked `filterMap` as proof. -/
theorem normalizeRvfiTrace?_filterMap {start : Nat}
    {observations : List RvfiObservation} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start observations = some retirements) :
    observations.filterMap RvfiObservation.toRetirement? = retirements := by
  induction observations generalizing start retirements with
  | nil =>
      simp [normalizeRvfiTrace?] at h ⊢
      cases h
      rfl
  | cons observation observations ih =>
      by_cases hv : observation.valid = true
      · simp [normalizeRvfiTrace?, hv] at h
        by_cases ho : observation.order = start
        · simp [ho] at h
          cases hret : observation.toRetirement? with
          | none => simp [hret] at h
          | some retirement =>
              cases htail : normalizeRvfiTrace? (start + 1) observations with
              | none => simp [hret, htail] at h
              | some retirements =>
                  simp [hret, htail] at h
                  cases h
                  simp only [List.filterMap, hret]
                  congr 1
                  exact ih htail
        · simp [ho] at h
      · have hv' : observation.valid = false := by
          cases hval : observation.valid with
          | false => exact rfl
          | true => exact False.elim (hv hval)
        simp [normalizeRvfiTrace?, hv'] at h
        have hnone : observation.toRetirement? = none := by
          simp [RvfiObservation.toRetirement?, hv']
        simp only [List.filterMap, hnone]
        exact ih h

/-! ## Feeding packed observations into the cycle bridge -/

/-- A cycle-level core whose commit port is the packed RVFI shape. -/
structure RvfiCycleMachine (State : Type) where
  init : State
  step : State → Input → State × RvfiObservation

/-- Adapt an RVFI cycle port to the generic cycle-to-retirement bridge.
Invalid or non-valid records become bubbles; a core-specific admission proof
must establish `wellFormed` whenever `valid` is asserted. -/
def RvfiCycleMachine.toCycleMachine {State : Type}
    (machine : RvfiCycleMachine State) : CycleMachine State where
  init := machine.init
  step state input :=
    let (state', observation) := machine.step state input
    (state', observation.toRetirement?)

/-! ## Strict packed-cycle refinement -/

/-- A cycle-level refinement stated before projecting a packed RVFI row to an
optional retirement.

Unlike `CycleStepRefines machine.toCycleMachine`, this relation does not let a
malformed valid row become a bubble: every `valid = true` observation must
normalize to one retirement that matches the ISA step.  Invalid observations
remain explicit bubbles.  The separate definition is useful at the loaded
core boundary, where the invariant is proved from the raw RVFI fields before
the generic optional-retirement adapter is applied. -/
def RvfiCycleStepRefines {State IsaState : Type}
    (machine : RvfiCycleMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Prop) (admit : Input → Prop) : Prop :=
  rel machine.init isa.init ∧
    ∀ (state : State) (isaState : IsaState) (input : Input),
      rel state isaState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ retirement,
          (observation.toRetirement? = some retirement) ∧
            ((rel state' (isa.step isaState input).fst) ∧
              (retirement = (isa.step isaState input).snd))
      else
        rel state' isaState

/-- The strict packed-cycle contract implies the existing optional-retirement
cycle contract.  The proof is the only place that turns a valid raw row into
the generic `some` branch; malformed valid rows have no branch to enter. -/
theorem rvfiCycleStepRefines_toCycleStepRefines
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : RvfiCycleStepRefines machine isa rel admit) :
    CycleStepRefines machine.toCycleMachine isa rel admit := by
  constructor
  · exact h.1
  · intro state isaState input hrel hadmit
    have hs := h.2 state isaState input hrel hadmit
    rcases hstep : machine.step state input with ⟨state', observation⟩
    simp only [hstep] at hs
    by_cases hv : observation.valid = true
    · rw [hv] at hs
      cases hs with
      | intro retirement hbody =>
          have hretirement := hbody.1
          have hrel' := hbody.2.1
          have hcommit := hbody.2.2
          simp only [RvfiCycleMachine.toCycleMachine, hstep]
          rw [hretirement]
          exact ⟨hrel', hcommit⟩
    · have hv' : observation.valid = false := by
        cases hvalue : observation.valid with
        | false => exact rfl
        | true => exact False.elim (hv hvalue)
      have hnone : observation.toRetirement? = none := by
        simp [RvfiObservation.toRetirement?, hv']
      rw [hv'] at hs
      simp only [RvfiCycleMachine.toCycleMachine, hstep]
      rw [hnone]
      simpa using hs

/-- A valid row in the strict contract is genuinely well formed, and its
concrete packed retirement is the ISA retirement.  This projection keeps
callers from treating the optional adapter as a second source of semantics. -/
theorem rvfiCycleStepRefines_valid_step
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : RvfiCycleStepRefines machine isa rel admit)
    (state : State) (isaState : IsaState) (input : Input)
    (hrel : rel state isaState) (hadmit : admit input)
    (hvalid : (machine.step state input).2.valid = true) :
    (machine.step state input).2.wellFormed ∧
    rel (machine.step state input).1 (isa.step isaState input).fst ∧
    (machine.step state input).2.toRetirement =
      (isa.step isaState input).snd := by
  rcases hstep : machine.step state input with ⟨state', observation⟩
  rcases hisa : isa.step isaState input with ⟨isaState', isaRetirement⟩
  have hvalid' : observation.valid = true := by
    simpa [hstep] using hvalid
  have hs := h.2 state isaState input hrel hadmit
  simp only [hstep, hisa] at hs ⊢
  rw [hvalid'] at hs
  rcases hs with ⟨retirement, hretirement, hrel', hcommit⟩
  have hwell : observation.wellFormed :=
    observation.wellFormed_of_toRetirement?_eq_some hvalid' hretirement
  have hsome : observation.toRetirement? = some observation.toRetirement :=
    observation.toRetirement?_eq_some hvalid' hwell
  have hto : observation.toRetirement = retirement := by
    exact Option.some.inj (hsome.symm.trans hretirement)
  exact ⟨hwell, hrel', hto.trans hcommit⟩

/-- An invalid RVFI row is an explicit bubble: the strict contract carries the
core relation across the cycle while the ISA state stutters. -/
theorem rvfiCycleStepRefines_invalid_step
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : RvfiCycleStepRefines machine isa rel admit)
    (state : State) (isaState : IsaState) (input : Input)
    (hrel : rel state isaState) (hadmit : admit input)
    (hinvalid : (machine.step state input).2.valid = false) :
    rel (machine.step state input).1 isaState := by
  rcases hstep : machine.step state input with ⟨state', observation⟩
  have hinvalid' : observation.valid = false := by
    simpa [hstep] using hinvalid
  have hs := h.2 state isaState input hrel hadmit
  simp only [hstep] at hs ⊢
  rw [hinvalid'] at hs
  exact hs

/-! A single per-cycle projection dispatches to the two strict branches.  The
valid side exposes the decoded row and architectural step; the invalid side
is an explicit ISA stutter.  Keeping the validity bit in each disjunct makes
the branch total and prevents a caller from treating an unchecked row as a
bubble. -/
theorem rvfiCycleStepRefines_step
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : RvfiCycleStepRefines machine isa rel admit)
    (state : State) (isaState : IsaState) (input : Input)
    (hrel : rel state isaState) (hadmit : admit input) :
    let (state', observation) := machine.step state input
    let (isaState', isaRetirement) := isa.step isaState input
    (observation.valid = true ∧ observation.wellFormed ∧
        rel state' isaState' ∧ observation.toRetirement = isaRetirement) ∨
      (observation.valid = false ∧ rel state' isaState) := by
  rcases hstep : machine.step state input with ⟨state', observation⟩
  rcases hisa : isa.step isaState input with ⟨isaState', isaRetirement⟩
  by_cases hv : observation.valid = true
  · left
    have hvalid : (machine.step state input).2.valid = true := by
      simpa [hstep] using hv
    have hs := rvfiCycleStepRefines_valid_step h state isaState input
      hrel hadmit hvalid
    simpa [hstep, hisa] using And.intro hv hs
  · right
    have hinvalid : (machine.step state input).2.valid = false := by
      cases hvalue : observation.valid with
      | false => simp [hstep, hvalue]
      | true => exact False.elim (hv hvalue)
    have hs := rvfiCycleStepRefines_invalid_step h state isaState input
      hrel hadmit hinvalid
    exact ⟨by
      cases hvalue : observation.valid with
      | false => rfl
      | true => exact False.elim (hv hvalue), by simpa [hstep] using hs⟩

/-! The branch projection is also an introduction rule.  A core invariant can
prove one exhaustive valid/invalid case split per cycle and let this theorem
package the valid row's concrete retirement into the strict contract's
existential form. -/
theorem rvfiCycleStepRefines_of_step
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (hinit : rel machine.init isa.init)
    (hstep : ∀ (state : State) (isaState : IsaState) (input : Input),
      rel state isaState → admit input →
      let (state', observation) := machine.step state input
      let (isaState', isaRetirement) := isa.step isaState input
      (observation.valid = true ∧ observation.wellFormed ∧
          rel state' isaState' ∧ observation.toRetirement = isaRetirement) ∨
        (observation.valid = false ∧ rel state' isaState)) :
    RvfiCycleStepRefines machine isa rel admit := by
  constructor
  · exact hinit
  · intro state isaState input hrel hadmit
    rcases hstep state isaState input hrel hadmit with hvalid | hinvalid
    · rcases hvalid with ⟨hvalid, hwell, hrel', hto⟩
      simp only [hvalid]
      exact ⟨_, RvfiObservation.toRetirement?_eq_some _ hvalid hwell,
        hrel', hto⟩
    · rcases hinvalid with ⟨hinvalid, hrel'⟩
      simp only [hinvalid]
      exact hrel'

/-! The optional cycle contract can be lifted back to the raw RVFI contract
when a separate wire invariant proves that every valid row is well formed on
related, admitted states.  Without this premise the optional adapter could
turn a malformed valid row into `none`, so the reverse direction would be
unsound. -/
theorem cycleStepRefines_to_rvfiCycleStepRefines_of_rel
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : CycleStepRefines machine.toCycleMachine isa rel admit)
    (hwell : ∀ (state : State) (isaState : IsaState) (input : Input),
      rel state isaState → admit input →
      (machine.step state input).2.valid = true →
      (machine.step state input).2.wellFormed) :
    RvfiCycleStepRefines machine isa rel admit := by
  refine rvfiCycleStepRefines_of_step h.1 ?_
  intro state isaState input hrel hadmit
  rcases hstep : machine.step state input with ⟨state', observation⟩
  rcases hisa : isa.step isaState input with ⟨isaState', isaRetirement⟩
  have hcycle := h.2 state isaState input hrel hadmit
  simp only [RvfiCycleMachine.toCycleMachine, hstep, hisa] at hcycle
  by_cases hv : observation.valid = true
  · have hwell' : observation.wellFormed := by
      have hvalid : (machine.step state input).2.valid = true := by
        simpa [hstep] using hv
      have hwellRaw := hwell state isaState input hrel hadmit hvalid
      simpa [hstep] using hwellRaw
    have hsome : observation.toRetirement? = some observation.toRetirement :=
      observation.toRetirement?_eq_some hv hwell'
    rw [hsome] at hcycle
    exact Or.inl ⟨hv, hwell', hcycle.1, hcycle.2⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hnone : observation.toRetirement? = none := by
      simp [RvfiObservation.toRetirement?, hv']
    rw [hnone] at hcycle
    exact Or.inr ⟨hv', hcycle⟩

/-! A global raw-row invariant is a convenient specialization of the
relation-aware bridge above. -/
theorem cycleStepRefines_to_rvfiCycleStepRefines
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : CycleStepRefines machine.toCycleMachine isa rel admit)
    (hwell : ∀ (state : State) (input : Input),
      (machine.step state input).2.valid = true →
      (machine.step state input).2.wellFormed) :
    RvfiCycleStepRefines machine isa rel admit := by
  exact cycleStepRefines_to_rvfiCycleStepRefines_of_rel h
    (fun state _ input _ _ hvalid => hwell state input hvalid)

/-! With the raw well-formedness invariant in hand, the optional and strict
cycle contracts are equivalent.  The relation-aware form matches the
invariant available in a loaded-core proof. -/
theorem cycleStepRefines_iff_rvfiCycleStepRefines_of_rel
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (hwell : ∀ (state : State) (isaState : IsaState) (input : Input),
      rel state isaState → admit input →
      (machine.step state input).2.valid = true →
      (machine.step state input).2.wellFormed) :
    CycleStepRefines machine.toCycleMachine isa rel admit ↔
      RvfiCycleStepRefines machine isa rel admit := by
  constructor
  · intro h
    exact cycleStepRefines_to_rvfiCycleStepRefines_of_rel h hwell
  · intro h
    exact rvfiCycleStepRefines_toCycleStepRefines h

/-! The global-row equivalence is a convenience specialization of the
relation-aware statement. -/
theorem cycleStepRefines_iff_rvfiCycleStepRefines
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (hwell : ∀ (state : State) (input : Input),
      (machine.step state input).2.valid = true →
      (machine.step state input).2.wellFormed) :
    CycleStepRefines machine.toCycleMachine isa rel admit ↔
      RvfiCycleStepRefines machine isa rel admit := by
  exact cycleStepRefines_iff_rvfiCycleStepRefines_of_rel
    (fun state _ input _ _ hvalid => hwell state input hvalid)

/-! The strict contract and the total raw-cycle case split are equivalent.
This form lets a loaded-core proof work entirely with packed fields and defer
the optional-retirement adapter to the generic constructor. -/
theorem rvfiCycleStepRefines_iff_step
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop} :
    RvfiCycleStepRefines machine isa rel admit ↔
      rel machine.init isa.init ∧
      (∀ (state : State) (isaState : IsaState) (input : Input),
        rel state isaState → admit input →
        let (state', observation) := machine.step state input
        let (isaState', isaRetirement) := isa.step isaState input
        (observation.valid = true ∧ observation.wellFormed ∧
            rel state' isaState' ∧ observation.toRetirement = isaRetirement) ∨
          (observation.valid = false ∧ rel state' isaState)) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro state isaState input hrel hadmit
    exact rvfiCycleStepRefines_step h state isaState input hrel hadmit
  · rintro ⟨hinit, hstep⟩
    exact rvfiCycleStepRefines_of_step hinit hstep

@[simp] theorem RvfiCycleMachine.toCycleMachine_init {State : Type}
    (machine : RvfiCycleMachine State) :
    machine.toCycleMachine.init = machine.init := rfl

/-- The packed observations emitted by a finite cycle window.  Unlike
`cycleTrace`, this retains bubbles and malformed valid rows so that the RVFI
normalizer can check the complete wire stream before it is projected to
architectural retirements. -/
def rvfiObservations {State : Type} (machine : RvfiCycleMachine State) :
    State → List Input → List RvfiObservation
  | _, [] => []
  | state, input :: inputs =>
      let (state', observation) := machine.step state input
      observation :: rvfiObservations machine state' inputs

/-! ## State-threaded RVFI observation windows -/

/-- The RVFI machine state after a finite observation window.  The wire rows
are discarded here; the state is retained for the next window. -/
def rvfiStateAfter {State : Type} (machine : RvfiCycleMachine State) :
    State → List Input → State
  | state, [] => state
  | state, input :: inputs =>
      rvfiStateAfter machine (machine.step state input).1 inputs

theorem RvfiCycleMachine.toCycleMachine_stateAfter {State : Type}
    (machine : RvfiCycleMachine State) (state : State) (inputs : List Input) :
    cycleStateAfter machine.toCycleMachine state inputs =
      rvfiStateAfter machine state inputs := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input inputs ih =>
      cases hstep : machine.step state input with
      | mk state' observation =>
          simp only [cycleStateAfter, rvfiStateAfter,
            RvfiCycleMachine.toCycleMachine, hstep]
          exact ih state'

theorem rvfiStateAfter_append {State : Type}
    (machine : RvfiCycleMachine State) (state : State)
    (first second : List Input) :
    rvfiStateAfter machine state (first ++ second) =
      rvfiStateAfter machine
        (rvfiStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : machine.step state input with
      | mk state' observation =>
          simp only [List.cons_append, rvfiStateAfter, hstep]
          exact ih state'

theorem rvfiObservations_append {State : Type}
    (machine : RvfiCycleMachine State) (state : State)
    (first second : List Input) :
    rvfiObservations machine state (first ++ second) =
      rvfiObservations machine state first ++
        rvfiObservations machine (rvfiStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : machine.step state input with
      | mk state' observation =>
          simp only [List.cons_append, rvfiObservations, rvfiStateAfter, hstep]
          rw [ih state']

theorem normalizeRvfiCycleTrace_append {State : Type}
    (machine : RvfiCycleMachine State) (state : State)
    (first second : List Input)
    {start : Nat} {firstRetirements secondRetirements : List Retirement}
    (hfirst : normalizeRvfiTrace? start
        (rvfiObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiObservations machine
          (rvfiStateAfter machine state first) second) =
      some secondRetirements) :
    normalizeRvfiTrace? start
        (rvfiObservations machine state (first ++ second)) =
      some (firstRetirements ++ secondRetirements) := by
  rw [rvfiObservations_append, normalizeRvfiTrace?_append]
  simp [hfirst, hsecond]

/-- A successful RVFI normalization is exactly the retirement stream emitted
by the generic cycle bridge for the same window.  The hypothesis is
deliberately an executable certificate: valid rows must have consecutive
orders and decode to a retirement, while invalid rows are explicit bubbles.
Thus the bridge never repairs, sorts, or silently drops a malformed row. -/
theorem normalizeRvfiCycleTrace {State : Type}
    (machine : RvfiCycleMachine State) (state : State) (inputs : List Input)
    {start : Nat} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start (rvfiObservations machine state inputs) =
      some retirements) :
    cycleTrace machine.toCycleMachine state inputs = retirements := by
  induction inputs generalizing state start retirements with
  | nil =>
      simp [rvfiObservations, normalizeRvfiTrace?, cycleTrace] at h ⊢
      cases h
      rfl
  | cons input inputs ih =>
      cases hstep : machine.step state input with
      | mk state' observation =>
        have hobs : rvfiObservations machine state (input :: inputs) =
            observation :: rvfiObservations machine state' inputs := by
          simp [rvfiObservations, hstep]
        rw [hobs] at h
        have hcycle : cycleTrace machine.toCycleMachine state (input :: inputs) =
            match observation.toRetirement? with
            | none => cycleTrace machine.toCycleMachine state' inputs
            | some retirement => retirement :: cycleTrace machine.toCycleMachine state' inputs := by
          simp [cycleTrace, RvfiCycleMachine.toCycleMachine, hstep]
          rfl
        rw [hcycle]
        by_cases hv : observation.valid = true
        · simp [normalizeRvfiTrace?, hv] at h
          by_cases ho : observation.order = start
          · simp [ho] at h
            cases hret : observation.toRetirement? with
            | none => simp [hret] at h
            | some retirement =>
                cases htail : normalizeRvfiTrace? (start + 1)
                    (rvfiObservations machine state' inputs) with
                | none => simp [hret, htail] at h
                | some retirements =>
                    simp [hret, htail] at h
                    cases h
                    change retirement :: cycleTrace machine.toCycleMachine state' inputs =
                      retirement :: retirements
                    congr 1
                    exact ih state' (start := start + 1)
                      (retirements := retirements) htail
          · simp [ho] at h
        · have hv' : observation.valid = false := by
            cases hval : observation.valid with
            | false => exact rfl
            | true => exact False.elim (hv hval)
          simp [normalizeRvfiTrace?, hv'] at h
          have hnone : observation.toRetirement? = none := by
            simp [RvfiObservation.toRetirement?, hv']
          rw [hnone]
          exact ih state' (start := start) (retirements := retirements) h

theorem normalizeRvfiCycleTrace_input_length {State : Type}
    (machine : RvfiCycleMachine State) (state : State) (inputs : List Input)
    {start : Nat} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start (rvfiObservations machine state inputs) =
      some retirements) :
    (retireInputs machine.toCycleMachine state inputs).length =
      retirements.length := by
  have htrace := normalizeRvfiCycleTrace machine state inputs h
  have hlength := congrArg List.length htrace
  rw [cycleTrace_length_eq_retireInputs_length] at hlength
  exact hlength

theorem rvfiStateAfter_refines
    {State IsaState : Type}
    (machine : RvfiCycleMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Prop) (admit : Input → Prop)
    (h : CycleStepRefines machine.toCycleMachine isa rel admit) :
    ∀ (state : State) (isaState : IsaState) (inputs : List Input),
      rel state isaState →
      (∀ i ∈ inputs, admit i) →
      rel (rvfiStateAfter machine state inputs)
        (machineStateAfter isa isaState
          (retireInputs machine.toCycleMachine state inputs)) := by
  intro state isaState inputs hrel hall
  have hstate := cycleStateAfter_refines h state isaState inputs hrel hall
  rw [RvfiCycleMachine.toCycleMachine_stateAfter] at hstate
  exact hstate

/-- The strict packed-cycle contract directly gives the existing finite trace
theorem.  Keeping this wrapper next to the raw contract prevents a loaded-core
proof from accidentally invoking the optional adapter without first proving
that valid rows normalize. -/
theorem rvfiCycleStepRefines_trace_refines
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : RvfiCycleStepRefines machine isa rel admit) :
    ∀ (state : State) (isaState : IsaState) (inputs : List Input),
      rel state isaState → (∀ i ∈ inputs, admit i) →
      cycleTrace machine.toCycleMachine state inputs =
        trace isa isaState
          (retireInputs machine.toCycleMachine state inputs) := by
  exact cycle_trace_refines (rvfiCycleStepRefines_toCycleStepRefines h)

/-- The strict packed-cycle contract also transports the relation to the
post-state retained by the RVFI machine, with bubbles omitted from the ISA
input stream exactly as in `rvfiStateAfter_refines`. -/
theorem rvfiCycleStepRefines_stateAfter_refines
    {State IsaState : Type}
    (machine : RvfiCycleMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Prop) (admit : Input → Prop)
    (h : RvfiCycleStepRefines machine isa rel admit) :
    ∀ (state : State) (isaState : IsaState) (inputs : List Input),
      rel state isaState → (∀ i ∈ inputs, admit i) →
      rel (rvfiStateAfter machine state inputs)
        (machineStateAfter isa isaState
          (retireInputs machine.toCycleMachine state inputs)) := by
  exact rvfiStateAfter_refines machine isa rel admit
    (rvfiCycleStepRefines_toCycleStepRefines h)

/-- A strict packed-cycle proof and a successful raw normalization certificate
compose to the ISA trace directly.  The normalization hypothesis checks the
wire-level validity and order, while the strict contract supplies the
architectural retirement and state relation; neither obligation is hidden in
the optional `toRetirement?` adapter. -/
theorem rvfiCycleStepRefines_normalized_trace_refines
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : RvfiCycleStepRefines machine isa rel admit)
    (state : State) (isaState : IsaState) (inputs : List Input)
    {start : Nat} {retirements : List Retirement}
    (hrel : rel state isaState)
    (hall : ∀ i ∈ inputs, admit i)
    (hnorm : normalizeRvfiTrace? start
        (rvfiObservations machine state inputs) = some retirements) :
    retirements = trace isa isaState
      (retireInputs machine.toCycleMachine state inputs) := by
  have hcycle := normalizeRvfiCycleTrace machine state inputs hnorm
  have htrace := rvfiCycleStepRefines_trace_refines h
    state isaState inputs hrel hall
  exact hcycle.symm.trans htrace

/-- The complete strict normalized RVFI boundary exposes the ISA trace and
the carried post-window relation together.  Raw normalization remains an
explicit premise, so a malformed valid row cannot disappear while obtaining
either conclusion. -/
theorem rvfiCycleStepRefines_normalized
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : RvfiCycleStepRefines machine isa rel admit)
    (state : State) (isaState : IsaState) (inputs : List Input)
    {start : Nat} {retirements : List Retirement}
    (hrel : rel state isaState)
    (hall : ∀ i ∈ inputs, admit i)
    (hnorm : normalizeRvfiTrace? start
        (rvfiObservations machine state inputs) = some retirements) :
    (retirements = trace isa isaState
      (retireInputs machine.toCycleMachine state inputs)) ∧
    rel (rvfiStateAfter machine state inputs)
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state inputs)) := by
  exact ⟨rvfiCycleStepRefines_normalized_trace_refines h state isaState inputs
      hrel hall hnorm,
    rvfiCycleStepRefines_stateAfter_refines machine isa rel admit h
      state isaState inputs hrel hall⟩

/-! An ordinary optional-cycle proof can consume the raw normalization
certificate directly once the separate valid-row well-formedness invariant is
available.  This wrapper keeps the strict bridge explicit while avoiding
repeated construction in loaded-core trace theorems. -/
theorem cycleStepRefines_normalized_trace_refines
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : CycleStepRefines machine.toCycleMachine isa rel admit)
    (hwell : ∀ (state : State) (input : Input),
      (machine.step state input).2.valid = true →
      (machine.step state input).2.wellFormed)
    (state : State) (isaState : IsaState) (inputs : List Input)
    {start : Nat} {retirements : List Retirement}
    (hrel : rel state isaState)
    (hall : ∀ i ∈ inputs, admit i)
    (hnorm : normalizeRvfiTrace? start
        (rvfiObservations machine state inputs) = some retirements) :
    retirements = trace isa isaState
      (retireInputs machine.toCycleMachine state inputs) := by
  exact rvfiCycleStepRefines_normalized_trace_refines
    (cycleStepRefines_to_rvfiCycleStepRefines h hwell)
    state isaState inputs hrel hall hnorm

/-! The optional-cycle form also exposes the complete normalized boundary:
the ISA trace equality and the relation carried by the retained core state.
The relation-aware form keeps the raw well-formedness premise restricted to
states that the invariant can actually reach. -/
theorem cycleStepRefines_normalized_of_rel
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : CycleStepRefines machine.toCycleMachine isa rel admit)
    (hwell : ∀ (state : State) (isaState : IsaState) (input : Input),
      rel state isaState → admit input →
      (machine.step state input).2.valid = true →
      (machine.step state input).2.wellFormed)
    (state : State) (isaState : IsaState) (inputs : List Input)
    {start : Nat} {retirements : List Retirement}
    (hrel : rel state isaState)
    (hall : ∀ i ∈ inputs, admit i)
    (hnorm : normalizeRvfiTrace? start
        (rvfiObservations machine state inputs) = some retirements) :
    (retirements = trace isa isaState
      (retireInputs machine.toCycleMachine state inputs)) ∧
    rel (rvfiStateAfter machine state inputs)
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state inputs)) := by
  exact rvfiCycleStepRefines_normalized
    (cycleStepRefines_to_rvfiCycleStepRefines_of_rel h hwell)
    state isaState inputs hrel hall hnorm

/-! The global-row normalized theorem is a convenience specialization of the
relation-aware boundary above. -/
theorem cycleStepRefines_normalized
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : CycleStepRefines machine.toCycleMachine isa rel admit)
    (hwell : ∀ (state : State) (input : Input),
      (machine.step state input).2.valid = true →
      (machine.step state input).2.wellFormed)
    (state : State) (isaState : IsaState) (inputs : List Input)
    {start : Nat} {retirements : List Retirement}
    (hrel : rel state isaState)
    (hall : ∀ i ∈ inputs, admit i)
    (hnorm : normalizeRvfiTrace? start
        (rvfiObservations machine state inputs) = some retirements) :
    (retirements = trace isa isaState
      (retireInputs machine.toCycleMachine state inputs)) ∧
    rel (rvfiStateAfter machine state inputs)
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state inputs)) := by
  exact cycleStepRefines_normalized_of_rel h
    (fun state _ input _ _ hvalid => hwell state input hvalid)
    state isaState inputs hrel hall hnorm

/-- Adjacent raw-normalized RVFI windows compose through the strict boundary.
The second certificate starts at the first window's retirement count, while
the strict step proof is applied once to the concatenated cycle input stream. -/
theorem rvfiCycleStepRefines_normalized_append
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : RvfiCycleStepRefines machine isa rel admit)
    (state : State) (isaState : IsaState)
    (first second : List Input)
    {start : Nat} {firstRetirements secondRetirements : List Retirement}
    (hrel : rel state isaState)
    (hall : ∀ i ∈ first ++ second, admit i)
    (hfirst : normalizeRvfiTrace? start
        (rvfiObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiObservations machine
          (rvfiStateAfter machine state first) second) =
      some secondRetirements) :
    (firstRetirements ++ secondRetirements =
      trace isa isaState
        (retireInputs machine.toCycleMachine state (first ++ second))) ∧
    rel (rvfiStateAfter machine state (first ++ second))
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state (first ++ second))) := by
  have hcombined := normalizeRvfiCycleTrace_append machine state first second
    hfirst hsecond
  exact rvfiCycleStepRefines_normalized h state isaState (first ++ second)
    hrel hall hcombined

/-! Adjacent normalized windows can use the optional cycle contract as well.
The relation-aware form keeps the raw well-formedness premise restricted to
related, admitted states. -/
theorem cycleStepRefines_normalized_append_of_rel
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : CycleStepRefines machine.toCycleMachine isa rel admit)
    (hwell : ∀ (state : State) (isaState : IsaState) (input : Input),
      rel state isaState → admit input →
      (machine.step state input).2.valid = true →
      (machine.step state input).2.wellFormed)
    (state : State) (isaState : IsaState)
    (first second : List Input)
    {start : Nat} {firstRetirements secondRetirements : List Retirement}
    (hrel : rel state isaState)
    (hall : ∀ i ∈ first ++ second, admit i)
    (hfirst : normalizeRvfiTrace? start
        (rvfiObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiObservations machine
          (rvfiStateAfter machine state first) second) =
      some secondRetirements) :
    (firstRetirements ++ secondRetirements =
      trace isa isaState
        (retireInputs machine.toCycleMachine state (first ++ second))) ∧
    rel (rvfiStateAfter machine state (first ++ second))
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state (first ++ second))) := by
  exact rvfiCycleStepRefines_normalized_append
    (cycleStepRefines_to_rvfiCycleStepRefines_of_rel h hwell)
    state isaState first second hrel hall hfirst hsecond

/-! The global-row append theorem is a convenience specialization of the
relation-aware boundary above. -/
theorem cycleStepRefines_normalized_append
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : CycleStepRefines machine.toCycleMachine isa rel admit)
    (hwell : ∀ (state : State) (input : Input),
      (machine.step state input).2.valid = true →
      (machine.step state input).2.wellFormed)
    (state : State) (isaState : IsaState)
    (first second : List Input)
    {start : Nat} {firstRetirements secondRetirements : List Retirement}
    (hrel : rel state isaState)
    (hall : ∀ i ∈ first ++ second, admit i)
    (hfirst : normalizeRvfiTrace? start
        (rvfiObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiObservations machine
          (rvfiStateAfter machine state first) second) =
      some secondRetirements) :
    (firstRetirements ++ secondRetirements =
      trace isa isaState
        (retireInputs machine.toCycleMachine state (first ++ second))) ∧
    rel (rvfiStateAfter machine state (first ++ second))
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state (first ++ second))) := by
  exact cycleStepRefines_normalized_append_of_rel h
    (fun state _ input _ _ hvalid => hwell state input hvalid)
    state isaState first second hrel hall hfirst hsecond

/-! A normalized two-window proof also exposes the relation at the boundary
between the windows.  The second window is checked from the ISA state reached
by the first retiring-input stream, so a loaded-core invariant can be resumed
at a raw observation boundary without rebuilding the prefix proof. -/
theorem rvfiCycleStepRefines_normalized_chain
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : RvfiCycleStepRefines machine isa rel admit)
    (state : State) (isaState : IsaState)
    (first second : List Input)
    {start : Nat} {firstRetirements secondRetirements : List Retirement}
    (hrel : rel state isaState)
    (hallFirst : ∀ i ∈ first, admit i)
    (hallSecond : ∀ i ∈ second, admit i)
    (hfirst : normalizeRvfiTrace? start
        (rvfiObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiObservations machine
          (rvfiStateAfter machine state first) second) =
      some secondRetirements) :
    (firstRetirements = trace isa isaState
      (retireInputs machine.toCycleMachine state first)) ∧
    rel (rvfiStateAfter machine state first)
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state first)) ∧
    (secondRetirements = trace isa
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state first))
      (retireInputs machine.toCycleMachine
        (rvfiStateAfter machine state first) second)) ∧
    rel (rvfiStateAfter machine state (first ++ second))
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state (first ++ second))) := by
  have hfirstBoundary := rvfiCycleStepRefines_normalized h state isaState first
    hrel hallFirst hfirst
  have hsecondBoundary := rvfiCycleStepRefines_normalized h
    (rvfiStateAfter machine state first)
    (machineStateAfter isa isaState
      (retireInputs machine.toCycleMachine state first))
    second hfirstBoundary.2 hallSecond hsecond
  have hfinal : rel (rvfiStateAfter machine state (first ++ second))
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state (first ++ second))) := by
    rw [rvfiStateAfter_append]
    rw [retireInputs_append]
    rw [RvfiCycleMachine.toCycleMachine_stateAfter]
    rw [machineStateAfter_append]
    exact hsecondBoundary.2
  exact ⟨hfirstBoundary.1, hfirstBoundary.2,
    hsecondBoundary.1, hfinal⟩

/-! The optional cycle contract has the same segmented boundary theorem.
The relation-aware form keeps the raw well-formedness premise restricted to
the exact state/ISA pairs reached by the invariant. -/
theorem cycleStepRefines_normalized_chain_of_rel
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : CycleStepRefines machine.toCycleMachine isa rel admit)
    (hwell : ∀ (state : State) (isaState : IsaState) (input : Input),
      rel state isaState → admit input →
      (machine.step state input).2.valid = true →
      (machine.step state input).2.wellFormed)
    (state : State) (isaState : IsaState)
    (first second : List Input)
    {start : Nat} {firstRetirements secondRetirements : List Retirement}
    (hrel : rel state isaState)
    (hallFirst : ∀ i ∈ first, admit i)
    (hallSecond : ∀ i ∈ second, admit i)
    (hfirst : normalizeRvfiTrace? start
        (rvfiObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiObservations machine
          (rvfiStateAfter machine state first) second) =
      some secondRetirements) :
    (firstRetirements = trace isa isaState
      (retireInputs machine.toCycleMachine state first)) ∧
    rel (rvfiStateAfter machine state first)
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state first)) ∧
    (secondRetirements = trace isa
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state first))
      (retireInputs machine.toCycleMachine
        (rvfiStateAfter machine state first) second)) ∧
    rel (rvfiStateAfter machine state (first ++ second))
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state (first ++ second))) := by
  exact rvfiCycleStepRefines_normalized_chain
    (cycleStepRefines_to_rvfiCycleStepRefines_of_rel h hwell)
    state isaState first second hrel hallFirst hallSecond hfirst hsecond

/-! The global-row chain theorem is a convenience specialization of the
relation-aware segmented boundary. -/
theorem cycleStepRefines_normalized_chain
    {State IsaState : Type}
    {machine : RvfiCycleMachine State} {isa : Machine IsaState}
    {rel : State → IsaState → Prop} {admit : Input → Prop}
    (h : CycleStepRefines machine.toCycleMachine isa rel admit)
    (hwell : ∀ (state : State) (input : Input),
      (machine.step state input).2.valid = true →
      (machine.step state input).2.wellFormed)
    (state : State) (isaState : IsaState)
    (first second : List Input)
    {start : Nat} {firstRetirements secondRetirements : List Retirement}
    (hrel : rel state isaState)
    (hallFirst : ∀ i ∈ first, admit i)
    (hallSecond : ∀ i ∈ second, admit i)
    (hfirst : normalizeRvfiTrace? start
        (rvfiObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiObservations machine
          (rvfiStateAfter machine state first) second) =
      some secondRetirements) :
    (firstRetirements = trace isa isaState
      (retireInputs machine.toCycleMachine state first)) ∧
    rel (rvfiStateAfter machine state first)
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state first)) ∧
    (secondRetirements = trace isa
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state first))
      (retireInputs machine.toCycleMachine
        (rvfiStateAfter machine state first) second)) ∧
    rel (rvfiStateAfter machine state (first ++ second))
      (machineStateAfter isa isaState
        (retireInputs machine.toCycleMachine state (first ++ second))) := by
  exact cycleStepRefines_normalized_chain_of_rel h
    (fun state _ input _ _ hvalid => hwell state input hvalid)
    state isaState first second hrel hallFirst hallSecond hfirst hsecond

/-! ## Encoding an existing semantic retirement -/

structure RvfiMemFields where
  addr : Word := 0
  rmask : ByteMask := 0
  wmask : ByteMask := 0
  rdata : Word := 0
  wdata : Word := 0

def memoryFields : Option MemoryEffect → RvfiMemFields
  | none => {}
  | some (.read address width data) =>
      { addr := address, rmask := maskOfWidth width, rdata := data }
  | some (.write address width data) =>
      { addr := address, wmask := maskOfWidth width, wdata := data }

@[simp] theorem validMaskB_maskOfWidth (width : MemW) :
    validMaskB (maskOfWidth width) = true := by
  cases width <;> decide

@[simp] theorem memoryFields_rmask_valid (memory : Option MemoryEffect) :
    validMaskB (memoryFields memory).rmask = true := by
  cases memory with
  | none => rfl
  | some effect =>
      cases effect with
      | read address width data =>
          cases width <;> rfl
      | write address width data =>
          rfl

@[simp] theorem memoryFields_wmask_valid (memory : Option MemoryEffect) :
    validMaskB (memoryFields memory).wmask = true := by
  cases memory with
  | none => rfl
  | some effect =>
      cases effect with
      | read address width data =>
          rfl
      | write address width data =>
          cases width <;> rfl

@[simp] theorem memoryFields_exclusive (memory : Option MemoryEffect) :
    (memoryFields memory).rmask = 0 || (memoryFields memory).wmask = 0 := by
  cases memory with
  | none => simp [memoryFields]
  | some effect =>
      cases effect with
      | read address width data => simp [memoryFields]
      | write address width data => simp [memoryFields]

def trapFlag : Option Cause → Bool
  | none => false
  | some _ => true

def intrFlag : Option Cause → Bool
  | none => false
  | some c => c.isInterrupt

def RvfiObservation.ofRetirement (r : Retirement)
    (rd : Option (Reg × Word)) : RvfiObservation :=
  let mf := memoryFields r.memory
  let (rdAddr, rdWdata, rdValid) := match rd with
    | none => (0, 0, false)
    | some (reg, data) => (reg, data, true)
  { valid := true
    order := 0
    insn := r.instr
    pcRdata := r.pc
    pcWdata := r.nextPc
    trap := trapFlag r.trap
    intr := intrFlag r.trap
    rdAddr := rdAddr
    rdWdata := rdWdata
    rdWdataValid := rdValid
    memAddr := mf.addr
    memRmask := mf.rmask
    memWmask := mf.wmask
    memRdata := mf.rdata
    memWdata := mf.wdata
    cause := r.trap }

/-- A `Retirement` is RVFI-representable when it has at most one non-x0 write.
The RISC-V step adapter has exactly this shape; keeping the predicate explicit
prevents a future multi-write ISA extension from being truncated silently. -/
def Retirement.rvfiRepresentable (r : Retirement) : Prop :=
  r.writes = [] ∨
    ∃ reg data, reg ≠ 0 ∧ r.writes = [(reg, data)]

def Retirement.toRvfi? (r : Retirement) : Option RvfiObservation :=
  match r.writes with
  | [] => some (RvfiObservation.ofRetirement r none)
  | [(reg, data)] =>
      if reg = 0 then none
      else some (RvfiObservation.ofRetirement r (some (reg, data)))
  | _ => none

theorem RvfiObservation.ofRetirement_wellFormed (r : Retirement)
    (rd : Option (Reg × Word)) :
    (RvfiObservation.ofRetirement r rd).wellFormed := by
  cases r with
  | mk pc instr nextPc writes memory trap =>
      cases memory with
      | none =>
          cases trap with
          | none => cases rd <;> rfl
          | some c => cases c <;> cases rd <;> rfl
      | some effect =>
          cases effect with
          | read address width data =>
              cases width <;>
                cases trap with
                | none => cases rd <;> rfl
                | some c => cases c <;> cases rd <;> rfl
          | write address width data =>
              cases width <;>
                cases trap with
                | none => cases rd <;> rfl
                | some c => cases c <;> cases rd <;> rfl

theorem RvfiObservation.ofRetirement_toRetirement? (r : Retirement)
    (rd : Option (Reg × Word)) :
    (RvfiObservation.ofRetirement r rd).toRetirement? =
      some (RvfiObservation.ofRetirement r rd).toRetirement := by
  exact RvfiObservation.toRetirement?_eq_some _ rfl
    (RvfiObservation.ofRetirement_wellFormed r rd)

/-! ## Lossless representable-retirement round trip -/

private theorem ofRetirement_none_toRetirement (r : Retirement)
    (hwrites : r.writes = []) :
    (RvfiObservation.ofRetirement r none).toRetirement = r := by
  cases r with
  | mk pc instr nextPc writes memory trap =>
    cases hwrites
    cases memory with
    | none =>
        simp [RvfiObservation.ofRetirement, RvfiObservation.toRetirement,
          RvfiObservation.memoryEffect?, memoryFields, widthOfMask, maskOfWidth]
    | some effect =>
        cases effect with
        | read address width data =>
            cases width <;>
              simp [RvfiObservation.ofRetirement, RvfiObservation.toRetirement,
                RvfiObservation.memoryEffect?, memoryFields, widthOfMask,
                maskOfWidth]
        | write address width data =>
            cases width <;>
              simp [RvfiObservation.ofRetirement, RvfiObservation.toRetirement,
                RvfiObservation.memoryEffect?, memoryFields, widthOfMask,
                maskOfWidth]

private theorem ofRetirement_some_toRetirement (r : Retirement)
    (reg : Reg) (data : Word) (hreg : reg ≠ 0)
    (hwrites : r.writes = [(reg, data)]) :
    (RvfiObservation.ofRetirement r (some (reg, data))).toRetirement = r := by
  cases r with
  | mk pc instr nextPc writes memory trap =>
    cases hwrites
    cases memory with
    | none =>
        simp [RvfiObservation.ofRetirement, RvfiObservation.toRetirement,
          RvfiObservation.memoryEffect?, memoryFields, widthOfMask, maskOfWidth,
          hreg]
    | some effect =>
        cases effect with
        | read address width data' =>
            cases width <;>
              simp [RvfiObservation.ofRetirement, RvfiObservation.toRetirement,
                RvfiObservation.memoryEffect?, memoryFields, widthOfMask,
                maskOfWidth, hreg]
        | write address width data' =>
            cases width <;>
              simp [RvfiObservation.ofRetirement, RvfiObservation.toRetirement,
                RvfiObservation.memoryEffect?, memoryFields, widthOfMask,
                maskOfWidth, hreg]

/-- Encoding and immediately decoding a representable retirement preserves it.

The predicate is explicit because RVFI's packed shape has room for at most one
non-`x0` register write.  A caller that has more writes must provide a wider
interface instead of silently truncating the list. -/
theorem Retirement.toRvfi?_bind_toRetirement? (r : Retirement)
    (h : r.rvfiRepresentable) :
    (r.toRvfi?).bind RvfiObservation.toRetirement? = some r := by
  rcases h with hwrites | ⟨reg, data, hreg, hwrites⟩
  · simp only [Retirement.toRvfi?, hwrites, Option.bind_some]
    rw [RvfiObservation.ofRetirement_toRetirement?]
    exact congrArg some (ofRetirement_none_toRetirement r hwrites)
  · simp only [Retirement.toRvfi?, hwrites]
    have hzero : ¬ reg = 0 := hreg
    simp only [hzero, ↓reduceIte, Option.bind_some]
    rw [RvfiObservation.ofRetirement_toRetirement?]
    exact congrArg some (ofRetirement_some_toRetirement r reg data hreg hwrites)

end LeanModels.Refine

#print axioms LeanModels.Refine.RvfiObservation.ofRetirement_toRetirement?
#print axioms LeanModels.Refine.RvfiObservation.wellFormed_of_toRetirement?_eq_some
#print axioms LeanModels.Refine.RvfiObservation.toRetirement?_eq_some_iff
#print axioms LeanModels.Refine.RvfiObservation.toRetirement?_eq_none_iff
#print axioms LeanModels.Refine.normalizeRvfiTrace?_eq_none_iff
#print axioms LeanModels.Refine.Retirement.toRvfi?_bind_toRetirement?
#print axioms LeanModels.Refine.rvfiCycleStepRefines_toCycleStepRefines
#print axioms LeanModels.Refine.rvfiCycleStepRefines_valid_step
#print axioms LeanModels.Refine.rvfiCycleStepRefines_invalid_step
#print axioms LeanModels.Refine.rvfiCycleStepRefines_step
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_step
#print axioms LeanModels.Refine.cycleStepRefines_to_rvfiCycleStepRefines_of_rel
#print axioms LeanModels.Refine.cycleStepRefines_to_rvfiCycleStepRefines
#print axioms LeanModels.Refine.cycleStepRefines_iff_rvfiCycleStepRefines_of_rel
#print axioms LeanModels.Refine.cycleStepRefines_iff_rvfiCycleStepRefines
#print axioms LeanModels.Refine.rvfiCycleStepRefines_iff_step
#print axioms LeanModels.Refine.rvfiCycleStepRefines_trace_refines
#print axioms LeanModels.Refine.rvfiCycleStepRefines_stateAfter_refines
#print axioms LeanModels.Refine.rvfiCycleStepRefines_normalized_trace_refines
#print axioms LeanModels.Refine.rvfiCycleStepRefines_normalized
#print axioms LeanModels.Refine.cycleStepRefines_normalized_trace_refines
#print axioms LeanModels.Refine.cycleStepRefines_normalized_of_rel
#print axioms LeanModels.Refine.cycleStepRefines_normalized
#print axioms LeanModels.Refine.cycleStepRefines_normalized_append_of_rel
#print axioms LeanModels.Refine.cycleStepRefines_normalized_append
#print axioms LeanModels.Refine.cycleStepRefines_normalized_chain_of_rel
#print axioms LeanModels.Refine.cycleStepRefines_normalized_chain
#print axioms LeanModels.Refine.rvfiCycleStepRefines_normalized_append
#print axioms LeanModels.Refine.rvfiCycleStepRefines_normalized_chain
#print axioms LeanModels.Refine.normalizeRvfiTrace?_iff
#print axioms LeanModels.Refine.normalizeRvfiTrace?_wellFormed
#print axioms LeanModels.Refine.normalizeRvfiTrace?_append
#print axioms LeanModels.Refine.normalizeRvfiTrace?_filterMap
#print axioms LeanModels.Refine.RvfiCycleMachine.toCycleMachine_stateAfter
#print axioms LeanModels.Refine.rvfiStateAfter_refines
#print axioms LeanModels.Refine.rvfiStateAfter_append
#print axioms LeanModels.Refine.rvfiObservations_append
#print axioms LeanModels.Refine.normalizeRvfiCycleTrace_append
#print axioms LeanModels.Refine.normalizeRvfiCycleTrace
#print axioms LeanModels.Refine.normalizeRvfiCycleTrace_input_length
