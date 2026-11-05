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

@[simp] theorem RvfiCycleMachine.toCycleMachine_init {State : Type}
    (machine : RvfiCycleMachine State) :
    machine.toCycleMachine.init = machine.init := rfl

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
#print axioms LeanModels.Refine.Retirement.toRvfi?_bind_toRetirement?
#print axioms LeanModels.Refine.normalizeRvfiTrace?_iff
#print axioms LeanModels.Refine.normalizeRvfiTrace?_append
