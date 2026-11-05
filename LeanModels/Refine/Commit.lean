import LeanModels.Rv.Step

/-!
# Commit observations and one-step refinement

This is the core-level interface for the R1 rung.  A hardware design may take
many clocked and combinational steps between two architectural retirements;
the proof exposes only one `Retirement` for each committed instruction.  The
interface is deliberately independent of a particular core and of the SV
backend: a core is a state machine fed by an always-ready instruction/data
input, and an ISA model is another state machine over the same input.

`StepRefines` is a forward simulation.  It quantifies an admission predicate
over inputs, so a later core can state its RV32I subset without changing the
observation type.  `trace_refines` is the reusable induction that turns the
one-step contract into equality of retired-instruction streams.

The RISC-V adapter below uses `LeanModels.Rv.isaStep` as the architectural
step.  Its memory input is a total byte function (`Rv.Mem`), so there is no
wait-state or cache nondeterminism in this first memory model.  A later core
can refine that input protocol while retaining the same `Retirement` and
`StepRefines` definitions.
-/

namespace LeanModels.Refine

open LeanModels.Rv

abbrev Word := BitVec 32
abbrev Memory := Rv.Mem

/-- The always-ready instruction/data input at one architectural step. -/
structure Input where
  fetched : Rv.Fetched
  memory : Memory
  irq : Word := 0

/-- A memory operation observed at retirement.  Reads carry the value returned
by the always-ready memory; writes carry the value presented by the core. -/
inductive MemoryEffect where
  | read (address : Word) (width : Rv.MemW) (data : Word)
  | write (address : Word) (width : Rv.MemW) (data : Word)
  deriving DecidableEq, Repr

/-- The commit-level observation, modelled on RVFI's retirement tuple.

`writes` is a list rather than a single optional register because it is the
stable interface for future instructions that expose more than one
architectural update.  The RV32I/RV32M adapter emits at most one entry. -/
structure Retirement where
  pc : Word
  instr : Word
  nextPc : Word
  writes : List (Rv.Reg × Word)
  memory : Option MemoryEffect := none
  trap : Option Rv.Cause := none
  deriving DecidableEq, Repr

/-- A finite-state core or architectural model. -/
structure Machine (State : Type) where
  init : State
  step : State → Input → State × Retirement

/-- The retired stream produced by a machine on an input sequence. -/
def trace {State : Type} (m : Machine State) : State → List Input → List Retirement
  | _, [] => []
  | s, i :: is =>
      let (s', o) := m.step s i
      o :: trace m s' is

/-! ## RISC-V adapter -/

/-- The raw parcel bits used in the commit observation.  A compressed parcel
is zero-extended here; the architectural decoder still retains the original
`Fetched.half`, so no compressed instruction is silently reinterpreted. -/
def fetchedBits : Rv.Fetched → Word
  | .word w => w
  | .half h => h.setWidth 32

/-- Register differences are the architectural register effects of a step. -/
def regWrites (before after : Rv.ArchState) : List (Rv.Reg × Word) :=
  (List.finRange 32).filterMap fun r =>
    if before.readReg r == after.readReg r then none else some (r, after.readReg r)

private def memEffect (m : Memory) (f : Rv.Fetched) : Option Rv.MemEffect → Option MemoryEffect
  | none => none
  | some (.write address width data) => some (.write address width data)
  | some (.read address width) =>
      let signed := match f.decode with
        | some (.mem (.load signed) _ _ _ _) => signed
        | _ => false
      some (.read address width (Rv.loadVal m width signed address))

/-- Turn the ISA step's effects plus its before/after states into RVFI-shaped
retirement data. -/
def Retirement.ofRvStep (before : Rv.ArchState) (input : Input)
    (after : Rv.ArchState) (effects : Rv.StepEffects) : Retirement :=
  { pc := before.pc
    instr := fetchedBits input.fetched
    nextPc := after.pc
    writes := regWrites before after
    memory := memEffect input.memory input.fetched effects.mem
    trap := effects.trap }

/-- The official model exposed through the generic machine interface. -/
def rvMachine : Machine Rv.ArchState where
  init := Rv.ArchState.init 0
  step s input :=
    let (s', e) := Rv.isaStep s input.memory input.fetched input.irq
    (s', Retirement.ofRvStep s input s' e)

/-! ## The reusable refinement statement -/

/-- One-step forward simulation from a core state to an ISA state.  `admit`
is the architectural subset (for example, RV32I without interrupts); keeping
it as a predicate means the same observation type serves every later core. -/
def StepRefines {CoreState IsaState : Type}
    (core : Machine CoreState) (isa : Machine IsaState)
    (rel : CoreState → IsaState → Prop) (admit : Input → Prop) : Prop :=
  rel core.init isa.init ∧
    ∀ (c : CoreState) (a : IsaState) (input : Input),
      rel c a → admit input →
      let (c', co) := core.step c input
      let (a', io) := isa.step a input
      rel c' a' ∧ co = io

/-- Equality of committed streams follows by induction from `StepRefines`.
This is the theorem every core-specific proof consumes; it mentions neither
SV syntax nor the internals of the chosen ISA model. -/
theorem trace_refines {CoreState IsaState : Type}
    {core : Machine CoreState} {isa : Machine IsaState}
    {rel : CoreState → IsaState → Prop} {admit : Input → Prop}
    (h : StepRefines core isa rel admit) :
    ∀ (c : CoreState) (a : IsaState) (inputs : List Input),
      rel c a → (∀ i ∈ inputs, admit i) →
      trace core c inputs = trace isa a inputs := by
  intro c a inputs hrel
  induction inputs generalizing c a with
  | nil =>
      intro _
      rfl
  | cons input rest ih =>
      intro hall
      have hi : admit input := hall input (by simp)
      have hrest : ∀ i ∈ rest, admit i := by
        intro i hi'
        exact hall i (by simp [hi'])
      have hs := h.2 c a input hrel hi
      rcases hC : core.step c input with ⟨c', co⟩
      rcases hI : isa.step a input with ⟨a', io⟩
      simp only [trace, hC, hI]
      rcases hs with ⟨hrel', hout⟩
      simp only [hC, hI] at hrel' hout
      rw [hout, ih c' a' hrel' hrest]

end LeanModels.Refine
