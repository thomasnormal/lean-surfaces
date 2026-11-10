import LeanModels.Sv.Observe
import LeanModels.Refine.RvfiRv32iProgram

/-!
# Retirement refinement from E observations

**Status: derived from E's observation interface, conditional on the loaded
core's invariant.** No loaded core is certified here. E supplies every run,
choice, environment, and pre/post sample; there is no cycle executor in this
bridge. A partial port decoder must account for every sample, including
bubbles. Failure to decode a four-state port value cannot erase a cycle.

The invariant is indexed by retirement order. Its transition spans the
interval from the preceding cycle's post sample (the first pre sample at
reset) to this cycle's post sample, including intervening E steps. Bubbles
retain both the ISA state and the order. Retirements use the existing mixed
RV32I boundary and advance the order once. Samples remain chronological.

This is the finite safety part of R2. Existence of completed E behaviours,
memory/environment admission, and retirement progress remain separate core
obligations. This safety theorem establishes neither completion nor progress
toward a requested retirement prefix.
-/

namespace LeanModels.Refine

open LeanModels.Rv
open LeanModels.Sv.Observe

set_option autoImplicit false

namespace RvfiE

/-- Decode every trusted cycle sample, in order. `none` is a failed decode,
not a bubble: a bubble is a successfully decoded row with `valid = false`. -/
def decodeSamples (decode : CycleObs PortSample → Option RvfiObservation) :
    List (CycleObs PortSample) → Option (List RvfiObservation)
  | [] => some []
  | sample :: samples => do
      let row ← decode sample
      let rows ← decodeSamples decode samples
      pure (row :: rows)

/-- The existing E interface's two trusted port samples at cycle `cycle`. -/
def sample (E : ESig) (d : E.Elab) (env : E.Env)
    (b : Nat → E.Config) (cycle : Nat) : CycleObs PortSample :=
  (CycleObs.mk (E.preponed b (E.edgeSlot env cycle))
    (b (E.edgeSlot env cycle))).map ((Obs_E E).sample d)

/-- Cut points of an actual E run. The initial cut is before its first
observed edge; subsequent cuts are the preceding cycle's post sample. -/
def boundary (E : ESig) (env : E.Env) (b : Nat → E.Config) : Nat → E.Config
  | 0 => E.preponed b (E.edgeSlot env 0)
  | cycle + 1 => b (E.edgeSlot env cycle)

/-- The loaded core's per-cycle proof obligation, on E's actual cut points.
Each order obligation requires that same index in the state relation.
The decoder reads only declared ports. -/
def StepRefines (E : ESig) (d : E.Elab)
    (decode : CycleObs PortSample → Option RvfiObservation)
    (rel : Nat → E.Config → RvMemoryState → Prop)
    (env : E.Env) (b : Nat → E.Config) : Prop :=
  ∀ cycle, cycle < E.cycles env →
    ∀ order state, rel order (boundary E env b cycle) state →
    ∃ row, decode (sample E d env b cycle) = some row ∧
      if row.valid then
        ∃ instruction,
          row.order = order ∧
          Rv32iBoundary state.arch (rv32iProgramInput state instruction) row
            (rv32iProgramStep state instruction)
            (rv32iProgramRetirement state instruction) ∧
          rel (order + 1) (boundary E env b (cycle + 1))
            (rv32iProgramStep state instruction)
      else rel order (boundary E env b (cycle + 1)) state

/-- The observable finite R2 safety claim. Every cycle decodes, RVFI order
is consecutive from reset, and the committed stream is the existing stateful
RV32I machine's stream for the witnessed mixed program. -/
def TraceRefines (profile : PlatformProfile) (initial : RvMemoryState)
    (decode : CycleObs PortSample → Option RvfiObservation)
    (samples : List (CycleObs PortSample)) : Prop :=
  ∃ rows program,
    decodeSamples decode samples = some rows ∧
    normalizeRvfiTrace? 0 rows =
      some (trace (rvMemoryMachineWith profile) initial
        (rv32iProgramInputs initial program))

private theorem trace_of_step
    {E : ESig} {d : E.Elab}
    {decode : CycleObs PortSample → Option RvfiObservation}
    {rel : Nat → E.Config → RvMemoryState → Prop}
    {env : E.Env} {b : Nat → E.Config}
    (hstep : StepRefines E d decode rel env b)
    (memory : Memory) (count offset order : Nat) (state : RvMemoryState)
    (hbound : offset + count ≤ E.cycles env)
    (hrel : rel order (boundary E env b offset) state) :
    ∃ rows program,
      decodeSamples decode ((List.range' offset count).map (sample E d env b)) =
        some rows ∧
      Rv32iRvfiTrace memory order state rows program ∧
      rel (order + program.length) (boundary E env b (offset + count))
        (rv32iProgramState state program) := by
  induction count generalizing offset order state with
  | zero =>
      exact ⟨[], [], rfl, .nil order state, by simpa [rv32iProgramState] using hrel⟩
  | succ count ih =>
      obtain ⟨row, hdecode, hrow⟩ := hstep offset (by omega) order state hrel
      by_cases hvalid : row.valid = true
      · simp only [hvalid, ite_true] at hrow
        obtain ⟨instruction, horder, hboundary, hnext⟩ := hrow
        obtain ⟨rows, program, hdecodeTail, htrace, hfinal⟩ :=
          ih (offset + 1) (order + 1) (rv32iProgramStep state instruction)
            (by omega) hnext
        refine ⟨row :: rows, instruction :: program, ?_,
          .retire horder hboundary htrace, ?_⟩
        · simp [List.range'_succ, decodeSamples, hdecode, hdecodeTail]
        · simpa [rv32iProgramState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hfinal
      · have hfalse : row.valid = false := by cases h : row.valid <;> simp_all
        simp only [hfalse, Bool.false_eq_true, ite_false] at hrow
        obtain ⟨rows, program, hdecodeTail, htrace, hfinal⟩ :=
          ih (offset + 1) order state (by omega) hrow
        refine ⟨row :: rows, program, ?_, .bubble hfalse htrace, ?_⟩
        · simp [List.range'_succ, decodeSamples, hdecode, hdecodeTail]
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal

/-- The indexed invariant proves finite retirement safety for every legal E
choice, admitted environment, and completed E behaviour. No particular
schedule or unknown-value resolution is selected by this theorem.

`hinit` includes reset and the inter-edge environment obligations. `hstep`
must be proved on the loaded design's E runs; it is not an executable cycle
model. Progress is deliberately not inferred from this safety conclusion. -/
theorem safe_of_invariant
    (E : ESig) (d : E.Elab) (clocking : Clocking) (admit : E.Env → Prop)
    (profile : PlatformProfile) (initial : RvMemoryState)
    (decode : CycleObs PortSample → Option RvfiObservation)
    (rel : Nat → E.Config → RvMemoryState → Prop)
    (hinit : ∀ ch env b, admit env → E.Disciplined clocking env →
      E.Behaves d env ch b → rel 0 (boundary E env b 0) initial)
    (hstep : ∀ ch env b, admit env → E.Disciplined clocking env →
      E.Behaves d env ch b → StepRefines E d decode rel env b) :
    (Obs_E E).SafeOn clocking d admit
      (fun _ samples => TraceRefines profile initial decode samples) := by
  intro ch env samples hadmit hdisc hbehaves
  obtain ⟨probes, ⟨b, hb, hprobes⟩, hsamples⟩ := hbehaves
  obtain ⟨rows, program, hdecode, htrace, _⟩ :=
    trace_of_step (hstep ch env b hadmit hdisc hb)
      initial.memory (E.cycles env) 0 0 initial (by omega)
      (hinit ch env b hadmit hdisc hb)
  refine ⟨rows, program, ?_, htrace.trace_refines profile⟩
  subst probes
  subst samples
  change decodeSamples decode
    (((List.range (E.cycles env)).map fun cycle =>
      CycleObs.mk (E.preponed b (E.edgeSlot env cycle))
        (b (E.edgeSlot env cycle))).map (CycleObs.map ((Obs_E E).sample d))) = some rows
  dsimp only [Obs_E]
  rw [List.map_map, List.range_eq_range']
  change decodeSamples decode
    ((List.range' 0 (E.cycles env)).map (RvfiE.sample E d env b)) = some rows
  exact hdecode

end RvfiE

#print axioms RvfiE.safe_of_invariant

end LeanModels.Refine
