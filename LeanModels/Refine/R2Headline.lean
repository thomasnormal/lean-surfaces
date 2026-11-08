import LeanModels.Refine.RvfiProgress

/-!
# The R2 headline

This is the end-to-end statement the loaded core must eventually discharge.
`machine` is the parsed core's RVFI cycle port, `profile` selects the
stateful RV32I model, and `rel` is the core-to-ISA invariant.  The cycle
schedule is allowed to stutter; `target` names the retirement-input stream.
The progress premise says that every finite target prefix is reached by some
finite cycle boundary, so the result is an all-prefix statement rather than a
captured finite window.

The current R0 implementation is `rvMemoryMachineWith profile`.  Its profile
and the four core-side premises below remain explicit parameters until a real
loaded core supplies them.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- From reset, every finite prefix of a legal RV32I retirement stream is
represented by a finite core cycle boundary with the same committed stream as
the stateful ISA model, and with the retained core state related to the ISA
state after that target prefix. -/
def Rv32iR2Headline {State : Type}
    (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop)
    (schedule target : Nat → Input) : Prop :=
  ∀ k : Nat, ∃ boundary : Nat,
    cycleTrace machine.toCycleMachine machine.init
        (schedulePrefix schedule boundary) =
      trace (rvMemoryMachineWith profile)
        (rvMemoryMachineWith profile).init (schedulePrefix target k) ∧
    rel (rvfiStateAfter machine machine.init
        (schedulePrefix schedule boundary))
      (rvMemoryStateAfter profile (rvMemoryMachineWith profile).init
        (schedulePrefix target k))

/-- The named R2 headline follows from the loaded core's indexed RV32I step
invariant, reset relation, pointwise admission, and explicit progress witness.
These premises are the exact obligations a future PicoRV32 proof must supply;
the theorem itself chooses no RTL state, schedule, or decoder resolution. -/
theorem rv32i_r2_headline
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hstep : Rv32iCycleStepRefines machine rel admit)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget machine machine.init schedule target) :
    Rv32iR2Headline profile machine rel schedule target := by
  exact rv32i_reset_stream_refines profile machine rel admit hstep hinit
    hschedule progress

#print axioms LeanModels.Refine.rv32i_r2_headline

end LeanModels.Refine
