/-
sunfish pin shard: THE TRANSPORT THEOREM — an empty-trace probe
transported to every seeded trace.

SHARD of the `pins_clock` battery (2026-08-25 topology change): the prose
and the shard map are in `pins_clock.lean`. Every `#guard` moved VERBATIM;
`searcherWT`/`boundProbeT` moved to `pins_common.lean` unchanged.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_clock_transport

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

/-- **The transport**: a probe decided at the EMPTY trace answers the
same pair under EVERY seeded trace — `evalExpr`/`callIn` clock erasure
composed through the probe's projections (heap reads never see the
clock). -/
theorem boundProbeT_all_traces {pos : RVal} {gamma depth : Int}
    {p : Int × Int} (h : boundProbeT [] pos gamma depth = some p)
    (tr : ClockTrace) : boundProbeT tr pos gamma depth = some p := by
  unfold boundProbeT searcherWT at h ⊢
  rw [World.withClock_self (initWorld_clock sunfish)] at h
  obtain ⟨hok, -, -⟩ :=
    evalExpr_clockErased 4096 sunfish ⟨initWorld sunfish, []⟩
      (.call (.name "Searcher" sp0) #[] #[] Option.none sp0)
      (initWorld_clock sunfish)
  cases hrun : evalExpr sunfish 4096 ⟨initWorld sunfish, []⟩
      (.call (.name "Searcher" sp0) #[] #[] Option.none sp0) with
  | ok st v =>
    obtain ⟨hst, hy⟩ := hok st v hrun
    simp only [FrameState.withClock_mk] at hy
    rw [hrun] at h
    simp only [hy]
    cases v <;> try (simp_all)
    case ref a =>
      try simp only [FrameState.withClock_world, FrameState.withClock_locals,
        World.withClock_heap, World.withClock_globals]
      obtain ⟨hok2, -, -⟩ :=
        callIn_clockErased 1000000 sunfish st.world "Searcher.bound"
          #[.ref a, pos, .int gamma, .int depth] hst
    -- the base h reduced to the callIn match at st.world
      cases hci : callIn sunfish 1000000 st.world "Searcher.bound"
          #[.ref a, pos, .int gamma, .int depth] with
      | ok w' rv =>
        obtain ⟨hw', hy2⟩ := hok2 w' rv hci
        rw [hci] at h
        simp only [hy2]
        cases rv <;> simp_all
      | exn w' e => rw [hci] at h; simp at h
      | timeout => rw [hci] at h; simp at h
      | unsupported msg => rw [hci] at h; simp at h
  | exn st e => rw [hrun] at h; simp at h
  | timeout => rw [hrun] at h; simp at h
  | unsupported msg => rw [hrun] at h; simp at h

end Examples.python.sunfish.pins_clock_transport
