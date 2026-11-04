import LeanModels.Sv.Contract
import LeanModels.Sv.ObserveFrame
import LeanModels.Sv.Comb2Example
import LeanModels.Sv.Comb2Proc

/-!
# The full adder's contract over `run2` (D11, Day 7)

**Status: provisional over `run2`.** Imported by nothing in the tree.

## What is here

1. Two `run2` library pieces for contracts:
   - `Contract.receptive_of_writesInput`: receptiveness, in the contract's valuation form, for any
     terminating design that writes no input port. It is the same frame lemma as `ObsComb.lean`'s,
     so golfers and contract authors never prove receptiveness by hand.
   - `Obs_run2.comb_samples`: in every run of a comb-profile design (`CombDesign`), BOTH samples of
     every cycle solve the design's equations and have the comb shape. So a comb contract may
     speak about the pre sample, which the edge reads, as well as the post sample.
2. `faContract`, the contract of `Comb2Smoke.faDesign` (ports `a b ci` → `s co y`; the full adder
   of the existing comb proof `Comb2Example.lean`): trivial ghost, trivial rely, the guarantee
   `s = a ^ b ^ ci` and `co = maj(a, b, ci)` on both samples of every cycle, arcs from each input
   bit to each output bit, direction `overApprox` (a safety contract). `fa_sat` proves all four
   conjuncts of `Sat` over `Obs_run2`.

## The `ripple_fa` child (closed until R-HIER on E-core-2; lead's ruling, Day 8, option (b))

`ripple_fa`'s `full_adder` (`Examples/system-verilog/ripple_fa/ripple_fa.sv`) is the same two
equations, with ports `cin`/`cout` and no `y` bus. Its contract is this one with those names. The
composition goes through `Contract.compose_safe_inv`, not `compose_safe`, because the flattened parent
has glue processes (READ: `c[0] = cin`, `cout = c[N]`, and five port connections per bit, `gen.lean`
`faProcs`) that hold only on runs. What it needs, with costs (all JUDGED):
1. **`Inv`** (every probe of a parent run solves the parent's equations): from R-COMB-0's closed store
   on E. Over `run2` it would be `Obs_run2.comb_samples`, given item 3. About 10 to 20 lines once
   R-COMB-0 is merged.
2. **`hproj`** (every parent run, read at instance `k`'s ports, is a behaviour of `full_adder`): from
   R-HIER on E-core-2. This is what reuses the child's proof. Over `run2` it would be 250 to 400 lines
   (a renaming lemma for `evalPure2`/`CombEqs`, plus uniqueness of an acyclic design's settled
   solution), a provisional duplicate of R-HIER, so it is not built.
3. **The parent's own profile**: `CombDesign (ripple_fa.sem N)` over `run2`, or its E-fragment proof
   on E. The `sv_comb` tactics refuse instances (`ripple_fa/comb_errors.lean`); `ripple_add`'s hand
   proof of the same shape is about 60 lines.
4. **The ripple arithmetic** in `hpar`, at symbolic `N`: about 120 lines, partly reusable from
   `ripple_add/proof.lean` (`ripple_settled`, `ripple_arith`).
5. **The child's `Sat`** over the shipped ports (`a b cin → s cout`): `fa_sat` with the names changed,
   about 60 lines over `run2`; on E, through A's transport.
Total beyond R-HIER and R-COMB-0: about 250 to 300 lines.
-/

namespace LeanModels.Sv.Observe

/-! ## `run2` library pieces -/

/-- An input name is a port of the `Obs_run2` interface. -/
theorem Obs_run2.mem_names_of_inputName {d : Design2} {n : String}
    (hn : n ∈ d.inputNames.toList) : n ∈ (Obs_run2.iface d).names := by
  obtain ⟨dc, hdc, hin, rfl⟩ : ∃ dc ∈ d.decls.toList, dc.isInput = true ∧ dc.name = n := by
    simpa [Design2.inputNames] using hn
  simp only [Iface.names, List.mem_append, List.mem_map]
  exact Or.inl ⟨(dc.name, dc.width), List.mem_filterMap.mpr ⟨dc, hdc, by simp [hin]⟩, rfl⟩

/-- The stimulus entry that binds each port of `free` to its known value. -/
def entryOfVal (free : List Sig) (v : Valuation) : SvState :=
  free.map fun p => (p.1, LVec.ofBitVec (v p))

theorem lookup_entryOfVal {v : Valuation} :
    ∀ {free : List Sig}, (free.map Prod.fst).Nodup → ∀ p ∈ free,
      SvState.lookup (entryOfVal free v) p.1 = some (LVec.ofBitVec (v p))
  | [], _, p, hp => by simp at hp
  | q :: rest, hnd, p, hp => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hp with rfl | hp
      · simp [entryOfVal, SvState.lookup]
      · have hne : q.1 ≠ p.1 := fun h => hnd.1 (by rw [h]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
        simp only [entryOfVal, List.map_cons, SvState.lookup]
        rw [if_neg (by simpa using hne)]
        exact lookup_entryOfVal hnd.2 p hp

/-- **Receptiveness for free, contract form** (library theorem): a terminating design that writes no
input port is receptive for any contract whose free ports are distinct inputs of the design. -/
theorem Contract.receptive_of_writesInput (C : Contract) {d : Design2}
    (hd : d.writesInput = false) (hT : Terminates2 d)
    (hfree : ∀ p ∈ C.free, p.1 ∈ d.inputNames.toList) (hnd : (C.free.map Prod.fst).Nodup) :
    C.Receptive Obs_run2 d := by
  intro σ s
  obtain ⟨tr, htr⟩ := hT σ (s.map (entryOfVal C.free))
  obtain ⟨r, hr, rfl⟩ := Obs_run2.runs_of_runs2 htr
  refine ⟨s.map (entryOfVal C.free), r.map (CycleObs.map (Obs_run2.sample d)), trivial,
    ⟨r, hr, rfl⟩, ?_, ?_⟩
  · obtain ⟨fuel, hrun⟩ := hr
    simp [runObs2_length hrun]
  · intro c o v hc hv p hp
    rw [List.getElem?_map] at hc
    cases hrc : r[c]? with
    | none => rw [hrc] at hc; cases hc
    | some o' =>
        rw [hrc] at hc
        simp only [Option.map_some, Option.some.injEq] at hc
        subst hc
        have he : (s.map (entryOfVal C.free))[c]? = some (entryOfVal C.free v) := by simp [hv]
        rw [CycleObs.map_pre, Obs_run2.read_sample (Obs_run2.mem_names_of_inputName (hfree p hp))]
        exact Obs_run2.pre_input hd hr he hrc (hfree p hp) (lookup_entryOfVal hnd p hp)

/-- **Both samples of a comb design are settled**: in every run of a comb-profile design, the pre
and the post sample of every cycle solve the design's equations (`CombEqs`) and have the comb shape. -/
theorem Obs_run2.comb_samples {d : Design2} (hd : CombDesign d) {σ : ScheduleOracle}
    {stim : List SvState} {r : List (CycleObs SvState)} (hr : Obs_run2.Runs d σ stim r) {c : Nat}
    {o : CycleObs SvState} (ho : r[c]? = some o) :
    (CombEqs d o.pre ∧ StateShape d o.pre) ∧ (CombEqs d o.post ∧ StateShape d o.post) := by
  have hruns := Obs_run2.runs2_of_runs hd.noQualified hr
  obtain ⟨fuel, hrun⟩ := hr
  obtain ⟨inputs, prev, kc, kc', -, hprev, hcyc⟩ := runFromObs2_cycle hrun ho
  have hsh : StateShape d prev := by
    cases c with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hprev
        subst hprev
        exact StateShape.of_initState2 hd
    | succ c =>
        simp only [List.getElem?_cons_succ] at hprev
        exact Runs2.comb_shape hd hruns c prev hprev
  obtain ⟨st1, k1, k2, h1, hnil, -, -, hpost⟩ := pre_sample_spec hcyc
  obtain ⟨hpre, -⟩ := hnil (hd.resetIndices_eq prev st1)
  obtain ⟨he1, hs1, -⟩ := combSettle2_eqs hd (StateShape.of_applyInputs2 hd hsh inputs) h1
  rw [← hpre] at he1 hs1
  refine ⟨⟨he1, hs1⟩, ?_⟩
  -- the edge part of a comb design is one more settle
  unfold cyclePost2 at hpost
  rw [hd.edgeIndices_eq, σ.choose_nil] at hpost
  simp only [edgePass2, Res.ok_bind] at hpost
  have hc : commitNba2 o.pre [] = o.pre := rfl
  rw [hc] at hpost
  obtain ⟨he2, hs2, -⟩ := combSettle2_eqs hd hs1 hpost
  exact ⟨he2, hs2⟩

/-! ## The full adder's contract -/

open Comb2Smoke Comb2Example

/-- The full adder's equations on one trusted sample: known `a b ci` give the sum on `s` and the
majority on `co`. -/
def FAEq (s : PortSample) : Prop :=
  ∀ x y z : BitVec 1, s.read "a" = some (LVec.ofBitVec x) → s.read "b" = some (LVec.ofBitVec y) →
    s.read "ci" = some (LVec.ofBitVec z) →
    s.read "s" = some (LVec.ofBitVec (x ^^^ y ^^^ z)) ∧
    s.read "co" = some (LVec.ofBitVec (x &&& y ||| x &&& z ||| y &&& z))

/-- The full adder's ports. -/
def faIface : Iface := ⟨[("a", 1), ("b", 1), ("ci", 1)], [("s", 1), ("co", 1), ("y", 2)]⟩

/-- Its arcs, at bit granularity: every input bit to every output bit. -/
def faArcs : List Arc :=
  [("a", 0, 1), ("b", 0, 1), ("ci", 0, 1)].flatMap fun src =>
    [("s", 0, 1), ("co", 0, 1), ("y", 0, 1), ("y", 1, 1)].map fun dst => ⟨src, dst⟩

/-- **The full adder's contract**: no clock, every input free, no ghost state, no rely; the sum and
the majority on both samples of every cycle. A safety contract (`overApprox`). -/
def faContract : Contract where
  iface := faIface
  clocking := {}
  free := faIface.inputs
  Ghost := Unit
  ginit := ()
  gnext _ _ := ()
  rely _ _ := True
  guar _ o := FAEq o.pre ∧ FAEq o.post
  arcs := faArcs
  dir := .overApprox

/-- The full adder's equations on the trusted sample of a settled state. -/
theorem faEq_of_settled {st : SvState} (heqs : CombEqs faDesign st) (hs : StateShape faDesign st) :
    FAEq (Obs_run2.sample faDesign st) := by
  have hr : ∀ n ∈ ["a", "b", "ci", "s", "co"],
      (Obs_run2.sample faDesign st).read n = SvState.lookup st n := by
    intro n hn
    exact Obs_run2.read_sample (by revert n; decide)
  intro x y z ha hb hc
  rw [hr "a" (by simp)] at ha
  rw [hr "b" (by simp)] at hb
  rw [hr "ci" (by simp)] at hc
  obtain ⟨hS, hCO, -⟩ := fa_settled heqs hs ha hb hc
  rw [hr "s" (by simp), hr "co" (by simp)]
  exact ⟨hS, hCO⟩

/-- **The full adder satisfies its contract over `Obs_run2`**: its ports, realizability (every run
completes), receptiveness (by the library theorem), and on both samples of every cycle of every run
the sum and the majority. -/
theorem fa_sat : faContract.Sat Obs_run2 faDesign where
  iface := by decide
  realizable := Obs_run2.progress_of_terminates _ _ fa_terminates
  receptive := faContract.receptive_of_writesInput (by decide) fa_terminates (by decide) (by decide)
  safe := by
    rintro σ stim b - ⟨r, hr, rfl⟩ c - g o - ho
    rw [List.getElem?_map] at ho
    cases hrc : r[c]? with
    | none => rw [hrc] at ho; cases ho
    | some o' =>
        rw [hrc] at ho
        simp only [Option.map_some, Option.some.injEq] at ho
        subst ho
        obtain ⟨⟨he1, hs1⟩, ⟨he2, hs2⟩⟩ := Obs_run2.comb_samples fa_comb hr hrc
        exact ⟨faEq_of_settled he1 hs1, faEq_of_settled he2 hs2⟩

#print axioms Obs_run2.mem_names_of_inputName
#print axioms lookup_entryOfVal
#print axioms Contract.receptive_of_writesInput
#print axioms Obs_run2.comb_samples
#print axioms faEq_of_settled
#print axioms fa_sat

end LeanModels.Sv.Observe
