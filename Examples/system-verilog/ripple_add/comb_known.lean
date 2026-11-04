import Examples.«system-verilog».ripple_add.proof
import LeanModels.Sv.CombKnownThm

/-!
# `ripple_add` and the x-free knownness theorem (`LeanModels/Sv/CombKnownThm.lean`)

A test of `CombKnown.settled` on the `N`-bit ripple-carry adder, for every `N ≥ 1`. The existing
by-hand structure proofs (`ripple_comb`, `ripple_acyclic`, `ripple_proc`, `ripple_writes` of
`proof.lean`) supply `CombDesign` and `Acyclic`; this file adds the two STATIC checks the
theorem needs, which `sv_known` would produce (`ripple_xfree`: every right-hand side is in the
x-free fragment; `ripple_covered`: no read touches an undriven bit), and then derives, in a few
lines per statement:

* `ripple_known` — in any settled state with known inputs, every bit of `s`, `cout` and the whole
  carry chain `c` is known (no `ofBitVec` bookkeeping, no induction along the carry chain: the
  induction is the theorem's, over the rank);
* `ripple_sum_ofBitVec` — the `sv_bitvec` step for the sum port (`ofBitVec` of the `BitVec` of
  its Boolean bits);
* `ripple_equations` — the four pointwise Boolean equations of the adder over the settled state
  (`c 0 = cin`, `c (i+1) = (a i && b i) || (c i && (a i ^^ b i))`, `s i = a i ^^ b i ^^ c i`,
  `cout = c N`, with `x i := st.boolAt "x" i`) — the shape `sv_equations` hands to the consumer
  half `svgolf/design/ideal_add_lib.lean`;
* `ripple_addView` — those equations assembled into the `AddView` producer contract of
  `svgolf/design/ideal_add_lib.lean` (mirrored locally: plain Lean files are not importable),
  with the port bridges `SvState.boolAt_ofBitVec`;
* `ripple_known_run` — the run-level reading (`⊨₂`) and its non-vacuity (`∃ run`).

## Non-vacuity and necessity of the hypotheses

* Satisfiable: the adder satisfies every hypothesis (above), and a full adder
  (`Comb2Smoke.faDesign`) passes the DECIDABLE checks `xfreeB`/`coveredB` by `decide`.
* A design with an `x` literal is NOT in the fragment (`badX_not_xfree`, decided): the theorem
  does not apply.
* A design with an UNDRIVEN read signal is not `Covered` (`badU_not_covered`, decided), and the
  hypothesis cannot be dropped: `covered_necessary` exhibits a state of that design satisfying
  `CombDesign`, `Acyclic`, `XFree`, `CombEqs`, `StateShape`, `InputsKnown`, in which the output
  is not known. The static check is what keeps the theorem honest.
-/

namespace Examples.«system-verilog».ripple_add.comb_known

open LeanModels.Sv
open Examples.«system-verilog».ripple_add.gen
open Examples.«system-verilog».ripple_add.proof

/-! ## The two static checks, for every `N ≥ 1` -/

section Ripple

variable {N : Nat} (hN : 1 ≤ N)
include hN

theorem ripple_declWidth_a : (ripple_add.sem N).declWidth "a" = some N := by
  simp [ripple_declWidth hN, rippleDecls]

theorem ripple_declWidth_b : (ripple_add.sem N).declWidth "b" = some N := by
  simp [ripple_declWidth hN, rippleDecls]

theorem ripple_declWidth_cin : (ripple_add.sem N).declWidth "cin" = some 1 := by
  simp [ripple_declWidth hN, rippleDecls]

/-- The right-hand side of bit `i`'s sum cell. -/
def sumRhs (i : Nat) : Expr2 :=
  .binary .xor (.binary .xor (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))
    (.slice (.ident "c") i 1)

/-- The right-hand side of bit `i`'s carry cell. -/
def carryRhs (i : Nat) : Expr2 :=
  .binary .or (.binary .and (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))
    (.binary .and (.slice (.ident "c") i 1)
      (.binary .xor (.slice (.ident "a") i 1) (.slice (.ident "b") i 1)))

theorem sumRhs_xfWidth {i : Nat} (hi : i < N) :
    (sumRhs i).xfWidth (ripple_add.sem N) = some 1 := by
  have h1 : i + 1 ≤ N := hi
  have h2 : i + 1 ≤ N + 1 := by omega
  simp [sumRhs, Expr2.xfWidth, XF.same, ripple_declWidth_a hN, ripple_declWidth_b hN,
    ripple_declWidth_c hN, h1, h2]

theorem carryRhs_xfWidth {i : Nat} (hi : i < N) :
    (carryRhs i).xfWidth (ripple_add.sem N) = some 1 := by
  have h1 : i + 1 ≤ N := hi
  have h2 : i + 1 ≤ N + 1 := by omega
  simp [carryRhs, Expr2.xfWidth, XF.same, ripple_declWidth_a hN, ripple_declWidth_b hN,
    ripple_declWidth_c hN, h1, h2]

/-- **Check 1: every right-hand side is in the x-free fragment** (every `N ≥ 1`). -/
theorem ripple_xfree : (ripple_add.sem N).XFree := by
  intro j t e hp
  rcases ripple_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨i, hi, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
    simp only [cinProc, coutProc, sumProc, carryProc, Process2.assign.injEq] at h <;>
    obtain ⟨-, rfl⟩ := h
  · exact ⟨1, by simp [Expr2.xfWidth, ripple_declWidth_cin hN]⟩
  · exact ⟨1, by simp [Expr2.xfWidth, ripple_declWidth_c hN]⟩
  · exact ⟨1, sumRhs_xfWidth hN hi⟩
  · exact ⟨1, carryRhs_xfWidth hN hi⟩

/-- Every bit of `a` and `b` below `N` is an input bit. -/
theorem ripple_sourced_input {n : String} (hn : n = "a" ∨ n = "b") {k : Nat} (hk : k < N) :
    (ripple_add.sem N).Sourced n k := by
  refine Or.inl ⟨?_, N, ?_, hk⟩
  · rw [ripple_inputNames hN]; rcases hn with rfl | rfl <;> simp
  · rcases hn with rfl | rfl
    · exact ripple_declWidth_a hN
    · exact ripple_declWidth_b hN

/-- Every bit of the sum `s` is driven (bit `i`'s sum cell). -/
theorem ripple_sourced_s {k : Nat} (hk : k < N) : (ripple_add.sem N).Sourced "s" k :=
  Or.inr ⟨2 * k + 2, k, 1, (ripple_writes hN).mpr (Or.inr (Or.inr ⟨k, hk, Or.inl ⟨rfl, rfl⟩⟩)),
    Nat.le_refl _, by omega⟩

/-- Every bit of the carry chain `c` is driven (`c[0]` by the carry-in, `c[k+1]` by bit `k`'s
carry cell). -/
theorem ripple_sourced_c {k : Nat} (hk : k ≤ N) : (ripple_add.sem N).Sourced "c" k := by
  right
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exact ⟨0, 0, 1, (ripple_writes hN).mpr (Or.inl ⟨rfl, rfl⟩), Nat.le_refl _, by omega⟩
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact ⟨2 * k' + 3, k' + 1, 1,
      (ripple_writes hN).mpr (Or.inr (Or.inr ⟨k', by omega, Or.inr ⟨rfl, rfl⟩⟩)),
      Nat.le_refl _, by omega⟩

/-- **Check 2: no read touches an undriven bit** (every `N ≥ 1`). -/
theorem ripple_covered : (ripple_add.sem N).Covered := by
  have three : ∀ i, i < N → ∀ r : ReadWin,
      (r = .win "a" i 1 ∨ r = .win "b" i 1 ∨ r = .win "c" i 1) → r.Covered (ripple_add.sem N) := by
    intro i hi r hr
    rcases hr with rfl | rfl | rfl <;> intro k hk <;> obtain rfl : k = 0 := (by omega)
    · exact ripple_sourced_input hN (Or.inl rfl) hi
    · exact ripple_sourced_input hN (Or.inr rfl) hi
    · exact ripple_sourced_c hN (by omega)
  intro j t e hp r hr
  rcases ripple_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨i, hi, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
    simp only [cinProc, coutProc, sumProc, carryProc, Process2.assign.injEq] at h <;>
    obtain ⟨-, rfl⟩ := h <;>
    simp [Expr2.reads, Expr2.sliceReads] at hr
  · subst hr
    refine ⟨1, ripple_declWidth_cin hN, by omega, fun k hk => Or.inl ⟨?_, 1, ripple_declWidth_cin hN, hk⟩⟩
    rw [ripple_inputNames hN]; simp
  · subst hr
    intro k hk
    obtain rfl : k = 0 := by omega
    exact ripple_sourced_c hN (by omega)
  · exact three i hi r hr
  · rcases hr with h | h | h | h | h <;> exact three i hi r (by simp [h])

/-- Known inputs, from the usual `ofBitVec` port hypotheses. -/
theorem ripple_inputsKnown {st : SvState} {x y : BitVec N} {ci : Bool}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    (ripple_add.sem N).InputsKnown st := by
  intro n hn
  rw [ripple_inputNames hN] at hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact ⟨_, ha, LVec.allKnown_ofBitVec x, by rw [LVec.width_ofBitVec]; exact ripple_declWidth_a hN⟩
  · exact ⟨_, hb, LVec.allKnown_ofBitVec y, by rw [LVec.width_ofBitVec]; exact ripple_declWidth_b hN⟩
  · exact ⟨_, hc, LVec.allKnown_ofBitVec _, by rw [LVec.width_ofBitVec]; exact ripple_declWidth_cin hN⟩

/-! ## The consequences -/

/-- **The known-signals fact**: in any settled state with known inputs, `s`, `cout` and the
whole carry chain are known. -/
theorem ripple_known {st : SvState} (heqs : CombEqs (ripple_add.sem N) st)
    (hs : StateShape (ripple_add.sem N) st) {x y : BitVec N} {ci : Bool}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    (∀ i, i < N → KnownBit st "s" i) ∧ KnownBit st "cout" 0 ∧ ∀ k, k ≤ N → KnownBit st "c" k := by
  have hin := ripple_inputsKnown hN ha hb hc
  have H : ∀ {n : String} {k : Nat}, (ripple_add.sem N).DrivenBit n k → KnownBit st n k :=
    fun h => CombKnown.driven_bit_known (ripple_comb N hN) (ripple_acyclic N hN) (ripple_xfree hN)
      (ripple_covered hN) heqs hs hin h
  refine ⟨fun i hi => H ⟨2 * i + 2, i, 1, (ripple_writes hN).mpr
      (Or.inr (Or.inr ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩)), Nat.le_refl _, by omega⟩,
    H ⟨1, 0, 1, (ripple_writes hN).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), Nat.le_refl _, by omega⟩,
    fun k hk => ?_⟩
  rcases ripple_sourced_c hN hk with h | h
  · exact absurd h.1 (by rw [ripple_inputNames hN]; decide)
  · exact H h

/-- **The `sv_bitvec` step**: the sum port of any settled state with known inputs IS the
`ofBitVec` of the `BitVec` of its Boolean bits (so the consumer half can speak `BitVec`). -/
theorem ripple_sum_ofBitVec {st : SvState} (heqs : CombEqs (ripple_add.sem N) st)
    (hs : StateShape (ripple_add.sem N) st) {x y : BitVec N} {ci : Bool}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    SvState.lookup st "s" = some (LVec.ofBitVec (XF.bv N (st.boolAt "s"))) :=
  CombKnown.signal_eq_ofBitVec (ripple_comb N hN) (ripple_acyclic N hN) (ripple_xfree hN)
    (ripple_covered hN) heqs hs (ripple_inputsKnown hN ha hb hc) (ripple_declWidth_s hN) (by omega)
    fun _ hk => ripple_sourced_s hN hk

/-- **The adder's four equations, pointwise over the settled state**, with `x i` read as
`st.boolAt "x" i`. The shape of `AddNetlistView` (`svgolf/design/ideal_add_lib.lean`). -/
theorem ripple_equations {st : SvState} (heqs : CombEqs (ripple_add.sem N) st)
    (hs : StateShape (ripple_add.sem N) st) {x y : BitVec N} {ci : Bool}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    st.boolAt "c" 0 = st.boolAt "cin" 0 ∧
    (∀ i, i < N → st.boolAt "c" (i + 1) =
      ((st.boolAt "a" i && st.boolAt "b" i) ||
        (st.boolAt "c" i && (st.boolAt "a" i ^^ st.boolAt "b" i)))) ∧
    (∀ i, i < N → st.boolAt "s" i =
      ((st.boolAt "a" i ^^ st.boolAt "b" i) ^^ st.boolAt "c" i)) ∧
    st.boolAt "cout" 0 = st.boolAt "c" N := by
  have hin := ripple_inputsKnown hN ha hb hc
  have hd := ripple_comb N hN
  have hac := ripple_acyclic N hN
  have hx := ripple_xfree hN
  have hcv := ripple_covered hN
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · have := (CombKnown.settled_slice hd hac hx hcv heqs hs hin (ripple_proc_cin N) (k := 0)
      (by omega)).2
    simpa [Expr2.xfBitsZ, Expr2.xfWidth, Expr2.xfBits, ripple_declWidth_cin hN] using this
  · have hp : (ripple_add.sem N).processes[2 * i + 3]? =
        some (.assign (.slice "c" (i + 1) 1) (carryRhs i)) := ripple_proc_carry hi
    have := (CombKnown.settled_slice hd hac hx hcv heqs hs hin hp (k := 0) (by omega)).2
    rw [Expr2.xfBitsZ, carryRhs_xfWidth hN hi] at this
    simpa [carryRhs, Expr2.xfBits] using this
  · have hp : (ripple_add.sem N).processes[2 * i + 2]? =
        some (.assign (.slice "s" i 1) (sumRhs i)) := ripple_proc_sum hi
    have := (CombKnown.settled_slice hd hac hx hcv heqs hs hin hp (k := 0) (by omega)).2
    rw [Expr2.xfBitsZ, sumRhs_xfWidth hN hi] at this
    simpa [sumRhs, Expr2.xfBits] using this
  · have := (CombKnown.settled_ident hd hac hx hcv heqs hs hin (ripple_declWidth_cout hN)
      (ripple_proc_cout N) (k := 0) (by omega)).2
    simpa [Expr2.xfBitsZ, coutProc, Expr2.xfWidth, ripple_declWidth_c hN, Expr2.xfBits] using this

/-- Mirror of `AddView` of `svgolf/design/ideal_add_lib.lean` (plain Lean, not importable here):
the producer contract of the consumer half, one field per group of `assign`s. -/
structure AddView (N : Nat) (a b : BitVec N) (cin : Bool) (c s : Nat → Bool) (cout : Bool) :
    Prop where
  carry_zero : c 0 = cin
  carry_step : ∀ i < N, c (i + 1) =
    ((a.getLsbD i && b.getLsbD i) || (c i && (a.getLsbD i ^^ b.getLsbD i)))
  sum_bit : ∀ i < N, s i = (a.getLsbD i ^^ b.getLsbD i ^^ c i)
  carry_out : cout = c N

/-- **The producer contract is inhabited by the actual `ripple_add.sem N`**: with `c i`, `s i` the
Boolean bits of the settled state and `a`, `b`, `cin` the port values, the four equations are an
`AddView`. Consumed by `add_value`/`add_spec` of `ideal_add_lib.lean`, this is the knownness
half of the full composition (the structure half is `sv_structure`). -/
theorem ripple_addView {st : SvState} (heqs : CombEqs (ripple_add.sem N) st)
    (hs : StateShape (ripple_add.sem N) st) {x y : BitVec N} {ci : Bool}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    AddView N x y ci (fun i => st.boolAt "c" i) (fun i => st.boolAt "s" i)
      (st.boolAt "cout" 0) := by
  obtain ⟨h0, hstep, hsum, hout⟩ := ripple_equations hN heqs hs ha hb hc
  have hci : st.boolAt "cin" 0 = ci := by
    rw [SvState.boolAt_ofBitVec hc (by omega)]; simp
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, hout⟩
  · simp only [h0, hci]
  · simp only [hstep i hi, SvState.boolAt_ofBitVec ha hi, SvState.boolAt_ofBitVec hb hi]
  · simp only [hsum i hi, SvState.boolAt_ofBitVec ha hi, SvState.boolAt_ofBitVec hb hi]

/-- **Run-level reading** (`⊨₂`): on every snapshot of every completed run whose stimulus drives
`a`, `b`, `cin` with known values, `s` and `cout` are known. -/
theorem ripple_known_run :
    ripple_add.sem N ⊨₂ spec2 fun stim tr => ∀ (c : Nat) (inputs st : SvState),
      stim[c]? = some inputs → tr[c]? = some st → ∀ (x y : BitVec N) (ci : Bool),
      SvState.lookup inputs "a" = some (LVec.ofBitVec x) →
      SvState.lookup inputs "b" = some (LVec.ofBitVec y) →
      SvState.lookup inputs "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
      (∀ i, i < N → KnownBit st "s" i) ∧ KnownBit st "cout" 0 := by
  apply Models2.of_comb_inputs (ripple_comb N hN)
  intro stim tr h c inputs st hi hc x y ci ha hb hci
  obtain ⟨heqs, hs, hin⟩ := h c st hc
  have hmem : ∀ n, n = "a" ∨ n = "b" ∨ n = "cin" →
      n ∈ (ripple_add.sem N).inputNames.toList := by
    intro n hn
    rw [ripple_inputNames hN]
    rcases hn with rfl | rfl | rfl <;> simp
  obtain ⟨hS, hCO, -⟩ := ripple_known hN heqs hs
    (hin inputs hi "a" (hmem _ (by simp)) _ ha)
    (hin inputs hi "b" (hmem _ (by simp)) _ hb)
    (hin inputs hi "cin" (hmem _ (by simp)) _ hci)
  exact ⟨hS, hCO⟩

/-- Non-vacuity of the run-level statement: a completed run exists under every schedule and
stimulus, and it satisfies the statement. -/
example (σ : ScheduleOracle) (stim : List SvState) :
    ∃ tr, Runs2 (ripple_add.sem N) σ stim tr ∧ ∀ (c : Nat) (inputs st : SvState),
      stim[c]? = some inputs → tr[c]? = some st → ∀ (x y : BitVec N) (ci : Bool),
      SvState.lookup inputs "a" = some (LVec.ofBitVec x) →
      SvState.lookup inputs "b" = some (LVec.ofBitVec y) →
      SvState.lookup inputs "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
      (∀ i, i < N → KnownBit st "s" i) ∧ KnownBit st "cout" 0 :=
  Models2.exists_of_terminates (ripple_terminates N hN) (ripple_known_run hN) σ stim

end Ripple

/-! ## The decidable checks on the real generated design (sample widths)

`ripple_add.sem N` is built by a well-founded expansion, so `decide` cannot run these; the compiled
evaluator can. The symbolic-`N` proofs above are the real statement; this is a differential
sanity check of the checks themselves. -/

#guard ([1, 2, 3, 5, 8, 16].all fun n => (ripple_add.sem n).xfreeB && (ripple_add.sem n).coveredB)

/-! ## The conclusion against the executable semantics

`settledCheck d st` is the theorem's conclusion as a Boolean: every bit of every window of every
assign is known, and equals the Boolean evaluation of its right-hand side. It is checked on the
snapshots `run2` (the interpreter, not the proof layer) produces for the real generated adder, for
every width up to 5 and every input triple of that width. A transcription error in `xfBits`,
`boolAt` or the window offsets would fail here before it fails in a proof. -/

/-- Bit `k` of `n` exists in `st` and is `0`/`1` (the Boolean twin of `KnownBit`). -/
def knownBitB (st : SvState) (n : String) (k : Nat) : Bool :=
  match SvState.lookup st n with
  | some v => (v.bits[k]?).any Logic.isKnown
  | none => false

/-- The conclusion of `CombKnown.settled`, as a Boolean, on one state. -/
def settledCheck (d : Design2) (st : SvState) : Bool :=
  d.processes.toList.all fun p =>
    match p with
    | .assign t e =>
        (Win.placed (t.wins d)).all fun (wn, off) =>
          (List.range wn.2.2).all fun k =>
            knownBitB st wn.1 (wn.2.1 + k) &&
              st.boolAt wn.1 (wn.2.1 + k) == e.xfBitsZ d st.boolAt (off + k)
    | _ => false

private def rippleRun (N a b cin : Nat) : Option SvState :=
  match (run2 (ripple_add.sem N) σ_src 256
      [[("a", LVec.ofNat N a), ("b", LVec.ofNat N b), ("cin", LVec.ofNat 1 cin)]]).toOption with
  | some [st] => some st
  | _ => none

#guard ((List.range 5).all fun n =>
  let N := n + 1
  (List.range (2 ^ N)).all fun a => (List.range (2 ^ N)).all fun b => [0, 1].all fun cin =>
    match rippleRun N a b cin with
    | some st => settledCheck (ripple_add.sem N) st
    | none => false)

/-! ## Non-vacuity of the decidable checks: a concrete passing design -/

example : Comb2Smoke.faDesign.xfreeB = true := by decide
example : Comb2Smoke.faDesign.coveredB = true := by decide

/-- The full adder passes both static checks, so the theorem applies to it. -/
theorem fa_xfree : Comb2Smoke.faDesign.XFree := Design2.XFree.of_xfreeB (by decide)

theorem fa_covered : Comb2Smoke.faDesign.Covered := Design2.Covered.of_coveredB (by decide)

/-! ## Negative tests: designs outside the fragment -/

/-- `assign y = 1'bx`: an `x` literal. -/
def badX : Design2 where
  name := "badX"
  decls := #[{ name := "y", width := 1, isOutput := true }]
  processes := #[.assign (.ident "y") (.lit ⟨#[Logic.lx]⟩)]

example : badX.xfreeB = false := by decide

/-- An `x` literal is outside the fragment: the theorem does not apply. -/
theorem badX_not_xfree : ¬ badX.XFree := by
  intro h
  obtain ⟨w, hw⟩ := h 0 (.ident "y") (.lit ⟨#[Logic.lx]⟩) rfl
  have : (Expr2.lit ⟨#[Logic.lx]⟩).xfWidth badX = none := by decide
  rw [this] at hw
  cases hw

/-- `assign y = u` where `u` is declared but never driven and not an input. -/
def badU : Design2 where
  name := "badU"
  decls := #[{ name := "u", width := 1 }, { name := "y", width := 1, isOutput := true }]
  processes := #[.assign (.ident "y") (.ident "u")]

example : badU.xfreeB = true := by decide
example : badU.coveredB = false := by decide

/-- An undriven read is not covered: the theorem does not apply. -/
theorem badU_not_covered : ¬ badU.Covered := by
  intro h
  obtain ⟨W, hW, -, hsrc⟩ := h 0 (.ident "y") (.ident "u") rfl (.whole "u") (by simp [Expr2.reads])
  have h0 := Design2.sourcedB_iff.mpr (hsrc 0 (by
    have : W = 1 := by
      simp [Design2.declWidth, badU] at hW
      omega
    omega))
  revert h0
  decide

/-! ### The hypothesis `Covered` cannot be dropped

`badU` satisfies everything else, and has a settled state in which `y` is not known. -/

theorem badU_proc {i : Nat} {p : Process2} :
    badU.processes[i]? = some p ↔ i = 0 ∧ p = .assign (.ident "y") (.ident "u") := by
  match i with
  | 0 => simp [badU, eq_comm]
  | i + 1 => simp [badU]

theorem badU_writes {i : Nat} {n : String} {lo w : Nat} :
    badU.Writes i (n, lo, w) ↔ i = 0 ∧ n = "y" ∧ lo = 0 ∧ w = 1 := by
  constructor
  · rintro ⟨t, e, hp, hw⟩
    obtain ⟨rfl, h⟩ := badU_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Design2.declWidth, badU] at hw
    exact ⟨rfl, hw⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨_, _, rfl, by simp [Design2.declWidth, badU]⟩

theorem badU_comb : CombDesign badU where
  nodup := by decide
  assign := by
    intro i p hp
    obtain ⟨rfl, rfl⟩ := badU_proc.mp hp
    exact ⟨_, _, [("y", 0, 1)], rfl, by simp [Design2.declWidth, badU]⟩
  inWidth := by
    intro i n lo w h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := badU_writes.mp h
    exact ⟨1, by simp [Design2.declWidth, badU], by omega⟩
  notInput := by
    intro n ⟨i, lo, w, h⟩
    obtain ⟨rfl, rfl, -, -⟩ := badU_writes.mp h
    simp [Design2.inputNames, badU]
  disjoint := by
    intro i j ⟨n, lo, w⟩ ⟨n', lo', w'⟩ hij hi hj
    obtain ⟨rfl, -⟩ := badU_writes.mp hi
    obtain ⟨rfl, -⟩ := badU_writes.mp hj
    exact absurd rfl hij
  selfDisjoint := by
    intro i t e hp
    obtain ⟨rfl, h⟩ := badU_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro i t e hp
    obtain ⟨rfl, h⟩ := badU_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  rhsDeclared := by
    intro i t e hp
    obtain ⟨rfl, h⟩ := badU_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Expr2.idents, badU]
  initWidth := by
    intro n _ dc hdc _ v hv
    simp [badU] at hdc
    rcases hdc with rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    simp [badU] at hdc
    rcases hdc with rfl | rfl <;> rfl

theorem badU_acyclic : Acyclic badU := by
  refine ⟨fun _ => 0, ?_⟩
  intro i j ti ei tj ej wj hi hj hw hex
  obtain ⟨rfl, h⟩ := badU_proc.mp hi
  simp only [Process2.assign.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨n, lo, w⟩ := wj
  obtain ⟨rfl, rfl, rfl, rfl⟩ := badU_writes.mp ⟨tj, ej, hj, hw⟩
  obtain ⟨r, hr, hov⟩ := hex
  simp [Expr2.reads] at hr
  subst hr
  exact absurd hov (by decide)

theorem badU_xfree : badU.XFree := Design2.XFree.of_xfreeB (by decide)

/-- The all-`x` state: `u` is undriven and stays `x`, so `y = u` is `x`. -/
def badUState : SvState := [("u", LVec.xVec 1), ("y", LVec.xVec 1)]

theorem covered_necessary :
    CombDesign badU ∧ Acyclic badU ∧ badU.XFree ∧ CombEqs badU badUState ∧
      StateShape badU badUState ∧ badU.InputsKnown badUState ∧ ¬ KnownBit badUState "y" 0 := by
  refine ⟨badU_comb, badU_acyclic, badU_xfree, ?_, ?_, ?_, ?_⟩
  · intro i t e n lo w off hp hm
    obtain ⟨rfl, h⟩ := badU_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Design2.declWidth, badU, Win.placed] at hm
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hm
    refine ⟨LVec.xVec 1, LVec.xVec 1, by decide, by decide, by decide⟩
  · refine ⟨by decide, ?_⟩
    intro n ⟨i, lo, w, h⟩
    obtain ⟨rfl, rfl, -, -⟩ := badU_writes.mp h
    exact ⟨LVec.xVec 1, by decide, by simp [Design2.declWidth, badU, LVec.xVec, LVec.replicate,
      LVec.width]⟩
  · intro n hn
    simp [Design2.inputNames, badU] at hn
  · rintro ⟨v, hv, b, hb, hk⟩
    have : v = LVec.xVec 1 := by
      simp only [badUState, SvState.lookup] at hv
      simpa using hv.symm
    subst this
    simp [LVec.xVec, LVec.replicate] at hb
    subst hb
    simp [Logic.isKnown] at hk

/-! ## Axiom pins -/

/-- info: 'Examples.«system-verilog».ripple_add.comb_known.ripple_equations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ripple_equations

/-- info: 'Examples.«system-verilog».ripple_add.comb_known.covered_necessary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms covered_necessary

/-- info: 'Examples.«system-verilog».ripple_add.comb_known.ripple_known_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ripple_known_run

end Examples.«system-verilog».ripple_add.comb_known
