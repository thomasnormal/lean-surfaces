import LeanModels.Sv.CombKnownBits

/-!
# The x-free knownness theorem for combinational designs (`LeanModels.Sv` — Design2)

Part 2 (the design-level theorem) of the x-free knownness theorem of `docs/sv-comb-design.md`
(principle 14); part 1 is `CombKnownBits.lean` (the fragment, the Boolean evaluator, the
expression theorem). Lane K of the `sv_comb` effort.

**The statement in one sentence.** If every right-hand side of a comb design is in the x-free
fragment (`Design2.XFree`), no read touches an undriven bit (`Design2.Covered`), and the state
solves the settle equations (`CombEqs`) with the comb shape (`StateShape`) and known inputs
(`Design2.InputsKnown`), then EVERY driven bit of EVERY signal is known, and each bit equals
the Boolean evaluation of its right-hand side over the Boolean bits of the same state.

## The headline: `CombKnown.settled`

```
theorem CombKnown.settled (hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree) (hc : d.Covered)
    (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st) :
    ∀ i t e n lo w off, d.processes[i]? = some (.assign t e) →
      ((n, lo, w), off) ∈ Win.placed (t.wins d) → ∀ k, k < w →
        KnownBit st n (lo + k) ∧
          SvState.boolAt st n (lo + k) = e.xfBitsZ d (SvState.boolAt st) (off + k)
```

Read it as: *for each assign process `t = e`, each window `(n, lo, w)` of its target (placed
at bit offset `off` of the concatenated value, `Win.placed`), and each bit `k < w`: the bit
`n[lo + k]` of the settled state is known, and as a `Bool` it equals the Boolean bit
`off + k` of `e`* (`Expr2.xfBitsZ`: zero-extended past the static width of `e`, which is
`LVec.resizeU`). Induction is on the rank of `Acyclic` (strong induction on the rank value, one
step per process, the IH being "every window written by a lower-ranked process is known").

## What `sv_equations` consumes

* `CombKnown.settled_slice` — `assign n[lo +: w] = e`: for `k < w`,
  `st.boolAt n (lo + k) = e.xfBitsZ d st.boolAt k`. `CombKnown.settled_ident` — the same for a
  whole-signal target of declared width `W`. These are the leaf forms; the general (concat)
  form is `CombKnown.settled` itself. `CombKnown.settled_slice_eq` / `settled_ident_eq` drop the
  zero-extension (`xfBitsZ` → `xfBits`) when the right-hand side has the target's width, which
  is the case for every instantiated gate-level assign. `CombKnown.settled_of_checks` takes the
  decidable checks `xfreeB`/`coveredB` of a concrete design in place of the `Prop`s.
* The Boolean evaluator unfolds by `rfl`/`simp [Expr2.xfBits]` one constructor at a time, so
  the right-hand side of the ripple adder's carry cell becomes
  `(env "a" i && env "b" i) || (env "c" i && (env "a" i ^^ env "b" i))` with
  `env n k = SvState.boolAt st n k` — the pointwise equation `c (i+1) = …` of
  `svgolf/design/ideal_add_lib.lean`'s `AddNetlistView`, with `c i := st.boolAt "c" i`.
* Bridges to the port types: `SvState.boolAt_ofBitVec` (a port holding `LVec.ofBitVec x` has
  `st.boolAt n i = x.getLsbD i`), `KnownBit.exists_bits` (a known bit IS `Logic.ofBool` of its
  Boolean), `SvState.lookup_eq_ofBitVec_bv` (a signal all of whose bits are known IS
  `LVec.ofBitVec (XF.bv W (st.boolAt n))`, with `(XF.bv W f).getLsbD k = f k`: the `sv_bitvec`
  bridge; for the settled state `CombKnown.signal_eq_ofBitVec` applies it to every fully
  sourced signal, e.g. each output port), `CombKnown.driven_bit_known` /
  `CombKnown.sourced_bit_known` (every driven / sourced bit is known, without the equation),
  `CombKnown.sourced_bits` (the vector bit IS `Logic.ofBool (st.boolAt n k)`).

## The hypotheses

* `Design2.XFree d` — `∀ i t e, d.processes[i]? = some (.assign t e) → ∃ w, e.xfWidth d = some w`.
  Structural; for a concrete design `d.xfreeB = true` (`Design2.XFree.of_xfreeB`).
* `Design2.Covered d` — every read of every right-hand side (`Expr2.reads`) only touches
  *sourced* bits (`Design2.Sourced`): an input bit (`Design2.InputBit`, below the declared
  width) or a driven bit (`Design2.DrivenBit`: some process writes a window containing it).
  This IS fourstate rule (e), "no wire bit that is used but has no driver". For a concrete
  design `d.coveredB = true` (`Design2.Covered.of_coveredB`, `Design2.sourcedB_iff`); for a
  generate family it is the "coverage of generated ranges" goal (design principle 1).
* `Design2.InputsKnown d st` — every input port holds a fully known vector of its declared
  width.
* `CombDesign d`, `Acyclic d`, `CombEqs d st`, `StateShape d st` — the existing comb layer
  (`Comb2Base.lean`); `CombEqs`/`StateShape` hold of every snapshot of every completed run
  (`Runs2.comb_snapshot`, `Models2.of_comb_pointwise`).

`CombDesign d` is carried for the contract's sake: the proof uses its consequences only through
`CombEqs`/`StateShape`/`Acyclic`.

## Why each hypothesis is needed (non-vacuity of the static checks)

Dropping `Covered` makes the theorem FALSE: `Examples/system-verilog/ripple_add/comb_known.lean`
exhibits a design with an undriven read signal that satisfies `CombDesign`, `Acyclic`,
`XFree` and has a state with `CombEqs`, `StateShape` and known inputs, in which the output is
`x`. An `x` literal is outside the fragment (`xfWidth = none`, decided). So the static checks
are exactly what keeps the theorem honest; the theorem turns "the checks pass" into "all
settled values are known".

## Not covered (stated limits)

* Operators outside the fragment (dynamic `index`, `/ % **`, signed forms, wildcard
  equalities, width-mismatched operands; see the table in `CombKnownBits.lean`): extension work
  or deliberate refusals, not a soundness issue — the theorem does not apply to a design that
  uses them.
* Declaration initializers are not a *source*: an undriven, non-input signal is never
  `Sourced`, even if it has a known `init`.
* `always_comb`, instances, edge-triggered processes: outside `CombDesign`.
-/

namespace LeanModels.Sv

/-! ## The design-level hypotheses -/

/-- Bit `k` of the input port `n` exists (`k` is below its declared width). -/
def Design2.InputBit (d : Design2) (n : String) (k : Nat) : Prop :=
  n ∈ d.inputNames.toList ∧ ∃ W, d.declWidth n = some W ∧ k < W

/-- Some process writes a window of `n` containing bit `k`. -/
def Design2.DrivenBit (d : Design2) (n : String) (k : Nat) : Prop :=
  ∃ i lo w, d.Writes i (n, lo, w) ∧ lo ≤ k ∧ k < lo + w

/-- Bit `k` of `n` has a source: it is an input bit or a driven bit. -/
def Design2.Sourced (d : Design2) (n : String) (k : Nat) : Prop :=
  d.InputBit n k ∨ d.DrivenBit n k

/-- Every bit a read observes has a source (no undriven read). A whole read needs the whole
declared vector sourced (and non-empty). -/
def ReadWin.Covered (d : Design2) : ReadWin → Prop
  | .whole n => ∃ W, d.declWidth n = some W ∧ 0 < W ∧ ∀ k, k < W → d.Sourced n k
  | .win n lo w => ∀ k, k < w → d.Sourced n (lo + k)

/-- **No undriven read**: every read of every assign's right-hand side is covered. -/
def Design2.Covered (d : Design2) : Prop :=
  ∀ (i : Nat) (t : Lhs2) (e : Expr2), d.processes[i]? = some (.assign t e) →
    ∀ r ∈ e.reads, r.Covered d

/-- **x-free right-hand sides**: every assign's right-hand side is in the fragment
(`Expr2.xfWidth`). -/
def Design2.XFree (d : Design2) : Prop :=
  ∀ (i : Nat) (t : Lhs2) (e : Expr2), d.processes[i]? = some (.assign t e) →
    ∃ w, e.xfWidth d = some w

/-- **Known inputs**: every input port holds a fully known vector of its declared width. -/
def Design2.InputsKnown (d : Design2) (st : SvState) : Prop :=
  ∀ n ∈ d.inputNames.toList, ∃ v, SvState.lookup st n = some v ∧ v.allKnown = true ∧
    d.declWidth n = some v.width

/-! ## Reads are known -/

section Main

variable {d : Design2} {st : SvState}

theorem input_bit_known (hin : d.InputsKnown st) {n : String} {k : Nat} (h : d.InputBit n k) :
    KnownBit st n k := by
  obtain ⟨hn, W, hW, hk⟩ := h
  obtain ⟨v, hv, hall, hdw⟩ := hin n hn
  rw [hW] at hdw
  have hdw' : W = v.bits.size := Option.some.inj hdw
  have hk' : k < v.bits.size := by omega
  refine ⟨v, hv, v.bits[k], Array.getElem?_eq_getElem hk', ?_⟩
  simp only [LVec.allKnown, Array.all_eq_true] at hall
  exact hall k hk'

theorem sourced_width (hs : StateShape d st) (hin : d.InputsKnown st) {n : String} {k : Nat}
    (h : d.Sourced n k) {W : Nat} (hW : d.declWidth n = some W) :
    ∃ v, SvState.lookup st n = some v ∧ v.width = W := by
  rcases h with ⟨hn, W', hW', hk⟩ | ⟨i, lo, w, hwr, -, -⟩
  · obtain ⟨v, hv, -, hdw⟩ := hin n hn
    rw [hW] at hdw
    exact ⟨v, hv, (Option.some.inj hdw).symm⟩
  · obtain ⟨v, hv, hdw⟩ := hs.driven n ⟨i, lo, w, hwr⟩
    rw [hW] at hdw
    exact ⟨v, hv, (Option.some.inj hdw).symm⟩

theorem ReadWin.overlaps_of_bit {r : ReadWin} {n : String} {k lo w : Nat}
    (hr : r.overlaps (n, k, 1) = true) (hlo : lo ≤ k) (hhi : k < lo + w) :
    r.overlaps (n, lo, w) = true := by
  cases r with
  | whole m => simpa [ReadWin.overlaps] using hr
  | win m a b =>
      simp only [ReadWin.overlaps, Win.overlaps_eq_true] at hr ⊢
      obtain ⟨h1, h2, h3⟩ := hr
      exact ⟨h1, by omega, by omega⟩

/-- A covered read is known, provided its driven bits are known (inputs are known by
hypothesis). -/
theorem readKnown_of_covered (hs : StateShape d st) (hin : d.InputsKnown st) {r : ReadWin}
    (hc : r.Covered d)
    (hdrv : ∀ n k, r.overlaps (n, k, 1) = true → d.DrivenBit n k → KnownBit st n k) :
    ReadKnown d st r := by
  have src : ∀ n k, r.overlaps (n, k, 1) = true → d.Sourced n k → KnownBit st n k := by
    intro n k hov hsrc
    rcases hsrc with h | h
    · exact input_bit_known hin h
    · exact hdrv n k hov h
  cases r with
  | win n lo w =>
      intro k hk
      refine src n (lo + k) ?_ (hc k hk)
      simp only [ReadWin.overlaps, Win.overlaps_eq_true]
      refine ⟨trivial, ?_, ?_⟩ <;> omega
  | whole n =>
      obtain ⟨W, hW, hpos, hsrc⟩ := hc
      have hov : ∀ k, (ReadWin.whole n).overlaps (n, k, 1) = true := by
        intro k; simp [ReadWin.overlaps]
      obtain ⟨v, hv, hvw⟩ := sourced_width hs hin (hsrc 0 hpos) hW
      refine ⟨W, v, hW, hv, hvw, ?_⟩
      simp only [LVec.allKnown, Array.all_eq_true]
      intro i hi
      have hiW : i < W := by
        have : v.width = v.bits.size := rfl
        omega
      obtain ⟨v', hv', bb, hbb, hbk⟩ := src n i (hov i) (hsrc i hiW)
      rw [hv] at hv'
      cases hv'
      rw [Array.getElem?_eq_getElem hi] at hbb
      cases hbb
      exact hbk

/-- The bits of a settled window, read off `CombEqs`: bit `lo + k` of the target holds bit
`off + k` of the right-hand side's value resized to the target's total width `tw`. -/
theorem window_bit {old : LVec} {wd tw lo w off : Nat} {f : Nat → Bool}
    (hext : old.extract lo w = ((LVec.ofBoolFn wd f).resizeU tw).extract off w)
    (hoff : off + w ≤ tw) {k : Nat} (hk : k < w) :
    old.bits[lo + k]? = some (Logic.ofBool (decide (off + k < wd) && f (off + k))) := by
  rw [LVec.resizeU_ofBoolFn, LVec.extract_ofBoolFn _ hoff] at hext
  have h1 := congrArg (fun u : LVec => u.bits[k]?) hext
  simp only [LVec.getElem?_extract, LVec.getElem?_ofBoolFn, hk, if_true] at h1
  have h2 := Option.some.inj h1
  generalize (decide (off + k < wd) && f (off + k)) = X at h2 ⊢
  cases hb : old.bits[lo + k]? with
  | none =>
      rw [hb] at h2
      cases X <;> simp [Logic.ofBool] at h2
  | some b =>
      rw [hb] at h2
      rw [Option.getD_some] at h2
      rw [h2]

/-- **Knownness of every driven bit**, by strong induction on the rank. Needs the profile only
through its parts: the rank certificate, the settle equations, the state shape. -/
theorem driven_known (_hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree) (hc : d.Covered)
    (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st) :
    ∀ n k, d.DrivenBit n k → KnownBit st n k := by
  obtain ⟨rank, hrank⟩ := ha
  have key : ∀ m, ∀ (i : Nat) (t : Lhs2) (e : Expr2), rank i = m →
      d.processes[i]? = some (.assign t e) →
      ∀ n lo w off, ((n, lo, w), off) ∈ Win.placed (t.wins d) →
        ∀ k, k < w → KnownBit st n (lo + k) := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro i t e hrm hp n lo w off hm k hk
      subst hrm
      have hreads : ∀ r ∈ e.reads, ReadKnown d st r := by
        intro r hr
        refine readKnown_of_covered hs hin (hc i t e hp r hr) ?_
        intro n' k' hov ⟨j, lo', w', ⟨tj, ej, hpj, hmem⟩, hlo, hhi⟩
        have hlt := hrank i j t e tj ej (n', lo', w') hp hpj hmem
          ⟨r, hr, ReadWin.overlaps_of_bit hov hlo hhi⟩
        obtain ⟨off', hm'⟩ := Win.exists_mem_placed hmem
        have := ih (rank j) hlt j tj ej rfl hpj n' lo' w' off' hm' (k' - lo') (by omega)
        rwa [show lo' + (k' - lo') = k' by omega] at this
      obtain ⟨wd, hwd⟩ := hx i t e hp
      have hev := Expr2.evalPure2_ofBoolFn (e.size + 1) e (Nat.lt_succ_self _) hwd hreads
      obtain ⟨old, v, hold, hv, hext⟩ := heqs i t e n lo w off hp hm
      rw [hev] at hv
      cases hv
      have hoff : off + w ≤ Win.sumWidth (t.wins d) := by
        have := Win.le_sumWidth_of_mem_placed hm
        simpa using this
      have hb := window_bit hext hoff hk
      exact ⟨old, hold, _, hb, Logic.isKnown_ofBool _⟩
  rintro n k ⟨i, lo, w, ⟨t, e, hp, hmem⟩, hlo, hhi⟩
  obtain ⟨off, hm⟩ := Win.exists_mem_placed hmem
  have := key (rank i) i t e rfl hp n lo w off hm (k - lo) (by omega)
  rwa [show lo + (k - lo) = k by omega] at this

/-- **The x-free knownness theorem, with the Boolean equations.** For a comb design whose
right-hand sides are in the x-free fragment (`d.XFree`), with no undriven read (`d.Covered`),
in any state that solves the settle equations (`CombEqs`), has the comb shape (`StateShape`)
and holds known inputs (`d.InputsKnown`): for EVERY assign process `i` (target `t`, right-hand
side `e`) and every placed window `(n, lo, w)` at offset `off` of its target, every bit of the
window is known, and its Boolean value is the Boolean evaluation of `e` at bit `off + k` (the
zero-extended read, `Expr2.xfBitsZ`) over the Boolean bits of the same state. -/
theorem CombKnown.settled (hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree) (hc : d.Covered)
    (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st) :
    ∀ (i : Nat) (t : Lhs2) (e : Expr2) (n : String) (lo w off : Nat),
      d.processes[i]? = some (.assign t e) →
      ((n, lo, w), off) ∈ Win.placed (t.wins d) → ∀ k, k < w →
        KnownBit st n (lo + k) ∧
          SvState.boolAt st n (lo + k) = e.xfBitsZ d (SvState.boolAt st) (off + k) := by
  intro i t e n lo w off hp hm k hk
  have hdk := driven_known hd ha hx hc heqs hs hin
  have hreads : ∀ r ∈ e.reads, ReadKnown d st r := fun r hr =>
    readKnown_of_covered hs hin (hc i t e hp r hr) (fun n' k' _ hdr => hdk n' k' hdr)
  obtain ⟨wd, hwd⟩ := hx i t e hp
  have hev := Expr2.evalPure2_ofBoolFn (e.size + 1) e (Nat.lt_succ_self _) hwd hreads
  obtain ⟨old, v, hold, hv, hext⟩ := heqs i t e n lo w off hp hm
  rw [hev] at hv
  cases hv
  have hoff : off + w ≤ Win.sumWidth (t.wins d) := by
    have := Win.le_sumWidth_of_mem_placed hm
    simpa using this
  have hb := window_bit hext hoff hk
  refine ⟨⟨old, hold, _, hb, Logic.isKnown_ofBool _⟩, ?_⟩
  simp only [SvState.boolAt, hold, LVec.boolAt, hb, Option.getD_some, Logic.ofBool_beq_l1,
    Expr2.xfBitsZ, hwd, Option.getD_some]

/-- A known bit reads back as its Boolean: the bit of the vector is `Logic.ofBool` of the
Boolean accessor. -/
theorem KnownBit.exists_bits {n : String} {k : Nat} (h : KnownBit st n k) :
    ∃ v, SvState.lookup st n = some v ∧
      v.bits[k]? = some (Logic.ofBool (SvState.boolAt st n k)) := by
  obtain ⟨v, hv, b, hb, hk⟩ := h
  refine ⟨v, hv, ?_⟩
  simp only [SvState.boolAt, hv, LVec.boolAt, hb, Option.getD_some]
  rw [Logic.ofBool_beq_l1_of_isKnown hk]

/-- **Every driven bit is known** (corollary of `CombKnown.settled`). -/
theorem CombKnown.driven_bit_known (hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree)
    (hc : d.Covered) (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st)
    {n : String} {k : Nat} (h : d.DrivenBit n k) : KnownBit st n k :=
  driven_known hd ha hx hc heqs hs hin n k h

/-- **Every sourced bit is known**: an input bit (by hypothesis) or a driven bit (by the
theorem). -/
theorem CombKnown.sourced_bit_known (hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree)
    (hc : d.Covered) (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st)
    {n : String} {k : Nat} (h : d.Sourced n k) : KnownBit st n k := by
  rcases h with h | h
  · exact input_bit_known hin h
  · exact driven_known hd ha hx hc heqs hs hin n k h

/-! ### Leaf forms (what `sv_equations` instantiates) -/

/-- `assign n[lo +: w] = e`: bit `lo + k` of `n` is the Boolean evaluation of `e` at bit `k`. -/
theorem CombKnown.settled_slice (hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree)
    (hc : d.Covered) (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st)
    {i : Nat} {n : String} {lo w : Nat} {e : Expr2}
    (hp : d.processes[i]? = some (.assign (.slice n lo w) e)) {k : Nat} (hk : k < w) :
    KnownBit st n (lo + k) ∧
      SvState.boolAt st n (lo + k) = e.xfBitsZ d (SvState.boolAt st) k := by
  have := CombKnown.settled hd ha hx hc heqs hs hin i (.slice n lo w) e n lo w 0 hp
    (by simp) k hk
  simpa using this

/-- `assign n = e` (whole signal of declared width `W`): bit `k` of `n` is the Boolean
evaluation of `e` at bit `k`. -/
theorem CombKnown.settled_ident (hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree)
    (hc : d.Covered) (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st)
    {i : Nat} {n : String} {e : Expr2} {W : Nat} (hW : d.declWidth n = some W)
    (hp : d.processes[i]? = some (.assign (.ident n) e)) {k : Nat} (hk : k < W) :
    KnownBit st n k ∧ SvState.boolAt st n k = e.xfBitsZ d (SvState.boolAt st) k := by
  have := CombKnown.settled hd ha hx hc heqs hs hin i (.ident n) e n 0 W 0 hp
    (by simp [hW]) k hk
  simpa using this

/-- `assign n[lo +: w] = e` with `e` of static width `w` (the usual case): no zero-extension. -/
theorem CombKnown.settled_slice_eq (hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree)
    (hc : d.Covered) (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st)
    {i : Nat} {n : String} {lo w : Nat} {e : Expr2}
    (hp : d.processes[i]? = some (.assign (.slice n lo w) e)) (hwe : e.xfWidth d = some w)
    {k : Nat} (hk : k < w) :
    KnownBit st n (lo + k) ∧ SvState.boolAt st n (lo + k) = e.xfBits d (SvState.boolAt st) k := by
  have := CombKnown.settled_slice hd ha hx hc heqs hs hin hp hk
  rwa [Expr2.xfBitsZ_of_lt hwe hk] at this

/-- `assign n = e` with `e` of static width `W` (the declared width of `n`): no zero-extension. -/
theorem CombKnown.settled_ident_eq (hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree)
    (hc : d.Covered) (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st)
    {i : Nat} {n : String} {e : Expr2} {W : Nat} (hW : d.declWidth n = some W)
    (hp : d.processes[i]? = some (.assign (.ident n) e)) (hwe : e.xfWidth d = some W)
    {k : Nat} (hk : k < W) :
    KnownBit st n k ∧ SvState.boolAt st n k = e.xfBits d (SvState.boolAt st) k := by
  have := CombKnown.settled_ident hd ha hx hc heqs hs hin hW hp hk
  rwa [Expr2.xfBitsZ_of_lt hwe hk] at this

/-- **Reading a sourced bit gives a Boolean**: bit `k` of any signal bit with a source is the
vector bit `Logic.ofBool (st.boolAt n k)` — no `x`, no `z`, no missing bit. -/
theorem CombKnown.sourced_bits (hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree)
    (hc : d.Covered) (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st)
    {n : String} {k : Nat} (h : d.Sourced n k) :
    ∃ v, SvState.lookup st n = some v ∧
      v.bits[k]? = some (Logic.ofBool (SvState.boolAt st n k)) :=
  (CombKnown.sourced_bit_known hd ha hx hc heqs hs hin h).exists_bits

/-- **A fully sourced signal is an `ofBitVec`** (the `sv_bitvec` bridge): if every bit of the
declared vector `n` (width `W > 0`) has a source, the settled value of `n` IS
`LVec.ofBitVec (XF.bv W (st.boolAt n))`, whose bit `k` is `st.boolAt n k`
(`XF.getLsbD_bv`). E.g. every output port of the ripple adder. -/
theorem CombKnown.signal_eq_ofBitVec (hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree)
    (hc : d.Covered) (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st)
    {n : String} {W : Nat} (hW : d.declWidth n = some W) (hpos : 0 < W)
    (hsrc : ∀ k, k < W → d.Sourced n k) :
    SvState.lookup st n = some (LVec.ofBitVec (XF.bv W (SvState.boolAt st n))) := by
  obtain ⟨v, hv, hvw⟩ := sourced_width hs hin (hsrc 0 hpos) hW
  rw [hv]
  exact congrArg some (SvState.lookup_eq_ofBitVec_bv hv hvw fun k hk =>
    CombKnown.sourced_bit_known hd ha hx hc heqs hs hin (hsrc k hk))

/-- A bit of an input port is known and reads back as a Boolean. -/
theorem InputsKnown.boolAt_bits (hin : d.InputsKnown st) {n : String} {k : Nat}
    (h : d.InputBit n k) :
    ∃ v, SvState.lookup st n = some v ∧
      v.bits[k]? = some (Logic.ofBool (SvState.boolAt st n k)) :=
  (input_bit_known hin h).exists_bits

end Main

/-! ## Decidable checks for concrete designs

The hypotheses `d.XFree` and `d.Covered` are Props over a design of symbolic size; for a
concrete design they are decided by these Boolean checks (and the negative tests use their
`false`). -/

/-- Boolean check of `d.XFree`. -/
def Design2.xfreeB (d : Design2) : Bool :=
  d.processes.toList.all fun p =>
    match p with
    | .assign _ e => (e.xfWidth d).isSome
    | _ => false

theorem Design2.XFree.of_xfreeB {d : Design2} (h : d.xfreeB = true) : d.XFree := by
  intro i t e hp
  have hmem : Process2.assign t e ∈ d.processes.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hp)
  have := List.all_eq_true.mp h _ hmem
  simpa [Option.isSome_iff_exists] using this

/-- Boolean check that bit `k` of `n` has a source. -/
def Design2.sourcedB (d : Design2) (n : String) (k : Nat) : Bool :=
  (decide (n ∈ d.inputNames.toList) &&
      match d.declWidth n with
      | some W => decide (k < W)
      | none => false) ||
    d.processes.toList.any fun p =>
      match p with
      | .assign t _ =>
          (t.wins d).any fun wn => wn.1 == n && decide (wn.2.1 ≤ k) && decide (k < wn.2.1 + wn.2.2)
      | _ => false

theorem Design2.sourcedB_iff {d : Design2} {n : String} {k : Nat} :
    d.sourcedB n k = true ↔ d.Sourced n k := by
  unfold Design2.sourcedB Design2.Sourced Design2.InputBit Design2.DrivenBit
  rw [Bool.or_eq_true]
  apply or_congr
  · rw [Bool.and_eq_true, decide_eq_true_iff]
    apply and_congr Iff.rfl
    cases hW : d.declWidth n with
    | none => simp
    | some W => simp
  · rw [List.any_eq_true]
    constructor
    · rintro ⟨p, hp, hany⟩
      cases p with
      | assign t e =>
          obtain ⟨wn, hwn, hcond⟩ := List.any_eq_true.mp hany
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
          rw [Array.getElem?_toList] at hi
          obtain ⟨m, lo, w⟩ := wn
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          obtain ⟨⟨rfl, h1⟩, h2⟩ := hcond
          exact ⟨i, lo, w, ⟨t, e, hi, hwn⟩, h1, h2⟩
      | alwaysFF _ _ => simp at hany
      | alwaysPlain _ _ => simp at hany
      | alwaysComb _ => simp at hany
      | alwaysFFR _ _ _ => simp at hany
      | unsupported _ _ => simp at hany
    · rintro ⟨i, lo, w, ⟨t, e, hp, hmem⟩, hlo, hhi⟩
      refine ⟨.assign t e, List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hp), ?_⟩
      exact List.any_eq_true.mpr ⟨(n, lo, w), hmem, by simp [hlo, hhi]⟩

/-- Boolean check of `ReadWin.Covered`. -/
def ReadWin.coveredB (d : Design2) : ReadWin → Bool
  | .whole n =>
      match d.declWidth n with
      | some W => decide (0 < W) && (List.range W).all fun k => d.sourcedB n k
      | none => false
  | .win n lo w => (List.range w).all fun k => d.sourcedB n (lo + k)

theorem ReadWin.Covered.of_coveredB {d : Design2} {r : ReadWin} (h : r.coveredB d = true) :
    r.Covered d := by
  cases r with
  | whole n =>
      simp only [ReadWin.coveredB] at h
      cases hW : d.declWidth n with
      | none => simp [hW] at h
      | some W =>
          simp only [hW, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
            List.mem_range] at h
          exact ⟨W, hW, h.1, fun k hk => Design2.sourcedB_iff.mp (h.2 k hk)⟩
  | win n lo w =>
      simp only [ReadWin.coveredB, List.all_eq_true, List.mem_range] at h
      exact fun k hk => Design2.sourcedB_iff.mp (h k hk)

/-- Boolean check of `d.Covered`. -/
def Design2.coveredB (d : Design2) : Bool :=
  d.processes.toList.all fun p =>
    match p with
    | .assign _ e => e.reads.all (ReadWin.coveredB d)
    | _ => false

theorem Design2.Covered.of_coveredB {d : Design2} (h : d.coveredB = true) : d.Covered := by
  intro i t e hp r hr
  have hmem : Process2.assign t e ∈ d.processes.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hp)
  have := List.all_eq_true.mp h _ hmem
  simp only [List.all_eq_true] at this
  exact ReadWin.Covered.of_coveredB (this r hr)


/-- The theorem for a CONCRETE design, from the two decidable checks (`Design2.xfreeB`,
`Design2.coveredB`) instead of the `Prop` hypotheses. -/
theorem CombKnown.settled_of_checks {d : Design2} {st : SvState} (hd : CombDesign d) (ha : Acyclic d)
    (hx : d.xfreeB = true) (hc : d.coveredB = true)
    (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st) :
    ∀ (i : Nat) (t : Lhs2) (e : Expr2) (n : String) (lo w off : Nat),
      d.processes[i]? = some (.assign t e) →
      ((n, lo, w), off) ∈ Win.placed (t.wins d) → ∀ k, k < w →
        KnownBit st n (lo + k) ∧
          SvState.boolAt st n (lo + k) = e.xfBitsZ d (SvState.boolAt st) (off + k) :=
  CombKnown.settled hd ha (Design2.XFree.of_xfreeB hx) (Design2.Covered.of_coveredB hc)
    heqs hs hin


/-! ## Axiom pins

Standard axioms only: no `sorry`, no `native_decide`, no `bv_decide`. -/

/-- info: 'LeanModels.Sv.Expr2.evalPure2_ofBoolFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Expr2.evalPure2_ofBoolFn

/-- info: 'LeanModels.Sv.CombKnown.settled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombKnown.settled

/-- info: 'LeanModels.Sv.CombKnown.sourced_bit_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombKnown.sourced_bit_known

/-- info: 'LeanModels.Sv.CombKnown.settled_of_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombKnown.settled_of_checks

/-- info: 'LeanModels.Sv.CombKnown.signal_eq_ofBitVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombKnown.signal_eq_ofBitVec

/-- info: 'LeanModels.Sv.SvState.lookup_eq_ofBitVec_bv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SvState.lookup_eq_ofBitVec_bv

end LeanModels.Sv
