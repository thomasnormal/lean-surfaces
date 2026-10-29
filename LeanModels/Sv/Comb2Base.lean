import LeanModels.Sv.Pure2
import LeanModels.Sv.Spec2

/-!
# Combinational designs: windows, the comb profile, frame lemmas (`LeanModels.Sv` — Design2)

Base layer of the combinational settle theorem (the
`Comb2Base`/`Comb2Sound`/`Comb2Term`/`Comb2` layer). `Comb2Sound.lean`
(settle ⇒ fixpoint equations) and `Comb2Term.lean` (acyclic ⇒ settle
terminates) are built on what this file provides.

**Scope.** Designs whose processes are ALL continuous assigns
`Process2.assign t e` with `t` a LEAF — a whole signal (`.ident n`), a
constant slice (`.slice n lo w`), or a constant-literal element select
(`.index n (.lit c) elemW`) — or a CONCATENATION of leaves (`.concat parts`,
nested concatenations included: `assign {co, s} = a + b + ci;`,
`assign {y[3:2], {z, y[1:0]}} = x;`). This covers what an instantiated
gate-level generate design produces (the ripple adder of
`Examples/system-verilog/ripple_add/gen.lean`: `.slice "c" 0 1`, `.ident "cout"`,
`.slice "s" i 1`, `.slice "c" (i+1) 1`, reading `.ident "cin"` and
`.slice (.ident x) i 1`) and the word-level `{carry, sum} = …` idiom
(`Comb2ConcatExample.lean`).

## API index

* Vocabulary: `Win` (`(name, lo, width)`), `Win.overlaps`, `Lhs2.window?`
  (static write window of a leaf), `Lhs2.windows?` / `Lhs2.listWindows?`
  (static window LIST of any target, MSB-first; `none` off-profile),
  `Lhs2.wins` (the same as a plain list), `Win.sumWidth` (total width),
  `Win.placed` (each window with its bit offset in the concatenated value),
  `ReadWin` (`whole n` / `win n lo w`), `Expr2.reads` (`Expr2.listReads`),
  `ReadWin.overlaps`, `ReadWin.agree` (what two states must share for a read
  to see the same thing), `Design2.declWidth`, `Design2.Writes d i wn`
  (`Design2.writes_of_window?` for a leaf), `Driven`, `NotDriven`.
* Target windows, computed (`simp` set): `Lhs2.windows?_ident`/`_slice`/
  `_index_lit`/`_concat`, `Lhs2.listWindows?_nil`/`_cons` (+
  `listWindows?_cons_eq_some`), `Lhs2.wins_ident`/`_slice`/`_index_lit`/
  `_concat`, `Win.sumWidth_nil`/`_cons`, `Win.placed_nil`/`_cons`; bridges
  `Lhs2.windows?_of_window?`, `Lhs2.window?_of_windows?`,
  `Lhs2.wins_of_windows?`, `Lhs2.wins_of_window?`,
  `Lhs2.exists_windows?_of_mem_wins`, `Lhs2.wins_pairwise_of_leaf` (the
  `selfDisjoint` obligation of a leaf target), `Win.map_fst_placed`,
  `Win.mem_of_mem_placed`, `Win.exists_mem_placed`,
  `Win.le_sumWidth_of_mem_placed`, `CombDesign.windows?_of_proc`.
* Judgments: `CombDesign` (the profile, a `Prop` structure discharged once per
  design), `StateShape` (the state invariant), `CombEqs` (the fixpoint
  equations), `Acyclic` (the rank certificate).
* (a) `LVec` window algebra, 4-state: `LVec.width_extract`/`width_insertAt`/
  `width_resizeU`/`width_xVec`, `LVec.extract_insertAt_self`,
  `LVec.extract_insertAt_of_disjoint`, `LVec.insertAt_extract_self`,
  `LVec.insertAt_eq_self_of_extract`, `LVec.insertAt_comm`,
  `LVec.insertAt_insertAt_of_width_le`, `LVec.extract_extract`,
  `LVec.extract_eq_of_bits`, `LVec.eq_of_extract_one`, `LVec.ext_getD`
  (bit primitives `LVec.getD_extract`, `LVec.getD_insertAt`).
* (b) `SvState` algebra: `SvState.lookup_set` (+ `_self`, `_ne`),
  `SvState.keys_set`, `SvState.set_of_lookup`, `SvState.ext`,
  `SvState.lookup_isSome_iff`/`lookup_eq_none_iff`/`exists_lookup_of_mem`;
  shaped-state forms `StateShape.ext`, `StateShape.eq_of_agree_bits`,
  `StateShape.set_insertAt`.
* (c) one process: `combWrite d st t v` (the state after `t = e` with
  `e ↦ v`: `SvState.writeWins` of the resized value's slices into the
  placed windows); `runCombProcess2_assign_write` (forward, any target,
  `e.size < fuel`), `runCombProcess2_assign_write_ok` (inversion of ANY
  `.ok` run); the leaf forms `runCombProcess2_assign_eq` / `_assign` /
  `_assign_ok` (through `combWrite_of_window?`); `CombDesign.evalPure2_ok`,
  `CombDesign.lookup_writes`, `CombDesign.extract_written`.
* (c') multi-window writes: `SvState.writeWins_cons_some`/`_cons_none`,
  `SvState.exists_lookup_set_insertAt`, `SvState.writeWins_eq_self`
  (identity), `ReadWin.agree_writeWins` (frame), `StateShape.writeWins`,
  `SvState.writeWins_readBack` (read-back under pairwise disjointness);
  per process `StateShape.combWrite`, `ReadWin.agree_combWrite`,
  `CombDesign.placed_bound`, `CombDesign.combWrite_readBack`,
  `combWrite_eq_self`, `LVec.extract_zero_of_width`.
* (c'') the interpreter's concatenation path: `resolveLhs2_of_window?`,
  `resolveConcatLhs2_of_windows?` (+ `resolveConcatLhs2_list_of_windows?`:
  on a shaped state the dynamic resolution IS the static window list),
  `writeConcatLhs2_eq` (`writeConcatLhs2` IS `SvState.writeWins` at the
  `Win.placed` offsets).
* (d) `evalPure2_congr_reads` / `evalPures2_congr_reads`; read agreement
  `ReadWin.agree_refl`/`symm`/`trans`/`of_lookup`/`win_of_lookup`/
  `win_of_bits`, `ReadWin.agree_set` (frame of one write),
  `ReadWin.lookup_eq_of_agree_bits`, `ReadWin.overlaps_win_one`.
* (e) passes: `combPass2_frame` (shape kept; every read overlapping no listed
  window agrees), `combPass2_notDriven`, `combPass2_keys`, `combPass2_width`,
  `combPass2_cons_ok` (step inversion, `combWrite` form),
  `combPass2_cons_write` (step forward, any target) and its leaf form
  `combPass2_cons_assign`, `combPass2_cons_none`/`_some`, `combPass2_ok` /
  `combPass2_ok_of_combFuel` (a pass completes above `Design2.combFuel`,
  `Design2.size_lt_combFuel`).
* (f) comb-only phases: `CombDesign.combIndices_eq` (`= List.range size`),
  `CombDesign.edgeIndices_eq` (`= []`), `CombDesign.resetIndices_eq` (`= []`),
  `CombDesign.choose_perm_range`/`nodup_choose`/`mem_choose`,
  `cycleStep2_of_comb` (a cycle = input settle, then post-edge settle),
  `StateShape.of_initState2`, `StateShape.of_applyInputs2`,
  `lookup_applyInputs2`, `keys_applyInputs2`,
  `CombDesign.lookup_applyInputs2_driven`, `CombDesign.notDriven_of_input`,
  `lookup_initState2`.

## Design laws

* **Value-agnostic.** Everything here is 4-state: no `BitVec`, no
  `ofBitVec`, no known-value calculus (that is `Known2.lean`, which this file
  deliberately does not import). The window algebra is proved bit-by-bit on
  `v.bits[i]?.getD .lx`, the exact read primitive of `LVec.extract` and
  `LVec.insertAt`.
* **Two kinds of read.** `evalPure2 st (.ident n)` returns the WHOLE vector
  (its width included), while `evalPure2 st (.slice (.ident n) lo w)` depends
  only on `v.extract lo w`. `ReadWin.whole n` and `ReadWin.win n lo w` keep the
  two apart, so a design whose processes read single bits of a partially
  driven signal (`c[i]` of a ripple-carry chain) gets bit-precise
  dependencies. A window read is agreement on `(v.width, v.extract lo w)` — the
  width is included because a constant-index select `v[k]` range-checks
  against it, and every comb write preserves widths anyway
  (`combPass2_width`). A whole read overlaps every window of its signal.
* **Windows are static; the interpreter's are dynamic.** `Lhs2.window?`
  reads an `.ident` target as `(n, 0, declared width)` while `resolveLhs2`
  uses the CURRENT width (and range-checks a constant index against it);
  `StateShape` (driven signals sit at their declared width) is what makes the
  two coincide, and every lemma about a process run assumes it.
* **A target is a window list; a process is `combWrite`.** A leaf target has
  one window, a concatenation its leaves' windows flattened MSB-first
  (`Lhs2.windows?`, matching `resolveConcatLhs2`). Every process, leaf or
  concatenation, has the same effect shape: the right-hand side resized to
  the target's total width `Win.sumWidth`, slice `[off, off + w)` written
  into window `(n, lo, w)` at its `Win.placed` offset `off` (the first part
  gets the high slice, `writeConcatLhs2`). For a leaf this is the familiar
  `set st n (old.insertAt lo (v.resizeU w))` (`combWrite_of_window?`). With
  `CombDesign.selfDisjoint` (one target's windows are pairwise disjoint) and
  `CombDesign.disjoint` (distinct processes' windows are), every bit has at
  most one writing window in the whole design, so the window-at-a-time
  arguments of the settle proofs run unchanged, window by window, over each
  process's list.
* **Fuel enters only through `Expr2.size`.** The process-level lemmas take
  `e.size < fuel` (forward direction) or nothing at all (inversion of an
  `.ok` run, via `evalPure2_of_evalExpr2_ok`); `Design2.combFuel` bounds every
  right-hand side of a design at once.
* **No name shadows the interpreter.** Theorems about `initState2`,
  `applyInputs2`, `combIndices`, … are named `of_initState2`,
  `combIndices_eq`, … so that declarations in the `StateShape` / `CombDesign`
  namespaces can still mention the interpreter functions unqualified.

## Deviations from the original statement

* `Expr2.reads` takes no `Design2` argument and returns `List ReadWin`
  (whole-signal reads are their own constructor instead of "the whole
  declared width" window: the declared width is not what `evalPure2` reads
  — an input may hold a vector of any width, since stimulus entries are
  applied verbatim; see `Spec2.lean`, "Stimulus conventions"). Accordingly
  `Acyclic` uses `ReadWin.overlaps` (`(∃ r ∈ ei.reads, r.overlaps wj = true)`).
* `CombDesign` states its per-window fields through `Design2.Writes`/`Driven`;
  its `initWidth` field (a driven signal's initializer has the declared width)
  is an addition: without it `initState2` could start a driven signal at a
  width other than its declared one, breaking `StateShape`.
* `StateShape` additionally fixes the state's KEY LIST (`= decl names`, in
  order), which with `CombDesign.nodup` makes states extensional
  (`SvState.ext`) — what the settle proofs need to turn window facts into the
  `st' == st` fixpoint test. Every state a comb run visits has it.
* (2026-10-27, concatenation targets) The profile was generalized from ONE
  window per process to a window LIST: `Design2.Writes`, `CombEqs`, `Acyclic`
  (and `Comb2Term.AcyclicBy`) are stated through `Lhs2.wins`,
  `CombDesign.assign` through `Lhs2.windows?`, and `CombDesign` gained the
  field `selfDisjoint`. `CombEqs` now says each placed window holds its slice
  of `v.resizeU (Win.sumWidth (t.wins d))`; for a leaf (offset 0, total `w`)
  that is the old `old.extract lo w = v.resizeU w`. Step lemmas whose old
  statement named THE window changed statement: `CombDesign.writes_of_lt`,
  `combPass2_cons_ok`, and `Comb2Sound.combPass2_fixpoint_aux`,
  `Comb2Term.combPass2_mid`. Everything a design proof or a run-level
  statement consumes is a conservative extension: the settle and
  termination theorems, the `⊨₂` introductions, the leaf read-backs
  (`CombEqs.lookup_ident`/`extract_slice`/`extract_index`), and the leaf
  forms `runCombProcess2_assign_eq`/`_assign`/`_assign_ok` and
  `combPass2_cons_assign` keep their statements; a leaf-only design proof
  changes only in the `Writes` membership form (`by simp` for `rfl`), the
  `assign` field's one-element window list, and the new `selfDisjoint` field
  (`Lhs2.wins_pairwise_of_leaf`).

The smoke section at the end proves `CombDesign`/`Acyclic` for a hand-built
full adder with a slice-target and an index-target bus, and runs it through
`run2` under two schedules. Its fixtures (`Comb2Smoke.faDesign`, `fa_comb`,
`fa_acyclic`, …) are public: the smoke sections of `Comb2Sound`/`Comb2Term`/
`Comb2` and the end-to-end example `Comb2Example` reuse them. Concatenated
targets are exercised end to end by `Comb2ConcatExample.lean`.
-/

namespace LeanModels.Sv

/-! ## `LVec` window algebra (4-state) -/

namespace LVec

/-- A slice has the requested width. -/
@[simp] theorem width_extract (v : LVec) (lo w : Nat) : (v.extract lo w).width = w := by
  simp [extract, width]

/-- A select-write keeps the target's width. -/
@[simp] theorem width_insertAt (v : LVec) (lo : Nat) (p : LVec) :
    (v.insertAt lo p).width = v.width := by
  simp [insertAt, width]

/-- `resizeU` has the requested width. -/
@[simp] theorem width_resizeU (v : LVec) (w : Nat) : (v.resizeU w).width = w := by
  simp [resizeU, width]

/-- The all-`x` vector has the requested width. -/
@[simp] theorem width_xVec (w : Nat) : (xVec w).width = w := by
  simp [xVec, replicate, width]

/-- Bit `i` of a slice (the `getD .lx` read primitive). -/
theorem getD_extract (v : LVec) (lo w i : Nat) :
    (v.extract lo w).bits[i]?.getD .lx = if i < w then v.bits[lo + i]?.getD .lx else .lx := by
  simp only [extract, Array.getElem?_ofFn]
  split <;> simp

/-- Bit `i` of a select-write. -/
theorem getD_insertAt (v : LVec) (lo : Nat) (p : LVec) (i : Nat) :
    (v.insertAt lo p).bits[i]?.getD .lx =
      if lo ≤ i ∧ i < lo + p.width then
        (if i < v.width then p.bits[i - lo]?.getD .lx else .lx)
      else v.bits[i]?.getD .lx := by
  simp only [insertAt, Array.getElem?_ofFn]
  by_cases hi : i < v.width
  · simp only [hi, dif_pos, Option.getD_some, if_true]
  · have : v.bits[i]? = none := Array.getElem?_eq_none (by simpa [width] using hi)
    simp only [hi, dif_neg, not_false_eq_true, Option.getD_none, if_false, this]
    split <;> rfl

/-- Extensionality on the `getD .lx` bit reads (4-state). -/
theorem ext_getD {u v : LVec} (hw : u.width = v.width)
    (h : ∀ i, i < u.width → u.bits[i]?.getD .lx = v.bits[i]?.getD .lx) : u = v := by
  cases u with | mk ub => cases v with | mk vb =>
  simp only [width] at hw h
  congr 1
  apply Array.ext hw
  intro i h1 h2
  have := h i h1
  rwa [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] at this

/-- Two vectors of equal width agreeing on every 1-bit window are equal. -/
theorem eq_of_extract_one {u v : LVec} (hw : u.width = v.width)
    (h : ∀ i, i < u.width → u.extract i 1 = v.extract i 1) : u = v := by
  apply ext_getD hw
  intro i hi
  have h1 := congrArg (fun x : LVec => x.bits[0]?.getD .lx) (h i hi)
  simpa [getD_extract] using h1

/-- A sub-window of a window is a window of the original vector. -/
theorem extract_extract (v : LVec) {lo w lo' w' : Nat} (h : lo' + w' ≤ w) :
    (v.extract lo w).extract lo' w' = v.extract (lo + lo') w' := by
  apply ext_getD (by simp)
  intro i hi
  simp only [width_extract] at hi
  rw [getD_extract, getD_extract, getD_extract, if_pos hi, if_pos hi, if_pos (by omega),
    Nat.add_assoc]

/-- Two windows are equal when all their 1-bit sub-windows are. -/
theorem extract_eq_of_bits {u v : LVec} {lo w : Nat}
    (h : ∀ k, k < w → u.extract (lo + k) 1 = v.extract (lo + k) 1) :
    u.extract lo w = v.extract lo w := by
  apply ext_getD (by simp)
  intro i hi
  simp only [width_extract] at hi
  have h1 := congrArg (fun x : LVec => x.bits[0]?.getD .lx) (h i hi)
  simp only [getD_extract, Nat.zero_lt_one, if_true, Nat.add_zero] at h1
  rw [getD_extract, getD_extract, if_pos hi, if_pos hi, h1]

/-- **Read-back of a write.** Extracting the window just written returns the
written part (in range). -/
theorem extract_insertAt_self {v p : LVec} {lo w : Nat} (hp : p.width = w)
    (hw : lo + w ≤ v.width) : (v.insertAt lo p).extract lo w = p := by
  apply ext_getD (by simp [hp])
  intro i hi
  simp only [width_extract] at hi
  rw [getD_extract, if_pos hi, getD_insertAt, if_pos ⟨by omega, by omega⟩,
    if_pos (by omega), Nat.add_sub_cancel_left]

/-- **Frame of a write.** A window disjoint from the written one is unchanged. -/
theorem extract_insertAt_of_disjoint {v p : LVec} {lo lo' w' : Nat}
    (h : lo' + w' ≤ lo ∨ lo + p.width ≤ lo') :
    (v.insertAt lo p).extract lo' w' = v.extract lo' w' := by
  apply ext_getD (by simp)
  intro i hi
  simp only [width_extract] at hi
  rw [getD_extract, getD_extract, if_pos hi, if_pos hi, getD_insertAt,
    if_neg (by omega)]

/-- Writing a vector's own window back is the identity (no range condition:
out-of-range positions are dropped by `insertAt` and read `x` by `extract`
alike). -/
theorem insertAt_extract_self (v : LVec) (lo w : Nat) : v.insertAt lo (v.extract lo w) = v := by
  apply ext_getD (by simp)
  intro i hi
  simp only [width_insertAt] at hi
  rw [getD_insertAt]
  by_cases h : lo ≤ i ∧ i < lo + (v.extract lo w).width
  · rw [if_pos h, if_pos hi, getD_extract, if_pos (by simp at h; omega), Nat.add_sub_cancel' h.1]
  · rw [if_neg h]

/-- A write of the window's current content is the identity. -/
theorem insertAt_eq_self_of_extract {v p : LVec} {lo w : Nat} (h : v.extract lo w = p) :
    v.insertAt lo p = v := by
  subst h; exact insertAt_extract_self v lo w

/-- Writes to disjoint windows commute. -/
theorem insertAt_comm {v p q : LVec} {lo lo' : Nat}
    (h : lo + p.width ≤ lo' ∨ lo' + q.width ≤ lo) :
    (v.insertAt lo p).insertAt lo' q = (v.insertAt lo' q).insertAt lo p := by
  apply ext_getD (by simp)
  intro i hi
  simp only [width_insertAt] at hi
  simp only [getD_insertAt, width_insertAt, hi, ↓reduceIte]
  by_cases h1 : lo ≤ i ∧ i < lo + p.width
  · have h2 : ¬(lo' ≤ i ∧ i < lo' + q.width) := by omega
    simp only [h1, h2, ↓reduceIte]
  · by_cases h2 : lo' ≤ i ∧ i < lo' + q.width
    · simp only [h1, h2, ↓reduceIte]
    · simp only [h1, h2, ↓reduceIte]

/-- A second write to the same window with a part at least as wide overwrites
the first. -/
theorem insertAt_insertAt_of_width_le {v p q : LVec} {lo : Nat} (h : p.width ≤ q.width) :
    (v.insertAt lo p).insertAt lo q = v.insertAt lo q := by
  apply ext_getD (by simp)
  intro i hi
  simp only [width_insertAt] at hi
  simp only [getD_insertAt, width_insertAt, hi, ↓reduceIte]
  by_cases h2 : lo ≤ i ∧ i < lo + q.width
  · rw [if_pos h2, if_pos h2]
  · have h1 : ¬(lo ≤ i ∧ i < lo + p.width) := by omega
    simp only [h1, h2, ↓reduceIte]

end LVec

/-! ## `SvState` algebra -/

namespace SvState

/-- Nothing is bound in the empty state. -/
@[simp] theorem lookup_nil (n : String) : lookup [] n = none := rfl

/-- `lookup` on a cons cell, with propositional key equality. -/
theorem lookup_cons (k : String) (v : LVec) (rest : SvState) (n : String) :
    lookup ((k, v) :: rest) n = if k = n then some v else lookup rest n := by
  simp [lookup]

/-- Lookup after `set`, both cases at once. -/
theorem lookup_set (st : SvState) (n : String) (v : LVec) (m : String) :
    lookup (set st n v) m = if n = m then some v else lookup st m := by
  induction st with
  | nil => simp [set, lookup_cons]
  | cons kv rest ih =>
      obtain ⟨k, w⟩ := kv
      by_cases hk : k = n
      · subst hk; by_cases hkm : k = m <;> simp [set, lookup_cons, hkm]
      · simp only [set, beq_iff_eq, hk, if_false, lookup_cons, ih]
        by_cases hkm : k = m
        · subst hkm; simp [Ne.symm hk]
        · simp [hkm]

/-- Lookup of the name just `set` returns the new value. -/
@[simp] theorem lookup_set_self (st : SvState) (n : String) (v : LVec) :
    lookup (set st n v) n = some v := by
  simp [lookup_set]

/-- `set` of one name leaves the lookup of every other name unchanged. -/
theorem lookup_set_ne (st : SvState) {n m : String} (v : LVec) (h : n ≠ m) :
    lookup (set st n v) m = lookup st m := by
  simp [lookup_set, h]

/-- A name is bound iff it is a key. -/
theorem lookup_isSome_iff {st : SvState} {n : String} :
    (lookup st n).isSome ↔ n ∈ st.map Prod.fst := by
  induction st with
  | nil => simp
  | cons kv rest ih =>
      obtain ⟨k, w⟩ := kv
      by_cases hk : k = n
      · subst hk; simp [lookup_cons]
      · simp [lookup_cons, hk, ih, Ne.symm hk]

/-- A name is unbound iff it is not a key. -/
theorem lookup_eq_none_iff {st : SvState} {n : String} :
    lookup st n = none ↔ n ∉ st.map Prod.fst := by
  rw [← lookup_isSome_iff]; simp

/-- Every key is bound to some value. -/
theorem exists_lookup_of_mem {st : SvState} {n : String} (h : n ∈ st.map Prod.fst) :
    ∃ v, lookup st n = some v := by
  rw [← lookup_isSome_iff] at h
  exact Option.isSome_iff_exists.mp h

/-- `set` of an existing key keeps the key list (in place replacement). -/
theorem keys_set {st : SvState} {n : String} (v : LVec) (h : n ∈ st.map Prod.fst) :
    (set st n v).map Prod.fst = st.map Prod.fst := by
  induction st with
  | nil => simp at h
  | cons kv rest ih =>
      obtain ⟨k, w⟩ := kv
      by_cases hk : k = n
      · subst hk; simp [set]
      · have h' : n ∈ rest.map Prod.fst := by
          simp only [List.map_cons, List.mem_cons] at h
          rcases h with h | h
          · exact absurd h.symm hk
          · exact h
        simp [set, hk, ih h']

/-- Re-writing the current binding is the identity. -/
theorem set_of_lookup {st : SvState} {n : String} {v : LVec} (h : lookup st n = some v) :
    set st n v = st := by
  induction st with
  | nil => simp at h
  | cons kv rest ih =>
      obtain ⟨k, w⟩ := kv
      by_cases hk : k = n
      · subst hk
        simp only [lookup_cons, if_true, Option.some.injEq] at h
        subst h; simp [set]
      · simp only [lookup_cons, hk, if_false] at h
        simp [set, hk, ih h]

/-- **State extensionality**: equal duplicate-free key lists and equal lookups
make two states equal. -/
theorem ext {st st' : SvState} (hk : st.map Prod.fst = st'.map Prod.fst)
    (hn : (st.map Prod.fst).Nodup) (h : ∀ n, lookup st n = lookup st' n) : st = st' := by
  induction st generalizing st' with
  | nil => cases st' <;> simp_all
  | cons kv rest ih =>
      obtain ⟨k, w⟩ := kv
      cases st' with
      | nil => simp at hk
      | cons kv' rest' =>
          obtain ⟨k', w'⟩ := kv'
          simp only [List.map_cons, List.cons.injEq] at hk
          obtain ⟨rfl, hk⟩ := hk
          simp only [List.map_cons, List.nodup_cons] at hn
          have hw : w = w' := by
            have := h k
            simp only [lookup_cons, if_true, Option.some.injEq] at this
            exact this
          subst hw
          have hrest : rest = rest' := by
            apply ih hk hn.2
            intro n
            by_cases hkn : k = n
            · subst hkn
              rw [lookup_eq_none_iff.mpr hn.1, lookup_eq_none_iff.mpr (hk ▸ hn.1)]
            · have := h n
              simp only [lookup_cons, hkn, if_false] at this
              exact this
          rw [hrest]

end SvState

/-! ## Windows, reads, and the comb profile -/

/-- A bit window of a signal: `(name, lo, width)` — bits `[lo, lo + width)`
of `name` (LSB-first). -/
abbrev Win := String × Nat × Nat

/-- Two windows overlap: same signal and intersecting HALF-OPEN bit ranges
(`lo < lo' + w'` and `lo' < lo + w`). Conservative on zero-width windows: a
zero-width window `(n, lo, 0)` overlaps `(n, lo', w')` exactly when
`lo' < lo < lo' + w'` (`("n", 2, 0)` overlaps `("n", 1, 3)`), although a
zero-width write changes no bit; it overlaps no window it merely touches at
an end, and no other zero-width window. -/
def Win.overlaps : Win → Win → Bool
  | (n, lo, w), (n', lo', w') => n == n' && decide (lo < lo' + w') && decide (lo' < lo + w)

/-- `Win.overlaps` as a proposition. -/
theorem Win.overlaps_eq_true {n n' : String} {lo w lo' w' : Nat} :
    Win.overlaps (n, lo, w) (n', lo', w') = true ↔ n = n' ∧ lo < lo' + w' ∧ lo' < lo + w := by
  simp [Win.overlaps, and_assoc]

/-- Non-overlap of two windows of the same signal: the ranges are disjoint. -/
theorem Win.overlaps_eq_false {n n' : String} {lo w lo' w' : Nat} :
    Win.overlaps (n, lo, w) (n', lo', w') = false ↔ n ≠ n' ∨ lo' + w' ≤ lo ∨ lo + w ≤ lo' := by
  rw [← Bool.not_eq_true, Win.overlaps_eq_true]
  by_cases h : n = n'
  · simp only [h, true_and, ne_eq, not_true_eq_false, false_or]
    omega
  · simp [h]

/-- `Win.overlaps` is symmetric. -/
theorem Win.overlaps_comm (a b : Win) : Win.overlaps a b = Win.overlaps b a := by
  obtain ⟨n, lo, w⟩ := a
  obtain ⟨n', lo', w'⟩ := b
  rw [Bool.eq_iff_iff, Win.overlaps_eq_true, Win.overlaps_eq_true]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1.symm, h3, h2⟩

/-- Declared width of a signal (the first declaration of that name — the one
`SvState.lookup` finds in `initState2`). -/
def Design2.declWidth (d : Design2) (n : String) : Option Nat :=
  (d.decls.toList.find? fun dc => dc.name == n).map Decl.width

/-- Write window `(name, lo, width)` of a LEAF continuous-assign target;
`none` = no single window. A whole-signal target is its full DECLARED width;
a constant-index element select `n[k]` (literal index) is the window
`resolveLhs2` computes for it (`(k·elemW, elemW)`); a dynamic select is out
of the comb profile. A concatenation target has no single window but IS in
the profile: its windows, one per leaf, are `Lhs2.windows?` below (the form
`CombDesign.assign` asks for). -/
def Lhs2.window? (d : Design2) : Lhs2 → Option Win
  | .ident n => (d.declWidth n).map fun w => (n, 0, w)
  | .slice n lo w => some (n, lo, w)
  | .index n (.lit c) elemW => c.toNat?.map fun k => (n, k * elemW, elemW)
  | _ => none

mutual

/-- Static write windows of a continuous-assign target, MSB-first: a leaf
target (whole signal, constant slice, constant-literal element select) is its
one `Lhs2.window?`; a concatenation `{p₀, …, pₖ}` — nested ones included — is
the windows of its parts in source order, flattened. These are the windows,
in the order, that `resolveConcatLhs2` resolves on a shaped state
(`resolveConcatLhs2_of_windows?`). `none` = out of profile (some leaf has no
static window: a dynamic select). -/
def Lhs2.windows? (d : Design2) : Lhs2 → Option (List Win)
  | .ident n => ((Lhs2.ident n).window? d).map ([·])
  | .slice n lo w => ((Lhs2.slice n lo w).window? d).map ([·])
  | .index n idx elemW => ((Lhs2.index n idx elemW).window? d).map ([·])
  | .concat parts => Lhs2.listWindows? d parts
termination_by structural t => t

/-- `Lhs2.windows?` of a part list, in order (`none` if a part is out of
profile). -/
def Lhs2.listWindows? (d : Design2) : List Lhs2 → Option (List Win)
  | [] => some []
  | t :: ts =>
      match Lhs2.windows? d t, Lhs2.listWindows? d ts with
      | some a, some b => some (a ++ b)
      | _, _ => none
termination_by structural ts => ts

end

/-- The write windows of a target as a list, MSB-first (`[]` off-profile; on
a comb design every target is in profile, `CombDesign.assign`). A leaf target
has at most one window; a concatenation has one per leaf. -/
def Lhs2.wins (d : Design2) (t : Lhs2) : List Win := (t.windows? d).getD []

/-- `Lhs2.listWindows?` of an empty part list. -/
@[simp] theorem Lhs2.listWindows?_nil (d : Design2) : Lhs2.listWindows? d [] = some [] := by
  simp [Lhs2.listWindows?]

/-- `Lhs2.listWindows?` of a part list succeeds exactly when its head and its
tail do, and is their concatenation. -/
theorem Lhs2.listWindows?_cons_eq_some {d : Design2} {t : Lhs2} {ts : List Lhs2}
    {ws : List Win} : Lhs2.listWindows? d (t :: ts) = some ws ↔
      ∃ a b, t.windows? d = some a ∧ Lhs2.listWindows? d ts = some b ∧ ws = a ++ b := by
  rw [Lhs2.listWindows?]
  cases t.windows? d <;> cases Lhs2.listWindows? d ts <;> simp [eq_comm]

/-- `Lhs2.listWindows?` of a cons cell, computed (the `simp` normal form on
concrete part lists). -/
@[simp] theorem Lhs2.listWindows?_cons (d : Design2) (t : Lhs2) (ts : List Lhs2) :
    Lhs2.listWindows? d (t :: ts) =
      (t.windows? d).bind fun a => (Lhs2.listWindows? d ts).map fun b => a ++ b := by
  rw [Lhs2.listWindows?]
  cases t.windows? d <;> cases Lhs2.listWindows? d ts <;> rfl

/-- `Lhs2.windows?` of a concatenation is its parts' windows. -/
@[simp] theorem Lhs2.windows?_concat (d : Design2) (parts : List Lhs2) :
    (Lhs2.concat parts).windows? d = Lhs2.listWindows? d parts := by
  simp [Lhs2.windows?]

/-- `Lhs2.windows?` of a whole-signal target: its declared width. -/
@[simp] theorem Lhs2.windows?_ident (d : Design2) (n : String) :
    (Lhs2.ident n).windows? d = (d.declWidth n).map fun w => [(n, 0, w)] := by
  simp [Lhs2.windows?, Lhs2.window?, Option.map_map, Function.comp_def]

/-- `Lhs2.windows?` of a constant slice target. -/
@[simp] theorem Lhs2.windows?_slice (d : Design2) (n : String) (lo w : Nat) :
    (Lhs2.slice n lo w).windows? d = some [(n, lo, w)] := by
  simp [Lhs2.windows?, Lhs2.window?]

/-- `Lhs2.windows?` of a constant-literal element-select target. -/
@[simp] theorem Lhs2.windows?_index_lit (d : Design2) (n : String) (c : LVec) (elemW : Nat) :
    (Lhs2.index n (.lit c) elemW).windows? d =
      c.toNat?.map fun k => [(n, k * elemW, elemW)] := by
  simp [Lhs2.windows?, Lhs2.window?, Option.map_map, Function.comp_def]

/-- A leaf target with a window has exactly that one window. -/
theorem Lhs2.windows?_of_window? {d : Design2} {t : Lhs2} {wn : Win}
    (h : t.window? d = some wn) : t.windows? d = some [wn] := by
  cases t with
  | ident n => simp only [Lhs2.windows?, h, Option.map_some]
  | slice n lo w => simp only [Lhs2.windows?, h, Option.map_some]
  | index n idx elemW => simp only [Lhs2.windows?, h, Option.map_some]
  | concat parts => simp [Lhs2.window?] at h

/-- A leaf target in profile has exactly one window, its `Lhs2.window?`. -/
theorem Lhs2.window?_of_windows? {d : Design2} {t : Lhs2} (hnc : ∀ ps, t = .concat ps → False)
    {ws : List Win} (h : t.windows? d = some ws) : ∃ wn, t.window? d = some wn ∧ ws = [wn] := by
  cases t with
  | concat ps => exact absurd rfl (hnc ps)
  | _ =>
      simp only [Lhs2.windows?] at h
      obtain ⟨wn, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨wn, hw, rfl⟩

/-- A target in profile: `Lhs2.wins` is its window list. -/
theorem Lhs2.wins_of_windows? {d : Design2} {t : Lhs2} {ws : List Win}
    (h : t.windows? d = some ws) : t.wins d = ws := by
  simp [Lhs2.wins, h]

/-- A leaf target with a window: `Lhs2.wins` is that one window. -/
theorem Lhs2.wins_of_window? {d : Design2} {t : Lhs2} {wn : Win}
    (h : t.window? d = some wn) : t.wins d = [wn] :=
  Lhs2.wins_of_windows? (Lhs2.windows?_of_window? h)

/-- A target with some window is in profile. -/
theorem Lhs2.exists_windows?_of_mem_wins {d : Design2} {t : Lhs2} {wn : Win}
    (h : wn ∈ t.wins d) : ∃ ws, t.windows? d = some ws := by
  cases hw : t.windows? d with
  | none => simp [Lhs2.wins, hw] at h
  | some ws => exact ⟨ws, rfl⟩

/-- `Lhs2.wins` of a whole-signal target. -/
@[simp] theorem Lhs2.wins_ident (d : Design2) (n : String) :
    (Lhs2.ident n).wins d = ((d.declWidth n).map fun w => (n, 0, w)).toList := by
  simp only [Lhs2.wins, Lhs2.windows?_ident]
  cases d.declWidth n <;> rfl

/-- `Lhs2.wins` of a constant slice target. -/
@[simp] theorem Lhs2.wins_slice (d : Design2) (n : String) (lo w : Nat) :
    (Lhs2.slice n lo w).wins d = [(n, lo, w)] := by
  simp [Lhs2.wins]

/-- `Lhs2.wins` of a constant-literal element-select target. -/
@[simp] theorem Lhs2.wins_index_lit (d : Design2) (n : String) (c : LVec) (elemW : Nat) :
    (Lhs2.index n (.lit c) elemW).wins d = (c.toNat?.map fun k => (n, k * elemW, elemW)).toList := by
  simp only [Lhs2.wins, Lhs2.windows?_index_lit]
  cases c.toNat? <;> rfl

/-- `Lhs2.wins` of a concatenation target. -/
@[simp] theorem Lhs2.wins_concat (d : Design2) (parts : List Lhs2) :
    (Lhs2.concat parts).wins d = (Lhs2.listWindows? d parts).getD [] := by
  simp [Lhs2.wins]

/-- A leaf target's window list has at most one window, so it is pairwise
anything (the `CombDesign.selfDisjoint` obligation of a leaf target). -/
theorem Lhs2.wins_pairwise_of_leaf {d : Design2} {t : Lhs2} (h : ∀ ps, t ≠ .concat ps)
    (R : Win → Win → Prop) : (t.wins d).Pairwise R := by
  cases hws : t.windows? d with
  | none => simp [Lhs2.wins, hws]
  | some ws =>
      obtain ⟨wn, -, rfl⟩ := Lhs2.window?_of_windows? h hws
      simp [Lhs2.wins, hws]

/-- Total width of a window list (`Win`'s third component, summed). -/
def Win.sumWidth : List Win → Nat
  | [] => 0
  | wn :: rest => wn.2.2 + Win.sumWidth rest

/-- An MSB-first window list with each window's bit OFFSET in the
concatenated value: the total width of the windows after it.
`writeConcatLhs2` gives the first window the high slice
`value[total-1 -: w₀]` and the last one the low slice `value[w-1:0]`. -/
def Win.placed : List Win → List (Win × Nat)
  | [] => []
  | wn :: rest => (wn, Win.sumWidth rest) :: Win.placed rest

@[simp] theorem Win.sumWidth_nil : Win.sumWidth [] = 0 := rfl

@[simp] theorem Win.sumWidth_cons (wn : Win) (rest : List Win) :
    Win.sumWidth (wn :: rest) = wn.2.2 + Win.sumWidth rest := rfl

@[simp] theorem Win.placed_nil : Win.placed [] = [] := rfl

@[simp] theorem Win.placed_cons (wn : Win) (rest : List Win) :
    Win.placed (wn :: rest) = (wn, Win.sumWidth rest) :: Win.placed rest := rfl

/-- `Win.placed` keeps the windows (and their order). -/
@[simp] theorem Win.map_fst_placed : ∀ ws : List Win, (Win.placed ws).map Prod.fst = ws
  | [] => rfl
  | wn :: rest => by simp [Win.map_fst_placed rest]

/-- A placed window is a window of the list. -/
theorem Win.mem_of_mem_placed {ws : List Win} {wn : Win} {off : Nat}
    (h : (wn, off) ∈ Win.placed ws) : wn ∈ ws := by
  have := List.mem_map_of_mem (f := Prod.fst) h
  rwa [Win.map_fst_placed] at this

/-- Every window of the list is placed at some offset. -/
theorem Win.exists_mem_placed {ws : List Win} {wn : Win} (h : wn ∈ ws) :
    ∃ off, (wn, off) ∈ Win.placed ws := by
  rw [← Win.map_fst_placed ws] at h
  obtain ⟨⟨wn', off⟩, hm, rfl⟩ := List.mem_map.mp h
  exact ⟨off, hm⟩

/-- A placed window lies inside the concatenated value: offset plus width is
at most the total width. -/
theorem Win.le_sumWidth_of_mem_placed : ∀ {ws : List Win} {wn : Win} {off : Nat},
    (wn, off) ∈ Win.placed ws → off + wn.2.2 ≤ Win.sumWidth ws
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: rest, wn, off, h => by
      rw [Win.placed_cons, List.mem_cons] at h
      rcases h with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Win.sumWidth_cons]
        omega
      · have := Win.le_sumWidth_of_mem_placed h
        simp only [Win.sumWidth_cons]
        omega

/-- A read of an expression: the WHOLE vector of a signal (`ident n`:
`evalPure2` returns it, width included), or a bit WINDOW of it (`slice
(ident n) lo w`, constant `index (ident n) (lit c) elemW`). -/
inductive ReadWin where
  | whole (name : String)
  | win (name : String) (lo w : Nat)
deriving Repr, DecidableEq, Inhabited

/-- The signal a read observes. -/
def ReadWin.name : ReadWin → String
  | .whole n | .win n _ _ => n

/-- A read overlaps a write window: a whole read overlaps every window of its
signal (conservative); a window read overlaps per `Win.overlaps`. -/
def ReadWin.overlaps : ReadWin → Win → Bool
  | .whole n, (m, _, _) => n == m
  | .win n lo w, wn => Win.overlaps (n, lo, w) wn

/-- A 1-bit window read overlaps a write window iff it reads a bit inside it. -/
theorem ReadWin.overlaps_win_one {n m : String} {i lo w : Nat} :
    (ReadWin.win n i 1).overlaps (m, lo, w) = true ↔ n = m ∧ lo ≤ i ∧ i < lo + w := by
  simp only [ReadWin.overlaps, Win.overlaps_eq_true]
  by_cases h : n = m
  · simp only [h, true_and]; omega
  · simp [h]

/-- Two states agree on what a read observes: the whole binding for a whole
read; the width and the window's bits for a window read (both sides unbound
counts as agreement — the evaluator refuses identically). -/
def ReadWin.agree (st st' : SvState) : ReadWin → Prop
  | .whole n => SvState.lookup st n = SvState.lookup st' n
  | .win n lo w =>
      (SvState.lookup st n).map (fun v => (v.width, v.extract lo w)) =
        (SvState.lookup st' n).map (fun v => (v.width, v.extract lo w))

/-- Read set of `slice base lo w` given the base's own reads `dflt`: a window
when the base is an identifier, else `dflt`. -/
def Expr2.sliceReads : Expr2 → Nat → Nat → List ReadWin → List ReadWin
  | .ident n, lo, w, _ => [.win n lo w]
  | _, _, _, dflt => dflt

/-- Read set of `index base idx elemW` given the operands' reads `dflt`: a
window for an identifier base with a literal, known index; else `dflt`. -/
def Expr2.indexReads : Expr2 → Expr2 → Nat → List ReadWin → List ReadWin
  | .ident n, .lit c, elemW, dflt =>
      match c.toNat? with
      | some k => [.win n (k * elemW) elemW]
      | none => dflt
  | _, _, _, dflt => dflt

mutual

/-- Conservative read set of an expression (`evalPure2_congr_reads`: two
states agreeing on every read evaluate the expression identically). `ident n`
is a whole read; `slice (ident n) lo w` and a constant-literal `index` are
window reads; every other node is the union of its children's reads. -/
def Expr2.reads : Expr2 → List ReadWin
  | .ident n => [.whole n]
  | .lit _ | .unsupported _ _ => []
  | .slice a lo w => Expr2.sliceReads a lo w a.reads
  | .index a i elemW => Expr2.indexReads a i elemW (a.reads ++ i.reads)
  | .unary _ a | .resizeSigned _ a | .squash2 a | .repl _ a | .reduce _ a | .resize _ a => a.reads
  | .binary _ l r | .scmp _ l r | .logical _ l r => l.reads ++ r.reads
  | .ternary c t f => c.reads ++ t.reads ++ f.reads
  | .concat parts => Expr2.listReads parts.toList
termination_by structural e => e

/-- `Expr2.reads` of a part list, concatenated. -/
def Expr2.listReads : List Expr2 → List ReadWin
  | [] => []
  | e :: es => e.reads ++ Expr2.listReads es
termination_by structural es => es

end

/-- Process `i` is a continuous assign one of whose target's write windows is
`wn` (the one window of a leaf target; any leaf window of a concatenation). -/
def Design2.Writes (d : Design2) (i : Nat) (wn : Win) : Prop :=
  ∃ t e, d.processes[i]? = some (.assign t e) ∧ wn ∈ t.wins d

/-- A leaf assign writes its window (the pre-concatenation form of
`Design2.Writes`). -/
theorem Design2.writes_of_window? {d : Design2} {i : Nat} {t : Lhs2} {e : Expr2} {wn : Win}
    (hp : d.processes[i]? = some (.assign t e)) (hw : t.window? d = some wn) : d.Writes i wn :=
  ⟨t, e, hp, by rw [Lhs2.wins_of_window? hw]; exact List.mem_singleton_self _⟩

/-- Some process writes a window of `n`. -/
def Driven (d : Design2) (n : String) : Prop := ∃ i lo w, d.Writes i (n, lo, w)

/-- No process writes any window of `n` (inputs, constants, undriven nets). -/
def NotDriven (d : Design2) (n : String) : Prop := ¬ Driven d n

/-- **The comb profile** (well-formedness bundle, discharged once per design).
Every field is a static fact about the design; nothing mentions a state. -/
structure CombDesign (d : Design2) : Prop where
  /-- Declaration names are pairwise distinct (states are then extensional). -/
  nodup : (d.decls.toList.map Decl.name).Nodup
  /-- Every process is a continuous assign whose target has static write
  windows: a leaf with a window, or a (possibly nested) concatenation of
  such leaves. -/
  assign : ∀ (i : Nat) (p : Process2), d.processes[i]? = some p →
    ∃ (t : Lhs2) (e : Expr2) (ws : List Win), p = .assign t e ∧ t.windows? d = some ws
  /-- Every write window lies inside its signal's declared width. -/
  inWidth : ∀ i n lo w, d.Writes i (n, lo, w) → ∃ dw, d.declWidth n = some dw ∧ lo + w ≤ dw
  /-- No driven signal is an input port (`applyInputs2` never touches a
  driven signal). -/
  notInput : ∀ n, Driven d n → n ∉ d.inputNames.toList
  /-- Windows of distinct processes are disjoint (one driver per bit). -/
  disjoint : ∀ i j wi wj, i ≠ j → d.Writes i wi → d.Writes j wj → Win.overlaps wi wj = false
  /-- The windows of ONE target are pairwise disjoint (a concatenation
  writes each bit at most once; a leaf target has one window,
  `Lhs2.wins_pairwise_of_leaf`). -/
  selfDisjoint : ∀ (i : Nat) (t : Lhs2) (e : Expr2), d.processes[i]? = some (.assign t e) →
    (t.wins d).Pairwise fun a b => Win.overlaps a b = false
  /-- No `.unsupported` node in any right-hand side. -/
  rhsFree : ∀ (i : Nat) (t : Lhs2) (e : Expr2), d.processes[i]? = some (.assign t e) →
    e.unsupportedFree = true
  /-- Every identifier a right-hand side mentions is declared. -/
  rhsDeclared : ∀ (i : Nat) (t : Lhs2) (e : Expr2), d.processes[i]? = some (.assign t e) →
    ∀ x ∈ e.idents, x ∈ d.decls.toList.map Decl.name
  /-- A driven signal's initializer, if any, has the declared width (so
  `initState2 d` satisfies `StateShape d`). -/
  initWidth : ∀ n, Driven d n → ∀ dc ∈ d.decls.toList, dc.name = n →
    ∀ v, dc.init = some v → v.width = dc.width
  /-- No input port is a 2-state declaration. `applyInputs2` stores a stimulus
  value verbatim on a 4-state input, but squashes x/z to 0 at the boundary of
  a 2-state one (`Decl.twoState`, IEEE 1800-2023 §6.11), so the comb theorems
  (`Runs2.comb_snapshot`: "every input the entry binds holds exactly that
  value") are stated for 4-state input ports only. Added when the merge with
  the 2-state declaration tier changed `applyInputs2`/`initState2`. -/
  inFourState : ∀ dc ∈ d.decls.toList, dc.isInput = true → dc.twoState = false

/-- States of the right shape: exactly the declared names as keys, in
declaration order; every driven signal at its declared width. -/
structure StateShape (d : Design2) (st : SvState) : Prop where
  /-- The key list is the declaration-name list. -/
  keys : st.map Prod.fst = d.decls.toList.map Decl.name
  /-- Driven signals are bound at their declared width. -/
  driven : ∀ n, Driven d n → ∃ v, SvState.lookup st n = some v ∧ d.declWidth n = some v.width

/-- The settle fixpoint equations: each window of an assign's target holds
its slice of the right-hand side's value resized to the target's total width
— window `(n, lo, w)` placed at offset `off` (`Win.placed`, MSB-first as
`writeConcatLhs2` distributes it) holds bits `[off, off + w)` of
`v.resizeU (Win.sumWidth (t.wins d))`. For a leaf target (one window,
offset `0`, total `w`) that is the whole resized value `v.resizeU w`
(`CombEqs.extract_slice` and friends, `Comb2.lean`). -/
def CombEqs (d : Design2) (st : SvState) : Prop :=
  ∀ (i : Nat) (t : Lhs2) (e : Expr2) (n : String) (lo w off : Nat),
    d.processes[i]? = some (.assign t e) → ((n, lo, w), off) ∈ Win.placed (t.wins d) →
    ∃ old v, SvState.lookup st n = some old ∧ evalPure2 st e = .ok v ∧
      old.extract lo w = (v.resizeU (Win.sumWidth (t.wins d))).extract off w

/-- Acyclicity certificate: a rank on process indices such that every
process reads only windows written by strictly lower-ranked processes
(self-reads are thereby forbidden). -/
def Acyclic (d : Design2) : Prop :=
  ∃ rank : Nat → Nat, ∀ (i j : Nat) (ti : Lhs2) (ei : Expr2) (tj : Lhs2) (ej : Expr2) (wj : Win),
    d.processes[i]? = some (.assign ti ei) →
    d.processes[j]? = some (.assign tj ej) → wj ∈ tj.wins d →
    (∃ r ∈ ei.reads, r.overlaps wj = true) → rank j < rank i

/-! ## Declarations and the profile's basic consequences -/

/-- `declWidth` as a `find?` fact. -/
theorem Design2.declWidth_eq_some_iff {d : Design2} {n : String} {w : Nat} :
    d.declWidth n = some w ↔
      ∃ dc, d.decls.toList.find? (fun dc => dc.name == n) = some dc ∧ dc.width = w := by
  simp [Design2.declWidth, Option.map_eq_some_iff]

/-- A name with a declared width is a declared name. -/
theorem Design2.mem_names_of_declWidth {d : Design2} {n : String} {w : Nat}
    (h : d.declWidth n = some w) : n ∈ d.decls.toList.map Decl.name := by
  obtain ⟨dc, hf, -⟩ := Design2.declWidth_eq_some_iff.mp h
  have hn : dc.name = n := by simpa using List.find?_some hf
  exact List.mem_map.mpr ⟨dc, List.mem_of_find?_eq_some hf, hn⟩

/-- A declared name has a declared width. -/
theorem Design2.declWidth_isSome_of_mem {d : Design2} {n : String}
    (h : n ∈ d.decls.toList.map Decl.name) : (d.declWidth n).isSome := by
  obtain ⟨dc, hdc, rfl⟩ := List.mem_map.mp h
  cases hf : d.decls.toList.find? (fun x => x.name == dc.name) with
  | none =>
      have := List.find?_eq_none.mp hf dc hdc
      simp at this
  | some _ => simp [Design2.declWidth, hf]

/-- With duplicate-free names, a declaration's own width is the declared width. -/
theorem Design2.declWidth_of_mem {d : Design2} (hn : (d.decls.toList.map Decl.name).Nodup)
    {dc : Decl} (h : dc ∈ d.decls.toList) : d.declWidth dc.name = some dc.width := by
  simp only [Design2.declWidth]
  generalize d.decls.toList = ds at hn h
  induction ds with
  | nil => cases h
  | cons x rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · have hx : x.name ≠ dc.name := by
          intro hx; exact hn.1 (hx ▸ List.mem_map.mpr ⟨dc, h, rfl⟩)
        simp [hx, ih hn.2 h]

namespace CombDesign

variable {d : Design2}

/-- A process index in range is a windowed assign. -/
theorem writes_of_lt (hd : CombDesign d) {i : Nat} (hi : i < d.processes.size) :
    ∃ t e ws, d.processes[i]? = some (.assign t e) ∧ t.windows? d = some ws := by
  obtain ⟨t, e, ws, hp, hw⟩ := hd.assign i d.processes[i] (Array.getElem?_eq_getElem hi)
  exact ⟨t, e, ws, hp ▸ Array.getElem?_eq_getElem hi, hw⟩

/-- The target of an assign of a comb design is in profile. -/
theorem windows?_of_proc (hd : CombDesign d) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) : t.windows? d = some (t.wins d) := by
  obtain ⟨t', e', ws, h, hw⟩ := hd.assign i _ hp
  simp only [Process2.assign.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [Lhs2.wins_of_windows? hw, hw]

/-- Every process is a comb-phase process: the comb ready list is every index. -/
theorem combIndices_eq (hd : CombDesign d) : d.combIndices = List.range d.processes.size := by
  unfold Design2.combIndices
  rw [List.filter_eq_self]
  intro i hi
  obtain ⟨t, e, wn, hp, -⟩ := hd.writes_of_lt (List.mem_range.mp hi)
  simp [hp, Process2.isCombPhase]

/-- No process is an edge-phase process. -/
theorem edgeIndices_eq (hd : CombDesign d) : d.edgeIndices = [] := by
  unfold Design2.edgeIndices
  rw [List.filter_eq_nil_iff]
  intro i hi
  obtain ⟨t, e, wn, hp, -⟩ := hd.writes_of_lt (List.mem_range.mp hi)
  simp [hp, Process2.isEdgePhase]

/-- No process is an async-reset process: the reset-event phase never fires. -/
theorem resetIndices_eq (hd : CombDesign d) (prev cur : SvState) :
    d.resetIndices prev cur = [] := by
  unfold Design2.resetIndices
  rw [List.filter_eq_nil_iff]
  intro i hi
  obtain ⟨t, e, wn, hp, -⟩ := hd.writes_of_lt (List.mem_range.mp hi)
  simp [hp]

/-- Every comb pass order a schedule can pick is a permutation of all
process indices. -/
theorem choose_perm_range (hd : CombDesign d) (σ : ScheduleOracle) (k : Nat) :
    (σ.choose k d.combIndices).Perm (List.range d.processes.size) :=
  hd.combIndices_eq ▸ σ.choose_perm k d.combIndices

/-- A comb pass order lists every process exactly once. -/
theorem nodup_choose (hd : CombDesign d) (σ : ScheduleOracle) (k : Nat) :
    (σ.choose k d.combIndices).Nodup :=
  (hd.choose_perm_range σ k).nodup_iff.mpr List.nodup_range

/-- Membership in a comb pass order is being a process index. -/
theorem mem_choose (hd : CombDesign d) (σ : ScheduleOracle) (k i : Nat) :
    i ∈ σ.choose k d.combIndices ↔ i < d.processes.size := by
  rw [(hd.choose_perm_range σ k).mem_iff, List.mem_range]

end CombDesign

/-! ## `StateShape` -/

namespace StateShape

variable {d : Design2} {st : SvState}

/-- A shaped state's keys are duplicate-free. -/
theorem nodup (hd : CombDesign d) (hs : StateShape d st) : (st.map Prod.fst).Nodup :=
  hs.keys ▸ hd.nodup

/-- Every declared name is bound in a shaped state. -/
theorem lookup_of_mem (hs : StateShape d st) {n : String}
    (h : n ∈ d.decls.toList.map Decl.name) : ∃ v, SvState.lookup st n = some v :=
  SvState.exists_lookup_of_mem (hs.keys ▸ h)

/-- Shaped states are extensional in their lookups. -/
theorem ext (hd : CombDesign d) {st' : SvState} (hs : StateShape d st) (hs' : StateShape d st')
    (h : ∀ n, SvState.lookup st n = SvState.lookup st' n) : st = st' :=
  SvState.ext (hs.keys.trans hs'.keys.symm) (hs.nodup hd) h

/-- A select-write into a bound signal keeps the shape. -/
theorem set_insertAt (hs : StateShape d st) {n : String} {old : LVec}
    (hold : SvState.lookup st n = some old) (lo : Nat) (p : LVec) :
    StateShape d (SvState.set st n (old.insertAt lo p)) := by
  refine ⟨?_, ?_⟩
  · rw [SvState.keys_set _ (SvState.lookup_isSome_iff.mp (by simp [hold])), hs.keys]
  · intro m hm
    obtain ⟨v, hv, hw⟩ := hs.driven m hm
    by_cases hnm : n = m
    · subst hnm
      rw [hold] at hv; cases hv
      exact ⟨_, SvState.lookup_set_self _ _ _, by simpa using hw⟩
    · exact ⟨v, by rw [SvState.lookup_set_ne _ _ hnm, hv], hw⟩

end StateShape

/-- The written signal of a process is bound in a shaped state at its
declared width, and the window fits in it. -/
theorem CombDesign.lookup_writes {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {n : String} {lo w : Nat} (hW : d.Writes i (n, lo, w)) :
    ∃ old, SvState.lookup st n = some old ∧ lo + w ≤ old.width ∧
      d.declWidth n = some old.width := by
  obtain ⟨dw, hdw, hle⟩ := hd.inWidth i n lo w hW
  obtain ⟨v, hv, hvw⟩ := hs.driven n ⟨i, lo, w, hW⟩
  rw [hdw] at hvw; cases hvw
  exact ⟨v, hv, hle, hdw⟩

/-! ## Read agreement -/

namespace ReadWin

/-- Agreement is reflexive. -/
theorem agree_refl (st : SvState) (r : ReadWin) : r.agree st st := by
  cases r <;> rfl

/-- Agreement is symmetric. -/
theorem agree_symm {st st' : SvState} {r : ReadWin} (h : r.agree st st') : r.agree st' st := by
  cases r <;> exact h.symm

/-- Agreement is transitive. -/
theorem agree_trans {st st' st'' : SvState} {r : ReadWin} (h : r.agree st st')
    (h' : r.agree st' st'') : r.agree st st'' := by
  cases r <;> exact h.trans h'

/-- Equal bindings of the read's signal give agreement. -/
theorem agree_of_lookup {st st' : SvState} {r : ReadWin}
    (h : SvState.lookup st r.name = SvState.lookup st' r.name) : r.agree st st' := by
  cases r <;> simp only [agree, name] at h ⊢ <;> rw [h]

/-- **Frame of one select-write**: a read not overlapping the written window
`(n, lo, w)` (part of width `w`) sees the same thing before and after. -/
theorem agree_set {st : SvState} {n : String} {old p : LVec} {lo w : Nat}
    (hold : SvState.lookup st n = some old) (hp : p.width = w) {r : ReadWin}
    (h : r.overlaps (n, lo, w) = false) :
    r.agree st (SvState.set st n (old.insertAt lo p)) := by
  cases r with
  | whole m =>
      have hmn : n ≠ m := by
        intro hnm; subst hnm; simp [overlaps] at h
      exact (SvState.lookup_set_ne _ _ hmn).symm
  | win m lo' w' =>
      simp only [overlaps] at h
      by_cases hmn : n = m
      · subst hmn
        rw [Win.overlaps_eq_false] at h
        simp only [ne_eq, not_true_eq_false, false_or] at h
        simp only [agree, hold, SvState.lookup_set_self, Option.map_some, LVec.width_insertAt,
          Option.some.injEq, Prod.mk.injEq, true_and]
        rw [LVec.extract_insertAt_of_disjoint (by omega)]
      · simp only [agree, SvState.lookup_set_ne _ _ hmn]

/-- Window agreement from the two bindings. -/
theorem agree_win_of_lookup {st st' : SvState} {n : String} {lo w : Nat} {u u' : LVec}
    (hu : SvState.lookup st n = some u) (hu' : SvState.lookup st' n = some u')
    (hw : u.width = u'.width) (he : u.extract lo w = u'.extract lo w) :
    (ReadWin.win n lo w).agree st st' := by
  simp [agree, hu, hu', hw, he]

/-- Window agreement from agreement of the widths and of every 1-bit
sub-window (the bit-by-bit route of a stability argument). -/
theorem agree_win_of_bits {st st' : SvState} {n : String} {lo w : Nat}
    (h0 : (SvState.lookup st n).map LVec.width = (SvState.lookup st' n).map LVec.width)
    (h : ∀ k, k < w → (ReadWin.win n (lo + k) 1).agree st st') :
    (ReadWin.win n lo w).agree st st' := by
  cases hu : SvState.lookup st n <;> cases hu' : SvState.lookup st' n <;>
    simp only [hu, hu', Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq] at h0
  · simp [agree, hu, hu']
  · rename_i u u'
    refine agree_win_of_lookup hu hu' h0 (LVec.extract_eq_of_bits fun k hk => ?_)
    have := h k hk
    simp only [agree, hu, hu', Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
    exact this.2

/-- Agreement on every 1-bit window of `n` is equality of the bindings. -/
theorem lookup_eq_of_agree_bits {st st' : SvState} {n : String}
    (h : ∀ i, (ReadWin.win n i 1).agree st st') :
    SvState.lookup st n = SvState.lookup st' n := by
  have h0 := h 0
  simp only [agree] at h0
  cases hu : SvState.lookup st n with
  | none =>
      rw [hu] at h0
      cases hu' : SvState.lookup st' n
      · rfl
      · rw [hu'] at h0; simp at h0
  | some u =>
      rw [hu] at h0
      cases hu' : SvState.lookup st' n with
      | none => rw [hu'] at h0; simp at h0
      | some u' =>
          rw [hu'] at h0
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h0
          congr 1
          apply LVec.eq_of_extract_one h0.1
          intro i _
          have hi := h i
          simp only [agree, hu, hu', Option.map_some, Option.some.injEq, Prod.mk.injEq] at hi
          exact hi.2

end ReadWin

/-- Two shaped states agreeing on every 1-bit window of every signal are equal. -/
theorem StateShape.eq_of_agree_bits {d : Design2} (hd : CombDesign d) {st st' : SvState}
    (hs : StateShape d st) (hs' : StateShape d st')
    (h : ∀ n i, (ReadWin.win n i 1).agree st st') : st = st' :=
  hs.ext hd hs' fun n => ReadWin.lookup_eq_of_agree_bits (h n)

/-! ## Window-granular congruence of `evalPure2` -/

private theorem sliceReads_eq_dflt {a : Expr2} (h : ∀ m, a ≠ .ident m) (lo w : Nat)
    (dflt : List ReadWin) : Expr2.sliceReads a lo w dflt = dflt := by
  cases a <;> first | rfl | exact absurd rfl (h _)

private theorem indexReads_eq_dflt {a i : Expr2}
    (h : ∀ m c k, a = .ident m → i = .lit c → c.toNat? ≠ some k) (elemW : Nat)
    (dflt : List ReadWin) : Expr2.indexReads a i elemW dflt = dflt := by
  cases a with
  | ident m =>
      cases i with
      | lit c =>
          cases hc : c.toNat? with
          | none => simp [Expr2.indexReads, hc]
          | some k => exact absurd hc (h m c k rfl rfl)
      | _ => rfl
  | _ => rfl

private theorem evalPure2_slice_ident_congr {st st' : SvState} {n : String} {lo w : Nat}
    (h : (ReadWin.win n lo w).agree st st') :
    evalPure2 st (.slice (.ident n) lo w) = evalPure2 st' (.slice (.ident n) lo w) := by
  simp only [ReadWin.agree] at h
  cases hu : SvState.lookup st n <;> cases hu' : SvState.lookup st' n <;>
    simp only [hu, hu', Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
      Prod.mk.injEq] at h
  · simp [readSignal, hu, hu']
  · simp [readSignal, hu, hu', h.2]

private theorem evalPure2_index_ident_congr {st st' : SvState} {n : String} {c : LVec}
    {elemW k : Nat} (hk : c.toNat? = some k)
    (h : (ReadWin.win n (k * elemW) elemW).agree st st') :
    evalPure2 st (.index (.ident n) (.lit c) elemW) =
      evalPure2 st' (.index (.ident n) (.lit c) elemW) := by
  simp only [ReadWin.agree] at h
  cases hu : SvState.lookup st n <;> cases hu' : SvState.lookup st' n <;>
    simp only [hu, hu', Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
      Prod.mk.injEq] at h
  · simp [readSignal, hu, hu']
  · simp [readSignal, hu, hu', hk, h.1, h.2]

private theorem congr_reads_aux (st st' : SvState) : ∀ n : Nat,
    (∀ e : Expr2, e.size < n → (∀ r ∈ e.reads, r.agree st st') →
        evalPure2 st e = evalPure2 st' e) ∧
    (∀ es : List Expr2, Expr2.listSize es < n →
      (∀ r ∈ Expr2.listReads es, r.agree st st') → evalPures2 st es = evalPures2 st' es)
  | 0 => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨ihE, ihL⟩ := congr_reads_aux st st' n
    refine ⟨fun e hs hb => ?_, fun es hs hb => ?_⟩
    · cases e with
      | ident name =>
          have h := hb (.whole name) (by simp [Expr2.reads])
          simp only [ReadWin.agree] at h
          simp only [evalPure2, readSignal, h]
      | slice a lo w =>
          by_cases ha : ∃ m, a = .ident m
          · obtain ⟨m, rfl⟩ := ha
            exact evalPure2_slice_ident_congr (hb _ (by simp [Expr2.reads, Expr2.sliceReads]))
          · have hr : (Expr2.slice a lo w).reads = a.reads := by
              simp only [Expr2.reads]
              exact sliceReads_eq_dflt (fun m h => ha ⟨m, h⟩) lo w _
            simp only [Expr2.size] at hs
            rw [evalPure2_slice, evalPure2_slice,
              ihE a (by omega) (fun r h => hb r (hr ▸ h))]
      | index a idx elemW =>
          by_cases ha : ∃ m c k, a = .ident m ∧ idx = .lit c ∧ c.toNat? = some k
          · obtain ⟨m, c, k, rfl, rfl, hk⟩ := ha
            exact evalPure2_index_ident_congr hk
              (hb _ (by simp [Expr2.reads, Expr2.indexReads, hk]))
          · have hr : (Expr2.index a idx elemW).reads = a.reads ++ idx.reads := by
              simp only [Expr2.reads]
              exact indexReads_eq_dflt (fun m c k h1 h2 h3 => ha ⟨m, c, k, h1, h2, h3⟩) _ _
            simp only [Expr2.size] at hs
            rw [evalPure2_index, evalPure2_index,
              ihE a (by omega) (fun r h => hb r (hr ▸ List.mem_append_left _ h)),
              ihE idx (by omega) (fun r h => hb r (hr ▸ List.mem_append_right _ h))]
      | _ =>
          simp only [Expr2.size] at hs
          simp only [Expr2.reads, List.mem_append] at hb
          simp (disch := first | omega | (intro x hx; apply hb; simp [hx]))
            only [evalPure2, ihE, ihL]
    · cases es with
      | nil => rfl
      | cons e rest =>
          simp only [Expr2.listSize] at hs
          simp only [Expr2.listReads, List.mem_append] at hb
          simp (disch := first | omega | (intro x hx; apply hb; simp [hx]))
            only [evalPures2, ihE, ihL]

/-- **Frame (window granularity).** Two states agreeing on every read of `e`
— the whole binding for a whole read, width and window bits for a window read —
evaluate `e` identically. -/
theorem evalPure2_congr_reads {st st' : SvState} {e : Expr2}
    (h : ∀ r ∈ e.reads, r.agree st st') : evalPure2 st e = evalPure2 st' e :=
  (congr_reads_aux st st' (e.size + 1)).1 e (Nat.lt_succ_self _) h

/-- List twin of `evalPure2_congr_reads`. -/
theorem evalPures2_congr_reads {st st' : SvState} {es : List Expr2}
    (h : ∀ r ∈ Expr2.listReads es, r.agree st st') : evalPures2 st es = evalPures2 st' es :=
  (congr_reads_aux st st' (Expr2.listSize es + 1)).2 es (Nat.lt_succ_self _) h

/-! ## Multi-window writes -/

/-- Select-write the placed windows of a value into a state, in list order:
`((n, lo, w), off)` writes `val.extract off w` at bit `lo` of `n` (an unbound
name is skipped; on a shaped state every written name is bound). The pure
image of `writeConcatLhs2` (`writeConcatLhs2_eq`). -/
def SvState.writeWins (st : SvState) (val : LVec) : List (Win × Nat) → SvState
  | [] => st
  | (wn, off) :: rest =>
      SvState.writeWins
        (match SvState.lookup st wn.1 with
         | some old => SvState.set st wn.1 (old.insertAt wn.2.1 (val.extract off wn.2.2))
         | none => st)
        val rest

/-- **The state after one comb process** `t = e` whose right-hand side
evaluated to `v`: `v` resized to the target's total width, its slices written
MSB-first into the target's windows (`writeConcatLhs2`'s windows, offsets and
order; for a leaf target the single window write of `runCombProcess2`,
`combWrite_of_window?`). -/
def combWrite (d : Design2) (st : SvState) (t : Lhs2) (v : LVec) : SvState :=
  SvState.writeWins st (v.resizeU (Win.sumWidth (t.wins d))) (Win.placed (t.wins d))

namespace SvState

variable {val : LVec}

/-- `writeWins` on a cons cell whose name is bound. -/
theorem writeWins_cons_some {st : SvState} {n : String} {lo w off : Nat} {old : LVec}
    (h : lookup st n = some old) (rest : List (Win × Nat)) :
    writeWins st val (((n, lo, w), off) :: rest) =
      writeWins (set st n (old.insertAt lo (val.extract off w))) val rest := by
  simp only [writeWins, h]

/-- `writeWins` on a cons cell whose name is unbound skips it. -/
theorem writeWins_cons_none {st : SvState} {n : String} {lo w off : Nat}
    (h : lookup st n = none) (rest : List (Win × Nat)) :
    writeWins st val (((n, lo, w), off) :: rest) = writeWins st val rest := by
  simp only [writeWins, h]

/-- A select-write keeps every name bound, at its width. -/
theorem exists_lookup_set_insertAt {st : SvState} {n m : String} {old old' : LVec} {lo : Nat}
    {p : LVec} (h : lookup st n = some old) (hm : lookup st m = some old') :
    ∃ x, lookup (set st n (old.insertAt lo p)) m = some x ∧ x.width = old'.width := by
  by_cases hnm : n = m
  · subst hnm
    rw [h] at hm; cases hm
    exact ⟨_, lookup_set_self _ _ _, LVec.width_insertAt _ _ _⟩
  · exact ⟨old', by rw [lookup_set_ne _ _ hnm, hm], rfl⟩

/-- **Identity of a multi-window write**: if every window already holds its
part, writing them all changes nothing. -/
theorem writeWins_eq_self : ∀ {st : SvState} {pl : List (Win × Nat)},
    (∀ p ∈ pl, ∃ old, lookup st p.1.1 = some old ∧
      old.extract p.1.2.1 p.1.2.2 = val.extract p.2 p.1.2.2) →
    writeWins st val pl = st
  | _, [], _ => rfl
  | st, ((n, lo, w), off) :: rest, h => by
      obtain ⟨old, hold, hext⟩ := h _ (List.mem_cons_self ..)
      rw [writeWins_cons_some hold, LVec.insertAt_eq_self_of_extract hext, set_of_lookup hold]
      exact writeWins_eq_self fun p hp => h p (List.mem_cons_of_mem _ hp)

end SvState

/-- **Frame of a multi-window write**: a read that overlaps none of the
written windows sees the same thing before and after. -/
theorem ReadWin.agree_writeWins {val : LVec} {r : ReadWin} : ∀ {st : SvState}
    {pl : List (Win × Nat)}, (∀ p ∈ pl, r.overlaps p.1 = false) →
    r.agree st (SvState.writeWins st val pl)
  | _, [], _ => ReadWin.agree_refl _ _
  | st, ((n, lo, w), off) :: rest, h => by
      cases hl : SvState.lookup st n with
      | none =>
          rw [SvState.writeWins_cons_none hl]
          exact ReadWin.agree_writeWins fun p hp => h p (List.mem_cons_of_mem _ hp)
      | some old =>
          rw [SvState.writeWins_cons_some hl]
          exact ReadWin.agree_trans
            (ReadWin.agree_set hl (LVec.width_extract _ _ _) (h _ (List.mem_cons_self ..)))
            (ReadWin.agree_writeWins fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- A multi-window write keeps the shape. -/
theorem StateShape.writeWins {d : Design2} (val : LVec) : ∀ {st : SvState}
    {pl : List (Win × Nat)}, StateShape d st → StateShape d (SvState.writeWins st val pl)
  | _, [], hs => hs
  | st, ((n, lo, w), off) :: rest, hs => by
      cases hl : SvState.lookup st n with
      | none =>
          rw [SvState.writeWins_cons_none hl]
          exact StateShape.writeWins val hs
      | some old =>
          rw [SvState.writeWins_cons_some hl]
          exact StateShape.writeWins val (hs.set_insertAt hl lo _)

/-- **Read-back of a multi-window write.** With pairwise-disjoint windows,
each bound and in range, every window holds its part afterwards. -/
theorem SvState.writeWins_readBack {val : LVec} : ∀ {st : SvState} {pl : List (Win × Nat)},
    (pl.map Prod.fst).Pairwise (fun a b => Win.overlaps a b = false) →
    (∀ p ∈ pl, ∃ old, SvState.lookup st p.1.1 = some old ∧ p.1.2.1 + p.1.2.2 ≤ old.width) →
    ∀ (n : String) (lo w off : Nat), ((n, lo, w), off) ∈ pl →
      ∃ u, SvState.lookup (SvState.writeWins st val pl) n = some u ∧
        u.extract lo w = val.extract off w
  | _, [], _, _, _, _, _, _, h => absurd h List.not_mem_nil
  | st, ((n₀, lo₀, w₀), off₀) :: rest, hpw, hb, n, lo, w, off, hmem => by
      simp only [List.map_cons, List.pairwise_cons] at hpw
      obtain ⟨old₀, hold₀, hin₀⟩ := hb _ (List.mem_cons_self ..)
      rw [SvState.writeWins_cons_some hold₀]
      rcases List.mem_cons.mp hmem with h | h
      · -- the head window: written now, untouched by the (disjoint) rest
        simp only [Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
        have h1 := ReadWin.agree_writeWins (val := val) (r := .win n lo w)
          (st := SvState.set st n (old₀.insertAt lo (val.extract off w))) (pl := rest)
          fun p hp => hpw.1 p.1 (List.mem_map_of_mem hp)
        simp only [ReadWin.agree, SvState.lookup_set_self, Option.map_some] at h1
        cases hu : SvState.lookup
            (SvState.writeWins (SvState.set st n (old₀.insertAt lo (val.extract off w))) val rest)
            n with
        | none => rw [hu] at h1; cases h1
        | some u =>
            rw [hu] at h1
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
            exact ⟨u, rfl, h1.2.symm.trans
              (LVec.extract_insertAt_self (LVec.width_extract _ _ _) hin₀)⟩
      · refine SvState.writeWins_readBack hpw.2 (fun p hp => ?_) n lo w off h
        obtain ⟨o, ho, hr⟩ := hb p (List.mem_cons_of_mem _ hp)
        obtain ⟨x, hx, hxw⟩ := SvState.exists_lookup_set_insertAt hold₀ ho (lo := lo₀)
          (p := val.extract off₀ w₀)
        exact ⟨x, hx, hxw ▸ hr⟩

/-- One comb process keeps the shape. -/
theorem StateShape.combWrite {d : Design2} {st : SvState} (hs : StateShape d st) (t : Lhs2)
    (v : LVec) : StateShape d (combWrite d st t v) :=
  StateShape.writeWins _ hs

/-- **Frame of one comb process**: a read overlapping none of the target's
windows sees the same thing before and after. -/
theorem ReadWin.agree_combWrite {d : Design2} {st : SvState} {t : Lhs2} {v : LVec}
    {r : ReadWin} (h : ∀ wn ∈ t.wins d, r.overlaps wn = false) :
    r.agree st (combWrite d st t v) :=
  ReadWin.agree_writeWins fun p hp => h p.1 (Win.mem_of_mem_placed hp)

/-- Every placed window of a process target is bound and in range on a
shaped state. -/
theorem CombDesign.placed_bound {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) :
    ∀ p ∈ Win.placed (t.wins d), ∃ old, SvState.lookup st p.1.1 = some old ∧
      p.1.2.1 + p.1.2.2 ≤ old.width := by
  rintro ⟨⟨n, lo, w⟩, off⟩ hm
  obtain ⟨old, hold, hin, -⟩ := hd.lookup_writes hs ⟨t, e, hp, Win.mem_of_mem_placed hm⟩
  exact ⟨old, hold, hin⟩

/-- **Read-back of one comb process.** After the process `t = e` (value
`v`), every placed window of `t` holds its slice of `v` resized to the
target's total width. -/
theorem CombDesign.combWrite_readBack {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) (v : LVec) {n : String} {lo w off : Nat}
    (hm : ((n, lo, w), off) ∈ Win.placed (t.wins d)) :
    ∃ u, SvState.lookup (combWrite d st t v) n = some u ∧
      u.extract lo w = (v.resizeU (Win.sumWidth (t.wins d))).extract off w :=
  SvState.writeWins_readBack (by rw [Win.map_fst_placed]; exact hd.selfDisjoint i t e hp)
    (hd.placed_bound hs hp) n lo w off hm

/-- **Identity of one comb process**: if every placed window already holds
its slice, the process changes nothing. -/
theorem combWrite_eq_self {d : Design2} {st : SvState} {t : Lhs2} {v : LVec}
    (h : ∀ (n : String) (lo w off : Nat), ((n, lo, w), off) ∈ Win.placed (t.wins d) →
      ∃ old, SvState.lookup st n = some old ∧
        old.extract lo w = (v.resizeU (Win.sumWidth (t.wins d))).extract off w) :
    combWrite d st t v = st :=
  SvState.writeWins_eq_self fun ⟨⟨n, lo, w⟩, off⟩ hp => h n lo w off hp

/-- The full-width slice at bit 0 of a vector of that width is the vector. -/
theorem LVec.extract_zero_of_width {u : LVec} {w : Nat} (h : u.width = w) : u.extract 0 w = u := by
  apply LVec.ext_getD (by simp [h])
  intro i hi
  simp only [LVec.width_extract] at hi
  rw [LVec.getD_extract, if_pos hi, Nat.zero_add]

/-- **A leaf process writes its one window** with the whole resized value. -/
theorem combWrite_of_window? {d : Design2} {st : SvState} {t : Lhs2} {n : String} {lo w : Nat}
    (ht : t.window? d = some (n, lo, w)) {old : LVec} (hold : SvState.lookup st n = some old)
    (v : LVec) : combWrite d st t v = SvState.set st n (old.insertAt lo (v.resizeU w)) := by
  simp only [combWrite, Lhs2.wins_of_window? ht, Win.sumWidth_cons, Win.sumWidth_nil,
    Win.placed_cons, Win.placed_nil, Nat.add_zero, SvState.writeWins_cons_some hold,
    LVec.extract_zero_of_width (LVec.width_resizeU v w)]
  rfl

/-! ## Resolving and writing a concatenated target -/

/-- A leaf target with a static window resolves to it (on a state where the
signal is bound at its declared width and the window is in range, at
positive fuel — the literal index of an element select is evaluated). -/
theorem resolveLhs2_of_window? {d : Design2} {fuel : Nat} (hf : 0 < fuel) {st : SvState}
    {t : Lhs2} {n : String} {lo w : Nat} (ht : t.window? d = some (n, lo, w)) {old : LVec}
    (hold : SvState.lookup st n = some old) (hin : lo + w ≤ old.width)
    (hdw : d.declWidth n = some old.width) :
    resolveLhs2 fuel st t = .ok (n, some (lo, w)) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  cases t with
  | ident m =>
      simp only [Lhs2.window?, Option.map_eq_some_iff, Prod.mk.injEq] at ht
      obtain ⟨dw, hdw', rfl, rfl, rfl⟩ := ht
      rw [hdw] at hdw'; cases hdw'
      simp [resolveLhs2, hold]
  | slice m lo' w' =>
      simp only [Lhs2.window?, Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl, rfl⟩ := ht
      rfl
  | index m idx elemW =>
      cases idx with
      | lit c =>
          simp only [Lhs2.window?, Option.map_eq_some_iff, Prod.mk.injEq] at ht
          obtain ⟨k, hk, rfl, rfl, rfl⟩ := ht
          have hr : (k + 1) * elemW ≤ old.width := by rw [Nat.succ_mul]; omega
          have hlit : evalExpr2 (f + 1) st (.lit c) = .ok c := rfl
          simp [resolveLhs2, hold, hk, hr, hlit]
      | _ => simp [Lhs2.window?] at ht
  | concat parts => simp [Lhs2.window?] at ht

/-- A leaf target resolves, as a one-leaf concatenation, to its window. -/
private theorem resolveConcatLhs2_leaf {d : Design2} {fuel : Nat} (hf : 0 < fuel) {st : SvState}
    {t : Lhs2} (hnc : ∀ ps, t = .concat ps → False) {n : String} {lo w : Nat}
    (ht : t.window? d = some (n, lo, w)) {old : LVec} (hold : SvState.lookup st n = some old)
    (hin : lo + w ≤ old.width) (hdw : d.declWidth n = some old.width) :
    resolveConcatLhs2 fuel st t = .ok [(n, lo, w)] := by
  rw [resolveConcatLhs2.eq_2 fuel st t hnc, resolveLhs2_of_window? hf ht hold hin hdw]
  rfl

/-- The leaf case of `resolveConcatLhs2_of_windows?`. -/
private theorem resolveConcatLhs2_of_windows?_leaf {d : Design2} {fuel : Nat} (hf : 0 < fuel)
    {st : SvState} {t : Lhs2} (hnc : ∀ ps, t = .concat ps → False) {ws : List Win}
    (h : ((t.window? d).map ([·])) = some ws)
    (hb : ∀ n lo w, (n, lo, w) ∈ ws → ∃ old, SvState.lookup st n = some old ∧
      lo + w ≤ old.width ∧ d.declWidth n = some old.width) :
    resolveConcatLhs2 fuel st t = .ok ws := by
  obtain ⟨⟨n, lo, w⟩, ht, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨old, hold, hin, hdw⟩ := hb n lo w (List.mem_singleton_self _)
  exact resolveConcatLhs2_leaf hf hnc ht hold hin hdw

mutual

/-- **Static windows resolve.** On a state where every window of the target
is bound at its declared width and in range, `resolveConcatLhs2` (at positive
fuel) returns exactly the static windows `Lhs2.windows?`, in order. -/
theorem resolveConcatLhs2_of_windows? {d : Design2} {fuel : Nat} (hf : 0 < fuel)
    {st : SvState} : ∀ (t : Lhs2) (ws : List Win), t.windows? d = some ws →
      (∀ n lo w, (n, lo, w) ∈ ws → ∃ old, SvState.lookup st n = some old ∧
        lo + w ≤ old.width ∧ d.declWidth n = some old.width) →
      resolveConcatLhs2 fuel st t = .ok ws
  | .ident n, ws, h, hb =>
      resolveConcatLhs2_of_windows?_leaf hf (fun _ h => by cases h) h hb
  | .slice n lo w, ws, h, hb =>
      resolveConcatLhs2_of_windows?_leaf hf (fun _ h => by cases h) h hb
  | .index n idx elemW, ws, h, hb =>
      resolveConcatLhs2_of_windows?_leaf hf (fun _ h => by cases h) h hb
  | .concat parts, ws, h, hb => by
      rw [resolveConcatLhs2.eq_1]
      have := resolveConcatLhs2_list_of_windows? hf parts [] ws h hb
      rwa [List.nil_append] at this
termination_by structural t => t

/-- The part-list fold of `resolveConcatLhs2_of_windows?` (accumulator
generalized). -/
theorem resolveConcatLhs2_list_of_windows? {d : Design2} {fuel : Nat} (hf : 0 < fuel)
    {st : SvState} : ∀ (parts : List Lhs2) (acc ws : List Win),
      Lhs2.listWindows? d parts = some ws →
      (∀ n lo w, (n, lo, w) ∈ ws → ∃ old, SvState.lookup st n = some old ∧
        lo + w ≤ old.width ∧ d.declWidth n = some old.width) →
      parts.foldlM (fun acc part => do
          let windows ← resolveConcatLhs2 fuel st part
          pure (acc ++ windows)) acc = .ok (acc ++ ws)
  | [], acc, ws, h, _ => by
      simp only [Lhs2.listWindows?_nil, Option.some.injEq] at h
      subst h
      simp
  | t :: ts, acc, ws, h, hb => by
      obtain ⟨a, b, ha, hbs, rfl⟩ := Lhs2.listWindows?_cons_eq_some.mp h
      rw [List.foldlM_cons, resolveConcatLhs2_of_windows? hf t a ha
        (fun n lo w hm => hb n lo w (List.mem_append_left _ hm))]
      rw [Res.ok_bind]
      show List.foldlM _ (acc ++ a) ts = _
      rw [resolveConcatLhs2_list_of_windows? hf ts (acc ++ a) b hbs
        (fun n lo w hm => hb n lo w (List.mem_append_right _ hm)), List.append_assoc]
termination_by structural parts => parts

end

/-- The width total `writeConcatLhs2` folds is `Win.sumWidth`. -/
private theorem foldl_width_eq {f : Nat → Win → Nat} (hf : ∀ n x, f n x = n + x.2.2) :
    ∀ (ws : List Win) (acc : Nat), ws.foldl f acc = acc + Win.sumWidth ws
  | [], acc => by simp
  | x :: rest, acc => by
      rw [List.foldl_cons, foldl_width_eq hf rest, hf, Win.sumWidth_cons]
      omega

/-- `writeConcatLhs2`'s worker is `SvState.writeWins` of the placed windows
(every name bound). -/
private theorem writeConcatLhs2_go_eq (repl : LVec) : ∀ (s : SvState) (rem : List Win),
    (∀ wn ∈ rem, (SvState.lookup s wn.1).isSome) →
    writeConcatLhs2.go repl s rem (Win.sumWidth rem) =
      .ok (SvState.writeWins s repl (Win.placed rem))
  | _, [], _ => rfl
  | s, (n, lo, w) :: rest, hb => by
      obtain ⟨old, hold⟩ := Option.isSome_iff_exists.mp (hb _ (List.mem_cons_self ..))
      rw [writeConcatLhs2.go.eq_2, hold, Win.placed_cons, SvState.writeWins_cons_some hold]
      simp only [Win.sumWidth_cons, Nat.add_sub_cancel_left]
      refine writeConcatLhs2_go_eq repl _ rest fun wn hwn => ?_
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hb wn (List.mem_cons_of_mem _ hwn))
      obtain ⟨x, hx, -⟩ := SvState.exists_lookup_set_insertAt hold ho (lo := lo)
        (p := repl.extract (Win.sumWidth rest) w)
      simp [hx]

/-- **`writeConcatLhs2` is a multi-window write**: on a state binding every
window's name, it writes the value resized to the total width, slice by slice
at the `Win.placed` offsets. -/
theorem writeConcatLhs2_eq {st : SvState} {v : LVec} {ws : List Win}
    (hb : ∀ wn ∈ ws, (SvState.lookup st wn.1).isSome) :
    writeConcatLhs2 st v ws =
      .ok (SvState.writeWins st (v.resizeU (Win.sumWidth ws)) (Win.placed ws)) := by
  unfold writeConcatLhs2
  rw [foldl_width_eq (fun _ _ => rfl), Nat.zero_add]
  exact writeConcatLhs2_go_eq _ st ws hb

/-! ## One comb process -/

/-- Right-hand sides of a comb design evaluate (`.ok`) on shaped states. -/
theorem CombDesign.evalPure2_ok {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) : ∃ v, evalPure2 st e = .ok v :=
  evalPure2_ok_of_wf (hd.rhsFree i t e hp)
    (fun x hx => hs.lookup_of_mem (hd.rhsDeclared i t e hp x hx))

/-- **One comb process, from an evaluated right-hand side** (any target in
profile, leaf or concatenation): the run is `combWrite`. -/
private theorem runCombProcess2_assign_of_eval {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e))
    {fuel : Nat} (hfuel : 0 < fuel) {v : LVec} (he : evalExpr2 fuel st e = .ok v) :
    runCombProcess2 fuel st (.assign t e) = .ok (combWrite d st t v) := by
  have hws := hd.windows?_of_proc hp
  have hb : ∀ n lo w, (n, lo, w) ∈ t.wins d → ∃ old, SvState.lookup st n = some old ∧
      lo + w ≤ old.width ∧ d.declWidth n = some old.width :=
    fun n lo w hm => hd.lookup_writes hs ⟨t, e, hp, hm⟩
  cases t with
  | concat parts =>
      have hres := resolveConcatLhs2_of_windows? hfuel (.concat parts) _ hws hb
      have hwr := writeConcatLhs2_eq (st := st) (v := v) (ws := (Lhs2.concat parts).wins d)
        fun wn hwn => by
          obtain ⟨n, lo, w⟩ := wn
          obtain ⟨old, hold, -, -⟩ := hb n lo w hwn
          simp [hold]
      simp only [runCombProcess2, he, Res.ok_bind, hres, hwr]
      rfl
  | _ =>
      obtain ⟨⟨n, lo, w⟩, hw, -⟩ := Lhs2.window?_of_windows? (fun _ h => by cases h) hws
      obtain ⟨old, hold, hin, hdw⟩ := hd.lookup_writes hs (Design2.writes_of_window? hp hw)
      rw [combWrite_of_window? hw hold]
      have hr := resolveLhs2_of_window? hfuel hw hold hin hdw
      simp only [runCombProcess2, he, Res.ok_bind, hr, hold]

/-- **One comb process, forward** (any target in profile). On a shaped state,
with fuel above the right-hand side's size, an assign whose right-hand side
evaluates to `v` produces `combWrite d st t v`. -/
theorem runCombProcess2_assign_write {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) {fuel : Nat} (hf : e.size < fuel) {v : LVec}
    (hv : evalPure2 st e = .ok v) :
    runCombProcess2 fuel st (.assign t e) = .ok (combWrite d st t v) :=
  runCombProcess2_assign_of_eval hd hs hp (by omega) ((evalExpr2_eq_evalPure2 hf).trans hv)

/-- **One comb process, inversion** (any target in profile, any fuel). A
successful run of an assign on a shaped state is `combWrite` of the
fuel-free value of its right-hand side. -/
theorem runCombProcess2_assign_write_ok {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) {fuel : Nat} {st' : SvState}
    (h : runCombProcess2 fuel st (.assign t e) = .ok st') :
    ∃ v, evalPure2 st e = .ok v ∧ st' = combWrite d st t v := by
  have : ∃ v, evalExpr2 fuel st e = .ok v := by
    cases he : evalExpr2 fuel st e with
    | ok v => exact ⟨v, rfl⟩
    | timeout => simp [runCombProcess2, he] at h
    | unsupported msg => simp [runCombProcess2, he] at h
  obtain ⟨v, he⟩ := this
  have hfuel : 0 < fuel := by
    cases fuel with
    | zero => simp [evalExpr2] at he
    | succ => omega
  rw [runCombProcess2_assign_of_eval hd hs hp hfuel he] at h
  cases h
  exact ⟨v, evalPure2_of_evalExpr2_ok he, rfl⟩

/-- **One comb process, forward** (a leaf target). On a shaped state, with
fuel above the right-hand side's size, a windowed assign writes the resized
value into its window: `set st n (old.insertAt lo (v.resizeU w))`. -/
theorem runCombProcess2_assign_eq {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2} {n : String} {lo w : Nat}
    (hp : d.processes[i]? = some (.assign t e)) (hw : t.window? d = some (n, lo, w))
    {fuel : Nat} (hf : e.size < fuel) {old v : LVec}
    (hold : SvState.lookup st n = some old) (hv : evalPure2 st e = .ok v) :
    runCombProcess2 fuel st (.assign t e) =
      .ok (SvState.set st n (old.insertAt lo (v.resizeU w))) := by
  rw [runCombProcess2_assign_write hd hs hp hf hv, combWrite_of_window? hw hold]

/-- `runCombProcess2_assign_eq` with the old value and the right-hand side's
value produced (they exist on a shaped state). -/
theorem runCombProcess2_assign {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2} {n : String} {lo w : Nat}
    (hp : d.processes[i]? = some (.assign t e)) (hw : t.window? d = some (n, lo, w))
    {fuel : Nat} (hf : e.size < fuel) :
    ∃ old v, SvState.lookup st n = some old ∧ evalPure2 st e = .ok v ∧
      runCombProcess2 fuel st (.assign t e) =
        .ok (SvState.set st n (old.insertAt lo (v.resizeU w))) := by
  obtain ⟨old, hold, -, -⟩ := hd.lookup_writes hs (Design2.writes_of_window? hp hw)
  obtain ⟨v, hv⟩ := hd.evalPure2_ok hs hp
  exact ⟨old, v, hold, hv, runCombProcess2_assign_eq hd hs hp hw hf hold hv⟩

/-- **One comb process, inversion** (a leaf target, any fuel). A successful
run of a windowed assign on a shaped state is the window write of the
fuel-free value. -/
theorem runCombProcess2_assign_ok {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2} {n : String} {lo w : Nat}
    (hp : d.processes[i]? = some (.assign t e)) (hw : t.window? d = some (n, lo, w))
    {fuel : Nat} {st' : SvState} (h : runCombProcess2 fuel st (.assign t e) = .ok st') :
    ∃ old v, SvState.lookup st n = some old ∧ evalPure2 st e = .ok v ∧
      st' = SvState.set st n (old.insertAt lo (v.resizeU w)) := by
  obtain ⟨v, hv, rfl⟩ := runCombProcess2_assign_write_ok hd hs hp h
  obtain ⟨old, hold, -, -⟩ := hd.lookup_writes hs (Design2.writes_of_window? hp hw)
  exact ⟨old, v, hold, hv, combWrite_of_window? hw hold v⟩

/-- After a window write, the window holds the written part (in range by the
profile). -/
theorem CombDesign.extract_written {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {n : String} {lo w : Nat} (hW : d.Writes i (n, lo, w))
    {old : LVec} (hold : SvState.lookup st n = some old) {p : LVec} (hp : p.width = w) :
    SvState.lookup (SvState.set st n (old.insertAt lo p)) n = some (old.insertAt lo p) ∧
      (old.insertAt lo p).extract lo w = p := by
  obtain ⟨old', hold', hin, -⟩ := hd.lookup_writes hs hW
  rw [hold] at hold'; cases hold'
  exact ⟨SvState.lookup_set_self _ _ _, LVec.extract_insertAt_self hp hin⟩

/-! ## A comb pass -/

/-- The empty pass is the identity. -/
@[simp] theorem combPass2_nil (d : Design2) (fuel : Nat) (st : SvState) :
    combPass2 d fuel st [] = .ok st := rfl

/-- A pass step at an out-of-range index is skipped. -/
theorem combPass2_cons_none {d : Design2} {fuel : Nat} {st : SvState} {i : Nat}
    {is : List Nat} (h : d.processes[i]? = none) :
    combPass2 d fuel st (i :: is) = combPass2 d fuel st is := by
  simp [combPass2, h]

/-- A pass step at a process runs it, then the rest. -/
theorem combPass2_cons_some {d : Design2} {fuel : Nat} {st : SvState} {i : Nat}
    {is : List Nat} {p : Process2} (h : d.processes[i]? = some p) :
    combPass2 d fuel st (i :: is) =
      (runCombProcess2 fuel st p >>= fun st' => combPass2 d fuel st' is) := by
  simp [combPass2, h]

/-- A pass step at an assign, forward (any target in profile; fuel above the
rhs size): the head process's `combWrite`, then the rest. -/
theorem combPass2_cons_write {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) {fuel : Nat} (hf : e.size < fuel) {v : LVec}
    (hv : evalPure2 st e = .ok v) (is : List Nat) :
    combPass2 d fuel st (i :: is) = combPass2 d fuel (combWrite d st t v) is := by
  rw [combPass2_cons_some hp, runCombProcess2_assign_write hd hs hp hf hv]
  rfl

/-- A pass step at a windowed (leaf-target) assign, forward (fuel above the
rhs size). -/
theorem combPass2_cons_assign {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2} {n : String} {lo w : Nat}
    (hp : d.processes[i]? = some (.assign t e)) (hw : t.window? d = some (n, lo, w))
    {fuel : Nat} (hf : e.size < fuel) {old v : LVec}
    (hold : SvState.lookup st n = some old) (hv : evalPure2 st e = .ok v) (is : List Nat) :
    combPass2 d fuel st (i :: is) =
      combPass2 d fuel (SvState.set st n (old.insertAt lo (v.resizeU w))) is := by
  rw [combPass2_cons_write hd hs hp hf hv, combWrite_of_window? hw hold]

/-- **Pass step inversion** (any fuel): a successful pass from a shaped state
either skipped an out-of-range index or ran the head process — an assign
whose right-hand side evaluated to `v` — as `combWrite`. -/
theorem combPass2_cons_ok {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {fuel : Nat} {i : Nat} {is : List Nat} {st' : SvState}
    (h : combPass2 d fuel st (i :: is) = .ok st') :
    (d.processes[i]? = none ∧ combPass2 d fuel st is = .ok st') ∨
    ∃ t e v, d.processes[i]? = some (.assign t e) ∧ evalPure2 st e = .ok v ∧
      combPass2 d fuel (combWrite d st t v) is = .ok st' := by
  cases hpi : d.processes[i]? with
  | none => exact Or.inl ⟨rfl, by rw [combPass2_cons_none hpi] at h; exact h⟩
  | some p =>
      right
      obtain ⟨t, e, ws, rfl, -⟩ := hd.assign i p hpi
      rw [combPass2_cons_some hpi] at h
      obtain ⟨s1, h1, h2⟩ := Res.bind_eq_ok.mp h
      obtain ⟨v, hv, rfl⟩ := runCombProcess2_assign_write_ok hd hs hpi h1
      exact ⟨t, e, v, rfl, hv, h2⟩

/-- **Frame of a pass.** A successful pass (any fuel, any index list) from a
shaped state ends in a shaped state, and every read that overlaps no window of
a listed process sees the same thing before and after. -/
theorem combPass2_frame {d : Design2} (hd : CombDesign d) {fuel : Nat} :
    ∀ {is : List Nat} {st st' : SvState}, StateShape d st → combPass2 d fuel st is = .ok st' →
      StateShape d st' ∧
      ∀ r : ReadWin, (∀ i ∈ is, ∀ wn, d.Writes i wn → r.overlaps wn = false) → r.agree st st'
  | [], st, st', hs, h => by
      cases h
      exact ⟨hs, fun r _ => ReadWin.agree_refl _ r⟩
  | i :: is, st, st', hs, h => by
      rcases combPass2_cons_ok hd hs h with ⟨-, h⟩ | ⟨t, e, v, hp, hv, h⟩
      · obtain ⟨hs', hagree⟩ := combPass2_frame hd hs h
        exact ⟨hs', fun r hr => hagree r (fun j hj => hr j (List.mem_cons_of_mem _ hj))⟩
      · obtain ⟨hs', hagree⟩ := combPass2_frame hd (hs.combWrite t v) h
        refine ⟨hs', fun r hr => ?_⟩
        have h1 : r.agree st (combWrite d st t v) :=
          ReadWin.agree_combWrite fun wn hwn => hr i (List.mem_cons_self ..) wn ⟨t, e, hp, hwn⟩
        exact ReadWin.agree_trans h1
          (hagree r (fun j hj => hr j (List.mem_cons_of_mem _ hj)))

/-- A pass never touches an undriven signal. -/
theorem combPass2_notDriven {d : Design2} (hd : CombDesign d) {fuel : Nat} {is : List Nat}
    {st st' : SvState} (hs : StateShape d st) (h : combPass2 d fuel st is = .ok st')
    {n : String} (hn : NotDriven d n) : SvState.lookup st' n = SvState.lookup st n := by
  have := (combPass2_frame hd hs h).2 (.whole n) (fun i _ wn hW => by
    obtain ⟨m, lo, w⟩ := wn
    have hnm : n ≠ m := fun hnm => hn ⟨i, lo, w, hnm ▸ hW⟩
    simp [ReadWin.overlaps, hnm])
  exact this.symm

/-- A pass keeps the key list. -/
theorem combPass2_keys {d : Design2} (hd : CombDesign d) {fuel : Nat} {is : List Nat}
    {st st' : SvState} (hs : StateShape d st) (h : combPass2 d fuel st is = .ok st') :
    st'.map Prod.fst = st.map Prod.fst :=
  (combPass2_frame hd hs h).1.keys.trans hs.keys.symm

/-- Widths never change in a pass (`insertAt` is width-preserving). -/
theorem combPass2_width {d : Design2} (hd : CombDesign d) {fuel : Nat} {is : List Nat}
    {st st' : SvState} (hs : StateShape d st) (h : combPass2 d fuel st is = .ok st') (n : String) :
    (SvState.lookup st n).map LVec.width = (SvState.lookup st' n).map LVec.width := by
  -- the zero-width read at bit 0 sees only the width, and overlaps no write
  -- window (`Win.overlaps` would need a window starting below bit 0)
  have := (combPass2_frame hd hs h).2 (.win n 0 0) (fun _ _ wn _ => by
    obtain ⟨m, lo, w⟩ := wn
    simp [ReadWin.overlaps, Win.overlaps])
  simp only [ReadWin.agree] at this
  have h' := congrArg (Option.map Prod.fst) this
  simpa [Option.map_map, Function.comp_def] using h'

/-- **A pass completes** at any fuel above every right-hand side's size. -/
theorem combPass2_ok {d : Design2} (hd : CombDesign d) {fuel : Nat}
    (hf : ∀ (i : Nat) (t : Lhs2) (e : Expr2), d.processes[i]? = some (.assign t e) →
      e.size < fuel) :
    ∀ (is : List Nat) {st : SvState}, StateShape d st → ∃ st', combPass2 d fuel st is = .ok st'
  | [], st, _ => ⟨st, rfl⟩
  | i :: is, st, hs => by
      cases hpi : d.processes[i]? with
      | none =>
          rw [combPass2_cons_none hpi]
          exact combPass2_ok hd hf is hs
      | some p =>
          obtain ⟨t, e, ws, rfl, -⟩ := hd.assign i p hpi
          obtain ⟨v, hv⟩ := hd.evalPure2_ok hs hpi
          rw [combPass2_cons_write hd hs hpi (hf i t e hpi) hv]
          exact combPass2_ok hd hf is (hs.combWrite t v)

/-! ## Fuel for every right-hand side -/

/-- Size of a process's right-hand side (`0` off-profile). -/
def Process2.rhsSize : Process2 → Nat
  | .assign _ e => e.size
  | _ => 0

/-- Expression fuel sufficient for every right-hand side of the design
(`Design2.size_lt_combFuel`). -/
def Design2.combFuel (d : Design2) : Nat :=
  (d.processes.toList.map Process2.rhsSize).foldr max 0 + 1

private theorem le_foldr_max {x : Nat} : ∀ {l : List Nat}, x ∈ l → x ≤ l.foldr max 0
  | a :: l, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

/-- Every right-hand side is smaller than `Design2.combFuel`. -/
theorem Design2.size_lt_combFuel {d : Design2} {i : Nat} {t : Lhs2} {e : Expr2}
    (h : d.processes[i]? = some (.assign t e)) : e.size < d.combFuel := by
  have hmem : Process2.assign t e ∈ d.processes.toList :=
    List.mem_iff_getElem?.mpr ⟨i, by rw [Array.getElem?_toList]; exact h⟩
  have := le_foldr_max (l := d.processes.toList.map Process2.rhsSize)
    (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  simp only [Process2.rhsSize] at this
  simp only [Design2.combFuel]
  omega

/-- **A pass completes** at any fuel from `Design2.combFuel` on. -/
theorem combPass2_ok_of_combFuel {d : Design2} (hd : CombDesign d) {fuel : Nat}
    (hf : d.combFuel ≤ fuel) (is : List Nat) {st : SvState} (hs : StateShape d st) :
    ∃ st', combPass2 d fuel st is = .ok st' :=
  combPass2_ok hd (fun _ _ _ hp => Nat.lt_of_lt_of_le (Design2.size_lt_combFuel hp) hf) is hs

/-! ## The comb-only cycle -/

/-- `initState2` binds each declared name to its initializer (else all-x), the
value then squashed to 2-state for a 2-state declaration. -/
theorem lookup_initState2 (d : Design2) (n : String) :
    SvState.lookup (initState2 d) n =
      (d.decls.toList.find? fun dc => dc.name == n).map
        fun dc => if dc.twoState then (dc.init.getD (LVec.xVec dc.width)).toTwoState
          else dc.init.getD (LVec.xVec dc.width) := by
  unfold initState2
  generalize d.decls.toList = ds
  induction ds with
  | nil => rfl
  | cons dc rest ih =>
      simp only [List.map_cons, SvState.lookup_cons, List.find?_cons, ih]
      by_cases h : dc.name = n
      · simp [h]
      · have hb : (dc.name == n) = false := by simpa using h
        simp [h, hb]

/-- The startup state has the comb shape. -/
theorem StateShape.of_initState2 {d : Design2} (hd : CombDesign d) :
    StateShape d (LeanModels.Sv.initState2 d) := by
  refine ⟨by simp [LeanModels.Sv.initState2], ?_⟩
  intro n hn
  obtain ⟨i, lo, w, hW⟩ := hn
  obtain ⟨dw, hdw, -⟩ := hd.inWidth i n lo w hW
  obtain ⟨dc, hf, rfl⟩ := Design2.declWidth_eq_some_iff.mp hdw
  have hname : dc.name = n := by simpa using List.find?_some hf
  have hmem := List.mem_of_find?_eq_some hf
  have hw0 : (dc.init.getD (LVec.xVec dc.width)).width = dc.width := by
    cases hi : dc.init with
    | none => simp
    | some v => simp [hd.initWidth n ⟨i, lo, w, hW⟩ dc hmem hname v hi]
  refine ⟨if dc.twoState then (dc.init.getD (LVec.xVec dc.width)).toTwoState
      else dc.init.getD (LVec.xVec dc.width), by rw [lookup_initState2, hf]; rfl, ?_⟩
  rw [hdw]
  by_cases h2 : dc.twoState = true
  · simp [h2, LVec.toTwoState, LVec.width] at hw0 ⊢
    exact hw0.symm
  · simp [h2, hw0]

/-- Input names are declared names. -/
theorem Design2.mem_names_of_mem_inputNames {d : Design2} {n : String}
    (h : n ∈ d.inputNames.toList) : n ∈ d.decls.toList.map Decl.name := by
  simp only [Design2.inputNames, Array.toList_filterMap, List.mem_filterMap] at h
  obtain ⟨dc, hdc, hf⟩ := h
  split at hf
  · cases hf; exact List.mem_map.mpr ⟨dc, hdc, rfl⟩
  · cases hf

/-- On a design whose input declarations are all 4-state, `applyInputs2` is
the plain walk over the input names (the stimulus value stored verbatim): the
squash of a 2-state input is the only difference from the pre-2-state
definition. -/
theorem applyInputs2_eq_names (d : Design2) (inputs st : SvState)
    (h4 : ∀ dc ∈ d.decls.toList, dc.isInput = true → dc.twoState = false) :
    applyInputs2 d inputs st =
      d.inputNames.toList.foldl
        (fun s name => match SvState.lookup inputs name with
          | some v => SvState.set s name v
          | none => s) st := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  simp only [Design2.inputNames, Array.toList_filterMap]
  generalize d.decls.toList = ds at h4 ⊢
  induction ds generalizing st with
  | nil => rfl
  | cons dc rest ih =>
      have ih' := fun st' => ih st' (fun x hx => h4 x (List.mem_cons_of_mem _ hx))
      cases hin : dc.isInput with
      | false => simp [List.foldl_cons, List.filterMap_cons, hin, ih']
      | true =>
          have h2 : dc.twoState = false := h4 dc (List.mem_cons_self ..) hin
          simp only [List.foldl_cons, List.filterMap_cons, hin, h2, if_true, Bool.false_eq_true,
            if_false]
          exact ih' _

/-- What `applyInputs2` does to one name: an input takes the stimulus value
if the stimulus has one; every other binding is held. (4-state inputs: the
profile field `CombDesign.inFourState`.) -/
theorem lookup_applyInputs2 (d : Design2) (inputs st : SvState) (n : String)
    (h4 : ∀ dc ∈ d.decls.toList, dc.isInput = true → dc.twoState = false) :
    SvState.lookup (applyInputs2 d inputs st) n =
      if n ∈ d.inputNames.toList then (SvState.lookup inputs n).or (SvState.lookup st n)
      else SvState.lookup st n := by
  rw [applyInputs2_eq_names d inputs st h4]
  generalize d.inputNames.toList = names
  induction names generalizing st with
  | nil => simp
  | cons m ms ih =>
      rw [List.foldl_cons, ih]
      cases hm : SvState.lookup inputs m with
      | none =>
          by_cases hmn : m = n
          · subst hmn; simp [hm]
          · simp [Ne.symm hmn]
      | some v =>
          by_cases hmn : m = n
          · subst hmn; simp [hm, SvState.lookup_set_self]
          · simp [Ne.symm hmn, SvState.lookup_set_ne _ _ hmn]

/-- `applyInputs2` keeps the key list when every input name is a key. -/
theorem keys_applyInputs2 (d : Design2) (inputs : SvState) {st : SvState}
    (h4 : ∀ dc ∈ d.decls.toList, dc.isInput = true → dc.twoState = false)
    (h : ∀ n ∈ d.inputNames.toList, n ∈ st.map Prod.fst) :
    (applyInputs2 d inputs st).map Prod.fst = st.map Prod.fst := by
  rw [applyInputs2_eq_names d inputs st h4]
  generalize d.inputNames.toList = names at h
  induction names generalizing st with
  | nil => rfl
  | cons m ms ih =>
      rw [List.foldl_cons]
      have hm := h m (List.mem_cons_self ..)
      cases hv : SvState.lookup inputs m with
      | none =>
          exact ih (fun n hn => h n (List.mem_cons_of_mem _ hn))
      | some v =>
          simp only
          rw [ih (fun n hn => by
              rw [SvState.keys_set _ hm]; exact h n (List.mem_cons_of_mem _ hn)),
            SvState.keys_set _ hm]

/-- Input ports are undriven. -/
theorem CombDesign.notDriven_of_input {d : Design2} (hd : CombDesign d) {n : String}
    (h : n ∈ d.inputNames.toList) : NotDriven d n :=
  fun hD => hd.notInput n hD h

/-- `applyInputs2` never touches a driven signal. -/
theorem CombDesign.lookup_applyInputs2_driven {d : Design2} (hd : CombDesign d)
    (inputs st : SvState) {n : String} (hn : Driven d n) :
    SvState.lookup (applyInputs2 d inputs st) n = SvState.lookup st n := by
  rw [lookup_applyInputs2 d inputs st n hd.inFourState, if_neg (hd.notInput n hn)]

/-- `applyInputs2` keeps the comb shape. -/
theorem StateShape.of_applyInputs2 {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) (inputs : SvState) :
    StateShape d (LeanModels.Sv.applyInputs2 d inputs st) := by
  refine ⟨?_, ?_⟩
  · rw [keys_applyInputs2 d inputs hd.inFourState
      (fun n hn => hs.keys ▸ Design2.mem_names_of_mem_inputNames hn), hs.keys]
  · intro n hn
    rw [hd.lookup_applyInputs2_driven inputs st hn]
    exact hs.driven n hn

/-- **The comb-only cycle**: no reset event, no edge process, an empty NBA
queue — a cycle is the input settle followed by the post-edge settle. -/
theorem cycleStep2_of_comb {d : Design2} (hd : CombDesign d) (σ : ScheduleOracle) (fuel : Nat)
    (inputs st : SvState) (k : Nat) :
    cycleStep2 d σ fuel inputs st k =
      (combSettle2 d σ fuel (LeanModels.Sv.applyInputs2 d inputs st) k >>=
        fun p => combSettle2 d σ fuel p.1 (p.2 + 1)) := by
  unfold cycleStep2
  simp only [hd.resetIndices_eq, hd.edgeIndices_eq, ScheduleOracle.choose_nil]
  cases combSettle2 d σ fuel (LeanModels.Sv.applyInputs2 d inputs st) k with
  | ok p => obtain ⟨st1, k1⟩ := p; rfl
  | timeout => rfl
  | unsupported msg => rfl

/-! ## Smoke test: a hand-built full adder is in the profile

`faDesign` is a full adder (`s = a ^ b ^ ci`, `co = (a & b) | (ci & (a ^ b))`)
plus a 2-bit bus `y` driven by one slice target (`y[1] = co`) and one
constant-index target (`y[0] = s`, the `index … (lit 0) 1` shape) — every
target kind of the profile. `fa_comb`/`fa_acyclic` prove the profile and the
certificate (explicit rank: the adder gates 0, the bus 1); the `#guard`s run
it through `run2` under two schedules.

These are SHARED smoke fixtures, public on purpose: `faDesign`, `fa_proc`,
`fa_writes`, `fa_driven`, `fa_comb` and `fa_acyclic` are consumed by the smoke
sections of `Comb2Sound.lean`, `Comb2Term.lean` and `Comb2.lean`, and by the
end-to-end example `Comb2Example.lean`. -/

namespace Comb2Smoke

/-- The full adder with a 2-bit bus. -/
def faDesign : Design2 where
  name := "fa"
  decls := #[
    { name := "a", width := 1, isInput := true },
    { name := "b", width := 1, isInput := true },
    { name := "ci", width := 1, isInput := true },
    { name := "s", width := 1, isOutput := true },
    { name := "co", width := 1, isOutput := true },
    { name := "y", width := 2, isOutput := true }]
  processes := #[
    .assign (.ident "s") (.binary .xor (.binary .xor (.ident "a") (.ident "b")) (.ident "ci")),
    .assign (.ident "co") (.binary .or (.binary .and (.ident "a") (.ident "b"))
      (.binary .and (.ident "ci") (.binary .xor (.ident "a") (.ident "b")))),
    .assign (.slice "y" 1 1) (.ident "co"),
    .assign (.index "y" (.lit (LVec.ofNat 1 0)) 1) (.ident "s")]

/-- The process table, as a disjunction. -/
theorem fa_proc {i : Nat} {p : Process2} : faDesign.processes[i]? = some p ↔
    (i = 0 ∧ p = .assign (.ident "s")
      (.binary .xor (.binary .xor (.ident "a") (.ident "b")) (.ident "ci"))) ∨
    (i = 1 ∧ p = .assign (.ident "co") (.binary .or (.binary .and (.ident "a") (.ident "b"))
      (.binary .and (.ident "ci") (.binary .xor (.ident "a") (.ident "b"))))) ∨
    (i = 2 ∧ p = .assign (.slice "y" 1 1) (.ident "co")) ∨
    (i = 3 ∧ p = .assign (.index "y" (.lit (LVec.ofNat 1 0)) 1) (.ident "s")) := by
  match i with
  | 0 | 1 | 2 | 3 => simp [faDesign, eq_comm]
  | i + 4 => simp [faDesign]

/-- The write windows. -/
theorem fa_writes {i : Nat} {wn : Win} : faDesign.Writes i wn ↔
    (i = 0 ∧ wn = ("s", 0, 1)) ∨ (i = 1 ∧ wn = ("co", 0, 1)) ∨
    (i = 2 ∧ wn = ("y", 1, 1)) ∨ (i = 3 ∧ wn = ("y", 0, 1)) := by
  have h0 : (LVec.ofNat 1 0).toNat? = some 0 := by rw [LVec.toNat?_ofNat]
  constructor
  · rintro ⟨t, e, hp, hw⟩
    rcases fa_proc.mp hp with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      simp only [Process2.assign.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      simp [Design2.declWidth, faDesign, h0] at hw <;> simp [hw]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      exact ⟨_, _, rfl, by simp [Design2.declWidth, faDesign, h0]⟩

/-- The driven signals. -/
theorem fa_driven {n : String} : Driven faDesign n ↔ n = "s" ∨ n = "co" ∨ n = "y" := by
  constructor
  · rintro ⟨i, lo, w, h⟩
    rcases fa_writes.mp h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Prod.mk.injEq] at h <;> simp [h.1]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, 0, 1, fa_writes.mpr (by simp)⟩
    · exact ⟨1, 0, 1, fa_writes.mpr (by simp)⟩
    · exact ⟨2, 1, 1, fa_writes.mpr (by simp)⟩

/-- **Satisfiability of the profile.** -/
theorem fa_comb : CombDesign faDesign where
  nodup := by decide
  assign := by
    intro i p hp
    have hW : ∃ wn, faDesign.Writes i wn := by
      rcases fa_proc.mp hp with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨_, fa_writes.mpr (Or.inl ⟨rfl, rfl⟩)⟩
      · exact ⟨_, fa_writes.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · exact ⟨_, fa_writes.mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
      · exact ⟨_, fa_writes.mpr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    obtain ⟨wn, t, e, h1, h2⟩ := hW
    rw [hp] at h1; cases h1
    obtain ⟨ws, hws⟩ := Lhs2.exists_windows?_of_mem_wins h2
    exact ⟨t, e, ws, rfl, hws⟩
  inWidth := by
    intro i n lo w h
    rcases fa_writes.mp h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;>
      simp [Design2.declWidth, faDesign]
  notInput := by
    intro n hn
    rcases fa_driven.mp hn with rfl | rfl | rfl <;> simp [Design2.inputNames, faDesign]
  disjoint := by
    intro i j wi wj hij hi hj
    rcases fa_writes.mp hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases fa_writes.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact absurd rfl hij | decide
  selfDisjoint := by
    intro i t e hp
    rcases fa_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Process2.assign.injEq] at h <;> obtain ⟨rfl, -⟩ := h <;>
      exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro i t e hp
    rcases fa_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Process2.assign.injEq] at h <;> obtain ⟨-, rfl⟩ := h <;> rfl
  rhsDeclared := by
    intro i t e hp
    rcases fa_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Process2.assign.injEq] at h <;> obtain ⟨-, rfl⟩ := h <;>
      simp [Expr2.idents, faDesign]
  initWidth := by
    intro n _ dc hdc _ v hv
    simp [faDesign] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    simp [faDesign] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **Satisfiability of the certificate**: rank 0 for the adder gates (they
read only inputs), rank 1 for the bus (it reads `s`/`co`). -/
theorem fa_acyclic : Acyclic faDesign := by
  refine ⟨fun i => if i < 2 then 0 else 1, ?_⟩
  intro i j ti ei tj ej wj hi hj hw hex
  have hWj := fa_writes.mp ⟨tj, ej, hj, hw⟩
  rcases fa_proc.mp hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    simp only [Process2.assign.injEq] at h <;> obtain ⟨-, rfl⟩ := h <;>
    rcases hWj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | decide | exact absurd hex (by decide)

/-- The startup state has the comb shape (through the general lemma). -/
example : StateShape faDesign (initState2 faDesign) := StateShape.of_initState2 fa_comb

/-- Every comb pass order is a permutation of the four processes. -/
example (σ : ScheduleOracle) (k : Nat) :
    (σ.choose k faDesign.combIndices).Perm (List.range 4) :=
  fa_comb.choose_perm_range σ k

private def faStim : List SvState :=
  [[("a", .lit "1"), ("b", .lit "1"), ("ci", .lit "0")],
   [("a", .lit "1"), ("b", .lit "0"), ("ci", .lit "1")],
   [("a", .lit "0"), ("b", .lit "0"), ("ci", .lit "1")]]

private def faView (st : SvState) : String × String × String :=
  (SvState.showSignal st "s", SvState.showSignal st "co", SvState.showSignal st "y")

#guard (run2 faDesign σ_src 64 faStim).toOption.map (·.map faView) ==
  some [("0", "1", "10"), ("0", "1", "10"), ("1", "0", "01")]
#guard (run2 faDesign σ_rev 64 faStim).toOption.map (·.map faView) ==
  some [("0", "1", "10"), ("0", "1", "10"), ("1", "0", "01")]

end Comb2Smoke

end LeanModels.Sv
