import LeanModels.Sv.CombGuard2
import LeanModels.Sv.Obs

/-!
# The self-read guard is sound: an admitted body is its own fixpoint (WP4)

`CombGuard2.lean` refuses an `always_comb` body when some path through it
reads a bit before writing it and writes it later. This file proves the
guard's justification: **a body the guard admits is idempotent** — running
it on the state its own run produced changes nothing
(`execStmt2_idem_of_admits`; at the process level
`runCombProcess2_alwaysComb_idem_of_admits`), on shaped states
(`CombGuard.Shaped`: no duplicate signal names, every signal at its declared
width). This generalizes `runCombProcess2_alwaysComb_idem` (`Comb2Proc.lean`)
from the stricter `SymState.selfReadFree` profile — which refuses latches and
needs a symbolically executable body — to every body the guard admits:
latches that hold or read their own value, run-time index reads and writes,
procedural concatenation targets, `case … inside`, nonblocking assignments.

**What it means.** `combSettle2` re-runs every comb-phase process until the
state stops changing; an event-driven simulator runs an `always_comb` block
once per wake-up, and the block's own writes never wake it (IEEE 1800-2023
§9.2.2.2.1). On an admitted body the one run IS the fixpoint: re-running it
is the identity, so the settle loop's re-runs of the block itself change
nothing, and the value the simulator's single run leaves is the value the
settle semantics settles the block to. Across blocks, a simulator re-runs
a block when another process changes a variable it reads, as the settle
loop does (measured: Xcelium 24.03, Verilator 5.042). Icarus 12.0 differs
in two measured cases, both outside this theorem (which is about one block
re-run on its own result) and declared on `harness/sv/cases2.json` rows
(`docs/sv-oracle-disagreements.md`; corrected round 4 from measurements):
(1) on a pure continuous copy of a variable the block writes
(`assign w = t;`, `wire [1:0] w = t;`, or a port loop — a child's input and
output port connected to one parent variable) the copy STAYS in the
block's sensitivity list, but Icarus propagates its update synchronously
inside the block's run, before the block reaches its event control, so
the wake-up is lost; IEEE 1800-2023 §4.7/§4.8 permit that interleaving, so
this is a tool split, not a departure (rows `acg_alias_assign`,
`acg_alias_port`); (2) on a variable whose other bits another process
writes (a legal bit split, §9.2.2.2), Icarus leaves the whole variable out
of the list, against §9.2.2.2.1 (row `acg_xproc_bits`).

## The proof

Fix the first run `st ⟶ r` and run the body again from `r`. Along the
(common) path, the second run's state `τ` relates to the first run's state
`σ` at the same point by `Inv M r τ σ`: every bit of `τ` equals `σ`'s, or —
only for a bit outside `M`, the bits the path must have written so far —
equals the FINAL state `r`'s. A bit outside `M` that the rest of the run may
write is exactly what the guard forbids the body to read, and a bit the rest
of the run does not write already holds its final value (`Frame`), so every
read of the second run sees the first run's value (`agree_of_viol`), both
runs take the same branches and write the same values to the same windows
(`eval_congr`, `resolveLhs2_congr`, `resolveConcatLhs2_congr`, `go_rel`),
and at the end of the body `Inv` says `τ` and `r` agree on every bit. The
induction is ONE fuel induction over `execStmt2`/`execCase2`/`execStmts2`
(`sim`), which also returns the first run's frame (`Frame`: only bits the
statement may write change), so no separate frame induction is needed.

The first run's own frame is obtained from `sim` itself, run with the
second state equal to the first (`τ := σ`, `F := σ'`): `Inv` and the final
state hypothesis are then trivial.

The theorem covers the whole statement language of the tier — blocking and
nonblocking assignments, whole-signal, constant-slice, run-time-index and
concatenated targets, `if`, `case`/`case … inside`, `begin … end` — so it
applies to every body `Stmt2.combAdmits` accepts, not only to the fragment
`Comb2Proc.lean` lowers symbolically.
-/

namespace LeanModels.Sv

open CombGuard

namespace CombGuard

/-! ## Window algebra -/

theorem inSet_append {X Y : List BWin} {n : String} {i : Nat} :
    InSet (X ++ Y) n i ↔ InSet X n i ∨ InSet Y n i := by
  simp only [InSet, List.mem_append]
  constructor
  · rintro ⟨W, hW | hW, hm⟩
    · exact Or.inl ⟨W, hW, hm⟩
    · exact Or.inr ⟨W, hW, hm⟩
  · rintro (⟨W, hW, hm⟩ | ⟨W, hW, hm⟩)
    · exact ⟨W, Or.inl hW, hm⟩
    · exact ⟨W, Or.inr hW, hm⟩

theorem inSet_cons {W : BWin} {L : List BWin} {n : String} {i : Nat} :
    InSet (W :: L) n i ↔ W.Mem n i ∨ InSet L n i := by
  simp [InSet]

@[simp] theorem inSet_nil {n : String} {i : Nat} : ¬ InSet [] n i := by
  simp [InSet]

theorem inSet_singleton {W : BWin} {n : String} {i : Nat} : InSet [W] n i ↔ W.Mem n i := by
  simp [InSet]

theorem BWin.mem_inter {a b : BWin} {n : String} {i : Nat} :
    (a.inter b).Mem n i ↔ a.Mem n i ∧ b.Mem n i := by
  obtain ⟨an, al, aw⟩ := a
  obtain ⟨bn, bl, bw⟩ := b
  simp only [BWin.inter, BWin.Mem]
  by_cases h : an = bn
  · subst h
    by_cases hn : an = n
    · subst hn; simp only [if_true, true_and]; omega
    · simp [hn]
  · simp only [h, if_false]
    constructor
    · intro ⟨_, h1, h2⟩; omega
    · rintro ⟨⟨h1, _⟩, ⟨h2, _⟩⟩; exact absurd (h1.trans h2.symm) h

theorem BWin.mem_sub {a b : BWin} {n : String} {i : Nat} :
    (∃ p ∈ a.sub b, p.Mem n i) ↔ a.Mem n i ∧ ¬ b.Mem n i := by
  obtain ⟨an, al, aw⟩ := a
  obtain ⟨bn, bl, bw⟩ := b
  simp only [BWin.sub, BWin.Mem]
  by_cases h : an = bn
  · subst h
    by_cases hn : an = n
    · subst hn
      simp only [if_true, true_and, List.mem_append]
      constructor
      · rintro ⟨p, hp, hp1, hp2, hp3⟩
        rcases hp with hp | hp <;> split at hp <;> simp at hp <;> subst hp <;>
          simp at hp1 hp2 hp3 ⊢ <;> omega
      · rintro ⟨⟨h1, h2⟩, h3⟩
        by_cases hi : i < bl
        · refine ⟨(an, al, min (al + aw) bl - al), Or.inl ?_, rfl, ?_, ?_⟩
          · rw [if_pos (by omega)]; simp
          · dsimp only; omega
          · dsimp only; omega
        · refine ⟨(an, max al (bl + bw), al + aw - max al (bl + bw)), Or.inr ?_, rfl, ?_, ?_⟩
          · rw [if_pos (by omega)]; simp
          · dsimp only; omega
          · dsimp only; omega
    · simp only [if_true, List.mem_append]
      constructor
      · rintro ⟨p, hp, hp1, -, -⟩
        rcases hp with hp | hp <;> split at hp <;> simp at hp <;> subst hp <;> exact absurd hp1 hn
      · rintro ⟨⟨h1, -⟩, -⟩; exact absurd h1 hn
  · simp only [h, if_false]
    by_cases hw : aw = 0
    · simp only [hw, if_true, List.not_mem_nil, false_and, exists_false, false_iff]
      omega
    · simp only [hw, if_false, List.mem_singleton, exists_eq_left]
      constructor
      · intro hm; exact ⟨hm, fun ⟨h2, _⟩ => h (hm.1.trans h2.symm)⟩
      · exact fun hm => hm.1

theorem BWin.mem_subAll : ∀ (bs : List BWin) (a : BWin) {n : String} {i : Nat},
    (∃ p ∈ a.subAll bs, p.Mem n i) ↔ a.Mem n i ∧ ¬ InSet bs n i
  | [], a, n, i => by
      obtain ⟨an, al, aw⟩ := a
      by_cases hw : aw = 0
      · simp [BWin.subAll, hw, BWin.Mem]
      · simp [BWin.subAll, hw]
  | b :: bs, a, n, i => by
      simp only [BWin.subAll, List.mem_flatMap]
      constructor
      · rintro ⟨p, ⟨q, hq, hp⟩, hpm⟩
        have h1 := (BWin.mem_subAll bs q).mp ⟨p, hp, hpm⟩
        have h2 := BWin.mem_sub.mp ⟨q, hq, h1.1⟩
        refine ⟨h2.1, fun h3 => ?_⟩
        rcases inSet_cons.mp h3 with h3 | h3
        · exact h2.2 h3
        · exact h1.2 h3
      · rintro ⟨ha, hb⟩
        have hb' : ¬ b.Mem n i := fun h => hb (inSet_cons.mpr (Or.inl h))
        have hbs : ¬ InSet bs n i := fun h => hb (inSet_cons.mpr (Or.inr h))
        obtain ⟨q, hq, hqm⟩ := BWin.mem_sub.mpr ⟨ha, hb'⟩
        obtain ⟨p, hp, hpm⟩ := (BWin.mem_subAll bs q).mpr ⟨hqm, hbs⟩
        exact ⟨p, ⟨q, hq, hp⟩, hpm⟩

theorem inSet_interL {X Y : List BWin} {n : String} {i : Nat} :
    InSet (interL X Y) n i ↔ InSet X n i ∧ InSet Y n i := by
  simp only [InSet, interL, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, hm⟩
    have := BWin.mem_inter.mp hm
    exact ⟨⟨x, hx, this.1⟩, ⟨y, hy, this.2⟩⟩
  · rintro ⟨⟨x, hx, hxm⟩, ⟨y, hy, hym⟩⟩
    exact ⟨x.inter y, ⟨x, hx, y, hy, rfl⟩, BWin.mem_inter.mpr ⟨hxm, hym⟩⟩

/-- **The read check, semantically**: when `readsViol M A R` finds nothing,
every bit of `R` that `A` may write is in `M`. -/
theorem readsViol_none {M A R : List BWin} (h : readsViol M A R = none) {n : String} {i : Nat}
    (hr : InSet R n i) (ha : InSet A n i) : InSet M n i := by
  obtain ⟨r, hrR, hrm⟩ := hr
  obtain ⟨x, hxA, hxm⟩ := ha
  unfold readsViol at h
  rw [List.findSome?_eq_none_iff] at h
  have h1 := h r hrR
  rw [List.findSome?_eq_none_iff] at h1
  have h2 := h1 x hxA
  rw [List.head?_eq_none_iff] at h2
  refine Classical.byContradiction fun hM => ?_
  obtain ⟨p, hp, -⟩ := (BWin.mem_subAll M (r.inter x)).mpr ⟨BWin.mem_inter.mpr ⟨hrm, hxm⟩, hM⟩
  rw [h2] at hp
  exact absurd hp List.not_mem_nil

/-- A width-`0` window has no pieces left over. -/
theorem BWin.subAll_zero : ∀ (bs : List BWin) (a : BWin), a.2.2 = 0 → a.subAll bs = []
  | [], a, h => by simp [BWin.subAll, h]
  | b :: bs, a, h => by
      obtain ⟨an, al, aw⟩ := a
      simp only at h
      subst h
      simp only [BWin.subAll]
      have : BWin.sub (an, al, 0) b = [] := by
        obtain ⟨bn, bl, bw⟩ := b
        simp only [BWin.sub]
        split <;> simp <;> omega
      rw [this]
      rfl

/-- Reads of other signals than the ones `X` may write never violate. -/
theorem readsViol_none_of_names {M X R : List BWin} {N : List String}
    (hR : ∀ r ∈ R, r.1 ∉ N) (hX : ∀ x ∈ X, x.1 ∈ N) : readsViol M X R = none := by
  unfold readsViol
  rw [List.findSome?_eq_none_iff]
  intro r hr
  rw [List.findSome?_eq_none_iff]
  intro x hx
  have hne : r.1 ≠ x.1 := fun h => hR r hr (h ▸ hX x hx)
  rw [BWin.subAll_zero M (r.inter x) (by simp [BWin.inter, hne])]
  rfl

/-! ## The bit view of a state -/

/-- Bit `i` of signal `n` (`none`: absent signal or bit past its width). -/
def bitAt (st : SvState) (n : String) (i : Nat) : Option Logic :=
  (SvState.lookup st n).bind fun v => v.bits[i]?

/-- The same signals in the same order, each at the same width. -/
def SameShape (τ σ : SvState) : Prop :=
  τ.map Prod.fst = σ.map Prod.fst ∧
    ∀ n, (SvState.lookup τ n).map LVec.width = (SvState.lookup σ n).map LVec.width

/-- **Shaped** (for the width table `wd`): no signal name twice, and every
signal at the width `wd` declares — the states `run2` builds from a design
whose declaration names are distinct, with `wd` its declared widths. -/
def Shaped (wd : String → Option Nat) (st : SvState) : Prop :=
  (st.map Prod.fst).Nodup ∧ ∀ n v, SvState.lookup st n = some v → wd n = some v.width

/-- `τ` and `σ` agree on every bit of `R`. -/
def AgreeOn (R : List BWin) (τ σ : SvState) : Prop :=
  ∀ n i, InSet R n i → bitAt τ n i = bitAt σ n i

/-- `σ'` differs from `σ` only on bits of `X` (and has its shape). -/
def Frame (X : List BWin) (σ σ' : SvState) : Prop :=
  SameShape σ' σ ∧ ∀ n i, ¬ InSet X n i → bitAt σ' n i = bitAt σ n i

/-- The simulation invariant: every bit of `τ` is `σ`'s, or — only outside
`M` — the final state `F`'s. -/
def Inv (M : List BWin) (F τ σ : SvState) : Prop :=
  ∀ n i, bitAt τ n i = bitAt σ n i ∨ (¬ InSet M n i ∧ bitAt τ n i = bitAt F n i)

theorem SameShape.refl (σ : SvState) : SameShape σ σ := ⟨rfl, fun _ => rfl⟩

theorem SameShape.symm {τ σ : SvState} (h : SameShape τ σ) : SameShape σ τ :=
  ⟨h.1.symm, fun n => (h.2 n).symm⟩

theorem SameShape.trans {a b c : SvState} (h1 : SameShape a b) (h2 : SameShape b c) :
    SameShape a c := ⟨h1.1.trans h2.1, fun n => (h1.2 n).trans (h2.2 n)⟩

theorem SameShape.cases {τ σ : SvState} (h : SameShape τ σ) (n : String) :
    (SvState.lookup τ n = none ∧ SvState.lookup σ n = none) ∨
      ∃ u v, SvState.lookup τ n = some u ∧ SvState.lookup σ n = some v ∧ u.width = v.width := by
  have := h.2 n
  cases hτ : SvState.lookup τ n <;> cases hσ : SvState.lookup σ n <;> simp_all

theorem SameShape.some {τ σ : SvState} (h : SameShape τ σ) {n : String} {v : LVec}
    (hσ : SvState.lookup σ n = some v) :
    ∃ u, SvState.lookup τ n = some u ∧ u.width = v.width := by
  rcases h.cases n with ⟨-, h2⟩ | ⟨u, v', h1, h2, h3⟩
  · rw [hσ] at h2; cases h2
  · rw [hσ] at h2; cases h2; exact ⟨u, h1, h3⟩

theorem SameShape.none {τ σ : SvState} (h : SameShape τ σ) {n : String}
    (hσ : SvState.lookup σ n = none) : SvState.lookup τ n = none := by
  rcases h.cases n with ⟨h1, -⟩ | ⟨u, v', h1, h2, h3⟩
  · exact h1
  · rw [hσ] at h2; cases h2

theorem Shaped.of_sameShape {wd : String → Option Nat} {τ σ : SvState} (h : SameShape τ σ)
    (hs : Shaped wd σ) : Shaped wd τ := by
  refine ⟨h.1 ▸ hs.1, fun n u hu => ?_⟩
  rcases h.cases n with ⟨h1, -⟩ | ⟨u', v, h1, h2, h3⟩
  · rw [hu] at h1; cases h1
  · rw [hu] at h1; cases h1; rw [hs.2 n v h2, h3]

theorem Frame.refl (X : List BWin) (σ : SvState) : Frame X σ σ :=
  ⟨SameShape.refl σ, fun _ _ _ => rfl⟩

theorem Frame.mono {X Y : List BWin} {σ σ' : SvState} (h : Frame X σ σ')
    (hXY : ∀ n i, InSet X n i → InSet Y n i) : Frame Y σ σ' :=
  ⟨h.1, fun n i hn => h.2 n i fun hx => hn (hXY n i hx)⟩

theorem Frame.trans {X Y : List BWin} {a b c : SvState} (h1 : Frame X a b) (h2 : Frame Y b c) :
    Frame (X ++ Y) a c :=
  ⟨h2.1.trans h1.1, fun n i hn => by
    have hx : ¬ InSet X n i := fun h => hn (inSet_append.mpr (Or.inl h))
    have hy : ¬ InSet Y n i := fun h => hn (inSet_append.mpr (Or.inr h))
    rw [h2.2 n i hy, h1.2 n i hx]⟩

theorem Inv.mono {M X Y : List BWin} {F τ σ : SvState} (h : Inv (M ++ X) F τ σ)
    (hYX : ∀ n i, InSet Y n i → InSet X n i) : Inv (M ++ Y) F τ σ := by
  intro n i
  rcases h n i with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨fun hy => h1 ?_, h2⟩
    rcases inSet_append.mp hy with hy | hy
    · exact inSet_append.mpr (Or.inl hy)
    · exact inSet_append.mpr (Or.inr (hYX n i hy))

theorem Inv.append_nil {M : List BWin} {F τ σ : SvState} (h : Inv M F τ σ) :
    Inv (M ++ []) F τ σ := by simpa using h

/-! ## `LVec` and `SvState` facts -/

theorem bits_insertAt (v : LVec) (lo : Nat) (p : LVec) (i : Nat) :
    (v.insertAt lo p).bits[i]? = if i < v.width then
      some (if lo ≤ i ∧ i < lo + p.width then p.bits[i - lo]?.getD .lx else v.bits[i]?.getD .lx)
    else none := by
  simp only [LVec.insertAt, Array.getElem?_ofFn]
  split <;> rfl

theorem bits_extract (v : LVec) (lo w i : Nat) :
    (v.extract lo w).bits[i]? = if i < w then some (v.bits[lo + i]?.getD .lx) else none := by
  simp only [LVec.extract, Array.getElem?_ofFn]
  split <;> rfl

theorem LVec.ext_bits {u v : LVec} (h : ∀ i : Nat, u.bits[i]? = v.bits[i]?) : u = v := by
  obtain ⟨u⟩ := u; obtain ⟨v⟩ := v
  congr 1
  exact Array.ext_getElem? h

@[simp] theorem width_insertAt (v : LVec) (lo : Nat) (p : LVec) :
    (v.insertAt lo p).width = v.width := by simp [LVec.insertAt, LVec.width]

@[simp] theorem width_resizeU (v : LVec) (w : Nat) : (v.resizeU w).width = w := by
  simp [LVec.resizeU, LVec.width]

@[simp] theorem width_extract (v : LVec) (lo w : Nat) : (v.extract lo w).width = w := by
  simp [LVec.extract, LVec.width]

theorem bits_none_of_width {v : LVec} {i : Nat} (h : v.width ≤ i) : v.bits[i]? = none := by
  simp only [LVec.width] at h; simp [h]

theorem bits_getD_of_lt {v : LVec} {i : Nat} (d : Logic) (h : i < v.width) :
    some (v.bits[i]?.getD d) = v.bits[i]? := by
  simp only [LVec.width] at h; simp [h]

theorem lookup_set_self (st : SvState) (n : String) (v : LVec) :
    SvState.lookup (SvState.set st n v) n = some v := by
  induction st with
  | nil => simp [SvState.set, SvState.lookup]
  | cons kv rest ih =>
    obtain ⟨k, w⟩ := kv
    by_cases h : k = n
    · subst h; simp [SvState.set, SvState.lookup]
    · simp [SvState.set, SvState.lookup, h, ih]

theorem lookup_set_ne (st : SvState) {n m : String} (v : LVec) (h : m ≠ n) :
    SvState.lookup (SvState.set st n v) m = SvState.lookup st m := by
  induction st with
  | nil => simp [SvState.set, SvState.lookup, Ne.symm h]
  | cons kv rest ih =>
    obtain ⟨k, w⟩ := kv
    by_cases hk : k = n
    · subst hk; simp [SvState.set, SvState.lookup, Ne.symm h]
    · by_cases hkm : k = m
      · subst hkm; simp [SvState.set, SvState.lookup, hk]
      · simp [SvState.set, SvState.lookup, hk, hkm, ih]

theorem keys_set {st : SvState} {n : String} {old v : LVec}
    (h : SvState.lookup st n = some old) :
    (SvState.set st n v).map Prod.fst = st.map Prod.fst := by
  induction st with
  | nil => simp [SvState.lookup] at h
  | cons kv rest ih =>
    obtain ⟨k, w⟩ := kv
    by_cases hk : k = n
    · subst hk; simp [SvState.set]
    · simp only [SvState.lookup, beq_iff_eq, hk, if_false] at h
      simp [SvState.set, hk, ih h]

theorem lookup_eq_none_of_not_mem {st : SvState} {n : String}
    (h : n ∉ st.map Prod.fst) : SvState.lookup st n = none := by
  induction st with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k, w⟩ := kv
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [SvState.lookup, Ne.symm h.1, ih h.2]

theorem eq_of_lookup : ∀ {a b : SvState}, a.map Prod.fst = b.map Prod.fst →
    (a.map Prod.fst).Nodup → (∀ n, SvState.lookup a n = SvState.lookup b n) → a = b
  | [], [], _, _, _ => rfl
  | [], _ :: _, hk, _, _ => by simp at hk
  | _ :: _, [], hk, _, _ => by simp at hk
  | (k, v) :: as, (k', v') :: bs, hk, hnd, hl => by
      simp only [List.map_cons, List.cons.injEq] at hk
      obtain ⟨rfl, hk⟩ := hk
      simp only [List.map_cons, List.nodup_cons] at hnd
      have hv : v = v' := by
        have := hl k
        simp [SvState.lookup] at this
        exact this
      subst hv
      congr 1
      apply eq_of_lookup hk hnd.2
      intro n
      by_cases hn : n = k
      · subst hn
        rw [lookup_eq_none_of_not_mem hnd.1, lookup_eq_none_of_not_mem (hk ▸ hnd.1)]
      · have := hl n
        simp only [SvState.lookup, beq_iff_eq, Ne.symm hn, if_false] at this
        exact this

theorem bitAt_none_of_width {st : SvState} {n : String} {v : LVec}
    (h : SvState.lookup st n = some v) {j : Nat} (hj : v.width ≤ j) : bitAt st n j = none := by
  simp [bitAt, h, bits_none_of_width hj]

/-- A signal's value is fixed by its shape and its bits. -/
theorem lookup_eq_of_bits {τ σ : SvState} (hsh : SameShape τ σ) {n : String}
    (h : ∀ i, bitAt τ n i = bitAt σ n i) : SvState.lookup τ n = SvState.lookup σ n := by
  rcases hsh.cases n with ⟨h1, h2⟩ | ⟨u, v, h1, h2, h3⟩
  · rw [h1, h2]
  · rw [h1, h2]
    congr 1
    apply LVec.ext_bits
    intro i
    have := h i
    simp only [bitAt, h1, h2, Option.bind_some] at this
    exact this

/-! ## One write -/

/-- The bits after writing `p` at offset `lo` of signal `n`. -/
theorem bitAt_set_insertAt {st : SvState} {n : String} {old : LVec}
    (h : SvState.lookup st n = some old) (lo : Nat) (p : LVec) (m : String) (j : Nat) :
    bitAt (SvState.set st n (old.insertAt lo p)) m j =
      if m = n ∧ lo ≤ j ∧ j < lo + p.width ∧ j < old.width then some (p.bits[j - lo]?.getD .lx)
      else bitAt st m j := by
  by_cases hm : m = n
  · subst hm
    simp only [bitAt, lookup_set_self, h, Option.bind_some, bits_insertAt, true_and]
    by_cases hj : j < old.width
    · by_cases hw : lo ≤ j ∧ j < lo + p.width
      · rw [if_pos hj, if_pos hw, if_pos ⟨hw.1, hw.2, hj⟩]
      · rw [if_pos hj, if_neg hw, if_neg (fun h => hw ⟨h.1, h.2.1⟩), bits_getD_of_lt _ hj]
    · rw [if_neg hj, if_neg (fun h => hj h.2.2), bits_none_of_width (by omega)]
  · simp [bitAt, lookup_set_ne _ _ hm, hm]

theorem bitAt_set_insertAt_of_not_mem {st : SvState} {n : String} {old : LVec}
    (h : SvState.lookup st n = some old) (lo : Nat) (p : LVec) {m : String} {j : Nat}
    (hm : ¬ BWin.Mem (n, lo, p.width) m j) :
    bitAt (SvState.set st n (old.insertAt lo p)) m j = bitAt st m j := by
  rw [bitAt_set_insertAt h, if_neg]
  rintro ⟨h1, h2, h3, -⟩
  exact hm ⟨h1.symm, h2, h3⟩

/-- Writing the same `p` at the same place of two same-shaped states keeps
them same-shaped and makes them agree on the written window. -/
theorem write_rel {τ σ : SvState} (hsh : SameShape τ σ) {n : String} {oτ oσ : LVec}
    (hτ : SvState.lookup τ n = some oτ) (hσ : SvState.lookup σ n = some oσ) (lo : Nat)
    (p : LVec) :
    SameShape (SvState.set τ n (oτ.insertAt lo p)) (SvState.set σ n (oσ.insertAt lo p)) ∧
      ∀ m j, BWin.Mem (n, lo, p.width) m j →
        bitAt (SvState.set τ n (oτ.insertAt lo p)) m j =
          bitAt (SvState.set σ n (oσ.insertAt lo p)) m j := by
  obtain ⟨u, hu, hw⟩ := hsh.some hσ
  rw [hτ] at hu; cases hu
  refine ⟨⟨by rw [keys_set hτ, keys_set hσ, hsh.1], fun m => ?_⟩, fun m j hm => ?_⟩
  · by_cases hmn : m = n
    · subst hmn; simp [lookup_set_self, hw]
    · rw [lookup_set_ne _ _ hmn, lookup_set_ne _ _ hmn]; exact hsh.2 m
  · obtain ⟨rfl, h1, h2⟩ := hm
    rw [bitAt_set_insertAt hτ, bitAt_set_insertAt hσ, hw]
    by_cases hj : j < oσ.width
    · rw [if_pos ⟨rfl, h1, h2, hj⟩, if_pos ⟨rfl, h1, h2, hj⟩]
    · rw [if_neg (fun h => hj h.2.2.2), if_neg (fun h => hj h.2.2.2),
        bitAt_none_of_width hτ (by omega), bitAt_none_of_width hσ (by omega)]

/-- The first run's frame of one write: only the window's existing bits
change, and `Y` covers them. -/
theorem write_frame {Y : List BWin} {σ : SvState} {n : String} {oσ : LVec} {lo : Nat}
    {p : LVec} (hσ : SvState.lookup σ n = some oσ)
    (hY : ∀ j, BWin.Mem (n, lo, p.width) n j → j < oσ.width → InSet Y n j) :
    Frame Y σ (SvState.set σ n (oσ.insertAt lo p)) := by
  refine ⟨⟨keys_set hσ, fun m => ?_⟩, fun m j hm => ?_⟩
  · by_cases hmn : m = n
    · subst hmn; simp [lookup_set_self, hσ]
    · rw [lookup_set_ne _ _ hmn]
  · by_cases hW : BWin.Mem (n, lo, p.width) m j
    · have hnm : n = m := hW.1
      subst hnm
      by_cases hj : j < oσ.width
      · exact absurd (hY j hW hj) hm
      · rw [bitAt_none_of_width (lookup_set_self σ n _) (by simp; omega),
          bitAt_none_of_width hσ (by omega)]
    · exact bitAt_set_insertAt_of_not_mem hσ lo p hW

/-- **The post-state of one write**, in the invariant's terms: the window
`(n, lo, p.width)` agrees after the write; the must-set `X` (every existing
bit of it in the window) joins `M`; the first run's frame is any `Y`
covering the window's existing bits. -/
theorem write_post {M X Y : List BWin} {F τ σ : SvState} {n : String} {oτ oσ : LVec}
    {lo : Nat} {p : LVec} (hsh : SameShape τ σ) (hinv : Inv M F τ σ)
    (hτ : SvState.lookup τ n = some oτ) (hσ : SvState.lookup σ n = some oσ)
    (hX : ∀ m j, InSet X m j → ∀ v, SvState.lookup σ m = some v → j < v.width →
      BWin.Mem (n, lo, p.width) m j)
    (hY : ∀ j, BWin.Mem (n, lo, p.width) n j → j < oσ.width → InSet Y n j) :
    SameShape (SvState.set τ n (oτ.insertAt lo p)) (SvState.set σ n (oσ.insertAt lo p)) ∧
    Inv (M ++ X) F (SvState.set τ n (oτ.insertAt lo p)) (SvState.set σ n (oσ.insertAt lo p)) ∧
    Frame Y σ (SvState.set σ n (oσ.insertAt lo p)) := by
  obtain ⟨hsh', hwin⟩ := write_rel hsh hτ hσ lo p
  have hshσ : SameShape (SvState.set σ n (oσ.insertAt lo p)) σ :=
    ⟨keys_set hσ, fun m => by
      by_cases hmn : m = n
      · subst hmn; simp [lookup_set_self, hσ]
      · rw [lookup_set_ne _ _ hmn]⟩
  refine ⟨hsh', fun m j => ?_, hshσ, fun m j hm => ?_⟩
  · by_cases hW : BWin.Mem (n, lo, p.width) m j
    · exact Or.inl (hwin m j hW)
    · rw [bitAt_set_insertAt_of_not_mem hτ lo p hW, bitAt_set_insertAt_of_not_mem hσ lo p hW]
      rcases hinv m j with h | ⟨h1, h2⟩
      · exact Or.inl h
      · -- a bit of `X` that exists lies in the window; one that does not exist is `none` in both
        rcases hsh.cases m with ⟨h3, h4⟩ | ⟨u, v, h3, h4, h5⟩
        · left; simp [bitAt, h3, h4]
        · by_cases hj : j < v.width
          · refine Or.inr ⟨fun hx => ?_, h2⟩
            rcases inSet_append.mp hx with hx | hx
            · exact h1 hx
            · exact hW (hX m j hx v h4 hj)
          · left
            rw [bitAt_none_of_width h3 (by omega), bitAt_none_of_width h4 (by omega)]
  · by_cases hW : BWin.Mem (n, lo, p.width) m j
    · have hnm : n = m := hW.1
      subst hnm
      by_cases hj : j < oσ.width
      · exact absurd (hY j hW hj) hm
      · rw [bitAt_none_of_width (lookup_set_self σ n _) (by simp; omega),
          bitAt_none_of_width hσ (by omega)]
    · exact bitAt_set_insertAt_of_not_mem hσ lo p hW

/-! ## Expression congruence -/

theorem AgreeOn.left {X Y : List BWin} {τ σ : SvState} (h : AgreeOn (X ++ Y) τ σ) :
    AgreeOn X τ σ := fun n i hn => h n i (inSet_append.mpr (Or.inl hn))

theorem AgreeOn.right {X Y : List BWin} {τ σ : SvState} (h : AgreeOn (X ++ Y) τ σ) :
    AgreeOn Y τ σ := fun n i hn => h n i (inSet_append.mpr (Or.inr hn))

/-- A whole-signal read agrees when the signal's declared bits do. -/
theorem lookup_eq_of_whole {wd : String → Option Nat} {τ σ : SvState} (hsh : SameShape τ σ)
    (hs : Shaped wd σ) {n : String} (h : AgreeOn [whole wd n] τ σ) :
    SvState.lookup τ n = SvState.lookup σ n := by
  rcases hsh.cases n with ⟨h1, h2⟩ | ⟨u, v, h1, h2, h3⟩
  · rw [h1, h2]
  · apply lookup_eq_of_bits hsh
    intro i
    by_cases hi : i < v.width
    · exact h n i (inSet_singleton.mpr ⟨rfl, Nat.zero_le _, by simp [whole, hs.2 n v h2]; exact hi⟩)
    · rw [bitAt_none_of_width h1 (by omega), bitAt_none_of_width h2 (by omega)]

/-- A constant-slice read agrees when the slice's bits do. -/
theorem extract_eq_of_agree {τ σ : SvState} (hsh : SameShape τ σ) {n : String} {lo w : Nat}
    (h : AgreeOn [(n, lo, w)] τ σ) :
    (SvState.lookup τ n).map (·.extract lo w) = (SvState.lookup σ n).map (·.extract lo w) := by
  rcases hsh.cases n with ⟨h1, h2⟩ | ⟨u, v, h1, h2, h3⟩
  · rw [h1, h2]
  · rw [h1, h2]
    simp only [Option.map_some, Option.some.injEq]
    apply LVec.ext_bits
    intro i
    rw [bits_extract, bits_extract]
    by_cases hi : i < w
    · have := h n (lo + i)
        (inSet_singleton.mpr ⟨rfl, Nat.le_add_right _ _, by show lo + i < lo + w; omega⟩)
      simp only [bitAt, h1, h2, Option.bind_some] at this
      rw [if_pos hi, if_pos hi, this]
    · rw [if_neg hi, if_neg hi]

theorem sliceRd_cases (a : Expr2) (lo w : Nat) (r : List BWin) :
    (∃ n, a = .ident n ∧ sliceRd a lo w r = [(n, lo, w)]) ∨ sliceRd a lo w r = r := by
  cases a <;> simp [sliceRd]

/-- **Expression congruence**: evaluation at every fuel depends only on the
bits `Expr2.rdW` names. -/
theorem eval_congr {wd : String → Option Nat} {τ σ : SvState} (hsh : SameShape τ σ)
    (hs : Shaped wd σ) : ∀ fuel : Nat,
    (∀ e : Expr2, AgreeOn (e.rdW wd) τ σ → evalExpr2 fuel τ e = evalExpr2 fuel σ e) ∧
    (∀ es : List Expr2, AgreeOn (Expr2.listRdW wd es) τ σ →
      evalExprs2 fuel τ es = evalExprs2 fuel σ es) := by
  intro fuel
  induction fuel with
  | zero => exact ⟨fun e _ => by simp [evalExpr2], fun es _ => by simp [evalExprs2]⟩
  | succ k ih =>
    obtain ⟨ihE, ihEs⟩ := ih
    refine ⟨fun e h => ?_, fun es h => ?_⟩
    · cases e with
      | lit v => rfl
      | ident n =>
        simp only [Expr2.rdW] at h
        simp only [evalExpr2, readSignal, lookup_eq_of_whole hsh hs h]
      | unsupported k x => rfl
      | unary op a => simp only [Expr2.rdW] at h; simp only [evalExpr2, ihE a h]
      | resizeSigned w a => simp only [Expr2.rdW] at h; simp only [evalExpr2, ihE a h]
      | squash2 a => simp only [Expr2.rdW] at h; simp only [evalExpr2, ihE a h]
      | repl c a => simp only [Expr2.rdW] at h; simp only [evalExpr2, ihE a h]
      | reduce op a => simp only [Expr2.rdW] at h; simp only [evalExpr2, ihE a h]
      | resize w a => simp only [Expr2.rdW] at h; simp only [evalExpr2, ihE a h]
      | binary op l r =>
        simp only [Expr2.rdW] at h
        simp only [evalExpr2, ihE l h.left, ihE r h.right]
      | scmp op l r =>
        simp only [Expr2.rdW] at h
        simp only [evalExpr2, ihE l h.left, ihE r h.right]
      | logical b l r =>
        simp only [Expr2.rdW] at h
        simp only [evalExpr2, ihE l h.left, ihE r h.right]
      | ternary c t f =>
        simp only [Expr2.rdW] at h
        simp only [evalExpr2, ihE c h.left, ihE t h.right.left, ihE f h.right.right]
      | index a i ew =>
        simp only [Expr2.rdW] at h
        simp only [evalExpr2, ihE a h.left, ihE i h.right]
      | concat ps =>
        simp only [Expr2.rdW] at h
        simp only [evalExpr2, ihEs ps.toList h]
      | slice a lo w =>
        simp only [Expr2.rdW] at h
        rcases sliceRd_cases a lo w (a.rdW wd) with ⟨n, rfl, hr⟩ | hr
        · rw [hr] at h
          have hx := extract_eq_of_agree hsh h
          simp only [evalExpr2]
          cases k with
          | zero => simp [evalExpr2]
          | succ k =>
            simp only [evalExpr2, readSignal]
            rcases hsh.cases n with ⟨h1, h2⟩ | ⟨u, v, h1, h2, h3⟩
            · rw [h1, h2]
            · rw [h1, h2] at hx ⊢
              simp only [Option.map_some, Option.some.injEq] at hx
              simp [hx]
        · rw [hr] at h
          simp only [evalExpr2, ihE a h]
    · cases es with
      | nil => rfl
      | cons e rest =>
        simp only [Expr2.listRdW] at h
        simp only [evalExprs2, ihE e h.left, ihEs rest h.right]

/-! ## Target congruence -/

/-- Two same-shaped states resolve a non-concatenated target alike when its
index expression's bits agree. -/
theorem resolveLhs2_congr {wd : String → Option Nat} {fuel : Nat} {τ σ : SvState}
    (hsh : SameShape τ σ)
    (hE : ∀ e : Expr2, AgreeOn (e.rdW wd) τ σ → evalExpr2 fuel τ e = evalExpr2 fuel σ e)
    (t : Lhs2) (h : AgreeOn (t.rdW wd) τ σ) : resolveLhs2 fuel τ t = resolveLhs2 fuel σ t := by
  cases t with
  | ident n =>
    simp only [resolveLhs2]
    rcases hsh.cases n with ⟨h1, h2⟩ | ⟨u, v, h1, h2, h3⟩
    · rw [h1, h2]
    · rw [h1, h2]; simp [h3]
  | slice n lo w => rfl
  | index n idx ew =>
    simp only [Lhs2.rdW] at h
    simp only [resolveLhs2, hE idx h]
    rcases hsh.cases n with ⟨h1, h2⟩ | ⟨u, v, h1, h2, h3⟩
    · rw [h1, h2]
    · rw [h1, h2]; simp [h3]
  | concat ps => rfl

/-- A target never resolves to "no write" unless it is a run-time index (its
must-set is then empty). -/
theorem resolveLhs2_none {wd : String → Option Nat} {fuel : Nat} {σ : SvState} {t : Lhs2}
    {n : String} (h : resolveLhs2 fuel σ t = .ok (n, none)) : t.mustW wd = [] := by
  cases t with
  | ident m =>
    simp only [resolveLhs2] at h
    cases hm : SvState.lookup σ m <;> rw [hm] at h <;> simp at h
  | slice m lo w => simp [resolveLhs2] at h
  | index m idx ew => rfl
  | concat ps => simp [resolveLhs2] at h

/-- The window a non-concatenated target resolves to: it contains every
existing bit of the target's must-set, and its existing bits lie in the
target's may-set. -/
theorem resolveLhs2_some {wd : String → Option Nat} {fuel : Nat} {σ : SvState} {t : Lhs2}
    {n : String} {lo w : Nat} (hs : Shaped wd σ)
    (h : resolveLhs2 fuel σ t = .ok (n, some (lo, w))) :
    (∀ m j, InSet (t.mustW wd) m j → ∀ v, SvState.lookup σ m = some v → j < v.width →
      BWin.Mem (n, lo, w) m j) ∧
    (∀ j, BWin.Mem (n, lo, w) n j → ∀ old, SvState.lookup σ n = some old →
      j < old.width → InSet (t.mayW wd) n j) := by
  cases t with
  | ident m =>
    simp only [resolveLhs2] at h
    cases hm : SvState.lookup σ m with
    | none => rw [hm] at h; simp at h
    | some old =>
      rw [hm] at h
      simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨fun m' j hj v hv hjv => ?_, fun j _ old' hold hj => ?_⟩
      · have hj' := inSet_singleton.mp hj
        have hm' : m' = m := by simpa [whole] using hj'.1.symm
        rw [hm'] at hv ⊢
        rw [hm] at hv; cases hv
        exact ⟨rfl, Nat.zero_le _, by simpa using hjv⟩
      · rw [hm] at hold; cases hold
        exact inSet_singleton.mpr ⟨rfl, Nat.zero_le _, by simp [whole, hs.2 _ _ hm]; exact hj⟩
  | slice m lo' w' =>
    simp only [resolveLhs2, Res.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨fun m' j hj _ _ _ => inSet_singleton.mp hj, fun j hj _ _ _ => inSet_singleton.mpr hj⟩
  | index m idx ew =>
    simp only [resolveLhs2] at h
    obtain ⟨iv, -, h⟩ := Res.bind_eq_ok.mp h
    cases hm : SvState.lookup σ m with
    | none => rw [hm] at h; simp at h
    | some old =>
      rw [hm] at h
      have hn : n = m := by
        rcases hiv : iv.toNat? with _ | i
        · rw [hiv] at h; simp at h
        · rw [hiv] at h
          simp only at h
          by_cases hc : (i + 1) * ew ≤ old.width
          · rw [if_pos hc] at h; simp at h; exact h.1.symm
          · rw [if_neg hc] at h; simp at h
      subst hn
      refine ⟨fun m' j hj => absurd hj (by simp [Lhs2.mustW]), fun j _ old' hold hj => ?_⟩
      rw [hm] at hold; cases hold
      exact inSet_singleton.mpr ⟨rfl, Nat.zero_le _, by simp [whole, hs.2 _ _ hm]; exact hj⟩
  | concat ps => simp [resolveLhs2] at h

theorem listRdW_of_mem {wd : String → Option Nat} {t : Lhs2} :
    ∀ {ts : List Lhs2}, t ∈ ts → ∀ n i, InSet (t.rdW wd) n i → InSet (Lhs2.listRdW wd ts) n i
  | [], h => absurd h List.not_mem_nil
  | s :: ss, h => by
      intro n i hn
      simp only [Lhs2.listRdW]
      rcases List.mem_cons.mp h with rfl | h
      · exact inSet_append.mpr (Or.inl hn)
      · exact inSet_append.mpr (Or.inr (listRdW_of_mem h n i hn))

theorem listMayW_of_mem {wd : String → Option Nat} {t : Lhs2} :
    ∀ {ts : List Lhs2}, t ∈ ts → ∀ n i, InSet (t.mayW wd) n i → InSet (Lhs2.listMayW wd ts) n i
  | [], h => absurd h List.not_mem_nil
  | s :: ss, h => by
      intro n i hn
      simp only [Lhs2.listMayW]
      rcases List.mem_cons.mp h with rfl | h
      · exact inSet_append.mpr (Or.inl hn)
      · exact inSet_append.mpr (Or.inr (listMayW_of_mem h n i hn))

theorem foldlM_congr {α β : Type} {f g : β → α → Res β} :
    ∀ (l : List α) (init : β), (∀ b a, a ∈ l → f b a = g b a) →
      l.foldlM f init = l.foldlM g init
  | [], _, _ => rfl
  | a :: as, init, h => by
      simp only [List.foldlM]
      rw [h init a (List.mem_cons_self ..)]
      cases g init a with
      | ok b => exact foldlM_congr as b fun b' a' ha' => h b' a' (List.mem_cons_of_mem _ ha')
      | timeout => rfl
      | unsupported m => rfl

/-- The windows a concatenation's leaf fold collects come from its leaves. -/
theorem foldlM_wins {α : Type} {g : α → Res (List BWin)} :
    ∀ (l : List α) (acc ws : List BWin),
      l.foldlM (fun acc part => do let w ← g part; pure (acc ++ w)) acc = .ok ws →
      ∀ x ∈ ws, x ∈ acc ∨ ∃ p ∈ l, ∃ w, g p = .ok w ∧ x ∈ w
  | [], acc, ws, h => by
      simp only [List.foldlM] at h
      cases h
      exact fun x hx => Or.inl hx
  | p :: ps, acc, ws, h => by
      simp only [List.foldlM] at h
      cases hg : g p with
      | ok w =>
        rw [hg] at h
        simp only [Res.ok_bind, Res.pure_eq] at h
        intro x hx
        rcases foldlM_wins ps (acc ++ w) ws h x hx with h1 | ⟨q, hq, w', hw', hx'⟩
        · rcases List.mem_append.mp h1 with h1 | h1
          · exact Or.inl h1
          · exact Or.inr ⟨p, List.mem_cons_self .., w, hg, h1⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, w', hw', hx'⟩
      | timeout => rw [hg] at h; simp at h
      | unsupported m => rw [hg] at h; simp at h

/-- Two same-shaped states resolve a concatenated target alike. -/
theorem resolveConcatLhs2_congr {wd : String → Option Nat} {fuel : Nat} {τ σ : SvState}
    (hR : ∀ t : Lhs2, AgreeOn (t.rdW wd) τ σ → resolveLhs2 fuel τ t = resolveLhs2 fuel σ t) :
    ∀ t : Lhs2, AgreeOn (t.rdW wd) τ σ → resolveConcatLhs2 fuel τ t = resolveConcatLhs2 fuel σ t
  | .concat parts, h => by
      rw [resolveConcatLhs2.eq_1, resolveConcatLhs2.eq_1]
      apply foldlM_congr
      intro acc part hmem
      have hp : AgreeOn (part.rdW wd) τ σ := fun n i hn =>
        h n i (by simp only [Lhs2.rdW]; exact listRdW_of_mem hmem n i hn)
      rw [resolveConcatLhs2_congr hR part hp]
  | .ident n, h => by simp only [resolveConcatLhs2]; rw [hR _ h]
  | .slice n lo w, h => by simp only [resolveConcatLhs2]; rw [hR _ h]
  | .index n idx ew, h => by simp only [resolveConcatLhs2]; rw [hR _ h]
termination_by t => sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem hmem
  simp_wf
  omega

/-- A leaf's `resolveLhs2` window lies in the leaf's may-set (existing bits). -/
theorem leaf_sub {wd : String → Option Nat} {fuel : Nat} {σ : SvState} (hs : Shaped wd σ)
    {t : Lhs2} {name : String} {lo w : Nat}
    (hres : resolveLhs2 fuel σ t = .ok (name, some (lo, w))) :
    ∀ m j, InSet [(name, lo, w)] m j → ∀ v, SvState.lookup σ m = some v → j < v.width →
      InSet (t.mayW wd) m j := by
  intro m j hm v hv hj
  have hm' := inSet_singleton.mp hm
  have hnm : name = m := hm'.1
  subst hnm
  exact (resolveLhs2_some hs hres).2 j hm' v hv hj

/-- Every existing bit of a window `resolveConcatLhs2` returns is one the
target may write. -/
theorem resolveConcatLhs2_sub {wd : String → Option Nat} {fuel : Nat} {σ : SvState}
    (hs : Shaped wd σ) :
    ∀ (t : Lhs2) (ws : List BWin), resolveConcatLhs2 fuel σ t = .ok ws →
      ∀ m j, InSet ws m j → ∀ v, SvState.lookup σ m = some v → j < v.width →
        InSet (t.mayW wd) m j
  | .concat parts, ws, h => by
      rw [resolveConcatLhs2.eq_1] at h
      intro m j hm v hv hj
      obtain ⟨x, hx, hxm⟩ := hm
      rcases foldlM_wins parts [] ws h x hx with h1 | ⟨part, hpart, w, hw, hxw⟩
      · exact absurd h1 List.not_mem_nil
      · simp only [Lhs2.mayW]
        exact listMayW_of_mem hpart m j
          (resolveConcatLhs2_sub hs part w hw m j ⟨x, hxw, hxm⟩ v hv hj)
  | .ident n, ws, h => by
      simp only [resolveConcatLhs2] at h
      obtain ⟨⟨name, win⟩, hres, h⟩ := Res.bind_eq_ok.mp h
      cases win with
      | none => simp at h
      | some lw =>
        obtain ⟨lo', w'⟩ := lw
        simp only [Res.pure_eq, Res.ok.injEq] at h
        subst h
        exact leaf_sub hs hres
  | .slice n lo w, ws, h => by
      simp only [resolveConcatLhs2] at h
      obtain ⟨⟨name, win⟩, hres, h⟩ := Res.bind_eq_ok.mp h
      cases win with
      | none => simp at h
      | some lw =>
        obtain ⟨lo', w'⟩ := lw
        simp only [Res.pure_eq, Res.ok.injEq] at h
        subst h
        exact leaf_sub hs hres
  | .index n idx ew, ws, h => by
      simp only [resolveConcatLhs2] at h
      obtain ⟨⟨name, win⟩, hres, h⟩ := Res.bind_eq_ok.mp h
      cases win with
      | none => simp at h
      | some lw =>
        obtain ⟨lo', w'⟩ := lw
        simp only [Res.pure_eq, Res.ok.injEq] at h
        subst h
        exact leaf_sub hs hres
termination_by t => sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem hpart
  simp_wf
  omega

/-! ## Concatenated writes -/

/-- **Two runs of the concatenated-target writer** with the same windows and
the same sampled value, from same-shaped states: same shape after, agreement
on every written window, and every other bit unchanged in both. -/
theorem go_rel (rep : LVec) : ∀ (ws : List BWin) (τ σ σ' : SvState) (rw : Nat),
    SameShape τ σ → writeConcatLhs2.go rep σ ws rw = .ok σ' →
    ∃ τ', writeConcatLhs2.go rep τ ws rw = .ok τ' ∧ SameShape τ' σ' ∧
      (∀ m j, InSet ws m j → bitAt τ' m j = bitAt σ' m j) ∧
      (∀ m j, ¬ InSet ws m j → bitAt τ' m j = bitAt τ m j ∧ bitAt σ' m j = bitAt σ m j)
  | [], τ, σ, σ', rw, hsh, h => by
      simp only [writeConcatLhs2.go, Res.ok.injEq] at h
      subst h
      exact ⟨τ, rfl, hsh, fun _ _ h => absurd h inSet_nil, fun _ _ _ => ⟨rfl, rfl⟩⟩
  | (n, lo, w) :: rest, τ, σ, σ', rw, hsh, h => by
      simp only [writeConcatLhs2.go] at h
      cases hσ : SvState.lookup σ n with
      | none => rw [hσ] at h; simp at h
      | some oσ =>
        rw [hσ] at h
        simp only at h
        obtain ⟨oτ, hτ, -⟩ := hsh.some hσ
        have hp : (rep.extract (rw - w) w).width = w := width_extract _ _ _
        obtain ⟨hsh1, hwin⟩ := write_rel hsh hτ hσ lo (rep.extract (rw - w) w)
        obtain ⟨τ', h1, hsh', hin, hout⟩ := go_rel rep rest _ _ σ' (rw - w) hsh1 h
        refine ⟨τ', ?_, hsh', fun m j hm => ?_, fun m j hm => ?_⟩
        · simp only [writeConcatLhs2.go, hτ]; exact h1
        · rcases inSet_cons.mp hm with hm | hm
          · by_cases hr : InSet rest m j
            · exact hin m j hr
            · obtain ⟨e1, e2⟩ := hout m j hr
              rw [e1, e2]
              exact hwin m j (by rw [hp]; exact hm)
          · exact hin m j hm
        · have hm1 : ¬ BWin.Mem (n, lo, (rep.extract (rw - w) w).width) m j := by
            rw [hp]; exact fun h => hm (inSet_cons.mpr (Or.inl h))
          have hm2 : ¬ InSet rest m j := fun h => hm (inSet_cons.mpr (Or.inr h))
          obtain ⟨e1, e2⟩ := hout m j hm2
          rw [e1, e2, bitAt_set_insertAt_of_not_mem hτ lo _ hm1,
            bitAt_set_insertAt_of_not_mem hσ lo _ hm1]
          exact ⟨rfl, rfl⟩

/-! ## The simulation -/

theorem orElse_eq_none {α : Type} {x y : Option α} : (x <|> y) = none ↔ x = none ∧ y = none := by
  cases x <;> simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- The reads of a point agree between the two runs: a read bit is in `M`
(so `Inv` makes the runs agree on it) or the rest of the first run does not
write it (so the final state holds the first run's current value). -/
theorem agree_of_viol {M X R : List BWin} {F τ σ : SvState} (hv : readsViol M X R = none)
    (hinv : Inv M F τ σ) (hF : ∀ n i, ¬ InSet X n i → bitAt F n i = bitAt σ n i) :
    AgreeOn R τ σ := by
  intro n i hr
  rcases hinv n i with h | ⟨h1, h2⟩
  · exact h
  · by_cases hx : InSet X n i
    · exact absurd (readsViol_none hv hr hx) h1
    · rw [h2, hF n i hx]

/-- The final state agrees with the state before a statement on every bit
neither the statement nor the rest of the run may write. -/
theorem hF_pre {X A : List BWin} {F σ σ' : SvState}
    (hF : ∀ n i, ¬ InSet A n i → bitAt F n i = bitAt σ' n i) (hfr : Frame X σ σ') :
    ∀ n i, ¬ InSet (X ++ A) n i → bitAt F n i = bitAt σ n i := by
  intro n i h
  have hx : ¬ InSet X n i := fun hx => h (inSet_append.mpr (Or.inl hx))
  have ha : ¬ InSet A n i := fun ha => h (inSet_append.mpr (Or.inr ha))
  rw [hF n i ha, hfr.2 n i hx]

/-- A frame from the windows a write sequence touched: bits outside them are
unchanged, and their existing bits are in `X`. -/
theorem frame_of_wins {X ws : List BWin} {σ σ' : SvState} (hsh : SameShape σ' σ)
    (hout : ∀ m j, ¬ InSet ws m j → bitAt σ' m j = bitAt σ m j)
    (hsub : ∀ m j, InSet ws m j → ∀ v, SvState.lookup σ m = some v → j < v.width →
      InSet X m j) : Frame X σ σ' := by
  refine ⟨hsh, fun m j hm => ?_⟩
  by_cases hw : InSet ws m j
  · rcases hsh.cases m with ⟨h1, h2⟩ | ⟨u, v, h1, h2, h3⟩
    · simp [bitAt, h1, h2]
    · by_cases hj : j < v.width
      · exact absurd (hsub m j hw v h2 hj) hm
      · rw [bitAt_none_of_width h1 (by omega), bitAt_none_of_width h2 (by omega)]
  · exact hout m j hw

theorem go_shape (rep : LVec) : ∀ (ws : List BWin) (σ σ' : SvState) (rw : Nat),
    writeConcatLhs2.go rep σ ws rw = .ok σ' → SameShape σ' σ
  | [], σ, σ', rw, h => by
      simp only [writeConcatLhs2.go, Res.ok.injEq] at h
      subst h; exact SameShape.refl _
  | (n, lo, w) :: rest, σ, σ', rw, h => by
      simp only [writeConcatLhs2.go] at h
      cases hσ : SvState.lookup σ n with
      | none => rw [hσ] at h; simp at h
      | some oσ =>
        rw [hσ] at h
        simp only at h
        refine (go_shape rep rest _ σ' _ h).trans ⟨keys_set hσ, fun m => ?_⟩
        by_cases hmn : m = n
        · subst hmn; simp [lookup_set_self, hσ]
        · rw [lookup_set_ne _ _ hmn]

theorem inSet_mustW_listMustW_left {wd : String → Option Nat} {md : List BWin}
    {it : CaseItem2} {rest : List CaseItem2} {n : String} {i : Nat}
    (h : InSet (CaseItem2.listMustW wd md (it :: rest)) n i) : InSet (it.mustW wd) n i := by
  simp only [CaseItem2.listMustW] at h
  exact (inSet_interL.mp h).1

theorem inSet_mustW_listMustW_right {wd : String → Option Nat} {md : List BWin}
    {it : CaseItem2} {rest : List CaseItem2} {n : String} {i : Nat}
    (h : InSet (CaseItem2.listMustW wd md (it :: rest)) n i) :
    InSet (CaseItem2.listMustW wd md rest) n i := by
  simp only [CaseItem2.listMustW] at h
  exact (inSet_interL.mp h).2

/-- The non-concatenated blocking assignment case of `sim`: both runs
resolve the same window (or none) and write the same value into it. -/
theorem assign_sim {wd : String → Option Nat} {k : Nat} {t : Lhs2} {e : Expr2} {v : LVec}
    {F σ τ σ' : SvState} {nb q : NbaQueue2} {M A : List BWin}
    (hs : Shaped wd σ) (hsh : SameShape τ σ) (hinv : Inv M F τ σ)
    (hF : ∀ n i, ¬ InSet A n i → bitAt F n i = bitAt σ' n i)
    (hv : readsViol M (t.mayW wd ++ A) (e.rdW wd ++ t.rdW wd) = none)
    (hev : evalExpr2 k σ e = .ok v)
    (h1 : (do
      let x ← resolveLhs2 k σ t
      match x.snd with
      | none => Res.ok (σ, nb)
      | some (lo, w) =>
          match SvState.lookup σ x.fst with
          | some old => Res.ok (SvState.set σ x.fst (old.insertAt lo (v.resizeU w)), nb)
          | none => Res.unsupported s!"unknown assignment target '{x.fst}'") = .ok (σ', q))
    (hE : ∀ e : Expr2, AgreeOn (e.rdW wd) τ σ → evalExpr2 k τ e = evalExpr2 k σ e)
    (hR : ∀ t : Lhs2, AgreeOn (t.rdW wd) τ σ → resolveLhs2 k τ t = resolveLhs2 k σ t) :
    evalExpr2 k τ e = .ok v ∧ ∃ τ', (do
      let x ← resolveLhs2 k τ t
      match x.snd with
      | none => Res.ok (τ, nb)
      | some (lo, w) =>
          match SvState.lookup τ x.fst with
          | some old => Res.ok (SvState.set τ x.fst (old.insertAt lo (v.resizeU w)), nb)
          | none => Res.unsupported s!"unknown assignment target '{x.fst}'") = .ok (τ', q) ∧
      SameShape τ' σ' ∧ Inv (M ++ t.mustW wd) F τ' σ' ∧ Frame (t.mayW wd) σ σ' := by
  obtain ⟨⟨n, win⟩, hres, h1⟩ := Res.bind_eq_ok.mp h1
  cases win with
  | none =>
    simp only [Res.ok.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    have hag := agree_of_viol hv hinv (hF_pre hF (Frame.refl (t.mayW wd) σ))
    have hev' : evalExpr2 k τ e = .ok v := by rw [hE e hag.left, hev]
    have hres' : resolveLhs2 k τ t = .ok (n, none) := by rw [hR t hag.right, hres]
    refine ⟨hev', τ, by rw [hres']; rfl, hsh, ?_, Frame.refl _ _⟩
    rw [resolveLhs2_none hres]; exact hinv.append_nil
  | some lw =>
    obtain ⟨lo, w⟩ := lw
    simp only at h1
    cases hl : SvState.lookup σ n with
    | none => rw [hl] at h1; simp at h1
    | some old =>
      rw [hl] at h1
      simp only [Res.ok.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨hmust, hmay⟩ := resolveLhs2_some hs hres
      have hY : ∀ j, BWin.Mem (n, lo, (v.resizeU w).width) n j → j < old.width →
          InSet (t.mayW wd) n j := fun j hj hjw => hmay j (by simpa using hj) old hl hjw
      have hframe := write_frame hl hY
      have hag := agree_of_viol hv hinv (hF_pre hF hframe)
      have hev' : evalExpr2 k τ e = .ok v := by rw [hE e hag.left, hev]
      have hres' : resolveLhs2 k τ t = .ok (n, some (lo, w)) := by rw [hR t hag.right, hres]
      obtain ⟨oτ, hτ, -⟩ := hsh.some hl
      have hX : ∀ m j, InSet (t.mustW wd) m j → ∀ v', SvState.lookup σ m = some v' →
          j < v'.width → BWin.Mem (n, lo, (v.resizeU w).width) m j :=
        fun m j hm v' hv' hj => by simpa using hmust m j hm v' hv' hj
      obtain ⟨hsh', hinv', -⟩ := write_post hsh hinv hτ hl hX hY
      refine ⟨hev', SvState.set τ n (oτ.insertAt lo (v.resizeU w)), ?_, hsh', hinv', hframe⟩
      rw [hres']
      simp only [Res.ok_bind, hτ]

/-- **The simulation**: one fuel induction over `execStmt2`/`execCase2`/
`execStmts2`. If the first run takes a statement from `σ` to `σ'` (`q` its
NBA queue), the guard finds nothing with must-set `M` and may-after set
`A`, the second run's state `τ` is in `Inv M F τ σ`, and the final state `F`
agrees with `σ'` outside `A`, then the second run takes the statement from
`τ` to some `τ'` with the same queue, `τ'` has `σ'`'s shape, `Inv` grows by
the statement's must-writes, and the first run changed only bits the
statement may write (`Frame`). -/
theorem sim (wd : String → Option Nat) : ∀ fuel : Nat,
    (∀ (s : Stmt2) (F σ τ σ' : SvState) (nb q : NbaQueue2) (M A : List BWin),
      Shaped wd σ → SameShape τ σ → s.combViol wd M A = none →
      execStmt2 fuel σ nb s = .ok (σ', q) → Inv M F τ σ →
      (∀ n i, ¬ InSet A n i → bitAt F n i = bitAt σ' n i) →
      ∃ τ', execStmt2 fuel τ nb s = .ok (τ', q) ∧ SameShape τ' σ' ∧
        Inv (M ++ s.mustW wd) F τ' σ' ∧ Frame (s.mayW wd) σ σ') ∧
    (∀ (its : List CaseItem2) (d : Option Stmt2) (sv : LVec) (inside : Bool)
        (F σ τ σ' : SvState) (nb q : NbaQueue2) (M A md : List BWin),
      Shaped wd σ → SameShape τ σ →
      CaseItem2.listCombViol wd M A (Stmt2.optMayW wd d) (Stmt2.optCombViol wd M A d) its = none →
      md = (Stmt2.optMustW wd d).getD [] →
      execCase2 fuel σ nb sv its d inside = .ok (σ', q) → Inv M F τ σ →
      (∀ n i, ¬ InSet A n i → bitAt F n i = bitAt σ' n i) →
      ∃ τ', execCase2 fuel τ nb sv its d inside = .ok (τ', q) ∧ SameShape τ' σ' ∧
        Inv (M ++ CaseItem2.listMustW wd md its) F τ' σ' ∧
        Frame (CaseItem2.listMayW wd its ++ Stmt2.optMayW wd d) σ σ') ∧
    (∀ (ss : List Stmt2) (F σ τ σ' : SvState) (nb q : NbaQueue2) (M A : List BWin),
      Shaped wd σ → SameShape τ σ → Stmt2.listCombViol wd M A ss = none →
      execStmts2 fuel σ nb ss = .ok (σ', q) → Inv M F τ σ →
      (∀ n i, ¬ InSet A n i → bitAt F n i = bitAt σ' n i) →
      ∃ τ', execStmts2 fuel τ nb ss = .ok (τ', q) ∧ SameShape τ' σ' ∧
        Inv (M ++ Stmt2.listMustW wd ss) F τ' σ' ∧ Frame (Stmt2.listMayW wd ss) σ σ') := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun s F σ τ σ' nb q M A _ _ _ h1 => ?_,
      fun its d sv inside F σ τ σ' nb q M A md _ _ _ _ h1 => ?_,
      fun ss F σ τ σ' nb q M A _ _ _ h1 => ?_⟩
    · simp [execStmt2] at h1
    · cases its with
      | nil => simp [execCase2] at h1
      | cons it rest => cases it; simp [execCase2] at h1
    · simp [execStmts2] at h1
  | succ k ih =>
    obtain ⟨ihS, ihC, ihSs⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- execStmt2
    · intro s F σ τ σ' nb q M A hs hsh hv h1 hinv hF
      have hE := (eval_congr hsh hs k).1
      have hEs := (eval_congr hsh hs k).2
      have hR := resolveLhs2_congr (fuel := k) hsh hE
      cases s with
      | blockingAssign t e =>
        simp only [Stmt2.combViol] at hv
        simp only [execStmt2] at h1
        obtain ⟨v, hev, h1⟩ := Res.bind_eq_ok.mp h1
        cases t with
        | concat parts =>
          simp only at h1
          obtain ⟨ws, hws, h1⟩ := Res.bind_eq_ok.mp h1
          obtain ⟨σ'', hσ'', h1⟩ := Res.bind_eq_ok.mp h1
          simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          unfold writeConcatLhs2 at hσ''
          have hframe : Frame ((Lhs2.concat parts).mayW wd) σ σ'' := by
            obtain ⟨_, -, -, -, hout⟩ := go_rel _ ws σ σ σ'' _ (SameShape.refl σ) hσ''
            exact frame_of_wins (go_shape _ ws σ σ'' _ hσ'') (fun m j hm => (hout m j hm).2)
              (resolveConcatLhs2_sub hs _ ws hws)
          have hag := agree_of_viol hv hinv (hF_pre hF hframe)
          have hev' : evalExpr2 k τ e = .ok v := by rw [hE e hag.left, hev]
          have hws' : resolveConcatLhs2 k τ (.concat parts) = .ok ws := by
            rw [resolveConcatLhs2_congr (fun t ht => resolveLhs2_congr hsh hE t ht) _ hag.right, hws]
          obtain ⟨τ', hgo, hsh', hin, hout⟩ := go_rel _ ws τ σ σ'' _ hsh hσ''
          refine ⟨τ', ?_, hsh', ?_, hframe⟩
          · simp only [execStmt2, hev', Res.ok_bind, hws', writeConcatLhs2, hgo]
            rfl
          · simp only [Lhs2.mustW, Stmt2.mustW]
            intro m j
            by_cases hw : InSet ws m j
            · exact Or.inl (hin m j hw)
            · obtain ⟨e1, e2⟩ := hout m j hw
              rw [e1, e2]
              rcases hinv m j with h | ⟨h3, h4⟩
              · exact Or.inl h
              · exact Or.inr ⟨by simpa using h3, h4⟩
        | ident n0 =>
          simp only at h1
          obtain ⟨hev', τ', h2, h3, h4, h5⟩ := assign_sim hs hsh hinv hF hv hev h1 hE hR
          refine ⟨τ', ?_, h3, by simpa [Stmt2.mustW] using h4, by simpa [Stmt2.mayW] using h5⟩
          simp only [execStmt2, hev', Res.ok_bind]
          exact h2
        | slice n0 lo w =>
          simp only at h1
          obtain ⟨hev', τ', h2, h3, h4, h5⟩ := assign_sim hs hsh hinv hF hv hev h1 hE hR
          refine ⟨τ', ?_, h3, by simpa [Stmt2.mustW] using h4, by simpa [Stmt2.mayW] using h5⟩
          simp only [execStmt2, hev', Res.ok_bind]
          exact h2
        | index n0 idx ew =>
          simp only at h1
          obtain ⟨hev', τ', h2, h3, h4, h5⟩ := assign_sim hs hsh hinv hF hv hev h1 hE hR
          refine ⟨τ', ?_, h3, by simpa [Stmt2.mustW] using h4, by simpa [Stmt2.mayW] using h5⟩
          simp only [execStmt2, hev', Res.ok_bind]
          exact h2
      | nbaAssign t e =>
        simp only [Stmt2.combViol] at hv
        simp only [execStmt2] at h1
        obtain ⟨v, hev, h1⟩ := Res.bind_eq_ok.mp h1
        obtain ⟨⟨n, win⟩, hres, h1⟩ := Res.bind_eq_ok.mp h1
        cases win with
        | none =>
          simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          have hag := agree_of_viol hv hinv hF
          have hev' : evalExpr2 k τ e = .ok v := by rw [hE e hag.left, hev]
          have hres' : resolveLhs2 k τ t = .ok (n, none) := by rw [hR t hag.right, hres]
          refine ⟨τ, ?_, hsh, ?_, Frame.refl _ _⟩
          · simp only [execStmt2, hev', Res.ok_bind, hres']; rfl
          · simpa [Stmt2.mustW] using hinv
        | some lw =>
          obtain ⟨lo, w⟩ := lw
          simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          have hag := agree_of_viol hv hinv hF
          have hev' : evalExpr2 k τ e = .ok v := by rw [hE e hag.left, hev]
          have hres' : resolveLhs2 k τ t = .ok (n, some (lo, w)) := by rw [hR t hag.right, hres]
          refine ⟨τ, ?_, hsh, ?_, Frame.refl _ _⟩
          · simp only [execStmt2, hev', Res.ok_bind, hres']; rfl
          · simpa [Stmt2.mustW] using hinv
      | ifStmt c a b =>
        simp only [Stmt2.combViol, orElse_eq_none] at hv
        obtain ⟨hvc, hva, hvb⟩ := hv
        simp only [execStmt2] at h1
        obtain ⟨cv, hcv, h1⟩ := Res.bind_eq_ok.mp h1
        by_cases hct : cv.condTrue = true
        · rw [if_pos hct] at h1
          obtain ⟨τ', hτ', hsh', hinv', hfr⟩ := ihS a F σ τ σ' nb q M A hs hsh hva h1 hinv hF
          have hframe : Frame (a.mayW wd ++ Stmt2.optMayW wd b) σ σ' :=
            hfr.mono fun n i h => inSet_append.mpr (Or.inl h)
          have hpre := hF_pre hF hframe
          have hag := agree_of_viol hvc hinv hpre
          have hcv' : evalExpr2 k τ c = .ok cv := by rw [hE c hag, hcv]
          refine ⟨τ', ?_, hsh', ?_, by simpa [Stmt2.mayW] using hframe⟩
          · simp only [execStmt2, hcv', Res.ok_bind, if_pos hct]; exact hτ'
          · refine hinv'.mono fun n i hn => ?_
            cases b with
            | none => simp [Stmt2.mustW, Stmt2.optMustW] at hn
            | some s =>
              simp only [Stmt2.mustW, Stmt2.optMustW] at hn
              exact (inSet_interL.mp hn).1
        · rw [if_neg hct] at h1
          cases b with
          | none =>
            simp only [Res.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1
            have hpre := hF_pre hF (Frame.refl (a.mayW wd ++ Stmt2.optMayW wd none) σ)
            have hag := agree_of_viol hvc hinv hpre
            have hcv' : evalExpr2 k τ c = .ok cv := by rw [hE c hag, hcv]
            refine ⟨τ, ?_, hsh, ?_, Frame.refl _ _⟩
            · simp only [execStmt2, hcv', Res.ok_bind, if_neg hct]
            · simpa [Stmt2.mustW, Stmt2.optMustW] using hinv
          | some s' =>
            simp only [Stmt2.optCombViol] at hvb
            obtain ⟨τ', hτ', hsh', hinv', hfr⟩ := ihS s' F σ τ σ' nb q M A hs hsh hvb h1 hinv hF
            have hframe : Frame (a.mayW wd ++ Stmt2.optMayW wd (some s')) σ σ' :=
              hfr.mono fun n i h => inSet_append.mpr (Or.inr (by simpa [Stmt2.optMayW] using h))
            have hpre := hF_pre hF hframe
            have hag := agree_of_viol hvc hinv hpre
            have hcv' : evalExpr2 k τ c = .ok cv := by rw [hE c hag, hcv]
            refine ⟨τ', ?_, hsh', ?_, by simpa [Stmt2.mayW] using hframe⟩
            · simp only [execStmt2, hcv', Res.ok_bind, if_neg hct]; exact hτ'
            · refine hinv'.mono fun n i hn => ?_
              simp only [Stmt2.mustW, Stmt2.optMustW] at hn
              exact (inSet_interL.mp hn).2
      | block body =>
        simp only [Stmt2.combViol] at hv
        simp only [execStmt2] at h1
        obtain ⟨τ', hτ', hsh', hinv', hfr⟩ := ihSs body.toList F σ τ σ' nb q M A hs hsh hv h1 hinv hF
        refine ⟨τ', ?_, hsh', ?_, ?_⟩
        · simp only [execStmt2]; exact hτ'
        · simp only [Stmt2.mustW]; exact hinv'
        · simp only [Stmt2.mayW]; exact hfr
      | caseStmt subj its d inside chk =>
        simp only [Stmt2.combViol, orElse_eq_none] at hv
        obtain ⟨hvs, hvi⟩ := hv
        simp only [execStmt2] at h1
        obtain ⟨sv, hsv, h1⟩ := Res.bind_eq_ok.mp h1
        obtain ⟨τ', hτ', hsh', hinv', hfr⟩ := ihC its.toList d sv inside F σ τ σ' nb q M A
          ((Stmt2.optMustW wd d).getD []) hs hsh hvi rfl h1 hinv hF
        have hpre := hF_pre hF hfr
        have hag := agree_of_viol hvs hinv hpre
        have hsv' : evalExpr2 k τ subj = .ok sv := by rw [hE subj hag, hsv]
        refine ⟨τ', ?_, hsh', ?_, ?_⟩
        · simp only [execStmt2, hsv', Res.ok_bind]; exact hτ'
        · simp only [Stmt2.mustW]
          cases hd : Stmt2.optMustW wd d with
          | none => exact hinv'.mono fun n i hn => absurd hn inSet_nil
          | some md => rw [hd] at hinv'; exact hinv'
        · simp only [Stmt2.mayW]; exact hfr
      | unsupported k x =>
        simp [execStmt2] at h1
    -- execCase2
    · intro its d sv inside F σ τ σ' nb q M A md hs hsh hv hmd h1 hinv hF
      have hEs := (eval_congr hsh hs k).2
      cases its with
      | nil =>
        simp only [CaseItem2.listCombViol] at hv
        cases d with
        | none =>
          simp only [execCase2, Res.ok.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          simp only [Stmt2.optMustW, Option.getD_none] at hmd
          subst hmd
          refine ⟨τ, by simp [execCase2], hsh, ?_, Frame.refl _ _⟩
          simpa [CaseItem2.listMustW] using hinv
        | some s =>
          simp only [execCase2] at h1
          simp only [Stmt2.optCombViol] at hv
          obtain ⟨τ', hτ', hsh', hinv', hfr⟩ := ihS s F σ τ σ' nb q M A hs hsh hv h1 hinv hF
          simp only [Stmt2.optMustW, Option.getD_some] at hmd
          subst hmd
          refine ⟨τ', by simp only [execCase2]; exact hτ', hsh', ?_, ?_⟩
          · simpa [CaseItem2.listMustW] using hinv'
          · simpa [CaseItem2.listMayW, Stmt2.optMayW] using hfr
      | cons it rest =>
        obtain ⟨pats, body⟩ := it
        simp only [CaseItem2.listCombViol, orElse_eq_none] at hv
        obtain ⟨hvp, hvb, hvr⟩ := hv
        simp only [execCase2] at h1
        obtain ⟨pvs, hpvs, h1⟩ := Res.bind_eq_ok.mp h1
        by_cases hhit : (pvs.any fun pv => caseHit inside sv pv) = true
        · rw [if_pos hhit] at h1
          obtain ⟨τ', hτ', hsh', hinv', hfr⟩ := ihS body F σ τ σ' nb q M A hs hsh hvb h1 hinv hF
          have hframe : Frame (CaseItem2.listMayW wd (.mk pats body :: rest) ++ Stmt2.optMayW wd d)
              σ σ' := hfr.mono fun n i h => by
            simp only [CaseItem2.listMayW, CaseItem2.mayW, List.append_assoc]
            exact inSet_append.mpr (Or.inl h)
          have hpre := hF_pre hF hframe
          simp only [CaseItem2.listMayW, CaseItem2.mayW] at hpre
          have hag := agree_of_viol hvp hinv hpre
          have hpvs' : evalExprs2 k τ pats.toList = .ok pvs := by rw [hEs _ hag, hpvs]
          refine ⟨τ', ?_, hsh', ?_, hframe⟩
          · simp only [execCase2, hpvs', Res.ok_bind, if_pos hhit]; exact hτ'
          · exact hinv'.mono fun n i hn => by
              simpa [CaseItem2.mustW] using inSet_mustW_listMustW_left hn
        · rw [if_neg hhit] at h1
          obtain ⟨τ', hτ', hsh', hinv', hfr⟩ :=
            ihC rest d sv inside F σ τ σ' nb q M A md hs hsh hvr hmd h1 hinv hF
          have hframe : Frame (CaseItem2.listMayW wd (.mk pats body :: rest) ++ Stmt2.optMayW wd d)
              σ σ' := hfr.mono fun n i h => by
            simp only [CaseItem2.listMayW, CaseItem2.mayW, List.append_assoc]
            exact inSet_append.mpr (Or.inr h)
          have hpre := hF_pre hF hframe
          simp only [CaseItem2.listMayW, CaseItem2.mayW] at hpre
          have hag := agree_of_viol hvp hinv hpre
          have hpvs' : evalExprs2 k τ pats.toList = .ok pvs := by rw [hEs _ hag, hpvs]
          refine ⟨τ', ?_, hsh', hinv'.mono fun n i hn => inSet_mustW_listMustW_right hn, hframe⟩
          simp only [execCase2, hpvs', Res.ok_bind, if_neg hhit]; exact hτ'
    -- execStmts2
    · intro ss F σ τ σ' nb q M A hs hsh hv h1 hinv hF
      cases ss with
      | nil =>
        simp only [execStmts2, Res.ok.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨τ, by simp [execStmts2], hsh, by simpa [Stmt2.listMustW] using hinv,
          Frame.refl _ _⟩
      | cons s ss =>
        simp only [Stmt2.listCombViol, orElse_eq_none] at hv
        obtain ⟨hvs, hvss⟩ := hv
        simp only [execStmts2] at h1
        obtain ⟨⟨σ1, q1⟩, h1s, h1ss⟩ := Res.bind_eq_ok.mp h1
        -- the first run's frames (the second run taken equal to the first)
        obtain ⟨-, -, -, -, hfr1⟩ := ihS s σ1 σ σ σ1 nb q1 M (Stmt2.listMayW wd ss ++ A) hs
          (SameShape.refl σ) hvs h1s (fun _ _ => Or.inl rfl) (fun _ _ _ => rfl)
        have hs1 : Shaped wd σ1 := Shaped.of_sameShape hfr1.1 hs
        obtain ⟨-, -, -, -, hfr2⟩ := ihSs ss σ' σ1 σ1 σ' q1 q (M ++ s.mustW wd) A hs1
          (SameShape.refl σ1) hvss h1ss (fun _ _ => Or.inl rfl) (fun _ _ _ => rfl)
        -- the second run
        obtain ⟨τ1, hτ1, hsh1, hinv1, -⟩ :=
          ihS s F σ τ σ1 nb q1 M _ hs hsh hvs h1s hinv (hF_pre hF hfr2)
        obtain ⟨τ', hτ', hsh', hinv', -⟩ :=
          ihSs ss F σ1 τ1 σ' q1 q (M ++ s.mustW wd) A hs1 hsh1 hvss h1ss hinv1 hF
        refine ⟨τ', ?_, hsh', ?_, ?_⟩
        · simp only [execStmts2, hτ1, Res.ok_bind]; exact hτ'
        · simpa [Stmt2.listMustW, List.append_assoc] using hinv'
        · simpa [Stmt2.listMayW] using hfr1.trans hfr2

/-! ## The guard's theorem -/

/-- **An admitted body is its own fixpoint** (the guard's justification,
module docstring): on a shaped state, re-running a body the guard admits
on the state its own run produced reproduces that state and the same NBA
queue, at the same fuel. -/
theorem execStmt2_idem_of_admits {wd : String → Option Nat} {body : Stmt2}
    (hadm : body.combAdmits wd = true) {st r : SvState} {nb q : NbaQueue2} {f : Nat}
    (hs : Shaped wd st) (h : execStmt2 f st nb body = .ok (r, q)) :
    execStmt2 f r nb body = .ok (r, q) := by
  have hv : body.combViol wd [] [] = none := by
    simpa [Stmt2.combAdmits] using hadm
  -- the first run's frame: `r` has `st`'s shape
  obtain ⟨-, -, -, -, hfr⟩ := (sim wd f).1 body r st st r nb q [] [] hs (SameShape.refl st) hv h
    (fun _ _ => Or.inl rfl) (fun _ _ _ => rfl)
  have hshr : SameShape r st := hfr.1
  -- the second run, from `r`, related to the first by `Inv [] r r st`
  obtain ⟨τ', hτ', hsh', hinv', -⟩ := (sim wd f).1 body r st r r nb q [] [] hs hshr hv h
    (fun n i => Or.inr ⟨fun h => absurd h inSet_nil, rfl⟩) (fun _ _ _ => rfl)
  have hbits : ∀ n i, bitAt τ' n i = bitAt r n i := fun n i => by
    rcases hinv' n i with h | ⟨-, h⟩ <;> exact h
  have hτr : τ' = r := by
    have hsr : Shaped wd r := Shaped.of_sameShape hshr hs
    exact eq_of_lookup (hsh'.1) (hsh'.1 ▸ hsr.1) fun n => lookup_eq_of_bits hsh' (hbits n)
  rw [hτ', hτr]

end CombGuard

/-- **An admitted `always_comb` process is its own fixpoint**: on a shaped
state, re-running the process on the state its run produced changes
nothing. So the settle semantics' re-runs of the block itself are the
identity, and the one run an event-driven simulator makes per wake-up
(IEEE 1800-2023 §9.2.2.2.1: the block's own writes never wake it) already
leaves the block's settled value — the reason `combGuardProc` admits it.
Generalizes `runCombProcess2_alwaysComb_idem` (`Comb2Proc.lean`) from the
`SymState.selfReadFree` profile to every body `Stmt2.combAdmits` accepts. -/
theorem runCombProcess2_alwaysComb_idem_of_admits {wd : String → Option Nat} {body : Stmt2}
    (hadm : body.combAdmits wd = true) {st r : SvState} {f : Nat} (hs : CombGuard.Shaped wd st)
    (h : runCombProcess2 f st (.alwaysComb body) = .ok r) :
    runCombProcess2 f r (.alwaysComb body) = .ok r := by
  simp only [runCombProcess2] at h ⊢
  obtain ⟨⟨r', q⟩, hr, h⟩ := Res.bind_eq_ok.mp h
  cases q with
  | cons x xs => simp at h
  | nil =>
    simp only [Res.ok.injEq] at h
    subst h
    rw [CombGuard.execStmt2_idem_of_admits hadm hs hr]
    rfl

end LeanModels.Sv

/-! ## Axiom pins -/

/--
info: 'LeanModels.Sv.runCombProcess2_alwaysComb_idem_of_admits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.runCombProcess2_alwaysComb_idem_of_admits

/--
info: 'LeanModels.Sv.CombGuard.execStmt2_idem_of_admits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombGuard.execStmt2_idem_of_admits
