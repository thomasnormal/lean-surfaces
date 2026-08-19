import LeanModels.Python.VCGen

/-! # The dict-CONTENTS calculus — what a table SAYS, not where it lives

docs/backlog.md §L10 (b) split the transposition-table problem in two and
measured both halves: *"existing machinery for the heap FRAME, NEW calculus
for the table CONTENTS."* The frame half was already there — `PayloadBlind`'s
`Heap.swapAt` algebra and `Heap.get?_update_ne` say a write at one slot leaves
another alone. This module is the other half: `dictFind`/`dictStore` as an
algebra, and a table invariant preserved by it.

Nothing here mentions a program, a module literal or an interpreter run. It is
`Bool`- and `List`-level, elaborates in ~2 s, and serves any dict-using Python
— which is the point: a source refactor cannot rot it.

**The pieces.**

* §1–§1c — `keyEq` is an EQUIVALENCE on the hashable keys. Proved through a
  normal form (`keyNF`) rather than 81 constructor pairs: `keyEq a b` holds iff
  both keys have the same normal form, and `hashableKey` is exactly having one.
  Reflexivity, symmetry and transitivity then cost one line each — and all
  three are needed downstream, transitivity by exactly one lemma.
* §2 — the three `dictFind`/`dictStore` lemmas §L10 priced: find-after-store at
  an equal key, at an unequal key, and the SOUNDNESS of find (whatever a probe
  reads really is stored, under a key it cannot tell apart from its own).
* §3 — `Bracket`, `TableOK` and its two rules: preservation by a store and
  consumption by a find. The bracket schema is a pair of partial functions
  (what the KEY names, what an ENTRY carries), so the module commits to no
  particular entry shape.
* §4 — the same at a heap slot: `TableAt`, preserved by `heapStore` at the
  slot and by `Heap.update` anywhere else, and read through `heapGet` — the
  `.get(k, default)` shape, whose answer is the default or a bracketing entry.
* §5–§7 — pair keys `(k, depth)`, and §L10 (b)'s HARD SUB-CASE: a depth-`d`
  store is invisible to a depth-`e` probe for `d ≠ e`, at the dict and at the
  heap. It needs nothing about the positions or the entries; the key
  comparison decides it.
* §8 — `SubtreeWrites`: the recursion rule's table half. A child subtree is
  any number of bracketing stores at other depths, arbitrary writes elsewhere
  and ALLOCATIONS, and across it the parent's probe is STABLE and the
  invariant SURVIVES. `trans` makes a schedule of children one subtree, so a
  move fold needs no third theorem.

**Two things the proofs forced, both worth knowing before writing a schema.**

1. *A schema keyed on the plain-tuple spelling has a FALSE `KeyDetermined`.*
   `keyEq` erases the namedtuple class, so `(pos, d)` and `Key(pos, d)` address
   ONE slot and a schema that reads only `.tuple` would owe them two values.
   `pairKey` reads both spellings; `keyInt` likewise reads `True` as `1`.
2. *"Written post-finalizer only" needs no clause of its own.* §L10 stated the
   invariant with a second requirement — entries are written after the
   correction, never mid-fold. It is not a separate conjunct here: it is
   `TableOK.store`'s own hypothesis `S.Holds k v`, which a mid-fold `best`
   simply cannot discharge. The program's statement ORDER is what makes the
   hypothesis dischargeable; the calculus only has to demand it. -/

namespace LeanModels.Python

/-! ## §1 The key normal form

`keyEq` is Python `==` on hashable values, and it is not syntactic equality:
`True` is `1`, and a namedtuple compares as a plain tuple. `keyNF` is the
value a key COMPARES AS — `none` for the values that are equal to nothing at
all, themselves included. -/

inductive KeyNF where
  | unit
  | int (n : Int)
  | str (s : String)
  | tup (xs : List KeyNF)

mutual
  def keyNF : RVal → Option KeyNF
    | .none => some .unit
    | .bool b => some (.int (if b then 1 else 0))
    | .int n => some (.int n)
    | .str s => some (.str s)
    | .tuple xs => (keyNFList xs.toList).map .tup
    | .ntuple _ _ xs => (keyNFList xs.toList).map .tup
    | .listV _ => Option.none
    | .rangeV .. => Option.none
    | .ref _ => Option.none

  def keyNFList : List RVal → Option (List KeyNF)
    | [] => some []
    | v :: vs =>
      match keyNF v, keyNFList vs with
      | some n, some ns => some (n :: ns)
      | _, _ => Option.none
end

private theorem some_eq_map_tup {x : KeyNF} {o : Option (List KeyNF)} :
    (some x = o.map KeyNF.tup) ↔ ∃ l, o = some l ∧ x = KeyNF.tup l := by
  cases o <;> simp [eq_comm]

private theorem tup_lift {as bs : List RVal}
    (h : keyEqList as bs = true ↔ (keyNFList as).isSome = true ∧ keyNFList as = keyNFList bs) :
    keyEqList as bs = true ↔
      ((keyNFList as).map KeyNF.tup).isSome = true ∧
        (keyNFList as).map KeyNF.tup = (keyNFList bs).map KeyNF.tup := by
  rw [h]
  cases keyNFList as <;> cases keyNFList bs <;> simp

mutual
  theorem keyEq_iff_nf : (a b : RVal) →
      (keyEq a b = true ↔ (keyNF a).isSome = true ∧ keyNF a = keyNF b)
    | .none, b => by cases b <;> simp [keyEq, keyNF, some_eq_map_tup]
    | .bool x, b => by
        cases b
        case bool y => cases x <;> cases y <;> simp [keyEq, keyNF]
        all_goals simp [keyEq, keyNF, some_eq_map_tup]
    | .int n, b => by
        cases b
        case bool y => cases y <;> simp [keyEq, keyNF]
        all_goals simp [keyEq, keyNF, some_eq_map_tup]
    | .str s, b => by cases b <;> simp [keyEq, keyNF, some_eq_map_tup]
    | .listV _, b => by cases b <;> simp [keyEq, keyNF]
    | .rangeV .., b => by cases b <;> simp [keyEq, keyNF]
    | .ref _, b => by cases b <;> simp [keyEq, keyNF]
    | .tuple xs, b => by
        cases b
        case tuple ys => exact tup_lift (keyEqList_iff_nf xs.toList ys.toList)
        case ntuple _ _ ys => exact tup_lift (keyEqList_iff_nf xs.toList ys.toList)
        all_goals (simp only [keyEq, keyNF]; cases keyNFList xs.toList <;> simp)
    | .ntuple _ _ xs, b => by
        cases b
        case tuple ys => exact tup_lift (keyEqList_iff_nf xs.toList ys.toList)
        case ntuple _ _ ys => exact tup_lift (keyEqList_iff_nf xs.toList ys.toList)
        all_goals (simp only [keyEq, keyNF]; cases keyNFList xs.toList <;> simp)

  theorem keyEqList_iff_nf : (as bs : List RVal) →
      (keyEqList as bs = true ↔ (keyNFList as).isSome = true ∧ keyNFList as = keyNFList bs)
    | [], bs => by
        cases bs with
        | nil => simp [keyEqList, keyNFList]
        | cons b bs =>
          simp only [keyEqList, keyNFList]
          cases keyNF b <;> cases keyNFList bs <;> simp
    | a :: as, bs => by
        cases bs with
        | nil =>
          simp only [keyEqList, keyNFList]
          cases keyNF a <;> cases keyNFList as <;> simp
        | cons b bs =>
          have h1 := keyEq_iff_nf a b
          have h2 := keyEqList_iff_nf as bs
          simp only [keyEqList, keyNFList, Bool.and_eq_true, h1, h2]
          cases hna : keyNF a <;> cases hnb : keyNF b <;>
            cases hla : keyNFList as <;> cases hlb : keyNFList bs <;> simp
end

/-! ## §1b hashability IS having a normal form -/

mutual
  theorem hashableKey_iff_nf : (k : RVal) → (hashableKey k = true ↔ (keyNF k).isSome = true)
    | .none => by simp [hashableKey, keyNF]
    | .bool _ => by simp [hashableKey, keyNF]
    | .int _ => by simp [hashableKey, keyNF]
    | .str _ => by simp [hashableKey, keyNF]
    | .listV _ => by simp [hashableKey, keyNF]
    | .rangeV .. => by simp [hashableKey, keyNF]
    | .ref _ => by simp [hashableKey, keyNF]
    | .tuple xs => by
        simp only [hashableKey, keyNF]
        rw [hashableKeyList_iff_nf xs.toList]
        cases keyNFList xs.toList <;> simp
    | .ntuple _ _ xs => by
        simp only [hashableKey, keyNF]
        rw [hashableKeyList_iff_nf xs.toList]
        cases keyNFList xs.toList <;> simp

  theorem hashableKeyList_iff_nf : (ks : List RVal) →
      (hashableKeyList ks = true ↔ (keyNFList ks).isSome = true)
    | [] => by simp [hashableKeyList, keyNFList]
    | k :: ks => by
        simp only [hashableKeyList, keyNFList, Bool.and_eq_true,
          hashableKey_iff_nf k, hashableKeyList_iff_nf ks]
        cases keyNF k <;> cases keyNFList ks <;> simp
end

/-! ## §1c `keyEq` is an equivalence on the hashable keys -/

theorem keyEq_refl {k : RVal} (h : hashableKey k = true) : keyEq k k = true := by
  rw [keyEq_iff_nf k k]
  exact ⟨(hashableKey_iff_nf k).mp h, rfl⟩

theorem keyEq_symm (a b : RVal) : keyEq a b = keyEq b a := by
  rw [Bool.eq_iff_iff, keyEq_iff_nf a b, keyEq_iff_nf b a]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by rw [← h2]; exact h1, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨by rw [← h2]; exact h1, h2.symm⟩

theorem keyEq_trans {a b c : RVal} (h1 : keyEq a b = true) (h2 : keyEq b c = true) :
    keyEq a c = true := by
  rw [keyEq_iff_nf a b] at h1
  rw [keyEq_iff_nf b c] at h2
  rw [keyEq_iff_nf a c]
  exact ⟨h1.1, h1.2.trans h2.2⟩

/-- Only hashable values are `keyEq` to anything (the interpreter checks the
PROBE; this is why it need not re-check the stored key). -/
theorem hashableKey_of_keyEq {a b : RVal} (h : keyEq a b = true) : hashableKey a = true := by
  rw [keyEq_iff_nf a b] at h
  exact (hashableKey_iff_nf a).mpr h.1

/-- **The separation step**: a stored key equal to the written key is
`keyEq`-different from every probe the written key is different from. This is
the only place `dictFind_store_ne` needs `keyEq`'s symmetry AND transitivity,
and it is what keeps an unrelated entry unreadable after a write. -/
theorem keyEq_false_of_keyEq {k' k j : RVal} (h : keyEq k' k = true) (hj : keyEq k j = false) :
    keyEq k' j = false := by
  cases hc : keyEq k' j
  · rfl
  · rw [keyEq_symm k' k] at h
    have ht := keyEq_trans h hc
    simp [ht] at hj

/-! ## §2 The `dictFind`/`dictStore` algebra -/

@[simp] theorem dictFind_nil (k : RVal) : dictFind [] k = Option.none := rfl

theorem dictFind_cons (k' v' : RVal) (rest : List (RVal × RVal)) (k : RVal) :
    dictFind ((k', v') :: rest) k = if keyEq k' k then some v' else dictFind rest k := rfl

@[simp] theorem dictStore_nil (k v : RVal) : dictStore [] k v = ([(k, v)], true) := rfl

theorem dictStore_cons (k' v' : RVal) (rest : List (RVal × RVal)) (k v : RVal) :
    dictStore ((k', v') :: rest) k v =
      if keyEq k' k then ((k', v) :: rest, false)
      else ((k', v') :: (dictStore rest k v).1, (dictStore rest k v).2) := by
  simp only [dictStore]

/-- **Lemma 1 — find after store at the SAME key.** Hashability is the
interpreter's own precondition (`heapStore` checks it before calling
`dictStore`), and it is exactly what the append arm needs. -/
theorem dictFind_store_self : (es : List (RVal × RVal)) → {k : RVal} → (v : RVal) →
    hashableKey k = true → dictFind (dictStore es k v).1 k = some v
  | [], k, v, hk => by simp [dictFind_cons, keyEq_refl hk]
  | (k', v') :: rest, k, v, hk => by
      rw [dictStore_cons]
      by_cases h : keyEq k' k = true
      · simp [h, dictFind_cons]
      · rw [Bool.not_eq_true] at h
        simp only [h, Bool.false_eq_true, if_false, dictFind_cons]
        simp [dictFind_store_self rest v hk]

/-- **Lemma 2 — find after store at a DIFFERENT key.** The written key is
invisible to every probe it is `keyEq`-different from — including the entry it
REPLACED, whose stored key survives the write (`dictStore` keeps the old key
and the old position). -/
theorem dictFind_store_ne : (es : List (RVal × RVal)) → {k j : RVal} → (v : RVal) →
    keyEq k j = false → dictFind (dictStore es k v).1 j = dictFind es j
  | [], k, j, v, h => by simp [dictFind_cons, h]
  | (k', v') :: rest, k, j, v, h => by
      rw [dictStore_cons]
      by_cases hk : keyEq k' k = true
      · simp [hk, dictFind_cons, keyEq_false_of_keyEq hk h]
      · rw [Bool.not_eq_true] at hk
        simp only [hk, Bool.false_eq_true, if_false, dictFind_cons]
        by_cases hj : keyEq k' j = true
        · simp [hj]
        · rw [Bool.not_eq_true] at hj
          simp [hj, dictFind_store_ne rest v h]

/-- **Lemma 3 — find is SOUND.** Whatever `dictFind` answers really is stored,
under a key the probe cannot be told apart from. This is what lets an
invariant quantified over the ENTRIES transfer to whatever a probe reads. -/
theorem dictFind_sound : (es : List (RVal × RVal)) → {k v : RVal} →
    dictFind es k = some v → ∃ k', (k', v) ∈ es ∧ keyEq k' k = true
  | [], k, v, h => by simp [dictFind] at h
  | (k', v') :: rest, k, v, h => by
      rw [dictFind_cons] at h
      by_cases hk : keyEq k' k = true
      · rw [if_pos hk] at h
        exact ⟨k', by simp [Option.some.inj h], hk⟩
      · rw [Bool.not_eq_true] at hk
        rw [if_neg (by simp [hk])] at h
        obtain ⟨k'', hm, he⟩ := dictFind_sound rest h
        exact ⟨k'', by simp [hm], he⟩

/-- **The membership shape of a store**: every entry afterwards is an old
entry, or carries the written VALUE under a key `keyEq` to the written one.
The invariant's preservation reads off this. -/
theorem dictStore_mem : (es : List (RVal × RVal)) → {k v : RVal} → {p : RVal × RVal} →
    hashableKey k = true → p ∈ (dictStore es k v).1 →
    p ∈ es ∨ (p.2 = v ∧ keyEq p.1 k = true)
  | [], k, v, p, hk, h => by
      simp only [dictStore_nil, List.mem_singleton] at h
      exact Or.inr ⟨by simp [h], by simp [h, keyEq_refl hk]⟩
  | (k', v') :: rest, k, v, p, hk, h => by
      rw [dictStore_cons] at h
      by_cases hkk : keyEq k' k = true
      · simp only [hkk, if_true, List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inr ⟨rfl, hkk⟩
        · exact Or.inl (by simp [h])
      · rw [Bool.not_eq_true] at hkk
        simp only [hkk, Bool.false_eq_true, if_false, List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inl (by simp)
        · rcases dictStore_mem rest hk h with h' | h'
          · exact Or.inl (by simp [h'])
          · exact Or.inr h'

/-! ## §3 `TableOK` -/

/-- A **bracket schema** for a dict used as a memo table. -/
structure Bracket where
  /-- The single value the KEY determines (`none`: outside the domain). -/
  val : RVal → Option Int
  /-- The `(lower, upper)` a stored ENTRY carries (`none`: not an entry). -/
  bounds : RVal → Option (Int × Int)

/-- **Keys a dict cannot tell apart name the same value.** -/
def Bracket.KeyDetermined (S : Bracket) : Prop :=
  ∀ j k : RVal, keyEq j k = true → S.val j = S.val k

/-- One entry brackets its key's value. -/
def Bracket.Holds (S : Bracket) (k v : RVal) : Prop :=
  ∃ lo up m, S.bounds v = some (lo, up) ∧ S.val k = some m ∧ lo ≤ m ∧ m ≤ up

/-- **The table invariant**: every entry brackets the one value its key
determines. -/
def Bracket.TableOK (S : Bracket) (es : List (RVal × RVal)) : Prop :=
  ∀ p ∈ es, S.Holds p.1 p.2

theorem Bracket.TableOK.nil (S : Bracket) : S.TableOK [] := by
  intro p hp; simp at hp

/-- `Holds` transports along `keyEq` — the one use of `KeyDetermined`. -/
theorem Bracket.Holds.congr {S : Bracket} (hd : S.KeyDetermined) {j k v : RVal}
    (he : keyEq j k = true) (h : S.Holds k v) : S.Holds j v := by
  obtain ⟨lo, up, m, hb, hv, h1, h2⟩ := h
  exact ⟨lo, up, m, hb, (hd j k he).trans hv, h1, h2⟩

/-- **Preservation.** A store of a bracketing entry keeps the invariant —
including at the REPLACED entry, whose own (different, `keyEq`-equal) stored
key survives the write. -/
theorem Bracket.TableOK.store {S : Bracket} (hd : S.KeyDetermined)
    {es : List (RVal × RVal)} {k v : RVal} (hk : hashableKey k = true)
    (h : S.TableOK es) (hv : S.Holds k v) : S.TableOK (dictStore es k v).1 := by
  intro p hp
  rcases dictStore_mem es hk hp with hp' | ⟨hval, hkey⟩
  · exact h p hp'
  · exact (hval ▸ hv).congr hd hkey

/-- **Consumption.** Whatever a probe reads out of an OK table brackets the
probe's own value. -/
theorem Bracket.TableOK.find {S : Bracket} (hd : S.KeyDetermined)
    {es : List (RVal × RVal)} {k v : RVal}
    (h : S.TableOK es) (hf : dictFind es k = some v) : S.Holds k v := by
  obtain ⟨k', hm, he⟩ := dictFind_sound es hf
  exact ((h (k', v) hm).congr hd (by rw [keyEq_symm k' k] at he; exact he))

/-- The bracket, read off. -/
theorem Bracket.Holds.le {S : Bracket} {k v : RVal} {lo up m : Int}
    (h : S.Holds k v) (hb : S.bounds v = some (lo, up)) (hm : S.val k = some m) :
    lo ≤ m ∧ m ≤ up := by
  obtain ⟨lo', up', m', hb', hm', h1, h2⟩ := h
  rw [hb] at hb'; rw [hm] at hm'
  cases Option.some.inj hb'; cases Option.some.inj hm'
  exact ⟨h1, h2⟩

/-! ## §4 The table at a heap slot -/

/-- The dict at address `a` is a table satisfying `S`. -/
def Bracket.TableAt (S : Bracket) (h : Heap) (a : Addr) : Prop :=
  ∃ es ver, Heap.get? h a = some (.dict es ver) ∧ S.TableOK es.toList

/-- A successful `d[k] = v` on a dict checked the probe's hashability — so a
consumer never has to assume it. -/
theorem hashableKey_of_heapStore {h h' : Heap} {a : Addr} {k v : RVal}
    (hs : heapStore h a k v = .ok h') (es : Array (RVal × RVal)) (ver : Nat)
    (hg : Heap.get? h a = some (.dict es ver)) : hashableKey k = true := by
  by_cases hk : hashableKey k = true
  · exact hk
  · exfalso
    simp only [heapStore, hg, if_neg hk, keyRefusal] at hs
    split at hs <;> simp at hs

/-- **The heap-level preservation**: `self.tp_score[key] = entry`. -/
theorem Bracket.TableAt.store {S : Bracket} (hd : S.KeyDetermined)
    {h h' : Heap} {a : Addr} {k v : RVal}
    (ht : S.TableAt h a) (hv : S.Holds k v) (hs : heapStore h a k v = .ok h') :
    S.TableAt h' a := by
  obtain ⟨es, ver, hg, hok⟩ := ht
  have hk := hashableKey_of_heapStore hs es ver hg
  simp only [heapStore, hg, if_pos hk] at hs
  cases hds : dictStore es.toList k v with
  | mk es' grew =>
    rw [hds] at hs
    cases hu : Heap.update h a (.dict es'.toArray (if grew then ver + 1 else ver)) with
    | none => rw [hu] at hs; simp at hs
    | some h'' =>
      rw [hu] at hs
      cases Res.ok.inj hs
      refine ⟨es'.toArray, _, Heap.get?_update_self hu, ?_⟩
      have : es' = (dictStore es.toList k v).1 := by rw [hds]
      simpa [this] using hok.store hd hk hv

/-- **The frame**: a write at any OTHER slot leaves the table alone. This is
the half the existing `Heap` algebra already carried. -/
theorem Bracket.TableAt.update_ne {S : Bracket} {h h' : Heap} {a b : Addr} {o : Obj}
    (hne : b ≠ a) (hu : Heap.update h b o = some h') (ht : S.TableAt h a) :
    S.TableAt h' a := by
  obtain ⟨es, ver, hg, hok⟩ := ht
  exact ⟨es, ver, (Heap.get?_update_ne hu (Ne.symm hne)).trans hg, hok⟩

/-- **The probe.** `entry = d.get(key, default)` off an OK table: the answer is
the default, or it brackets the probe's value. Exactly the shipped
`self.tp_score.get((pos, depth), Entry(-MATE_UPPER, MATE_UPPER))`. -/
theorem Bracket.TableAt.get {S : Bracket} (hd : S.KeyDetermined)
    {h : Heap} {a : Addr} {k dflt v : RVal}
    (ht : S.TableAt h a) (hg : heapGet h a k dflt = .ok v) :
    v = dflt ∨ S.Holds k v := by
  obtain ⟨es, ver, hslot, hok⟩ := ht
  simp only [heapGet, hslot] at hg
  by_cases hk : hashableKey k = true
  · rw [if_pos hk] at hg
    cases hf : dictFind es.toList k with
    | none => exact Or.inl (by rw [hf] at hg; simpa using (Res.ok.inj hg).symm)
    | some w =>
      rw [hf] at hg
      have : v = w := by simpa using (Res.ok.inj hg).symm
      exact Or.inr (this ▸ hok.find hd hf)
  · rw [if_neg hk, keyRefusal] at hg
    exfalso; split at hg <;> simp at hg

/-! ## §5 Pair keys, and the depth separation -/

/-- A `(key, int)` pair key compares componentwise. -/
theorem keyEq_pair (p q : RVal) (d e : Int) :
    keyEq (.tuple #[p, .int d]) (.tuple #[q, .int e]) = (keyEq p q && d == e) := by
  simp [keyEq, keyEqList]

/-- **The hard sub-case, in one line**: a depth-`e` probe is `keyEq`-different
from EVERY depth-`d` key, whatever the positions, as soon as `d ≠ e`. -/
theorem keyEq_pair_depth_ne {p q : RVal} {d e : Int} (h : d ≠ e) :
    keyEq (.tuple #[p, .int d]) (.tuple #[q, .int e]) = false := by
  simp [keyEq_pair, h]


/-- **A depth-`d` store is invisible to a depth-`e` probe.** -/
theorem dictFind_store_depth_ne {es : List (RVal × RVal)} {p q : RVal} {d e : Int}
    (v : RVal) (h : d ≠ e) :
    dictFind (dictStore es (.tuple #[p, .int d]) v).1 (.tuple #[q, .int e])
      = dictFind es (.tuple #[q, .int e]) :=
  dictFind_store_ne es v (keyEq_pair_depth_ne h)

/-- **A table keyed entirely at depth `d` MISSES every depth-`e` probe.** -/
theorem dictFind_depth_ne : (es : List (RVal × RVal)) → {q : RVal} → {d e : Int} →
    (∀ p ∈ es, ∃ r, p.1 = .tuple #[r, .int d]) → d ≠ e →
    dictFind es (.tuple #[q, .int e]) = Option.none
  | [], q, d, e, _, _ => rfl
  | (k', v') :: rest, q, d, e, hes, hde => by
      obtain ⟨r, hr⟩ := hes (k', v') (by simp)
      simp only at hr
      rw [dictFind_cons, hr, keyEq_pair_depth_ne hde]
      simp only [Bool.false_eq_true, if_false]
      exact dictFind_depth_ne rest (fun p hp => hes p (by simp [hp])) hde

/-! ## §6 The transposition-table schema -/

/-- What an `int`-shaped key component means. `d[True]` IS `d[1]`, so a schema
that reads only `.int` has a FALSE `KeyDetermined`. -/
def keyInt : RVal → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | _ => Option.none

theorem keyInt_congr : (a b : RVal) → keyEq a b = true → keyInt a = keyInt b
  | .none, b, h => by cases b <;> simp_all [keyEq, keyInt]
  | .bool x, b, h => by cases b <;> cases x <;> simp_all [keyEq, keyInt]
  | .int _, b, h => by cases b <;> simp_all [keyEq, keyInt]
  | .str _, b, h => by cases b <;> simp_all [keyEq, keyInt]
  | .listV _, b, h => by cases b <;> simp_all [keyEq]
  | .rangeV .., b, h => by cases b <;> simp_all [keyEq]
  | .ref _, b, h => by cases b <;> simp_all [keyEq]
  | .tuple _, b, h => by cases b <;> simp_all [keyEq, keyInt]
  | .ntuple _ _ _, b, h => by cases b <;> simp_all [keyEq, keyInt]

theorem keyEqList_pair {x y : RVal} {ys : List RVal} (h : keyEqList [x, y] ys = true) :
    ∃ q e, ys = [q, e] ∧ keyEq x q = true ∧ keyEq y e = true := by
  rcases ys with _ | ⟨q, _ | ⟨e, _ | ⟨z, rest⟩⟩⟩
  · simp [keyEqList] at h
  · simp [keyEqList] at h
  · simp only [keyEqList, Bool.and_eq_true] at h
    exact ⟨q, e, rfl, h.1, h.2.1⟩
  · simp [keyEqList] at h

/-- A `(key, int)` pair key, read out of EITHER spelling — `keyEq` erases the
namedtuple class, so `(pos, d)` and `Key(pos, d)` address one slot. -/
def pairKeyList : List RVal → Option (RVal × Int)
  | [p, d] => (keyInt d).map (fun n => (p, n))
  | _ => Option.none

def pairKey : RVal → Option (RVal × Int)
  | .tuple xs => pairKeyList xs.toList
  | .ntuple _ _ xs => pairKeyList xs.toList
  | _ => Option.none

theorem pairKeyList_congr {l ys : List RVal} (h : keyEqList l ys = true)
    {p : RVal} {d : Int} (hj : pairKeyList l = some (p, d)) :
    ∃ q, pairKeyList ys = some (q, d) ∧ keyEq p q = true := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · simp [pairKeyList] at hj
  · simp [pairKeyList] at hj
  · simp only [pairKeyList, Option.map_eq_some_iff] at hj
    obtain ⟨n, hn, hpair⟩ := hj
    cases hpair
    obtain ⟨q, e, rfl, h1, h2⟩ := keyEqList_pair h
    exact ⟨q, by simp [pairKeyList, ← keyInt_congr y e h2, hn], h1⟩
  · simp [pairKeyList] at hj

/-- **The key congruence the table needs**: keys a dict cannot tell apart have
the same DEPTH and `keyEq`-equal positions. -/
theorem pairKey_congr {j k : RVal} (h : keyEq j k = true) {p : RVal} {d : Int}
    (hj : pairKey j = some (p, d)) :
    ∃ q, pairKey k = some (q, d) ∧ keyEq p q = true := by
  cases j
  case tuple xs =>
    cases k
    case tuple ys => exact pairKeyList_congr (by simpa [keyEq] using h) hj
    case ntuple _ _ ys => exact pairKeyList_congr (by simpa [keyEq] using h) hj
    all_goals simp [keyEq] at h
  case ntuple _ _ xs =>
    cases k
    case tuple ys => exact pairKeyList_congr (by simpa [keyEq] using h) hj
    case ntuple _ _ ys => exact pairKeyList_congr (by simpa [keyEq] using h) hj
    all_goals simp [keyEq] at h
  all_goals simp [pairKey] at hj

/-- An `Entry(lower, upper)` namedtuple, decoded. Written through `xs.toList`
rather than an ARRAY-LITERAL pattern on purpose: a `#[…]` argument pattern
costs the equational theorems outright (docs/backlog.md §L11 finding 1, §L12
finding 1), and a `List` pattern is `cons` and does not. -/
def entryBounds (v : RVal) : Option (Int × Int) :=
  match v with
  | .ntuple _ _ xs =>
    match xs.toList with
    | [.int lo, .int up] => some (lo, up)
    | _ => Option.none
  | _ => Option.none

/-- **The transposition-table schema**: a `(key, depth)` pair naming the one
value `V key depth`, an `Entry(lower, upper)` bracketing it. -/
def tpBracket (V : RVal → Int → Int) : Bracket where
  val := fun k => (pairKey k).map (fun pd => V pd.1 pd.2)
  bounds := entryBounds

/-- The schema IS key-determined, provided the value function is blind to the
difference between `keyEq`-equal positions. -/
theorem tpBracket_keyDetermined {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d) : (tpBracket V).KeyDetermined := by
  intro j k he
  simp only [tpBracket]
  cases hjk : pairKey j with
  | none =>
    cases hkk : pairKey k with
    | none => simp
    | some qd =>
      obtain ⟨q', d'⟩ := qd
      obtain ⟨r, hr, _⟩ := pairKey_congr (by rw [keyEq_symm k j]; exact he) hkk
      rw [hjk] at hr; simp at hr
  | some pd =>
    obtain ⟨p, d⟩ := pd
    obtain ⟨q, hq, hpq⟩ := pairKey_congr he hjk
    rw [hq]; simp [hV p q d hpq]

/-! ### Why `pairKey` reads BOTH spellings — the schema that does not

A schema keyed on the plain tuple with an `.int` depth looks right and is
UNSOUND, and the two theorems below are the witnesses rather than a warning.
`keyEq` erases the namedtuple class and reads `True` as `1`, so `(p, 1)`,
`Key(p, 1)` and `(p, True)` are ONE dict slot — a schema that answers `some`
for the first and `none` for the others would owe that slot two values, and
`KeyDetermined` is exactly what refuses it. -/

/-- The narrow reading: plain tuple, `.int` depth, nothing else. -/
def narrowVal (V : RVal → Int → Int) (k : RVal) : Option Int :=
  match k with
  | .tuple xs =>
    match xs.toList with
    | [p, .int d] => some (V p d)
    | _ => Option.none
  | _ => Option.none

/-- The narrow schema. -/
def narrowBracket (V : RVal → Int → Int) : Bracket where
  val := narrowVal V
  bounds := entryBounds

/-- **The namedtuple spelling refutes it**, for every value function. -/
theorem narrowBracket_not_keyDetermined (V : RVal → Int → Int) :
    ¬ (narrowBracket V).KeyDetermined := by
  intro h
  have := h (.tuple #[.str "p", .int 1])
    (.ntuple "Key" #["pos", "depth"] #[.str "p", .int 1]) (by decide)
  simp [narrowBracket, narrowVal] at this

/-- **And so does the bool spelling** — `d[(p, True)]` IS `d[(p, 1)]`. -/
theorem narrowBracket_not_keyDetermined_bool (V : RVal → Int → Int) :
    ¬ (narrowBracket V).KeyDetermined := by
  intro h
  have := h (.tuple #[.str "p", .int 1]) (.tuple #[.str "p", .bool true]) (by decide)
  simp [narrowBracket, narrowVal] at this

/-! ## §7 The hard sub-case, at the heap -/

/-- **A depth-`d` store is invisible to a depth-`e` probe, through the HEAP.**
This is §L10 (b)'s hard sub-case — a depth-2 call probing entries a depth-1
child wrote — and it needs nothing about the positions, the entries or the
rest of the table: the key comparison decides it. -/
theorem heapGet_heapStore_depth_ne {h h' : Heap} {a : Addr} {p q : RVal} {d e : Int}
    {v dflt : RVal} (hne : d ≠ e) (hq : hashableKey q = true)
    (hs : heapStore h a (.tuple #[p, .int d]) v = .ok h') :
    heapGet h' a (.tuple #[q, .int e]) dflt = heapGet h a (.tuple #[q, .int e]) dflt := by
  have hqk : hashableKey (.tuple #[q, .int e]) = true := by
    simp [hashableKey, hashableKeyList, hq]
  cases hslot : Heap.get? h a with
  | none => rw [heapStore, hslot] at hs; simp at hs
  | some o =>
    cases o
    case dict es ver =>
      have hk : hashableKey (RVal.tuple #[p, .int d]) = true :=
        hashableKey_of_heapStore hs es ver hslot
      simp only [heapStore, hslot, if_pos hk] at hs
      cases hds : dictStore es.toList (.tuple #[p, .int d]) v with
      | mk es' grew =>
        rw [hds] at hs
        cases hu : Heap.update h a (.dict es'.toArray (if grew then ver + 1 else ver)) with
        | none => rw [hu] at hs; simp at hs
        | some h'' =>
          rw [hu] at hs
          cases Res.ok.inj hs
          simp only [heapGet, Heap.get?_update_self hu, hslot, if_pos hqk]
          have hes : es' = (dictStore es.toList (.tuple #[p, .int d]) v).1 := by rw [hds]
          rw [hes, dictFind_store_depth_ne v hne]
    all_goals (rw [heapStore, hslot] at hs; simp [asInt] at hs)

/-! ## §8 The recursion rule's table half -/

/-- **What a child subtree does to the parent's table**, as far as the parent
can see: any number of steps, each either

* a bracketing store at the table's OWN slot, keyed at a depth `≠ e` (a child
  searching at `d - 1` while the parent probes at `d`),
* a write at ANY OTHER slot — the node counter, `tp_move`, a mutated list, or
* an ALLOCATION, at a fresh address that is by construction not the table's.

The first two arms are §L10 (b)'s split: the second is carried by the existing
`Heap` frame algebra, the first is what the dict-contents calculus above adds.
The third arm is not decoration — a child call of `Searcher.bound` allocates
on every visit (the `moves()` generator object, the `sorted(...)` list), and
`Heap.update` cannot describe an append. Without it the relation is true and
UNINHABITABLE at the shipped code, and `probe_stable`/`tableAt` would be
theorems about a subtree that does not exist. -/
inductive Bracket.SubtreeWrites (S : Bracket) (a : Addr) (e : Int) : Heap → Heap → Prop
  | nil {h : Heap} : S.SubtreeWrites a e h h
  | store {h h₁ h₂ : Heap} {p v : RVal} {d : Int} :
      d ≠ e → S.Holds (.tuple #[p, .int d]) v →
      heapStore h a (.tuple #[p, .int d]) v = .ok h₁ →
      S.SubtreeWrites a e h₁ h₂ → S.SubtreeWrites a e h h₂
  | other {h h₁ h₂ : Heap} {b : Addr} {o : Obj} :
      b ≠ a → Heap.update h b o = some h₁ →
      S.SubtreeWrites a e h₁ h₂ → S.SubtreeWrites a e h h₂
  /-- The fresh address is `h.size`, and the side condition `a ≠ b` says the
  table is not it — which a live table discharges outright. It is a real
  condition and not a formality: at `a = h.size` the probe's answer changes
  from `.unsupported` (dangling) to whatever was appended. -/
  | alloc {h h₁ h₂ : Heap} {o : Obj} {b : Addr} :
      Heap.alloc h o = (h₁, b) → a ≠ b →
      S.SubtreeWrites a e h₁ h₂ → S.SubtreeWrites a e h h₂

/-- **The parent's probe is blind to the whole child subtree.** This is the
statement a depth-`d` gate needs about its depth-`(d-1)` recursive calls, and
it holds for ANY positions, entries and table contents. -/
theorem Bracket.SubtreeWrites.probe_stable {S : Bracket} {a : Addr} {e : Int}
    {q dflt : RVal} (hq : hashableKey q = true) :
    {h h' : Heap} → S.SubtreeWrites a e h h' →
    heapGet h' a (.tuple #[q, .int e]) dflt = heapGet h a (.tuple #[q, .int e]) dflt
  | _, _, .nil => rfl
  | h, h', .store hne _ hs rest => by
      rw [probe_stable hq rest, heapGet_heapStore_depth_ne hne hq hs]
  | h, h', .other hb hu rest => by
      have hqk : hashableKey (RVal.tuple #[q, .int e]) = true := by
        simp [hashableKey, hashableKeyList, hq]
      rw [probe_stable hq rest]
      simp only [heapGet, Heap.get?_update_ne hu (Ne.symm hb), if_pos hqk]
  | h, h', .alloc ha hab rest => by
      have ih := probe_stable (dflt := dflt) hq rest
      have hqk : hashableKey (RVal.tuple #[q, .int e]) = true := by
        simp [hashableKey, hashableKeyList, hq]
      simp only [Heap.alloc, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      rw [ih]
      simp only [heapGet, Heap.get?_push_ne hab, if_pos hqk]

/-- **And the invariant survives it.** Together with `probe_stable` this is the
whole of what a depth-`d` statement has to know about its children's effect on
the table.

Both new arms read the slot through `Heap.get?_push_ne` rather than through
its older sibling `Heap.get?_push_of_get?`: the probe's arm needs the extra
generality (a probe carries no liveness hypothesis), and this one needs the
CHOICE-FREEDOM — the sibling goes through `Array.getElem?_push`, which costs
`Classical.choice`. -/
theorem Bracket.SubtreeWrites.tableAt {S : Bracket} (hd : S.KeyDetermined) {a : Addr} {e : Int} :
    {h h' : Heap} → S.SubtreeWrites a e h h' → S.TableAt h a → S.TableAt h' a
  | _, _, .nil, ht => ht
  | _, _, .store _ hv hs rest, ht => tableAt hd rest (ht.store hd hv hs)
  | _, _, .other hb hu rest, ht => tableAt hd rest (ht.update_ne hb hu)
  | _, _, .alloc ha _ rest, ht => by
      refine tableAt hd rest ?_
      obtain ⟨es, ver, hg, hok⟩ := ht
      simp only [Heap.alloc, Prod.mk.injEq] at ha
      obtain ⟨rfl, -⟩ := ha
      exact ⟨es, ver, (Heap.get?_push_ne (Nat.ne_of_lt (Heap.lt_size_of_get? hg))).trans hg, hok⟩

/-- **A schedule's worth of children is ONE subtree.** The relation is already
a chain, so composing the fold's rounds costs an append and no new reasoning:
this is why threading the table through the move loop needs nothing beyond the
two theorems above. -/
theorem Bracket.SubtreeWrites.trans {S : Bracket} {a : Addr} {e : Int} :
    {h h₁ h₂ : Heap} → S.SubtreeWrites a e h h₁ → S.SubtreeWrites a e h₁ h₂ →
    S.SubtreeWrites a e h h₂
  | _, _, _, .nil, k => k
  | _, _, _, .store hne hv hs rest, k => .store hne hv hs (trans rest k)
  | _, _, _, .other hb hu rest, k => .other hb hu (trans rest k)
  | _, _, _, .alloc ha hab rest, k => .alloc ha hab (trans rest k)

/-! ## §9 Non-vacuity -/

private def kA : RVal := .tuple #[.str "posA", .int 1]
private def kB : RVal := .tuple #[.str "posB", .int 1]
private def kA2 : RVal := .tuple #[.str "posA", .int 2]
private def entryV (lo up : Int) : RVal := .ntuple "Entry" #["lower", "upper"] #[.int lo, .int up]

/-! A depth-2 probe misses a table written entirely at depth 1 — and the
depth-1 probe still hits. -/
#guard dictFind (dictStore [] kA (entryV 3 7)).1 kA2 == Option.none
#guard dictFind (dictStore [] kA (entryV 3 7)).1 kA == some (entryV 3 7)
#guard dictFind (dictStore (dictStore [] kA (entryV 3 7)).1 kB (entryV 1 9)).1 kA2 == Option.none

/-! The namedtuple spelling of a key addresses the SAME slot as the tuple —
the reason `pairKey` reads both. -/
#guard dictFind (dictStore [] kA (entryV 3 7)).1
    (.ntuple "Key" #["pos", "depth"] #[.str "posA", .int 1]) == some (entryV 3 7)
#guard (pairKey (.ntuple "Key" #["pos", "depth"] #[.str "posA", .int 1])).isSome

/-! `True` IS `1` as a depth — the reason `keyInt` reads bools. -/
#guard keyEq (.tuple #[.str "p", .int 1]) (.tuple #[.str "p", .bool true])
#guard pairKey (.tuple #[.str "p", .bool true]) == some (.str "p", 1)

/-! The entry decoder, and a bracket that holds. -/
#guard entryBounds (entryV 3 7) == some (3, 7)
#guard entryBounds (.int 3) == Option.none

/-! **The allocation arm, and why its side condition is real.** A one-slot heap
holding the table: appending leaves the probe's answer alone at slot `0`, and
the fresh address is `1` — where the same append turns a dangling read into a
live one. `a ≠ b` is that difference, not a formality. -/
private def hTab : Heap := #[.dict #[(kA, entryV 3 7)] 1]

#guard heapGet hTab 0 kA (.int 0) == Res.ok (entryV 3 7)
#guard heapGet (Heap.alloc hTab (.list #[])).1 0 kA (.int 0) == Res.ok (entryV 3 7)
#guard (Heap.alloc hTab (.list #[])).2 == 1
#guard Heap.get? hTab 1 == Option.none
#guard (Heap.get? (Heap.alloc hTab (.list #[])).1 1).isSome
#guard Heap.update hTab 1 (.list #[]) == Option.none

#print axioms keyEq_refl
#print axioms keyEq_trans
#print axioms dictFind_store_self
#print axioms dictFind_store_ne
#print axioms dictFind_sound
#print axioms Bracket.TableOK.store
#print axioms Bracket.TableOK.find
#print axioms Bracket.TableAt.store
#print axioms Bracket.TableAt.get
#print axioms tpBracket_keyDetermined
#print axioms heapGet_heapStore_depth_ne
#print axioms Bracket.SubtreeWrites.probe_stable
#print axioms Bracket.SubtreeWrites.tableAt
#print axioms Bracket.SubtreeWrites.trans
#print axioms narrowBracket_not_keyDetermined

end LeanModels.Python
