/-
**The Lean-structures census's experiment file** — `docs/lean-structures-census.md`
is its report, and `docs/mvcgen-pilot.lean` is its sibling.

**OUT OF THE PINNED BUILD BY CONSTRUCTION.** `lakefile.toml`'s globs are the
`LeanModels` lib root and `Examples.+`; nothing under `docs/` is either, so
`lake build` never sees this file and no other lane is affected by it. Run it
directly:

    lake env lean docs/lean-structures-census.lean

Zero `sorry`. Zero `native_decide`. Zero `bv_decide` — **that is deliberate**:
`bv_decide` adds a per-theorem `_native` axiom whenever its SAT solver runs
(§8 of the report has the exact axiom names), so its runs are the report's
SUBJECT and are quoted there rather than landed here. Every theorem below is
checked by `#print axioms`.
-/
import LeanModels.Python.Semantics
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Do
import Std.Tactic.Do

open Std.Do LeanModels LeanModels.Python
set_option mvcgen.warning false
set_option linter.unusedSimpArgs false

namespace StructuresCensus

/-! # §1 `grind` — the tactic is adopted, the REGISTRY is not, and the
     composition point is one `macro_rules` line

`grind` is at the pin and the tree already calls it 67 times in 22 files.
`@[grind]`, `@[grind =]`, `@[grind intro]`, `@[grind cases]`, `@[grind ext]`
— the registry — is used **zero** times.

The composition with `@[spec]` is not a conflict and not a merge: `mvcgen`
discharges its VCs by calling `mvcgen_trivial`, which core declares as
delegating to the user-extensible `mvcgen_trivial_extensible`. Wiring `grind`
there makes the two registries compose with NO tactic script at the call
site — `@[spec]` says what `mvcgen` APPLIES, `@[grind]` says what CLOSES what
is left. -/

macro_rules | `(tactic| mvcgen_trivial_extensible) => `(tactic| grind)

/-! ## §1.1 The substrate, transcribed from the mvcgen pilot (§4 there). -/

abbrev Loud := Unit ⊕ String
abbrev PM (σ : Type) := ExceptT PyErr (StateT σ (Except Loud))
abbrev PS (σ : Type) : PostShape := .except PyErr (.arg σ (.except Loud .pure))
abbrev FM := PM FrameState

def loud (m : String) : FM α := fun _ => .error (.inr m)

def liftRes : Res RVal → FM RVal
  | .ok v          => pure v
  | .exn e         => throw e
  | .timeout       => fun _ => .error (.inl ())
  | .unsupported m => loud m

def resolve (st : FrameState) (id : String) : Option RVal :=
  match Env.lookup st.locals id with
  | some v      => some v
  | Option.none => Env.lookup st.world.globals id

def lookupName (id : String) : FM RVal := do
  let st ← get
  match resolve st id with
  | some v      => pure v
  | Option.none => throw (.nameError id)

def indexM (c k : RVal) : FM RVal := do
  let st ← get
  liftRes (indexValH st.world.heap c k)

def binOpM (op : BinOp) (a b : RVal) : FM RVal := liftRes (evalBinOp op a b)

def bindLocal (n : String) (v : RVal) : FM Unit :=
  modify fun st => { st with locals := Env.set st.locals n v }

@[spec] theorem lookupName_spec (id : String) (st0 : FrameState)
    (h : (resolve st0 id).isSome) :
    ⦃fun st => ⌜st = st0⌝⦄ lookupName id
    ⦃⇓ r => fun st => ⌜resolve st0 id = some r ∧ st = st0⌝⦄ := by
  mvcgen [lookupName]

@[spec] theorem indexM_spec (c k : RVal) (st0 : FrameState)
    (h : ∃ v, indexValH st0.world.heap c k = .ok v) :
    ⦃fun st => ⌜st = st0⌝⦄ indexM c k
    ⦃⇓ r => fun st => ⌜indexValH st0.world.heap c k = .ok r ∧ st = st0⌝⦄ := by
  mvcgen [indexM, liftRes]

@[spec] theorem binOpM_spec (op : BinOp) (a b : RVal) (st0 : FrameState)
    (h : ∃ v, evalBinOp op a b = .ok v) :
    ⦃fun st => ⌜st = st0⌝⦄ binOpM op a b
    ⦃⇓ r => fun st => ⌜evalBinOp op a b = .ok r ∧ st = st0⌝⦄ := by
  mvcgen [binOpM, liftRes]

@[spec] theorem bindLocal_spec (n : String) (v : RVal) (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ bindLocal n v
    ⦃⇓ _ => fun st => ⌜st = { st0 with locals := Env.set st0.locals n v }⌝⦄ := by
  mvcgen [bindLocal]

def evalM : Expr → FM RVal
  | .name id _       => lookupName id
  | .subscript r k _ => do let c ← evalM r; let x ← evalM k; indexM c x
  | .binOp l op r _  => do let a ← evalM l; let b ← evalM r; binOpM op a b
  | _                => loud "outside the twin's slice"

def execM : Stmt → FM Unit
  | .assign tgts rhs _ =>
      match tgts.toList with
      | [.name n _] => do let v ← evalM rhs; bindLocal n v
      | _           => loud "outside the twin's slice"
  | _ => loud "outside the twin's slice"

def vlScoreLit (a b c d e f g h i k l m n : Span) : Stmt :=
    .assign #[.name "score" a]
      (.binOp (.subscript (.subscript (.name "pst" b) (.name "p" c) d) (.name "j" e) f)
        .sub
        (.subscript (.subscript (.name "pst" g) (.name "p" h) i) (.name "i" k) l) m) n

/-! ## §1.2 GATE 3 with the registries WIRED — no closing tactic at all.

The mvcgen pilot's `value_scores_M` ended in three lines
(`all_goals intros` / `all_goals subst_vars` / `all_goals simp_all [8 lemmas]`).
With `grind` wired into `mvcgen_trivial_extensible`, `mvcgen` closes the gate
by itself: the proof is the eight `have`s and the `mvcgen` call, and NOTHING
follows it. Measured: bare `mvcgen` leaves **12 VCs** (`vc1`…`vc12`); wired,
it leaves **0**. Same axioms either way. -/

theorem value_scores_M (w : World) (e : REnv) (pa : Addr) (pc : String)
    (es : Array (RVal × RVal)) (sv : Nat) (xs : Array RVal) (i j zi zj : Int)
    (sa sb sc sd se sf sg sh si sk sl sm sn : Span)
    (hnp : Env.lookup e "pst" = Option.none)
    (hp : Env.lookup e "p" = some (.str pc))
    (hei : Env.lookup e "i" = some (.int i))
    (hej : Env.lookup e "j" = some (.int j))
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es sv))
    (hrow : dictFind es.toList (.str pc) = some (.tuple xs))
    (hsz : xs.size = 120)
    (hi : 0 ≤ i) (hi' : i < 120) (hj : 0 ≤ j) (hj' : j < 120)
    (hxi : xs[i.toNat]?.getD .none = .int zi)
    (hxj : xs[j.toNat]?.getD .none = .int zj) :
    ⦃fun st => ⌜st = ⟨w, e⟩⌝⦄
      execM (vlScoreLit sa sb sc sd se sf sg sh si sk sl sm sn)
    ⦃⇓ _ => fun st => ⌜st = ⟨w, Env.set e "score" (.int (zj - zi))⟩⌝⦄ := by
  have hpst : resolve ⟨w, e⟩ "pst" = some (.ref pa) := by simp [resolve, hnp, hg]
  have hpp  : resolve ⟨w, e⟩ "p" = some (.str pc) := by simp [resolve, hp]
  have hii  : resolve ⟨w, e⟩ "i" = some (.int i) := by simp [resolve, hei]
  have hjj  : resolve ⟨w, e⟩ "j" = some (.int j) := by simp [resolve, hej]
  have hrowIdx : indexValH w.heap (.ref pa) (.str pc) = .ok (.tuple xs) := by
    simp [indexValH, heapIndex, hd, hrow, hashableKey]
  have hjIdx : indexValH w.heap (.tuple xs) (.int j) = .ok (.int zj) := by
    simp [indexValH, indexVal, asInt, normIndex, hsz, hxj,
      if_neg (show ¬ j < 0 by omega), if_pos (show (0 ≤ j ∧ j < (120:Int)) from ⟨hj, hj'⟩)]
  have hiIdx : indexValH w.heap (.tuple xs) (.int i) = .ok (.int zi) := by
    simp [indexValH, indexVal, asInt, normIndex, hsz, hxi,
      if_neg (show ¬ i < 0 by omega), if_pos (show (0 ≤ i ∧ i < (120:Int)) from ⟨hi, hi'⟩)]
  have hsub : evalBinOp .sub (.int zj) (.int zi) = .ok (.int (zj - zi)) := rfl
  mvcgen [execM, evalM, vlScoreLit]

#print axioms value_scores_M
#print axioms lookupName_spec

/-! ## §1.3 WHERE `grind` STOPS — the residue-spelling law survives it.

The mvcgen pilot recorded *"computed-shape / residue-spelling PERSISTS
verbatim"*. This is that row, measured in `grind`'s vocabulary: `grind`
closes the two residues that are LOOKUPS, and fails on the two that are
COMPUTATIONS. -/

section Residues
variable (w : World) (e : REnv) (pa : Addr) (pc : String)
  (es : Array (RVal × RVal)) (sv : Nat) (xs : Array RVal) (i j zi zj : Int)

/-- CLOSES: name resolution through the two-level lookup. -/
theorem resid_resolve (hnp : Env.lookup e "pst" = Option.none)
    (hg : Env.lookup w.globals "pst" = some (.ref pa)) :
    resolve ⟨w, e⟩ "pst" = some (.ref pa) := by grind [resolve]

/-- CLOSES: the heap-indexing residue. -/
theorem resid_heap (hd : Heap.get? w.heap pa = some (.dict es sv))
    (hrow : dictFind es.toList (.str pc) = some (.tuple xs)) :
    indexValH w.heap (.ref pa) (.str pc) = .ok (.tuple xs) := by
  grind [indexValH, heapIndex, hashableKey]

/-- FAILS under `grind`, `grind [= evalBinOp]`, `simp [evalBinOp]` and
`unfold evalBinOp; grind` alike — and the pin's NEW `cbv` tactic closes it
in one token, as does `rfl`. This is §10's finding. -/
theorem resid_binop_cbv : evalBinOp .sub (.int zj) (.int zi) = .ok (.int (zj - zi)) := by
  cbv

/-- The computed-shape tuple index: `grind` fails with and without a `simp only`
prelude; only the hand-picked `simp` carrying the `if_neg`/`if_pos` DECISIONS
closes it. The law and its tactic survive `grind` intact. -/
theorem resid_index (hsz : xs.size = 120) (hj : 0 ≤ j) (hj' : j < 120)
    (hxj : xs[j.toNat]?.getD .none = .int zj) :
    indexValH w.heap (.tuple xs) (.int j) = .ok (.int zj) := by
  simp [indexValH, indexVal, asInt, normIndex, hsz, hxj,
    if_neg (show ¬ j < 0 by omega), if_pos (show (0 ≤ j ∧ j < (120:Int)) from ⟨hj, hj'⟩)]

end Residues

#print axioms resid_resolve
#print axioms resid_heap
#print axioms resid_binop_cbv
#print axioms resid_index

/-! # §2 `EStateM` — the corrected layer order, SHIPPED, with 7 free spec lemmas

`docs/family-architecture.md` §3.4's substrate is `ExceptT ρ (StateT W Halt)`.
Core ships `EStateM ε σ` with the WPMonad shape `.except ε (.arg σ .pure)` —
**that same order, already instantiated** — plus seven `@[spec]` lemmas.
Core's own docstring: *"exceptions do not automatically roll back the state"*,
which is `Run`'s `.exn` rule (docs/memory-model.md v2) verbatim. -/

namespace E2
variable {ε σ α L : Type}

/-- The two unfoldings, side by side. They are NOT the same type: `Result` is
an inductive, the other a product of a sum — the report quotes the failed
`rfl`. The ISO is what holds, and it is below. -/
example : EStateM ε σ α = (σ → EStateM.Result ε σ α) := rfl
example : ExceptT ε (StateT σ Id) α = (σ → (Except ε α × σ)) := rfl

/-- The error barrel SEES the state — the corrected order, shipped. -/
example : ExceptConds (.except ε (.arg σ .pure)) = ((ε → σ → ULift Prop) × Unit) := rfl
/-- The WRONG order, for contrast: the state is gone in the barrel. -/
example : ExceptConds (.arg σ (.except ε .pure)) = ((ε → ULift Prop) × Unit) := rfl

#synth WPMonad (EStateM ε σ) (.except ε (.arg σ .pure))

/-- `Run`'s state-RETAINING core (its `.ok`/`.exn` arms). -/
inductive Run2 (ε σ α : Type) where
  | ok  (state : σ) (value : α)
  | exn (state : σ) (error : ε)

def ofRun2 (r : σ → Run2 ε σ α) : EStateM ε σ α := fun s =>
  match r s with
  | .ok s' a  => .ok a s'
  | .exn s' e => .error e s'

def toRun2 (x : EStateM ε σ α) : σ → Run2 ε σ α := fun s =>
  match x s with
  | .ok a s'    => .ok s' a
  | .error e s' => .exn s' e

theorem toRun2_ofRun2 (r : σ → Run2 ε σ α) : toRun2 (ofRun2 r) = r := by
  funext s; simp only [toRun2, ofRun2]; cases r s <;> rfl

theorem ofRun2_toRun2 (x : EStateM ε σ α) : ofRun2 (toRun2 x) = x := by
  funext s; simp only [toRun2, ofRun2]; cases x s <;> rfl

/-- **The mvcgen pilot's §1.4 BUG DOES NOT ARISE ON EStateM.** There, a bare
polymorphic `throw` in `StateT W (Except ε)` left four metavariable goals and
the declaration was rejected for universe metavariables, because
`Spec.throw_Except` is declared under an undetermined `variable {m} {ps}`.
`Spec.throw_EStateM`'s conclusion determines everything, so the bare `throw`
below simply works. -/
abbrev M2 := EStateM String Nat

def bareThrow : M2 Nat := do
  let n ← get
  if n = 0 then throw "zero" else pure n

theorem bareThrow_spec (n0 : Nat) (h : n0 ≠ 0) :
    ⦃fun s => ⌜s = n0⌝⦄ bareThrow ⦃⇓ r => fun s => ⌜r = n0 ∧ s = n0⌝⦄ := by
  mvcgen [bareThrow]

/-! Adding the state-DISCARDING Halt barrel back: the `WPMonad` synthesizes,
but the barrel becomes STATE-AWARE — the type can no longer SAY the state is
discarded, which the pilot's 3-layer stack can. This is the price. -/
#synth WPMonad (ExceptT L (EStateM ε σ)) (.except L (.except ε (.arg σ .pure)))

example : ExceptConds (.except L (.except ε (.arg σ .pure)))
    = ((L → σ → ULift Prop) × (ε → σ → ULift Prop) × Unit) := rfl
example : ExceptConds (.except ε (.arg σ (.except L .pure)))
    = ((ε → σ → ULift Prop) × (L → ULift Prop) × Unit) := rfl

#print axioms toRun2_ofRun2
#print axioms ofRun2_toRun2
#print axioms bareThrow_spec
end E2

/-! # §4 Std's verified containers vs `LeanModels/Python/DictCalc.lean`

`Std.HashMap` ships **1 354 theorems** at the pin, and its lemmas assume
`[EquivBEq α] [LawfulHashable α]` — **an equivalence relation, NOT `Eq`**.
That is exactly what DictCalc §1 proves about `keyEq` (`keyEq_refl`,
`keyEq_symm`, `keyEq_trans`, through the `keyNF` normal form). So the Python
key IS a lawful Std key, and the obligation is six lines given a normal form
the tier already has. -/

namespace E4

/-- A miniature of `RVal`'s hashable-key fragment carrying DictCalc's two
"forced" facts: `True == 1`, and a namedtuple compares as a plain tuple. -/
inductive K where
  | int  (n : Int)
  | bool (b : Bool)
  | str  (s : String)
deriving Repr, DecidableEq

/-- DictCalc's `keyNF`, at this scale. -/
def K.nf : K → Int ⊕ String
  | .int n  => .inl n
  | .bool b => .inl (if b then 1 else 0)
  | .str s  => .inr s

instance : BEq K := ⟨fun a b => decide (a.nf = b.nf)⟩

@[simp] theorem K.beq_iff {a b : K} : (a == b) = true ↔ a.nf = b.nf := by
  simp [BEq.beq]

def K.hashNF : Int ⊕ String → UInt64
  | .inl n => hash n
  | .inr t => hash t
instance : Hashable K := ⟨fun a => K.hashNF a.nf⟩

/-- **THE WHOLE OBLIGATION**, and it unlocks 1 354 lemmas. -/
instance : EquivBEq K where
  rfl   := by simp
  symm  := by intro a b h; simp_all
  trans := by intro a b c h1 h2; simp_all

instance : LawfulHashable K where
  hash_eq := by intro a b h; simp_all [Hashable.hash]

/-- NOT `LawfulBEq`: `True == 1` while `.bool true ≠ .int 1`. -/
example : (K.bool true == K.int 1) = true := by decide
example : K.bool true ≠ K.int 1 := by decide

section Maps
variable (m : Std.HashMap K Nat) (k a : K) (v : Nat)

/-- DictCalc's `dictFind_store_self`. -/
theorem std_find_store_self : (m.insert k v)[k]? = some v := by simp
/-- DictCalc's `dictFind_store_ne`. -/
theorem std_find_store_ne (h : (k == a) = false) : (m.insert k v)[a]? = m[a]? := by grind
/-- DictCalc §4's `TableAt.get` — the `.get(k, default)` shape. -/
theorem std_getD : (m.insert k v).getD k 0 = v := by grind

/-- **THE MISMATCH, located exactly.** `Std.insert` REPLACES the key;
`dictStore` KEEPS the stored key and its insertion position (`{True: _}`
updated through `1` still lists `[True]`). `getKey?` makes it visible, and
`insertIfNew` is the arm that matches Python. -/
theorem std_insert_replaces_key : (m.insert k v).getKey? k = some k := by simp
theorem std_insertIfNew_keeps_key (h : k ∈ m) :
    (m.insertIfNew k v).getKey? k = m.getKey? k := by grind
end Maps

/-! And ORDER: Std gives a `Perm`, never a sequence. Python's dict is
insertion-ordered and `dictStore` is defined to preserve position. -/
#check @Std.HashMap.toList_insert_perm

#print axioms std_find_store_self
#print axioms std_find_store_ne
#print axioms std_getD
#print axioms std_insert_replaces_key
#print axioms std_insertIfNew_keeps_key
end E4

/-! # §5 `Decidable` exhaustion — CORE has no `Fintype`, and the instance is
     three lines

Core at the pin ships `Decidable (∀ x : Bool, p x)`, `decidableForallFin`,
`Decidable (∀ o : Ordering, p o)` and `decidableBallLT` — and NOTHING generic.
For a user inductive like `LeanModels.Sv.Logic` there is no instance, so
`decide` fails outright. Writing it costs three lines and stays CORE-ONLY
(Mathlib's `Fintype` + `deriving Fintype` is the alternative, and would put
Mathlib in the Sv tier's import closure). -/

namespace E5

/-- `LeanModels.Sv.Logic`, transcribed (IEEE 1800-2017 §6.3.1). -/
inductive Logic where | l0 | l1 | lx | lz
deriving Repr, BEq, DecidableEq, Inhabited

namespace Logic
def and : Logic → Logic → Logic
  | l0, _ => l0 | _, l0 => l0 | l1, l1 => l1 | _, _ => lx
def or : Logic → Logic → Logic
  | l1, _ => l1 | _, l1 => l1 | l0, l0 => l0 | _, _ => lx
def not : Logic → Logic
  | l0 => l1 | l1 => l0 | _ => lx
end Logic

/-- THE THREE LINES. -/
instance instDecForallLogic (p : Logic → Prop) [DecidablePred p] : Decidable (∀ a, p a) :=
  decidable_of_iff (p .l0 ∧ p .l1 ∧ p .lx ∧ p .lz)
    ⟨fun ⟨h0, h1, hx, hz⟩ a => by cases a <;> assumption, fun h => ⟨h _, h _, h _, h _⟩⟩

/-- 16 cases. -/
theorem deMorgan : ∀ a b : Logic, (a.and b).not = a.not.or b.not := by decide
/-- 64 cases. -/
theorem andAssoc : ∀ a b c : Logic, (a.and b).and c = a.and (b.and c) := by decide
/-- 4 096 cases — still ~1 s. -/
theorem six : ∀ a b c d e f : Logic,
    (((a.and b).and (c.and d)).and e).and f = a.and (b.and (c.and (d.and (e.and f)))) := by
  decide

/-! ## A ∀-SCHEDULE property over a REIFIED finite schedule.

`LeanModels.Sv.ScheduleOracle` is a STRUCTURE WITH A FUNCTION FIELD
(`choose : Nat → List Nat → List Nat` plus a permutation proof), so `∀ σ` is
a quantifier over a function space and has no `Decidable` instance — that is
where this technique stops. Reified at a bound (`k` invocations, each either
source or reverse order — `ScheduleOracle.revWhen`'s Boolean), it becomes a
finite domain and `decide` settles ∀-schedule questions outright. -/

def step (rev : Bool) (s : Nat × Nat) : Nat × Nat :=
  if rev then (1, s.2 + 2) else (s.1 + 1, 2)
def run (r1 r2 : Bool) (s : Nat × Nat) : Nat × Nat := step r2 (step r1 s)

/-- σ-IRRELEVANCE of the first invocation — `Sv/Obs.lean`'s
`choose_singleton` shape, settled by exhaustion. -/
theorem sched_first_irrelevant : ∀ r1 r2 : Bool, run r1 r2 (0, 0) = run false r2 (0, 0) := by
  decide

/-- And the RACE, exhibited by the SAME call: cell 1 is schedule-DEPENDENT.
**`decide` found this by refuting the author's first draft**, which asserted
independence — the report records that, because a refuting `decide` is a
counterexample finder, not only a prover. -/
theorem sched_race : ¬ (∀ r1 r2 : Bool, (run r1 r2 (0, 0)).1 = (run false false (0, 0)).1) := by
  decide

#print axioms deMorgan
#print axioms andAssoc
#print axioms six
#print axioms sched_first_irrelevant
#print axioms sched_race
end E5

/-! # §7 `partial_fixpoint` — equational lemmas YES, kernel computation NO

At the pin. It defines a fuel-free recursive function, gives `eq_def` and a
`partial_correctness` induction principle — and does **not** reduce in the
kernel, which is what confines it to MODEL-side functions. The failing `rfl`
is quoted in the report (it cannot be landed: it is an error). -/

namespace E7
def loop (n : Nat) (acc : Nat) : Option Nat :=
  if n = 0 then some acc else loop (n - 1) (acc + n)
partial_fixpoint

/-- The unfolding equation exists and rewrites. -/
theorem loop_unfold (n acc : Nat) :
    loop n acc = if n = 0 then some acc else loop (n - 1) (acc + n) := by
  rw [loop.eq_def]

/-! The proof rule core generates: PARTIAL correctness — *if* it returns.
Termination is never on offer. -/
#check @E7.loop.partial_correctness

#print axioms loop_unfold
end E7

/-! # §8 The bit-vector facts, WIDTH-PARAMETRIC — the route with no new axiom

`bv_decide` proves these at a FIXED width and adds a `_native` axiom whenever
its SAT solver runs (report §8 has the exact names). The proofs below are the
alternative measured against it: they hold at EVERY width, and their axioms
are the ordinary three. -/

namespace E8
open BitVec

/-- **FACT-C** — `LeanModels/Rv/Exec.lean`'s `divRem .div` overflow arm, and
the neighbour of `LeanModels.C.C23.UB.divideOverflow` (*"`INT_MIN / -1`: the
quotient is unrepresentable"*): dividing by `-1` negates, at every width ≥ 2. -/
theorem sdiv_allOnes {w : Nat} (hw : 1 < w) (a : BitVec w) :
    a.sdiv (BitVec.allOnes w) = -a := by
  have h1 : (1#w) ≠ BitVec.intMin w := by
    intro h
    have := congrArg BitVec.msb h
    simp [BitVec.msb_one, BitVec.msb_intMin] at this
    omega
  rw [← BitVec.neg_one_eq_allOnes, BitVec.sdiv_neg h1, BitVec.sdiv_one]

/-- **THE EDGE THE PARAMETRIC PROOF EXPOSES AND A FIXED-WIDTH RUN HIDES.**
At `w = 1`, `intMin 1 = 1#1`, the side condition fails, and the fact is a
DIFFERENT fact. No `bv_decide` run at width 8/16/32/64/128 could have told us. -/
theorem sdiv_allOnes_w1 : ∀ a : BitVec 1, a.sdiv (BitVec.allOnes 1) = a := by decide

/-- **FACT-SV** — `LeanModels.Sv.Logic`'s 4-state operators, vectorised into
the `(value, unknown)` BitVec-pair encoding an efficient `LVec` twin would use
(IEEE 1800-2017 §11.4.8). -/
abbrev L4 (w : Nat) := BitVec w × BitVec w

def not4 {w} (a : L4 w) : L4 w := (~~~a.1 &&& ~~~a.2, a.2)
def and4 {w} (a b : L4 w) : L4 w :=
  let u := (a.2 ||| b.2) &&& (a.1 ||| a.2) &&& (b.1 ||| b.2)
  (a.1 &&& b.1 &&& ~~~u, u)
def or4 {w} (a b : L4 w) : L4 w :=
  let u := (a.2 ||| b.2) &&& (~~~a.1 ||| a.2) &&& (~~~b.1 ||| b.2)
  (a.1 ||| b.1, u)

/-- Canonical: an unknown bit carries value 0. -/
def canon {w} (a : L4 w) : Prop := a.1 &&& a.2 = 0#w

/-- DE MORGAN on the vectorised encoding, proved BITWISE — so it holds at
EVERY width, where `bv_decide` proves it one width at a time. -/
theorem deMorgan4 {w} (a b : L4 w) (ha : canon a) (hb : canon b) :
    not4 (and4 a b) = or4 (not4 a) (not4 b) := by
  obtain ⟨av, au⟩ := a; obtain ⟨bv, bu⟩ := b
  simp only [canon] at ha hb
  simp only [not4, and4, or4, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  case refine_1 =>
    ext i hi
    have ha' : (av &&& au)[i] = (0#w)[i] := by rw [ha]
    have hb' : (bv &&& bu)[i] = (0#w)[i] := by rw [hb]
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at ha' hb'
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
    revert ha' hb'
    cases av[i] <;> cases au[i] <;> cases bv[i] <;> cases bu[i] <;> simp
  case refine_2 =>
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
    cases av[i] <;> cases au[i] <;> cases bv[i] <;> cases bu[i] <;> simp

#print axioms sdiv_allOnes
#print axioms sdiv_allOnes_w1
#print axioms deMorgan4
end E8

end StructuresCensus
