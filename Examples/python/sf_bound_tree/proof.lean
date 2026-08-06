/-
Real proofs for Examples/python/sf_bound_tree/spec.lean.

THE NEGAMAX MILESTONE: sunfish.py's `Searcher.bound` logical skeleton —
depth-limited fail-soft negamax over explicit `(eval, children)` game
trees, with the MTD-bi null-window flip `1 - gamma` and the beta cutoff —
proved totally correct against `sfBoundModel`, which is exactly
`formal/Sunfish/Bound.lean`'s

    def bound (G : Game) : Nat → G.Pos → Int → Int
      | 0, p, _ => G.eval p
      | d+1, p, gamma =>
        searchMoves gamma (fun m => -(bound G d m (1 - gamma))) (G.moves p) LOSS

specialized to the tree game (`sfSearchMoves` is the shared verbatim
`searchMoves` copy from sf_bound_rec).

Proof: outer Nat induction on the depth (`bound_core`); per level the
`for` loop is the sf_bound_for pattern — frozen `execFor`, list-induction
loop lemma `keyT` in fuel-threshold form, hand-unrolled first iteration
(the loop creates `kid` and `s`, so the environment grows) — with the
depth IH spliced at each recursive `bound(kid, 1 - gamma, depth - 1)`
call through `callFunction`'s frozen-recursion-point discipline
(`CallsTo.at_least` thresholds, side conditions by `omega`).
-/
import Examples.python.sf_bound_rec.proof

namespace Examples.python.sf_bound_tree.proof

open LeanModels LeanModels.Python

load_program sf_bound_tree from "Examples/python/sf_bound_tree/sf_bound_tree.json"

/-- Explicit game trees: `(eval, children)`. -/
inductive GTree where
  | node (eval : Int) (kids : List GTree)
deriving Repr

/- Marshalling: a tree is the Python pair `(eval, [children…])`.
Mutual STRUCTURAL recursion (a nested `kids.map GTree.toVal` would compile
to non-rfl-reducible recursion and break kernel evaluation — the
mergeSort-trap house rule). -/
mutual
def GTree.toVal : GTree → Val
  | .node e kids => .tuple #[.int e, .list ((GTree.toValList kids).toArray)]
def GTree.toValList : List GTree → List Val
  | [] => []
  | t :: ts => GTree.toVal t :: GTree.toValList ts
end

instance : ToVal GTree := ⟨GTree.toVal⟩

@[simp] private theorem toVal_node (e : Int) (kids : List GTree) :
    (ToVal.toVal (GTree.node e kids) : Val)
      = .tuple #[.int e, .list ((GTree.toValList kids).toArray)] := rfl

@[simp] private theorem gtoVal_node (e : Int) (kids : List GTree) :
    GTree.toVal (GTree.node e kids)
      = .tuple #[.int e, .list ((GTree.toValList kids).toArray)] := rfl

@[simp] private theorem toValList_nil : GTree.toValList [] = [] := rfl

@[simp] private theorem toValList_cons (t : GTree) (ts : List GTree) :
    GTree.toValList (t :: ts) = GTree.toVal t :: GTree.toValList ts := rfl

@[simp] private theorem toVal_eq_toVal (t : GTree) :
    (ToVal.toVal t : Val) = GTree.toVal t := rfl

/-- `formal/Sunfish/Bound.lean`'s `bound`, specialized to the tree game
(root namespace: the twin statements must mention the same constant). -/
def _root_.sfBoundModel (gamma : Int) : Nat → GTree → Int
  | 0, .node e _ => e
  | d + 1, .node _ kids =>
      sfSearchMoves gamma
        (kids.map fun k => -sfBoundModel (1 - gamma) d k) (-69290)

/-- The loop target (`kid`) of the loaded literal's `for`. -/
private def loopTgt : Expr :=
  .name "kid" { lineno := 17, colOffset := 8, endLineno := 17, endColOffset := 11 }

/-- The loop body of the loaded literal's `for`:
`s = -bound(kid, 1 - gamma, depth - 1)`, `best = max(best, s)`,
`if best >= gamma: break`. -/
private def loopBody : List Stmt :=
  [.assign
      #[.name "s" { lineno := 18, colOffset := 8, endLineno := 18, endColOffset := 9 }]
      (.unaryOp .usub
        (.call
          (.name "bound" { lineno := 18, colOffset := 13, endLineno := 18, endColOffset := 18 })
          #[.name "kid" { lineno := 18, colOffset := 19, endLineno := 18, endColOffset := 22 },
            .binOp
              (.constant (.int 1) { lineno := 18, colOffset := 24, endLineno := 18, endColOffset := 25 })
              .sub
              (.name "gamma" { lineno := 18, colOffset := 28, endLineno := 18, endColOffset := 33 })
              { lineno := 18, colOffset := 24, endLineno := 18, endColOffset := 33 },
            .binOp
              (.name "depth" { lineno := 18, colOffset := 35, endLineno := 18, endColOffset := 40 })
              .sub
              (.constant (.int 1) { lineno := 18, colOffset := 43, endLineno := 18, endColOffset := 44 })
              { lineno := 18, colOffset := 35, endLineno := 18, endColOffset := 44 }]
          Option.none
          { lineno := 18, colOffset := 13, endLineno := 18, endColOffset := 45 })
        { lineno := 18, colOffset := 12, endLineno := 18, endColOffset := 45 })
      { lineno := 18, colOffset := 8, endLineno := 18, endColOffset := 45 },
   .assign
      #[.name "best" { lineno := 19, colOffset := 8, endLineno := 19, endColOffset := 12 }]
      (.call
        (.name "max" { lineno := 19, colOffset := 15, endLineno := 19, endColOffset := 18 })
        #[.name "best" { lineno := 19, colOffset := 19, endLineno := 19, endColOffset := 23 },
          .name "s" { lineno := 19, colOffset := 25, endLineno := 19, endColOffset := 26 }]
        Option.none
        { lineno := 19, colOffset := 15, endLineno := 19, endColOffset := 27 })
      { lineno := 19, colOffset := 8, endLineno := 19, endColOffset := 27 },
   .ifStmt
      (.compare
        (.name "best" { lineno := 20, colOffset := 11, endLineno := 20, endColOffset := 15 })
        #[.gtE]
        #[.name "gamma" { lineno := 20, colOffset := 19, endLineno := 20, endColOffset := 24 }]
        { lineno := 20, colOffset := 11, endLineno := 20, endColOffset := 24 })
      #[.brk { lineno := 21, colOffset := 12, endLineno := 21, endColOffset := 17 }]
      #[]
      { lineno := 20, colOffset := 8, endLineno := 21, endColOffset := 17 }]

/-- The uniform loop environment: params, the running `best`, the loop
variable `kid` and body local `s` (present from the first iteration on). -/
private def E (tv : Val) (gamma depth b : Int) (kv : Val) (sv : Int) : Env :=
  [("tree", tv), ("gamma", Val.int gamma), ("depth", Val.int depth),
   ("best", Val.int b), ("kid", kv), ("s", Val.int sv)]

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- The loop lemma at one negamax level: from the uniform shape, the `for`
tail over children `ks` folds `sfSearchMoves` over the negated recursive
scores into `best`. The depth IH enters as `IH` (fuel-threshold per kid via
`CallsTo.at_least`). -/
private theorem keyT (tv : Val) (gamma depth : Int) (d : Nat)
    (hd : (depth - 1).toNat = d)
    (IH : ∀ (k : GTree) (gamma' depth' : Int), depth'.toNat = d →
      CallsTo sf_bound_tree "bound"
        #[ToVal.toVal k, Val.int gamma', Val.int depth']
        (Val.int (sfBoundModel gamma' d k))) :
    ∀ (ks : List GTree) (b : Int) (kv : Val) (sv : Int),
      ∃ f₀ kv' sv', ∀ F, f₀ ≤ F →
        execFor sf_bound_tree F (E tv gamma depth b kv sv) loopTgt
            (GTree.toValList ks) loopBody
          = .ok (E tv gamma depth
              (sfSearchMoves gamma
                (ks.map fun k => -sfBoundModel (1 - gamma) d k) b)
              kv' sv', .next) := by
  intro ks
  induction ks with
  | nil =>
    intro b kv sv
    refine ⟨1, kv, sv, fun F hF => ?_⟩
    have hrun : execFor sf_bound_tree 1 (E tv gamma depth b kv sv)
        loopTgt (GTree.toValList []) loopBody
        = .ok (E tv gamma depth b kv sv, .next) := by
      rw [toValList_nil, execFor.eq_2]
    have := execFor_mono hrun (by simp) F hF
    simpa [sfSearchMoves] using this
  | cons k rest ih =>
    intro b kv sv
    obtain ⟨fk, hk⟩ := (IH k (1 - gamma) (depth - 1) (by omega)).at_least
    have hk' : ∀ F, fk ≤ F → callFunction sf_bound_tree "bound"
        #[ToVal.toVal k, Val.int (1 - gamma), Val.int (depth - 1)] F
        = .ok (Val.int (sfBoundModel (1 - gamma) d k)) := fun F hF => hk F hF
    simp only [sf_bound_tree, toVal_eq_toVal] at hk'
    by_cases hc : gamma ≤ max b (-sfBoundModel (1 - gamma) d k)
    · -- cutoff: this iteration breaks
      refine ⟨fk + 64, ToVal.toVal k, -sfBoundModel (1 - gamma) d k,
        fun F hF => ?_⟩
      have hrun : execFor sf_bound_tree (fk + 64) (E tv gamma depth b kv sv)
          loopTgt (GTree.toValList (k :: rest)) loopBody
          = .ok (E tv gamma depth (max b (-sfBoundModel (1 - gamma) d k))
              (ToVal.toVal k) (-sfBoundModel (1 - gamma) d k), .next) := by
        rw [toValList_cons, execFor.eq_3]
        py_simp [sf_bound_tree, loopTgt, loopBody, E, hc]
        simp (disch := omega) only [hk']
        py_simp [hc]
      have := execFor_mono hrun (by simp) F hF
      simpa [sfSearchMoves, if_pos hc] using this
    · obtain ⟨f₁, kv₁, sv₁, h₁⟩ := ih (max b (-sfBoundModel (1 - gamma) d k))
        (ToVal.toVal k) (-sfBoundModel (1 - gamma) d k)
      refine ⟨fk + f₁ + 64, kv₁, sv₁, fun F hF => ?_⟩
      have hrun : execFor sf_bound_tree (fk + f₁ + 64)
          (E tv gamma depth b kv sv)
          loopTgt (GTree.toValList (k :: rest)) loopBody
          = .ok (E tv gamma depth
              (sfSearchMoves gamma
                (rest.map fun k => -sfBoundModel (1 - gamma) d k)
                (max b (-sfBoundModel (1 - gamma) d k)))
              kv₁ sv₁, .next) := by
        rw [toValList_cons, execFor.eq_3]
        simp only [sf_bound_tree, E, loopTgt, loopBody, toVal_eq_toVal] at h₁ ⊢
        py_simp [sf_bound_tree, (show ¬ gamma ≤ max b
          (-sfBoundModel (1 - gamma) d k) from hc)]
        simp (disch := omega) only [hk']
        py_simp [(show ¬ gamma ≤ max b
          (-sfBoundModel (1 - gamma) d k) from hc)]
        simp (disch := omega) only [h₁]
      have := execFor_mono hrun (by simp) F hF
      simpa [sfSearchMoves, if_neg hc] using this

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- The depth induction: at every modeled depth `d = depth.toNat`, the run
returns `sfBoundModel gamma d t`. -/
private theorem bound_core (d : Nat) : ∀ (t : GTree) (gamma depth : Int),
    depth.toNat = d →
    CallsTo sf_bound_tree "bound"
      #[ToVal.toVal t, Val.int gamma, Val.int depth]
      (Val.int (sfBoundModel gamma d t)) := by
  induction d with
  | zero =>
    intro t gamma depth h0
    obtain ⟨e, kids⟩ := t
    refine ⟨32, ?_⟩
    rw [callFunction.eq_2]
    py_simp [sf_bound_tree, sfBoundModel, (show (depth : Int) ≤ 0 by omega)]
  | succ d ihd =>
    intro t gamma depth hd
    obtain ⟨e, kids⟩ := t
    have hpos : ¬ ((depth : Int) ≤ 0) := by omega
    cases kids with
    | nil =>
      refine ⟨64, ?_⟩
      rw [callFunction.eq_2]
      py_simp [sf_bound_tree, hpos]
      rw [execFor.eq_2]
      py_simp [sfBoundModel, sfSearchMoves]
    | cons k0 krest =>
      obtain ⟨fk, hk⟩ := (ihd k0 (1 - gamma) (depth - 1) (by omega)).at_least
      have hk' : ∀ F, fk ≤ F → callFunction sf_bound_tree "bound"
          #[ToVal.toVal k0, Val.int (1 - gamma), Val.int (depth - 1)] F
          = .ok (Val.int (sfBoundModel (1 - gamma) d k0)) := fun F hF => hk F hF
      simp only [sf_bound_tree, toVal_eq_toVal] at hk'
      by_cases hc : gamma ≤ -min 69290 (sfBoundModel (1 - gamma) d k0)
      · -- the very first iteration breaks
        refine ⟨fk + 96, ?_⟩
        rw [callFunction.eq_2]
        py_simp [sf_bound_tree, hpos]
        rw [execFor.eq_3]
        py_simp [hc]
        simp (disch := omega) only [hk']
        py_simp [hc]
        py_simp [sfBoundModel, sfSearchMoves, hc]
      · -- unroll the first iteration by hand, splice `keyT` for the rest
        obtain ⟨f₁, kv₁, sv₁, h₁⟩ := keyT
          (ToVal.toVal (GTree.node e (k0 :: krest))) gamma depth d (by omega)
          (fun k g' d' h' => ihd k g' d' h') krest
          (max (-69290) (-sfBoundModel (1 - gamma) d k0))
          (ToVal.toVal k0) (-sfBoundModel (1 - gamma) d k0)
        py_simp [sf_bound_tree, E, loopTgt, loopBody] at h₁
        refine ⟨fk + f₁ + 96, ?_⟩
        rw [callFunction.eq_2]
        py_simp [sf_bound_tree, hpos]
        rw [execFor.eq_3]
        py_simp [hc]
        simp (disch := omega) only [hk']
        py_simp [hc]
        simp (disch := omega) only [h₁]
        py_simp [sfBoundModel, sfSearchMoves, hc]

/-- **Total correctness** of the negamax skeleton: for every game tree,
window, and depth, the Python run terminates and returns exactly
`formal/Sunfish/Bound.lean`'s `bound` (tree game, `sfBoundModel`). -/
theorem bound_total (t : GTree) (gamma depth : PyInt) :
    sf_bound_tree.bound(t, gamma, depth) ==>
      sfBoundModel gamma depth.toNat t :=
  bound_core depth.toNat t gamma depth rfl

end Examples.python.sf_bound_tree.proof
