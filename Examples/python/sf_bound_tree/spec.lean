/-
Examples/python/sf_bound_tree — three-file example layout. THE NEGAMAX
MILESTONE of the sunfish ladder: `Searcher.bound`'s logical skeleton —
depth-limited fail-soft negamax over explicit `(eval, children)` game
trees with the MTD-bi null-window flip `1 - gamma` and the beta cutoff —
proved TOTALLY CORRECT against `sfBoundModel`, which is verbatim
`formal/Sunfish/Bound.lean`'s

    def bound (G : Game) : Nat → G.Pos → Int → Int
      | 0, p, _ => G.eval p
      | d+1, p, gamma =>
        searchMoves gamma (fun m => -(bound G d m (1 - gamma))) (G.moves p) LOSS

specialized to the tree game. The recursion, the window flip, the
G1 module constant `-MATE_UPPER`, the `for` loop, and `max()` are all the
real interpreter's semantics; the sole transliteration vs the shipped
loop is the generator `moves()` precomputed as the children list.

Differential rows: harness/cases.json carries typed-JSON argument
rows for this function (leanmodels-run accepts the canonical
{"t":…,"v":…} encoding for list/tuple arguments); the runs below
are additionally checked at elaboration time.
-/
import Examples.python.sf_bound_tree.proof

open LeanModels LeanModels.Python
open Examples.python.sf_bound_tree.proof (GTree)

/-- Leaf helper for the concrete checks. -/
private def leaf (e : Int) : GTree := .node e []

load_program sf_bound_tree from "Examples/python/sf_bound_tree/sf_bound_tree.json"

/-! Non-vacuity: concrete runs (values cross-checked against CPython).
`t1 = (5, [(3,[]), (-2,[])])`, `t2 = (0, [(4, [(1,[]), (-7,[])]), (2,[])])`. -/
private def t1 : GTree := .node 5 [leaf 3, leaf (-2)]
private def t2 : GTree := .node 0 [.node 4 [leaf 1, leaf (-7)], leaf 2]

#py_check sf_bound_tree.bound(leaf 7, 0, 0) = 7
#py_check sf_bound_tree.bound(leaf 7, 0, 3) = -69290
#py_check sf_bound_tree.bound(t1, 10, 1) = 2
#py_check sf_bound_tree.bound(t1, -10, 1) = -3
#py_check sf_bound_tree.bound(t2, 5, 2) = 69290
#py_check sf_bound_tree.bound(t2, 8, 2) = 69290
#py_check sf_bound_tree.bound(t1, 10, -2) = 5

/-- **Total correctness** of the negamax skeleton: for every game tree,
window, and depth, the Python run terminates and returns exactly
`formal/Sunfish/Bound.lean`'s `bound` (tree game, `sfBoundModel`). -/
theorem bound_total (t : GTree) (gamma depth : PyInt) :
    sf_bound_tree.bound(t, gamma, depth) ==>
      sfBoundModel gamma depth.toNat t := by proofs
