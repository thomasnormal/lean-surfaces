/-
Proof module for `Examples/python/sf_position/spec.lean` (three-file
example layout). The namedtuple VALUE tier as theorems: constructions are
IMMEDIATE values (no allocation — `CallsIn` hands back the input world),
field access is tuple indexing, and the transposition-table pattern —
a tuple key CONTAINING a Position, Entry values, `.get` defaults, an
equal-but-distinct reconstructed key — decides by pure `keyEq`
reflexivity, symbolically in the score and depth. Straight-line public
totals go through `py_prove`; the stateful values through one
`rw [callIn.eq_2]` + `py_simp` (the sf_searcher geometry — no nested
`callIn` exists here: constructor calls are interpreter-inline). The
`for`-over-a-namedtuple total steps the frozen `execFor` per element
(`eq_3` twice, `eq_2` at nil — one whole-loop `py_simp [execFor]` blows
the simp step budget); `bad_arity`'s interpolated `TypeError` message
leaves one literal `String.append` equation, closed by `rfl`.
-/
import LeanModels

namespace Examples.python.sf_position.proof

open LeanModels LeanModels.Python

-- (envelope regenerated 2026-08-09: the verbatim shipped `rotate` method +
-- the `rotate_fields`/`rotate_null_fields` differential wrappers — H5
-- strings; `load_program` does not track the JSON as a build input, so this
-- comment is also the content change that forces the rebuild)
load_program sf_position from "Examples/python/sf_position/sf_position.json"

/-- The fresh world of every public call: the whole top level is the
docstring plus the RECOGNIZED namedtuple binds (ingested as `pass`), so
nothing is allocated and nothing is bound. -/
private def w0 : World := ⟨#[], [], [], []⟩

/-- The Position VALUE `tp_score_flow` builds — the real six-field shape,
as an immediate `RVal.ntuple` (the recorded VALUE-like decision). -/
private def posV (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "brd", .int s, .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

/-- The world after `tp_score_flow`: ONE dict, keyed by the tuple
`(pos, depth, True)` — a namedtuple inside a tuple key, sunfish's
`tp_score` pattern — holding the Entry VALUE. -/
private def wTp (s d : Int) : World :=
  ⟨#[.dict #[(.tuple #[posV s, .int d, .bool true],
              .ntuple "Entry" #["lower", "upper"] #[.int (s - 1), .int (s + 1)])] 1],
   [], [], []⟩

theorem entry_window_total (lo hi : PyInt) :
    sf_position.entry_window(lo, hi) ==> hi - lo := by
  py_prove [sf_position]

set_option maxRecDepth 8192 in
theorem iterate_entry_total (lo hi : PyInt) :
    sf_position.iterate_entry(lo, hi) ==> lo + hi := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [sf_position]
  rw [execFor.eq_3]
  py_simp []
  rw [execFor.eq_3]
  py_simp []
  rw [execFor.eq_2]
  py_simp []

set_option maxRecDepth 4096 in
theorem bad_arity_raises (i : PyInt) :
    sf_position.bad_arity(i) ==>!
      .typeError "Move() takes 3 positional arguments but 1 were given" := by
  py_prove [sf_position]
  rfl

theorem missing_field_raises (i j : PyInt) :
    sf_position.missing_field(i, j) ==>! .attributeError := by
  py_prove [sf_position]

set_option maxRecDepth 4096 in
theorem mk_move_value (i j : Int) :
    CallsIn sf_position w0 "mk_move" #[.int i, .int j] w0
      (.ntuple "Move" #["i", "j", "prom"] #[.int i, .int j, .str ""]) := by
  refine ⟨64, ?_⟩
  rw [callIn.eq_2]
  py_simp [sf_position, w0]

set_option maxRecDepth 4096 in
theorem move_fields_callsIn (i j : Int) :
    CallsIn sf_position w0 "move_fields" #[.int i, .int j] w0
      (.tuple #[.int i, .int j, .str "q"]) := by
  refine ⟨64, ?_⟩
  rw [callIn.eq_2]
  py_simp [sf_position, w0]

set_option maxRecDepth 4096 in
theorem move_eq_symbolic (i j : Int) (hij : ¬ (i = j)) :
    CallsIn sf_position w0 "move_eq" #[.int i, .int j] w0
      (.tuple #[.bool true, .bool true, .bool true, .bool true]) := by
  refine ⟨64, ?_⟩
  rw [callIn.eq_2]
  -- `-valEq, -valEqList`: with the comparison's rhs still symbolic under
  -- the chain's binder, the equation-lemma unfolding of `valEq` at a
  -- (constructor, variable) pair produces a KERNEL-REJECTED `Eq.refl`
  -- (smart-unfolding mismatch); erased, the pairs reduce only once both
  -- sides are concrete-shaped — recorded finding, see AGENTS.md.
  py_simp [sf_position, w0, hij, -valEq, -valEqList]

set_option maxRecDepth 8192 in
theorem tp_score_flow_callsIn (s d : Int) :
    CallsIn sf_position w0 "tp_score_flow" #[.int s, .int d] (wTp s d)
      (.tuple #[.int (s - 1), .int (s + 1), .int (-10), .int 10, .int (s + 1),
                .bool true, .int 1]) := by
  refine ⟨64, ?_⟩
  rw [callIn.eq_2]
  py_simp [sf_position, w0, wTp, posV]

private def posB (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "brd", .int s, .tuple #[.bool true, .bool true],
      .tuple #[.bool false, .bool false], .int 3, .int 4]

private def posM (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "brd", .int (-s), .tuple #[.bool false, .bool false],
      .tuple #[.bool true, .bool true], .int 3, .int 4]

set_option maxRecDepth 8192 in
theorem position_mirror_callsIn (s : Int) :
    CallsIn sf_position w0 "Position.mirror" #[posB s] w0 (posM s) := by
  refine ⟨64, ?_⟩
  rw [callIn.eq_2]
  py_simp [sf_position, w0, posB, posM]

set_option maxRecDepth 8192 in
theorem mirror_score_callsIn (s : Int) :
    CallsIn sf_position w0 "mirror_score" #[.int s] w0
      (.tuple #[.int (-s), .str "brd", .bool false, .bool true,
                .int 3, .int 4]) := by
  -- the recorded per-call geometry (sf_searcher): one `callIn.eq_2` step
  -- per call — the outer frame first, then the nested `Position.mirror`
  -- the run is stuck on (whole-driver unfolding storms)
  refine ⟨64, ?_⟩
  rw [callIn.eq_2]
  py_simp [sf_position, w0]
  rw [callIn.eq_2]
  py_simp [sf_position]

end Examples.python.sf_position.proof
