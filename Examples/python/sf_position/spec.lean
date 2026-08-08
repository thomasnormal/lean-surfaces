/-
Examples/python/sf_position — three-file example layout. The namedtuple
sunfish artifact (the recorded VALUE-like decision, implemented): the
REAL Move/Entry/Position field shapes flowing through construction,
field access, equality, iteration, unpacking, and — the transposition-
table pattern — dict-keying by tuples CONTAINING a Position, with the
Entry `.get` default and an equal-but-distinct reconstructed key hitting
the SAME slot. Construction is an IMMEDIATE value: the `CallsIn`
theorems hand back the input world unchanged and show the `RVal.ntuple`
value itself; a namedtuple RESULT refuses the public boundary loudly
(no `Val` observation form — a tuple snapshot would forget the class).
The shipped sunfish `Position` is a namedtuple SUBCLASS with methods —
still loudly uninstantiable; this file carries its field shape as the
plain namedtuple (docs/memory-model.md §class semantics).
-/
import Examples.python.sf_position.proof

open LeanModels LeanModels.Python

load_program sf_position from "Examples/python/sf_position/sf_position.json"

/-! Non-vacuity: the recognition itself (all three namedtuple binds under
the benign import structured into the table; nothing bound, nothing
allocated at module init), then concrete runs cross-checked against
CPython (`harness/cases.json` rows). -/

#guard sf_position.namedtuples.map NamedTupleDefn.name == #["Move", "Entry", "Position"]
#guard sf_position.namedtuples.map NamedTupleDefn.fields ==
  #[#["i", "j", "prom"], #["lower", "upper"],
    #["board", "score", "wc", "bc", "ep", "kp"]]
#guard initWorld sf_position == ⟨#[], [], []⟩

#py_check sf_position.move_fields(3, 7) = (Val.tuple #[.int 3, .int 7, .str "q"])
#py_check sf_position.move_eq(3, 7) =
  (Val.tuple #[.bool true, .bool true, .bool true, .bool true])
#py_check sf_position.entry_window(-10, 10) = 20
#py_check sf_position.position_fields(40, 95) =
  (Val.tuple #[.int 40, .str "board", .bool true, .bool false, .int 95, .int 6])
#py_check sf_position.tp_score_flow(40, 2) =
  (Val.tuple #[.int 39, .int 41, .int (-10), .int 10, .int 41, .bool true, .int 1])
#py_check sf_position.unpack_move(3, 7) = (Val.tuple #[.int 3, .int 7, .str "p"])
#py_check sf_position.iterate_entry(3, 7) = 10
#py_check sf_position.move_index(3, 7) = (Val.tuple #[.int 3, .str "n", .int 7])
#py_check sf_position.bad_arity(1) raises
  (.typeError "Move() takes 3 positional arguments but 1 were given")
#py_check sf_position.missing_field(1, 2) raises .attributeError

/-! The loud frontier, pinned raw (no surface form for `unsupported` —
deliberate): a namedtuple result refuses the public freeze; the
namedtuple protocol (`._asdict()`, `._fields`) exists in CPython and is
out of tier — loud, never a fake `AttributeError`. -/

#guard callFunction sf_position "mk_move" #[.int 1, .int 2] 4096 matches .unsupported _
#guard callFunction sf_position "asdict_is_loud" #[.int 1, .int 2] 4096 matches .unsupported _
#guard callFunction sf_position "fields_are_loud" #[.int 1, .int 2] 4096 matches .unsupported _

/-- The fresh world of every public call (see the `#guard` above). -/
private def w0 : World := ⟨#[], [], []⟩

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
   [], []⟩

/-- Field access is tuple indexing: `Entry(lo, hi).upper - Entry(lo, hi).lower`
is total, symbolically. -/
theorem entry_window_total (lo hi : PyInt) :
    sf_position.entry_window(lo, hi) ==> hi - lo := by
  proofs

/-- namedtuples iterate as tuples: the `for v in Entry(lo, hi)` sum. -/
theorem iterate_entry_total (lo hi : PyInt) :
    sf_position.iterate_entry(lo, hi) ==> lo + hi := by
  proofs

/-- Wrong constructor arity is the faithful `TypeError`, for every
argument. -/
theorem bad_arity_raises (i : PyInt) :
    sf_position.bad_arity(i) ==>!
      .typeError "Move() takes 3 positional arguments but 1 were given" := by
  proofs

/-- A non-field, non-protocol attribute is the faithful `AttributeError`. -/
theorem missing_field_raises (i j : PyInt) :
    sf_position.missing_field(i, j) ==>! .attributeError := by
  proofs

/-- **The VALUE-like decision as a theorem**: constructing `Move(i, j, "")`
is an IMMEDIATE value — the stateful judgment shows the `RVal.ntuple`
itself, and the world comes back exactly as it went in (no allocation). -/
theorem mk_move_value (i j : Int) :
    CallsIn sf_position w0 "mk_move" #[.int i, .int j] w0
      (.ntuple "Move" #["i", "j", "prom"] #[.int i, .int j, .str ""]) := by
  proofs

/-- Construction + field access round-trip, symbolically: the fields come
back in declaration order, the world untouched. -/
theorem move_fields_callsIn (i j : Int) :
    CallsIn sf_position w0 "move_fields" #[.int i, .int j] w0
      (.tuple #[.int i, .int j, .str "q"]) := by
  proofs

/-- namedtuple equality IS tuple equality (the class erased, both
directions), and two distinct Moves differ — for every `i ≠ j`. -/
theorem move_eq_symbolic (i j : Int) (hij : ¬ (i = j)) :
    CallsIn sf_position w0 "move_eq" #[.int i, .int j] w0
      (.tuple #[.bool true, .bool true, .bool true, .bool true]) := by
  proofs

/-- **The transposition-table pattern, symbolic in score and depth**: a
tuple key CONTAINING a Position stores an Entry; the `.get` hit returns
it and the miss takes the default; an equal-but-distinct reconstructed
Position key addresses the SAME slot (pure `keyEq` — hash-equality
through the namedtuple, exactly why sunfish's `tp_score` keys stay in
tier); membership and `len` agree; the final world holds ONE entry. -/
theorem tp_score_flow_callsIn (s d : Int) :
    CallsIn sf_position w0 "tp_score_flow" #[.int s, .int d] (wTp s d)
      (.tuple #[.int (s - 1), .int (s + 1), .int (-10), .int 10, .int (s + 1),
                .bool true, .int 1]) := by
  proofs
