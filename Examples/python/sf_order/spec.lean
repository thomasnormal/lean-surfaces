import LeanModels

/-!
# sf_order — sunfish's move-ordering surface, END TO END (H6)

`Position.gen_moves` and `Position.value` are VERBATIM from the shipped
sunfish.py; `pst` is the padded table (CPython's own output of the
shipped padding loop — the module-init tier gap, worked around with the
oracle's data, never with guessed semantics). `order_from` carries the
shipped ordering line verbatim (sunfish.py line 412):

    sorted(((pos.value(m), m) for m in pos.gen_moves()), reverse=True)

so this example is the H6 milestone's capstone: a generator expression
lowered at ingestion, DRAINED by `sorted` through the H4 stepper,
ordered by the shared `rvalLt` relation on `(value, Move)` pairs —
namedtuple ties class-erased — descending and stable, exactly CPython's
move ordering for `Searcher.bound`'s loop.

Pinned here: the FULL ordered move list on a promotion-blocked board and
an en-passant board, and the opening board's count/head/tail (the
20-move list itself rides the differential battery). `value` facts pin
the capture arm (`q.islower()`/`q.upper()`, the H6 str additions) and
the en-passant bonus.

`proof.lean` (2026-08-17, docs/backlog.md §L8) proves the three constructs
`bound_probe` was blocked behind, over the shipped program: the ordering
line evaluates to the sorted list, the `moves` loop cuts at the threshold,
and the nested `def` allocates the closure its call turns into a
generator. The reference-enumeration equality for the ordering — the
decided gen_moves statement extended by `value` — is still open, and these
pins are its concrete anchors.
-/

open LeanModels LeanModels.Python

set_option maxRecDepth 100000 in
load_program sf_order from "Examples/python/sf_order/sf_order.json"

private def openingB : String :=
  "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n"

private def promoB : String :=
  "         \n         \n .r.r....\n .P......\n ........\n ........\n ........\n ........\n ........\n K.......\n         \n         \n"

private def epB : String :=
  "         \n         \n ........\n ........\n ........\n pP......\n ........\n ........\n ........\n K.......\n         \n         \n"

/-! ### the ordering, whole lists (CPython's answers, order included) -/

#guard callFunction sf_order "move_order" #[.str promoB, .int 0, .int 0] 60000 ==
  .ok (.list #[.tuple #[.int 13, .int 91, .int 92, .str ""],
               .tuple #[.int (-14), .int 91, .int 82, .str ""],
               .tuple #[.int (-21), .int 91, .int 81, .str ""]])
#guard callFunction sf_order "move_order" #[.str epB, .int 42, .int 0] 60000 ==
  .ok (.list #[.tuple #[.int 113, .int 52, .int 42, .str ""],
               .tuple #[.int 13, .int 91, .int 92, .str ""],
               .tuple #[.int (-14), .int 91, .int 82, .str ""],
               .tuple #[.int (-21), .int 91, .int 81, .str ""]])

/-! ### the opening board: 20 moves, d2d4 first, CPython's order -/

#guard (match callFunction sf_order "move_order" #[.str openingB, .int 0, .int 0] 60000 with
  | .ok (.list ms) =>
      ms.size == 20 &&
      ms[0]! == .tuple #[.int 46, .int 84, .int 64, .str ""] &&
      ms[1]! == .tuple #[.int 42, .int 85, .int 65, .str ""] &&
      ms[19]! == .tuple #[.int (-5), .int 82, .int 62, .str ""]
  | _ => false)
#py_check sf_order.best_move(
    "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n",
    0, 0) = (Val.tuple #[.int 46, .int 84, .int 64, .str ""])

/-! ### value: the verbatim scorer (islower/upper capture arm, ep bonus) -/

#py_check sf_order.value_of(
    "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n",
    84, 64, "", 0, 0) = 46
#py_check sf_order.value_of(
    "         \n         \n ........\n ........\n ........\n pP......\n ........\n ........\n ........\n K.......\n         \n         \n",
    52, 42, "", 42, 0) = 113

/-! ### H7 capstone: the moves()-shaped nested GENERATOR (bound_probe)

The nested `def moves():` closes over `pos`/`depth`/`val_lower` (never
rebound after the def — the shipped file's own shape), carries the
verbatim ordering line, and is consumed LAZILY with the beta cutoff:
`(46, 1)` under a cutting window vs `(46, 20)` without — the generator
is abandoned mid-drain after ONE consumed yield, which an eager design
cannot reproduce. -/

#py_check sf_order.bound_probe(
    "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n",
    40, 1, 0, 0) = (Val.tuple #[.int 46, .int 1])
#py_check sf_order.bound_probe(
    "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n",
    1000, 1, 0, 0) = (Val.tuple #[.int 46, .int 20])
#py_check sf_order.bound_probe(
    "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n",
    1000, 0, 0, 0) = (Val.tuple #[.int 46, .int 3])

/-! ### H7+ capstone: move_probe (verbatim move+rotate, the put lambda)
and killer_probe (tp_move.get through an instance attribute, keyed by
the Position, the killer gate, the ordered tail) -/

#py_check sf_order.killer_probe(
    "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n",
    40, 1, 0, 0, 85, 65) = (Val.tuple #[.int 1,
      .list #[.tuple #[.int 42, .int 85, .int 65]]])
#py_check sf_order.killer_probe(
    "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n",
    1000, 1, 0, 0, -1, 0) = (Val.tuple #[.int 20,
      .list #[.tuple #[.int 46, .int 84, .int 64],
              .tuple #[.int 42, .int 85, .int 65]]])

/-! ### bound() arc pass 2 capstone: rec_probe — the RECURSION shape of
the shipped bound(). `-self.bound(pos.move(move), 1 - gamma, depth - 1)`
yielded from the nested generator through the captured self (captures
depth/gamma/pos/self/val_lower — the shipped moves() set), folded below
with the beta cutoff. `nodes` counts bound() entries: at the same depth
the cutting window prunes the recursion TREE ((113, 7) vs (113, 15) at
depth 2), not just the top drain — an eager design searches every
subtree and cannot reproduce the pair. -/

private def pawnB : String :=
  "         \n         \n ....k...\n ........\n ........\n ........\n ...p....\n ....P...\n ........\n ....K...\n         \n         \n"

#guard callFunction sf_order "rec_probe" #[.str pawnB, .int 0, .int 1, .int 0, .int 0] 200000 ==
  .ok (.tuple #[.int 133, .int 2])
#guard callFunction sf_order "rec_probe" #[.str pawnB, .int 1000, .int 1, .int 0, .int 0] 200000 ==
  .ok (.tuple #[.int 133, .int 8])
#guard callFunction sf_order "rec_probe" #[.str pawnB, .int 0, .int 2, .int 0, .int 0] 200000 ==
  .ok (.tuple #[.int 113, .int 7])
#guard callFunction sf_order "rec_probe" #[.str pawnB, .int 1000, .int 2, .int 0, .int 0] 200000 ==
  .ok (.tuple #[.int 113, .int 15])
#guard callFunction sf_order "rec_probe" #[.str openingB, .int 0, .int 1, .int 0, .int 0] 200000 ==
  .ok (.tuple #[.int 46, .int 2])
