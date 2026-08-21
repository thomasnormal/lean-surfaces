/-
**F1b-iii — `Position.move`'s GATE**, thirteen statements at a free board.
docs/backlog.md §L44 projected the body and measured its exit law; this file is
the gate that measurement decided the shape of.
-/
import Examples.python.sunfish.move_residue

namespace Examples.python.sunfish.move_gate

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)
open Examples.python.sunfish.basecase_depth0 (mvOf)
open Examples.python.sunfish.move_residue

set_option maxRecDepth 100000

/-! ## §0 The method, projected — thirteen statements, each pinned by `rfl` -/

private def nowhere : Span := ⟨0, 0, 0, 0⟩

private def nth (n : Nat) (ss : List Stmt) : Stmt :=
  match ss.drop n with | s :: _ => s | [] => .pass nowhere

/-- `Position.move`'s own `FunctionDefn`, projected. -/
def mvF : FunctionDefn :=
  match findFunction sunfish "Position.move" with | some f => f | none => default

/-- Its body — thirteen statements. -/
def mvB : List Stmt := mvF.body.toList

/-- `i, j, prom = move`. -/
def mvUnpack : Stmt := nth 0 mvB
/-- `p, q = self.board[i], self.board[j]`. -/
def mvPQ : Stmt := nth 1 mvB
/-- `put = lambda board, i, p: board[:i] + p + board[i + 1:]` — the ONE
allocation the exit law measured. -/
def mvDef : Stmt := nth 2 mvB
/-- `board = self.board`. -/
def mvBoard : Stmt := nth 3 mvB
/-- `wc, bc, ep, kp = self.wc, self.bc, 0, 0`. -/
def mvFields : Stmt := nth 4 mvB
/-- `score = self.score + self.value(move)`. -/
def mvScore : Stmt := nth 5 mvB
/-- `board = put(board, j, board[i])`. -/
def mvPut1 : Stmt := nth 6 mvB
/-- `board = put(board, i, ".")`. -/
def mvPut2 : Stmt := nth 7 mvB
/-- `wc = (wc[0] and i != A1, wc[1] and i != H1)`. -/
def mvWc : Stmt := nth 8 mvB
/-- `bc = (bc[0] and j != H8, bc[1] and j != A8)`. -/
def mvBc : Stmt := nth 9 mvB
/-- `if p == "K": …` — the castling block. -/
def mvKing : Stmt := nth 10 mvB
/-- `if p == "P": …` — the pawn block. -/
def mvPawn : Stmt := nth 11 mvB
/-- `return Position(board, score, wc, bc, ep, kp).rotate()`. -/
def mvRet : Stmt := nth 12 mvB

theorem mvB_split :
    mvB = [mvUnpack, mvPQ, mvDef, mvBoard, mvFields, mvScore, mvPut1, mvPut2,
           mvWc, mvBc, mvKing, mvPawn, mvRet] := rfl

theorem mvF_lit : findFunction sunfish "Position.move" = some mvF ∧
    mvF.params = #[⟨"self", mvF.params[0]!.span, Option.none⟩,
                   ⟨"move", mvF.params[1]!.span, Option.none⟩] := ⟨rfl, rfl⟩

/-- **No statement is `Stmt.unsupported`** — §L44's census, as a `rfl`. -/
theorem mvB_in_tier : mvB.all (fun s => match s with | .unsupported .. => false | _ => true)
    = true := rfl

/-! ## §1 THE ONE ALLOCATION — `put`'s closure

§L44's exit law measured `Position.move` at heap 66 → 67 with **only the new slot
touched**, and this is the statement that does it. `put` captures NOTHING
(`captures = #[]` in the projected AST), so `allocCells` is a no-op and
`capturesSnapshot` answers `[]` — the closure that lands on the heap is
cell-free, which is what makes `cellsFor` trivial at the two call sites in §2. -/

theorem mvDef_lit : ∃ sb si sp2 sA sB sC sD sE sF sG sH sI sJ sK sL sM sN sO sP sQ, mvDef =
    .defStmt "put" #[⟨"board", sb, Option.none⟩, ⟨"i", si, Option.none⟩,
                     ⟨"p", sp2, Option.none⟩] true true false false
      #[.ret (some (.binOp
          (.binOp (.slice (.name "board" sA) (.constant .none sB) (.name "i" sC)
                    (.constant .none sD) sE)
            .add (.name "p" sF) sG)
          .add
          (.slice (.name "board" sH)
            (.binOp (.name "i" sI) .add (.constant (.int 1) sJ) sK)
            (.constant .none sL) (.constant .none sM) sN) sO)) sP]
      #[] sQ :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- The closure object the statement pushes — `put`'s own, cell-free. -/
def putObj : Obj :=
  match mvDef with
  | .defStmt nm ps ao lo hg ig bd _ _ => .closure nm ps ao lo hg ig bd []
  | _ => .dict #[] 0

/-- **GATE — the `def`.** One `push`, one binding, and nothing else moves. -/
theorem move_defines_put (w : World) (e : REnv) (F : Nat) :
    execStmt sunfish (F + 2) ⟨w, e⟩ mvDef
      = .ok ⟨{ w with heap := w.heap.push putObj }, Env.set e "put" (.ref w.heap.size)⟩ .next := by
  obtain ⟨sb, si, sp2, sA, sB, sC, sD, sE, sF, sG, sH, sI, sJ, sK, sL, sM, sN, sO, sP, sQ,
    hlit⟩ := mvDef_lit
  rw [hlit]
  py_simp [-globalsFold, -globalsStep, putObj, hlit, allocCells, capturesSnapshot]

/-! ## §2 THE `put` CALL — where §L41's residue lemmas are spent

Both of statements 6 and 7 are `put(board, k, c)` at the closure §1 allocated.
The body is one `return` of `board[:i] + p + board[i+1:]`, whose two
`Expr.slice`s are exactly the argument orders §L41 proved — lower, upper, step —
so the answer is `putStr`. -/

theorem mvPut1_lit : ∃ s1 s2 s3 s4 s5 s6 s7 s8 s9, mvPut1 =
    .assign #[.name "board" s1]
      (.call (.name "put" s2) #[.name "board" s3, .name "j" s4,
        .subscript (.name "board" s5) (.name "i" s6) s7] #[] Option.none s8) s9 :=
  ⟨_, _, _, _, _, _, _, _, _, rfl⟩

theorem mvPut2_lit : ∃ s1 s2 s3 s4 s5 s6 s7, mvPut2 =
    .assign #[.name "board" s1]
      (.call (.name "put" s2) #[.name "board" s3, .name "i" s4,
        .constant (.str ".") s5] #[] Option.none s6) s7 :=
  ⟨_, _, _, _, _, _, _, rfl⟩

/-! **The branch the call takes, pinned.** `evalExpr`'s call arm short-circuits to
a faithful `TypeError` when the whole module is heap-free
(`funsHeapFree … && topLevelDefFree`), and only otherwise reaches the closure.
sunfish is NOT heap-free — `Position.move`'s own `put` is why — so the gate below
will take the closure branch, and this `rfl` is what says so before anything
depends on it. -/
theorem sunfish_not_heapFree :
    (funsHeapFree sunfish.functions.toList && topLevelDefFree sunfish) = false := rfl

/-! **`put`'s closure is CELL-FREE**, so `cellsFor` is the identity at both call
sites (`cellsFor_cellFree`, §H7) and no cell ever reaches a value position. -/
theorem putObj_captures : (match putObj with | .closure _ _ _ _ _ _ _ cap => cap | _ => [])
    = [] := rfl

/-! ### §1, INSTANTIATED on the shipped engine

`move_defines_put` says the statement pushes ONE object and binds one name. The
engine agrees: after a real `Position.move` the heap has grown by exactly one
slot, slot **66**, and what is standing in it is a closure named `put` with three
parameters and no captures. That is §L44's exit law read off the object rather
than off the size. -/
#guard (match callIn sunfish 256 (initWorld sunfish) "Position.move" #[posH 0, mvOf 84 64 ""] with
  | .ok w _ =>
    w.heap.size == 67 && (initWorld sunfish).heap.size == 66 &&
      (match Heap.get? w.heap 66 with
       | some (.closure nm ps _ _ _ ig _ cap) =>
         nm == "put" && ps.size == 3 && ig == false && cap.isEmpty
       | _ => false)
  | _ => false)

/-! And the ONE object it pushes is `putObj`'s own shape — the gate's conclusion,
compared to the engine's heap slot rather than to a description of it. -/
#guard (match callIn sunfish 256 (initWorld sunfish) "Position.move" #[posH 0, mvOf 84 64 ""] with
  | .ok w _ => Heap.get? w.heap 66 == some putObj
  | _ => false)

/-! ### The `put` CALL's own exit law, measured for the next inch

The call gate is NOT proved here (see the file tail). What is measured is what it
will need: one `put(board, k, c)` call inside a real `Position.move` run, and the
fuel the whole method needs, which §L44 pinned at **32**. The call arm's own
branch is pinned above; the three argument evaluations, `callClosure`'s four
guards and the body's two slices are the next inch's bill. -/
#guard (match callIn sunfish 32 (initWorld sunfish) "Position.move" #[posH 0, mvOf 84 64 ""] with
  | .ok _ _ => true | _ => false)
#guard (match callIn sunfish 31 (initWorld sunfish) "Position.move" #[posH 0, mvOf 84 64 ""] with
  | .ok _ _ => false | _ => true)

/-! ### The axioms -/

#print axioms mvB_split
#print axioms mvF_lit
#print axioms mvB_in_tier
#print axioms mvDef_lit
#print axioms move_defines_put
#print axioms mvPut1_lit
#print axioms mvPut2_lit
#print axioms sunfish_not_heapFree
#print axioms putObj_captures

/-! ## What this file does NOT prove — and the bill for it

**F1b is NOT closed.** One statement of thirteen is gated. What is here is the
projection, the six `rfl` pins, and the ONE allocation §L44's exit law measured —
which is the statement the exit law was about, and the foundation the other
twelve thread through. What is owed:

* **the `put` CALL gate** (statements 6 and 7). The path is
  `evalExprs` on three arguments, the module-heap-free branch (pinned above),
  `cellsFor` at a cell-free capture list (`putObj_captures` plus
  `cellsFor_cellFree`), then `callClosure`'s four guards — `argsOk`, `localsOk`,
  `arityOk` at 3, and not-a-generator — and finally the body's single `ret`,
  where §L41's `strSlice_prefix`/`strSlice_suffix` and `putStr_toList` are spent.
  This is the inch's real content and it is the next one to take.
* **statement 5**, `score = self.score + self.value(move)`, which composes
  `value_bound.lean`'s whole eight-statement gate (§L28) as a sub-call;
* **statements 0, 1, 3, 4, 8, 9** — unpacks, reads and tuples, on
  `value_unpacks`' template;
* **statements 10 and 11**, the two `if`s, whose guards are `PlainBoard`'s
  (§L41) and whose bodies are dead under it;
* **statement 12**, the `return` through `Position(…)` and `.rotate()`, where
  §L41's `rotStr_residue` is spent.

The honest reading of the campaign ledger: **F1 is not complete.** F1a is
(§L37), F1b's string and value residues are (§L41, §L44), and F1b's interpreter
gate is one statement into thirteen. -/

end Examples.python.sunfish.move_gate
