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
open Examples.python.sunfish.faillow_census (d4B e4B)
open Examples.python.sunfish.bound_depth (execStmts_singleton_flow execStmt_assign_name)

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

/-! ### §2a THE ALTITUDE LEMMAS the call gate needed

`py_simp` on `put`'s body is a **`whnf` timeout**, not a slow proof: the `ret`'s
expression is a two-`add` chain over two `Expr.slice`s, and §L34's rule — *chains
with EXPENSIVE OPERANDS need altitude lemmas* — is exactly this shape. Each lemma
below proves an interpreter construct's outcome with every operand universally
quantified, so `evalExpr` is never applied to an operand and nothing reduces
under a binder. With them the whole §2 chain elaborates in under two seconds; the
`py_simp` attempt did not finish in two minutes at ten times the heartbeat
budget.

They are stated at a free `Module` and are general (`compare_one`'s family, in
`bound_depth.lean`, is where they belong once a file outside this one wants
them). -/

theorem binOp_two {m : Module} {F : Nat} {st st₁ st₂ : FrameState}
    {l r : Expr} {op : BinOp} {a b v : RVal} {sp : Span}
    (h1 : evalExpr m F st l = .ok st₁ a)
    (h2 : evalExpr m F st₁ r = .ok st₂ b)
    (hop : evalBinOp op a b = .ok v) :
    evalExpr m (F + 1) st (.binOp l op r sp) = .ok st₂ v := by
  rw [evalExpr, h1]
  simp only [Run.bind, h2, Run.liftRes, hop]

theorem slice_four {m : Module} {F : Nat} {st st₁ st₂ st₃ st₄ : FrameState}
    {ev el eu es : Expr} {cv lv uv sv v : RVal} {sp : Span}
    (h1 : evalExpr m F st ev = .ok st₁ cv)
    (h2 : evalExpr m F st₁ el = .ok st₂ lv)
    (h3 : evalExpr m F st₂ eu = .ok st₃ uv)
    (h4 : evalExpr m F st₃ es = .ok st₄ sv)
    (hop : sliceVal cv lv uv sv = .ok v) :
    evalExpr m (F + 1) st (.slice ev el eu es sp) = .ok st₄ v := by
  rw [evalExpr, h1]
  simp only [Run.bind, h2, h3, h4, Run.liftRes, hop]

theorem subscript_two {m : Module} {F : Nat} {st st₁ st₂ : FrameState}
    {ev ek : Expr} {cv kv v : RVal} {sp : Span}
    (h1 : evalExpr m F st ev = .ok st₁ cv)
    (h2 : evalExpr m F st₁ ek = .ok st₂ kv)
    (hop : indexValH st₂.world.heap cv kv = .ok v) :
    evalExpr m (F + 1) st (.subscript ev ek sp) = .ok st₂ v := by
  rw [evalExpr, h1]
  simp only [Run.bind, h2, Run.liftRes, hop]

theorem name_evals {m : Module} {F : Nat} {st : FrameState} {nm : String} {sp : Span}
    {v : RVal} (h : Env.lookup st.locals nm = some v) :
    evalExpr m (F + 1) st (.name nm sp) = .ok st v := by
  rw [evalExpr]
  simp only [h]

theorem const_evals {m : Module} {F : Nat} {st : FrameState} {c : Const} {sp : Span} :
    evalExpr m (F + 1) st (.constant c sp) = .ok st (Const.toRVal c) := by
  rw [evalExpr]

theorem evalExprs_nil {m : Module} {F : Nat} {st : FrameState} :
    evalExprs m (F + 1) st [] = .ok st [] := by rw [evalExprs]

theorem evalExprs_cons {m : Module} {F : Nat} {st st₁ st₂ : FrameState}
    {e : Expr} {rest : List Expr} {v : RVal} {vs : List RVal}
    (h1 : evalExpr m F st e = .ok st₁ v)
    (h2 : evalExprs m F st₁ rest = .ok st₂ vs) :
    evalExprs m (F + 1) st (e :: rest) = .ok st₂ (v :: vs) := by
  rw [evalExprs, h1]
  simp only [Run.bind, h2]

theorem execStmt_ret {m : Module} {F : Nat} {st st₁ : FrameState} {e : Expr} {sp : Span}
    {v : RVal} (h : evalExpr m F st e = .ok st₁ v) :
    execStmt m (F + 1) st (.ret (some e) sp) = .ok st₁ (.ret v) := by
  rw [execStmt, h]
  simp only [Run.bind]

/-- **THE CLOSURE-CALL ARM, at the chain.** A LOCAL name holding a closure ref,
the module NOT heap-free (`sunfish_not_heapFree` is what discharges `hhf` here),
the arguments already decided, the capture list already resolved — and the
callee's own run as a hypothesis, so `callClosure` never unfolds inside a caller.
The caller's locals ride around the call (`Run.withLocals`), which is why the
conclusion's frame is `st₁.locals` and not the callee's. -/
theorem call_closure_local {m : Module} {F : Nat} {st st₁ : FrameState}
    {fname nm : String} {args : Array Expr} {sp fp : Span} {a : Addr}
    {vs : List RVal} {ps : Array Param} {ao lo hg ig : Bool}
    {bd : Array Stmt} {cap cap' : REnv} {w' : World} {v : RVal}
    (hf : Env.lookup st.locals fname = some (.ref a))
    (hargs : evalExprs m F st args.toList = .ok st₁ vs)
    (hhf : (funsHeapFree m.functions.toList && topLevelDefFree m) = false)
    (hobj : Heap.get? st₁.world.heap a = some (.closure nm ps ao lo hg ig bd cap))
    (hcells : cellsFor st₁.world.heap st₁.locals cap = .ok cap')
    (hcall : callClosure m F st₁.world nm ps ao lo ig bd cap' vs.toArray = .ok w' v) :
    evalExpr m (F + 1) st (.call (.name fname fp) args #[] Option.none sp)
      = .ok ⟨w', st₁.locals⟩ v := by
  rw [evalExpr]
  simp only [hf, hargs, Run.bind, hhf, Bool.false_eq_true, if_false, hobj, hcells,
    Run.liftRes, hcall, Run.withLocals]
  rfl

/-- **`callClosure`'s FOUR GUARDS, retired.** `argsOk`, `localsOk`, `arityOk` and
not-a-generator, in the interpreter's own order; what is left is the body. -/
theorem callClosure_body {m : Module} {F : Nat} {w w' : World} {nm : String}
    {ps : Array Param} {bd : Array Stmt} {cap : REnv} {args : Array RVal}
    {e' : REnv} {v : RVal}
    (harity : arityOk ps args.size = true)
    (h : execStmts m F ⟨w, mkCallEnv ps args ++ cap⟩ bd.toList = .ok ⟨w', e'⟩ (.ret v)) :
    callClosure m (F + 1) w nm ps true true false bd cap args = .ok w' v := by
  rw [callClosure]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, harity, h, Run.bind,
    Run.toWorld]

/-! ### §2b `put`'s OWN pieces — the closure, its frame, and its body

Everything here is projected out of `mvDef`, never re-typed: `putParams` and
`putBd` are the statement's own fields, and `putObj_eq` says the object §1
allocates is built from exactly those. -/

/-- `put`'s parameter array — `[board, i, p]`, projected. -/
def putParams : Array Param :=
  match mvDef with | .defStmt _ ps _ _ _ _ _ _ _ => ps | _ => #[]

/-- `put`'s body — the single `ret`, projected. -/
def putBd : Array Stmt :=
  match mvDef with | .defStmt _ _ _ _ _ _ bd _ _ => bd | _ => #[]

theorem putObj_eq : putObj = .closure "put" putParams true true false false putBd [] := rfl

/-- The third of `callClosure`'s four guards, at the shipped arity. -/
theorem putArity : arityOk putParams 3 = true := rfl

/-- The body, SPELLED. §L45's law — an existential body cannot reduce, and a gate
that COMPUTES with the body has to spell it. Sixteen distinct spans; reusing one
would be a wrong pin, not a weak one. -/
theorem putBd_lit : ∃ sA sB sC sD sE sF sG sH sI sJ sK sL sM sN sO sP, putBd.toList =
    [.ret (some (.binOp
        (.binOp (.slice (.name "board" sA) (.constant .none sB) (.name "i" sC)
                  (.constant .none sD) sE)
          .add (.name "p" sF) sG)
        .add
        (.slice (.name "board" sH)
          (.binOp (.name "i" sI) .add (.constant (.int 1) sJ) sK)
          (.constant .none sL) (.constant .none sM) sN) sO)) sP] :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- The frame a `put` call builds. **The lambda's `i` is the CALL's second
argument**, which at statement 6 is `j` — the parameter shadows the enclosing
`i`, and the two `put` calls differ only in what lands here. -/
def putEnv (b : String) (k : Int) (c : String) : REnv :=
  [("board", .str b), ("i", .int k), ("p", .str c)]

theorem putCallEnv (b : String) (k : Int) (c : String) :
    mkCallEnv putParams #[.str b, .int k, .str c] ++ ([] : REnv) = putEnv b k c := rfl

/-- **THE BODY.** `board[:i] + p + board[i + 1:]`, and it answers `putStr` —
which §L41 already proved is `List.set`. The two `Expr.slice`s are discharged by
`putStr_slices`, the F1b-i lemma written for exactly this call; the two `add`s
are `evalBinOp`'s string arm, and `++` is left-associative on both sides. -/
theorem put_body (w : World) (b : String) (k : Nat) (c : Char) (F : Nat)
    (hk : k < b.toList.length) :
    execStmts sunfish (F + 7) ⟨w, putEnv b (k : Int) (String.singleton c)⟩ putBd.toList
      = .ok ⟨w, putEnv b (k : Int) (String.singleton c)⟩ (.ret (.str (putStr b k c))) := by
  obtain ⟨sA, sB, sC, sD, sE, sF, sG, sH, sI, sJ, sK, sL, sM, sN, sO, sP, hlit⟩ := putBd_lit
  obtain ⟨hpre, hsuf⟩ := putStr_slices b k hk
  rw [hlit]
  have hb : Env.lookup (putEnv b (k : Int) (String.singleton c)) "board" = some (.str b) := by
    simp [putEnv, Env.lookup]
  have hi : Env.lookup (putEnv b (k : Int) (String.singleton c)) "i" = some (.int (k : Int)) := by
    simp [putEnv, Env.lookup]
  have hp : Env.lookup (putEnv b (k : Int) (String.singleton c)) "p"
      = some (.str (String.singleton c)) := by simp [putEnv, Env.lookup]
  have es1 : evalExpr sunfish (F + 3) ⟨w, putEnv b (k : Int) (String.singleton c)⟩
      (.slice (.name "board" sA) (.constant .none sB) (.name "i" sC) (.constant .none sD) sE)
      = .ok ⟨w, putEnv b (k : Int) (String.singleton c)⟩
          (.str (String.ofList (b.toList.take k))) :=
    slice_four (name_evals hb) const_evals (name_evals hi) const_evals hpre
  have elo : evalExpr sunfish (F + 3) ⟨w, putEnv b (k : Int) (String.singleton c)⟩
      (.binOp (.name "i" sI) .add (.constant (.int 1) sJ) sK)
      = .ok ⟨w, putEnv b (k : Int) (String.singleton c)⟩ (.int ((k : Int) + 1)) :=
    binOp_two (name_evals hi) const_evals rfl
  have es2 : evalExpr sunfish (F + 4) ⟨w, putEnv b (k : Int) (String.singleton c)⟩
      (.slice (.name "board" sH) (.binOp (.name "i" sI) .add (.constant (.int 1) sJ) sK)
        (.constant .none sL) (.constant .none sM) sN)
      = .ok ⟨w, putEnv b (k : Int) (String.singleton c)⟩
          (.str (String.ofList (b.toList.drop (k + 1)))) :=
    slice_four (name_evals hb) elo const_evals const_evals hsuf
  have einner : evalExpr sunfish (F + 4) ⟨w, putEnv b (k : Int) (String.singleton c)⟩
      (.binOp (.slice (.name "board" sA) (.constant .none sB) (.name "i" sC)
                (.constant .none sD) sE) .add (.name "p" sF) sG)
      = .ok ⟨w, putEnv b (k : Int) (String.singleton c)⟩
          (.str (String.ofList (b.toList.take k) ++ String.singleton c)) :=
    binOp_two es1 (name_evals hp) rfl
  have eall : evalExpr sunfish (F + 5) ⟨w, putEnv b (k : Int) (String.singleton c)⟩
      (.binOp (.binOp (.slice (.name "board" sA) (.constant .none sB) (.name "i" sC)
                  (.constant .none sD) sE) .add (.name "p" sF) sG) .add
        (.slice (.name "board" sH)
          (.binOp (.name "i" sI) .add (.constant (.int 1) sJ) sK)
          (.constant .none sL) (.constant .none sM) sN) sO)
      = .ok ⟨w, putEnv b (k : Int) (String.singleton c)⟩ (.str (putStr b k c)) :=
    binOp_two einner es2 rfl
  exact execStmts_singleton_flow (execStmt_ret eall)

/-- **THE CALL, through `callClosure`.** The four guards and the body, composed:
`put` is heap-free — the world in is the world out — which is the other half of
§L44's exit law (one allocation at the `def`, none at either call). -/
theorem put_call (w : World) (b : String) (k : Nat) (c : Char) (F : Nat)
    (hk : k < b.toList.length) :
    callClosure sunfish (F + 8) w "put" putParams true true false putBd []
        #[.str b, .int (k : Int), .str (String.singleton c)]
      = .ok w (.str (putStr b k c)) := by
  have h := put_body w b k c F hk
  rw [← putCallEnv b (k : Int) (String.singleton c)] at h
  exact callClosure_body putArity h

/-! ### §2c THE TWO STATEMENTS

`board[i]` is a `Char` here rather than `value_bound`'s one-character `String`,
because that is what `putStr` takes and what F1a's `moveCells` is written in.
`cellAt` is the interpreter's own residue with the cast discharged. -/

/-- The character on a square, as a `Char` — the interpreter's own `getD`. -/
def cellAt (b : String) (i : Nat) : Char := b.toList.getD i ' '

theorem strIndex_inRange (h : Heap) (b : String) (i : Nat) (hi : i < b.toList.length) :
    indexValH h (.str b) (.int (i : Int)) = .ok (.str (String.singleton (cellAt b i))) := by
  have hlen : b.length = b.toList.length := by rw [String.length_toList]
  simp only [indexValH, indexVal, asInt, normIndex, cellAt, hlen,
    if_neg (show ¬ ((i : Int) < 0) from by omega),
    if_pos (show (0 ≤ (i : Int) ∧ (i : Int) < (b.toList.length : Int)) from ⟨by omega, by omega⟩)]
  norm_cast

/-- **GATE — statement 6, `board = put(board, j, board[i])`.** The mover lands on
the target square. Heap-free at a free world and a free frame. -/
theorem move_puts_target (w : World) (e : REnv) (a : Addr) (b : String) (i j : Nat) (F : Nat)
    (hput : Env.lookup e "put" = some (.ref a))
    (hobj : Heap.get? w.heap a = some putObj)
    (hb : Env.lookup e "board" = some (.str b))
    (hi : Env.lookup e "i" = some (.int (i : Int)))
    (hj : Env.lookup e "j" = some (.int (j : Int)))
    (hib : i < b.toList.length) (hjb : j < b.toList.length) :
    execStmt sunfish (F + 10) ⟨w, e⟩ mvPut1
      = .ok ⟨w, Env.set e "board" (.str (putStr b j (cellAt b i)))⟩ .next := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, hlit⟩ := mvPut1_lit
  rw [hlit]
  have ea3 : evalExpr sunfish (F + 5) (⟨w, e⟩ : FrameState)
      (.subscript (.name "board" s5) (.name "i" s6) s7)
      = .ok ⟨w, e⟩ (.str (String.singleton (cellAt b i))) :=
    subscript_two (name_evals hb) (name_evals hi) (strIndex_inRange w.heap b i hib)
  have eargs : evalExprs sunfish (F + 8) (⟨w, e⟩ : FrameState)
      [.name "board" s3, .name "j" s4, .subscript (.name "board" s5) (.name "i" s6) s7]
      = .ok ⟨w, e⟩ [.str b, .int (j : Int), .str (String.singleton (cellAt b i))] :=
    evalExprs_cons (name_evals hb) (evalExprs_cons (name_evals hj)
      (evalExprs_cons ea3 evalExprs_nil))
  exact execStmt_assign_name
    (call_closure_local (m := sunfish) (F := F + 8) (st := ⟨w, e⟩)
      hput eargs sunfish_not_heapFree (by rw [hobj, putObj_eq])
      (cellsFor_cellFree w.heap e [] rfl) (put_call w b j (cellAt b i) F hjb))

/-- **GATE — statement 7, `board = put(board, i, ".")`.** The square the mover
left becomes empty. Same chain; the only difference is that the third argument is
a CONSTANT rather than a subscript. -/
theorem move_puts_source (w : World) (e : REnv) (a : Addr) (b : String) (i : Nat) (F : Nat)
    (hput : Env.lookup e "put" = some (.ref a))
    (hobj : Heap.get? w.heap a = some putObj)
    (hb : Env.lookup e "board" = some (.str b))
    (hi : Env.lookup e "i" = some (.int (i : Int)))
    (hib : i < b.toList.length) :
    execStmt sunfish (F + 10) ⟨w, e⟩ mvPut2
      = .ok ⟨w, Env.set e "board" (.str (putStr b i '.'))⟩ .next := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, hlit⟩ := mvPut2_lit
  rw [hlit]
  have eargs : evalExprs sunfish (F + 8) (⟨w, e⟩ : FrameState)
      [.name "board" s3, .name "i" s4, .constant (.str ".") s5]
      = .ok ⟨w, e⟩ [.str b, .int (i : Int), .str (String.singleton '.')] :=
    evalExprs_cons (name_evals hb) (evalExprs_cons (name_evals hi)
      (evalExprs_cons const_evals evalExprs_nil))
  exact execStmt_assign_name
    (call_closure_local (m := sunfish) (F := F + 8) (st := ⟨w, e⟩)
      hput eargs sunfish_not_heapFree (by rw [hobj, putObj_eq])
      (cellsFor_cellFree w.heap e [] rfl) (put_call w b i '.' F hib))

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

/-! ### The whole method's fuel, which §L44 pinned at **32**. -/
#guard (match callIn sunfish 32 (initWorld sunfish) "Position.move" #[posH 0, mvOf 84 64 ""] with
  | .ok _ _ => true | _ => false)
#guard (match callIn sunfish 31 (initWorld sunfish) "Position.move" #[posH 0, mvOf 84 64 ""] with
  | .ok _ _ => false | _ => true)

/-! ### §2, INSTANTIATED on the shipped engine

The two gates conclude with `putStr b j (cellAt b i)` and `putStr b i '.'`. Run
them in that order on the opening board and rotate — the third call
`Position.move` makes — and the answer is the child the ENGINE returns, character
for character. `d4B` and `e4B` are `faillow_census`'s shipped children, measured
against CPython before F1a existed.

The first guard checks the mover the gate reads (`cellAt`, the subscript's own
residue); the second and third are the gates' conclusions composed; the fourth
runs the shipped `Position.move` and compares its returned board to the same
string. Nothing here is a constant this file wrote. -/
#guard cellAt board0 84 == 'P' && cellAt board0 85 == 'P'
#guard rotStr (putStr (putStr board0 64 (cellAt board0 84)) 84 '.') == d4B
#guard rotStr (putStr (putStr board0 65 (cellAt board0 85)) 85 '.') == e4B
#guard (match callIn sunfish 32 (initWorld sunfish) "Position.move" #[posH 0, mvOf 84 64 ""] with
  | .ok _ (.ntuple _ _ xs) => xs[0]?.getD .none == .str d4B
  | _ => false)
#guard (match callIn sunfish 32 (initWorld sunfish) "Position.move" #[posH 0, mvOf 85 65 ""] with
  | .ok _ (.ntuple _ _ xs) => xs[0]?.getD .none == .str e4B
  | _ => false)

/-! And the call ALLOCATES NOTHING — `put_call`'s world in is its world out. The
heap after the whole method is 67 slots and only slot 66 (the `def`'s closure)
differs, so neither of the two calls touched it: §L44's exit law, from the call
side. -/
#guard (match callIn sunfish 32 (initWorld sunfish) "Position.move" #[posH 0, mvOf 84 64 ""] with
  | .ok w _ =>
    w.heap.size == 67 &&
      (List.range 66).all (fun k => Heap.get? (initWorld sunfish).heap k == Heap.get? w.heap k)
  | _ => false)

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
#print axioms binOp_two
#print axioms slice_four
#print axioms subscript_two
#print axioms call_closure_local
#print axioms callClosure_body
#print axioms putObj_eq
#print axioms putBd_lit
#print axioms strIndex_inRange
#print axioms put_body
#print axioms put_call
#print axioms move_puts_target
#print axioms move_puts_source

/-! ## What this file does NOT prove — and the bill for it

**F1b is NOT closed.** THREE statements of thirteen are gated: the `def` (§1) and
the two `put` calls (§2), which §L45 named as *"the inch's real content"*. What is
owed:

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
gate is three statements into thirteen. -/

end Examples.python.sunfish.move_gate
