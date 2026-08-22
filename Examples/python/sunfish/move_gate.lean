/-
**F1b-iii — `Position.move`'s GATE**, thirteen statements at a free board.
docs/backlog.md §L44 projected the body and measured its exit law; this file is
the gate that measurement decided the shape of.
-/
import Examples.python.sunfish.move_residue
import Examples.python.sunfish.value_bound

namespace Examples.python.sunfish.move_gate

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)
open Examples.python.sunfish.basecase_depth0 (mvOf)
open Examples.python.sunfish.move_residue
open Examples.python.sunfish.faillow_census (d4B e4B)
open Examples.python.sunfish.value_bound (boardAt a1G h1G a8G h8G)
open Examples.python.sunfish.bound_depth (execStmts_singleton_flow execStmts_singleton
  execStmt_assign_name execStmt_if_true execStmt_if_false compare_one boolChain_and_falsy
  boolChain_and2 posCAux posCls posCls_methods posCls_ntBase_isSome absG absNotFun absCls absNT)

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

/-! ## §3 THE FOUR PLAIN STATEMENTS — unpacks, reads and tuples

Statements 0, 1, 3 and 4 are `value_unpacks`' and `value_reads_pq`' template
verbatim: no allocation, no call, and `py_simp` closes each one. Statement 1 is
the SAME SOURCE LINE as `Position.value`'s statement 1, so its gate says the same
thing with the same `boardAt`. -/

theorem mvUnpack_lit : ∃ p0 p1 p2 p3 p4 p5, mvUnpack =
    .assign #[.tuple #[.name "i" p0, .name "j" p1, .name "prom" p2] p3] (.name "move" p4) p5 :=
  ⟨_, _, _, _, _, _, rfl⟩

theorem mvPQ_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12, mvPQ =
    .assign #[.tuple #[.name "p" p0, .name "q" p1] p2]
      (.tuple #[.subscript (.attribute (.name "self" p3) "board" p4) (.name "i" p5) p6,
                .subscript (.attribute (.name "self" p7) "board" p8) (.name "j" p9) p10]
        p11) p12 :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem mvBoard_lit : ∃ p0 p1 p2 p3, mvBoard =
    .assign #[.name "board" p0] (.attribute (.name "self" p1) "board" p2) p3 :=
  ⟨_, _, _, _, rfl⟩

theorem mvFields_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12, mvFields =
    .assign #[.tuple #[.name "wc" p0, .name "bc" p1, .name "ep" p2, .name "kp" p3] p4]
      (.tuple #[.attribute (.name "self" p5) "wc" p6, .attribute (.name "self" p7) "bc" p8,
                .constant (.int 0) p9, .constant (.int 0) p10] p11) p12 :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- **GATE — statement 0, `i, j, prom = move`.** -/
theorem move_unpacks (w : World) (e : REnv) (i j : Int) (prom : String) (F : Nat)
    (hm : Env.lookup e "move" = some (mvOf i j prom)) :
    execStmt sunfish (F + 3) ⟨w, e⟩ mvUnpack
      = .ok ⟨w, Env.set (Env.set (Env.set e "i" (.int i)) "j" (.int j))
              "prom" (.str prom)⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, h⟩ := mvUnpack_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hm, mvOf]

/-- **GATE — statement 1, `p, q = self.board[i], self.board[j]`.** -/
theorem move_reads_pq (w : World) (e : REnv) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp i j : Int) (F : Nat)
    (hself : Env.lookup e "self" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hei : Env.lookup e "i" = some (.int i))
    (hej : Env.lookup e "j" = some (.int j))
    (hi : 0 ≤ i) (hi' : i < (b.length : Int))
    (hj : 0 ≤ j) (hj' : j < (b.length : Int)) :
    execStmt sunfish (F + 7) ⟨w, e⟩ mvPQ
      = .ok ⟨w, Env.set (Env.set e "p" (.str (boardAt b i))) "q" (.str (boardAt b j))⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, h⟩ := mvPQ_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hself, hei, hej, posOf, posCAux, posCls_methods,
    boardAt, normIndex, if_neg (show ¬ i < 0 by omega), if_neg (show ¬ j < 0 by omega),
    if_pos (show (0 ≤ i ∧ i < (b.length : Int)) from ⟨hi, hi'⟩),
    if_pos (show (0 ≤ j ∧ j < (b.length : Int)) from ⟨hj, hj'⟩)]

/-- **GATE — statement 3, `board = self.board`.** -/
theorem move_copies_board (w : World) (e : REnv) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (F : Nat)
    (hself : Env.lookup e "self" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp)) :
    execStmt sunfish (F + 3) ⟨w, e⟩ mvBoard
      = .ok ⟨w, Env.set e "board" (.str b)⟩ .next := by
  obtain ⟨p0, p1, p2, p3, h⟩ := mvBoard_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hself, posOf, posCAux, posCls_methods]

/-- **GATE — statement 4, `wc, bc, ep, kp = self.wc, self.bc, 0, 0`.** The two
reset fields are the reason `Position.move`'s child never carries a stale
en-passant or king-passant square. -/
theorem move_resets_fields (w : World) (e : REnv) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (F : Nat)
    (hself : Env.lookup e "self" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp)) :
    execStmt sunfish (F + 8) ⟨w, e⟩ mvFields
      = .ok ⟨w, Env.set (Env.set (Env.set (Env.set e
              "wc" (.tuple #[.bool wc0, .bool wc1])) "bc" (.tuple #[.bool bc0, .bool bc1]))
              "ep" (.int 0)) "kp" (.int 0)⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, h⟩ := mvFields_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hself, posOf, posCAux, posCls_methods]

/-! ## §4 THE CASTLING-RIGHTS TUPLES — statements 8 and 9

`wc = (wc[0] and i != A1, wc[1] and i != H1)`. Three constructs meet here: a
tuple display, two `and` chains, and two comparisons against module globals that
resolve STATICALLY (`A1 = 91`, `H1 = 98`, `H8 = 28`, `A8 = 21` — `value_bound`'s
own census). At two `Bool` operands Python's `and` and Lean's `&&` agree on both
arms, so `boolOp_and2_bool` states one answer where the two-gates-per-`if` law
would otherwise ask for two. -/

theorem tuple_evals {m : Module} {F : Nat} {st st' : FrameState}
    {elts : Array Expr} {vs : List RVal} {sp : Span}
    (h : evalExprs m F st elts.toList = .ok st' vs) :
    evalExpr m (F + 1) st (.tuple elts sp) = .ok st' (.tuple vs.toArray) := by
  rw [evalExpr, h]
  simp only [Run.bind]

/-- A name that resolves in the module's STATIC globals — the arm `A1`, `H1`,
`A8`, `H8` and `N` take, none of which is in any frame. -/
theorem globalName_evals {m : Module} {F : Nat} {st : FrameState} {nm : String} {sp : Span}
    {v : RVal} (hl : Env.lookup st.locals nm = Option.none)
    (hg : lookupG (moduleGlobals m).1 nm = some (some v)) :
    evalExpr m (F + 1) st (.name nm sp) = .ok st v := by
  rw [evalExpr]
  simp only [hl, hg]

/-- **`x and y` at two BOOLEANS, one lemma instead of two arms.** Python's `and`
answers the FIRST operand when it is falsy and the SECOND otherwise; at two
`Bool`s both arms are `.bool (p && q)`, so the case split lives inside the proof
rather than in two gates. -/
theorem boolOp_and2_bool {m : Module} {F : Nat} {st : FrameState}
    {e1 e2 : Expr} {sp : Span} {p q : Bool}
    (h1 : evalExpr m (F + 1) st e1 = .ok st (.bool p))
    (h2 : evalExpr m F st e2 = .ok st (.bool q)) :
    evalExpr m (F + 3) st (.boolOp .and #[e1, e2] sp) = .ok st (.bool (p && q)) := by
  rw [evalExpr]
  cases p with
  | false => exact boolChain_and_falsy h1 rfl
  | true => simpa using boolChain_and2 h1 rfl h2

theorem a1Gm : lookupG (moduleGlobals sunfish).1 "A1" = some (some (.int 91)) := a1G
theorem h1Gm : lookupG (moduleGlobals sunfish).1 "H1" = some (some (.int 98)) := h1G
theorem a8Gm : lookupG (moduleGlobals sunfish).1 "A8" = some (some (.int 21)) := a8G
theorem h8Gm : lookupG (moduleGlobals sunfish).1 "H8" = some (some (.int 28)) := h8G
/-- `N = -10`, the pawn's step — the one global this file adds to the census. -/
theorem nG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "N"
    = some (some (.int (-10))) := rfl
theorem nGm : lookupG (moduleGlobals sunfish).1 "N" = some (some (.int (-10))) := nG

theorem pairIndex0 (h : Heap) (x y : Bool) :
    indexValH h (.tuple #[.bool x, .bool y]) (.int 0) = .ok (.bool x) := rfl
theorem pairIndex1 (h : Heap) (x y : Bool) :
    indexValH h (.tuple #[.bool x, .bool y]) (.int 1) = .ok (.bool y) := rfl

theorem beqInt (x y : Int) : (x == y) = decide (x = y) := by
  by_cases h : x = y
  · simp [h]
  · simp [h]

theorem neqInt (h : Heap) (F : Nat) (x y : Int) :
    evalCompareOpH h F .notEq (.int x) (.int y) = .ok (decide (x ≠ y)) := by
  simp [evalCompareOpH, RVal.refFree, valEq, beqInt]

theorem mvWc_lit : ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16, mvWc =
    .assign #[.name "wc" a0]
      (.tuple #[
        .boolOp .and #[.subscript (.name "wc" a1) (.constant (.int 0) a2) a3,
                       .compare (.name "i" a4) #[.notEq] #[.name "A1" a5] a6] a7,
        .boolOp .and #[.subscript (.name "wc" a8) (.constant (.int 1) a9) a10,
                       .compare (.name "i" a11) #[.notEq] #[.name "H1" a12] a13] a14]
        a15) a16 :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem mvBc_lit : ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16, mvBc =
    .assign #[.name "bc" a0]
      (.tuple #[
        .boolOp .and #[.subscript (.name "bc" a1) (.constant (.int 0) a2) a3,
                       .compare (.name "j" a4) #[.notEq] #[.name "H8" a5] a6] a7,
        .boolOp .and #[.subscript (.name "bc" a8) (.constant (.int 1) a9) a10,
                       .compare (.name "j" a11) #[.notEq] #[.name "A8" a12] a13] a14]
        a15) a16 :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- **GATE — statement 8, WHITE's castling rights.** Each flag survives unless
the mover left that corner. -/
theorem move_wc (w : World) (e : REnv) (wc0 wc1 : Bool) (i : Int) (F : Nat)
    (hwc : Env.lookup e "wc" = some (.tuple #[.bool wc0, .bool wc1]))
    (hei : Env.lookup e "i" = some (.int i))
    (hna1 : Env.lookup e "A1" = Option.none)
    (hnh1 : Env.lookup e "H1" = Option.none) :
    execStmt sunfish (F + 12) ⟨w, e⟩ mvWc
      = .ok ⟨w, Env.set e "wc" (.tuple #[.bool (wc0 && decide (i ≠ 91)),
              .bool (wc1 && decide (i ≠ 98))])⟩ .next := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
    hlit⟩ := mvWc_lit
  rw [hlit]
  have c1 : evalExpr sunfish (F + 6) (⟨w, e⟩ : FrameState)
      (.compare (.name "i" a4) #[.notEq] #[.name "A1" a5] a6)
      = .ok ⟨w, e⟩ (.bool (decide (i ≠ 91))) :=
    compare_one (name_evals hei) (globalName_evals hna1 a1Gm) (neqInt w.heap (F + 4) i 91)
  have c2 : evalExpr sunfish (F + 5) (⟨w, e⟩ : FrameState)
      (.compare (.name "i" a11) #[.notEq] #[.name "H1" a12] a13)
      = .ok ⟨w, e⟩ (.bool (decide (i ≠ 98))) :=
    compare_one (name_evals hei) (globalName_evals hnh1 h1Gm) (neqInt w.heap (F + 3) i 98)
  have s1 : evalExpr sunfish (F + 7) (⟨w, e⟩ : FrameState)
      (.subscript (.name "wc" a1) (.constant (.int 0) a2) a3) = .ok ⟨w, e⟩ (.bool wc0) :=
    subscript_two (name_evals hwc) const_evals (pairIndex0 w.heap wc0 wc1)
  have s2 : evalExpr sunfish (F + 6) (⟨w, e⟩ : FrameState)
      (.subscript (.name "wc" a8) (.constant (.int 1) a9) a10) = .ok ⟨w, e⟩ (.bool wc1) :=
    subscript_two (name_evals hwc) const_evals (pairIndex1 w.heap wc0 wc1)
  exact execStmt_assign_name (tuple_evals
    (evalExprs_cons (boolOp_and2_bool s1 c1) (evalExprs_cons (boolOp_and2_bool s2 c2)
      evalExprs_nil)))

/-- **GATE — statement 9, BLACK's.** The mirror, and the corners are crossed:
`bc[0]` is tested against `H8` and `bc[1]` against `A8`, which is the shipped
line and not a typo. -/
theorem move_bc (w : World) (e : REnv) (bc0 bc1 : Bool) (j : Int) (F : Nat)
    (hbc : Env.lookup e "bc" = some (.tuple #[.bool bc0, .bool bc1]))
    (hej : Env.lookup e "j" = some (.int j))
    (hna8 : Env.lookup e "A8" = Option.none)
    (hnh8 : Env.lookup e "H8" = Option.none) :
    execStmt sunfish (F + 12) ⟨w, e⟩ mvBc
      = .ok ⟨w, Env.set e "bc" (.tuple #[.bool (bc0 && decide (j ≠ 28)),
              .bool (bc1 && decide (j ≠ 21))])⟩ .next := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
    hlit⟩ := mvBc_lit
  rw [hlit]
  have c1 : evalExpr sunfish (F + 6) (⟨w, e⟩ : FrameState)
      (.compare (.name "j" a4) #[.notEq] #[.name "H8" a5] a6)
      = .ok ⟨w, e⟩ (.bool (decide (j ≠ 28))) :=
    compare_one (name_evals hej) (globalName_evals hnh8 h8Gm) (neqInt w.heap (F + 4) j 28)
  have c2 : evalExpr sunfish (F + 5) (⟨w, e⟩ : FrameState)
      (.compare (.name "j" a11) #[.notEq] #[.name "A8" a12] a13)
      = .ok ⟨w, e⟩ (.bool (decide (j ≠ 21))) :=
    compare_one (name_evals hej) (globalName_evals hna8 a8Gm) (neqInt w.heap (F + 3) j 21)
  have s1 : evalExpr sunfish (F + 7) (⟨w, e⟩ : FrameState)
      (.subscript (.name "bc" a1) (.constant (.int 0) a2) a3) = .ok ⟨w, e⟩ (.bool bc0) :=
    subscript_two (name_evals hbc) const_evals (pairIndex0 w.heap bc0 bc1)
  have s2 : evalExpr sunfish (F + 6) (⟨w, e⟩ : FrameState)
      (.subscript (.name "bc" a8) (.constant (.int 1) a9) a10) = .ok ⟨w, e⟩ (.bool bc1) :=
    subscript_two (name_evals hbc) const_evals (pairIndex1 w.heap bc0 bc1)
  exact execStmt_assign_name (tuple_evals
    (evalExprs_cons (boolOp_and2_bool s1 c1) (evalExprs_cons (boolOp_and2_bool s2 c2)
      evalExprs_nil)))

/-! ## §5 THE TWO `if`s — statements 10 and 11

Two gates per `if` (§L28's law), and the bodies are PEELED rather than inlined so
the arms compose instead of being enumerated. Under `PlainBoard` (§L41) the
castling block's inner `if` is dead, the promotion arm is dead and the
en-passant capture is dead — but the pawn block's DOUBLE PUSH is not, and it is
the one arm of the four that fires. §L41 said so in prose (*"the double-push arm
writes only `ep` and never the board, so it is NOT excluded"*); this is that
sentence as two gates. -/

private def mvKingB : List Stmt := match mvKing with | .ifStmt _ b _ _ => b.toList | _ => []
/-- `wc = (False, False)`. -/
def mvKingWc : Stmt := nth 0 mvKingB
/-- `if abs(j - i) == 2: …` — the rook slide. -/
def mvKingCastle : Stmt := nth 1 mvKingB

theorem mvKingB_split : mvKingB = [mvKingWc, mvKingCastle] := rfl

theorem mvKing_lit : ∃ a b c d, mvKing =
    .ifStmt (.compare (.name "p" a) #[.eq] #[.constant (.str "K") b] c)
      mvKingB.toArray #[] d :=
  ⟨_, _, _, _, rfl⟩

theorem mvKingWc_lit : ∃ a b c d e, mvKingWc =
    .assign #[.name "wc" a]
      (.tuple #[.constant (.bool false) b, .constant (.bool false) c] d) e :=
  ⟨_, _, _, _, _, rfl⟩

theorem mvKingCastle_lit : ∃ (bd : Array Stmt) (a b c d e f g h : Span), mvKingCastle =
    .ifStmt (.compare (.call (.name "abs" a)
        #[.binOp (.name "j" b) .sub (.name "i" c) d] #[] Option.none e)
      #[.eq] #[.constant (.int 2) f] g) bd #[] h :=
  ⟨_, _, _, _, _, _, _, _, _, rfl⟩

/-- **GATE 10a — the mover is not the king**, and the whole block is dead. -/
theorem move_king_skips (w : World) (e : REnv) (pc : String) (F : Nat)
    (hp : Env.lookup e "p" = some (.str pc)) (hne : pc ≠ "K") :
    execStmt sunfish (F + 7) ⟨w, e⟩ mvKing = .ok ⟨w, e⟩ .next := by
  obtain ⟨a, b, c, d, hlit⟩ := mvKing_lit
  have hc : evalExpr sunfish (F + 6) (⟨w, e⟩ : FrameState)
      (.compare (.name "p" a) #[.eq] #[.constant (.str "K") b] c) = .ok ⟨w, e⟩ (.bool false) := by
    py_simp [-globalsFold, -globalsStep, hp, if_neg hne]
  rw [hlit, execStmt_if_false hc rfl]
  rfl

/-- **GATE 10b — the PEEL.** A king enters, and what is left is the two inner
statements. -/
theorem move_king_enters (w : World) (e : REnv) (F : Nat)
    (hp : Env.lookup e "p" = some (.str "K")) :
    execStmt sunfish (F + 7) ⟨w, e⟩ mvKing
      = execStmts sunfish (F + 6) ⟨w, e⟩ [mvKingWc, mvKingCastle] := by
  obtain ⟨a, b, c, d, hlit⟩ := mvKing_lit
  have hc : evalExpr sunfish (F + 6) (⟨w, e⟩ : FrameState)
      (.compare (.name "p" a) #[.eq] #[.constant (.str "K") b] c) = .ok ⟨w, e⟩ (.bool true) := by
    py_simp [-globalsFold, -globalsStep, hp]
  have hL : mvKingB.toArray.toList = [mvKingWc, mvKingCastle] := by simp [mvKingB_split]
  rw [hlit, execStmt_if_true hc rfl, hL]

/-- **GATE 10c — a king move forfeits BOTH rights**, unconditionally. -/
theorem move_king_clears_wc (w : World) (e : REnv) (F : Nat) :
    execStmt sunfish (F + 7) ⟨w, e⟩ mvKingWc
      = .ok ⟨w, Env.set e "wc" (.tuple #[.bool false, .bool false])⟩ .next := by
  obtain ⟨a, b, c, d, e', hlit⟩ := mvKingWc_lit
  rw [hlit]
  py_simp [-globalsFold, -globalsStep]

/-- **GATE 10d — the king moved ONE square**, so the rook slide is dead. This is
`PlainBoard`'s first conjunct, spent. -/
theorem move_castle_skips (w : World) (e : REnv) (i j : Int) (F : Nat)
    (hei : Env.lookup e "i" = some (.int i))
    (hej : Env.lookup e "j" = some (.int j))
    (hna : Env.lookup e "abs" = Option.none)
    (hshort : j - i ≠ 2 ∧ i - j ≠ 2) :
    execStmt sunfish (F + 9) ⟨w, e⟩ mvKingCastle = .ok ⟨w, e⟩ .next := by
  obtain ⟨bd, a, b, c, d, e', f, g, h, hlit⟩ := mvKingCastle_lit
  have habs : ¬ ((if j - i < 0 then -(j - i) else j - i) = 2) := by
    obtain ⟨h1, h2⟩ := hshort; split <;> omega
  have hc : evalExpr sunfish (F + 8) (⟨w, e⟩ : FrameState)
      (.compare (.call (.name "abs" a) #[.binOp (.name "j" b) .sub (.name "i" c) d] #[]
        Option.none e') #[.eq] #[.constant (.int 2) f] g) = .ok ⟨w, e⟩ (.bool false) := by
    py_simp [-globalsFold, -globalsStep, hei, hej, hna, absG, absNotFun, absCls, absNT,
      if_neg habs]
  rw [hlit, execStmt_if_false hc rfl]
  rfl

private def mvPawnB : List Stmt := match mvPawn with | .ifStmt _ b _ _ => b.toList | _ => []
/-- `if A8 <= j <= H8: board = put(board, j, prom)` — promotion. -/
def mvProm : Stmt := nth 0 mvPawnB
/-- `if j - i == 2 * N: ep = i + N` — the DOUBLE PUSH, the one live arm. -/
def mvEpSet : Stmt := nth 1 mvPawnB
/-- `if j == self.ep: board = put(board, j + S, ".")` — en-passant capture. -/
def mvEpCap : Stmt := nth 2 mvPawnB

theorem mvPawnB_split : mvPawnB = [mvProm, mvEpSet, mvEpCap] := rfl

theorem mvPawn_lit : ∃ a b c d, mvPawn =
    .ifStmt (.compare (.name "p" a) #[.eq] #[.constant (.str "P") b] c)
      mvPawnB.toArray #[] d :=
  ⟨_, _, _, _, rfl⟩

theorem mvProm_lit : ∃ (bd : Array Stmt) (a b c d e : Span), mvProm =
    .ifStmt (.compare (.name "A8" a) #[.ltE, .ltE] #[.name "j" b, .name "H8" c] d) bd #[] e :=
  ⟨_, _, _, _, _, _, rfl⟩

theorem mvEpSet_lit : ∃ a b c d e f g h i k l m n, mvEpSet =
    .ifStmt (.compare (.binOp (.name "j" a) .sub (.name "i" b) c) #[.eq]
        #[.binOp (.constant (.int 2) d) .mult (.name "N" e) f] g)
      #[.assign #[.name "ep" h] (.binOp (.name "i" i) .add (.name "N" k) l) m] #[] n :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem mvEpCap_lit : ∃ (bd : Array Stmt) (a b c d e : Span), mvEpCap =
    .ifStmt (.compare (.name "j" a) #[.eq] #[.attribute (.name "self" b) "ep" c] d) bd #[] e :=
  ⟨_, _, _, _, _, _, rfl⟩

/-- **GATE 11a — the mover is not a pawn**, and the whole block is dead. -/
theorem move_pawn_skips (w : World) (e : REnv) (pc : String) (F : Nat)
    (hp : Env.lookup e "p" = some (.str pc)) (hne : pc ≠ "P") :
    execStmt sunfish (F + 7) ⟨w, e⟩ mvPawn = .ok ⟨w, e⟩ .next := by
  obtain ⟨a, b, c, d, hlit⟩ := mvPawn_lit
  have hc : evalExpr sunfish (F + 6) (⟨w, e⟩ : FrameState)
      (.compare (.name "p" a) #[.eq] #[.constant (.str "P") b] c) = .ok ⟨w, e⟩ (.bool false) := by
    py_simp [-globalsFold, -globalsStep, hp, if_neg hne]
  rw [hlit, execStmt_if_false hc rfl]
  rfl

/-- **GATE 11b — the PEEL.** Three sibling `if`s, each with its own gate, so the
combinations compose. -/
theorem move_pawn_enters (w : World) (e : REnv) (F : Nat)
    (hp : Env.lookup e "p" = some (.str "P")) :
    execStmt sunfish (F + 7) ⟨w, e⟩ mvPawn
      = execStmts sunfish (F + 6) ⟨w, e⟩ [mvProm, mvEpSet, mvEpCap] := by
  obtain ⟨a, b, c, d, hlit⟩ := mvPawn_lit
  have hc : evalExpr sunfish (F + 6) (⟨w, e⟩ : FrameState)
      (.compare (.name "p" a) #[.eq] #[.constant (.str "P") b] c) = .ok ⟨w, e⟩ (.bool true) := by
    py_simp [-globalsFold, -globalsStep, hp]
  have hL : mvPawnB.toArray.toList = [mvProm, mvEpSet, mvEpCap] := by simp [mvPawnB_split]
  rw [hlit, execStmt_if_true hc rfl, hL]

/-- **GATE 11c — the pawn does not reach the last rank**, so the promotion `put`
never runs. `PlainBoard`'s second conjunct, first half. -/
theorem move_prom_skips (w : World) (e : REnv) (j : Int) (F : Nat)
    (hej : Env.lookup e "j" = some (.int j))
    (hna : Env.lookup e "A8" = Option.none)
    (hnh : Env.lookup e "H8" = Option.none)
    (hout : j < 21 ∨ 28 < j) :
    execStmt sunfish (F + 7) ⟨w, e⟩ mvProm = .ok ⟨w, e⟩ .next := by
  obtain ⟨bd, a, b, c, d, e', hlit⟩ := mvProm_lit
  have hc : evalExpr sunfish (F + 6) (⟨w, e⟩ : FrameState)
      (.compare (.name "A8" a) #[.ltE, .ltE] #[.name "j" b, .name "H8" c] d)
        = .ok ⟨w, e⟩ (.bool false) := by
    py_simp [-globalsFold, -globalsStep, hej, hna, hnh, a8G, h8G]
    omega
  rw [hlit, execStmt_if_false hc rfl]
  rfl

/-- **GATE 11d — not a double push**, so `ep` keeps the `0` statement 4 reset it
to. -/
theorem move_ep_set_skips (w : World) (e : REnv) (i j : Int) (F : Nat)
    (hei : Env.lookup e "i" = some (.int i))
    (hej : Env.lookup e "j" = some (.int j))
    (hnn : Env.lookup e "N" = Option.none)
    (hne : j - i ≠ -20) :
    execStmt sunfish (F + 8) ⟨w, e⟩ mvEpSet = .ok ⟨w, e⟩ .next := by
  obtain ⟨a, b, c, d, e', f, g, h, i', k, l, m, n, hlit⟩ := mvEpSet_lit
  have hop : evalCompareOpH w.heap (F + 5) .eq (.int (j - i)) (.int (-20)) = .ok false := by
    simp [evalCompareOpH, RVal.refFree, valEq, beqInt, hne]
  rw [hlit, execStmt_if_false (compare_one (F := F + 4)
    (binOp_two (name_evals hej) (name_evals hei) rfl)
    (binOp_two const_evals (globalName_evals hnn nGm) rfl) hop) rfl]
  rfl

/-- **GATE 11e — the DOUBLE PUSH, and it FIRES.** The one arm of the four inside
statements 10 and 11 that a plain move can take. It writes `ep` and never the
board, which is exactly why `PlainBoard` has three conjuncts and not four. -/
theorem move_ep_sets (w : World) (e : REnv) (i j : Int) (F : Nat)
    (hei : Env.lookup e "i" = some (.int i))
    (hej : Env.lookup e "j" = some (.int j))
    (hnn : Env.lookup e "N" = Option.none)
    (hpush : j - i = -20) :
    execStmt sunfish (F + 8) ⟨w, e⟩ mvEpSet
      = .ok ⟨w, Env.set e "ep" (.int (i + -10))⟩ .next := by
  obtain ⟨a, b, c, d, e', f, g, h, i', k, l, m, n, hlit⟩ := mvEpSet_lit
  have hop : evalCompareOpH w.heap (F + 5) .eq (.int (j - i)) (.int (-20)) = .ok true := by
    simp [evalCompareOpH, RVal.refFree, valEq, hpush]
  rw [hlit, execStmt_if_true (compare_one (F := F + 4)
    (binOp_two (name_evals hej) (name_evals hei) rfl)
    (binOp_two const_evals (globalName_evals hnn nGm) rfl) hop) rfl]
  exact execStmts_singleton (execStmt_assign_name
    (binOp_two (name_evals hei) (globalName_evals hnn nGm) rfl))

/-- **GATE 11f — the destination is not the en-passant square**, so that `put`
never runs. `PlainBoard`'s second conjunct, second half. -/
theorem move_epcap_skips (w : World) (e : REnv) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp j : Int) (F : Nat)
    (hself : Env.lookup e "self" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hej : Env.lookup e "j" = some (.int j))
    (hne : j ≠ ep) :
    execStmt sunfish (F + 6) ⟨w, e⟩ mvEpCap = .ok ⟨w, e⟩ .next := by
  obtain ⟨bd, a, b', c, d, e'', hlit⟩ := mvEpCap_lit
  have h1 : evalExpr sunfish (F + 4) (⟨w, e⟩ : FrameState) (.name "j" a)
      = .ok ⟨w, e⟩ (.int j) := name_evals hej
  have h2 : evalExpr sunfish (F + 3) (⟨w, e⟩ : FrameState)
      (.attribute (.name "self" b') "ep" c) = .ok ⟨w, e⟩ (.int ep) := by
    py_simp [-globalsFold, -globalsStep, hself, posOf, posCAux, posCls_methods]
  have hop : evalCompareOpH w.heap (F + 3) .eq (.int j) (.int ep) = .ok false := by
    simp [evalCompareOpH, RVal.refFree, valEq, hne]
  rw [hlit, execStmt_if_false (compare_one (F := F + 2) h1 h2 hop) rfl]
  rfl

/-! ## §6 STATEMENT 5 — where `Position.value`'s whole gate is spent

`score = self.score + self.value(move)` is the one statement that CALLS another
gated method. The call arrives as a hypothesis — `value_bound.lean`'s
`value_runs_quiet` (§L28) is what a caller supplies — so this gate says nothing
about `pst` and everything about the addition, which is `order_genexp.lean`'s
`value_call_evals` template on the receiver `self` rather than `pos`. -/

theorem mvScore_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8, mvScore =
    .assign #[.name "score" p0]
      (.binOp (.attribute (.name "self" p1) "score" p2) .add
        (.call (.attribute (.name "self" p3) "value" p4) #[.name "move" p5] #[] Option.none p6)
        p7) p8 :=
  ⟨_, _, _, _, _, _, _, _, _, rfl⟩

/-- **GATE — statement 5, `score = self.score + self.value(move)`.** -/
theorem move_scores (w : World) (e : REnv) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (mv : RVal) (z : Int) (F : Nat)
    (hself : Env.lookup e "self" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hm : Env.lookup e "move" = some mv)
    (hcall : callIn sunfish (F + 7) w "Position.value"
      #[posOf b sc wc0 wc1 bc0 bc1 ep kp, mv] = .ok w (.int z)) :
    execStmt sunfish (F + 10) ⟨w, e⟩ mvScore
      = .ok ⟨w, Env.set e "score" (.int (sc + z))⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, hlit⟩ := mvScore_lit
  rw [hlit]
  have ecall : evalExpr sunfish (F + 8) (⟨w, e⟩ : FrameState)
      (.call (.attribute (.name "self" p3) "value" p4) #[.name "move" p5] #[] Option.none p6)
      = .ok ⟨w, e⟩ (.int z) := by
    py_simp [-globalsFold, -globalsStep, hself, hm, posOf, posCAux, posCls_methods,
      posCls_ntBase_isSome]
    simpa only [posOf] using hcall
  have escore : evalExpr sunfish (F + 8) (⟨w, e⟩ : FrameState)
      (.attribute (.name "self" p1) "score" p2) = .ok ⟨w, e⟩ (.int sc) := by
    py_simp [-globalsFold, -globalsStep, hself, posOf, posCAux, posCls_methods]
  exact execStmt_assign_name (binOp_two escore ecall rfl)

/-! ## §7 STATEMENT 12 — the `return`, through a CONSTRUCTOR and a METHOD

`return Position(board, score, wc, bc, ep, kp).rotate()` is two calls in one
expression: a namedtuple-subclass INSTANTIATION (which allocates nothing — the
value is an `RVal.ntuple`, which is why §L44's exit law measured ONE heap slot
for the whole method) and then a method call on that value.

`Position`'s class shape is pinned before either: not a function name, not a
namedtuple assignment, not an exception, `ok`, and its `ntBase` carrying the six
fields in order. Each is a `rfl`, and each is a branch the interpreter takes
before it reaches the constructor — §L45's law again (*a conditional is a premise
until a `rfl` retires it*), five times over. -/

theorem mvRet_lit : ∃ q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10, mvRet =
    .ret (some (.call
      (.attribute
        (.call (.name "Position" q0) #[.name "board" q1, .name "score" q2, .name "wc" q3,
                                       .name "bc" q4, .name "ep" q5, .name "kp" q6]
          #[] Option.none q7)
        "rotate" q8)
      #[] #[] Option.none q9)) q10 :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem posG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "Position"
    = Option.none := rfl
theorem posFind : findFunction sunfish "Position" = Option.none := rfl
theorem posNotFun : ¬ ∃ x, x ∈ sunfish.functions ∧ x.name = "Position" := by
  simpa [findFunction] using posFind
theorem posInitF : findFunction sunfish "Position.__init__" = Option.none := rfl
theorem posInitNotFun : ¬ ∃ x, x ∈ sunfish.functions ∧ x.name = "Position.__init__" := by
  simpa [findFunction] using posInitF
theorem posNT : findNamedTupleAux sunfish.namedtuples.toList "Position" = Option.none := rfl
theorem posCls_isExc : posCls.2.isExc = false := rfl
theorem posCls_ok : posCls.2.ok = true := rfl
/-- The six fields, IN ORDER — the pin `posOf` is the mirror of. -/
theorem posCls_ntBase_pin : ∃ sp, posCls.2.ntBase =
    some ⟨"Position", "Position", #["board", "score", "wc", "bc", "ep", "kp"], sp⟩ := ⟨_, rfl⟩

set_option maxHeartbeats 1600000 in
/-- **`Position(board, score, wc, bc, ep, kp)` IS `posOf`.** No allocation: a
namedtuple-subclass instantiation is a VALUE. -/
theorem move_builds_position (w : World) (e : REnv) (bd : String) (scv : Int)
    (wc0 wc1 bc0 bc1 : Bool) (epv kpv : Int) (F : Nat) (q0 q1 q2 q3 q4 q5 q6 q7 : Span)
    (hb : Env.lookup e "board" = some (.str bd))
    (hs : Env.lookup e "score" = some (.int scv))
    (hwc : Env.lookup e "wc" = some (.tuple #[.bool wc0, .bool wc1]))
    (hbc : Env.lookup e "bc" = some (.tuple #[.bool bc0, .bool bc1]))
    (hep : Env.lookup e "ep" = some (.int epv))
    (hkp : Env.lookup e "kp" = some (.int kpv))
    (hnP : Env.lookup e "Position" = Option.none) :
    evalExpr sunfish (F + 10) ⟨w, e⟩
        (.call (.name "Position" q0) #[.name "board" q1, .name "score" q2, .name "wc" q3,
                                       .name "bc" q4, .name "ep" q5, .name "kp" q6]
          #[] Option.none q7)
      = .ok ⟨w, e⟩ (posOf bd scv wc0 wc1 bc0 bc1 epv kpv) := by
  obtain ⟨spnt, hnt⟩ := posCls_ntBase_pin
  py_simp [-globalsFold, -globalsStep, hb, hs, hwc, hbc, hep, hkp, hnP, posG, posFind,
    posNotFun, posInitNotFun, posNT, posCls_isExc, posCls_ok, posCAux, posCls_methods,
    posCls_ntBase_isSome, hnt, posOf]

/-- **A METHOD CALL ON A NAMEDTUPLE VALUE, at the chain.** The plan is decided
BEFORE the arguments (CPython's order), the clock guard is retired by the
attribute name, and the callee's own run arrives as a hypothesis — so `callIn`
never unfolds in a caller. `evalExpr`'s attribute-call arm, once. -/
theorem ntuple_method_call {m : Module} {F : Nat} {st st₁ : FrameState}
    {recv : Expr} {attr tn qname : String} {fs : Array String} {xs : Array RVal}
    {sp asp : Span} {w' : World} {v : RVal}
    (hr : evalExpr m (F + 1) st recv = .ok st₁ (.ntuple tn fs xs))
    (hattr : (attr == "time") = false)
    (hplan : ntupleCallPlan m tn fs attr = .instMethod qname)
    (hcall : callIn m (F + 1) st₁.world qname #[.ntuple tn fs xs] = .ok w' v) :
    evalExpr m (F + 2) st (.call (.attribute recv attr asp) #[] #[] Option.none sp)
      = .ok ⟨w', st₁.locals⟩ v := by
  rw [evalExpr, hr]
  simp only [Run.bind, hplan, isClockCall, hattr, Bool.false_and, Bool.false_eq_true,
    if_false, evalExprs, Run.withLocals, hcall]
  rfl

/-- `.rotate()` on a `Position` VALUE dispatches to `Position.rotate` — the
subclass-method arm, decided from `posCls.2.methods`. -/
theorem rotatePlan : ntupleCallPlan sunfish "Position"
    #["board", "score", "wc", "bc", "ep", "kp"] "rotate" = .instMethod "Position.rotate" := rfl

/-- **GATE — statement 12, the `return`.** The rotate call arrives as a
hypothesis, exactly as statement 5 takes `Position.value`'s. -/
theorem move_returns (w : World) (e : REnv) (bd : String) (scv : Int)
    (wc0 wc1 bc0 bc1 : Bool) (epv kpv : Int) (r : RVal) (w' : World) (F : Nat)
    (hb : Env.lookup e "board" = some (.str bd))
    (hs : Env.lookup e "score" = some (.int scv))
    (hwc : Env.lookup e "wc" = some (.tuple #[.bool wc0, .bool wc1]))
    (hbc : Env.lookup e "bc" = some (.tuple #[.bool bc0, .bool bc1]))
    (hep : Env.lookup e "ep" = some (.int epv))
    (hkp : Env.lookup e "kp" = some (.int kpv))
    (hnP : Env.lookup e "Position" = Option.none)
    (hrot : callIn sunfish (F + 10) w "Position.rotate"
      #[posOf bd scv wc0 wc1 bc0 bc1 epv kpv] = .ok w' r) :
    execStmt sunfish (F + 12) ⟨w, e⟩ mvRet = .ok ⟨w', e⟩ (.ret r) := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, hlit⟩ := mvRet_lit
  rw [hlit]
  exact execStmt_ret (ntuple_method_call (F := F + 9)
    (move_builds_position w e bd scv wc0 wc1 bc0 bc1 epv kpv F q0 q1 q2 q3 q4 q5 q6 q7
      hb hs hwc hbc hep hkp hnP) rfl rotatePlan hrot)

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
#print axioms mvUnpack_lit
#print axioms mvPQ_lit
#print axioms mvBoard_lit
#print axioms mvFields_lit
#print axioms move_unpacks
#print axioms move_reads_pq
#print axioms move_copies_board
#print axioms move_resets_fields
#print axioms tuple_evals
#print axioms globalName_evals
#print axioms boolOp_and2_bool
#print axioms nG
#print axioms mvWc_lit
#print axioms mvBc_lit
#print axioms move_wc
#print axioms move_bc
#print axioms mvKingB_split
#print axioms mvKing_lit
#print axioms mvKingWc_lit
#print axioms mvKingCastle_lit
#print axioms move_king_skips
#print axioms move_king_enters
#print axioms move_king_clears_wc
#print axioms move_castle_skips
#print axioms mvPawnB_split
#print axioms mvPawn_lit
#print axioms mvProm_lit
#print axioms mvEpSet_lit
#print axioms mvEpCap_lit
#print axioms move_pawn_skips
#print axioms move_pawn_enters
#print axioms move_prom_skips
#print axioms move_ep_set_skips
#print axioms move_ep_sets
#print axioms move_epcap_skips
#print axioms mvScore_lit
#print axioms move_scores
#print axioms mvRet_lit
#print axioms posCls_ntBase_pin
#print axioms move_builds_position
#print axioms ntuple_method_call
#print axioms rotatePlan
#print axioms move_returns

/-! ## What this file does NOT prove — and the bill for it

**ALL THIRTEEN STATEMENTS ARE GATED** — 0 through 12, statements 10 and 11
including every arm of their inner `if`s. What is owed before F1b closes:

* **the COMPOSITION** — the thirteen gates chained from the entry frame to the
  `return`, on `value_body_quiet`'s template, plus the `callIn` boundary;
* **`Position.rotate` at a SYMBOLIC board** — statement 12's `hrot` premise.
  `proof.lean` gates it at a CONCRETE board (`rotate_home_callsIn`); the
  composition needs it over a free board with the two `ifExp`s on `self.ep` and
  `self.kp` decided, and that is where §L41's `rotStr_residue` is spent.

The honest reading of the campaign ledger: **F1 is not complete.** F1a is
(§L37), F1b's string and value residues are (§L41, §L44), and F1b's interpreter
gate has all thirteen statements but not yet the chain that joins them. -/

end Examples.python.sunfish.move_gate
