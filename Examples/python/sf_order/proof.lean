/-
**`bound_probe`'s three constructs, on the shipped program** — the gates for
LeanModels/Python/GenBound.lean (§L8).

`Examples/python/sunfish/genmoves_drain.lean` closed the whole-drain bridge and
named, verbatim, the three things `sf_order`'s `bound_probe` still needed: *a
`sorted`-over-a-generator EXPRESSION rule, generator-internal `break` at the
loop-frame level, and `callClosure`'s generator arm.* GenBound.lean is those
three; this file is each one exercised on the ingested `sf_order`, whose
`Position.gen_moves`/`Position.value` are the shipped sunfish methods verbatim
and whose `bound_probe` carries the shipped ordering line (sunfish.py 412) and
the shipped `def moves():` shape.

Nothing here is retyped: every piece of program is PROJECTED out of `sf_order`
and pinned by `rfl`, so a changed program stops these theorems loudly rather
than letting them describe something else.

The three gates:

* **`order_line_sorts`** (§1) — the shipped ordering line
  `sorted(((pos.value(m), m) for m in pos.gen_moves()), reverse=True)`
  evaluates to a FRESH heap list holding `sortByLt true` of the lowered
  genexp's drain. Everything between the source text and that value is
  discharged: the generator METHOD call `pos.gen_moves()` (which allocates),
  the effectful argument list, the genexp call, the reverse flag's truthiness
  and the allocation of the result. The single hypothesis left is the genexp
  OBJECT's drain — `IterDrains`, §L6's judgment, which is "the ordering line
  itself, which is L4/L5" in §L3's own enumeration of this blocker.
* **`moves_loop_cuts`** (§2) — the shipped `for val, move in <ordered list>:
  if val < val_lower: break; yield (val, move.i, move.j)` emits exactly the
  triples of the rows above the threshold and stops AT the first row below it,
  with the loop frame consumed. Board-free, threshold-free, row-count-free:
  the kept rows, the cutting row and the abandoned tail are all arbitrary.
* **`moves_creates`** (§3) — the shipped `def moves():` allocates the closure
  with `depth`/`pos`/`val_lower` snapshotted, and `moves()` allocates the
  generator whose stored locals are exactly that snapshot and whose stored
  continuation is exactly `moves`' body.

Non-vacuity is pinned at the bottom by `#guard`s that RUN `bound_probe`: both
arms of §2's cutoff are reachable on the opening board (the cutting window
stops after one consumed yield, the open window drains all twenty), and the
ordering line's list is non-empty there.
-/
import Examples.python.sf_order.spec

namespace Examples.python.sf_order.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 100000

/-! ## The program, projected

`nth`/`nowhere` are the projection kit `Examples/python/sunfish` uses; every
definition below reads out of `sf_order` and every `_lit` theorem is an `rfl`
on that projection. -/

/-- The span a projection falls back to. -/
def nowhere : Span := ⟨0, 0, 0, 0⟩

/-- Positional projection into a statement list. -/
def nth (n : Nat) (ss : List Stmt) : Stmt :=
  match n, ss with
  | 0, s :: _ => s
  | n + 1, _ :: r => nth n r
  | _, _ => .pass nowhere

/-- `bound_probe`'s body — the H7 capstone's eight statements. -/
def bpB : List Stmt :=
  match findFunction sf_order "bound_probe" with
  | some f => f.body.toList
  | none => []

/-- `def moves(): …` — the nested generator, statement 4. -/
def bpDef : Stmt := nth 3 bpB

/-- `moves`' body: the `depth == 0` gate, then the ordering loop. -/
def mvB : List Stmt :=
  match bpDef with | .defStmt _ _ _ _ _ _ b _ _ => b.toList | _ => []

/-- The ordering `for` — statement 2 of `moves`, the whole construct. -/
def mvFor : Stmt := nth 1 mvB
/-- Its target, `(val, move)`. -/
def mvTarget : Expr :=
  match mvFor with | .forStmt t _ _ _ _ => t | _ => .constant .none nowhere
/-- **The shipped ordering line** (sunfish.py 412), as an AST. -/
def ordLine : Expr :=
  match mvFor with | .forStmt _ it _ _ _ => it | _ => .constant .none nowhere
/-- Its body: the cutoff guard, then the yield. -/
def mvBody : List Stmt :=
  match mvFor with | .forStmt _ _ b _ _ => b.toList | _ => []
/-- `if val < val_lower: break` — the beta cutoff. -/
def mvBreak : Stmt := nth 0 mvBody
/-- `yield (val, move.i, move.j)`. -/
def mvYield : Stmt := nth 1 mvBody

/-- The lowered generator EXPRESSION, `<genexpr@2>(pos.gen_moves(), pos)`. -/
def gxCall : Expr :=
  match ordLine with | .call _ args _ _ _ => args[0]! | _ => .constant .none nowhere
/-- The `reverse=` keyword's expression. -/
def revE : Expr :=
  match ordLine with | .call _ _ kws _ _ => kws[0]!.2 | _ => .constant .none nowhere
/-- `pos.gen_moves()` — the genexp's implicit first argument (CPython's
`.0`), and the one argument in the tier that ALLOCATES. -/
def gmCall : Expr :=
  match gxCall with | .call _ args _ _ _ => args[0]! | _ => .constant .none nowhere
/-- `pos` — the genexp's one capture. -/
def posE : Expr :=
  match gxCall with | .call _ args _ _ _ => args[1]! | _ => .constant .none nowhere

/-- `bound_probe`'s own loop, `for val, i, j in moves():`. -/
def bpFor : Stmt := nth 6 bpB
/-- `moves()` — the closure call. -/
def movesCall : Expr :=
  match bpFor with | .forStmt _ it _ _ _ => it | _ => .constant .none nowhere

theorem bpB_len : bpB.length = 8 := rfl

theorem bpDef_lit : ∃ sp, bpDef =
    .defStmt "moves" #[] true true false true mvB.toArray
      #["depth", "pos", "val_lower"] sp := ⟨_, rfl⟩

theorem mvB_split : mvB = [nth 0 mvB, mvFor] := rfl

theorem mvFor_lit : ∃ sp, mvFor = .forStmt mvTarget ordLine mvBody.toArray #[] sp :=
  ⟨_, rfl⟩

theorem mvTarget_lit : ∃ s₁ s₂ s₃,
    mvTarget = .tuple #[.name "val" s₁, .name "move" s₂] s₃ := ⟨_, _, _, rfl⟩

theorem ordLine_lit : ∃ s₁ s₂, ordLine =
    .call (.name "sorted" s₁) #[gxCall] #[("reverse", revE)] Option.none s₂ :=
  ⟨_, _, rfl⟩

theorem revE_lit : ∃ s, revE = .constant (.bool true) s := ⟨_, rfl⟩

theorem gxCall_lit : ∃ s₁ s₂, gxCall =
    .call (.name "<genexpr@2>" s₁) #[gmCall, posE] #[] Option.none s₂ := ⟨_, _, rfl⟩

theorem gmCall_lit : ∃ s₁ s₂ s₃, gmCall =
    .call (.attribute (.name "pos" s₁) "gen_moves" s₂) #[] #[] Option.none s₃ :=
  ⟨_, _, _, rfl⟩

theorem posE_lit : ∃ s, posE = .name "pos" s := ⟨_, rfl⟩

theorem movesCall_lit : ∃ s₁ s₂, movesCall =
    .call (.name "moves" s₁) #[] #[] Option.none s₂ := ⟨_, _, rfl⟩

theorem mvBody_split : mvBody = [mvBreak, mvYield] := rfl

theorem mvBreak_lit : ∃ s₁ s₂ s₃ s₄ s₅, mvBreak =
    .ifStmt (.compare (.name "val" s₁) #[.lt] #[.name "val_lower" s₂] s₃)
      #[.brk s₄] #[] s₅ := ⟨_, _, _, _, _, rfl⟩

theorem mvYield_lit : ∃ s₁ s₂ s₃ s₄ s₅ s₆ s₇, mvYield =
    .yieldStmt (.tuple #[.name "val" s₁, .attribute (.name "move" s₂) "i" s₃,
      .attribute (.name "move" s₄) "j" s₅] s₆) s₇ := ⟨_, _, _, _, _, _, _, rfl⟩

theorem mvBreak_plan : genPlan mvBreak = .delegate := rfl
theorem mvFor_plan : genPlan mvFor = .forHere mvTarget ordLine mvBody := rfl

/-! ## §1 The shipped ordering line

`sorted(((pos.value(m), m) for m in pos.gen_moves()), reverse=True)`. Read
outside in it is: a keyword `sorted` whose single argument is a call to the
LOWERED genexp function, whose own first argument is a generator METHOD call
on the receiver. Three allocations, two of them inside the argument list. -/

/-- The `Position` value, all six fields free — `genmoves_theorem.posOf`'s
shape, restated here because this file's module is `sf_order`. -/
def posNt (b : String) (score : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str b, .int score, .tuple #[.bool wc0, .bool wc1],
      .tuple #[.bool bc0, .bool bc1], .int ep, .int kp]

/-- The shipped `Position.gen_moves`, projected. -/
def gmF : FunctionDefn :=
  match findFunction sf_order "Position.gen_moves" with
  | some f => f
  | none => ⟨"", #[], false, false, false, false, #[], nowhere⟩

/-- The LOWERED generator expression, projected. -/
def gxF : FunctionDefn :=
  match findFunction sf_order "<genexpr@2>" with
  | some f => f
  | none => ⟨"", #[], false, false, false, false, #[], nowhere⟩

/-- The five facts `callIn`'s creation arm tests of `gen_moves`, plus the
call environment — every one an `rfl` on the projection. -/
theorem gm_lit : findFunction sf_order "Position.gen_moves" = some gmF ∧
    gmF.argsOk = true ∧ gmF.localsOk = true ∧ arityOk gmF.params 1 = true ∧
    gmF.isGenerator = true ∧ (∀ p : RVal, mkCallEnv gmF.params #[p] = [("self", p)]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- The same for the lowered genexp: two parameters (CPython's implicit `.0`
plus the one admitted capture), and a generator. -/
theorem gx_lit : findFunction sf_order "<genexpr@2>" = some gxF ∧
    gxF.argsOk = true ∧ gxF.localsOk = true ∧ arityOk gxF.params 2 = true ∧
    gxF.isGenerator = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The object `pos.gen_moves()` allocates. -/
def gmObj (pv : RVal) : Obj := genObj "Position.gen_moves" gmF #[pv]
/-- The object `<genexpr@2>(<that one>, pos)` allocates. -/
def gxObj (a : Addr) (pv : RVal) : Obj := genObj "<genexpr@2>" gxF #[.ref a, pv]
/-- The world after the receiver's method call. -/
def gmW (w : World) (pv : RVal) : World := { w with heap := w.heap.push (gmObj pv) }
/-- The world after the genexp call — two objects, in evaluation order. -/
def gxW (w : World) (pv : RVal) : World :=
  { w with heap := (w.heap.push (gmObj pv)).push (gxObj w.heap.size pv) }

/-- `sorted` is the builtin here, not a shadow — `evalExpr`'s own resolution
order, hypothesis by hypothesis. -/
theorem sorted_free : lookupG (moduleGlobals sf_order).1 "sorted" = Option.none ∧
    findFunction sf_order "sorted" = Option.none ∧
    findClass sf_order "sorted" = Option.none ∧
    findNamedTuple sf_order "sorted" = Option.none := ⟨rfl, rfl, rfl, rfl⟩

theorem gx_free : lookupG (moduleGlobals sf_order).1 "<genexpr@2>" = Option.none ∧
    findClass sf_order "<genexpr@2>" = Option.none ∧
    findNamedTuple sf_order "<genexpr@2>" = Option.none := ⟨rfl, rfl, rfl⟩

/-- The receiver's plan: `.gen_moves` on a `Position` value is the SUBCLASS
method, resolved before any argument runs. -/
theorem gm_plan : ntupleCallPlan sf_order "Position"
    #["board", "score", "wc", "bc", "ep", "kp"] "gen_moves"
    = .instMethod "Position.gen_moves" := rfl

/-- **GATE 1 — the shipped ordering line evaluates to the sorted list.**

In a frame that binds `pos` to a `Position` value and shadows neither `sorted`
nor the lowered genexp, the shipped line evaluates to a `.ref` at the
post-drain heap's END, and the object there is a fresh `.list` holding
`sortByLt true` of exactly what the genexp object drained to.

The world moves three times inside one expression — `pos.gen_moves()`
allocates, `<genexpr@2>(…)` allocates, and `sorted` allocates its answer —
which is why the statement is `EvalsIn` and why the argument list had to
become effectful (`EvalsInList`). The one hypothesis that is not bookkeeping
is `hdrain`: what the lowered genexp OBJECT yields, which is the ordering
line's L4/L5 half and is exactly `IterDrains`, §L6's judgment. -/
theorem order_line_sorts (w : World) (env : REnv)
    (fs : Array String) (xs : Array RVal)
    (vs sortedVs : List RVal) (w' : World)
    (hpos : Env.lookup env "pos" = some (.ntuple "Position" fs xs))
    (hplan : ntupleCallPlan sf_order "Position" fs "gen_moves"
      = .instMethod "Position.gen_moves")
    (hsorted : Env.lookup env "sorted" = Option.none)
    (hgxl : Env.lookup env "<genexpr@2>" = Option.none)
    (hdrain : IterDrains sf_order
      (gxW w (.ntuple "Position" fs xs)) (w.heap.size + 1) vs w')
    (hsort : sortByLt true vs = .ok sortedVs) :
    EvalsIn sf_order ⟨w, env⟩ ordLine (.ref w'.heap.size)
      ⟨{ w' with heap := w'.heap.push (.list sortedVs.toArray) }, env⟩ := by
  obtain ⟨s₁, s₂, hord⟩ := ordLine_lit
  obtain ⟨t₁, t₂, hgx⟩ := gxCall_lit
  obtain ⟨u₁, u₂, u₃, hgm⟩ := gmCall_lit
  obtain ⟨v₁, hposE⟩ := posE_lit
  obtain ⟨r₁, hrev⟩ := revE_lit
  -- the receiver's method call: allocates, runs nothing
  have hrecv : EvalsIn sf_order ⟨w, env⟩ (.name "pos" u₁)
      (.ntuple "Position" fs xs) ⟨w, env⟩ :=
    EvalsIn.of_evalsTo (EvalsTo.of_eval (fuel := 4) (by py_simp [hpos]))
  have hgmEv : EvalsIn sf_order ⟨w, env⟩ gmCall (.ref w.heap.size)
      ⟨gmW w (.ntuple "Position" fs xs), env⟩ := by
    rw [hgm]
    have := EvalsIn.ntupleGenMethod (qname := "Position.gen_moves") (f := gmF)
      (vs := []) (sp := u₂) (sp' := u₃) rfl hrecv hplan EvalsInList.nil
      gm_lit.1 gm_lit.2.1 gm_lit.2.2.1 (by simpa using gm_lit.2.2.2.1)
      gm_lit.2.2.2.2.1
    simpa [gmW, gmObj] using this
  -- the genexp call: its FIRST argument is the object just allocated
  have hposEv : EvalsIn sf_order ⟨gmW w (.ntuple "Position" fs xs), env⟩ posE
      (.ntuple "Position" fs xs) ⟨gmW w (.ntuple "Position" fs xs), env⟩ := by
    rw [hposE]
    exact EvalsIn.of_evalsTo (EvalsTo.of_eval (fuel := 4) (by py_simp [hpos]))
  have hargs : EvalsInList sf_order ⟨w, env⟩ [gmCall, posE]
      [.ref w.heap.size, .ntuple "Position" fs xs]
      ⟨gmW w (.ntuple "Position" fs xs), env⟩ :=
    EvalsInList.cons hgmEv (EvalsInList.one hposEv)
  have hgxEv : EvalsIn sf_order ⟨w, env⟩ gxCall (.ref (w.heap.size + 1))
      ⟨gxW w (.ntuple "Position" fs xs), env⟩ := by
    rw [hgx]
    have := EvalsIn.genCallIn (m := sf_order) (st := ⟨w, env⟩)
      (st₁ := ⟨gmW w (.ntuple "Position" fs xs), env⟩)
      (fname := "<genexpr@2>") (f := gxF) (argEs := #[gmCall, posE])
      (vs := [.ref w.heap.size, .ntuple "Position" fs xs]) (sp := t₁) (sp' := t₂)
      hgxl gx_free.1 gx_free.2.1 gx_free.2.2 gx_lit.1 gx_lit.2.1 gx_lit.2.2.1
      (by simpa using gx_lit.2.2.2.1) gx_lit.2.2.2.2 (by simpa using hargs)
    simpa [gmW, gxW, gxObj] using this
  -- the flag, then the drain, then the allocation of the answer
  have hrevEv : EvalsIn sf_order ⟨gxW w (.ntuple "Position" fs xs), env⟩ revE
      (.bool true) ⟨gxW w (.ntuple "Position" fs xs), env⟩ := by
    rw [hrev]; exact EvalsIn.of_evalsTo (EvalsTo.of_eval (fuel := 1) rfl)
  have hobj : Heap.get? (gxW w (.ntuple "Position" fs xs)).heap (w.heap.size + 1)
      = some (gxObj w.heap.size (.ntuple "Position" fs xs)) := by
    have h := Heap.get?_push_size (w.heap.push (gmObj (.ntuple "Position" fs xs)))
      (gxObj w.heap.size (.ntuple "Position" fs xs))
    simpa [gxW] using h
  rw [hord]
  exact EvalsIn.sortedDrainRev hsorted sorted_free.1 sorted_free.2.1
    sorted_free.2.2.1 sorted_free.2.2.2 hgxEv hrevEv rfl
    (by simpa [gxObj, genObj] using hobj) hdrain hsort

/-- The same at the SHIPPED `Position` shape: the plan hypothesis is `rfl`. -/
theorem order_line_sorts_pos (w : World) (env : REnv)
    (b : String) (score ep kp : Int) (wc0 wc1 bc0 bc1 : Bool)
    (vs sortedVs : List RVal) (w' : World)
    (hpos : Env.lookup env "pos" = some (posNt b score wc0 wc1 bc0 bc1 ep kp))
    (hsorted : Env.lookup env "sorted" = Option.none)
    (hgxl : Env.lookup env "<genexpr@2>" = Option.none)
    (hdrain : IterDrains sf_order
      (gxW w (posNt b score wc0 wc1 bc0 bc1 ep kp)) (w.heap.size + 1) vs w')
    (hsort : sortByLt true vs = .ok sortedVs) :
    EvalsIn sf_order ⟨w, env⟩ ordLine (.ref w'.heap.size)
      ⟨{ w' with heap := w'.heap.push (.list sortedVs.toArray) }, env⟩ :=
  order_line_sorts w env _ _ vs sortedVs w' hpos gm_plan hsorted hgxl hdrain hsort

/-! ## §2 The loop, and the beta cutoff

`sorted` ALLOCATES, so `execGen` pushes a **`forList`** frame at the ordering
line's answer; §L4's `GenEmits.blockBreak` unwinds the `break` and
GenBound's `forListRound`/`forListBreak` are the loop that receives it. The
rows below are the shape the ordering line produces — `(value, Move)` pairs —
with every field free. -/

/-- One row of the ordered move list. -/
structure Row where
  val : Int
  i : Int
  j : Int
  prom : String
deriving Inhabited

/-- The row's `Move`, as the shipped namedtuple. -/
def moveOf (r : Row) : RVal :=
  .ntuple "Move" #["i", "j", "prom"] #[.int r.i, .int r.j, .str r.prom]
/-- The row as the ordering line's `(value, Move)` pair. -/
def rowVal (r : Row) : RVal := .tuple #[.int r.val, moveOf r]
/-- What the loop YIELDS for a kept row: `(val, move.i, move.j)`. -/
def rowTriple (r : Row) : RVal := .tuple #[.int r.val, .int r.i, .int r.j]

/-- `moves`' frame at entry: nothing but the three captures. -/
def mvEnv (d : Int) (pv : RVal) (vl : Int) : REnv :=
  [("depth", .int d), ("pos", pv), ("val_lower", .int vl)]
/-- `moves`' frame with the loop target bound to a row. -/
def mvEnvAt (d : Int) (pv : RVal) (vl : Int) (r : Row) : REnv :=
  mvEnv d pv vl ++ [("val", .int r.val), ("move", moveOf r)]

/-- Binding `(val, move)` to a row, from the entry frame. -/
theorem assign_entry (h : Heap) (d : Int) (pv : RVal) (vl : Int) (r : Row) :
    assignToH h (mvEnv d pv vl) mvTarget (rowVal r) = .ok (mvEnvAt d pv vl r) := rfl

/-- Binding it again on the next round: `Env.set` replaces in place, so the
frame's shape is stable across rounds. -/
theorem assign_again (h : Heap) (d : Int) (pv : RVal) (vl : Int) (r₀ r : Row) :
    assignToH h (mvEnvAt d pv vl r₀) mvTarget (rowVal r) = .ok (mvEnvAt d pv vl r) := rfl

/-- The cutoff guard, symbolically: `val < val_lower` at an arbitrary row and
an arbitrary threshold. -/
theorem evals_gate (w : World) (d : Int) (pv : RVal) (vl : Int) (r : Row)
    (s₁ s₂ s₃ : Span) :
    EvalsTo sf_order ⟨w, mvEnvAt d pv vl r⟩
      (.compare (.name "val" s₁) #[.lt] #[.name "val_lower" s₂] s₃)
      (.bool (decide (r.val < vl))) := by
  refine EvalsTo.of_eval (fuel := 8) ?_
  py_simp [mvEnvAt, mvEnv]
  by_cases hlt : r.val < vl <;> simp [hlt]

/-- The yielded tuple, symbolically: two namedtuple FIELD reads off the bound
`move`, which is where `sf_order`'s own class table has to be consulted. -/
theorem evals_triple (w : World) (d : Int) (pv : RVal) (vl : Int) (r : Row)
    (s₁ s₂ s₃ s₄ s₅ s₆ : Span) :
    EvalsTo sf_order ⟨w, mvEnvAt d pv vl r⟩
      (.tuple #[.name "val" s₁, .attribute (.name "move" s₂) "i" s₃,
        .attribute (.name "move" s₄) "j" s₅] s₆) (rowTriple r) := by
  have hfc : findClassAux sf_order.classes.toList "Move" 0 = Option.none := by rfl
  refine EvalsTo.of_eval (fuel := 8) ?_
  py_simp [mvEnvAt, mvEnv, moveOf, rowTriple, hfc]

/-- The guard STATEMENT, at a row the threshold keeps: it falls through. -/
theorem mvBreak_next (w : World) (d : Int) (pv : RVal) (vl : Int) (r : Row)
    (hge : ¬ r.val < vl) :
    execStmt sf_order 12 ⟨w, mvEnvAt d pv vl r⟩ mvBreak
      = .ok ⟨w, mvEnvAt d pv vl r⟩ .next := by
  obtain ⟨s₁, s₂, s₃, s₄, s₅, hb⟩ := mvBreak_lit
  rw [hb]
  py_simp [mvEnvAt, mvEnv]
  simp [hge]

/-- The guard STATEMENT, at the cutting row: it BREAKS. -/
theorem mvBreak_brk (w : World) (d : Int) (pv : RVal) (vl : Int) (r : Row)
    (hlt : r.val < vl) :
    execStmt sf_order 12 ⟨w, mvEnvAt d pv vl r⟩ mvBreak
      = .ok ⟨w, mvEnvAt d pv vl r⟩ .brk := by
  obtain ⟨s₁, s₂, s₃, s₄, s₅, hb⟩ := mvBreak_lit
  rw [hb]
  py_simp [mvEnvAt, mvEnv]
  simp [hlt]

/-- **The body at a KEPT row**: the guard falls through and the `yield`
emits the row's triple. -/
theorem mv_body_keep (w : World) (d : Int) (pv : RVal) (vl : Int) (r : Row)
    (hge : ¬ r.val < vl) :
    GenEmits sf_order ⟨w, mvEnvAt d pv vl r⟩ [.block mvBody] [rowTriple r]
      ⟨w, mvEnvAt d pv vl r⟩ := by
  obtain ⟨y₁, y₂, y₃, y₄, y₅, y₆, y₇, hy⟩ := mvYield_lit
  have hyield : ∀ k : GenCont,
      GenSteps sf_order ⟨w, mvEnvAt d pv vl r⟩
        ([GenFrame.block [mvYield]] ++ k)
        (some (rowTriple r, [GenFrame.block []] ++ k)) ⟨w, mvEnvAt d pv vl r⟩ := by
    intro k
    have h := genSteps_yieldHere (m := sf_order) (st := ⟨w, mvEnvAt d pv vl r⟩)
      (s := mvYield) (ss := ([] : List Stmt)) (k := k) (v := rowTriple r)
      (by rw [hy]; rfl) (evals_triple w d pv vl r y₁ y₂ y₃ y₄ y₅ y₆)
    simpa using h
  have hsil : ∀ k : GenCont,
      GenSilent sf_order ⟨w, mvEnvAt d pv vl r⟩
        ([GenFrame.block mvBody] ++ k) ⟨w, mvEnvAt d pv vl r⟩
        ([GenFrame.block [mvYield]] ++ k) := by
    intro k
    have h := genSilent_delegate (m := sf_order) (s := mvBreak) (ss := [mvYield])
      (k := k) (st := ⟨w, mvEnvAt d pv vl r⟩) (st₁ := ⟨w, mvEnvAt d pv vl r⟩)
      mvBreak_plan ⟨12, fun F hF => execStmt_mono (mvBreak_next w d pv vl r hge)
        (by simp) F hF⟩
    simpa [mvBody_split] using h
  refine GenEmits.silent hsil (GenEmits.cons hyield ?_)
  exact GenEmits.silent (pre₁ := ([] : GenCont))
    (fun k => by simpa using genSilent_blockNil (m := sf_order) (k := k)) GenEmits.nil

/-- **The body at the CUTTING row**: the guard breaks, and the unwind takes
the enclosing loop frame with it — `GenEmits.blockBreak`, with the `forList`
frame in its polymorphic prefix. Nothing is emitted. -/
theorem mv_body_cut (w : World) (d : Int) (pv : RVal) (vl : Int) (r : Row)
    (ad : Addr) (i : Nat) (hlt : r.val < vl) :
    GenEmits sf_order ⟨w, mvEnvAt d pv vl r⟩
      [.block mvBody, .forList mvTarget ad i mvBody] [] ⟨w, mvEnvAt d pv vl r⟩ := by
  have h := GenEmits.blockBreak (m := sf_order) (s := mvBreak) (ss := [mvYield])
    (pre := [GenFrame.forList mvTarget ad i mvBody]) (st := ⟨w, mvEnvAt d pv vl r⟩)
    (st₁ := ⟨w, mvEnvAt d pv vl r⟩) mvBreak_plan (fun _ => rfl)
    ⟨12, fun F hF => execStmt_mono (mvBreak_brk w d pv vl r hlt) (by simp) F hF⟩
  simpa [mvBody_split] using h

/-- The rounds, by induction on the kept rows. -/
private theorem loop_go (w : World) (ad : Addr) (d : Int) (pv : RVal) (vl : Int)
    (xs : Array RVal) (cut : Row)
    (hobj : Heap.get? w.heap ad = some (.list xs)) (hcut : cut.val < vl) :
    ∀ (kept : List Row) (i : Nat) (env₀ : REnv),
      (∀ r : Row, assignToH w.heap env₀ mvTarget (rowVal r) = .ok (mvEnvAt d pv vl r)) →
      (∀ k, k < kept.length → xs.getD (i + k) .none = rowVal (kept.getD k default)) →
      xs.getD (i + kept.length) .none = rowVal cut →
      i + kept.length < xs.size →
      (∀ r ∈ kept, ¬ r.val < vl) →
      GenEmits sf_order ⟨w, env₀⟩ [.forList mvTarget ad i mvBody]
        (kept.map rowTriple) ⟨w, mvEnvAt d pv vl cut⟩ := by
  intro kept
  induction kept with
  | nil =>
    intro i env₀ hasg _ hrow hsize _
    refine GenEmits.forListBreak (xs := xs) (st := ⟨w, env₀⟩) (ad := ad) (i := i)
      (env₁ := mvEnvAt d pv vl cut) hobj (by simpa using hsize) ?_ ?_
    · rw [show xs.getD i .none = rowVal cut from by simpa using hrow]
      exact hasg cut
    · simpa using mv_body_cut w d pv vl cut ad (i + 1) hcut
  | cons r rest ih =>
    intro i env₀ hasg hrows hrow hsize hkeep
    have hr0 : xs.getD i .none = rowVal r := by simpa using hrows 0 (by simp)
    have hlt : i < xs.size := by simp at hsize; omega
    have hkeepr : ¬ r.val < vl := hkeep r (by simp)
    rw [show List.map rowTriple (r :: rest)
        = [rowTriple r] ++ List.map rowTriple rest from rfl]
    refine GenEmits.forListRound (xs := xs) (st := ⟨w, env₀⟩) (ad := ad) (i := i)
      (env₁ := mvEnvAt d pv vl r) (st₂ := ⟨w, mvEnvAt d pv vl r⟩) hobj hlt ?_ ?_ ?_
    · rw [hr0]; exact hasg r
    · simpa using mv_body_keep w d pv vl r hkeepr
    · refine ih (i + 1) (mvEnvAt d pv vl r)
        (fun r' => assign_again w.heap d pv vl r r') (fun k hk => ?_) ?_ (by simp at hsize ⊢; omega)
        (fun r' hr' => hkeep r' (by simp [hr']))
      · have := hrows (k + 1) (by simp; omega)
        simpa [Nat.add_right_comm, Nat.add_assoc] using this
      · have := hrow
        simpa [Nat.add_right_comm, Nat.add_assoc] using this

/-- **GATE 2 — the shipped loop, with the beta cutoff.**

`for val, move in <the ordered list>: if val < val_lower: break; yield (val,
move.i, move.j)`, inside the `moves` generator, over an arbitrary heap list
whose first rows are `(value, Move)` pairs: the generator emits exactly the
triples of the rows AT OR ABOVE the threshold, and then STOPS — the loop frame
is consumed by the `break` that ends it, and the rows after the cutting one are
never read.

Rows free, threshold free, count free, and the tail beyond the cutting row is
not constrained at all: laziness is the content of the theorem, and an eager
design cannot state it. -/
theorem moves_loop_cuts (w : World) (ad : Addr) (d : Int) (pv : RVal) (vl : Int)
    (xs : Array RVal) (kept : List Row) (cut : Row)
    (hobj : Heap.get? w.heap ad = some (.list xs))
    (hrows : ∀ k, k < kept.length → xs.getD k .none = rowVal (kept.getD k default))
    (hcutrow : xs.getD kept.length .none = rowVal cut)
    (hsize : kept.length < xs.size)
    (hkeep : ∀ r ∈ kept, ¬ r.val < vl) (hcut : cut.val < vl) :
    GenEmits sf_order ⟨w, mvEnv d pv vl⟩ [.forList mvTarget ad 0 mvBody]
      (kept.map rowTriple) ⟨w, mvEnvAt d pv vl cut⟩ :=
  loop_go w ad d pv vl xs cut hobj hcut kept 0 (mvEnv d pv vl)
    (fun r => assign_entry w.heap d pv vl r) (by simpa using hrows)
    (by simpa using hcutrow) (by simpa using hsize) hkeep

/-! ## §3 The nested generator `def`, and calling it -/

/-- The snapshot `def moves():` takes: `depth`, `pos`, `val_lower`, in the
extractor's own capture order. -/
def movesCap (d : Int) (pv : RVal) (vl : Int) : REnv :=
  [("depth", .int d), ("pos", pv), ("val_lower", .int vl)]

/-- The closure object the `def` statement allocates. -/
def movesClosure (d : Int) (pv : RVal) (vl : Int) : Obj :=
  .closure "moves" #[] true true false true mvB.toArray (movesCap d pv vl)

/-- The generator object `moves()` allocates. -/
def movesGen (d : Int) (pv : RVal) (vl : Int) : Obj :=
  closureGenObj "moves" #[] mvB.toArray (movesCap d pv vl) #[]

/-- The captures snapshot, from the three frame reads. -/
theorem moves_snapshot (env : REnv) (d : Int) (pv : RVal) (vl : Int)
    (hd : Env.lookup env "depth" = some (.int d))
    (hp : Env.lookup env "pos" = some pv)
    (hv : Env.lookup env "val_lower" = some (.int vl)) :
    capturesSnapshot env ["depth", "pos", "val_lower"] = some (movesCap d pv vl) := by
  simp [capturesSnapshot, hd, hp, hv, movesCap]

theorem notHeapFree :
    (funsHeapFree sf_order.functions.toList && topLevelDefFree sf_order) = false := rfl

/-- **GATE 3a — the shipped `def moves():` allocates the closure**, with the
three captures snapshotted out of `bound_probe`'s frame and the name bound to
its address. -/
theorem moves_def_allocates (w : World) (env : REnv) (F : Nat)
    (d : Int) (pv : RVal) (vl : Int)
    (hd : Env.lookup env "depth" = some (.int d))
    (hp : Env.lookup env "pos" = some pv)
    (hv : Env.lookup env "val_lower" = some (.int vl)) :
    execStmt sf_order (F + 1) ⟨w, env⟩ bpDef
      = .ok ⟨{ w with heap := w.heap.push (movesClosure d pv vl) },
              Env.set env "moves" (.ref w.heap.size)⟩ .next := by
  obtain ⟨sp, hdef⟩ := bpDef_lit
  rw [hdef]
  exact execStmt_nestedDef (moves_snapshot env d pv vl hd hp hv)

/-- **GATE 3b — calling it allocates the generator.** `moves()` runs no code:
it appends a suspended frame whose stored continuation is exactly `moves`'
body and whose stored locals are exactly the snapshot — which is what makes a
resume-time capture read an ordinary frame lookup. -/
theorem moves_call_creates (w : World) (env : REnv) (ad : Addr)
    (d : Int) (pv : RVal) (vl : Int)
    (hloc : Env.lookup env "moves" = some (.ref ad))
    (hobj : Heap.get? w.heap ad = some (movesClosure d pv vl)) :
    EvalsIn sf_order ⟨w, env⟩ movesCall (.ref w.heap.size)
      ⟨{ w with heap := w.heap.push (movesGen d pv vl) }, env⟩ := by
  obtain ⟨s₁, s₂, hcall⟩ := movesCall_lit
  rw [hcall]
  exact EvalsIn.closureGenCall hloc notHeapFree hobj rfl EvalsToList.nil

/-- The object it left, spelled out: the captures ARE the generator's locals,
and `moves`' body IS its continuation. -/
theorem movesGen_eq (d : Int) (pv : RVal) (vl : Int) :
    movesGen d pv vl
      = .generator "<closure:moves>" (movesCap d pv vl) [.block mvB] .created := rfl

/-! ## Non-vacuity, and the axioms

The gates are stated over free boards, free rows and free thresholds, so the
question a reader should ask is whether their hypotheses are ever SATISFIED.
These `#guard`s answer it by RUNNING the shipped `bound_probe` on the opening
board — CPython's own answers, already pinned differentially in `spec.lean`. -/

private def openingB : String :=
  "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n"

/-! §1 is not vacuous: the ordering line's drain is a TWENTY-row list here, so
the `sortByLt` in `order_line_sorts` has something to order. -/

#guard (match callFunction sf_order "move_order" #[.str openingB, .int 0, .int 0] 60000 with
  | .ok (.list ms) => ms.size == 20
  | _ => false)

/-! §2's CUTTING arm is reachable: at `depth = 0` the threshold is
`QS - 0 * QS_A = 40`, only two of the twenty rows clear it, and `bound_probe`
consumes three yields (the `depth == 0` yield plus those two) before the list
runs out — the `break` fired at row three of twenty. -/

#guard callFunction sf_order "bound_probe"
    #[.str openingB, .int 1000, .int 0, .int 0, .int 0] 200000
  == .ok (.tuple #[.int 46, .int 3])

/-! §2's KEPT arm is reachable at full length: at `depth = 1` the threshold is
`40 - 140 = -100`, every row clears it, and all twenty are consumed — so
`kept` is genuinely allowed to be long and the cutting row genuinely
optional. -/

#guard callFunction sf_order "bound_probe"
    #[.str openingB, .int 1000, .int 1, .int 0, .int 0] 200000
  == .ok (.tuple #[.int 46, .int 20])

/-! §3 is not vacuous: `bound_probe` DECIDES, so the closure is allocated, the
call finds it, and the generator it answers is stepped — with the OUTER beta
cutoff abandoning it after one consumed yield. -/

#guard callFunction sf_order "bound_probe"
    #[.str openingB, .int 40, .int 1, .int 0, .int 0] 200000
  == .ok (.tuple #[.int 46, .int 1])

#print axioms order_line_sorts
#print axioms order_line_sorts_pos
#print axioms moves_loop_cuts
#print axioms moves_def_allocates
#print axioms moves_call_creates

/-! ## What is still between here and the `bound_probe` COLLAPSE

The three constructs §L3 enumerated are landed and gated, and the collapse is
NOT reached. What remains is measured rather than guessed, and it is two
things, neither of them one of the three:

1. **The ordering line's CONTENT** — `hdrain` in §1. `IterDrains sf_order
   <the genexp object> vs` says the lowered `<genexpr@2>` yields `vs`; proving
   it is `for m in .0: yield (pos.value(m), m)` over the drain of
   `pos.gen_moves()`, i.e. `Position.value` agreement composed with the
   `gen_moves` drain. `Examples/python/sunfish/genmoves_drain.lean` has exactly
   that theorem for the `sunfish` module (`gen_moves_drains_ref`), and
   `sf_order`'s `Position.gen_moves` is the same method body — but it is a
   DIFFERENT `Module` literal, so the sunfish lane's chain does not transfer
   without a module-transfer argument, and `Position.value` has no agreement
   theorem in either lane. §L3 called this "the ordering line itself, which is
   L4/L5"; that is still what it is.
2. **`bound_probe`'s OWN loop** — `for val, i, j in moves():` with the
   `best`/`searched` fold and the OUTER cutoff `if best >= gamma: break`. That
   is a statement-level `forGen` over the object §3 allocates
   (`PyStmtTriple.forGen`, VCGen §L3, plus `IterSteps` per round), and it is
   blocked on 1 rather than on any missing rule: the rounds it takes are the
   yields `moves` produces, which are what the ordering line decides.

So the honest ledger is: three constructs asked for, three landed, three
gated on the shipped program; the collapse waits on the agreement half of the
tier, not on the calculus. -/

end Examples.python.sf_order.proof
