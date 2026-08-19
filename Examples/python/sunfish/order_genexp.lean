/-
**THE ORDERING GENEXP'S ROUND** — inch R2a of the `RecursionStep` campaign
(docs/backlog.md §L25), and the file that says which `for` rule the ordering line
needs.

`moves()`' last statement is
`yield from sorted(((v, m) for m in pos.gen_moves() if (v := pos.value(m)) >= QS or depth), reverse=True)`,
and §L25 decomposed it into three: the genexp's drain (R2a), the keyword
`sorted` (R2b), and the `for` over the sorted list (R2c). This file is R2a.

**Its own file, deliberately.** `bound_depth.lean` elaborates in 3 m 25 s and this
one in 14 s, so an inch that will take several passes belongs where a pass costs
seconds — the throughput law, and the reason value_bound.lean is separate too.

**The census, first, and it CORRECTED the plan.** §L25 reserved attention for the
walrus: *"the WALRUS `v :=` binds in the genexp's own frame — census it before
writing the gate."* There is nothing to census. Ingestion lowered
`(v := pos.value(m)) >= QS` into an ordinary `assign` HOISTED above the `if`, so
`v` is a plain local, the statement's `genPlan` is `.delegate`, and the binding is
an ordinary statement gate. §0 below pins that by `rfl`.

**Measured before anything here was written** (§L24's exit law), on the opening
position, whose `gen_moves` yields twenty moves:

* the drain yields **2** pairs at `depth = 0` and **20** at `depth = 3` — the QS
  floor of sunfish.py:443, in numbers;
* it allocates **81 objects** (heap 68 → 149), which is 81 of the 84 §L25
  measured for the whole ordering line;
* **208 fuel** decides the call and both drains; **200** does not.

**What R1 supplies.** `gx_binds` takes `Position.value`'s answer as a `callIn`
hypothesis, and value_bound.lean's four `value_runs_*` theorems are what discharge
it. `value_call_evals` is the bridge, and it is three lines: past
`posCls.2.ntBase.isSome` the interpreter's residue is `callIn` under
`Run.withLocals`, so R1's conclusion plugs in with no transport.
-/
import Examples.python.sunfish.value_bound

namespace Examples.python.sunfish.order_genexp

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)
open Examples.python.sunfish.bound_depth (posCAux posCls_methods posCls_ntBase_isSome
  execStmt_if_true execStmt_if_false execStmt_assign_name compare_one)
open Examples.python.sunfish.value_bound

set_option maxRecDepth 100000

private def nowhere : Span := ⟨0, 0, 0, 0⟩
private def nth (n : Nat) (ss : List Stmt) : Stmt :=
  match ss.drop n with | s :: _ => s | [] => .pass nowhere

/-! ## §0 The genexp, projected -/

def gxF : FunctionDefn :=
  match findFunction sunfish "<genexpr@1>" with | some f => f | none => default

def gxB : List Stmt := gxF.body.toList
def gxFor : Stmt := nth 0 gxB
def gxBody : List Stmt := match gxFor with | .forStmt _ _ b _ _ => b.toList | _ => []
def gxBind : Stmt := nth 0 gxBody
def gxTest : Stmt := nth 1 gxBody
def gxYield : Stmt := match gxTest with | .ifStmt _ b _ _ => nth 0 b.toList | _ => .pass nowhere

theorem gxB_split : gxB = [gxFor] := rfl
theorem gxBody_split : gxBody = [gxBind, gxTest] := rfl

theorem gxF_lit : findFunction sunfish "<genexpr@1>" = some gxF ∧
    gxF.argsOk = true ∧ gxF.localsOk = true ∧ gxF.isGenerator = true ∧
    gxF.hasGlobal = false ∧ gxF.body.toList = gxB ∧
    arityOk gxF.params 3 = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! The three parameters the lowering gave it, read off the projection. -/
#guard (gxF.params.map (fun p => p.arg)) == #[".0", "depth", "pos"]

theorem gxFor_lit : ∃ a b c, gxFor =
    .forStmt (.name "m" a) (.name ".0" b) gxBody.toArray #[] c := ⟨_, _, _, rfl⟩

theorem gxBind_lit : ∃ a b c d e, gxBind =
    .assign #[.name "v" a]
      (.call (.attribute (.name "pos" b) "value" c) #[.name "m" d] #[] Option.none e)
      a := ⟨_, _, _, _, _, rfl⟩

theorem gxTest_lit : ∃ a b c d e f, gxTest =
    .ifStmt (.boolOp .or #[.compare (.name "v" a) #[.gtE] #[.name "QS" b] c,
        .name "depth" d] e)
      #[gxYield] #[] f := ⟨_, _, _, _, _, _, rfl⟩

theorem gxYield_lit : ∃ a b c d, gxYield =
    .yieldStmt (.tuple #[.name "v" a, .name "m" b] c) d := ⟨_, _, _, _, rfl⟩

theorem gxPlan_for : ∃ a b, genPlan gxFor
    = .forHere (.name "m" a) (.name ".0" b) gxBody := ⟨_, _, rfl⟩
theorem gxPlan_bind : genPlan gxBind = .delegate := rfl
theorem gxPlan_test : ∃ a b c d e, genPlan gxTest
    = .branch (.boolOp .or #[.compare (.name "v" a) #[.gtE] #[.name "QS" b] c,
        .name "depth" d] e) [gxYield] [] := ⟨_, _, _, _, _, rfl⟩
theorem gxPlan_yield : ∃ a b c, genPlan gxYield
    = .yieldHere (.tuple #[.name "v" a, .name "m" b] c) := ⟨_, _, _, rfl⟩

/-! ## §1 What the filter needs of the world: `QS`, and nothing else -/

theorem qsG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "QS"
    = some (some (.int 40)) := rfl

/-! ## §2 The CALL allocates and runs nothing -/

def gxEnv (z0 : RVal) (d : Int) (p : RVal) : REnv :=
  [(".0", z0), ("depth", .int d), ("pos", p)]

theorem gxCallEnv (z0 : RVal) (d : Int) (p : RVal) :
    mkCallEnv gxF.params #[z0, .int d, p] = gxEnv z0 d p := rfl

def gxObj (z0 : RVal) (d : Int) (p : RVal) : Obj :=
  .generator "<genexpr@1>" (gxEnv z0 d p) [.block gxB] .created

def gxWorld (w : World) (z0 : RVal) (d : Int) (p : RVal) : World :=
  { w with heap := w.heap.push (gxObj z0 d p) }

theorem gx_call (w : World) (z0 : RVal) (d : Int) (p : RVal) (F : Nat) :
    callIn sunfish (F + 1) w "<genexpr@1>" #[z0, .int d, p]
      = .ok (gxWorld w z0 d p) (.ref w.heap.size) := by
  obtain ⟨hf, hargs, hloc, hgen, hglob, hbody, harity⟩ := gxF_lit
  rw [callIn_genCall hf hargs hloc (by simpa using harity) hgen]
  simp only [gxWorld, gxObj, genObj, gxCallEnv, hbody]

/-! ## §3 The `or` chain gets its altitude lemmas -/

theorem boolChain_or_truthy {m : Module} {F : Nat} {st st₁ : FrameState}
    {e1 : Expr} {es : List Expr} {v1 : RVal}
    (h1 : evalExpr m F st e1 = .ok st₁ v1)
    (hb1 : truthyH st₁.world.heap v1 = .ok true) :
    evalBoolChain m (F + 1) st .or e1 es = .ok st₁ v1 := by
  rw [evalBoolChain, h1]
  cases es <;> simp only [Run.bind, Run.liftRes, hb1, if_true]

theorem boolChain_or2 {m : Module} {F : Nat} {st st₁ st₂ : FrameState}
    {e1 e2 : Expr} {v1 v2 : RVal}
    (h1 : evalExpr m (F + 1) st e1 = .ok st₁ v1)
    (hb1 : truthyH st₁.world.heap v1 = .ok false)
    (h2 : evalExpr m F st₁ e2 = .ok st₂ v2) :
    evalBoolChain m (F + 2) st .or e1 [e2] = .ok st₂ v2 := by
  rw [evalBoolChain, h1]
  simp only [Run.bind, Run.liftRes, hb1, Bool.false_eq_true, if_false]
  rw [evalBoolChain, h2]
  simp only [Run.bind]

/-! ## §4 The binding statement, and it CONSUMES R1 -/

theorem value_call_evals {w : World} {e : REnv} {b : String} {sc ep kp : Int}
    {wc0 wc1 bc0 bc1 : Bool} {mv : RVal} {z : Int} {F : Nat}
    {sp1 sp2 sp3 sp4 : Span}
    (hp : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hm : Env.lookup e "m" = some mv)
    (hcall : callIn sunfish (F + 7) w "Position.value"
      #[posOf b sc wc0 wc1 bc0 bc1 ep kp, mv] = .ok w (.int z)) :
    evalExpr sunfish (F + 8) ⟨w, e⟩
        (.call (.attribute (.name "pos" sp1) "value" sp2) #[.name "m" sp3] #[] Option.none sp4)
      = .ok ⟨w, e⟩ (.int z) := by
  py_simp [-globalsFold, -globalsStep, hp, hm, posOf, posCAux, posCls_methods,
    posCls_ntBase_isSome]
  simpa only [posOf] using hcall

theorem gx_binds {w : World} {e : REnv} {b : String} {sc ep kp : Int}
    {wc0 wc1 bc0 bc1 : Bool} {mv : RVal} {z : Int} {F : Nat}
    (hp : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hm : Env.lookup e "m" = some mv)
    (hcall : callIn sunfish (F + 7) w "Position.value"
      #[posOf b sc wc0 wc1 bc0 bc1 ep kp, mv] = .ok w (.int z)) :
    execStmt sunfish (F + 9) ⟨w, e⟩ gxBind
      = .ok ⟨w, Env.set e "v" (.int z)⟩ .next := by
  obtain ⟨a, b', c, d, e', hlit⟩ := gxBind_lit
  rw [hlit]
  exact execStmt_assign_name (value_call_evals hp hm hcall)

/-! ## §5 The filter, ALL THREE arms -/

/-- The chain's first operand, at whichever truth value the QS floor gives it. -/
theorem gx_cmp_evals (w : World) (e : REnv) (v : Int) (F : Nat) (a b c : Span)
    (hv : Env.lookup e "v" = some (.int v))
    (hnq : Env.lookup e "QS" = Option.none) (hhi : 40 ≤ v) :
    evalExpr sunfish (F + 3) ⟨w, e⟩ (.compare (.name "v" a) #[.gtE] #[.name "QS" b] c)
      = .ok ⟨w, e⟩ (.bool true) := by
  py_simp [-globalsFold, -globalsStep, hv, hnq, qsG, if_pos hhi]

theorem gx_cmp_evals_low (w : World) (e : REnv) (v : Int) (F : Nat) (a b c : Span)
    (hv : Env.lookup e "v" = some (.int v))
    (hnq : Env.lookup e "QS" = Option.none) (hlo : v < 40) :
    evalExpr sunfish (F + 3) ⟨w, e⟩ (.compare (.name "v" a) #[.gtE] #[.name "QS" b] c)
      = .ok ⟨w, e⟩ (.bool false) := by
  py_simp [-globalsFold, -globalsStep, hv, hnq, qsG, if_neg (show ¬ (40 : Int) ≤ v by omega)]

/-- **THE MOVE CLEARS THE QS FLOOR**, so the chain stops at its first operand and
never reads `depth` at all. -/
theorem gx_filter_high (w : World) (e : REnv) (v : Int) (F : Nat) (a b c dd ee : Span)
    (hv : Env.lookup e "v" = some (.int v))
    (hnq : Env.lookup e "QS" = Option.none) (hhi : 40 ≤ v) :
    evalExpr sunfish (F + 5) ⟨w, e⟩
        (.boolOp .or #[.compare (.name "v" a) #[.gtE] #[.name "QS" b] c,
          .name "depth" dd] ee) = .ok ⟨w, e⟩ (.bool true) := by
  rw [evalExpr]
  exact boolChain_or_truthy (F := F + 3) (gx_cmp_evals w e v F a b c hv hnq hhi) rfl

/-- **THE MOVE IS SUB-FLOOR BUT THE SEARCH IS NOT A QSEARCH**: the chain falls
through to `depth`, whose own value is what the filter answers. -/
theorem gx_filter_low (w : World) (e : REnv) (v d : Int) (F : Nat) (a b c dd ee : Span)
    (hv : Env.lookup e "v" = some (.int v))
    (hd : Env.lookup e "depth" = some (.int d))
    (hnq : Env.lookup e "QS" = Option.none) (hlo : v < 40) :
    evalExpr sunfish (F + 5) ⟨w, e⟩
        (.boolOp .or #[.compare (.name "v" a) #[.gtE] #[.name "QS" b] c,
          .name "depth" dd] ee) = .ok ⟨w, e⟩ (.int d) := by
  have hdep : evalExpr sunfish (F + 2) ⟨w, e⟩ (.name "depth" dd) = .ok ⟨w, e⟩ (.int d) := by
    py_simp [-globalsFold, -globalsStep, hd]
  rw [evalExpr]
  exact boolChain_or2 (F := F + 2)
    (gx_cmp_evals_low w e v F a b c hv hnq hlo) rfl hdep

/-! And the two truthiness readings the `.branch` plan routes on: a sub-floor move
is DROPPED exactly at `depth = 0`, which is the QS floor the comment on
sunfish.py:443 claims — *"the QS floor lives here, ahead of the sort"*. -/

theorem gx_keeps_high (w : World) : truthyH w.heap (.bool true) = .ok true := rfl

theorem gx_drops_at_qs (w : World) : truthyH w.heap (.int 0) = .ok false := rfl

theorem gx_keeps_deep (w : World) (d : Int) (hd : d ≠ 0) :
    truthyH w.heap (.int d) = .ok true := by
  simp [truthyH, truthy, hd]


/-! ## §6 THE MEASUREMENTS, on the live engine

Run before a line above was written (§L24's exit law), and two of them are the
reason this file is worth having: they turn the shipped comment on sunfish.py:443
— *"the QS floor lives here, ahead of the sort, so the fold never walks sub-floor
junk"* — into a NUMBER.

The fixture is the opening position, whose `gen_moves` yields **20** moves. -/

/-- The generator `gen_moves` answers, which is the genexp's `.0`. -/
private def fxGm (F : Nat) : Option (World × Addr) :=
  match callIn sunfish F (initWorld sunfish) "Position.gen_moves" #[posH 0] with
  | .ok w (RVal.ref a) => some (w, a)
  | _ => Option.none

/-- The genexp, called on it — and this is `gx_call`'s conclusion on the fixture. -/
private def fxGx (F : Nat) (d : Int) : Option (World × Addr) :=
  match fxGm F with
  | some (w, a) =>
    (match callIn sunfish F w "<genexpr@1>" #[RVal.ref a, RVal.int d, posH 0] with
     | .ok w' (RVal.ref b) => some (w', b)
     | _ => Option.none)
  | none => Option.none

/-- Drained: the heap before, the heap after, and how many pairs came out. -/
private def fxDrain (F : Nat) (d : Int) : Option (Nat × Nat × Nat) :=
  match fxGx F d with
  | some (w, b) =>
    (match drainIter sunfish F w b with
     | .ok w' vs => some (w.heap.size, w'.heap.size, vs.length)
     | _ => Option.none)
  | none => Option.none

/-! Two CALLS, two objects: the live heap is 66, and `gen_moves` plus the genexp
leave it at 68 without running a step — which is `gx_call`'s content, checked. -/
#guard (initWorld sunfish).heap.size == 66
#guard (match fxGx 256 0 with | some (w, _) => w.heap.size == 68 | none => false)

/-! **THE QS FLOOR, MEASURED.** At `depth = 0` the drain yields **2** of the
twenty moves — the only two whose `Position.value` clears 40 — and at `depth = 3`
it yields all **20**, because the chain's second operand is truthy and the floor
never applies. That is `gx_filter_high`/`gx_filter_low`/`gx_drops_at_qs` on the
fixture, and it is the shipped comment's claim in numbers. -/
#guard (match fxDrain 256 0 with | some (_, _, n) => n == 2 | none => false)
#guard (match fxDrain 256 3 with | some (_, _, n) => n == 20 | none => false)

/-! **THE ALLOCATION.** The drain takes the heap 68 → 149: **81 objects**, one
`(v, m)` tuple per surviving pair plus the inner drain's own bookkeeping. §L25
measured 84 for the WHOLE ordering line, so 81 of the 84 are this genexp's and
`sorted` plus the `for` account for three. Its post-world is therefore
`++ ext`-shaped exactly as §L25 predicted. -/
#guard (match fxDrain 256 3 with | some (h0, h1, _) => h0 == 68 && h1 == 149 | none => false)

/-! **THE FUEL.** 208 decides the whole line — call, inner drain and outer drain —
and 200 does not. So the ~400 §L25 priced for the ordering LINE is roughly double
what its genexp needs, and no gate above pins a numeral. -/
#guard (match fxDrain 208 3 with | some (_, _, n) => n == 20 | none => false)
#guard (fxDrain 200 3).isNone

#print axioms gxB_split
#print axioms gxBody_split
#print axioms gxF_lit
#print axioms gxFor_lit
#print axioms gxBind_lit
#print axioms gxTest_lit
#print axioms gxYield_lit
#print axioms gxPlan_for
#print axioms gxPlan_bind
#print axioms gxPlan_test
#print axioms gxPlan_yield
#print axioms qsG
#print axioms gxCallEnv
#print axioms gx_call
#print axioms boolChain_or_truthy
#print axioms boolChain_or2
#print axioms value_call_evals
#print axioms gx_binds
#print axioms gx_cmp_evals
#print axioms gx_cmp_evals_low
#print axioms gx_filter_high
#print axioms gx_filter_low
#print axioms gx_keeps_high
#print axioms gx_drops_at_qs
#print axioms gx_keeps_deep

/-! ## What R2a still owes

**The round is complete; the INDUCTION over rounds is not.** What is proved here
is one round's worth of the genexp — the call, the binding statement, the filter
in all three arms, and the two truthiness readings the `.branch` plan routes on —
plus the measurements that say what the whole drain does. What is owed is the
`.forHere` induction that strings the rounds together, and its shape is now
FIXED rather than guessed, which is what this pass was for:

* **the inner iterable is a GENERATOR, not a list.** `.0` is the `.ref`
  `Position.gen_moves` answered, so the round's own `for` advances it by
  `stepIter` and `gen_moves_drains_ref` (§L8) is the supply. §L25's `.forList`
  live cursor is **R2c's** problem — the `for` over `sorted(…)`'s heap LIST — and
  not this one. Two different `for` rules, and the census is what separates them.
* **`genSilent_forHere`'s value-sequence form does not fit.** It covers a `for`
  over a value SEQUENCE; here the iterable is a heap object being consumed in
  lockstep, so the round lemma is `moves_loop_cuts`-shaped (sf_order's worked
  precedent) rather than `genSilent_forHere`-shaped.
* **the post-world is `++ ext`-shaped**, measured: 81 objects, heap 68 → 149. So
  every slot the rest of `moves()` reads survives by `Heap.get?_append`, exactly
  as §L25 priced it.
* **the yield's payload is a heap-free TUPLE of two values** (`gxYield_lit`), so
  the round's output needs no allocation lemma of its own — the 81 objects are the
  inner drain's and the tuple's, not the frame's.

**And one prediction of §L25 corrected.** The plan said *"the WALRUS `v :=` binds
in the genexp's own frame — census it before writing the gate."* There is no
walrus construct to census: ingestion lowered `(v := pos.value(m)) >= QS` into a
plain `assign` HOISTED above the `if` (`gxBind_lit`, `gxPlan_bind = .delegate`),
so `v` is an ordinary local and the binding is an ordinary statement gate. The
construct the plan reserved a session for does not exist in the projected program.

**What R1 supplies, and it is exactly what was owed.** `gx_binds` takes the
`Position.value` call as a `callIn` hypothesis, and `value_runs_quiet` /
`value_runs_capture` / `value_runs_kp` / `value_runs_castle` (value_bound.lean)
are the four theorems that discharge it. `value_call_evals` is the only bridge
that was missing: the interpreter reaches a namedtuple method through
`posCls.2.ntBase.isSome`, and past that guard the residue is `callIn` under
`Run.withLocals` — so R1's conclusion plugs in with no transport at all. -/

end Examples.python.sunfish.order_genexp
