/-
**THE ORDERING LINE** — inches R2a, R2b and R2c of the `RecursionStep` campaign
(docs/backlog.md §L25), from the genexp's round to the stream `moves()` emits.

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

**R2b and R2c** (§7, §8) close the outside of the line, and `sf_order`'s
`order_line_sorts`/`moves_loop_cuts` (§L8) are the worked precedents — the twin's
`Position.gen_moves`/`Position.value` are the shipped sunfish methods verbatim, so
transposing them is application rather than discovery. Two differences: the
genexp takes a THIRD argument here (sunfish's filter captures `depth`), and the
loop has no `break`, because ingestion's `yield from` rewrite left a body of one
statement — so this loop runs to exhaustion where the twin's cuts.

`ord_stmt_emits` (§8) is where the three meet: the shipped statement, from source
text to emitted stream, with **one** non-bookkeeping hypothesis left — the genexp
object's drain, which is R2a's remainder and is shaped in §10.
-/
import Examples.python.sunfish.value_bound

namespace Examples.python.sunfish.order_genexp

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)
open Examples.python.sunfish.bound_depth (posCAux posCls_methods posCls_ntBase_isSome
  execStmt_if_true execStmt_if_false execStmt_assign_name compare_one sbMB sbMBRest)
open Examples.python.sunfish.value_bound
open Examples.python.sunfish.genmoves_scan (genSilent_forHereGen)

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

/-! ## §7 R2b — THE ORDERING LINE ITSELF

`sorted(<genexpr@1>(pos.gen_moves(), depth, pos), reverse=True)`, read outside
in: a keyword `sorted` whose single argument is a call to the lowered genexp,
whose own first argument is a generator METHOD call on the receiver. **Three
allocations, two of them inside the argument list**, which is why the statement
is `EvalsIn` and not `EvalsTo`.

**Nothing here is new machinery.** `sf_order`'s `order_line_sorts` (§L8) is this
theorem on the ingested twin, whose `Position.gen_moves`/`Position.value` are the
shipped sunfish methods verbatim; `EvalsIn.sortedDrainRev` is the rule and the
census §L25 ran is what said it already existed. The two differences from the
twin are the genexp's THIRD argument — sunfish's filter captures `depth` as well
as `pos` — and the module. -/

def ordFor : Stmt := nth 1 sbMBRest
def ordTarget : Expr :=
  match ordFor with | .forStmt t _ _ _ _ => t | _ => .constant .none nowhere
/-- **The shipped ordering line** (sunfish.py:444), as an AST. -/
def ordLine : Expr :=
  match ordFor with | .forStmt _ it _ _ _ => it | _ => .constant .none nowhere
def ordBody : List Stmt :=
  match ordFor with | .forStmt _ _ b _ _ => b.toList | _ => []
/-- `yield <yieldfrom@2>` — what ingestion left of `yield from`. -/
def ordYield : Stmt := nth 0 ordBody

def ordGxCall : Expr :=
  match ordLine with | .call _ args _ _ _ => args[0]! | _ => .constant .none nowhere
def ordRevE : Expr :=
  match ordLine with | .call _ _ kws _ _ => kws[0]!.2 | _ => .constant .none nowhere
def ordGmCall : Expr :=
  match ordGxCall with | .call _ args _ _ _ => args[0]! | _ => .constant .none nowhere
def ordDepthE : Expr :=
  match ordGxCall with | .call _ args _ _ _ => args[1]! | _ => .constant .none nowhere
def ordPosE : Expr :=
  match ordGxCall with | .call _ args _ _ _ => args[2]! | _ => .constant .none nowhere

theorem sbMBRest_split : sbMBRest = [nth 0 sbMBRest, ordFor] := rfl

theorem ordFor_lit : ∃ sp, ordFor = .forStmt ordTarget ordLine ordBody.toArray #[] sp :=
  ⟨_, rfl⟩
theorem ordTarget_lit : ∃ sp, ordTarget = .name "<yieldfrom@2>" sp := ⟨_, rfl⟩
theorem ordBody_split : ordBody = [ordYield] := rfl
theorem ordYield_lit : ∃ s₁ s₂, ordYield = .yieldStmt (.name "<yieldfrom@2>" s₁) s₂ :=
  ⟨_, _, rfl⟩
theorem ordLine_lit : ∃ s₁ s₂, ordLine =
    .call (.name "sorted" s₁) #[ordGxCall] #[("reverse", ordRevE)] Option.none s₂ :=
  ⟨_, _, rfl⟩
theorem ordRevE_lit : ∃ s, ordRevE = .constant (.bool true) s := ⟨_, rfl⟩
theorem ordGxCall_lit : ∃ s₁ s₂, ordGxCall =
    .call (.name "<genexpr@1>" s₁) #[ordGmCall, ordDepthE, ordPosE] #[] Option.none s₂ :=
  ⟨_, _, rfl⟩
theorem ordGmCall_lit : ∃ s₁ s₂ s₃, ordGmCall =
    .call (.attribute (.name "pos" s₁) "gen_moves" s₂) #[] #[] Option.none s₃ := ⟨_, _, _, rfl⟩
theorem ordDepthE_lit : ∃ s, ordDepthE = .name "depth" s := ⟨_, rfl⟩
theorem ordPosE_lit : ∃ s, ordPosE = .name "pos" s := ⟨_, rfl⟩

theorem ordFor_plan : genPlan ordFor = .forHere ordTarget ordLine ordBody := rfl
theorem ordYield_plan : ∃ s, genPlan ordYield = .yieldHere (.name "<yieldfrom@2>" s) :=
  ⟨_, rfl⟩

/-- The shipped `Position.gen_moves`, projected. -/
def gmF : FunctionDefn :=
  match findFunction sunfish "Position.gen_moves" with
  | some f => f | none => default

theorem gm_lit : findFunction sunfish "Position.gen_moves" = some gmF ∧
    gmF.argsOk = true ∧ gmF.localsOk = true ∧ arityOk gmF.params 1 = true ∧
    gmF.isGenerator = true ∧ (∀ p : RVal, mkCallEnv gmF.params #[p] = [("self", p)]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- `sorted` is the builtin here, not a shadow — `evalExpr`'s own resolution
order, hypothesis by hypothesis, and every one is `rfl` at a literal module. -/
theorem sorted_free : lookupG (moduleGlobals sunfish).1 "sorted" = Option.none ∧
    findFunction sunfish "sorted" = Option.none ∧
    findClass sunfish "sorted" = Option.none ∧
    findNamedTuple sunfish "sorted" = Option.none := ⟨rfl, rfl, rfl, rfl⟩

theorem gxName_free : lookupG (moduleGlobals sunfish).1 "<genexpr@1>" = Option.none ∧
    findClass sunfish "<genexpr@1>" = Option.none ∧
    findNamedTuple sunfish "<genexpr@1>" = Option.none := ⟨rfl, rfl, rfl⟩

/-- `.gen_moves` on a `Position` value is the SUBCLASS method, resolved before
any argument runs. -/
theorem gm_plan : ntupleCallPlan sunfish "Position"
    #["board", "score", "wc", "bc", "ep", "kp"] "gen_moves"
    = .instMethod "Position.gen_moves" := rfl

/-- The object `pos.gen_moves()` allocates. -/
def gmObj (pv : RVal) : Obj := genObj "Position.gen_moves" gmF #[pv]
/-- The object `<genexpr@1>(<that one>, depth, pos)` allocates. -/
def gxObj3 (a : Addr) (d : Int) (pv : RVal) : Obj :=
  genObj "<genexpr@1>" gxF #[.ref a, .int d, pv]
/-- The world after the receiver's method call. -/
def gmW (w : World) (pv : RVal) : World := { w with heap := w.heap.push (gmObj pv) }
/-- The world after the genexp call — two objects, in evaluation order. -/
def gxW (w : World) (d : Int) (pv : RVal) : World :=
  { w with heap := (w.heap.push (gmObj pv)).push (gxObj3 w.heap.size d pv) }

/-- **GATE R2b — the shipped ordering line evaluates to the sorted list.**

In a frame that binds `pos` to a `Position` value and `depth` to an integer, and
shadows neither `sorted` nor the lowered genexp, the line evaluates to a `.ref`
at the post-drain heap's END, and the object there is a FRESH `.list` holding
`sortByLt true` of exactly what the genexp object drained to.

The one hypothesis that is not bookkeeping is `hdrain` — what the genexp OBJECT
yields — and that is R2a's remaining obligation, named here so the two inches
meet at a judgment rather than at a hope. -/
theorem order_line_sorts (w : World) (env : REnv) (d : Int)
    (b : String) (sc ep kp : Int) (wc0 wc1 bc0 bc1 : Bool)
    (vs sortedVs : List RVal) (w' : World)
    (hpos : Env.lookup env "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hdepth : Env.lookup env "depth" = some (.int d))
    (hsorted : Env.lookup env "sorted" = Option.none)
    (hgxl : Env.lookup env "<genexpr@1>" = Option.none)
    (hdrain : IterDrains sunfish
      (gxW w d (posOf b sc wc0 wc1 bc0 bc1 ep kp)) (w.heap.size + 1) vs w')
    (hsort : sortByLt true vs = .ok sortedVs) :
    EvalsIn sunfish ⟨w, env⟩ ordLine (.ref w'.heap.size)
      ⟨{ w' with heap := w'.heap.push (.list sortedVs.toArray) }, env⟩ := by
  obtain ⟨s₁, s₂, hord⟩ := ordLine_lit
  obtain ⟨t₁, t₂, hgx⟩ := ordGxCall_lit
  obtain ⟨u₁, u₂, u₃, hgm⟩ := ordGmCall_lit
  obtain ⟨v₁, hposE⟩ := ordPosE_lit
  obtain ⟨v₂, hdepE⟩ := ordDepthE_lit
  obtain ⟨r₁, hrev⟩ := ordRevE_lit
  have hrecv : EvalsIn sunfish ⟨w, env⟩ (.name "pos" u₁)
      (posOf b sc wc0 wc1 bc0 bc1 ep kp) ⟨w, env⟩ :=
    EvalsIn.of_evalsTo (EvalsTo.of_eval (fuel := 4) (by py_simp [hpos]))
  have hgmEv : EvalsIn sunfish ⟨w, env⟩ ordGmCall (.ref w.heap.size)
      ⟨gmW w (posOf b sc wc0 wc1 bc0 bc1 ep kp), env⟩ := by
    rw [hgm]
    have := EvalsIn.ntupleGenMethod (qname := "Position.gen_moves") (f := gmF)
      (vs := []) (sp := u₂) (sp' := u₃) rfl hrecv gm_plan EvalsInList.nil
      gm_lit.1 gm_lit.2.1 gm_lit.2.2.1 (by simpa using gm_lit.2.2.2.1)
      gm_lit.2.2.2.2.1
    simpa [gmW, gmObj, posOf] using this
  have hdepEv : EvalsIn sunfish ⟨gmW w (posOf b sc wc0 wc1 bc0 bc1 ep kp), env⟩
      ordDepthE (.int d) ⟨gmW w (posOf b sc wc0 wc1 bc0 bc1 ep kp), env⟩ := by
    rw [hdepE]
    exact EvalsIn.of_evalsTo (EvalsTo.of_eval (fuel := 4) (by py_simp [hdepth]))
  have hposEv : EvalsIn sunfish ⟨gmW w (posOf b sc wc0 wc1 bc0 bc1 ep kp), env⟩
      ordPosE (posOf b sc wc0 wc1 bc0 bc1 ep kp)
      ⟨gmW w (posOf b sc wc0 wc1 bc0 bc1 ep kp), env⟩ := by
    rw [hposE]
    exact EvalsIn.of_evalsTo (EvalsTo.of_eval (fuel := 4) (by py_simp [hpos]))
  have hargs : EvalsInList sunfish ⟨w, env⟩ [ordGmCall, ordDepthE, ordPosE]
      [.ref w.heap.size, .int d, posOf b sc wc0 wc1 bc0 bc1 ep kp]
      ⟨gmW w (posOf b sc wc0 wc1 bc0 bc1 ep kp), env⟩ :=
    EvalsInList.cons hgmEv (EvalsInList.cons hdepEv (EvalsInList.one hposEv))
  have hgxEv : EvalsIn sunfish ⟨w, env⟩ ordGxCall (.ref (w.heap.size + 1))
      ⟨gxW w d (posOf b sc wc0 wc1 bc0 bc1 ep kp), env⟩ := by
    rw [hgx]
    have := EvalsIn.genCallIn (m := sunfish) (st := ⟨w, env⟩)
      (st₁ := ⟨gmW w (posOf b sc wc0 wc1 bc0 bc1 ep kp), env⟩)
      (fname := "<genexpr@1>") (f := gxF) (argEs := #[ordGmCall, ordDepthE, ordPosE])
      (vs := [.ref w.heap.size, .int d, posOf b sc wc0 wc1 bc0 bc1 ep kp])
      (sp := t₁) (sp' := t₂)
      hgxl gxName_free.1 gxName_free.2.1 gxName_free.2.2 gxF_lit.1 gxF_lit.2.1
      gxF_lit.2.2.1 (by simpa using gxF_lit.2.2.2.2.2.2) gxF_lit.2.2.2.1
      (by simpa using hargs)
    simpa [gmW, gxW, gxObj3] using this
  have hrevEv : EvalsIn sunfish ⟨gxW w d (posOf b sc wc0 wc1 bc0 bc1 ep kp), env⟩
      ordRevE (.bool true) ⟨gxW w d (posOf b sc wc0 wc1 bc0 bc1 ep kp), env⟩ := by
    rw [hrev]; exact EvalsIn.of_evalsTo (EvalsTo.of_eval (fuel := 1) rfl)
  have hobj : Heap.get? (gxW w d (posOf b sc wc0 wc1 bc0 bc1 ep kp)).heap (w.heap.size + 1)
      = some (gxObj3 w.heap.size d (posOf b sc wc0 wc1 bc0 bc1 ep kp)) := by
    have h := Heap.get?_push_size (w.heap.push (gmObj (posOf b sc wc0 wc1 bc0 bc1 ep kp)))
      (gxObj3 w.heap.size d (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    simpa [gxW] using h
  rw [hord]
  exact EvalsIn.sortedDrainRev hsorted sorted_free.1 sorted_free.2.1
    sorted_free.2.2.1 sorted_free.2.2.2 hgxEv hrevEv rfl
    (by simpa [gxObj3, genObj] using hobj) hdrain hsort


/-! ## §8 R2c — THE LIVE-CURSOR LOOP over the sorted list

`sorted` ALLOCATES, so `execGen`'s `.forHere` arm pushes a **`forList`** frame at
the ordering line's answer — not a `forSeq`, which is why §L25 named the
live-cursor frame and why `genSilent_forHere`'s value-sequence rule is not the
one. `sf_order`'s `moves_loop_cuts` is the worked precedent; sunfish's loop is
**strictly simpler than its twin's**, because ingestion's `yield from` rewrite
left a body of one statement and no `break`: this loop runs to EXHAUSTION and
re-emits the list unchanged. The beta cutoff `moves_loop_cuts` proves lives in
the CONSUMER here (`bound()`'s own fold), not in this loop.

The exit FRAME is existential and the exit WORLD is not (§L26's law): the loop
allocates nothing, so the world rides through, and the only thing left unnamed is
the loop variable's last value — which nothing reads, because the ordering line
is `moves()`' last statement. -/

/-- The frame the target leaves; `Env.set` replaces in place, so the shape is
stable across rounds. -/
def ordEnvAt (env : REnv) (v : RVal) : REnv := Env.set env "<yieldfrom@2>" v

theorem ord_assign (h : Heap) (env : REnv) (v : RVal) :
    assignToH h env ordTarget v = .ok (ordEnvAt env v) := rfl

/-- **The body at any element**: one `yield`, emitting exactly what the target
was bound to. -/
theorem ord_body_emits (w : World) (e : REnv) (v : RVal)
    (hv : Env.lookup e "<yieldfrom@2>" = some v) :
    GenEmits sunfish ⟨w, e⟩ [.block ordBody] [v] ⟨w, e⟩ := by
  obtain ⟨s₁, s₂, hy⟩ := ordYield_lit
  have hyield : ∀ k : GenCont, GenSteps sunfish ⟨w, e⟩ ([GenFrame.block ordBody] ++ k)
      (some (v, [GenFrame.block []] ++ k)) ⟨w, e⟩ := by
    intro k
    have h := genSteps_yieldHere (m := sunfish) (st := ⟨w, e⟩) (s := ordYield)
      (ss := ([] : List Stmt)) (k := k) (v := v)
      (by rw [hy]; rfl) (EvalsTo.of_eval (fuel := 4) (by py_simp [hv]))
    simpa [ordBody_split] using h
  refine GenEmits.cons hyield ?_
  exact GenEmits.silent (pre₁ := ([] : GenCont))
    (fun k => by simpa using genSilent_blockNil (m := sunfish) (k := k)) GenEmits.nil

/-- An exhausted block frame emits nothing — the tail `blockForList` leaves
below the loop when the `for` is the last statement. -/
theorem ord_blockNil_emits (st : FrameState) :
    GenEmits sunfish st [.block []] [] st :=
  GenEmits.silent (pre₁ := ([] : GenCont))
    (fun k => by simpa using genSilent_blockNil (m := sunfish) (k := k)) GenEmits.nil

/-- The rounds, by induction on how many are left. -/
private theorem ord_go (w : World) (ad : Addr) (xs : Array RVal)
    (hobj : Heap.get? w.heap ad = some (.list xs)) :
    ∀ (n i : Nat) (env : REnv), i + n = xs.size →
      ∃ env', GenEmits sunfish ⟨w, env⟩ [.forList ordTarget ad i ordBody]
        (xs.toList.drop i) ⟨w, env'⟩ := by
  intro n
  induction n with
  | zero =>
    intro i env hn
    refine ⟨env, ?_⟩
    have hnil : xs.toList.drop i = [] := by
      apply List.drop_eq_nil_of_le
      simp
      omega
    rw [hnil]
    exact GenEmits.forListDone (m := sunfish) (target := ordTarget)
      (body := ordBody) (st := ⟨w, env⟩) (ad := ad) (i := i) hobj (by omega)
  | succ n ih =>
    intro i env hn
    have hi : i < xs.size := by omega
    have hil : i < xs.toList.length := by simpa using hi
    obtain ⟨env', hrest⟩ := ih (i + 1) (ordEnvAt env (xs.getD i .none)) (by omega)
    refine ⟨env', ?_⟩
    have hval : xs.getD i .none = xs.toList[i] := by simp [Array.getD, hi]
    have hround := GenEmits.forListRound (m := sunfish) (target := ordTarget)
      (body := ordBody) (ad := ad) (i := i) (xs := xs) (st := ⟨w, env⟩)
      (env₁ := ordEnvAt env (xs.getD i .none)) hobj hi (ord_assign w.heap env _)
      (ord_body_emits w (ordEnvAt env (xs.getD i .none)) (xs.getD i .none)
        (by simp [ordEnvAt, Env.lookup_set_self]))
      hrest
    rw [List.drop_eq_getElem_cons hil, ← hval]
    simpa using hround

/-- **GATE R2c — the loop re-emits the sorted list.** Over an arbitrary heap
list, the shipped `for <yieldfrom@2> in …: yield <yieldfrom@2>` emits exactly its
elements, in order, and pops its own frame at the end. -/
theorem ord_loop_emits (w : World) (ad : Addr) (xs : Array RVal) (env : REnv)
    (hobj : Heap.get? w.heap ad = some (.list xs)) :
    ∃ env', GenEmits sunfish ⟨w, env⟩ [.forList ordTarget ad 0 ordBody]
      xs.toList ⟨w, env'⟩ := by
  obtain ⟨env', h⟩ := ord_go w ad xs hobj xs.size 0 env (by omega)
  exact ⟨env', by simpa using h⟩

/-- The world the whole line leaves: the drain's world plus the sorted list. -/
def ordW (w' : World) (sortedVs : List RVal) : World :=
  { w' with heap := w'.heap.push (.list sortedVs.toArray) }

/-- **THE WHOLE ORDERING STATEMENT** — R2b and R2c joined at the frame the one
pushes and the other consumes.

From the source text of sunfish.py:444, inside the `moves()` generator: the line
evaluates (allocating the `gen_moves` generator, the genexp generator and the
sorted list), the loop opens on that list, and the generator emits `sortedVs` —
the drained pairs in descending order — leaving the drain's world plus one list.

`hdrain` is R2a's remaining obligation and the only hypothesis here that is not
bookkeeping; `hsort` is `sortByLt`'s own totality on the drained values. -/
theorem ord_stmt_emits (w : World) (env : REnv) (d : Int)
    (b : String) (sc ep kp : Int) (wc0 wc1 bc0 bc1 : Bool)
    (vs sortedVs : List RVal) (w' : World)
    (hpos : Env.lookup env "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hdepth : Env.lookup env "depth" = some (.int d))
    (hsorted : Env.lookup env "sorted" = Option.none)
    (hgxl : Env.lookup env "<genexpr@1>" = Option.none)
    (hdrain : IterDrains sunfish
      (gxW w d (posOf b sc wc0 wc1 bc0 bc1 ep kp)) (w.heap.size + 1) vs w')
    (hsort : sortByLt true vs = .ok sortedVs) :
    ∃ env', GenEmits sunfish ⟨w, env⟩ [.block [ordFor]] sortedVs
      ⟨ordW w' sortedVs, env'⟩ := by
  have hline := order_line_sorts w env d b sc ep kp wc0 wc1 bc0 bc1 vs sortedVs w'
    hpos hdepth hsorted hgxl hdrain hsort
  have hobj : Heap.get? (ordW w' sortedVs).heap w'.heap.size
      = some (.list sortedVs.toArray) := by
    simpa [ordW] using Heap.get?_push_size w'.heap (Obj.list sortedVs.toArray)
  obtain ⟨env', hloop⟩ := ord_loop_emits (ordW w' sortedVs) w'.heap.size
    sortedVs.toArray env hobj
  refine ⟨env', ?_⟩
  have hrest : GenEmits sunfish ⟨ordW w' sortedVs, env⟩
      [.forList ordTarget w'.heap.size 0 ordBody, .block []] sortedVs
      ⟨ordW w' sortedVs, env'⟩ := by
    simpa using GenEmits.trans hloop (ord_blockNil_emits ⟨ordW w' sortedVs, env'⟩)
  have h := GenEmits.blockForList (m := sunfish) (s := ordFor) (target := ordTarget)
    (iter := ordLine) (body := ordBody) (ss := ([] : List Stmt))
    (ad := w'.heap.size) (xs := sortedVs.toArray) ordFor_plan
    (by simpa [ordW] using hline) hobj hrest
  simpa using h


/-! ## §9 THE ROUND, both arms — what the `.forGen` induction will chain

§L29 owed "the induction over rounds", and the round's BODY is the part with
content: everything else is `GenEmits.forGenRound`/`forGenDone` bookkeeping. Two
theorems, one per arm of the filter, and between them they say what one move
costs the ordering stream.

Note which loop rule this is. R2c's loop reads a heap LIST and takes
`.forList`; **this one reads a generator OBJECT and takes `.forGen`**, because
`.0` is the `.ref` `Position.gen_moves` answered. Same statement shape in the
source, two different frames, and the census (§L29) is what separated them. -/

/-- The genexp's frame after the binding statement. -/
def gxEnvAt (env : REnv) (z : Int) : REnv := Env.set env "v" (.int z)

/-- `Position.value`'s answer, in the threshold form R1's four `value_runs_*`
theorems produce — so the round consumes them verbatim. -/
def ValueAnswers (w : World) (pv mv : RVal) (z : Int) : Prop :=
  ∃ t, ∀ F ≥ t, callIn sunfish F w "Position.value" #[pv, mv] = .ok w (.int z)

/-- The binding statement at threshold fuel, which is what `genSilent_delegate`
consumes. -/
theorem gx_binds_at {w : World} {env : REnv} {b : String} {sc ep kp : Int}
    {wc0 wc1 bc0 bc1 : Bool} {mv : RVal} {z : Int}
    (hp : Env.lookup env "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hm : Env.lookup env "m" = some mv)
    (hval : ValueAnswers w (posOf b sc wc0 wc1 bc0 bc1 ep kp) mv z) :
    ∃ t, ∀ F ≥ t, execStmt sunfish F ⟨w, env⟩ gxBind
      = .ok ⟨w, gxEnvAt env z⟩ .next := by
  obtain ⟨t, ht⟩ := hval
  refine ⟨t + 9, fun F hF => ?_⟩
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 9 := ⟨F - 9, by omega⟩
  exact gx_binds hp hm (ht (F' + 7) (by omega))

/-- **THE ROUND THAT KEEPS.** The move's value clears the QS floor, or the
search is not a QSearch: the binding runs, the branch is taken, and the round
emits the `(v, m)` pair the sort will order. -/
theorem gx_round_keeps (w : World) (env : REnv) (mv : RVal) (d z : Int)
    (b : String) (sc ep kp : Int) (wc0 wc1 bc0 bc1 : Bool)
    (hp : Env.lookup env "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hm : Env.lookup env "m" = some mv)
    (hd : Env.lookup env "depth" = some (.int d))
    (hnq : Env.lookup env "QS" = Option.none)
    (hval : ValueAnswers w (posOf b sc wc0 wc1 bc0 bc1 ep kp) mv z)
    (hpass : 40 ≤ z ∨ d ≠ 0) :
    GenEmits sunfish ⟨w, env⟩ [.block gxBody] [.tuple #[.int z, mv]]
      ⟨w, gxEnvAt env z⟩ := by
  obtain ⟨a, b', c, dd, ee, hplan⟩ := gxPlan_test
  have hv : Env.lookup (gxEnvAt env z) "v" = some (.int z) := by
    simp [gxEnvAt, Env.lookup_set_self]
  have hd' : Env.lookup (gxEnvAt env z) "depth" = some (.int d) := by
    simp [gxEnvAt, Env.lookup_set_ne, hd]
  have hnq' : Env.lookup (gxEnvAt env z) "QS" = Option.none := by
    simp [gxEnvAt, Env.lookup_set_ne, hnq]
  have hm' : Env.lookup (gxEnvAt env z) "m" = some mv := by
    simp [gxEnvAt, Env.lookup_set_ne, hm]
  -- the test's value, and it is truthy for whichever of the two reasons holds
  have htest : ∃ tv, EvalsTo sunfish ⟨w, gxEnvAt env z⟩
      (.boolOp .or #[.compare (.name "v" a) #[.gtE] #[.name "QS" b'] c,
        .name "depth" dd] ee) tv ∧ truthyH w.heap tv = .ok true := by
    by_cases hq : 40 ≤ z
    · exact ⟨.bool true, EvalsTo.of_eval (fuel := 5)
        (gx_filter_high w (gxEnvAt env z) z 0 a b' c dd ee hv hnq' hq), gx_keeps_high w⟩
    · have hd0 : d ≠ 0 := hpass.resolve_left hq
      exact ⟨.int d, EvalsTo.of_eval (fuel := 5)
        (gx_filter_low w (gxEnvAt env z) z d 0 a b' c dd ee hv hd' hnq' (by omega)),
        gx_keeps_deep w d hd0⟩
  obtain ⟨tv, htv, htruthy⟩ := htest
  -- statement 1 delegates, statement 2 branches into the yield
  have hsil1 : ∀ k : GenCont, GenSilent sunfish ⟨w, env⟩
      ([GenFrame.block gxBody] ++ k) ⟨w, gxEnvAt env z⟩ ([GenFrame.block [gxTest]] ++ k) := by
    intro k
    have h := genSilent_delegate (m := sunfish) (s := gxBind) (ss := [gxTest]) (k := k)
      (st := ⟨w, env⟩) (st₁ := ⟨w, gxEnvAt env z⟩) gxPlan_bind
      (gx_binds_at hp hm hval)
    simpa [gxBody_split] using h
  have hsil2 : ∀ k : GenCont, GenSilent sunfish ⟨w, gxEnvAt env z⟩
      ([GenFrame.block [gxTest]] ++ k) ⟨w, gxEnvAt env z⟩
      ([GenFrame.block [gxYield], GenFrame.block []] ++ k) := by
    intro k
    have h := genSilent_branch (m := sunfish) (s := gxTest) (ss := ([] : List Stmt))
      (k := k) (st := ⟨w, gxEnvAt env z⟩) (b := true) hplan htv htruthy
    simpa using h
  have hyield : ∀ k : GenCont, GenSteps sunfish ⟨w, gxEnvAt env z⟩
      ([GenFrame.block [gxYield]] ++ k)
      (some (.tuple #[.int z, mv], [GenFrame.block []] ++ k)) ⟨w, gxEnvAt env z⟩ := by
    intro k
    obtain ⟨y1, y2, y3, y4, hy⟩ := gxYield_lit
    have h := genSteps_yieldHere (m := sunfish) (st := ⟨w, gxEnvAt env z⟩) (s := gxYield)
      (ss := ([] : List Stmt)) (k := k) (v := .tuple #[.int z, mv])
      (by rw [hy]; rfl)
      (EvalsTo.of_eval (fuel := 6) (by py_simp [hv, hm']))
    simpa using h
  have hy : GenEmits sunfish ⟨w, gxEnvAt env z⟩ [.block [gxYield]]
      [.tuple #[.int z, mv]] ⟨w, gxEnvAt env z⟩ := by
    refine GenEmits.cons hyield ?_
    exact GenEmits.silent (pre₁ := ([] : GenCont))
      (fun k => by simpa using genSilent_blockNil (m := sunfish) (k := k)) GenEmits.nil
  refine GenEmits.silent hsil1 (GenEmits.silent hsil2 ?_)
  simpa using GenEmits.trans hy (ord_blockNil_emits ⟨w, gxEnvAt env z⟩)

/-- **THE ROUND THAT DROPS.** A sub-floor move at `depth = 0`: the binding still
runs — `Position.value` is called on every generated move, which is what makes
R1 a prerequisite of the whole line rather than of its surviving half — and the
branch is NOT taken, so nothing is emitted. -/
theorem gx_round_drops (w : World) (env : REnv) (mv : RVal) (z : Int)
    (b : String) (sc ep kp : Int) (wc0 wc1 bc0 bc1 : Bool)
    (hp : Env.lookup env "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hm : Env.lookup env "m" = some mv)
    (hd : Env.lookup env "depth" = some (.int 0))
    (hnq : Env.lookup env "QS" = Option.none)
    (hval : ValueAnswers w (posOf b sc wc0 wc1 bc0 bc1 ep kp) mv z)
    (hlow : z < 40) :
    GenEmits sunfish ⟨w, env⟩ [.block gxBody] [] ⟨w, gxEnvAt env z⟩ := by
  obtain ⟨a, b', c, dd, ee, hplan⟩ := gxPlan_test
  have hv : Env.lookup (gxEnvAt env z) "v" = some (.int z) := by
    simp [gxEnvAt, Env.lookup_set_self]
  have hd' : Env.lookup (gxEnvAt env z) "depth" = some (.int 0) := by
    simp [gxEnvAt, Env.lookup_set_ne, hd]
  have hnq' : Env.lookup (gxEnvAt env z) "QS" = Option.none := by
    simp [gxEnvAt, Env.lookup_set_ne, hnq]
  have hsil1 : ∀ k : GenCont, GenSilent sunfish ⟨w, env⟩
      ([GenFrame.block gxBody] ++ k) ⟨w, gxEnvAt env z⟩ ([GenFrame.block [gxTest]] ++ k) := by
    intro k
    have h := genSilent_delegate (m := sunfish) (s := gxBind) (ss := [gxTest]) (k := k)
      (st := ⟨w, env⟩) (st₁ := ⟨w, gxEnvAt env z⟩) gxPlan_bind
      (gx_binds_at hp hm hval)
    simpa [gxBody_split] using h
  have hsil2 : ∀ k : GenCont, GenSilent sunfish ⟨w, gxEnvAt env z⟩
      ([GenFrame.block [gxTest]] ++ k) ⟨w, gxEnvAt env z⟩
      ([GenFrame.block [], GenFrame.block []] ++ k) := by
    intro k
    have h := genSilent_branch (m := sunfish) (s := gxTest) (ss := ([] : List Stmt))
      (k := k) (st := ⟨w, gxEnvAt env z⟩) (b := false) hplan
      (EvalsTo.of_eval (fuel := 5)
        (gx_filter_low w (gxEnvAt env z) z 0 0 a b' c dd ee hv hd' hnq' hlow))
      (gx_drops_at_qs w)
    simpa using h
  refine GenEmits.silent hsil1 (GenEmits.silent hsil2 ?_)
  simpa using GenEmits.trans (ord_blockNil_emits ⟨w, gxEnvAt env z⟩)
    (ord_blockNil_emits ⟨w, gxEnvAt env z⟩)


/-! ### The ordering line, RUN — R2b's own statement on the live engine

`order_line_sorts` says the line evaluates to a fresh list holding `sortByLt`
of the drain. These guards run exactly that expression, in exactly the frame the
theorem quantifies over (`pos` a `Position`, `depth` an int, neither `sorted` nor
`<genexpr@1>` shadowed), on the shipped opening position. -/

private def fxOrd (F : Nat) (d : Int) : Option (Nat × Array RVal) :=
  match evalExpr sunfish F ⟨initWorld sunfish, [("pos", posH 0), ("depth", .int d)]⟩ ordLine with
  | .ok st (RVal.ref a) =>
    (match Heap.get? st.world.heap a with
     | some (Obj.list xs) => some (st.world.heap.size, xs)
     | _ => Option.none)
  | _ => Option.none

/-- The first component of a `(v, m)` row. -/
private def rowV : RVal → Int
  | RVal.tuple #[RVal.int v, _] => v
  | _ => -100000

/-! **The QS floor survives the sort**: two rows at `depth = 0`, twenty at
`depth = 3` — the same numbers §6 measured at the drain, now through `sorted`. -/
#guard (match fxOrd 512 0 with | some (_, xs) => xs.size == 2 | _ => false)
#guard (match fxOrd 512 3 with | some (_, xs) => xs.size == 20 | _ => false)

/-! **And it is DESCENDING**, which is `reverse=True` reaching `sortByLt true`
rather than a sort followed by a reversal. -/
#guard (match fxOrd 512 3 with
        | some (_, xs) =>
          (List.range (xs.size - 1)).all (fun k =>
            rowV (xs.getD (k + 1) RVal.none) ≤ rowV (xs.getD k RVal.none))
        | _ => false)

/-! **The allocation, end to end.** §6 measured the drain at 81 objects from a
heap of 68; the line starts from the live 66, allocates the two generators, drains,
and pushes ONE list — 66 + 2 + 81 + 1 = 150. -/
#guard (match fxOrd 512 3 with | some (h, _) => h == 150 | _ => false)

#print axioms ordFor_lit
#print axioms ordTarget_lit
#print axioms ordBody_split
#print axioms ordYield_lit
#print axioms ordLine_lit
#print axioms ordRevE_lit
#print axioms ordGxCall_lit
#print axioms ordGmCall_lit
#print axioms ordDepthE_lit
#print axioms ordPosE_lit
#print axioms ordFor_plan
#print axioms ordYield_plan
#print axioms gm_lit
#print axioms sorted_free
#print axioms gxName_free
#print axioms gm_plan
#print axioms order_line_sorts
#print axioms ord_assign
#print axioms ord_body_emits
#print axioms ord_blockNil_emits
#print axioms ord_loop_emits
#print axioms ord_stmt_emits
#print axioms gx_binds_at
#print axioms gx_round_keeps
#print axioms gx_round_drops

/-! ## §10 WHAT THE ORDERING LINE STILL OWES — one induction, shaped

R2b and R2c are closed and meet: `ord_stmt_emits` carries the shipped statement
from its source text to the stream it emits, with **one** hypothesis that is not
bookkeeping. That hypothesis is `hdrain`, and it is all of R2a that is left:

  `IterDrains sunfish (gxW w d pos) (w.heap.size + 1) vs w'`

— the genexp OBJECT, at the address the line allocated it at, drains to `vs`.

**Everything under it is proved.** `gx_round_keeps` and `gx_round_drops` are the
body at a kept and at a dropped move, `gx_call` is the object's creation, and R1's
four `value_runs_*` theorems discharge `ValueAnswers`. What is missing is the
CHAIN, and its three premises are these, in computed shape:

1. **Per-round `IterSteps` on the INNER generator. LANDED (2026-08-22).**
   `GenEmits.forGenRound` takes `IterSteps sunfish st.world (w.heap.size)
   (some mv) w₁` — one step of `pos.gen_moves()`'s object, at the world the round
   starts from. What existed was `gen_moves_drains_ref` (§L8), a WHOLE drain.
   `IterDrains.cons` builds a drain from steps; the inverses `IterDrains.uncons`
   and `IterDrains.exhausts` (VCGen.lean §L6) read one back OUT, and
   `gen_moves_iterDrains` (genmoves_drain.lean) is the rename that lets them
   apply. `IterDrains` is a threshold DEFINITION, not an inductive, so those
   inverses are theorems rather than a `cases` — which is why nobody had them.
2. **The per-round world — and this premise was WRONG as written.** It said *"the
   yield allocates the pair — so the round's world moves by exactly the tuple"*.
   **A tuple is an immediate value and allocates nothing.** What the round's world
   actually moves by is the INNER STEP's own allocation, measured in
   genmoves_drain.lean as **1 to 25 objects per step**, non-uniform, because a
   step runs however much of the board scan the next move needs. The 81 objects §6
   measured for the whole drain are ALL the inner generator's; the genexp
   contributes none. So the chain must thread the inner step's world OPAQUELY —
   which is exactly what `uncons` hands over — rather than compute it. The repair
   costs nothing because the inverse was going to be existential anyway; the
   record needed correcting all the same.
3. **The invariant across rounds.** `gxEnvAt env z` is `Env.set env "v" _`, so the
   frame's SHAPE is stable and the next round's premises are the previous round's
   with one `Env.set` in front — the same "assign_again" step `moves_loop_cuts`
   needs, and `Env.lookup_set_ne` is the whole of it.

**Price, re-quoted after the fact.** The step-indexed reading was priced at one
session and cost two theorems and a rename — `IterDrains.uncons`/`.exhausts` are
fifteen lines each and go through a single fuel, because neither side has to
agree on a threshold. What is LEFT is the chain: `GenEmits.forGenRound` iterated
with `GenEmits.forGenDone` at the end, the induction running on the reference
move list `gen_moves_iterDrains` now hands over as a judgment. There is no
`forGenRounds` batch lemma because, as VCGen.lean's own note says, an infinite
inner generator has no remainder list to induct on; here it is finite, so the
caller's induction is the one to write.

**And R3 is not blocked on this.** `ord_stmt_emits` is stated over a free `vs`,
so the fold's schedule can be chosen against it now: what the fold consumes is a
list of `(value, Move)` pairs in descending order, and that is exactly what this
theorem hands over.

**§11 below is the chain, landed** — so `hdrain` is discharged from a run of the
inner generator, and what remains is named there rather than here. -/



/-! ## §11 THE CHAIN — R2 CLOSES, and `hdrain` is discharged (2026-08-22)

§10 named one induction and priced it. This is it. `GenEmits.forGenRound`
iterated, `forGenDone` at the end, and the induction is the CALLER's — which is
what VCGen's own note says it must be, because a `forGenRounds` batch lemma
cannot exist for a generator that might be infinite. Here it is finite, and the
finiteness lives in the run.

### What the chain is stated over

`GxRun` is the genexp's walk of the inner generator, world-threaded: each round
takes one `IterSteps` on `pos.gen_moves()`' object — a **non-uniform** world
move, 1 to 25 objects, measured in genmoves_drain.lean — and then either KEEPS
the pair (`gx_round_keeps`) or DROPS it (`gx_round_drops`). The intermediate
worlds are existential in the relation for the reason the census gave: nothing
computes them.

`GxFrame` is the three slots every round reads (`pos`, `depth`, `QS`), and the
two `Env.set`s a round performs — `m` from the loop, `v` from the binding —
disturb none of them. That is §10's premise 3, and it is two lines rather than
the "assign_again" step it was priced as.

### The pieces

| declaration | |
|---|---|
| `GxRun` | the run: per-round inner step, then keep or drop |
| `gx_chain` | `forGenRound` iterated — the induction, on the run |
| `gx_drains` | the chain entered (`genSilent_forHereGen`) and closed (`toYields`, `IterDrains.of_genYields`): the genexp OBJECT drains |
| `ord_stmt_emits_run` | **R2's statement with `hdrain` discharged** |

`IterDrains.uncons`/`.exhausts` (§L58) are what let a whole-drain agreement feed
a round-by-round loop, and `gen_moves_iterDrains` is the rename that makes them
applicable to the shipped generator.

### What is STILL owed, named exactly

`gx_drains` takes a `GxRun`. Building one from `gen_moves_iterDrains`' drain is
`uncons` applied down the reference move list — mechanical — except for one
premise per round: **`ValueAnswers` at THAT round's world.** `Position.value` is
heap-free (R1, measured) but its answer is stated at a world, and the round's
world is whatever the inner step left. So the missing step is a FRAME condition:
*the inner generator's steps preserve the `pst` slot.* The census says they only
ever grow the heap — 67 → 69 → 70 → … → 148, monotone, never a shrink or an
in-place write outside the generator's own slot — so it is true and measurable;
it is simply not derivable from `IterSteps` alone, which says nothing about what
a step does to slots it did not touch.

That is one lemma about `Position.gen_moves`' stepper, and it is genmoves-side
material. With it, `GxRun` is produced by an induction on the reference list and
R2's `vs` becomes the concrete twenty pairs the fixture guards below already
show. -/

/-- The three frame slots every genexp round reads. `m` and `v` are written by
the loop and the binding; neither disturbs these. -/
def GxFrame (env : REnv) (pos : RVal) (d : Int) : Prop :=
  Env.lookup env "pos" = some pos ∧
  Env.lookup env "depth" = some (.int d) ∧
  Env.lookup env "QS" = Option.none

theorem GxFrame.set_m {env pos d} (h : GxFrame env pos d) (mv : RVal) :
    GxFrame (Env.set env "m" mv) pos d :=
  ⟨by simp [Env.lookup_set_ne, h.1], by simp [Env.lookup_set_ne, h.2.1],
   by simp [Env.lookup_set_ne, h.2.2]⟩

theorem GxFrame.set_v {env pos d} (h : GxFrame env pos d) (z : Int) :
    GxFrame (gxEnvAt env z) pos d :=
  ⟨by simp [gxEnvAt, Env.lookup_set_ne, h.1], by simp [gxEnvAt, Env.lookup_set_ne, h.2.1],
   by simp [gxEnvAt, Env.lookup_set_ne, h.2.2]⟩

/-- **The genexp's run over the inner generator**, world-threaded: each round
steps the inner object (a NON-uniform world move — genmoves_drain.lean's census)
and either keeps the pair or drops it. -/
inductive GxRun (pos : RVal) (d : Int) (a : Addr) :
    World → List RVal → List RVal → World → Prop
  | done {w w'} : IterSteps sunfish w a Option.none w' → GxRun pos d a w [] [] w'
  | keep {w w₁ w₂ : World} {mv : RVal} {z : Int} {ms vs : List RVal} :
      IterSteps sunfish w a (some mv) w₁ →
      ValueAnswers w₁ pos mv z → (40 ≤ z ∨ d ≠ 0) →
      GxRun pos d a w₁ ms vs w₂ →
      GxRun pos d a w (mv :: ms) (.tuple #[.int z, mv] :: vs) w₂
  | drop {w w₁ w₂ : World} {mv : RVal} {z : Int} {ms vs : List RVal} :
      IterSteps sunfish w a (some mv) w₁ →
      ValueAnswers w₁ pos mv z → z < 40 → d = 0 →
      GxRun pos d a w₁ ms vs w₂ →
      GxRun pos d a w (mv :: ms) vs w₂

/-- **THE CHAIN.** `GenEmits.forGenRound` iterated, `forGenDone` at the end, the
induction on the run — which is the caller's, exactly as VCGen's note says it
must be for a generator whose remainder list is finite. -/
theorem gx_chain {d : Int} {a : Addr} {b : String} {sc ep kp : Int}
    {wc0 wc1 bc0 bc1 : Bool} (sp : Span) :
    ∀ {w w' : World} {ms vs : List RVal},
      GxRun (posOf b sc wc0 wc1 bc0 bc1 ep kp) d a w ms vs w' →
      ∀ env : REnv, GxFrame env (posOf b sc wc0 wc1 bc0 bc1 ep kp) d →
      ∃ env', GenEmits sunfish ⟨w, env⟩ [.forGen (.name "m" sp) a gxBody] vs
        ⟨w', env'⟩ := by
  intro w w' ms vs hrun
  induction hrun with
  | done hstep => intro env _; exact ⟨env, GenEmits.forGenDone hstep⟩
  | @keep w w₁ w₂ mv z ms vs hstep hval hpass hrest ih =>
      intro env hfr
      obtain ⟨env', hem⟩ := ih (gxEnvAt (Env.set env "m" mv) z)
        ((hfr.set_m mv).set_v z)
      refine ⟨env', ?_⟩
      have hbody := gx_round_keeps w₁ (Env.set env "m" mv) mv d z b sc ep kp
        wc0 wc1 bc0 bc1
        (by simp [Env.lookup_set_ne, hfr.1]) (by simp [Env.lookup_set_self])
        (by simp [Env.lookup_set_ne, hfr.2.1]) (by simp [Env.lookup_set_ne, hfr.2.2])
        hval hpass
      simpa using GenEmits.forGenRound (m := sunfish) (target := .name "m" sp) (a := a)
        (st := ⟨w, env⟩) (w' := w₁) (env₁ := Env.set env "m" mv) (v := mv)
        hstep rfl hbody hem
  | @drop w w₁ w₂ mv z ms vs hstep hval hlow hd0 hrest ih =>
      intro env hfr
      obtain ⟨env', hem⟩ := ih (gxEnvAt (Env.set env "m" mv) z)
        ((hfr.set_m mv).set_v z)
      refine ⟨env', ?_⟩
      have hbody := gx_round_drops w₁ (Env.set env "m" mv) mv z b sc ep kp
        wc0 wc1 bc0 bc1
        (by simp [Env.lookup_set_ne, hfr.1]) (by simp [Env.lookup_set_self])
        (by simp [Env.lookup_set_ne, hd0 ▸ hfr.2.1]) (by simp [Env.lookup_set_ne, hfr.2.2])
        hval hlow
      simpa using GenEmits.forGenRound (m := sunfish) (target := .name "m" sp) (a := a)
        (st := ⟨w, env⟩) (w' := w₁) (env₁ := Env.set env "m" mv) (v := mv)
        hstep rfl hbody hem

/-- **THE GENEXP OBJECT DRAINS** — the chain, entered and closed. -/
theorem gx_drains (w : World) (d : Int) (b : String) (sc ep kp : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ms vs : List RVal) (h₁ : Heap) (wend : World)
    (iq : String) (il : REnv) (ic : GenCont) (ist : GenStatus)
    (hupd : Heap.update (gxW w d (posOf b sc wc0 wc1 bc0 bc1 ep kp)).heap (w.heap.size + 1)
        (.generator "<genexpr@1>" (gxEnv (.ref w.heap.size) d (posOf b sc wc0 wc1 bc0 bc1 ep kp))
          [.block gxB] .running) = some h₁)
    (hinner : Heap.get? h₁ w.heap.size = some (.generator iq il ic ist))
    (hgx : GxRun (posOf b sc wc0 wc1 bc0 bc1 ep kp) d w.heap.size
      { (gxW w d (posOf b sc wc0 wc1 bc0 bc1 ep kp)) with heap := h₁ } ms vs wend) :
    ∃ w', IterDrains sunfish (gxW w d (posOf b sc wc0 wc1 bc0 bc1 ep kp))
      (w.heap.size + 1) vs w' := by
  obtain ⟨a', b', hfor⟩ := gxPlan_for
  have hfr : GxFrame (gxEnv (.ref w.heap.size) d (posOf b sc wc0 wc1 bc0 bc1 ep kp))
      (posOf b sc wc0 wc1 bc0 bc1 ep kp) d := ⟨rfl, rfl, rfl⟩
  obtain ⟨envF, hem⟩ := gx_chain (b := b) (sc := sc) (ep := ep) (kp := kp)
    (wc0 := wc0) (wc1 := wc1) (bc0 := bc0) (bc1 := bc1) a' hgx
    (gxEnv (.ref w.heap.size) d (posOf b sc wc0 wc1 bc0 bc1 ep kp)) hfr
  refine IterDrains.of_genYields vs _
    (gxEnv (.ref w.heap.size) d (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    [.block gxB] .created h₁ ⟨wend, envF⟩ ?_ (Or.inl rfl) hupd ?_
  · simpa [gxW, gxObj3, genObj, gxCallEnv, gxF_lit.2.2.2.2.2.1] using
      Heap.get?_push_size (w.heap.push (gmObj (posOf b sc wc0 wc1 bc0 bc1 ep kp)))
        (gxObj3 w.heap.size d (posOf b sc wc0 wc1 bc0 bc1 ep kp))
  · refine GenEmits.toYields ?_
    refine GenEmits.silent
      (pre₁ := [GenFrame.forGen (.name "m" a') w.heap.size gxBody,
                GenFrame.block ([] : List Stmt)])
      (fun k => by
        simpa [gxB_split] using genSilent_forHereGen (m := sunfish) (s := gxFor)
          (ss := ([] : List Stmt)) (k := k) hfor
          (EvalsIn.of_evalsTo (EvalsTo.of_eval (fuel := 4) (by py_simp [gxEnv])))
          hinner) ?_
    simpa using GenEmits.trans hem (ord_blockNil_emits ⟨wend, envF⟩)

/-- **R2 CLOSES.** `ord_stmt_emits` with `hdrain` DISCHARGED: the statement's
emitted stream, from a run of the inner generator rather than from an assumption
about the genexp object. -/
theorem ord_stmt_emits_run (w : World) (env : REnv) (d : Int)
    (b : String) (sc ep kp : Int) (wc0 wc1 bc0 bc1 : Bool)
    (ms vs sortedVs : List RVal) (h₁ : Heap) (wend : World)
    (iq : String) (il : REnv) (ic : GenCont) (ist : GenStatus)
    (hpos : Env.lookup env "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hdepth : Env.lookup env "depth" = some (.int d))
    (hsorted : Env.lookup env "sorted" = Option.none)
    (hgxl : Env.lookup env "<genexpr@1>" = Option.none)
    (hupd : Heap.update (gxW w d (posOf b sc wc0 wc1 bc0 bc1 ep kp)).heap (w.heap.size + 1)
        (.generator "<genexpr@1>" (gxEnv (.ref w.heap.size) d (posOf b sc wc0 wc1 bc0 bc1 ep kp))
          [.block gxB] .running) = some h₁)
    (hinner : Heap.get? h₁ w.heap.size = some (.generator iq il ic ist))
    (hgx : GxRun (posOf b sc wc0 wc1 bc0 bc1 ep kp) d w.heap.size
      { (gxW w d (posOf b sc wc0 wc1 bc0 bc1 ep kp)) with heap := h₁ } ms vs wend)
    (hsort : sortByLt true vs = .ok sortedVs) :
    ∃ w' env', GenEmits sunfish ⟨w, env⟩ [.block [ordFor]] sortedVs
      ⟨ordW w' sortedVs, env'⟩ := by
  obtain ⟨w', hdrain⟩ := gx_drains w d b sc ep kp wc0 wc1 bc0 bc1 ms vs h₁ wend
    iq il ic ist hupd hinner hgx
  obtain ⟨env', hem⟩ := ord_stmt_emits w env d b sc ep kp wc0 wc1 bc0 bc1 vs sortedVs w'
    hpos hdepth hsorted hgxl hdrain hsort
  exact ⟨w', env', hem⟩

#print axioms gx_chain
#print axioms gx_drains
#print axioms ord_stmt_emits_run

end Examples.python.sunfish.order_genexp
