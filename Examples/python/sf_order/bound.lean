/-
**`bound_probe`'s own fold, on the shipped program** — the consumer half of
§L8's two-part remainder (docs/backlog.md §L9).

`Examples/python/sf_order/proof.lean` (§L8) proved the three constructs the
`bound_probe` collapse was blocked behind and then measured what was left:

1. the ordering line's CONTENT (`hdrain` — what the lowered genexp yields), and
2. **`bound_probe`'s OWN loop** — the `best`/`searched` fold over `moves()`
   with the OUTER cutoff `if best >= gamma: break`.

This file is (2), and it is not blocked on (1): the fold is a theorem about
what the loop does to *whatever* the generator hands over. So the object's
output is a HYPOTHESIS here (`Hands` — a schedule of `IterSteps`), exactly as
`moves_loop_cuts` takes the ordered rows as a hypothesis, and the theorem says
what `bound_probe` ANSWERS as a function of it.

The three gates:

* **`bound_loop_folds`** (§3) — the shipped `for val, i, j in moves():` with
  its body, over the generator the shipped `def moves():` allocates: the loop
  consumes the yields one at a time, counts them in `searched`, keeps the
  running maximum in `best`, and STOPS at the first yield that lifts `best` to
  `gamma`. Both arms in one statement (`probe`'s third component says which
  fired), yields free, window free, and the tail beyond the cutting yield is
  not constrained at all. `moves_call_creates` (§L8 gate 3b) is what turns the
  iterable into the object, so the gate composes rather than restates.
* **`bound_tail_returns`** (§4) — that loop and `return (best, searched)`.
* **`bound_probe_answers`** (§5) — **the whole shipped function**, from the
  public boundary: `Position(...)`, `val_lower = QS - depth * QS_A`, the nested
  `def` (§L8 gate 3a), the two accumulators, the loop and the return. A
  `CallsTo` on the RAW `sf_order` module whose only hypothesis is the yield
  schedule of the generator the function itself allocates.

Nothing is retyped: every piece of program is PROJECTED out of `sf_order` and
`rfl`-pinned, so a changed program stops these theorems loudly.

**On the module-literal transport, measured.** §L8 recorded the ordering
line's content as needing `gen_moves_drains_ref` (the `sunfish` lane's drain
theorem) transported to `sf_order`'s module literal, "sf_order's method body
being the same text". *It is not the same text* —
`Examples/python/sf_order/transport.lean` exhibits the difference — so there is
no transport to make, parametric or re-run. §6 states the price of the two
routes as measured, and the honest remainder.
-/
import Examples.python.sf_order.proof

namespace Examples.python.sf_order.bound

open LeanModels LeanModels.Python
open Examples.python.sf_order.proof

set_option maxRecDepth 100000

/-! ## §0 The program, projected

`bound_probe`'s eight statements, each read out of `sf_order` and pinned by
`rfl` (`bpB`/`bpDef`/`bpFor` are `proof.lean`'s own projections). -/

/-- The docstring — an expression statement. -/
def bpDoc : Stmt := nth 0 bpB
/-- `pos = Position(board, 0, (True, True), (True, True), ep, kp)`. -/
def bpPos : Stmt := nth 1 bpB
/-- `val_lower = QS - depth * QS_A`. -/
def bpVL : Stmt := nth 2 bpB
/-- `best = -100000`. -/
def bpBest : Stmt := nth 4 bpB
/-- `searched = 0`. -/
def bpSearched : Stmt := nth 5 bpB
/-- `return (best, searched)`. -/
def bpRet : Stmt := nth 7 bpB
/-- The outer loop's target, `(val, i, j)`. -/
def bpTarget : Expr :=
  match bpFor with | .forStmt t _ _ _ _ => t | _ => .constant .none nowhere
/-- The outer loop's body — three statements. -/
def bpBody : List Stmt :=
  match bpFor with | .forStmt _ _ b _ _ => b.toList | _ => []
/-- `searched = searched + 1`. -/
def bpBump : Stmt := nth 0 bpBody
/-- `if val > best: best = val`. -/
def bpMax : Stmt := nth 1 bpBody
/-- `if best >= gamma: break` — the OUTER beta cutoff. -/
def bpCut : Stmt := nth 2 bpBody

theorem bpB_split : bpB =
    [bpDoc, bpPos, bpVL, bpDef, bpBest, bpSearched, bpFor, bpRet] := rfl
theorem bpBody_split : bpBody = [bpBump, bpMax, bpCut] := rfl

theorem bpFor_lit : ∃ sp, bpFor = .forStmt bpTarget movesCall bpBody.toArray #[] sp :=
  ⟨_, rfl⟩
theorem bpTarget_lit : ∃ s₁ s₂ s₃ s₄, bpTarget =
    .tuple #[.name "val" s₁, .name "i" s₂, .name "j" s₃] s₄ := ⟨_, _, _, _, rfl⟩
theorem bpBump_lit : ∃ s₁ s₂ s₃ s₄ s₅, bpBump =
    .assign #[.name "searched" s₁]
      (.binOp (.name "searched" s₂) .add (.constant (.int 1) s₃) s₄) s₅ :=
  ⟨_, _, _, _, _, rfl⟩
theorem bpMax_lit : ∃ s₁ s₂ s₃ s₄ s₅ s₆ s₇, bpMax =
    .ifStmt (.compare (.name "val" s₁) #[.gt] #[.name "best" s₂] s₃)
      #[.assign #[.name "best" s₄] (.name "val" s₅) s₆] #[] s₇ :=
  ⟨_, _, _, _, _, _, _, rfl⟩
theorem bpCut_lit : ∃ s₁ s₂ s₃ s₄ s₅, bpCut =
    .ifStmt (.compare (.name "best" s₁) #[.gtE] #[.name "gamma" s₂] s₃)
      #[.brk s₄] #[] s₅ := ⟨_, _, _, _, _, rfl⟩
theorem bpDoc_lit : ∃ (c : String) (s₁ s₂ : Span),
    bpDoc = .exprStmt (.constant (.str c) s₁) s₂ := ⟨_, _, _, rfl⟩
theorem bpPos_lit : ∃ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ s₁₄, bpPos =
    .assign #[.name "pos" s₁]
      (.call (.name "Position" s₂)
        #[.name "board" s₃, .constant (.int 0) s₄,
          .tuple #[.constant (.bool true) s₅, .constant (.bool true) s₆] s₇,
          .tuple #[.constant (.bool true) s₈, .constant (.bool true) s₉] s₁₀,
          .name "ep" s₁₁, .name "kp" s₁₂] #[] Option.none s₁₃) s₁₄ :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
theorem bpVL_lit : ∃ s₁ s₂ s₃ s₄ s₅ s₆ s₇, bpVL =
    .assign #[.name "val_lower" s₁]
      (.binOp (.name "QS" s₂) .sub
        (.binOp (.name "depth" s₃) .mult (.name "QS_A" s₄) s₅) s₆) s₇ :=
  ⟨_, _, _, _, _, _, _, rfl⟩
theorem bpBest_lit : ∃ s₁ s₂ s₃ s₄, bpBest =
    .assign #[.name "best" s₁] (.unaryOp .usub (.constant (.int 100000) s₂) s₃) s₄ :=
  ⟨_, _, _, _, rfl⟩
theorem bpSearched_lit : ∃ s₁ s₂ s₃, bpSearched =
    .assign #[.name "searched" s₁] (.constant (.int 0) s₂) s₃ := ⟨_, _, _, rfl⟩
theorem bpRet_lit : ∃ s₁ s₂ s₃ s₄, bpRet =
    .ret (some (.tuple #[.name "best" s₁, .name "searched" s₂] s₃)) s₄ :=
  ⟨_, _, _, _, rfl⟩

/-! ## §1 The vocabulary

What the generator hands over, what the loop does with it, and the three frame
slots the loop reads. -/

/-- One yield of `moves()`: the shipped `yield (val, move.i, move.j)`. -/
structure Triple where
  /-- The move's ordering value. -/
  val : Int
  /-- The move's from-square. -/
  i : Int
  /-- The move's to-square. -/
  j : Int
deriving Inhabited

/-- The triple as the interpreter's value. `proof.lean`'s `rowTriple` is this
at a `Row`, definitionally (`rowTriple_eq`). -/
def tripleVal (t : Triple) : RVal := .tuple #[.int t.val, .int t.i, .int t.j]

/-- The bridge to §L8's rows: what `moves`' inner loop emits for a kept row IS
what `bound_probe`'s loop consumes. -/
theorem rowTriple_eq (r : Row) : rowTriple r = tripleVal ⟨r.val, r.i, r.j⟩ := rfl

/-- `if val > best: best = val`, spec-side. -/
def bump (best : Int) (t : Triple) : Int := if best < t.val then t.val else best

/-- **The walk `bound_probe`'s loop performs.** Count the yield, raise `best`
if the yield beats it, and STOP at the first yield that lifts `best` to
`gamma`: `.1` is the `best` it ends with, `.2.1` the `searched` it ends with,
`.2.2` whether it CUT (`true`) rather than running the generator out. -/
def probe (gamma : Int) : Int → List Triple → Int × Int × Bool
  | best, [] => (best, 0, false)
  | best, t :: ts =>
      if gamma ≤ bump best t then (bump best t, 1, true)
      else ((probe gamma (bump best t) ts).1,
            (probe gamma (bump best t) ts).2.1 + 1,
            (probe gamma (bump best t) ts).2.2)

/-- The same walk with the counter already at `n` — the loop invariant's
handle on "what the rounds still to come will answer". -/
def probeFrom (gamma best n : Int) (ts : List Triple) : Int × Int × Bool :=
  ((probe gamma best ts).1, (probe gamma best ts).2.1 + n, (probe gamma best ts).2.2)

theorem probeFrom_zero (gamma best : Int) (ts : List Triple) :
    probeFrom gamma best 0 ts = probe gamma best ts := by
  simp [probeFrom]

theorem probeFrom_nil (gamma best n : Int) :
    probeFrom gamma best n [] = (best, n, false) := by
  simp [probeFrom, probe]

theorem probeFrom_cons_next (gamma best n : Int) (t : Triple) (ts : List Triple)
    (h : ¬ gamma ≤ bump best t) :
    probeFrom gamma best n (t :: ts) = probeFrom gamma (bump best t) (n + 1) ts := by
  simp [probeFrom, probe, h] <;> omega

theorem probeFrom_cons_cut (gamma best n : Int) (t : Triple) (ts : List Triple)
    (h : gamma ≤ bump best t) :
    probeFrom gamma best n (t :: ts) = (bump best t, n + 1, true) := by
  simp [probeFrom, probe, h] <;> omega

/-- **The object's yield schedule**: stepping the generator at `a` from world
`w` hands over exactly `ts`, one `IterSteps` at a time, and lands at `w'`.

Nothing whatever is claimed about the object past `w'`, which is where the
laziness lives: a consumer that abandons the generator mid-drain constrains
only the prefix it actually consumed. -/
inductive Hands (m : Module) (a : Addr) : World → List Triple → World → Prop
  /-- The empty schedule: no step taken, the world is where it was. -/
  | nil {w : World} : Hands m a w [] w
  /-- One yield, then the rest. -/
  | cons {w w₁ w₂ : World} {t : Triple} {ts : List Triple} :
      IterSteps m w a (some (tripleVal t)) w₁ → Hands m a w₁ ts w₂ →
      Hands m a w (t :: ts) w₂

/-- The three frame slots the loop reads, as LOOKUPS — so every theorem below
is blind to the rest of the frame, and composes with whatever the statements
above the loop left there. -/
def LoopFrame (e : REnv) (gamma best searched : Int) : Prop :=
  Env.lookup e "gamma" = some (.int gamma) ∧
  Env.lookup e "best" = some (.int best) ∧
  Env.lookup e "searched" = some (.int searched)

/-- The frame with the loop target bound to a yield. -/
def bindTriple (e : REnv) (t : Triple) : REnv :=
  Env.set (Env.set (Env.set e "val" (.int t.val)) "i" (.int t.i)) "j" (.int t.j)

/-- Binding `(val, i, j)` — an `rfl` on the projected target. -/
theorem bind_eq (h : Heap) (e : REnv) (t : Triple) :
    assignToH h e bpTarget (tripleVal t) = .ok (bindTriple e t) := rfl

theorem lookup_bind_val (e : REnv) (t : Triple) :
    Env.lookup (bindTriple e t) "val" = some (.int t.val) := by
  simp [bindTriple, Env.lookup_set_self, Env.lookup_set_ne]

theorem lookup_bind_ne {e : REnv} {x : String} {v : RVal} (t : Triple)
    (hx : x ≠ "val") (hi : x ≠ "i") (hj : x ≠ "j") (h : Env.lookup e x = some v) :
    Env.lookup (bindTriple e t) x = some v := by
  simp [bindTriple, Env.lookup_set_ne, hx, hi, hj, h]

/-! ## §2 One round of the loop body

`searched = searched + 1`, then the maximum, then the cutoff — with the flow
the cutoff decides. -/

/-- **The body at one yield.** The counter goes up, `best` becomes the running
maximum, and the run BREAKS exactly when the new `best` has reached `gamma`.
The world is untouched: the body of `bound_probe`'s loop allocates nothing. -/
theorem round (w : World) (e : REnv) (gamma best n : Int) (t : Triple)
    (hf : LoopFrame e gamma best n) :
    ∃ e', execStmts sf_order 24 ⟨w, bindTriple e t⟩ bpBody
        = .ok ⟨w, e'⟩ (if gamma ≤ bump best t then .brk else .next)
      ∧ LoopFrame e' gamma (bump best t) (n + 1) := by
  obtain ⟨hg, hb, hs⟩ := hf
  obtain ⟨a₁, a₂, a₃, a₄, a₅, hbump⟩ := bpBump_lit
  obtain ⟨b₁, b₂, b₃, b₄, b₅, b₆, b₇, hmaxs⟩ := bpMax_lit
  obtain ⟨c₁, c₂, c₃, c₄, c₅, hcuts⟩ := bpCut_lit
  have hg' := lookup_bind_ne t (by decide) (by decide) (by decide) hg
  have hb' := lookup_bind_ne t (by decide) (by decide) (by decide) hb
  have hs' := lookup_bind_ne t (by decide) (by decide) (by decide) hs
  by_cases hmax : best < t.val
  · refine ⟨Env.set (Env.set (bindTriple e t) "searched" (.int (n + 1))) "best"
      (.int t.val), ?_, ?_, ?_, ?_⟩
    · by_cases hcut : gamma ≤ t.val <;>
        rw [bpBody_split, hbump, hmaxs, hcuts] <;>
        py_simp [hg', hb', hs', lookup_bind_val, bump, hmax, hcut,
          Env.lookup_set_self, Env.lookup_set_ne]
    · simp [Env.lookup_set_ne, hg']
    · simp [bump, hmax, Env.lookup_set_self]
    · simp [Env.lookup_set_ne, Env.lookup_set_self]
  · refine ⟨Env.set (bindTriple e t) "searched" (.int (n + 1)), ?_, ?_, ?_, ?_⟩
    · by_cases hcut : gamma ≤ best <;>
        rw [bpBody_split, hbump, hmaxs, hcuts] <;>
        py_simp [hg', hb', hs', lookup_bind_val, bump, hmax, hcut,
          Env.lookup_set_self, Env.lookup_set_ne]
    · simp [Env.lookup_set_ne, hg']
    · simp [bump, hmax, Env.lookup_set_ne, hb']
    · simp [Env.lookup_set_self]

/-! ## §3 The loop -/

/-- **GATE 1 — the shipped `for val, i, j in moves():` folds and cuts.**

In a frame that binds `moves` to the closure the shipped `def` allocated, the
loop CALLS it (allocating the generator — §L8 gate 3b), then consumes the
yields the object hands over: each one counted in `searched`, `best` kept as
the running maximum, and the loop ABANDONED at the first yield that lifts
`best` to `gamma`.

Yields free, window free, count free. `probe`'s third component says which arm
fired, and `hdone` is asked for only in the arm that needs it: the generator is
required to report exhaustion exactly when the walk runs out of yields. When
the cutoff fires first, nothing at all is assumed about the object past the
cutting yield — the laziness is the content of the statement. -/
theorem bound_loop_folds (w : World) (e : REnv) (ad : Addr)
    (d : Int) (pv : RVal) (vl gamma b0 : Int) (ts : List Triple) (wEnd : World)
    (hmoves : Env.lookup e "moves" = some (.ref ad))
    (hclos : Heap.get? w.heap ad = some (movesClosure d pv vl))
    (hframe : LoopFrame e gamma b0 0)
    (hands : Hands sf_order w.heap.size
      { w with heap := w.heap.push (movesGen d pv vl) } ts wEnd)
    (hdone : (probe gamma b0 ts).2.2 = false →
      ∃ w'', IterSteps sf_order wEnd w.heap.size Option.none w'') :
    PyStmtTriple sf_order (fun st => st = ⟨w, e⟩) bpFor
      (.ofNext fun st => LoopFrame st.locals gamma
        (probe gamma b0 ts).1 (probe gamma b0 ts).2.1) := by
  obtain ⟨sp, hfor⟩ := bpFor_lit
  rw [hfor]
  refine PyStmtTriple.forGen (α := Triple) (a := w.heap.size) tripleVal
    (fun rest st => ∃ best n, LoopFrame st.locals gamma best n ∧
      Hands sf_order w.heap.size st.world rest wEnd ∧
      probeFrom gamma best n rest = probe gamma b0 ts) ts rfl ?_ ?_ ?_
  · rintro st rfl
    refine ⟨⟨{ w with heap := w.heap.push (movesGen d pv vl) }, e⟩,
      "<closure:moves>", movesCap d pv vl, [.block mvB], .created,
      moves_call_creates w e ad d pv vl hmoves hclos, ?_, b0, 0, hframe, hands, ?_⟩
    · rw [← movesGen_eq d pv vl]; exact Heap.get?_push_size _ _
    · exact probeFrom_zero gamma b0 ts
  · rintro st ⟨best, n, hlf, hh, hp⟩
    cases hh with
    | @nil _ =>
      rw [probeFrom_nil] at hp
      obtain ⟨w'', hit⟩ := hdone (by rw [← hp])
      exact ⟨w'', hit, by rw [← hp] at *; exact hlf⟩
  · rintro x rest st ⟨best, n, hlf, hh, hp⟩
    cases hh with
    | @cons _ w₁ _ _ _ hstep hrest =>
      obtain ⟨e', hrun, hlf'⟩ := round w₁ st.locals gamma best n x hlf
      refine ⟨w₁, bindTriple st.locals x, hstep, bind_eq w₁.heap st.locals x, ?_⟩
      refine PyTriple.of_exec ?_
      rintro st' rfl
      refine ⟨24, ?_⟩
      by_cases hcut : gamma ≤ bump best x
      · rw [probeFrom_cons_cut gamma best n x rest hcut] at hp
        simp only [hcut, if_true] at hrun
        rw [hrun]
        simpa [PyPost.ofNext, ← hp] using hlf'
      · rw [probeFrom_cons_next gamma best n x rest hcut] at hp
        simp only [hcut, if_false] at hrun
        rw [hrun]
        exact ⟨bump best x, n + 1, hlf', hrest, hp⟩

/-! ## §4 The loop and the return -/

/-- **GATE 2 — the loop and `return (best, searched)`.** The pair the shipped
function hands back IS the walk's answer. -/
theorem bound_tail_returns (w : World) (e : REnv) (ad : Addr)
    (d : Int) (pv : RVal) (vl gamma b0 : Int) (ts : List Triple) (wEnd : World)
    (hmoves : Env.lookup e "moves" = some (.ref ad))
    (hclos : Heap.get? w.heap ad = some (movesClosure d pv vl))
    (hframe : LoopFrame e gamma b0 0)
    (hands : Hands sf_order w.heap.size
      { w with heap := w.heap.push (movesGen d pv vl) } ts wEnd)
    (hdone : (probe gamma b0 ts).2.2 = false →
      ∃ w'', IterSteps sf_order wEnd w.heap.size Option.none w'') :
    PyTriple sf_order (fun st => st = ⟨w, e⟩) [bpFor, bpRet]
      (.ofRet fun rv _ => rv =
        .tuple #[.int (probe gamma b0 ts).1, .int (probe gamma b0 ts).2.1]) := by
  obtain ⟨r₁, r₂, r₃, r₄, hret⟩ := bpRet_lit
  refine PyTriple.seq (R := fun st => LoopFrame st.locals gamma
    (probe gamma b0 ts).1 (probe gamma b0 ts).2.1) ?_ ?_
  · exact (bound_loop_folds w e ad d pv vl gamma b0 ts wEnd hmoves hclos hframe
      hands hdone).consequence (fun _ h => h)
      ⟨fun _ h => h, fun _ _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim,
        fun _ _ h => h.elim⟩
  · refine PyTriple.single ?_
    rw [hret]
    refine PyStmtTriple.retExpr (v := .tuple
      #[.int (probe gamma b0 ts).1, .int (probe gamma b0 ts).2.1]) ?_ ?_
    · rintro st ⟨hg, hb, hs⟩
      exact EvalsTo.of_eval (fuel := 8) (by py_simp [hb, hs])
    · intro st _
      rfl

/-! ## §5 The whole function

The four statements above the loop, and the boundary. Every module-level fact
the head needs is a PINNED RESIDUE rather than an unfolding of `sf_order`
(§L8 finding 2): the two globals `QS`/`QS_A`, and the four resolution steps
`Position(…)` takes before it reaches the namedtuple table. -/

theorem qs_pin :
    lookupG (globalsFold #[] [] true false sf_order.topLevel.toList).snd.fst "QS"
      = some (some (.int 40)) := rfl
theorem qsa_pin :
    lookupG (globalsFold #[] [] true false sf_order.topLevel.toList).snd.fst "QS_A"
      = some (some (.int 140)) := rfl
theorem posG_pin :
    lookupG (globalsFold #[] [] true false sf_order.topLevel.toList).snd.fst "Position"
      = Option.none := rfl
theorem posF_pin : findFunction sf_order "Position" = Option.none := rfl
theorem posNotFun : ¬ ∃ x, x ∈ sf_order.functions ∧ x.name = "Position" := by
  simpa [findFunction] using posF_pin
/-- `Position` is a CLASS with a namedtuple base (`class
Position(namedtuple(…))`, sunfish's own shape), so the constructor call goes
through the class table, not the namedtuple table — and every step of that
dispatch is pinned here rather than unfolded. -/
def posCls : Nat × ClassDefn :=
  match findClassAux sf_order.classes.toList "Position" 0 with
  | some p => p
  | none => default

/-- The namedtuple base the class instantiates as. -/
def posNTb : NamedTupleDefn :=
  match posCls.2.ntBase with
  | some nt => nt
  | none => default

theorem posCAux : findClassAux sf_order.classes.toList "Position" 0 = some posCls := rfl
theorem posNTAux :
    findNamedTupleAux sf_order.namedtuples.toList "Position" = Option.none := rfl
theorem posCls_isExc : posCls.2.isExc = false := rfl
theorem posCls_ok : posCls.2.ok = true := rfl
theorem posCls_dunder : hasExtraDunder posCls.2 = false := rfl
theorem posCls_init : findFunction sf_order "Position.__init__" = Option.none := rfl
theorem posCls_ntBase : posCls.2.ntBase = some posNTb := rfl
theorem posNTb_fields : posNTb.fields = #["board", "score", "wc", "bc", "ep", "kp"] := rfl
theorem posNTb_name : posNTb.name = "Position" := rfl

/-- The two dispatch guards `py_simp` opens rather than matches: the dunder
census and the `__init__` lookup, each stated in the shape the simp set leaves
and closed from the `rfl` pin above. -/
theorem posCls_methods :
    posCls.2.methods = #["gen_moves", "rotate", "move", "value", "king_capture"] := rfl

theorem posNoDunder : ¬ ∃ (i : Nat) (h : i < posCls.2.methods.size),
    (match posCls.2.methods[i].toList with
      | '_' :: '_' :: rest => endsWithUU rest
      | _ => false) = true ∧ ¬ posCls.2.methods[i] = "__init__" := by
  rw [posCls_methods]
  decide

theorem posNoInit : ¬ ∃ x, x ∈ sf_order.functions ∧ x.name = "Position.__init__" := by
  simpa [findFunction] using posCls_init

/-- `bound_probe`'s frame at entry: its five parameters. -/
def bpEnv0 (b : String) (gamma depth ep kp : Int) : REnv :=
  [("board", .str b), ("gamma", .int gamma), ("depth", .int depth),
   ("ep", .int ep), ("kp", .int kp)]

/-- The `Position` the shipped first statement builds. -/
def bpPosV (b : String) (ep kp : Int) : RVal := posNt b 0 true true true true ep kp
/-- The threshold the shipped second statement computes, `QS - depth * QS_A`. -/
def bpVLv (depth : Int) : Int := 40 - depth * 140

/-- The frame after the head: the five parameters, the `Position`, the
threshold, the closure's address and the two accumulators. -/
def bpEnv1 (b : String) (gamma depth ep kp : Int) (ad : Addr) : REnv :=
  Env.set (Env.set (Env.set (Env.set (Env.set (bpEnv0 b gamma depth ep kp)
    "pos" (bpPosV b ep kp)) "val_lower" (.int (bpVLv depth)))
    "moves" (.ref ad)) "best" (.int (-100000))) "searched" (.int 0)

/-- **The head runs**: docstring, `Position(…)`, `val_lower`. -/
theorem head_run (w : World) (b : String) (gamma depth ep kp : Int) :
    execStmts sf_order 32 ⟨w, bpEnv0 b gamma depth ep kp⟩ [bpDoc, bpPos, bpVL]
      = .ok ⟨w, Env.set (Env.set (bpEnv0 b gamma depth ep kp) "pos" (bpPosV b ep kp))
          "val_lower" (.int (bpVLv depth))⟩ .next := by
  obtain ⟨c, d₁, d₂, hdoc⟩ := bpDoc_lit
  obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, p₉, p₁₀, p₁₁, p₁₂, p₁₃, p₁₄, hpos⟩ := bpPos_lit
  obtain ⟨v₁, v₂, v₃, v₄, v₅, v₆, v₇, hvls⟩ := bpVL_lit
  rw [hdoc, hpos, hvls]
  py_simp [bpEnv0, bpPosV, bpVLv, posNt, qs_pin, qsa_pin, posG_pin, posNotFun,
    posCAux, posNTAux, posCls_isExc, posCls_ok, posCls_dunder, posCls_init,
    posCls_ntBase, posNTb_fields, posNTb_name, posNoInit]
  split
  · rename_i hc
    rw [posCls_methods] at hc
    exact absurd hc (by decide)
  · py_simp [bpEnv0, bpPosV, bpVLv, posNt, qs_pin, qsa_pin]

/-- **The two accumulators run**: `best = -100000`, `searched = 0`. -/
theorem acc_run (w : World) (e : REnv) :
    execStmts sf_order 16 ⟨w, e⟩ [bpBest, bpSearched]
      = .ok ⟨w, Env.set (Env.set e "best" (.int (-100000))) "searched" (.int 0)⟩ .next := by
  obtain ⟨b₁, b₂, b₃, b₄, hbest⟩ := bpBest_lit
  obtain ⟨s₁, s₂, s₃, hsearched⟩ := bpSearched_lit
  rw [hbest, hsearched]
  py_simp []

/-- The world after the nested `def`: the closure on the heap, at its end. -/
def bpW1 (w : World) (b : String) (depth ep kp : Int) : World :=
  { w with heap := w.heap.push (movesClosure depth (bpPosV b ep kp) (bpVLv depth)) }

/-- The world after `moves()`: the generator beside the closure. -/
def bpW2 (w : World) (b : String) (depth ep kp : Int) : World :=
  { bpW1 w b depth ep kp with
    heap := (bpW1 w b depth ep kp).heap.push (movesGen depth (bpPosV b ep kp) (bpVLv depth)) }

/-- **GATE 3 — the whole shipped body.** From `bound_probe`'s entry frame, the
function builds the `Position`, computes the threshold, allocates the closure,
zeroes the accumulators, consumes the generator its own `def` produced, and
returns the walk's `(best, searched)`.

The single hypothesis is the yield SCHEDULE of that generator — what the
ordering line inside `moves` decides, which is §L8 remainder 1 and is not
touched here. -/
theorem bound_body_returns (w : World) (b : String) (gamma depth ep kp : Int)
    (ts : List Triple) (wEnd : World)
    (hands : Hands sf_order (bpW1 w b depth ep kp).heap.size
      (bpW2 w b depth ep kp) ts wEnd)
    (hdone : (probe gamma (-100000) ts).2.2 = false →
      ∃ w'', IterSteps sf_order wEnd (bpW1 w b depth ep kp).heap.size Option.none w'') :
    PyTriple sf_order (fun st => st = ⟨w, bpEnv0 b gamma depth ep kp⟩) bpB
      (.ofRet fun rv _ => rv = .tuple
        #[.int (probe gamma (-100000) ts).1, .int (probe gamma (-100000) ts).2.1]) := by
  rw [bpB_split]
  refine PyTriple.run_seq (f := 32) (pre := [bpDoc, bpPos, bpVL])
    (rest := [bpDef, bpBest, bpSearched, bpFor, bpRet]) (head_run w b gamma depth ep kp) ?_
  refine PyTriple.seq (R := fun st => st = ⟨bpW1 w b depth ep kp,
    Env.set (Env.set (Env.set (bpEnv0 b gamma depth ep kp) "pos" (bpPosV b ep kp))
      "val_lower" (.int (bpVLv depth))) "moves" (.ref w.heap.size)⟩) ?_ ?_
  · refine PyStmtTriple.of_exec ?_
    rintro st rfl
    refine ⟨32, ?_⟩
    rw [moves_def_allocates w
      (Env.set (Env.set (bpEnv0 b gamma depth ep kp) "pos" (bpPosV b ep kp))
        "val_lower" (.int (bpVLv depth))) 31 depth (bpPosV b ep kp) (bpVLv depth)
      rfl rfl rfl]
    rfl
  · refine PyTriple.run_seq (f := 16) (pre := [bpBest, bpSearched])
      (rest := [bpFor, bpRet]) (acc_run _ _) ?_
    exact bound_tail_returns _ _ w.heap.size depth (bpPosV b ep kp) (bpVLv depth)
      gamma (-100000) ts wEnd rfl (by simp [bpW1, Heap.get?_push_size]) ⟨rfl, rfl, rfl⟩
      (by simpa [bpW1, bpW2] using hands) (by simpa [bpW1] using hdone)

/-- The shipped `bound_probe`, projected, and the five facts the boundary
tests. -/
def bpF : FunctionDefn :=
  match findFunction sf_order "bound_probe" with
  | some f => f
  | none => ⟨"", #[], false, false, false, false, #[], nowhere⟩

theorem bpF_lit : findFunction sf_order "bound_probe" = some bpF ∧
    bpF.argsOk = true ∧ bpF.localsOk = true ∧ bpF.isGenerator = false ∧
    bpF.body.toList = bpB ∧ (5 : Nat) = bpF.params.size :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bpCallEnv (b : String) (gamma depth ep kp : Int) :
    mkCallEnv bpF.params (RVal.thawArgs
        #[Val.str b, Val.int gamma, Val.int depth, Val.int ep, Val.int kp])
      = bpEnv0 b gamma depth ep kp := rfl

/-- **GATE 4 — `bound_probe` at the public boundary.** The first theorem in
this repo about a sunfish SEARCH function on the raw ingested module: the pair
the shipped `bound_probe` returns is the beta-cutoff walk of the yields its own
`moves()` generator hands over. -/
theorem bound_probe_answers (b : String) (gamma depth ep kp : Int)
    (ts : List Triple) (wEnd : World)
    (hands : Hands sf_order (bpW1 (initWorld sf_order) b depth ep kp).heap.size
      (bpW2 (initWorld sf_order) b depth ep kp) ts wEnd)
    (hdone : (probe gamma (-100000) ts).2.2 = false →
      ∃ w'', IterSteps sf_order wEnd
        (bpW1 (initWorld sf_order) b depth ep kp).heap.size Option.none w'') :
    CallsTo sf_order "bound_probe"
      #[Val.str b, Val.int gamma, Val.int depth, Val.int ep, Val.int kp]
      (.tuple #[.int (probe gamma (-100000) ts).1,
                .int (probe gamma (-100000) ts).2.1]) := by
  refine PyTriple.callsTo_ofRet bpF_lit.1 bpF_lit.2.1 bpF_lit.2.2.1 bpF_lit.2.2.2.1
    bpF_lit.2.2.2.2.2.symm ?_
  rw [bpF_lit.2.2.2.2.1, bpCallEnv]
  exact bound_body_returns (initWorld sf_order) b gamma depth ep kp ts wEnd hands hdone

/-! ## §6 Non-vacuity, and the axioms

The gates are stated over a free board, a free window and a free yield
schedule, so the question is whether `probe` — the spec-side walk everything
above is measured against — reproduces what the shipped program DOES. These
`#guard`s answer it by feeding `probe` the ordering CPython itself produces
(`move_order`, differentially pinned in `spec.lean`) and comparing against
`bound_probe`'s own runs. -/

private def openingB : String :=
  "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n"

/-- The triples `moves` yields from the ordered `(value, Move)` rows: the
inner loop's own `break` is the `takeWhile` here. -/
private def yieldsOf (vl : Int) : List Val → List Triple
  | [] => []
  | .tuple #[.int v, .int i, .int j, _] :: rest =>
      if v < vl then [] else ⟨v, i, j⟩ :: yieldsOf vl rest
  | _ :: _ => []

/-! The three runs the walk is measured against (spec.lean's `#py_check`s). -/
#guard callFunction sf_order "bound_probe"
    #[.str openingB, .int 40, .int 1, .int 0, .int 0] 200000
  == .ok (.tuple #[.int 46, .int 1])
#guard callFunction sf_order "bound_probe"
    #[.str openingB, .int 1000, .int 1, .int 0, .int 0] 200000
  == .ok (.tuple #[.int 46, .int 20])
#guard callFunction sf_order "bound_probe"
    #[.str openingB, .int 1000, .int 0, .int 0, .int 0] 200000
  == .ok (.tuple #[.int 46, .int 3])

/-! **`probe` reproduces all three**, from CPython's own move ordering: at
`depth = 1` the threshold is `40 - 140 = -100` and all twenty rows are yielded
— the cutting window stops after ONE of them, the open window walks all
twenty; at `depth = 0` the threshold is `40`, `moves` yields
`(0, 0, pos.score)` first and then the two rows that clear it, and the walk
consumes three. Both arms of the cutoff, and the `depth == 0` yield. -/
#guard (match callFunction sf_order "move_order"
    #[.str openingB, .int 0, .int 0] 60000 with
  | .ok (.list ms) =>
      let deep := yieldsOf (-100) ms.toList
      let shallow := (⟨0, 0, 0⟩ : Triple) :: yieldsOf 40 ms.toList
      deep.length == 20 && shallow.length == 3
        && probe 40 (-100000) deep == (46, 1, true)
        && probe 1000 (-100000) deep == (46, 20, false)
        && probe 1000 (-100000) shallow == (46, 3, false)
  | _ => false)

#print axioms round
#print axioms bound_loop_folds
#print axioms bound_tail_returns
#print axioms bound_body_returns
#print axioms bound_probe_answers

/-! ## §7 What is still between here and the COLLAPSE

One thing, and it is not (2) any more.

**The ordering line's CONTENT** — `hdrain` in §L8's `order_line_sorts`, which
is what would DISCHARGE the `Hands` hypothesis above rather than assume it.
§L8 recorded the route as "transport `gen_moves_drains_ref` from the `sunfish`
module literal to `sf_order`'s, the method body being the same text".
`Examples/python/sf_order/transport.lean` MEASURES that premise and it is
false: the two `Position.gen_moves` agree span-for-span everywhere except the
pawn-capture guard, where the shipped file has a four-conjunct `and` with
`j != self.ep` and `abs(j - self.kp) > 1` and `sf_order.py` has a
three-conjunct one with `j not in (self.ep, self.kp, self.kp - 1, self.kp + 1)`
— equivalent on integers, different ASTs (`transport.ep_guard_differs`).
`Position.value` diverges likewise. So neither transport route exists at
`sf_order` today, and the price of each is not the question: the fixture
claims verbatim and is not, which is the thing to fix first (an owner call —
it re-ingests the fixture).

What that leaves, in order:

1. make `sf_order.py`'s `Position.gen_moves`/`Position.value` verbatim again
   and re-extract, which turns the transport into a real question;
2. the transport itself — and the measurement above says which route is
   cheap: the proofs are already span-blind (`_lit` pins existentially
   quantify every span), so a module-parametric restatement is the natural
   form and the re-run is the fallback;
3. `Position.value` agreement, which no lane has;
4. then `hdrain`, and the `Hands` hypothesis of §5 is discharged for the
   shipped board — at which point `bound_probe_answers` is unconditional.

Nothing above waits on the CALCULUS: §L8 landed the constructs, and this file
landed the consumer. -/

end Examples.python.sf_order.bound
