/-
**F3c, inch 1 — THE DEPTH-0 STREAM, and the stand-pat yield is LIVE.**

§L30 named this inch precisely: *"what is left between [`ord_stmt_emits`] and
this arm is a DEPTH-0 twin of §L32's `moves_prologue` — and it is a different
theorem, not the same one at another depth: at depth 1 the prologue is three DEAD
statements and the stream is the ordering line alone, while at depth 0 the
stand-pat `yield None, None` is LIVE."*

That is the whole content of this file. `moves_prologue` (§L32) walks three dead
branches and hands over `[.block [ordFor]]`; `moves_prologue_qs` walks the FIRST
branch dead, the SECOND **live** — pushing its body, emitting the pair, popping
the frame — and the third dead. The depth-0 schedule is therefore
`standPatPair :: sortedVs`, which is exactly the shape §L36's
`qs_fold_report_failLow` and §L73's `qs_fold_report_cut` are stated over
(`standPat sc :: rs`).

**Censused first (§L73).** On 845 depth-0 nodes that actually fold, the schedule
was `standPat :: killer? :: sortedRounds` at every one, the killer appeared at
~1 % of nodes, and the schedule length was 2–4 rounds at 87 % of them with 8 as
the sample maximum. The `killer = none` hypothesis below is that measurement, and
the killer-present arm is named as owed rather than assumed away.

**What this file does NOT do.** It does not run the fold — it produces the
STREAM the fold consumes. `PyStmtTriple.forGen` at this schedule, the round
lemma, and `TableAt`/`SubtreeWrites` threaded per child are F3c's remaining
inches, and `hfall`/`boundRefinesW_zero` wait on those, not on this.
-/
import Examples.python.sunfish.order_genexp

namespace Examples.python.sunfish.qs_stream

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)
open Examples.python.sunfish.bound_depth
open Examples.python.sunfish.order_genexp

set_option maxRecDepth 100000

/-! ## §1 The pair the stand-pat yields, and the two branch rules

`yield None, None` is a TUPLE of two `None` constants, so the value on the wire
is `.tuple #[.none, .none]` — the same shape the ordering line's pairs have, and
the reason the consumer needs no special case for it. -/

/-- The stand-pat's yielded pair, `(None, None)`. -/
def standPatPair : RVal := .tuple #[.none, .none]

/-- The killer yield, projected off `sbMBRest`. (`fold_depth1.lean` has the same
statement under the same name; it is not imported here — see `branchFalseSilent`
for why this file stays off that lane's ground.) -/
def sbKillerQ : Stmt :=
  match sbMBRest with | s :: _ => s | [] => .pass ⟨0, 0, 0, 0⟩

/-- The generator body, split — the shape the prologue walks. -/
theorem sbMB_four_qs : sbMB = [sbNull, sbStand, sbKillerQ, ordFor] := rfl

/-- `sbStand`'s plan, SPELLED — §L45's law: a gate that COMPUTES with a body has
to pin the body, and this one pushes it. (`sbStand_plan` in `fold_depth1.lean`
leaves the body existential because the depth-1 prologue never enters it.) -/
theorem sbStand_plan_qs : ∃ p0 p1 p2 p3 p4 p5 p6, genPlan sbStand =
    .branch (.compare (.name "depth" p0) #[.eq] #[.constant (.int 0) p1] p2)
      [.yieldStmt (.tuple #[.constant .none p3, .constant .none p4] p5) p6] [] :=
  ⟨_, _, _, _, _, _, _, rfl⟩

theorem sbNull_plan_qs : ∃ p0 p1 p2 p3 p4 p5 bd, genPlan sbNull =
    .branch (.boolOp .and
      #[.compare (.constant (.int 2) p0) #[.lt, .lt]
          #[.name "depth" p1, .constant (.int 6) p2] p3,
        .name "guard" p4] p5) bd [] := ⟨_, _, _, _, _, _, _, rfl⟩

theorem sbKiller_plan_qs : ∃ (e₂ e₃ : Expr) (p q : Span) (bd : List Stmt),
    genPlan sbKillerQ = .branch (.boolOp .and #[.name "killer" p, e₂, e₃] q) bd [] :=
  ⟨_, _, _, _, _, rfl⟩

/-- **A `.branch` whose test is FALSY and whose `else` is empty is two silent
steps.** `fold_depth1.lean`'s `branch_false_silent` is this at `m := sunfish`;
stated here at a FREE module because nothing in it is about the engine. The two
should become one at the general layer the next time either file is touched. -/
theorem branchFalseSilent {m : Module} {s : Stmt} {test : Expr} {bd ss : List Stmt}
    {st : FrameState} {tv : RVal}
    (hplan : genPlan s = .branch test bd [])
    (hv : EvalsTo m st test tv)
    (hb : truthyH st.world.heap tv = .ok false) :
    ∀ k : GenCont, GenSilent m st (.block (s :: ss) :: k) st (.block ss :: k) := by
  intro k
  refine GenSilent.trans (genSilent_branch (m := m) (s := s) (ss := ss) (k := k)
    (st := st) (b := false) hplan hv hb) ?_
  simpa using genSilent_blockNil (m := m) (st := st) (k := .block ss :: k)

/-- …and its LIVE twin: a `.branch` whose test is TRUTHY pushes its body. -/
theorem branchTrueEnters {m : Module} {s : Stmt} {test : Expr} {bd ss : List Stmt}
    {st : FrameState} {tv : RVal}
    (hplan : genPlan s = .branch test bd [])
    (hv : EvalsTo m st test tv)
    (hb : truthyH st.world.heap tv = .ok true) :
    ∀ k : GenCont, GenSilent m st (.block (s :: ss) :: k) st
      (.block bd :: .block ss :: k) := by
  intro k
  simpa using genSilent_branch (m := m) (s := s) (ss := ss) (k := k) (st := st)
    (b := true) hplan hv hb

/-! ## §2 THE DEPTH-0 PROLOGUE — one live round, two dead branches

The depth-1 twin is three dead branches and a silent hand-over. This one is
**five steps**: the null branch dies, the stand-pat branch ENTERS, its `yield`
emits, the emptied body frame pops, and the killer branch dies. What is left on
the stack is the ordering line, exactly as at depth 1 — so the two prologues
converge on the same hand-over and differ only in what they put on the wire. -/

/-- **THE DEPTH-0 PROLOGUE.** Consumes the ordering line's own emission and puts
the stand-pat pair in front of it. Stated as a transformer rather than a
stand-alone `GenEmits` because the stand-pat is not the end of the stream — the
schedule the fold consumes is `standPat :: rest`, and `rest` is R2's. -/
theorem moves_prologue_qs (w : World) (e : REnv) {ws : List RVal} {stF : FrameState}
    (hd : Env.lookup e "depth" = some (.int 0))
    (hk : Env.lookup e "killer" = some .none)
    (hord : GenEmits sunfish ⟨w, e⟩ [.block [ordFor]] ws stF) :
    GenEmits sunfish ⟨w, e⟩ [.block sbMB] (standPatPair :: ws) stF := by
  obtain ⟨p0, p1, p2, p3, p4, p5, bd1, hpl1⟩ := sbNull_plan_qs
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, hpl2⟩ := sbStand_plan_qs
  obtain ⟨e₂, e₃, kp, kq, bd3, hpl3⟩ := sbKiller_plan_qs
  -- branch 1: `2 < depth < 6 and guard` dies on `2 < 0`
  have h1e : evalExpr sunfish 6 ⟨w, e⟩
      (.compare (.constant (.int 2) p0) #[.lt, .lt]
        #[.name "depth" p1, .constant (.int 6) p2] p3) = .ok ⟨w, e⟩ (.bool false) := by
    py_simp [-globalsFold, -globalsStep, hd]
  have hs1 := branchFalseSilent (m := sunfish) (s := sbNull)
    (ss := [sbStand, sbKillerQ, ordFor]) hpl1
    (EvalsTo.of_eval (fuel := 8)
      (by rw [evalExpr]; exact boolChain_and_falsy (F := 6) h1e rfl)) rfl
  -- branch 2: `depth == 0` FIRES
  have hda : evalExpr sunfish 7 ⟨w, e⟩ (.name "depth" q0) = .ok ⟨w, e⟩ (.int 0) := by
    py_simp [-globalsFold, -globalsStep, hd]
  have hzero : evalExpr sunfish 6 ⟨w, e⟩ (.constant (.int 0) q1) = .ok ⟨w, e⟩ (.int 0) := by
    py_simp [-globalsFold, -globalsStep]
  have hop : evalCompareOpH w.heap 6 .eq (.int 0) (.int 0) = .ok true := by
    simp [evalCompareOpH, RVal.refFree, valEq]
  have hs2 := branchTrueEnters (m := sunfish) (s := sbStand) (ss := [sbKillerQ, ordFor])
    hpl2 (EvalsTo.of_eval (fuel := 8) (compare_one (F := 5) hda hzero hop)) rfl
  -- the yield itself
  have hpair : evalExpr sunfish 4 ⟨w, e⟩
      (.tuple #[.constant .none q3, .constant .none q4] q5) = .ok ⟨w, e⟩ standPatPair := by
    py_simp [-globalsFold, -globalsStep, standPatPair]
  -- branch 3: the killer is absent
  have h3e : evalExpr sunfish 4 ⟨w, e⟩ (.name "killer" kp) = .ok ⟨w, e⟩ .none := by
    py_simp [-globalsFold, -globalsStep, hk]
  have hs3 := branchFalseSilent (m := sunfish) (s := sbKillerQ) (ss := [ordFor]) hpl3
    (EvalsTo.of_eval (fuel := 6)
      (by rw [evalExpr]; exact boolChain_and_falsy (F := 4) h3e rfl)) rfl
  rw [sbMB_four_qs]
  refine GenEmits.silent (pre := [GenFrame.block [sbNull, sbStand, sbKillerQ, ordFor]])
    (pre₁ := [GenFrame.block [sbStand, sbKillerQ, ordFor]])
    (fun k => by simpa using hs1 k) ?_
  refine GenEmits.silent (pre₁ := [GenFrame.block [.yieldStmt
      (.tuple #[.constant .none q3, .constant .none q4] q5) q6],
      GenFrame.block [sbKillerQ, ordFor]])
    (fun k => by simpa using hs2 k) ?_
  refine GenEmits.cons (v := standPatPair)
    (pre₁ := [GenFrame.block [], GenFrame.block [sbKillerQ, ordFor]])
    (fun k => by
      simpa using genSteps_yieldHere (m := sunfish) (st := (⟨w, e⟩ : FrameState))
        (s := .yieldStmt (.tuple #[.constant .none q3, .constant .none q4] q5) q6)
        (e := .tuple #[.constant .none q3, .constant .none q4] q5)
        (ss := ([] : List Stmt)) (k := GenFrame.block [sbKillerQ, ordFor] :: k)
        (v := standPatPair) rfl (EvalsTo.of_eval (fuel := 4) hpair)) ?_
  refine GenEmits.silent (pre₁ := [GenFrame.block [sbKillerQ, ordFor]])
    (fun k => by
      simpa using genSilent_blockNil (m := sunfish) (st := (⟨w, e⟩ : FrameState))
        (k := GenFrame.block [sbKillerQ, ordFor] :: k)) ?_
  exact GenEmits.silent (pre₁ := [GenFrame.block [ordFor]])
    (fun k => by simpa using hs3 k) hord

/-! ## §3 THE DEPTH-0 STREAM — the schedule the fold consumes

`moves_emits_ordered` (§L32) is the depth-1 statement: the stream IS the ordering
line. This is its depth-0 twin, and the one difference is the head. -/

/-- **`moves()` at depth 0 emits the STAND-PAT PAIR and then the sorted moves.**
The schedule `qs_fold_report_cut` and `qs_fold_report_failLow` are stated over,
produced by the shipped generator. -/
theorem moves_emits_qs (w : World) (e : REnv)
    (b : String) (sc ep kp : Int) (wc0 wc1 bc0 bc1 : Bool)
    (vs sortedVs : List RVal) (w' : World)
    (hd : Env.lookup e "depth" = some (.int 0))
    (hk : Env.lookup e "killer" = some .none)
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hsorted : Env.lookup e "sorted" = Option.none)
    (hgxl : Env.lookup e "<genexpr@1>" = Option.none)
    (hdrain : IterDrains sunfish
      (gxW w 0 (posOf b sc wc0 wc1 bc0 bc1 ep kp)) (w.heap.size + 1) vs w')
    (hsort : sortByLt true vs = .ok sortedVs) :
    ∃ env', GenEmits sunfish ⟨w, e⟩ [.block sbMB] (standPatPair :: sortedVs)
      ⟨ordW w' sortedVs, env'⟩ := by
  obtain ⟨env', hstmt⟩ := ord_stmt_emits w e 0 b sc ep kp wc0 wc1 bc0 bc1 vs sortedVs w'
    hpos hd hsorted hgxl hdrain hsort
  exact ⟨env', moves_prologue_qs w e hd hk hstmt⟩

/-! ## §4 What the stream is NOT, and what F3c still owes

* **The killer arm.** `hk` is `killer = none`, which the census measured at ~99 %
  of depth-0 nodes. When the killer IS present its own test is
  `val >= QS or depth` — and `depth` is falsy at 0, so the killer round survives
  only by clearing the QS floor. That arm inserts ONE extra round between the
  stand-pat and the sorted stream and is otherwise the same shape.
* **The fold over this stream.** `PyStmtTriple.forGen` at this schedule, the
  round lemma at the census's 2–4 realistic lengths with 8 as the stress case,
  and `TableAt`/`SubtreeWrites` threaded per child.
* **`hfall` and `boundRefinesW_zero`.** Both wait on the fold, not on the
  stream. -/

/-! ### INSTANTIATED — the shipped generator, DRAINED at depth 0

`moves_emits_qs` is stated over a free board and a free drain, so the question is
whether it describes what the engine does. These guards drain the SHIPPED
generator body on the fixture at depth 0 and read the answer off the wire.

**The two counts compose exactly.** `order_genexp.lean` measured the ordering
line alone at depth 0 as **2** emissions; the whole body here drains to **3**,
and the extra one is at the HEAD and is `standPatPair`. That is
`moves_prologue_qs`'s conclusion — `standPatPair :: ws` — read off the
interpreter rather than off the statement. -/

private def qsEnvP : REnv := [("depth", .int 0), ("killer", .none), ("pos", posH 0)]

private def qsDrainP (F : Nat) : Option (Nat × Option RVal) :=
  match drainGen sunfish F ⟨initWorld sunfish, qsEnvP⟩ [.block sbMB] with
  | .ok _ vs => some (vs.length, vs.head?)
  | _ => Option.none

/-! Three values, and the FIRST is the stand-pat pair. -/
#guard (match qsDrainP 8192 with
  | some (n, some v) => n == 3 && v == standPatPair
  | _ => false)

/-! …and the tail is the ordering line's own two, which is the count
`order_genexp.lean` measured for the line by itself: the prologue adds exactly
one round and it adds it at the head. -/
#guard (match qsDrainP 8192 with | some (n, _) => n - 1 == 2 | _ => false)

/-! The depth-0 killer really is absent in this frame, so `hk` is the fixture's
own shape and not an assumption bolted on. -/
#guard (Env.lookup qsEnvP "killer" == some RVal.none)
#guard (Env.lookup qsEnvP "depth" == some (RVal.int 0))

/-! ### The axioms -/

#print axioms sbStand_plan_qs
#print axioms sbNull_plan_qs
#print axioms sbMB_four_qs
#print axioms sbKiller_plan_qs
#print axioms branchFalseSilent
#print axioms branchTrueEnters
#print axioms moves_prologue_qs
#print axioms moves_emits_qs

end Examples.python.sunfish.qs_stream
