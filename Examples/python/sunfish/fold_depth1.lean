/-
**R3's CENSUS, and the depth-1 schedule** — inch R3 of the `RecursionStep`
campaign (docs/backlog.md §L25), opened census-first as the plan law requires.

§L25 priced R3 at *two sessions*: *"the many-round fold, with an IH per round…
what changes from depth 0 is that `Inv []` is no longer `False`."* **The census
says it is more than two, and it also says which two inches are the cheap ones.**
So this file is the measurement plus the plan, with the one piece that was cheap
already landed: the depth-1 PROLOGUE, which is what makes "R3's schedule is the
ordering line's stream" a theorem rather than a claim.

**Measured on the shipped fixture before a gate was written** (§L24's exit law),
`Searcher().bound(posH 0, gamma, 1)`:

| window | answer | nodes | heap |
|---|---|---|---|
| `gamma ≥ 47` | 46 | **1** | 70 → 246 |
| `gamma ≤ 0` | 0 | **2** | 70 → 247 |
| `gamma = 5` | 37 | 35 | 70 → 3024 |
| `gamma = 10` | 37 | 41 | 70 → 3496 |
| `gamma = 40` | 37 | 34 | 70 → 2881 |

The edges are one round and two rounds; the middle is forty. **300 fuel decides
both edges and 200 does not.**

**And the depth-1 stream has no virtual rounds at all.** Both `yield None, None`
statements are dead by arithmetic (`2 < depth` fails at depth 1, `depth == 0`
fails above 0) and the killer yield dies on its first operand, because a fresh
`Searcher()`'s `tp_move` is EMPTY — the one thing in that list which is a
measurement rather than arithmetic, and `#guard`ed below. So the depth-1 schedule
is exactly what R2c hands over, which is the complement of the depth-0 schedule
(one virtual round, and the fold cuts on it). **The two grounds do not overlap**,
and this file touches no depth-0 arm.
-/
import Examples.python.sunfish.order_genexp

namespace Examples.python.sunfish.fold_depth1

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)
open Examples.python.sunfish.bound_depth (sbMB sbMBRest sbNull sbStand sbMB_split
  sbNull_lit sbStand_lit compare_one boolChain_and_falsy
  sbScore sbScore_lit sbElse1 sbElse1_split sbVirt sbVirt_lit sbReal sbReal_lit
  sbB5 sbB5_split sbCapLine sbCapLine_lit sbBreak sbBreak_lit
  maxG maxNotFun maxCls maxNT mlG posCAux posCls_methods
  execStmt_if_true execStmt_if_false execStmts_singleton_flow
  Round Sound Report foldFrom settledCap fold_report foldFrom_cons_settle
  sbMoveDepth sbLive minG minNotFun minCls minNT muG boolChain_and3
  execStmt_assign_name)
open Examples.python.sunfish.order_genexp

set_option maxRecDepth 100000

private def nowhere : Span := ⟨0, 0, 0, 0⟩
private def nth (n : Nat) (ss : List Stmt) : Stmt :=
  match ss.drop n with | s :: _ => s | [] => .pass nowhere

/-! ## §0 THE CENSUS — the shipped `bound()` at depth 1, RUN -/

private def probe (gamma depth : Int) (F : Nat) : Option (Int × Int × Nat × Nat) :=
  match searcherW with
  | some (w, a) =>
    (match callIn sunfish F w "Searcher.bound" #[.ref a, posH 0, .int gamma, .int depth] with
     | .ok w' (RVal.int r) =>
       (match Heap.get? w'.heap a with
        | some (Obj.instance _ attrs) =>
          (match Env.lookup attrs.toList "nodes" with
           | some (RVal.int n) => some (r, n, w.heap.size, w'.heap.size)
           | _ => Option.none)
        | _ => Option.none)
     | _ => Option.none)
  | Option.none => Option.none

/-! **The killer table is EMPTY on a fresh `Searcher()`** — the fact that makes
the depth-1 prologue below reach the ordering line, and the one thing in it that
is a measurement rather than arithmetic. -/
#guard (match searcherW with
        | some (w, a) =>
          (match Heap.get? w.heap a with
           | some (Obj.instance _ attrs) =>
             (match Env.lookup attrs.toList "tp_move" with
              | some (RVal.ref t) =>
                (match Heap.get? w.heap t with
                 | some (Obj.dict es _) => es.size == 0
                 | _ => false)
              | _ => false)
           | _ => false)
        | _ => false)

/-! **The SETTLE arm — one round, ONE node, no recursion at all.** Above the
best move's value the futility cap `pos.score + val` is below the window, so the
fold settles on the first round and breaks. `best = 46`, and the child search
never happens. This is R3's cheapest schedule and the one to prove first. -/
#guard probe 47 1 300 == some (46, 1, 70, 246)
#guard probe 100 1 300 == some (46, 1, 70, 246)

/-! **The CUT arm — one searched round, then the cutoff.** At a window the first
move already meets, the fold searches once (2 nodes: this one and the child) and
cuts. This is the cheapest schedule that CONSUMES THE IH, and it is R3's second
inch. -/
#guard probe 0 1 300 == some (0, 2, 70, 247)
#guard probe (-40) 1 300 == some (0, 2, 70, 247)

/-! **The fuel.** 300 decides both arms; 200 does not — so no gate below pins a
numeral that was not measured. -/
#guard (probe 47 1 200).isNone && (probe 0 1 200).isNone

/-! **And the middle of the window is where the cost is**, which is why the two
arms above are the ones to prove: `gamma = 5` costs 35 nodes and `gamma = 10`
costs 41, against 1 and 2 at the edges. Measured on the same fixture, not
guarded here — a 41-node `bound` is seconds of elaboration for a number that
prices the plan rather than discharging a premise. -/

/-! ## §1 THE DEPTH-1 PROLOGUE — `moves()` reaches the ordering line

Three statements stand between the generator's entry and the ordering line, and
**at depth 1 with an empty killer table all three are dead**:

* `if 2 < depth < 6 and guard: yield None, None` — the chain dies on `2 < depth`;
* `if depth == 0: yield None, None` — the stand-pat, dead above depth 0;
* the killer yield — dies on its FIRST operand, the bare `killer`.

So the depth-1 schedule has **no virtual rounds at all**: it is exactly the
ordering line's stream, which is what R2c hands over. That is the complement of
the depth-0 schedule (one virtual round, and the fold cuts on it), and it is why
R3's ground and the base case's do not overlap. -/

/-- The killer yield — `sbMBRest`'s first statement. -/
def sbKiller : Stmt := nth 0 sbMBRest

theorem sbMB_four : sbMB = [sbNull, sbStand, sbKiller, ordFor] := rfl

theorem sbKiller_test_lit : ∃ (e₂ e₃ : Expr) (p q : Span) (bd : Array Stmt) (r : Span),
    sbKiller = .ifStmt (.boolOp .and #[.name "killer" p, e₂, e₃] q) bd #[] r :=
  ⟨_, _, _, _, _, _, rfl⟩

theorem sbNull_plan : ∃ p0 p1 p2 p3 p4 p5 bd, genPlan sbNull =
    .branch (.boolOp .and
      #[.compare (.constant (.int 2) p0) #[.lt, .lt]
          #[.name "depth" p1, .constant (.int 6) p2] p3,
        .name "guard" p4] p5) bd [] := ⟨_, _, _, _, _, _, _, rfl⟩

theorem sbStand_plan : ∃ p0 p1 p2 bd, genPlan sbStand =
    .branch (.compare (.name "depth" p0) #[.eq] #[.constant (.int 0) p1] p2) bd [] :=
  ⟨_, _, _, _, rfl⟩

theorem sbKiller_plan : ∃ (e₂ e₃ : Expr) (p q : Span) (bd : List Stmt), genPlan sbKiller =
    .branch (.boolOp .and #[.name "killer" p, e₂, e₃] q) bd [] := ⟨_, _, _, _, _, rfl⟩

/-- A `.branch` whose test is FALSY and whose `else` is empty is two silent
steps and no emission — the shape all three prologue statements take. -/
theorem branch_false_silent {s : Stmt} {test : Expr} {bd : List Stmt} {ss : List Stmt}
    {w : World} {e : REnv} {tv : RVal}
    (hplan : genPlan s = .branch test bd [])
    (hv : EvalsTo sunfish ⟨w, e⟩ test tv)
    (hb : truthyH w.heap tv = .ok false) :
    ∀ k : GenCont, GenSilent sunfish ⟨w, e⟩ (.block (s :: ss) :: k) ⟨w, e⟩
      (.block ss :: k) := by
  intro k
  refine GenSilent.trans (genSilent_branch (m := sunfish) (s := s) (ss := ss) (k := k)
    (st := ⟨w, e⟩) (b := false) hplan hv hb) ?_
  simpa using genSilent_blockNil (m := sunfish) (st := ⟨w, e⟩) (k := .block ss :: k)

/-- **The prologue, in one silent transition.** From the generator's whole body
to the ordering line alone, at `1 ≤ depth ≤ 2` with the killer absent. -/
theorem moves_prologue (w : World) (e : REnv) (d : Int)
    (hd : Env.lookup e "depth" = some (.int d))
    (hlo : 1 ≤ d) (hhi : d ≤ 2)
    (hk : Env.lookup e "killer" = some .none) :
    ∀ k : GenCont, GenSilent sunfish ⟨w, e⟩ (.block sbMB :: k) ⟨w, e⟩
      (.block [ordFor] :: k) := by
  intro k
  obtain ⟨p0, p1, p2, p3, p4, p5, bd1, hpl1⟩ := sbNull_plan
  obtain ⟨q0, q1, q2, bd2, hpl2⟩ := sbStand_plan
  obtain ⟨e₂, e₃, kp, kq, bd3, hpl3⟩ := sbKiller_plan
  have h1e : evalExpr sunfish 6 ⟨w, e⟩
      (.compare (.constant (.int 2) p0) #[.lt, .lt]
        #[.name "depth" p1, .constant (.int 6) p2] p3) = .ok ⟨w, e⟩ (.bool false) := by
    py_simp [-globalsFold, -globalsStep, hd, if_neg (show ¬ (2 : Int) < d by omega)]
  have hs1 := branch_false_silent (s := sbNull) (ss := [sbStand, sbKiller, ordFor])
    hpl1 (EvalsTo.of_eval (fuel := 8)
      (by rw [evalExpr]; exact boolChain_and_falsy (F := 6) h1e rfl)) rfl k
  have hda : evalExpr sunfish 7 ⟨w, e⟩ (.name "depth" q0) = .ok ⟨w, e⟩ (.int d) := by
    py_simp [-globalsFold, -globalsStep, hd]
  have hzero : evalExpr sunfish 6 ⟨w, e⟩ (.constant (.int 0) q1) = .ok ⟨w, e⟩ (.int 0) := by
    py_simp [-globalsFold, -globalsStep]
  have hop : evalCompareOpH w.heap 6 .eq (.int d) (.int 0) = .ok false := by
    simp [evalCompareOpH, RVal.refFree, valEq, show d ≠ 0 by omega]
  have h2 : EvalsTo sunfish ⟨w, e⟩
      (.compare (.name "depth" q0) #[.eq] #[.constant (.int 0) q1] q2) (.bool false) :=
    EvalsTo.of_eval (fuel := 8) (compare_one (F := 5) hda hzero hop)
  have hs2 := branch_false_silent (s := sbStand) (ss := [sbKiller, ordFor])
    hpl2 h2 rfl k
  have h3e : evalExpr sunfish 4 ⟨w, e⟩ (.name "killer" kp) = .ok ⟨w, e⟩ .none := by
    py_simp [-globalsFold, -globalsStep, hk]
  have hs3 := branch_false_silent (s := sbKiller) (ss := [ordFor])
    hpl3 (EvalsTo.of_eval (fuel := 6)
      (by rw [evalExpr]; exact boolChain_and_falsy (F := 4) h3e rfl)) rfl k
  rw [sbMB_four]
  exact GenSilent.trans hs1 (GenSilent.trans hs2 hs3)

/-! ## §2 THE DEPTH-1 STREAM — R2 and the prologue, joined -/

/-- **`moves()` at depth 1 emits exactly the ordering line's sorted pairs.**
The prologue is silent, the ordering statement is R2's `ord_stmt_emits`, and
between them the generator's whole body is accounted for. This is the schedule
R3's fold consumes, and it is `sortedVs` — free, descending `(value, Move)`
pairs — with no virtual round in front of it. -/
theorem moves_emits_ordered (w : World) (e : REnv) (d : Int)
    (b : String) (sc ep kp : Int) (wc0 wc1 bc0 bc1 : Bool)
    (vs sortedVs : List RVal) (w' : World)
    (hd : Env.lookup e "depth" = some (.int d)) (hlo : 1 ≤ d) (hhi : d ≤ 2)
    (hk : Env.lookup e "killer" = some .none)
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hsorted : Env.lookup e "sorted" = Option.none)
    (hgxl : Env.lookup e "<genexpr@1>" = Option.none)
    (hdrain : IterDrains sunfish
      (gxW w d (posOf b sc wc0 wc1 bc0 bc1 ep kp)) (w.heap.size + 1) vs w')
    (hsort : sortByLt true vs = .ok sortedVs) :
    ∃ env', GenEmits sunfish ⟨w, e⟩ [.block sbMB] sortedVs
      ⟨ordW w' sortedVs, env'⟩ := by
  obtain ⟨env', hstmt⟩ := ord_stmt_emits w e d b sc ep kp wc0 wc1 bc0 bc1 vs sortedVs w'
    hpos hd hsorted hgxl hdrain hsort
  exact ⟨env', GenEmits.silent (pre := [GenFrame.block sbMB])
    (pre₁ := [GenFrame.block [ordFor]])
    (fun k => by simpa using moves_prologue w e d hd hlo hhi hk k) hstmt⟩

#print axioms sbMB_four
#print axioms sbKiller_test_lit
#print axioms sbNull_plan
#print axioms sbStand_plan
#print axioms sbKiller_plan
#print axioms branch_false_silent
#print axioms moves_prologue
#print axioms moves_emits_ordered

/-! ## §3 THE R3 PLAN, priced per inch and censused first

§L25 gave R3 one paragraph and two sessions. The measurements above say it is
**five inches**, and they say which two to do first. The ordering is the one the
numbers imply, not the one the source text reads in.

### R3a — the SETTLE arm: one round, no recursion. **LANDED, §4 below.**

`gamma ≥ 47` on the fixture: the first move's futility cap
`pos.score + val + max(depth-1,0) * QS_A` is `pos.score + val` at depth 1, it is
below the window, and the fold **settles and breaks** — ONE node, no child call,
no IH. Schedule `[Round.settle cap]`, and `fold_report`'s `hfut` premise is
discharged by the cap being the round's own.

What it owes, in computed shape: the fold body's third branch (`else:` — a real
move) down to `if cap < gamma: best = max(best, cap); break`, which is
`sbScore`'s `elif` chain taken to its LAST arm. `execStmt_if_false` three times
keeps `py_simp` out of the recursive arms, exactly as `qs_score` does for
branch 1. **This inch consumes no IH and no `RecursionStepW` hypothesis**, so it
is the one that can be written against the census alone.

### R3b — the CUT arm: one searched round, then the cutoff. **HALF LANDED: §6 proves the reduction and the `live` update; §7 censuses the call.**

`gamma ≤ 0`: the cap clears the window, the child is searched at
`move_depth = depth - 1 - (…) - int(nmr)`, and `best ≥ gamma` cuts — TWO nodes.
This is the cheapest schedule that **consumes the IH**, through
`searchedMove_sound` (already proved, §L16). The child's depth is
`depth - 1` at depth 1 with `guard` false and `nmr` false, which is `0` — inside
`RecursionStepW`'s strong hypothesis `∀ e, 0 ≤ e → e < d`, and that is the whole
reason the strong form was landed (§L26).

*Owed:* `move_depth`'s arithmetic gate (three subtractions, two of them boolean
coercions), and the child call's `EvalsIn`, which allocates. **Its census is
taken (§5 below): `int()` is NOT lowered**, and both coercions the line needs are
implemented — so `move_depth` is ordinary arithmetic once its two boolean
operands are decided, and R3b's cost is the child call rather than the
reduction.

### R3c — the MANY-round fold. *Two sessions, and this is §L25's R3 proper.*

`PyStmtTriple.forGen` at a schedule of length > 1, with `Inv` carrying the
accumulator. `qs_fold_breaks` is the depth-0 template and `QSInv` is its
one-round invariant; the depth-1 invariant must carry `(best, live)` and the
remaining rounds, which is §L16's `Hands`. **`Inv []` is no longer `False`** — the
loop can run out of moves — so the exhaustion obligation returns and
`fold_report` must be discharged at `Exit.ran` as well as at `Exit.cut`.

*Census still owed here, and it is the one measurement this pass did NOT take:*
**does the depth-1 fold ever exhaust on the fixture?** Every window measured
above ends in a cut or a settle. Exhaustion needs `gamma` below every cap and
above every score, and whether that band is non-empty on this board is a
half-hour of `bd_probe`. Take it before writing `Inv []`.

### R3d — the correction and the store. *One session.*

`depth and not live and all(gen_moves() scan)` (§L25's R5) and
`sf_store_from_report` (§L20) at the computed store. Both are named elsewhere;
they are listed here because `RefinesAt`'s four conjuncts are not discharged
until they are.

### R3e — `SubtreeWrites` at a searched node. *One session.*

Depth 0's two proved leaves touch ONE heap slot (the node counter) and spend
`.other`/`.nil`. A depth-1 node allocates 176 objects on the settle arm alone
(measured above: 70 → 246), so the `.alloc` arm is unavoidable and this is where
§L14's allocation lemma finally gets spent at a real node.

### What R3 does NOT own

The depth-0 circular arm — the calmness genexp and the `±750` band — is the
census lane's ground (§L27), and nothing above touches it. If an inch here turns
out to need a depth-0 fact, the answer is to ask rather than to re-census.

### And the one remainder R2 left

`hdrain` in `moves_emits_ordered` is still the genexp object's drain (§L31 §10).
R3a and R3b are stated over a free `sortedVs`, so **neither is blocked on it**;
R3c's `Inv` is where a concrete schedule first has to be named, and that is the
point at which the step-indexed reading of `gen_moves_yields_ref` has to land. -/


/-! ## §4 R3a — THE SETTLE ARM, LANDED

The census's cheapest schedule: a real move whose futility cap is below the
window. The score chain falls through both `move is None` arms and the mate-band
arm, computes the cap, folds it into `best` with `max`, and BREAKS — no child
call, no `live` update, no killer store. One round, one node.

**`hfut` is discharged by the cap being the round's own.** `fold_report`'s
futility premise quantifies over every `settle` in the schedule; a one-settle
schedule has exactly one, so the premise collapses to the single hypothesis
`value ≤ capv`. And `Sound` comes free from the interpreter's own break
condition `capv < gamma` — the same inequality, read on the spec side.

`MATE_LOWER` is statically POISONED (§L26's `mlG`), so the mate-band arm's guard
takes it from `w.globals`; `QS_A` resolves statically, so the cap line says
nothing about the world beyond `pos`. -/

theorem qsaG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "QS_A"
    = some (some (.int 140)) := rfl

/-- **The futility cap at or below depth 3.** -/
theorem cap_line_low (w : World) (e : REnv) (d val sc : Int) (b : String)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (F : Nat)
    (hd : Env.lookup e "depth" = some (.int d))
    (hval : Env.lookup e "val" = some (.int val))
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hnomax : Env.lookup e "max" = Option.none)
    (hnqa : Env.lookup e "QS_A" = Option.none)
    (hlo : 1 ≤ d) (hhi : d ≤ 3) :
    execStmt sunfish (F + 16) ⟨w, e⟩ sbCapLine
      = .ok ⟨w, Env.set e "cap" (.int (sc + val + (d - 1) * 140))⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16,
    p17, p18, p19, hlit⟩ := sbCapLine_lit
  have hm : max (d - 1) (0 : Int) = d - 1 := by omega
  rw [hlit]
  py_simp [-globalsFold, -globalsStep, hd, hval, hpos, hnomax, hnqa, qsaG,
    maxG, maxNotFun, maxCls, maxNT, posOf, posCAux, posCls_methods,
    if_neg (show ¬ (3 : Int) < d by omega), hm]


theorem sbVirtElse_split :
    (match sbVirt with | Stmt.ifStmt _ _ o _ => o.toList | _ => []) = [sbReal] := rfl

/-- **THE BREAK.** `if cap < gamma: best = max(best, cap); break`. -/
theorem break_fires (w : World) (e : REnv) (capv bst gamma : Int) (F : Nat)
    (hcap : Env.lookup e "cap" = some (.int capv))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hb : Env.lookup e "best" = some (.int bst))
    (hnomax : Env.lookup e "max" = Option.none)
    (hlt : capv < gamma) :
    execStmt sunfish (F + 12) ⟨w, e⟩ sbBreak
      = .ok ⟨w, Env.set e "best" (.int (max bst capv))⟩ .brk := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, hlit⟩ := sbBreak_lit
  have hcond : evalExpr sunfish (F + 11) ⟨w, e⟩
      (.compare (.name "cap" p0) #[.lt] #[.name "gamma" p1] p2) = .ok ⟨w, e⟩ (.bool true) := by
    py_simp [-globalsFold, -globalsStep, hcap, hg, if_pos hlt]
  rw [hlit, execStmt_if_true hcond rfl]
  simp only [execStmts]
  py_simp [-globalsFold, -globalsStep, hcap, hb, hnomax, maxG, maxNotFun, maxCls, maxNT]

/-- The frame a settled round leaves: `cap` bound and `best` folded. -/
def envSettle (e : REnv) (capv bst : Int) : REnv :=
  Env.set (Env.set e "cap" (.int capv)) "best" (.int (max bst capv))

/-- **R3a — THE SETTLE ROUND.** A real move whose futility cap is below the
window: the score chain falls through both `move is None` arms and the mate-band
arm, the cap is computed, and the round BREAKS with `best` folded — no child
call, no `live`, no killer store. -/
theorem settle_round (w : World) (e : REnv) (d val sc bst gamma ml : Int) (mvv : RVal)
    (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (F : Nat)
    (hmv : Env.lookup e "move" = some mvv)
    (hisnot : ∀ G : Nat, evalCompareOpH w.heap G .is mvv .none = .ok false)
    (hd : Env.lookup e "depth" = some (.int d))
    (hval : Env.lookup e "val" = some (.int val))
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hnomax : Env.lookup e "max" = Option.none)
    (hnqa : Env.lookup e "QS_A" = Option.none)
    (hnml : Env.lookup e "MATE_LOWER" = Option.none)
    (hmlw : Env.lookup w.globals "MATE_LOWER" = some (.int ml))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hb : Env.lookup e "best" = some (.int bst))
    (hlo : 1 ≤ d) (hhi : d ≤ 3)
    (hband : val < ml)
    (hcut : sc + val + (d - 1) * 140 < gamma) :
    execStmt sunfish (F + 30) ⟨w, e⟩ sbScore
      = .ok ⟨w, envSettle e (sc + val + (d - 1) * 140) bst⟩ .brk := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, hslit⟩ := sbScore_lit
  obtain ⟨vo, v0, v1, v2, v3, hvlit⟩ := sbVirt_lit
  obtain ⟨rb, r0, r1, r2, r3, hrlit⟩ := sbReal_lit
  -- the `move is None` compare, at both spans
  have hmvE : ∀ (G : Nat) (q0 : Span), evalExpr sunfish (G + 2) ⟨w, e⟩ (.name "move" q0)
      = .ok ⟨w, e⟩ mvv := by
    intro G q0; py_simp [-globalsFold, -globalsStep, hmv]
  have hnoneE : ∀ (G : Nat) (q1 : Span),
      evalExpr sunfish (G + 1) ⟨w, e⟩ (.constant Const.none q1) = .ok ⟨w, e⟩ .none := by
    intro G q1; py_simp [-globalsFold, -globalsStep]
  have hisNone : ∀ (G : Nat) (q0 q1 q2 : Span), evalExpr sunfish (G + 3) ⟨w, e⟩
      (.compare (.name "move" q0) #[.is] #[.constant Const.none q1] q2)
        = .ok ⟨w, e⟩ (.bool false) :=
    fun G q0 q1 q2 => compare_one (F := G) (hmvE G q0) (hnoneE G q1) (hisnot (G + 1))
  -- the mate-band compare
  have hvalE : ∀ G : Nat, evalExpr sunfish (G + 2) ⟨w, e⟩ (.name "val" r0)
      = .ok ⟨w, e⟩ (.int val) := by
    intro G; py_simp [-globalsFold, -globalsStep, hval]
  have hmlE : ∀ G : Nat, evalExpr sunfish (G + 1) ⟨w, e⟩ (.name "MATE_LOWER" r1)
      = .ok ⟨w, e⟩ (.int ml) := by
    intro G; py_simp [-globalsFold, -globalsStep, hnml, hmlw, mlG]
  have hmlOp : ∀ G : Nat, evalCompareOpH w.heap G .gtE (.int val) (.int ml) = .ok false := by
    intro G; simp [evalCompareOpH, evalCompareOp, asInt, intCmp,
      show ¬ ml ≤ val by omega]
  have hmate : ∀ (G : Nat), evalExpr sunfish (G + 3) ⟨w, e⟩
      (.compare (.name "val" r0) #[.gtE] #[.name "MATE_LOWER" r1] r2)
        = .ok ⟨w, e⟩ (.bool false) :=
    fun G => compare_one (F := G) (hvalE G) (hmlE G) (hmlOp (G + 1))
  -- branch 5's two statements
  have hb5 : execStmts sunfish (F + 25) ⟨w, e⟩ sbB5
      = .ok ⟨w, envSettle e (sc + val + (d - 1) * 140) bst⟩ .brk := by
    rw [sbB5_split]
    simp only [execStmts]
    rw [cap_line_low w e d val sc b wc0 wc1 bc0 bc1 ep kp (F + 8) hd hval hpos hnomax
      hnqa hlo hhi]
    simp only [Run.bind]
    rw [break_fires w (Env.set e "cap" (.int (sc + val + (d - 1) * 140)))
      (sc + val + (d - 1) * 140) bst gamma (F + 11)
      (by simp [Env.lookup_set_self]) (by simp [Env.lookup_set_ne, hg])
      (by simp [Env.lookup_set_ne, hb]) (by simp [Env.lookup_set_ne, hnomax]) hcut]
    simp only [envSettle]
  -- the real-move arm
  have hreal : execStmt sunfish (F + 26) ⟨w, e⟩ sbReal
      = .ok ⟨w, envSettle e (sc + val + (d - 1) * 140) bst⟩ .brk := by
    rw [hrlit, execStmt_if_false (hmate (F + 22)) rfl]
    simpa using hb5
  -- the null arm
  have hvirt : execStmt sunfish (F + 28) ⟨w, e⟩ sbVirt
      = .ok ⟨w, envSettle e (sc + val + (d - 1) * 140) bst⟩ .brk := by
    rw [hvlit, execStmt_if_false (hisNone (F + 24) v0 v1 v2) rfl]
    have ho : vo.toList = [sbReal] := by
      have := sbVirtElse_split
      rw [hvlit] at this
      simpa using this
    rw [ho]
    exact execStmts_singleton_flow (F := F + 25) (by simpa using hreal)
  -- and the chain's head
  rw [hslit, execStmt_if_false
    (m := sunfish) (F := F + 29) (st₁ := ⟨w, e⟩) (v := .bool false)
    (by
      rw [evalExpr]
      exact boolChain_and_falsy (F := F + 27) (hisNone (F + 24) s0 s1 s2) rfl) rfl]
  have hel : sbElse1.toArray.toList = [sbVirt] := by simp [sbElse1_split]
  rw [hel]
  exact execStmts_singleton_flow (F := F + 27) (by simpa using hvirt)


/-- The spec-side fold of a one-settle schedule: `max` and nothing else. -/
theorem settle_folds (gamma bst capv : Int) (live : Bool) :
    (foldFrom gamma bst live [settledCap capv]).1 = max bst capv := by
  rw [show settledCap capv = Round.settle capv from rfl, foldFrom_cons_settle]

/-- **R3a's spec half — `Report` at a one-settle schedule.** `hfut` is
discharged by the cap being the round's OWN: the schedule has exactly one
`settle` and it is `capv`, so the futility premise is the single hypothesis
`value ≤ capv` rather than a quantified bet. `Sound` comes free from the
interpreter's own break condition `capv < gamma`. -/
theorem settle_report (gamma value bst capv : Int) (live : Bool)
    (hb : Sound gamma value bst) (hlt : capv < gamma) (hfut : value ≤ capv) :
    Report gamma (foldFrom gamma bst live [settledCap capv]).1 value := by
  refine fold_report hb ?_ (Or.inr ⟨settledCap capv, by simp, hfut⟩) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact Or.inl hlt
  · intro cap hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rw [show settledCap capv = Round.settle capv from rfl] at hm
    cases hm
    exact hfut

/-- **AND THE TWO HALVES AGREE.** The interpreter leaves `max bst capv` in
`best`; the schedule `[settledCap capv]` folds to the same number. One line, and
it is what makes R3a mean something rather than merely typecheck. -/
theorem settle_agrees (gamma bst capv : Int) (live : Bool) (e : REnv) :
    Env.lookup (envSettle e capv bst) "best"
      = some (.int (foldFrom gamma bst live [settledCap capv]).1) := by
  rw [settle_folds]
  simp [envSettle, Env.lookup_set_self]

/-! ### The settle arm, INSTANTIATED on the fixture -/

/-- The top row of the ordering line at depth `d`, on the opening position. -/
private def fxTopVal (d : Int) : Option Int :=
  match evalExpr sunfish 512
      ⟨initWorld sunfish, [("pos", posH 0), ("depth", .int d)]⟩ ordLine with
  | .ok st (RVal.ref a) =>
    (match Heap.get? st.world.heap a with
     | some (Obj.list xs) =>
       (match xs[0]?.getD RVal.none with
        | RVal.tuple #[RVal.int v, _] => some v
        | _ => Option.none)
     | _ => Option.none)
  | _ => Option.none

private def fxGlob (n : String) : Option Int :=
  match Env.lookup (initWorld sunfish).globals n with
  | some (RVal.int z) => some z | _ => Option.none

/-! The best move on the opening board is worth **46**, and `pos.score` is `0` —
so at depth 1 the cap is `0 + 46 + (1-1)*140 = 46`, which is `settle_round`'s
`hcut` at every window above it. -/
#guard fxTopVal 1 == some 46
#guard (0 : Int) + 46 + (1 - 1) * 140 == 46
#guard (decide ((46 : Int) < 47) : Bool)

/-! `hband` — the top value is far below the mate band, which the live world
supplies (`MATE_LOWER` is statically POISONED, so it is a world premise). -/
#guard (match fxGlob "MATE_LOWER" with | some ml => decide ((46 : Int) < ml) | _ => false)

/-! **And the two halves agree on the engine's own answer.** `settle_round`
leaves `best = max (-MATE_UPPER) 46`; `settle_folds` says the schedule
`[settledCap 46]` folds to the same; and the shipped `bound()` answers `46` in
ONE node at `gamma = 47`. -/
#guard (match fxGlob "MATE_UPPER" with | some mu => max (-mu) 46 == 46 | _ => false)
#guard (match fxGlob "MATE_UPPER" with
        | some mu => (foldFrom 47 (-mu) false [settledCap 46]).1 == 46 | _ => false)

/-! ## §5 R3b's CENSUS, taken — `int()` is NOT lowered

R3b's price turns on
`move_depth = depth - 1 - (guard and depth >= 6 and val < LMR) - int(nmr)`, and
§L32 named the open question: did the extractor lower `int()` or leave it a call?
**It left it a call** — `sbMoveDepth_lit` pins
`.call (.name "int" _) #[.name "nmr" _]` — so the line needs the interpreter's
`int` builtin on a Bool, and it needs `Int - Bool` as well, because the `and`
chain's value is a Bool and it is SUBTRACTED.

Both are implemented, measured below. So `move_depth` is ordinary arithmetic once
its two boolean operands are decided, and **R3b's cost is the child call rather
than the reduction** — which is the opposite of what the source text suggests.

`int` is also not shadowed: no global, no function, no class, no namedtuple. -/

private def evAt (e : Expr) (env : REnv) : Option RVal :=
  match evalExpr sunfish 64 ⟨initWorld sunfish, env⟩ e with
  | .ok _ v => some v | _ => Option.none

private def spz : Span := ⟨0, 0, 0, 0⟩

/-! `int(False)` is `0` and `int(True)` is `1` — the builtin coerces. -/
#guard evAt (.call (.name "int" spz) #[.name "nmr" spz] #[] Option.none spz)
  [("nmr", .bool false)] == some (RVal.int 0)
#guard evAt (.call (.name "int" spz) #[.name "nmr" spz] #[] Option.none spz)
  [("nmr", .bool true)] == some (RVal.int 1)

/-! And `Int - Bool` coerces too, which is what the LMR subtrahend needs. -/
#guard evAt (.binOp (.name "d" spz) .sub (.name "g" spz) spz)
  [("d", .int 1), ("g", .bool false)] == some (RVal.int 1)
#guard evAt (.binOp (.name "d" spz) .sub (.name "g" spz) spz)
  [("d", .int 1), ("g", .bool true)] == some (RVal.int 0)

/-! `int` is the builtin, not a shadow. -/
#guard (lookupG (moduleGlobals sunfish).1 "int").isNone
  && !(findFunction sunfish "int").isSome
  && !(findClass sunfish "int").isSome
  && !(findNamedTuple sunfish "int").isSome

/-! **And the child's depth at depth 1 is `0`.** `guard and depth >= 6 and …`
dies on its second operand and `nmr` on its own second, so both subtrahends are
`False` and `move_depth = 1 - 1 - 0 - 0`. That is inside `RecursionStepW`'s
`∀ e, 0 ≤ e → e < d`, which is what the strong form was landed for. -/
#guard (1 : Int) - 1 - 0 - 0 == 0

#print axioms qsaG
#print axioms cap_line_low
#print axioms sbVirtElse_split
#print axioms break_fires
#print axioms settle_round
#print axioms settle_folds
#print axioms settle_report
#print axioms settle_agrees


/-! ## §6 R3b — THE REDUCTION AND THE `live` UPDATE

The two halves of the searched round that are NOT the call. §5's census said the
reduction would be cheap and it is: below depth 6 both subtrahends are `False` —
the LMR chain dies on its second operand, or on its first when `guard` is falsy,
and `nmr` is `False` at every node the census reaches — so `move_depth` is
`depth - 1` and the child sits at `0` when the parent sits at `1`.

`sbMoveDepth_lit` leaves the LMR chain existential and this arm COMPUTES with it,
so it gets the sharper pin (§L28's law 5), and the chain is decided by casing on
`guard` rather than by an altitude lemma: all three operands are simple, so
`py_simp` can walk them once the case is fixed. That is the exception the `nmr`
gate's docstring predicts — the explosion there was a RECURSIVE third operand.

`live |= score > -MATE_UPPER` is the round's only other non-call statement, and
`MATE_UPPER` is statically POISONED, so it comes off `w.globals`. -/

/-! `int`'s module-level residues, in `maxG`/`minG`'s shape — the builtin the
reduction line reaches because ingestion did NOT lower `int()` (§L33). -/
theorem intG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "int"
    = Option.none := rfl
theorem intF : findFunction sunfish "int" = Option.none := rfl
theorem intNotFun : ¬ ∃ x, x ∈ sunfish.functions ∧ x.name = "int" := by
  simpa [findFunction] using intF
theorem intCls : findClassAux sunfish.classes.toList "int" 0 = Option.none := rfl
theorem intNT : findNamedTupleAux sunfish.namedtuples.toList "int" = Option.none := rfl

/-- The reduction line, body SPELLED — the LMR chain is COMPUTED with, so
`sbMoveDepth_lit`'s existential `r` cannot serve (§L28's law 5). -/
theorem sbMoveDepth_sharp : ∃ a b c d e f g h i k l m n o p q r t, sbMoveDepth =
    .assign #[.name "move_depth" a]
      (.binOp (.binOp (.binOp (.name "depth" b) .sub (.constant (.int 1) c) d)
          .sub
          (.boolOp .and #[.name "guard" e,
            .compare (.name "depth" f) #[.gtE] #[.constant (.int 6) g] h,
            .compare (.name "val" i) #[.lt] #[.name "LMR" k] l] m) n)
        .sub (.call (.name "int" o) #[.name "nmr" p] #[] Option.none q) r) t :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem sbLive_sharp : ∃ a b c d e f, sbLive =
    .augAssign (.name "live" a) .bitOr
      (.compare (.name "score" b) #[.gt]
        #[.unaryOp .usub (.name "MATE_UPPER" c) d] e) f :=
  ⟨_, _, _, _, _, _, rfl⟩

/-- **R3b's reduction gate.** Below depth 6 both subtrahends are `False`: the
LMR chain dies on its second operand (or its first, if `guard` is falsy) and
`nmr` is `False` at every node the census reaches. `int()` is a CALL — not
lowered (§L33) — and both coercions are the interpreter's own, so the line is
ordinary arithmetic and the child's depth is `depth - 1`. -/
theorem move_depth_low (w : World) (e : REnv) (d : Int) (gv : Bool) (F : Nat)
    (hd : Env.lookup e "depth" = some (.int d))
    (hg : Env.lookup e "guard" = some (.bool gv))
    (hnmr : Env.lookup e "nmr" = some (.bool false))
    (hni : Env.lookup e "int" = Option.none)
    (hd6 : d < 6) :
    execStmt sunfish (F + 20) ⟨w, e⟩ sbMoveDepth
      = .ok ⟨w, Env.set e "move_depth" (.int (d - 1))⟩ .next := by
  obtain ⟨a, b, c, d', e', f, g, h, i, k, l, m, n, o, p, q, r, t, hlit⟩ := sbMoveDepth_sharp
  rw [hlit]
  cases gv
  · py_simp [-globalsFold, -globalsStep, hd, hg, hnmr, hni, intG, intNotFun, intCls, intNT,
      if_neg (show ¬ (6 : Int) ≤ d by omega)]
  · py_simp [-globalsFold, -globalsStep, hd, hg, hnmr, hni, intG, intNotFun, intCls, intNT,
      if_neg (show ¬ (6 : Int) ≤ d by omega)]

/-- **R3b's `live` gate.** `live |= score > -MATE_UPPER` — a bitwise-or
augAssign on two Bools, and `MATE_UPPER` is statically POISONED so it comes off
`w.globals`. -/
theorem live_updates (w : World) (e : REnv) (scv mu : Int) (lv : Bool) (F : Nat)
    (hs : Env.lookup e "score" = some (.int scv))
    (hl : Env.lookup e "live" = some (.bool lv))
    (hnmu : Env.lookup e "MATE_UPPER" = Option.none)
    (hmuw : Env.lookup w.globals "MATE_UPPER" = some (.int mu)) :
    execStmt sunfish (F + 12) ⟨w, e⟩ sbLive
      = .ok ⟨w, Env.set e "live" (.bool (lv || decide (-mu < scv)))⟩ .next := by
  obtain ⟨a, b, c, d, e', f, hlit⟩ := sbLive_sharp
  rw [hlit]
  by_cases hlt : -mu < scv
  · py_simp [-globalsFold, -globalsStep, hs, hl, hnmu, hmuw, muG, if_pos hlt,
      decide_eq_true hlt]
  · py_simp [-globalsFold, -globalsStep, hs, hl, hnmu, hmuw, muG, if_neg hlt,
      decide_eq_false hlt]

/-! ## §7 R3b's CALL HALF — censused, not yet proved

The searched round's remaining statement is
`score = min(cap, -self.bound(pos.move(move), 1 - gamma, move_depth))`, and it is
the one place in the fold where the world MOVES twice inside one expression. Its
census is taken here so the next pass starts from measurements rather than from
the source text; the gate itself is deliberately not attempted, because a
half-proved call gate is worse than none.

**What was measured**, on the live engine:

* `pos.move(move)` allocates **exactly one object** (heap 66 → 67) and decides at
  **32** fuel — 16 times out. Its plan is `.instMethod "Position.move"` on a
  `Position` VALUE, the same namedtuple route `Position.value` takes (§L29's
  `value_call_evals`), so the bridge is the same shape one notch out;
* `self.bound(…)` on the shipped `Searcher()` instance resolves to
  `.instMethod "Searcher.bound"` through `attrCallPlan` — an INSTANCE `.ref`,
  not a namedtuple, so it is a different plan function from `pos.move`'s and the
  two cannot share a lemma;
* `Searcher.bound` takes **five** parameters and the call site passes **four**:
  `root` rides its default. So the arity check the call bridge runs is
  `arityOk f.params 4`, not `= 5`;
* `min` is the builtin, unshadowed.

**The shape the gate will take.** Three `EvalsIn` steps threaded through one
`EvalsInList` — the receiver `self`, then the argument list whose FIRST element
allocates — then the child call, then `unaryOp .usub`, then `min`. The child's
answer enters as a hypothesis in the same threshold form R1's `ValueAnswers` and
§L31's `hdrain` use, and `searchedMove_sound` is what consumes it at the spec
side. `order_line_sorts` (§L31) is the worked precedent for an expression whose
argument list moves the world; the difference is that there the mover was a
generator allocation and here it is a whole recursive search.

**Why it is a session and not a tail.** `pos.move(move)` allocating means the
child call's world is `w` plus one object, and the child's own world is that plus
whatever the subtree wrote — so the statement's out-world is two hops from its
in-world and every later premise in the round has to be restated at the second
hop. That is the same bookkeeping `SubtreeWrites` will need at R3e, and doing it
once, carefully, is worth more than doing it twice. -/

private def mvR (i j : Int) : RVal :=
  .ntuple "Move" #["i", "j", "prom"] #[.int i, .int j, .str ""]

private def mvHeap (F : Nat) : Option (Nat × Nat) :=
  match callIn sunfish F (initWorld sunfish) "Position.move" #[posH 0, mvR 84 64] with
  | .ok w (RVal.ntuple "Position" _ _) => some ((initWorld sunfish).heap.size, w.heap.size)
  | _ => Option.none

/-! `pos.move(move)` allocates exactly one object, and 32 fuel decides it. -/
#guard mvHeap 32 == some (66, 67)
#guard (mvHeap 16).isNone

/-! The two plans, and they are different functions: a namedtuple VALUE's method
against an instance `.ref`'s. -/
#guard (match ntupleCallPlan sunfish "Position"
          #["board", "score", "wc", "bc", "ep", "kp"] "move" with
        | .instMethod q => q == "Position.move" | _ => false)
#guard (match searcherW with
        | some (w, a) =>
          (match attrCallPlan sunfish w.heap a "bound" with
           | .instMethod q => q == "Searcher.bound" | _ => false)
        | _ => false)

/-! `Searcher.bound` takes five parameters and the call site passes four —
`root` rides its default, so the bridge's arity check is at 4. -/
#guard (match findFunction sunfish "Searcher.bound" with
        | some f => f.params.size == 5 && arityOk f.params 4 && f.argsOk && f.localsOk
            && !f.isGenerator && !f.hasGlobal
        | none => false)

#print axioms intG
#print axioms intNotFun
#print axioms sbMoveDepth_sharp
#print axioms sbLive_sharp
#print axioms move_depth_low
#print axioms live_updates


end Examples.python.sunfish.fold_depth1
