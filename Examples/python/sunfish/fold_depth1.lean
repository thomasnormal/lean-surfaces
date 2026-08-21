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
  maxG maxNotFun maxCls maxNT mlG posCAux posCls_methods posCls_ntBase_isSome
  execStmt_if_true execStmt_if_false execStmts_singleton_flow
  Round Sound Report foldFrom settledCap fold_report foldFrom_cons_settle
  sbMoveDepth sbLive sbSearch searcherObj searchedMove searchedMove_sound
  minG minNotFun minCls minNT muG boolChain_and3 Exit fold mateUpper
  foldFrom_nil foldFrom_cons_next foldFrom_cons_cut
  sbCorr sbCorr_noElse sbStore sbStore_lit sbEvict sbRet tableSize
  entryDefault entryOf tpKey entryG entryNotFun entryClsAux entryNTAux
  evict_dead ret_best corr_dead
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

*That census is TAKEN — §9 below, and it answers twice.* On this fixture the
fold **never** exhausts (the band's two ends are the wrong way round, and round
ONE is the reason). Off it exhaustion is reachable in two flavours, so `Inv []`
is not `False` and `live` cannot be pinned. Three consequences for `Inv`, one of
them a theorem (`foldFrom_ran_no_settle`), are recorded there.

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

/-! ## §7 R3b's CALL HALF — the census it was built from

The searched round's remaining statement is
`score = min(cap, -self.bound(pos.move(move), 1 - gamma, move_depth))`, and it is
the one place in the fold where the world MOVES twice inside one expression. This
section is the census the gate was built from; **the gate itself is §8**, and the
measurements below are what it takes as premises rather than guesses.

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

**The shape the gate was PREDICTED to take, and did not.** This section used to
say: three `EvalsIn` steps threaded through one `EvalsInList` — the receiver, the
argument list whose first element allocates, the child call, `unaryOp .usub`,
`min` — with `order_line_sorts` (§L31) as the precedent. Those five steps are
exactly what the interpreter walks, and §8 does walk them; what it does NOT need
is the judgment. See §8's first finding: `EvalsIn` buys the ability to hand a
moved world BETWEEN gates, and this statement is ONE gate.

**The two hops are real.** `pos.move(move)` allocating means the child call's
world is `w` plus one object, and the child's own world is that plus whatever the
subtree wrote — so the statement's out-world is two hops from its in-world and
every later premise in the round has to be restated at the second hop. That is
the same bookkeeping `SubtreeWrites` will need at R3e. -/

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


/-! ## §8 R3b — THE CALL GATE, LANDED

`score = min(cap, -self.bound(pos.move(move), 1 - gamma, move_depth))` in one
statement gate, over a free world, with the two nested calls as premises and the
answer `min cap (-child)` — which is `searchedMove cap child`'s score on the
schedule side, so the interpreter and §3's fold agree on the searched round the
same way `settle_agrees` makes them agree on the settled one.

### Three findings, and each one moved the gate

**1. `EvalsIn` is for handing a moved world BETWEEN gates, not for moving it
INSIDE one.** §7 committed to three `EvalsIn` steps through an `EvalsInList`, and
four general lemmas were drafted for it (a non-generator namedtuple method, an
instance-`.ref` method, `usub`, the two-argument `min`). None is needed. The
judgment exists because `evalExpr`'s fuel has to be existentially quantified when
one theorem's conclusion becomes another theorem's hypothesis — that is exactly
`order_line_sorts` feeding `ord_stmt_emits`. Here the whole expression is a
SINGLE gate at a symbolic fuel `F`, so the two `callIn` premises can be stated
`∀ G, … (F + G) …` and one `py_simp` walks receiver, argument list, child call,
`usub` and `min` in one step. **The carryable rule: an `∀`-over-fuel-offset call
premise is the cheap substitute for `EvalsIn` whenever the mover and its consumer
are inside the same theorem.**

**2. The plan premise CANNOT be `attrCallPlan … = .instMethod …`** — the
computed-shape law (§L20) at a new place, and with a twist: `py_simp` UNFOLDS
`attrCallPlan`, and `-attrCallPlan` does not stop it, because simp's erase does
not remove a lemma the tactic itself puts in the list. So the census's one line
becomes **four premises in the residue's own spelling**: the heap slot
(`searcherObj`, `Heap.get?`-normalised the way `killer_misses` does it), the
class (`classAt`), the method's membership in `c.methods`, and the class NAME —
because the plan the interpreter builds is `c.name ++ "." ++ attr`, not a
constant. `pos.move`'s plan needs none of this: its receiver is a namedtuple
VALUE, so `ntupleCallPlan` computes.

**3. `posOf` must be unfolded IN THE PREMISE before `py_simp` runs.** Listing
`posOf` in the simp set unfolds it in the GOAL but not in `hmove`'s left-hand
side, and the rewrite then silently misses — the residue keeps a `callIn` with a
spelled-out `.ntuple` where the premise has `posOf`. `value_call_evals` (§L31)
closes the same trap one level out with `simpa only [posOf] using hcall`; here it
is `simp only [posOf] at hmove` before the walk. Costs one line, and without it
the whole gate looks unprovable.

### What the gate says, and what it leaves free

The world moves TWICE — `w` to `w₁` (the one object `pos.move` allocates) to `w₂`
(whatever the child's subtree wrote) — and both hops are NAMED rather than hidden
in an `∃`, which is §L26's law. Nothing about `w₂` is claimed here: it is the
child's own out-world, and the round's later premises (`live_updates`' `MATE_UPPER`
read) are stated at it. -/

/-- The searched round's call statement, body SPELLED — the gate computes with
every operand, so `sbSearch` gets the sharp pin (§L28's law 5). -/
theorem sbSearch_sharp : ∃ a b c d e f g h i k l m n o p q t, sbSearch =
    .assign #[.name "score" a]
      (.call (.name "min" b)
        #[.name "cap" c,
          .unaryOp .usub
            (.call (.attribute (.name "self" d) "bound" e)
              #[.call (.attribute (.name "pos" f) "move" g) #[.name "move" h] #[] Option.none i,
                .binOp (.constant (.int 1) k) .sub (.name "gamma" l) m,
                .name "move_depth" n] #[] Option.none o) p]
        #[] Option.none q) t :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- **R3b's CALL GATE.** The child search, from source text to a bound `score`,
over a free world and a free frame.

The receiver `self` is an instance `.ref`, so the plan comes off the heap slot,
the class and the class's own name (finding 2); `pos.move(move)` is a namedtuple
method whose plan computes, and it is the argument that ALLOCATES, so the child
call runs at `w₁` and the statement lands at `w₂`. Both calls enter as premises
quantified over the fuel OFFSET, which is what lets one walk cross them
(finding 1). -/
theorem search_line (w w₁ w₂ : World) (e : REnv) (ci : ClassId) (scls : ClassDefn)
    (sa ts tm hs : Addr) (nd dl sft : Int)
    (capv gamma md r : Int) (mvv pv : RVal)
    (b : String) (sc ep kp : Int) (wc0 wc1 bc0 bc1 : Bool) (F : Nat)
    (hself : Env.lookup e "self" = some (.ref sa))
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hmv : Env.lookup e "move" = some mvv)
    (hcap : Env.lookup e "cap" = some (.int capv))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hmd : Env.lookup e "move_depth" = some (.int md))
    (hnomin : Env.lookup e "min" = Option.none)
    (hobj : Heap.get? w.heap sa = some (searcherObj ci ts tm hs nd dl sft))
    (hcl : classAt sunfish.classes.toList ci = some scls)
    (hmeth : "bound" ∈ scls.methods)
    (hnm : scls.name = "Searcher")
    (hmove : ∀ G : Nat, callIn sunfish (F + G) w "Position.move"
      #[posOf b sc wc0 wc1 bc0 bc1 ep kp, mvv] = .ok w₁ pv)
    (hchild : ∀ G : Nat, callIn sunfish (F + G) w₁ "Searcher.bound"
      #[.ref sa, pv, .int (1 - gamma), .int md] = .ok w₂ (.int r)) :
    execStmt sunfish (F + 20) ⟨w, e⟩ sbSearch
      = .ok ⟨w₂, Env.set e "score" (.int (min capv (-r)))⟩ .next := by
  obtain ⟨a, b', c, d, e', f, g, h, i, k, l, m, n, o, p, q, t, hlit⟩ := sbSearch_sharp
  simp only [Heap.get?] at hobj
  simp only [posOf] at hmove
  rw [hlit]
  py_simp [-globalsFold, -globalsStep, hself, hpos, hmv, hcap, hg, hmd,
    hnomin, hobj, hcl, hmeth, hnm, searcherObj, hmove, hchild,
    minG, minNotFun, minCls, minNT,
    posOf, posCAux, posCls_methods, posCls_ntBase_isSome]

/-- **AND THE TWO HALVES AGREE**, `settle_agrees`' twin for a searched round: the
frame the gate leaves holds exactly the number `searchedMove cap child` scores. -/
theorem search_agrees (capv r : Int) (e : REnv) :
    Env.lookup (Env.set e "score" (.int (min capv (-r)))) "score"
      = some (.int (searchedMove capv r).score) := by
  simp [searchedMove, Round.score, Env.lookup_set_self]

/-- **THE IH, CONSUMED.** The child's own contract at the flipped window is what
makes the round `Sound`, and `searchedMove_sound` (§L16) is the consumer — stated
here at the number the gate actually produces. At depth 1 the child sits at
`move_depth = 0` (`move_depth_low`), inside `RecursionStepW`'s
`∀ e, 0 ≤ e → e < d`, which is the whole reason the strong form was landed. -/
theorem search_sound {gamma capv childReport childValue value : Int}
    (hchild : Report (1 - gamma) childReport childValue)
    (hneg : -childValue ≤ value) :
    Sound gamma value (min capv (-childReport)) :=
  searchedMove_sound (cap := capv) hchild hneg

/-! ### The call gate, INSTANTIATED on the `gamma ≤ 0` census row

§0 measured that row as **answer 0 in two nodes**, heap 70 → 247. Those two nodes
are this gate: the parent's round, and the child it searches. Every premise is
checked separately on the live fixture below, then the conclusion. -/

/-- `pos.move(Move(84, 64))` at the SEARCHER's world — the top row of the ordering
line (§4's `fxTopVal`), and the one object it allocates. -/
private def mvAtW (F : Nat) : Option Nat :=
  match searcherW with
  | some (w, _) =>
    (match callIn sunfish F w "Position.move" #[posH 0, mvR 84 64] with
     | .ok w' (RVal.ntuple "Position" _ _) => some w'.heap.size
     | _ => Option.none)
  | _ => Option.none

/-! `hmove` on the fixture: heap **70 → 71**, and 32 fuel decides it (16 times
out) — the same one object §7 measured at `initWorld`. -/
#guard mvAtW 32 == some 71
#guard (mvAtW 16).isNone

/-- `self.bound(pos.move(move), 1 - 0, 0)` — the child, at the world the move
left. -/
private def childAtW (F : Nat) : Option (Int × Nat) :=
  match searcherW with
  | some (w, a) =>
    (match callIn sunfish 32 w "Position.move" #[posH 0, mvR 84 64] with
     | .ok w₁ pv =>
       (match callIn sunfish F w₁ "Searcher.bound" #[.ref a, pv, .int 1, .int 0] with
        | .ok w₂ (RVal.int rr) => some (rr, w₂.heap.size)
        | _ => Option.none)
     | _ => Option.none)
  | _ => Option.none

/-! `hchild` on the fixture: the child **answers 0** and leaves the heap at 159;
**512** fuel decides it and 256 times out. That is the second of the row's two
nodes, and the exit law's measurement for the second hop. -/
#guard childAtW 512 == some (0, 159)
#guard (childAtW 256).isNone

/-! `hobj`/`hcl`/`hmeth`/`hnm` on the fixture: the live instance's class is
`Searcher` and `bound` is one of its methods — the four premises finding 2
replaced the one-line plan with. -/
#guard (match searcherW with
        | some (w, a) =>
          (match Heap.get? w.heap a with
           | some (Obj.instance ci _) =>
             (match classAt sunfish.classes.toList ci with
              | some c => c.name == "Searcher" && c.methods.toList.contains "bound"
              | _ => false)
           | _ => false)
        | _ => false)

/-! And the conclusion: the cap is 46 (§4), the child answered 0, so the round's
score is `min 46 (-0) = 0` — which is `searchedMove 46 0`'s score, and which
`max (-MATE_UPPER) 0 = 0` folds to the number the shipped `bound()` returns at
`gamma = 0` in TWO nodes (§0's guard). -/
#guard min (46 : Int) (-0) == 0
#guard (searchedMove 46 0).score == 0
#guard (match fxGlob "MATE_UPPER" with | some mu => max (-mu) (0 : Int) == 0 | _ => false)

#print axioms sbSearch_sharp
#print axioms search_line
#print axioms search_agrees
#print axioms search_sound

/-! ### What R3b still owes, named at the statement that owes it

The searched round's five statements are all gated now (`cap_line_low`,
`break_fires`'s skip arm is the one-line twin of §4's, `move_depth_low`,
`search_line`, `live_updates`), and the two the fold runs AFTER the round are not:
`best = max(best, score)` is `qs_max` at the second hop, but **the cutoff is not
free at depth 1** the way it is at depth 0. `sbKill_lit`'s guard is
`move is not None and depth`, and at a real move with `depth = 1` BOTH conjuncts
hold — so `self.tp_move[pos] = move` runs, and behind it the eviction guard
`len(self.tp_move) > TABLE_SIZE` that §L27 recorded as `BoundWF.room`. `qs_cut`
cannot serve: its `hm` premise is `move is None`.

That is a heap WRITE inside the round, which puts it with R3e's allocation arm
rather than with this gate — and it is the honest edge this pass stops at. -/


/-! ## §9 R3c's EXHAUSTION CENSUS — ANSWERED, and it answers TWICE

§L32 left exactly one measurement owed and named the gate that needs it: *"does
the depth-1 fold ever EXHAUST on the fixture? … Take it before writing `Inv []`."*
Both halves are measured now, and they do not give the same answer.

**The band, written down first.** The fold exhausts at `gamma` iff no round
settles and no round cuts, i.e.

    max_m min(cap_m, -child_m)  <  gamma  ≤  min_m cap_m

— the right-hand end because the sorted stream's LAST cap must still clear the
window, the left-hand end because no prefix maximum may reach it.

### On the FIXTURE: NEVER — and round ONE is the reason, not a scan

`pos.score` is 0 at depth 1, so `cap_m = val_m`, and the ordering line's bottom
row is **-5**: every `gamma > -5` settles. At `gamma ≤ -5` the fold does not
settle — and it does not need to, because the FIRST round already scores 0 and
`0 ≥ gamma`, so it CUTS. Two nodes, at every window from -5 down to -20000.
`min_m cap_m` is -5 and the best move's score is 0: the band's two ends are the
wrong way round, by 5 points, on this board.

Scanned on the shipped engine over `gamma ∈ [-1000, 1000]`: **1038 cut, 963
settled, ZERO ran.**

### Off the fixture: REACHABLE, in two flavours

1. **Terminal (`live = False`) — checkmate.** `1. f3 e5 2. g4 Qh4#`, four plies of
   the shipped `Position.move`, pinned below. 19 rows, `pos.score = -69`, caps in
   `[-93, -23]`. At `gamma = -93` every round is a `searchedMove`, every child
   answers `MATE_UPPER` (the opponent captures the king), so every score is
   `-MATE_UPPER`, `live` stays **False**, and the fold RUNS OUT after 19 rounds —
   20 nodes, answer -47938. The band here is `1 - MATE_UPPER < gamma ≤ -93`,
   **69 197 integers wide**, against the fixture's empty one.
2. **Non-terminal (`live = True`).** A self-play position 32 rows wide exhausts on
   `gamma ∈ [39, 56]` (18 integers) with `best = 38`: every move's true value is
   below the WORST move's static cap, so the futility bet is loose on all of them
   at once. Measured on the shipped engine only — it is 119 nodes and is not
   reproduced here.

### FOUR consequences for `Inv`, and one of them is a theorem

* **`Inv []` is reachable, so it is not `False`** — §L25's prediction confirmed at
  depth 1, and confirmed OFF the fixture rather than on it.
* **`live` must be a real variable.** Both flavours occur, so the invariant cannot
  pin it either way.
* **No `settle` can precede exhaustion** — `foldFrom_ran_no_settle` below, and it
  is a theorem about the walk rather than a measurement: a `.settle` at the head
  returns `Exit.settled`. So **`fold_report`'s `hfut` is VACUOUS on the `Exit.ran`
  arm** (`fold_report_ran`): the futility bet §L27 called the hard premise is
  empty exactly where `Inv []` lives. 2160 classified runs agree, and did not
  have to.
* **THE WARNING, and it is a sequencing fact.** At `live = False` the tail
  REWRITES the fold's number: the fold leaves `-MATE_UPPER` and the shipped
  `bound()` returns `max(1 - MATE_UPPER, -MATE_LOWER - depth * EVAL_ROUGHNESS)`,
  which at depth 1 is **-47938**. So **an `Exit.ran` `Report` is NOT a statement
  about `bound()`'s return until R3d's correction lands.** `Inv` may not be
  written as though it were.

### Evidence strength, stated

The fixture verdict is a 2001-window scan PLUS a round-one argument that needs
only two numbers (`min cap = -5`, `score₁ = 0`); it is measured, not proved. The
reachability verdict is a construction — a played position with its band computed
— and the mate row is reproduced by the Lean interpreter as well as by the shipped
engine, though it is recorded rather than guarded (45 s — see below). The
`no settle` consequence is the only one that is proved.

**Placement note.** `foldFrom_ran_no_settle` and `fold_report_ran` are about
`fold` and belong beside `foldFrom_ran_ge` in `bound_depth.lean` §7; they are here
because that file is the 3 m 25 s one and a sibling lane is editing it. Migrating
them is a move, not an argument. -/

theorem foldFrom_ran_no_settle : ∀ (rs : List Round) (gamma best : Int) (live : Bool),
    (foldFrom gamma best live rs).2.2 = Exit.ran → ∀ cap, Round.settle cap ∉ rs
  | [], _, _, _, _, _ => by simp
  | .settle _ :: _, gamma, best, live, hran, _ => by
      rw [foldFrom_cons_settle] at hran; exact absurd hran (by simp)
  | .report sc lv :: rs, gamma, best, live, hran, cap => by
      by_cases hc : gamma ≤ max best sc
      · rw [foldFrom_cons_cut gamma best live lv sc rs hc] at hran
        exact absurd hran (by simp)
      · rw [foldFrom_cons_next gamma best live lv sc rs hc] at hran
        have := foldFrom_ran_no_settle rs gamma (max best sc) (live || lv) hran cap
        simpa using this

/-- **The exhausting arm's `Report` needs NO futility premise.** `fold_report`'s
`hfut` quantifies over the schedule's `settle` rounds and an exhausting schedule
has none — so R3c's hardest-looking premise is discharged by the exit itself. -/
theorem fold_report_ran {gamma value best : Int} {live : Bool} {rs : List Round}
    (hran : (foldFrom gamma best live rs).2.2 = Exit.ran)
    (hb : Sound gamma value best) (hrs : ∀ r ∈ rs, Sound gamma value r.score)
    (hattain : value ≤ best ∨ ∃ r ∈ rs, value ≤ r.score) :
    Report gamma (foldFrom gamma best live rs).1 value :=
  fold_report hb hrs hattain
    (fun cap hm => absurd hm (foldFrom_ran_no_settle rs gamma best live hran cap))

/-! ### The census, RUN -/

/-- The BOTTOM row of the ordering line at depth `d` — `fxTopVal`'s twin, and the
largest `gamma` that settles nothing. -/
private def fxBotVal (d : Int) : Option Int :=
  match evalExpr sunfish 512
      ⟨initWorld sunfish, [("pos", posH 0), ("depth", .int d)]⟩ ordLine with
  | .ok st (RVal.ref a) =>
    (match Heap.get? st.world.heap a with
     | some (Obj.list xs) =>
       (match xs.toList.getLast? with
        | some (RVal.tuple #[RVal.int v, _]) => some v
        | _ => Option.none)
     | _ => Option.none)
  | _ => Option.none

/-! The band's right-hand end on the fixture: `min_m cap_m = -5`. -/
#guard fxBotVal 1 == some (-5)

/-! And its left-hand end is ABOVE that: at every window from the bottom cap down,
the fold still cuts on round ONE — two nodes, answer 0. The band is empty. -/
#guard probe (-5) 1 300 == some (0, 2, 70, 247)
#guard probe (-40) 1 300 == some (0, 2, 70, 247)
#guard probe (-1000) 1 300 == some (0, 2, 70, 247)

/-- The board `1. f3 e5 2. g4 Qh4#` leaves, cached as a literal and PINNED to the
plies by one guard (§L28's law 8). -/
def mateBoard : String :=
  "         \n         \n rnb.kbnr\n pppp.ppp\n ........\n ....p...\n ......Pq\n .....P..\n PPPPP..P\n RNBQKBNR\n         \n         \n"

/-- Fool's mate, from White's side: the fold's terminal exhaustion fixture. -/
def posMate : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str mateBoard, .int (-69), .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

private def ply (p : Option RVal) (i j : Int) : Option RVal :=
  match p with
  | some pv =>
    (match callIn sunfish 64 (initWorld sunfish) "Position.move" #[pv, mvR i j] with
     | .ok _ v => some v | _ => Option.none)
  | Option.none => Option.none

/-! The literal is the shipped `Position.move`'s own answer, four plies deep —
`f2f3`, `e7e5`, `g2g4`, `d8h4` in the mover's frame. -/
#guard ply (ply (ply (ply (some (posH 0)) 86 76) 84 64) 87 67) 95 51 == some posMate

/-- The ordering line's VALUES at a position, descending — the engine's own
stream, read off the list `ordLine` allocates. -/
private def lineVals (p : RVal) (d : Int) : Option (List Int) :=
  match evalExpr sunfish 1024 ⟨initWorld sunfish, [("pos", p), ("depth", .int d)]⟩ ordLine with
  | .ok st (RVal.ref a) =>
    (match Heap.get? st.world.heap a with
     | some (Obj.list xs) =>
       some (xs.toList.filterMap (fun v => match v with
         | RVal.tuple #[RVal.int z, _] => some z | _ => Option.none))
     | _ => Option.none)
  | _ => Option.none

/-- The mate fixture's stream, CACHED as a literal and pinned by the one guard
below — a nullary `def` re-runs in every `#guard` that mentions it (§L28's
law 8), and this line is the expensive part of §9. -/
def mateVals : List Int :=
  [46, 42, 36, 35, 30, 26, 26, 17, 15, 12, 12, 9, 8, 5, 5, 3, 1, -5, -24]

#guard lineVals posMate 1 == some mateVals

/-! **19 rows**, and the caps are `pos.score + val` at `pos.score = -69`, so they
run `[-93, -23]`. Every window at or below **-93** therefore settles NOTHING —
the band's right-hand end, computed rather than asserted. -/
#guard mateVals.length == 19
#guard mateVals.map (fun v => -69 + v)
  == [-23, -27, -33, -34, -39, -43, -43, -52, -54, -57, -57, -60, -61,
      -64, -64, -66, -68, -74, -93]

/-! **EXHAUSTION, RUN — and NOT guarded, for the throughput law's own reason.**
At `gamma = -93` the depth-1 fold at `posMate` consumes all 19 rounds and cuts on
none of them: `bound()` answers **-47938** in **20 nodes**, this one and its
nineteen children. Every child answers `MATE_UPPER`, so every round scores
`-MATE_UPPER` and `live` stays False.

That row is **run on both instruments** — the shipped engine and, through
`Searcher.bound` on `searcherW`, this interpreter — and deliberately left
unguarded: it costs **45 s** of elaboration against 4 s for everything else in
§9, and §L32 made the same call for its own 34- and 41-node rows. What IS guarded
is the fixture it runs on (the pinned position and its stream), so the next inch
can instantiate `Inv []` on it without paying for the search twice.

The number the fold left in `best` is `-MATE_UPPER = -69290`; the number
`bound()` returned is `-47938`. The gap is the mate correction, in the constants'
own arithmetic: -/
#guard (match fxGlob "MATE_LOWER", fxGlob "MATE_UPPER" with
        | some ml, some mu => max (1 - mu) (-ml - 1 * 15) == -47938 && -mu == -69290
        | _, _ => false)

#print axioms foldFrom_ran_no_settle
#print axioms fold_report_ran


/-! ## §10 R3c's INVARIANT — the SPEC half, written against §9's census

§L25 asked for *"`Inv` carrying `(best, live)` and the rounds left"* and warned
that `Inv []` stops being `False`. §9 measured both halves of that, and this
section is the invariant those measurements imply. **It is the spec half only,
and its conclusion is about THE FOLD** — `foldFrom`'s number — *not* about what
`bound()` returns. §9's fourth consequence is why: at `live = False` the tail
rewrites the number, and until R3d lands, an `Exit.ran` `Report` that claimed to
be about `bound()` would be false.

### What the invariant carries, and the ONE field it does not

`RanInv` carries three things and deliberately not a fourth:

| field | why |
|---|---|
| `sound` | the accumulator is `Sound` — closed under `max`, which is the whole fold |
| `rounds` | every round still to come is `Sound` — one `searchedMove_sound` each |
| `attain` | the value is attained by the accumulator or by a round still to come |
| ~~futility~~ | **NOT carried** — see below |

The fourth row is the whole economy of this inch. `foldFrom_ran_no_settle` (§9)
says a schedule that reaches `Inv []` has no `settle` in it, so `fold_report`'s
`hfut` is vacuous there. §L27 called that premise the hard one; on this arm it
does not exist.

### The three obligations, and `Inv []` is DISCHARGED

* **step** — consuming one non-cutting `report` round preserves it, and the
  accumulator advances by `max`. That is `foldFrom_cons_next`'s side of the walk.
* **nil** — at the empty remainder `attain` collapses to `value ≤ best` and the
  `Report` falls out by trichotomy. **`Inv []` is discharged, not refuted** —
  which is exactly the difference from depth 0, where `QSInv []` is `False`.
* **run** — the whole schedule, through `fold_report` with `hfut` supplied by the
  exit rather than by the invariant.

### What the INTERPRETER half still owes

`PyStmtTriple.forGen` at a schedule of length > 1, with the world threaded
through each round's two hops (§8) and `Hands` handing the yields. Two things
gate it and neither is in this section: R2's `hdrain` (until it lands the
schedule is a free `sortedVs`, so no concrete round list can be named), and the
depth-1 cutoff's killer store, which is filed with R3e because it writes. -/

/-- **R3c's LOOP INVARIANT, spec side.** Three fields; the futility bet is not
one of them (§9). -/
structure RanInv (gamma value best : Int) (rs : List Round) : Prop where
  sound : Sound gamma value best
  rounds : ∀ r ∈ rs, Sound gamma value r.score
  attain : value ≤ best ∨ ∃ r ∈ rs, value ≤ r.score

/-- **THE STEP.** One non-cutting `report` round consumed, the accumulator
advanced by `max` — the invariant's half of `foldFrom_cons_next`. -/
theorem RanInv.step {gamma value best sc : Int} {lv : Bool} {rs : List Round}
    (h : RanInv gamma value best (.report sc lv :: rs)) :
    RanInv gamma value (max best sc) rs := by
  have h1 : Sound gamma value sc := by
    have := h.rounds (.report sc lv) (by simp)
    simpa [Round.score] using this
  refine ⟨h.sound.max h1, fun r hr => h.rounds r (by simp [hr]), ?_⟩
  rcases h.attain with hb | ⟨r, hr, hv⟩
  · exact Or.inl (by omega)
  · rcases List.mem_cons.mp hr with rfl | hr'
    · have hs : value ≤ sc := by simpa [Round.score] using hv
      exact Or.inl (by omega)
    · exact Or.inr ⟨r, hr', hv⟩

/-- **`Inv []` IS DISCHARGED** — the one thing depth 0 never had to do, because
`QSInv []` was `False` there. At the empty remainder `attain` collapses to
`value ≤ best` and the contract falls out by trichotomy on `best < gamma`. -/
theorem RanInv.nil {gamma value best : Int} (h : RanInv gamma value best []) :
    Report gamma best value := by
  have hv : value ≤ best := by
    rcases h.attain with hb | ⟨r, hr, -⟩
    · exact hb
    · exact absurd hr (by simp)
  by_cases hlt : best < gamma
  · exact Or.inl ⟨hlt, hv⟩
  · have hbv : best ≤ value := by
      rcases h.sound with h1 | h2
      · omega
      · exact h2
    exact Or.inr ⟨by omega, hbv⟩

/-- **AND THE WHOLE SCHEDULE.** The futility premise comes from the schedule
having no `settle` — which on the `ran` arm is `foldFrom_ran_no_settle`, not an
assumption the loop has to carry. -/
theorem RanInv.run {gamma value best : Int} {live : Bool} {rs : List Round}
    (h : RanInv gamma value best rs) (hns : ∀ cap, Round.settle cap ∉ rs) :
    Report gamma (foldFrom gamma best live rs).1 value :=
  fold_report h.sound h.rounds h.attain (fun cap hm => absurd hm (hns cap))

/-! ### The `ran` arm, INSTANTIATED on both of §9's flavours

The mate schedule's caps come off the stream this file EVALUATES (`mateVals`,
guarded in §9). The ordinary fixture's position is pinned to four plies of the
shipped `Position.move`, and its stream and child reports are RUN AND RECORDED
rather than guarded — 40 s and 32 depth-0 searches respectively, which is §9's
throughput call applied twice more. Every number below was produced by an
instrument, and which instrument is said at each one. -/

/-- The mate fixture's schedule: every child answers `MATE_UPPER`, so every round
scores `-MATE_UPPER`. -/
private def mateSched : List Round :=
  mateVals.map (fun v => searchedMove (-69 + v) mateUpper)

/-! It RUNS OUT, at `best = -MATE_UPPER` and `live = False` — flavour one, and the
flavour whose number R3d rewrites. -/
#guard foldFrom (-93) (-mateUpper) false mateSched == (-mateUpper, false, Exit.ran)

/-- The ordinary fixture — `pos.score = 112`, 32 rows — reached by four plies of
the shipped `Position.move` and cached as a literal (§L28's law 8). -/
def ranBoard : String :=
  "         \n         \n rnb.kbnr\n pp.ppppp\n ........\n q.P.....\n ........\n ........\n PPP.PPPP\n RNBQKBNR\n         \n         \n"

def posRan : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str ranBoard, .int 112, .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

#guard ply (ply (ply (ply (some (posH 0)) 84 64) 86 66) 64 53) 95 68 == some posRan

/-- Its stream. **RUN, not guarded**: `lineVals posRan 1` answers exactly this
list in the Lean interpreter and on the shipped engine, and it costs **40 s** on
its own — a queen and 32 moves against the opening board's 20. §9 made the same
call for its own expensive row, and the anchor that matters is above: the
POSITION is the shipped `Position.move`'s answer, four plies deep. -/
def ranVals : List Int :=
  [73, 67, 42, 37, 36, 31, 30, 30, 26, 23, 23, 23, 21, 17, 15, 12, 12, 12, 9, 8,
   8, 8, 5, 5, 2, 1, 1, 0, -3, -5, -6, -56]

/-! 32 rows, and the bottom cap is `112 + (-56) = 56` — the band's right end. -/
#guard ranVals.length == 32
#guard (ranVals.map (fun v => 112 + v)).foldl min 999 == 56

/-- The 32 child reports, MEASURED on the shipped engine at `gamma = 56` (window
`1 - 56`); most are `MATE_UPPER`, because after most moves the opponent captures
the king. -/
private def ranChildren : List Int :=
  [69290, 69290, 69290, 69290, -38, 69290, 69290, 69290, 69290, 69290,
   -25, 69290, -23, 69290, 69290, 69290, 69290, -14, 69290, 69290,
   69290, 69290, 69290, 69290, 69290, 69290, 69290, 69290, 69290, -37,
   -38, 69290]

#guard ranChildren.length == 32

private def ranSched : List Round :=
  (ranVals.zip ranChildren).map (fun p => searchedMove (112 + p.1) p.2)

/-! **Flavour two: it runs out at `best = 38` with `live = True`** — nothing
settles (the bottom cap IS `gamma`) and nothing cuts (the best score is 38 < 56).
This is the `ran` arm the invariant is for, and the flavour whose number the tail
leaves alone. -/
#guard foldFrom 56 (-mateUpper) false ranSched == (38, true, Exit.ran)

#print axioms RanInv.step
#print axioms RanInv.nil
#print axioms RanInv.run


/-! ## §11 R3d-i — THE TAIL AT DEPTH ≥ 1, ON THE ARM WHERE IT CHANGES NOTHING

§10 stopped at a `Report` about **the fold**, and §9's fourth consequence is why:
at `live = False` the tail rewrites the number. This section pays the other
arm — **`live = True`** — and there the tail is a no-op on the answer, so a
`ran`-arm `Report` about `foldFrom` becomes a `Report` about what `bound()`
returns. That is the upgrade R3d owes, delivered on the flavour §9's ordinary
fixture exhibits.

### The one gate that makes it cheap

`if depth and not live and all(pos.move(m).king_capture() for m in pos.gen_moves())`
— the `and` chain dies on its **second** operand when `live` is set, so the
third, a whole second `gen_moves` drain under `all(...)`, never runs.
`corr_skips_live` is that, at any non-zero depth, in twelve fuel. Depth 0's
`corr_dead` kills the same statement on the FIRST operand; these are the two
ways the correction is dead, and between them they cover every node except the
one R3d-ii owes.

### What the store needed: depth, unpinned

`store_runs` is stated at `depth = 0` — the key it writes is `tpKey pv 0`.
`store_runs_d` is the same gate with the depth free (`sbStoredAt` is `sbStored`
with the same generalisation), and the depth-0 gate is its `d := 0` instance.
Nothing in the proof cared; the pin was incidental.

### The eviction's premises live at the SECOND world, and that is the point

The store WRITES, so `evict_dead` — whose guard reads `len(self.tp_score)` —
runs in a world the store made. Its premises are therefore stated at
`w.heap.set ts (sbStoredAt …)`, not at `w`: **§L27's `BoundWF.room` bridge, in
the open.** `hroom` is the post-store size bound, in the residue's own spelling
(`dictStore`'s own array), because that is what the path leaves.

### One trap worth the line it costs

`tableSize` was not in the `open` list, so Lean **auto-bound it as an implicit
variable** and the theorem quietly became a statement about an arbitrary `Int`.
It typechecked; it only failed later, at the `evict_dead` application, as an
argument type mismatch a long way from the cause. *An auto-bound implicit is a
silent generalisation, and the symptom surfaces at the first place the real
constant is needed.*

### What R3d still owes

**R3d-ii — the correction that FIRES.** At `live = False` the third operand runs:
a second `gen_moves` drain, `pos.move(m).king_capture()` per move, and the `all`
builtin over a generator, then the mate/stalemate value
`max(1 - MATE_UPPER, -MATE_LOWER - depth * EVAL_ROUGHNESS)` — §9 measured it as
**-47938** at depth 1 on the mate fixture. That is the arm that rewrites the
number, and it is a session of its own. -/

/-- **GATE — the terminality correction is DEAD whenever `live`.** The `and`
chain dies on its SECOND operand, so the third — a whole second `gen_moves`
drain under `all(...)` — never runs. This is the arm §L43's ordinary flavour
needs, and it is the reason a `live = True` exhaustion leaves `bound()`'s number
alone. -/
theorem corr_skips_live (w : World) (e : REnv) (d : Int) (F : Nat)
    (hd : Env.lookup e "depth" = some (.int d))
    (hlive : Env.lookup e "live" = some (.bool true))
    (hd0 : d ≠ 0) :
    execStmt sunfish (F + 12) ⟨w, e⟩ sbCorr = .ok ⟨w, e⟩ .next := by
  obtain ⟨bx, bd, p0, p1, p2, p3, p4, p5, p6, h⟩ := sbCorr_noElse
  have h1 : evalExpr sunfish (F + 9) ⟨w, e⟩ (.name "depth" p0) = .ok ⟨w, e⟩ (.int d) := by
    py_simp [-globalsFold, -globalsStep, hd]
  have h2 : evalExpr sunfish (F + 8) ⟨w, e⟩ (.unaryOp .not (.name "live" p1) p2)
      = .ok ⟨w, e⟩ (.bool false) := by
    py_simp [-globalsFold, -globalsStep, hlive]
  have hb1 : truthyH w.heap (.int d) = .ok true := by
    simp [truthyH, truthy, hd0]
  have hc : evalExpr sunfish (F + 11) ⟨w, e⟩
      (.boolOp .and
        #[.name "depth" p0, .unaryOp .not (.name "live" p1) p2,
          .call (.name "all" p3) #[bx] #[] Option.none p4] p5)
        = .ok ⟨w, e⟩ (.bool false) := by
    rw [evalExpr]
    exact boolChain_and3 (F := F + 8) h1 hb1 h2 rfl
  rw [h, execStmt_if_false hc rfl]
  simp only [execStmts]

/-- The dict the store leaves at ANY depth — `sbStored`'s twin with the key's
depth free. -/
def sbStoredAt (es : Array (RVal × RVal)) (sv : Nat) (pv : RVal) (d sc : Int) : Obj :=
  .dict (dictStore es.toList (tpKey pv d) (entryOf sc mateUpper)).1.toArray
    (if (dictStore es.toList (tpKey pv d) (entryOf sc mateUpper)).2 = true then sv + 1 else sv)

/-- **GATE — the table store at a FREE depth.** `store_runs` with `depth`
unpinned; the depth-0 gate is its `d := 0` instance. -/
theorem store_runs_d (w : World) (e : REnv) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf sc gamma d : Int) (pv : RVal) (es : Array (RVal × RVal)) (sv : Nat)
    (hslf : Env.lookup e "self" = some (.ref sa))
    (hpos : Env.lookup e "pos" = some pv)
    (hd : Env.lookup e "depth" = some (.int d))
    (hb : Env.lookup e "best" = some (.int sc))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hen : Env.lookup e "entry" = some entryDefault)
    (hroot : Env.lookup e "root" = some (.bool false))
    (hnoe : Env.lookup e "Entry" = Option.none)
    (hobj : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict : Heap.get? w.heap ts = some (.dict es sv))
    (hlt : ts < w.heap.size)
    (hge : gamma ≤ sc) (hk : hashableKey pv = true) :
    execStmt sunfish 20 ⟨w, e⟩ sbStore
      = .ok ⟨{ w with heap := w.heap.set ts (sbStoredAt es sv pv d sc) hlt }, e⟩ .next := by
  obtain ⟨p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,
    hs'⟩ := sbStore_lit
  obtain ⟨sp, hnt⟩ := entryNTAux
  simp only [Heap.get?] at hobj hdict
  have hc : evalExpr sunfish 19 ⟨w, e⟩ (.unaryOp .not (.name "root" p0) p1)
      = .ok ⟨w, e⟩ (.bool true) := by
    py_simp [-globalsFold, -globalsStep, hroot]
  rw [hs', execStmt_if_true hc rfl]
  simp only [execStmts]
  py_simp [-globalsFold, -globalsStep, -heapStore, hk, hslf, hpos, hd, hb, hg, hen, hnoe,
    entryDefault, entryG, entryNotFun, entryClsAux, hnt, hobj, hdict, searcherObj, entryOf,
    tpKey, sbStoredAt, dif_pos hlt]
  rw [if_pos hge]
  py_simp [-globalsFold, -globalsStep, -heapStore, hk, hslf, hpos, hd, hb, hg, hen, hnoe,
    entryDefault, entryG, entryNotFun, entryClsAux, hnt, hobj, hdict, searcherObj, entryOf,
    tpKey, sbStoredAt, dif_pos hlt]
  rfl

/-- **R3d-i — THE TAIL AT DEPTH ≥ 1 WITH `live`, and it leaves the number
alone.** The correction is skipped on its second operand, the store writes the
entry, the eviction does not fire and the return hands back `best`. So a
`live = True` exhaustion's `Report` about the FOLD is a `Report` about
`bound()`'s own answer — which is precisely what §9's fourth consequence said
was NOT available at `live = False`.

The eviction's premises are stated at the POST-STORE world, because that is the
world it runs in and the store between them writes: §L27's `BoundWF.room`
bridge, made explicit rather than hidden. -/
theorem tail_runs_live (w : World) (e : REnv) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf sc gamma d : Int) (pv : RVal) (es : Array (RVal × RVal)) (sv : Nat)
    (hlt : ts < w.heap.size)
    (hslf : Env.lookup e "self" = some (.ref sa))
    (hpos : Env.lookup e "pos" = some pv)
    (hd : Env.lookup e "depth" = some (.int d))
    (hlive : Env.lookup e "live" = some (.bool true))
    (hb : Env.lookup e "best" = some (.int sc))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hen : Env.lookup e "entry" = some entryDefault)
    (hroot : Env.lookup e "root" = some (.bool false))
    (hnoe : Env.lookup e "Entry" = Option.none)
    (hnolen : Env.lookup e "len" = Option.none)
    (hnots : Env.lookup e "TABLE_SIZE" = Option.none)
    (hobj : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict : Heap.get? w.heap ts = some (.dict es sv))
    (hd0 : d ≠ 0) (hge : gamma ≤ sc) (hk : hashableKey pv = true)
    (hobj' : Heap.get? (w.heap.set ts (sbStoredAt es sv pv d sc) hlt) sa
      = some (searcherObj ci ts tm hs n dl sf))
    (hroom : ((dictStore es.toList (tpKey pv d) (entryOf sc mateUpper)).1.toArray.size : Int)
      ≤ tableSize) :
    execStmts sunfish 41 ⟨w, e⟩ [sbCorr, sbStore, sbEvict, sbRet]
      = .ok ⟨{ w with heap := w.heap.set ts (sbStoredAt es sv pv d sc) hlt }, e⟩
          (.ret (.int sc)) := by
  have hdict' : Heap.get? (w.heap.set ts (sbStoredAt es sv pv d sc) hlt) ts
      = some (.dict (dictStore es.toList (tpKey pv d) (entryOf sc mateUpper)).1.toArray
          (if (dictStore es.toList (tpKey pv d) (entryOf sc mateUpper)).2 = true then sv + 1
           else sv)) := by
    show Heap.get? (w.heap.set ts (sbStoredAt es sv pv d sc) hlt) ts
      = some (sbStoredAt es sv pv d sc)
    simp [Heap.get?, hlt]
  simp only [execStmts]
  rw [execStmt_mono (corr_skips_live w e d 28 hd hlive hd0) (by simp) 40 (by omega)]
  simp only [Run.bind]
  rw [execStmt_mono (store_runs_d w e ci sa ts tm hs n dl sf sc gamma d pv es sv
    hslf hpos hd hb hg hen hroot hnoe hobj hdict hlt hge hk) (by simp) 39 (by omega)]
  simp only []
  rw [execStmt_mono (evict_dead { w with heap := w.heap.set ts (sbStoredAt es sv pv d sc) hlt }
    e ci sa ts tm hs n dl sf
    (dictStore es.toList (tpKey pv d) (entryOf sc mateUpper)).1.toArray
    (if (dictStore es.toList (tpKey pv d) (entryOf sc mateUpper)).2 = true then sv + 1 else sv)
    hslf hnolen hnots hobj' hdict' hroom) (by simp) 38 (by omega)]
  simp only []
  rw [execStmt_mono (ret_best { w with heap := w.heap.set ts (sbStoredAt es sv pv d sc) hlt }
    e sc hb) (by simp) 37 (by omega)]


/-- **THE LOOP, CLOSED on the `live = True` arm.** `tail_runs_live` returns the
frame's `best`; `fold_report_ran` says that very number satisfies the shipped
contract, with no futility premise because the exit had no `settle` in it. Stated
as ONE theorem so the interpreter's answer and the model's claim cannot drift
apart — the two halves are about the same `(foldFrom gamma bst lv rs).1`, written
once and used on both sides.

**This is the sentence R3 has been building toward at depth 1**, and it is
carefully not more than it is: it holds where `live` is set, which §9 measured as
one of exhaustion's two flavours. The other is R3d-ii's. -/
theorem ran_live_answers (w : World) (e : REnv) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma d value bst : Int) (lv : Bool) (rs : List Round)
    (pv : RVal) (es : Array (RVal × RVal)) (sv : Nat)
    (hlt : ts < w.heap.size)
    (hslf : Env.lookup e "self" = some (.ref sa))
    (hpos : Env.lookup e "pos" = some pv)
    (hd : Env.lookup e "depth" = some (.int d))
    (hlive : Env.lookup e "live" = some (.bool true))
    (hb : Env.lookup e "best" = some (.int (foldFrom gamma bst lv rs).1))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hen : Env.lookup e "entry" = some entryDefault)
    (hroot : Env.lookup e "root" = some (.bool false))
    (hnoe : Env.lookup e "Entry" = Option.none)
    (hnolen : Env.lookup e "len" = Option.none)
    (hnots : Env.lookup e "TABLE_SIZE" = Option.none)
    (hobj : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict : Heap.get? w.heap ts = some (.dict es sv))
    (hd0 : d ≠ 0) (hge : gamma ≤ (foldFrom gamma bst lv rs).1) (hk : hashableKey pv = true)
    (hobj' : Heap.get? (w.heap.set ts
        (sbStoredAt es sv pv d (foldFrom gamma bst lv rs).1) hlt) sa
      = some (searcherObj ci ts tm hs n dl sf))
    (hroom : ((dictStore es.toList (tpKey pv d)
        (entryOf (foldFrom gamma bst lv rs).1 mateUpper)).1.toArray.size : Int) ≤ tableSize)
    (hran : (foldFrom gamma bst lv rs).2.2 = Exit.ran)
    (hinv : RanInv gamma value bst rs) :
    execStmts sunfish 41 ⟨w, e⟩ [sbCorr, sbStore, sbEvict, sbRet]
        = .ok ⟨{ w with heap := w.heap.set ts (sbStoredAt es sv pv d (foldFrom gamma bst lv rs).1) hlt }, e⟩
          (.ret (.int (foldFrom gamma bst lv rs).1))
      ∧ Report gamma (foldFrom gamma bst lv rs).1 value :=
  ⟨tail_runs_live w e ci sa ts tm hs n dl sf (foldFrom gamma bst lv rs).1 gamma d pv es sv
      hlt hslf hpos hd hlive hb hg hen hroot hnoe hnolen hnots hobj hdict hd0 hge hk
      hobj' hroom,
   fold_report_ran hran hinv.sound hinv.rounds hinv.attain⟩

#print axioms corr_skips_live
#print axioms store_runs_d
#print axioms tail_runs_live
#print axioms ran_live_answers


end Examples.python.sunfish.fold_depth1
