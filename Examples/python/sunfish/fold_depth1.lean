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
  sbNull_lit sbStand_lit compare_one boolChain_and_falsy)
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

### R3a — the SETTLE arm: one round, no recursion. *One session.*

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

### R3b — the CUT arm: one searched round, then the cutoff. *One session.*

`gamma ≤ 0`: the cap clears the window, the child is searched at
`move_depth = depth - 1 - (…) - int(nmr)`, and `best ≥ gamma` cuts — TWO nodes.
This is the cheapest schedule that **consumes the IH**, through
`searchedMove_sound` (already proved, §L16). The child's depth is
`depth - 1` at depth 1 with `guard` false and `nmr` false, which is `0` — inside
`RecursionStepW`'s strong hypothesis `∀ e, 0 ≤ e → e < d`, and that is the whole
reason the strong form was landed (§L26).

*Owed:* `move_depth`'s arithmetic gate (three subtractions, two of them boolean
coercions — `int(nmr)` and a parenthesised `and` chain, so the census question is
whether the extractor lowered `int()` or left it a call), and the child call's
`EvalsIn`, which allocates.

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


end Examples.python.sunfish.fold_depth1
