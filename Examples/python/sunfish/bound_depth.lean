/-
**Depth-bounded equivalences for the RAW shipped `bound()`** — step 2 of the
model-removal roadmap (docs/backlog.md §L10, re-pinned in §L15).

`Examples/python/sf_order/bound.lean` (§L9) proved `bound_probe`'s own fold on
the `sf_order` fixture and recorded the consumption note: *the fold's shape IS
the recursion shape* — an induction hypothesis at depth `d-1` is consumed as a
`Hands` schedule at depth `d`. This file takes that shape to the **shipped**
`Searcher.bound`, on `Examples/python/sunfish/sunfish.py`.

**RE-PINNED 2026-08-19 to engine master `e670434`** (`sunfish.py` `sha256
f6c481a6…`). The pass-7 fixture (`sha256 2142d9c2…`, engine `783b0d6`) had
drifted 33 commits; §L13 measured the drift and found the re-pin BLOCKED
rather than expensive (the shipped `moves()` captures `guard`, rebound after
the `def`, so the whole call answered `unsupported statement 'NestedDef'`),
and §L14 landed the closure-cell tier that unblocked it. The header this file
carried in between — a drift warning saying "not a theorem about TODAY's
engine master" — is retired: it is one again.

What #236 changed, and what it costs this file:

* `Searcher.bound` is **18 top-level statements**, not 13. `moves()` yields
  `(value, move)` PAIRS, `val_lower` is gone, and four new head statements
  (`killer`, `calm`/`guard`, `t`, `nmr`) sit between the probe and the fold —
  so every §0 pin from index 6 on moves. That is §0, re-projected.
* **The score is computed in the CONSUMER**, across five branches, and one of
  them BREAKS on a settled cap without touching `live` or the cutoff block.
  §3's fold vocabulary is therefore a different program, re-derived here
  against the new shape rather than patched: the walk is over ROUNDS (what the
  consumer makes of a yield), and it has TWO terminals.
* Everything the generator tier proves is unmoved (§L13 measured
  `gen_moves`/`value`/`move`/`rotate`/`king_capture`/`parse`/`render`
  byte-identical), and so is the whole TABLE shape — the probe
  (`entry = self.tp_score.get((pos, depth), Entry(-MATE_UPPER, MATE_UPPER))`),
  the store and `Entry = namedtuple("Entry", "lower upper")` are
  byte-identical in both versions. §6 wires step 3's calculus
  (`LeanModels/Python/DictCalc.lean`) to those three lines, which is what
  building it in the GENERAL layer bought.
* **§7 is the RECURSION RULE's spec side** (added 2026-08-19): the window
  contract `Report` — `formal/`'s `WindowReport`, restated and proved
  equivalent to the shipped docstring — the fold's bracket algebra, the two
  branches that consume an induction hypothesis, the table threaded through a
  whole body, and `BoundRefines`, the depth-indexed statement the induction
  runs on. It also records what the rule CANNOT have: without a futility
  premise the refinement is false, and `settle_needs_futility` is the
  schedule that refutes it.

The object is the real thing: eighteen statements, a node counter and a wall
clock on the receiver, two transposition dicts and a history set behind
attributes, a five-capture nested generator — one of them CELLED — that
RE-ENTERS `bound` on every searched move and on both null probes, a fold with
a table write inside its cutoff and an early break beside it, a terminality
correction carrying the mate distance, and a table store.
-/
import Examples.python.sunfish.genmoves_drain

namespace Examples.python.sunfish.bound_depth

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)

set_option maxRecDepth 100000

/-! ## §0 The program, projected

`Searcher.bound`'s eighteen statements, each READ OUT of the shipped module
and pinned by `rfl`. Nothing below is retyped: a changed program stops these
pins loudly. -/

/-- The span a projection falls back to. -/
def nowhere : Span := ⟨0, 0, 0, 0⟩

/-- Positional projection into a statement list. -/
def nth (n : Nat) (ss : List Stmt) : Stmt :=
  match n, ss with
  | 0, s :: _ => s
  | n + 1, _ :: r => nth n r
  | _, _ => .pass nowhere

/-- The shipped `Searcher.bound`, projected. -/
def sbF : FunctionDefn :=
  match findFunction sunfish "Searcher.bound" with
  | some f => f
  | none => ⟨"", #[], false, false, false, false, #[], nowhere⟩

/-- Its body — eighteen statements. -/
def sbB : List Stmt := sbF.body.toList

/-- The docstring — #236 rewrote it (the four exact promises), and the pin
below is span- AND text-blind on purpose. -/
def sbDoc : Stmt := nth 0 sbB
/-- `self.nodes += 1`. -/
def sbNodes : Stmt := nth 1 sbB
/-- `if self.nodes % 2048 == 0 and time.time() > self.deadline: raise Stop`. -/
def sbClock : Stmt := nth 2 sbB
/-- `depth = max(depth, 0)`. -/
def sbDepth : Stmt := nth 3 sbB
/-- `if pos.score <= -MATE_LOWER: return -MATE_UPPER`. -/
def sbMate : Stmt := nth 4 sbB
/-- `if not root:` — the table probe, the two bound returns, the repetition
truncation. -/
def sbProbe : Stmt := nth 5 sbB
/-- `killer = self.tp_move.get(pos)` — #236's first new statement: the killer
is read BEFORE the null probe, in case the recursive probe evicts it. -/
def sbKiller : Stmt := nth 6 sbB
/-- `def moves(): …` — the nested generator, five captures, one of them a
CELL (`guard`, written below the `def`). -/
def sbDef : Stmt := nth 7 sbB
/-- `calm = abs(pos.score) < 750 and any(c in pos.board for c in "RBNQ")` —
the ONE calmness test #236 lifted out of `moves()`. -/
def sbCalm : Stmt := nth 8 sbB
/-- `guard = not root and calm` — the celled capture, written AFTER the
`def` and read at the CALL. -/
def sbGuard : Stmt := nth 9 sbB
/-- `t = pos.score + NULL_MARGIN` — the deep-null probe's target. -/
def sbT : Stmt := nth 10 sbB
/-- `nmr = (calm and depth >= 6 and -self.bound(…) >= t)` — the fuel probe.
At a QS node the `depth >= 6` conjunct is false, so it never recurses. -/
def sbNmr : Stmt := nth 11 sbB
/-- `best, live = -MATE_UPPER, False`. -/
def sbAcc : Stmt := nth 12 sbB
/-- `for val, move in moves():` — the fold. The pair is `(value, move)`, in
that order: #236 turned it around. -/
def sbFor : Stmt := nth 13 sbB
/-- `if depth and not live and all(…): …` — the terminality correction. -/
def sbCorr : Stmt := nth 14 sbB
/-- `if not root: self.tp_score[pos, depth] = …` — the table store. -/
def sbStore : Stmt := nth 15 sbB
/-- `if len(self.tp_score) > TABLE_SIZE: del …` — the FIFO eviction. -/
def sbEvict : Stmt := nth 16 sbB
/-- `return best`. -/
def sbRet : Stmt := nth 17 sbB

theorem sbB_split : sbB =
    [sbDoc, sbNodes, sbClock, sbDepth, sbMate, sbProbe, sbKiller, sbDef,
     sbCalm, sbGuard, sbT, sbNmr, sbAcc, sbFor, sbCorr, sbStore, sbEvict,
     sbRet] := rfl

/-- The census as a NUMBER, so the 13 → 18 shift can never be silent again. -/
theorem sbB_length : sbB.length = 18 := rfl

/-! ### The head's five statements -/

theorem sbDoc_lit : ∃ (c : String) (s₁ s₂ : Span),
    sbDoc = .exprStmt (.constant (.str c) s₁) s₂ := ⟨_, _, _, rfl⟩

theorem sbNodes_lit : ∃ p0 p1 p2 p3, sbNodes =
    .augAssign (.attribute (.name "self" p0) "nodes" p1) .add
      (.constant (.int 1) p2) p3 := ⟨_, _, _, _, rfl⟩

/-- The clock guard. `time.time()` sits BEHIND an `and`, so a node count that
is not a multiple of 2048 never consults the world's clock trace — which is
the hypothesis every gate below carries instead of a reading. -/
theorem sbClock_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15, sbClock =
    .ifStmt
      (.boolOp .and
        #[.compare (.binOp (.attribute (.name "self" p0) "nodes" p1) .mod
            (.constant (.int 2048) p2) p3) #[.eq] #[.constant (.int 0) p4] p5,
          .compare (.call (.attribute (.name "time" p6) "time" p7) #[] #[] Option.none p8)
            #[.gt] #[.attribute (.name "self" p9) "deadline" p10] p11] p12)
      #[.raiseStmt (some (.name "Stop" p13)) Option.none p14] #[] p15 := ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem sbDepth_lit : ∃ p0 p1 p2 p3 p4 p5, sbDepth =
    .assign #[.name "depth" p0]
      (.call (.name "max" p1) #[.name "depth" p2, .constant (.int 0) p3] #[] Option.none p4) p5 := ⟨_, _, _, _, _, _, rfl⟩

theorem sbMate_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8, sbMate =
    .ifStmt (.compare (.attribute (.name "pos" p0) "score" p1) #[.ltE]
        #[.unaryOp .usub (.name "MATE_LOWER" p2) p3] p4)
      #[.ret (some (.unaryOp .usub (.name "MATE_UPPER" p5) p6)) p7] #[] p8 := ⟨_, _, _, _, _, _, _, _, _, rfl⟩

/-! ### The probe block

`sbProbe`'s four statements are projected separately: the gates below
case-split on the two bound returns and on the repetition test. All four are
byte-identical to the pass-7 fixture's. -/

/-- The four statements under `if not root:`. -/
def sbProbeB : List Stmt :=
  match sbProbe with | .ifStmt _ b _ _ => b.toList | _ => []
/-- `entry = self.tp_score.get((pos, depth), Entry(-MATE_UPPER, MATE_UPPER))`. -/
def sbEntry : Stmt := nth 0 sbProbeB
/-- `if entry.lower >= gamma: return entry.lower`. -/
def sbLo : Stmt := nth 1 sbProbeB
/-- `if entry.upper < gamma: return entry.upper`. -/
def sbUp : Stmt := nth 2 sbProbeB
/-- `if depth > 0 and pos in self.history: return 0`. -/
def sbRep : Stmt := nth 3 sbProbeB

theorem sbProbeB_split : sbProbeB = [sbEntry, sbLo, sbUp, sbRep] := rfl

theorem sbProbe_lit : ∃ p0 p1 p2, sbProbe =
    .ifStmt (.unaryOp .not (.name "root" p0) p1) sbProbeB.toArray #[] p2 := ⟨_, _, _, rfl⟩

theorem sbEntry_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13, sbEntry =
    .assign #[.name "entry" p0]
      (.call (.attribute (.attribute (.name "self" p1) "tp_score" p2) "get" p3)
        #[.tuple #[.name "pos" p4, .name "depth" p5] p6,
          .call (.name "Entry" p7)
            #[.unaryOp .usub (.name "MATE_UPPER" p8) p9, .name "MATE_UPPER" p10] #[]
            Option.none p11] #[] Option.none p12) p13 := ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem sbLo_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7, sbLo =
    .ifStmt (.compare (.attribute (.name "entry" p0) "lower" p1) #[.gtE]
        #[.name "gamma" p2] p3)
      #[.ret (some (.attribute (.name "entry" p4) "lower" p5)) p6] #[] p7 := ⟨_, _, _, _, _, _, _, _, rfl⟩

theorem sbUp_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7, sbUp =
    .ifStmt (.compare (.attribute (.name "entry" p0) "upper" p1) #[.lt]
        #[.name "gamma" p2] p3)
      #[.ret (some (.attribute (.name "entry" p4) "upper" p5)) p6] #[] p7 := ⟨_, _, _, _, _, _, _, _, rfl⟩

theorem sbRep_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10, sbRep =
    .ifStmt (.boolOp .and
        #[.compare (.name "depth" p0) #[.gt] #[.constant (.int 0) p1] p2,
          .compare (.name "pos" p3) #[.inOp] #[.attribute (.name "self" p4) "history" p5] p6] p7)
      #[.ret (some (.constant (.int 0) p8)) p9] #[] p10 := ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-! ### #236's four new head statements

They run between the probe and the fold, and each one is a reason the
statement census moved. `killer` feeds `moves()`; `calm` is the one calmness
test, split two ways by `guard`; `t` and `nmr` are the deep-null fuel probe,
which is the ONE recursive call `bound` makes outside the fold. -/

theorem sbKiller_lit : ∃ p0 p1 p2 p3 p4 p5 p6, sbKiller =
    .assign #[.name "killer" p0]
      (.call (.attribute (.attribute (.name "self" p1) "tp_move" p2) "get" p3)
        #[.name "pos" p4] #[] Option.none p5) p6 := ⟨_, _, _, _, _, _, _, rfl⟩

/-- `calm`'s piece probe is a LOWERED genexp (`<genexpr@3>`), so the second
conjunct is pinned existentially: what this file needs from it is that `calm`
is an `and` whose FIRST conjunct is the score band, and that nothing in it
reads the table. -/
theorem sbCalm_lit : ∃ (g : Expr) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Span), sbCalm =
    .assign #[.name "calm" p0]
      (.boolOp .and
        #[.compare (.call (.name "abs" p1) #[.attribute (.name "pos" p2) "score" p3] #[]
            Option.none p4) #[.lt] #[.constant (.int 750) p5] p6, g] p7) p8 :=
  ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩

/-- **The celled capture, in the source order that makes it one.** `guard` is
written HERE — below `def moves():` and above the first `moves()` call — so a
snapshot taken at the `def` would read an unbound name and the H7 tier
refused it outright (§L13). §L14's cell gives the name a heap slot addressed
under the directory key `<cell>guard`, allocated when the `def` runs and read
at the CALL, which is what makes this statement's position legal rather than
fatal. -/
theorem sbGuard_lit : ∃ p0 p1 p2 p3 p4 p5, sbGuard =
    .assign #[.name "guard" p0]
      (.boolOp .and #[.unaryOp .not (.name "root" p1) p2, .name "calm" p3] p4) p5 :=
  ⟨_, _, _, _, _, _, rfl⟩

theorem sbT_lit : ∃ p0 p1 p2 p3 p4 p5, sbT =
    .assign #[.name "t" p0]
      (.binOp (.attribute (.name "pos" p1) "score" p2) .add (.name "NULL_MARGIN" p3) p4) p5 :=
  ⟨_, _, _, _, _, _, rfl⟩

/-- **The deep-null fuel probe.** `depth >= 6` is the SECOND conjunct, so at
any node below depth 6 — every QS node included — the `and` short-circuits
before the recursive call and `nmr` is just `calm`'s truth value. That is what
keeps the depth-0 gate below free of a child. -/
theorem sbNmr_lit : ∃ (r : Expr) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Span), sbNmr =
    .assign #[.name "nmr" p0]
      (.boolOp .and
        #[.name "calm" p1,
          .compare (.name "depth" p2) #[.gtE] #[.constant (.int 6) p3] p4,
          .compare r #[.gtE] #[.name "t" p5] p6] p7) p8 :=
  ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩

/-! ### The accumulators, the fold, and the tail -/

theorem sbAcc_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7, sbAcc =
    .assign #[.tuple #[.name "best" p0, .name "live" p1] p2]
      (.tuple #[.unaryOp .usub (.name "MATE_UPPER" p3) p4, .constant (.bool false) p5] p6) p7 := ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- The fold's target, `(val, move)` — #236's order. -/
def sbTarget : Expr :=
  match sbFor with | .forStmt t _ _ _ _ => t | _ => .constant .none nowhere
/-- `moves()` — the closure call. -/
def sbMovesCall : Expr :=
  match sbFor with | .forStmt _ it _ _ _ => it | _ => .constant .none nowhere
/-- The fold's body — three statements. -/
def sbBody : List Stmt :=
  match sbFor with | .forStmt _ _ b _ _ => b.toList | _ => []
/-- `if move is None and depth == 0: … elif … else: …` — THE SCORE CHAIN,
#236's central move: the score is computed here, in the consumer, not in
`moves()`. -/
def sbScore : Stmt := nth 0 sbBody
/-- `best = max(best, score)` — byte-identical to pass 7's. -/
def sbMax : Stmt := nth 1 sbBody
/-- `if best >= gamma: …; break` — the beta cutoff, byte-identical to pass
7's. -/
def sbCut : Stmt := nth 2 sbBody
/-- The cutoff's body: the killer store, then `break`. -/
def sbCutB : List Stmt :=
  match sbCut with | .ifStmt _ b _ _ => b.toList | _ => []
/-- `if move is not None and depth:` — the DEPTH-GATED killer store. -/
def sbKill : Stmt := nth 0 sbCutB
/-- The killer store's body: the write, then the eviction guard. -/
def sbKillB : List Stmt :=
  match sbKill with | .ifStmt _ b _ _ => b.toList | _ => []

theorem sbBody_split : sbBody = [sbScore, sbMax, sbCut] := rfl
theorem sbCutB_split : ∃ s, sbCutB = [sbKill, .brk s] := ⟨_, rfl⟩

theorem sbFor_lit : ∃ sp, sbFor = .forStmt sbTarget sbMovesCall sbBody.toArray #[] sp :=
  ⟨_, rfl⟩
theorem sbTarget_lit : ∃ p0 p1 p2, sbTarget =
    .tuple #[.name "val" p0, .name "move" p1] p2 := ⟨_, _, _, rfl⟩
theorem sbMovesCall_lit : ∃ p0 p1, sbMovesCall =
    .call (.name "moves" p0) #[] #[] Option.none p1 := ⟨_, _, rfl⟩

/-! #### The score chain, branch by branch

Five branches, pinned as the nest the `elif` really is. The projections are
positional so a reordering stops them; the pins name the TEST of each branch
and leave the bodies existential where the body is another branch. -/

/-- Branch 1's body — `score = pos.score`, the QS stand-pat. -/
def sbB1 : List Stmt := match sbScore with | .ifStmt _ b _ _ => b.toList | _ => []
/-- The `elif` chain hanging off branch 1. -/
def sbElse1 : List Stmt := match sbScore with | .ifStmt _ _ o _ => o.toList | _ => []
/-- `elif move is None:` — the null-move arm. -/
def sbVirt : Stmt := nth 0 sbElse1
/-- The null arm's body: the CAP test. -/
def sbVirtB : List Stmt := match sbVirt with | .ifStmt _ b _ _ => b.toList | _ => []
/-- `else:` — the real-move arm. -/
def sbReal : Stmt := nth 0 (match sbVirt with | .ifStmt _ _ o _ => o.toList | _ => [])
/-- `if (cap := pos.score + EVAL_ROUGHNESS) >= gamma:` — branch 2 vs 3. -/
def sbCapPass : Stmt := nth 0 sbVirtB
/-- The real arm's body: `if val >= MATE_LOWER:` — branch 4 vs 5. -/
def sbMateVal : Stmt := sbReal
/-- Branch 5's statements: the cap, THE BREAK, the reduction, the search,
the `live` update. -/
def sbB5 : List Stmt := match sbReal with | .ifStmt _ _ o _ => o.toList | _ => []
/-- `cap = MATE_UPPER if depth > 3 else pos.score + val + max(depth-1,0)*QS_A`. -/
def sbCapLine : Stmt := nth 0 sbB5
/-- **`if cap < gamma: best = max(best, cap); break`** — #236's explicit
break, and the fold's SECOND terminal. -/
def sbBreak : Stmt := nth 1 sbB5
/-- `move_depth = depth - 1 - (guard and depth >= 6 and val < LMR) - int(nmr)`. -/
def sbMoveDepth : Stmt := nth 2 sbB5
/-- `score = min(cap, -self.bound(pos.move(move), 1 - gamma, move_depth))`. -/
def sbSearch : Stmt := nth 3 sbB5
/-- `live |= score > -MATE_UPPER`. -/
def sbLive : Stmt := nth 4 sbB5

theorem sbElse1_split : sbElse1 = [sbVirt] := rfl
theorem sbB5_split : sbB5 = [sbCapLine, sbBreak, sbMoveDepth, sbSearch, sbLive] := rfl

/-- **Branch 1's test** — `move is None and depth == 0`. The `depth == 0`
conjunct is what makes the QS stand-pat a LEAF: no cap, no child, no `live`. -/
theorem sbScore_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7, sbScore =
    .ifStmt (.boolOp .and
        #[.compare (.name "move" p0) #[.is] #[.constant Const.none p1] p2,
          .compare (.name "depth" p3) #[.eq] #[.constant (.int 0) p4] p5] p6)
      sbB1.toArray sbElse1.toArray p7 := ⟨_, _, _, _, _, _, _, _, rfl⟩

theorem sbB1_lit : ∃ p0 p1 p2 p3, sbB1 =
    [.assign #[.name "score" p0] (.attribute (.name "pos" p1) "score" p2) p3] :=
  ⟨_, _, _, _, rfl⟩

/-- **Branch 2/3's test** — `move is None`, i.e. a null-move pass at depth
≥ 1 (branch 1 already took the depth-0 case). -/
theorem sbVirt_lit : ∃ (o : Array Stmt) (p0 p1 p2 p3 : Span), sbVirt =
    .ifStmt (.compare (.name "move" p0) #[.is] #[.constant Const.none p1] p2)
      sbVirtB.toArray o p3 := ⟨_, _, _, _, _, rfl⟩

/-- **The pass's cap, and its WALRUS.** `(cap := pos.score + EVAL_ROUGHNESS)`
is `Expr.namedExpr` — §L14's tier item 3, the constructor the general walrus
needed. A cap below `gamma` answers the pass outright (branch 3); at or above
it, the child runs (branch 2). -/
theorem sbCapPass_lit : ∃ (b o : Array Stmt) (p0 p1 p2 p3 p4 p5 p6 p7 : Span), sbCapPass =
    .ifStmt (.compare
        (.namedExpr "cap"
          (.binOp (.attribute (.name "pos" p0) "score" p1) .add
            (.name "EVAL_ROUGHNESS" p2) p3) p4)
        #[.gtE] #[.name "gamma" p5] p6) b o p7 := ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩

/-- **Branch 4/5's test** — `val >= MATE_LOWER`, the intrinsic king capture:
an exact `MATE_UPPER` token and `live`, never a search. -/
theorem sbReal_lit : ∃ (b : Array Stmt) (p0 p1 p2 p3 : Span), sbReal =
    .ifStmt (.compare (.name "val" p0) #[.gtE] #[.name "MATE_LOWER" p1] p2)
      b sbB5.toArray p3 := ⟨_, _, _, _, _, rfl⟩

/-- **The futility cap.** Above depth 3 there is none (`MATE_UPPER`); at or
below it the cap is `pos.score + val + max(depth - 1, 0) * QS_A`, and at a QS
node the third term is `0 * QS_A`. -/
theorem sbCapLine_lit :
    ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19, sbCapLine =
    .assign #[.name "cap" p0]
      (.ifExp (.compare (.name "depth" p1) #[.gt] #[.constant (.int 3) p2] p3)
        (.name "MATE_UPPER" p4)
        (.binOp (.binOp (.attribute (.name "pos" p5) "score" p6) .add (.name "val" p7) p8)
          .add
          (.binOp (.call (.name "max" p9)
              #[.binOp (.name "depth" p10) .sub (.constant (.int 1) p11) p12,
                .constant (.int 0) p13] #[] Option.none p14)
            .mult (.name "QS_A" p15) p16) p17) p18) p19 :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- **THE BREAK.** `if cap < gamma: best = max(best, cap); break`. Two facts
the fold's spec reads off this pin: the cap is folded with `max` (an earlier
report may be tighter), and the `break` leaves the round BEFORE `live` and
BEFORE the cutoff block — so a settled move witnesses no legality and stores
no killer. -/
theorem sbBreak_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10, sbBreak =
    .ifStmt (.compare (.name "cap" p0) #[.lt] #[.name "gamma" p1] p2)
      #[.assign #[.name "best" p3]
          (.call (.name "max" p4) #[.name "best" p5, .name "cap" p6] #[] Option.none p7) p8,
        .brk p9] #[] p10 := ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- The reduction: `depth - 1` minus the LMR bit minus `int(nmr)`. Both
subtrahends are booleans, so the child's depth is in `[depth - 3, depth - 1]`
— strictly below the parent's at every `depth ≥ 1` (`child_depth_lt`). -/
theorem sbMoveDepth_lit : ∃ (r : Expr) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Span), sbMoveDepth =
    .assign #[.name "move_depth" p0]
      (.binOp (.binOp (.binOp (.name "depth" p1) .sub (.constant (.int 1) p2) p3)
          .sub r p4)
        .sub (.call (.name "int" p5) #[.name "nmr" p6] #[] Option.none p7) p8) p9 :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem sbLive_lit : ∃ p0 p1 p2 p3 p4 p5, sbLive =
    .augAssign (.name "live" p0) .bitOr
      (.compare (.name "score" p1) #[.gt]
        #[.unaryOp .usub (.name "MATE_UPPER" p2) p3] p4) p5 :=
  ⟨_, _, _, _, _, _, rfl⟩

theorem sbMax_lit : ∃ p0 p1 p2 p3 p4 p5, sbMax =
    .assign #[.name "best" p0]
      (.call (.name "max" p1) #[.name "best" p2, .name "score" p3] #[] Option.none p4) p5 :=
  ⟨_, _, _, _, _, _, rfl⟩

theorem sbCut_lit : ∃ p0 p1 p2 p3, sbCut =
    .ifStmt (.compare (.name "best" p0) #[.gtE] #[.name "gamma" p1] p2)
      sbCutB.toArray #[] p3 := ⟨_, _, _, _, rfl⟩

/-- The killer store's GATE: `move is not None` **and `depth`** — at a QS node
(`depth == 0`) the second conjunct is falsy and the store never runs, which is
what makes the depth-0 fold heap-free. -/
theorem sbKill_lit : ∃ p0 p1 p2 p3 p4 p5, sbKill =
    .ifStmt (.boolOp .and
        #[.compare (.name "move" p0) #[.isNot] #[.constant Const.none p1] p2,
          .name "depth" p3] p4) sbKillB.toArray #[] p5 := ⟨_, _, _, _, _, _, rfl⟩

theorem sbCorr_lit : ∃ (b : Expr) (bd oe : Array Stmt) (p0 p1 p2 p3 p4 p5 p6 : Span), sbCorr =
    .ifStmt (.boolOp .and
        #[.name "depth" p0, .unaryOp .not (.name "live" p1) p2,
          .call (.name "all" p3) #[b] #[] Option.none p4] p5) bd oe p6 :=
  ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩

theorem sbStore_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23, sbStore =
    .ifStmt (.unaryOp .not (.name "root" p0) p1)
      #[.assign #[.subscript (.attribute (.name "self" p2) "tp_score" p3)
            (.tuple #[.name "pos" p4, .name "depth" p5] p6) p7]
          (.ifExp (.compare (.name "best" p8) #[.gtE] #[.name "gamma" p9] p10)
            (.call (.name "Entry" p11) #[.name "best" p12,
              .attribute (.name "entry" p13) "upper" p14] #[] Option.none p15)
            (.call (.name "Entry" p16) #[.attribute (.name "entry" p17) "lower" p18,
              .name "best" p19] #[] Option.none p20) p21) p22] #[] p23 := ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- The eviction guard, and the FIFO delete it hides. `del d[k]` is outside
the tier and ingests as `Stmt.unsupported`, so every gate below must show the
guard is FALSE rather than step through it — which is exactly what the shipped
`TABLE_SIZE = 10**6` buys. Both `del`s (this one and the `tp_move` one inside
the cutoff) are the WHOLE of `bound`'s unsupported census — §L14 measured two,
down from §L13's three, once the closure cell removed the `NestedDef`. -/
theorem sbEvict_lit : ∃ (b : Array Stmt) (p0 p1 p2 p3 p4 p5 p6 : Span), sbEvict =
    .ifStmt (.compare (.call (.name "len" p0)
        #[.attribute (.name "self" p1) "tp_score" p2] #[] Option.none p3) #[.gt]
        #[.name "TABLE_SIZE" p4] p5) b #[] p6 :=
  ⟨_, _, _, _, _, _, _, _, rfl⟩

theorem sbRet_lit : ∃ p0 p1, sbRet = .ret (some (.name "best" p0)) p1 := ⟨_, _, rfl⟩

/-- The five facts `callIn`'s function arm tests, and the two shapes the body
gates are stated in: the parameter list is `self, pos, gamma, depth, root` and
`root` carries its literal default `False`. Unchanged by #236 — which is why
§L14 could report the gates green before the pins moved. -/
theorem sbF_lit : findFunction sunfish "Searcher.bound" = some sbF ∧
    sbF.argsOk = true ∧ sbF.localsOk = true ∧ sbF.isGenerator = false ∧
    sbF.body.toList = sbB ∧ (5 : Nat) = sbF.params.size :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The nested generator's capture set, pinned.** Five names, and `guard`
carries the `<cell>` directory prefix that §L14's tier gives a capture rebound
between the `def` and the call. The pin is the tier item's own object: drop
the cell and this line stops. -/
theorem sbDef_captures : ∃ (ps : Array Param) (ao lo hg : Bool)
    (b : Array Stmt) (sp : Span), sbDef =
    .defStmt "moves" ps ao lo hg true b
      #["depth", "gamma", "<cell>guard", "killer", "pos"] sp :=
  ⟨_, _, _, _, _, _, rfl⟩

/-! ## §1 The constants, and the module-level resolutions

`MATE_LOWER`/`MATE_UPPER` are NOT G1 module constants: the shipped file
computes them from the `piece` dict (`piece["K"] - 13 * piece["Q"]`), a
subscript, so the constant fold answers `some none` for both and the values
come from the world's GLOBALS, where module-init execution put them. Every
gate below therefore takes them as lookups on `w.globals` — which is also
what makes them invariant along the recursion: `Searcher.bound` has no
`global` statement, so no call in the tree can move them. -/

theorem sbF_noGlobal : sbF.hasGlobal = false := rfl

/-- `MATE_LOWER`, as the shipped file computes it. -/
def mateLower : Int := 47923
/-- `MATE_UPPER`, as the shipped file computes it. -/
def mateUpper : Int := 69290
/-- `TABLE_SIZE` — a G1 constant, unlike the two above. -/
def tableSize : Int := 1000000
/-- `EVAL_ROUGHNESS` — the null-move pass's cap increment. -/
def evalRoughness : Int := 15
/-- `QS_A` — the futility slope. -/
def qsA : Int := 140
/-- `NULL_MARGIN` — #236's deep-null target offset, a G1 constant. -/
def nullMargin : Int := -200

/-! The values are the shipped file's own. They are checked by RUNNING
module init (`#guard`, the compiled evaluator) rather than pinned by a kernel
`rfl`: `initWorld sunfish` executes the 1MB top level, and reducing that in
the kernel is measured at over 4M heartbeats and an out-of-memory kill
(docs/backlog.md §L10 §the price). -/
#guard Env.lookup (initWorld sunfish).globals "MATE_LOWER" == some (.int mateLower)
#guard Env.lookup (initWorld sunfish).globals "MATE_UPPER" == some (.int mateUpper)
#guard Env.lookup (initWorld sunfish).globals "TABLE_SIZE" == some (.int tableSize)
#guard Env.lookup (initWorld sunfish).globals "EVAL_ROUGHNESS" == some (.int evalRoughness)
#guard Env.lookup (initWorld sunfish).globals "QS_A" == some (.int qsA)
#guard Env.lookup (initWorld sunfish).globals "NULL_MARGIN" == some (.int nullMargin)

/-! ### The pinned residues

§L8 finding 2: pin the residue the unfold set leaves rather than let it
unfold. `max`, `min` and `Entry` are the three names the head and the fold
resolve (`min` is new: #236's `min(cap, -self.bound(…))` is how both searching
branches apply their cap); each resolution walks the constant fold, the
function table, the class table and the namedtuple table, and each of those
steps is an `rfl` here. -/

theorem maxG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "max"
    = Option.none := rfl
theorem maxF : findFunction sunfish "max" = Option.none := rfl
theorem maxNotFun : ¬ ∃ x, x ∈ sunfish.functions ∧ x.name = "max" := by
  simpa [findFunction] using maxF
theorem maxCls : findClassAux sunfish.classes.toList "max" 0 = Option.none := rfl
theorem maxNT : findNamedTupleAux sunfish.namedtuples.toList "max" = Option.none := rfl

theorem minG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "min"
    = Option.none := rfl
theorem minF : findFunction sunfish "min" = Option.none := rfl
theorem minNotFun : ¬ ∃ x, x ∈ sunfish.functions ∧ x.name = "min" := by
  simpa [findFunction] using minF
theorem minCls : findClassAux sunfish.classes.toList "min" 0 = Option.none := rfl
theorem minNT : findNamedTupleAux sunfish.namedtuples.toList "min" = Option.none := rfl

theorem absG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "abs"
    = Option.none := rfl
theorem absF : findFunction sunfish "abs" = Option.none := rfl
theorem absNotFun : ¬ ∃ x, x ∈ sunfish.functions ∧ x.name = "abs" := by
  simpa [findFunction] using absF
theorem absCls : findClassAux sunfish.classes.toList "abs" 0 = Option.none := rfl
theorem absNT : findNamedTupleAux sunfish.namedtuples.toList "abs" = Option.none := rfl

theorem mlG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst
    "MATE_LOWER" = some Option.none := rfl
theorem muG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst
    "MATE_UPPER" = some Option.none := rfl

/-- **`NULL_MARGIN` is NOT poisoned** — measured, and it corrects a recorded
assumption. `MATE_LOWER`/`MATE_UPPER` are `some none` (bound but dirty, so the
live view decides), but `NULL_MARGIN`, like `QS` and `LMR`, survives the static
fold with its value. So `t = pos.score + NULL_MARGIN` needs NO hypothesis about
`w.globals`, and `QSStandPat`'s `NULL_MARGIN` premise is REDUNDANT. It stays
(AGENTS.md: never delete a hypothesis that turns out unneeded — record it), and
the record is here: it only weakens the statement, it does not falsify it. -/
theorem nmarG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst
    "NULL_MARGIN" = some (some (.int nullMargin)) := rfl

theorem entryG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst
    "Entry" = Option.none := rfl
theorem entryF : findFunction sunfish "Entry" = Option.none := rfl
theorem entryNotFun : ¬ ∃ x, x ∈ sunfish.functions ∧ x.name = "Entry" := by
  simpa [findFunction] using entryF
theorem entryClsAux : findClassAux sunfish.classes.toList "Entry" 0 = Option.none := rfl
/-- `Entry` IS a namedtuple: `Entry = namedtuple("Entry", "lower upper")`, and
the table answers with the two fields the table probe reads. Byte-identical to
pass 7's — the whole reason §7 below is a wiring job and not a proof. -/
theorem entryNTAux : ∃ sp, findNamedTupleAux sunfish.namedtuples.toList "Entry"
    = some ⟨"Entry", "Entry", #["lower", "upper"], sp⟩ := ⟨_, rfl⟩

/-! ### The shipped VALUES the table lines are about

The probe's default, the table key and the entry the store builds. They sit
with the constants because §4's head gates read them — §6's theorems are what
wires them to `DictCalc`, and that wiring is unchanged by where the values are
declared. -/

/-- The shipped probe's DEFAULT, as a value: `Entry(-MATE_UPPER, MATE_UPPER)`. -/
def entryDefault : RVal :=
  .ntuple "Entry" #["lower", "upper"] #[.int (-mateUpper), .int mateUpper]

/-- The shipped table KEY, as a value: the plain tuple `(pos, depth)`. -/
def tpKey (p : RVal) (d : Int) : RVal := .tuple #[p, .int d]

/-- An `Entry(lo, up)`, as the store builds it. -/
def entryOf (lo up : Int) : RVal := .ntuple "Entry" #["lower", "upper"] #[.int lo, .int up]

/-! ### The `Position` class, projected

An attribute read on a namedtuple-SUBCLASS value forks on `c.ntBase.isSome &&
attr ∈ c.methods` — methods shadow field properties, CPython's MRO — and
`py_simp` OPENS that guard rather than matching it (§L9 finding 3). So the
class is projected once and the guard is decided from the pinned method ARRAY.
`posCAux` must be in the simp set for the residue to reach the shape
`posCls.2.methods`; without it the surviving `match` is a different matcher
constant and no pin can fire. -/

/-- The shipped `Position`, projected off the class table. -/
def posCls : Nat × ClassDefn :=
  match findClassAux sunfish.classes.toList "Position" 0 with
  | some p => p
  | none => default

theorem posCAux : findClassAux sunfish.classes.toList "Position" 0 = some posCls := rfl

/-- **The five methods, and `score` is not one of them.** `score` is a FIELD
of the namedtuple base, so `pos.score` is a tuple index and not a bound-method
value — which is what the head's mate check and four of the fold's five
branches read. -/
theorem posCls_methods :
    posCls.2.methods = #["gen_moves", "rotate", "move", "value", "king_capture"] := rfl

/-- And the base is there, so the shipped `Position` really is the subclass
shape the guard is about — a class WITHOUT `ntBase` would make every gate
below true for the wrong reason. -/
theorem posCls_ntBase_isSome : posCls.2.ntBase.isSome = true := rfl

/-! ## §2 The receiver, and the frame

`Searcher.__init__` binds SIX attributes in this order; the two transposition
tables and the history set are heap objects behind them, so a gate that says
what `bound` does to the table says it about `ts`/`tm`, never about the
instance.

**Six, not five** — engine master's `__init__` is `self.nodes,
self.deadline, self.soft = 0, 1 << 63, 1 << 63`, and `soft` is the second
wall the UCI driver arms (`search()` reads it once per completed depth). It
is nothing to `bound`, which never mentions it, but a receiver shape that
omitted it would make every gate below VACUOUS rather than wrong — so the
shape is pinned against a real `Searcher()` immediately after it. -/

/-- The receiver as the gates see it. -/
def searcherObj (ci : ClassId) (ts tm hs : Addr) (nodes dl sft : Int) : Obj :=
  .instance ci #[("tp_score", .ref ts), ("tp_move", .ref tm), ("history", .ref hs),
                 ("nodes", .int nodes), ("deadline", .int dl), ("soft", .int sft)]

/-! **The shape is the engine's own.** A fresh `Searcher()` over the real
`initWorld` matches `searcherObj` at the three fresh addresses, with both
walls at `1 << 63`. This `#guard` is the non-vacuity check the gates below
stand on: drop an attribute and it stops, instead of the gates quietly
becoming statements about nothing. -/
#guard (match searcherW with
  | some (w, a) =>
    (match Heap.get? w.heap a with
     | some (.instance ci attrs) =>
       (match attrs.toList with
        | [("tp_score", .ref ts), ("tp_move", .ref tm), ("history", .ref hs),
           ("nodes", .int n), ("deadline", .int dl), ("soft", .int sf)] =>
          Heap.get? w.heap a == some (searcherObj ci ts tm hs n dl sf)
            && n == 0 && dl == 9223372036854775808 && sf == 9223372036854775808
        | _ => false)
     | _ => false)
  | Option.none => false)

/-- `Searcher.bound`'s entry frame: its five parameters, `root` filled from
its literal default. -/
def sbEnv0 (slf pv : RVal) (gamma depth : Int) : REnv :=
  [("self", slf), ("pos", pv), ("gamma", .int gamma), ("depth", .int depth),
   ("root", .bool false)]

/-- The entry frame IS what `callIn` builds for a four-argument call: the
default-filled `root` is the shipped signature's own, not a choice here.
Unchanged across the re-pin — #236 touched the body, never the signature. -/
theorem sbCallEnv (slf pv : RVal) (gamma depth : Int) :
    mkCallEnv sbF.params #[slf, pv, .int gamma, .int depth] = sbEnv0 slf pv gamma depth := rfl

/-! ## §3 The vocabulary of a QS fold — RE-DERIVED for #236

Pass 7's `moves()` handed the consumer a finished `(move, score)`, and the
fold was a three-line walk over scores. #236 turned the pair around and moved
the SCORING into the loop: `moves()` now yields `(value, move)` — a static
value and a move, both `None` for a virtual yield — and the consumer decides
what that is worth across five branches, one of which BREAKS.

So this section is not the old one patched. The walk is over **rounds** (what
the consumer makes of a yield), and it has **two** terminals, not one. -/

/-- One yield of the shipped `moves()`: `yield <value>, <move>`. Both are
`None` for a VIRTUAL yield — the null-move pass and the QS stand-pat — and a
real yield carries `.int v` beside its `Move`, which is exactly the
distinction the consumer's `move is None` tests and `live` tracks. -/
structure Yield where
  /-- The static value, or `None` for a virtual yield. -/
  val : RVal
  /-- The move, or `None` for a virtual yield. -/
  move : RVal

/-- The yield as the interpreter's value: the shipped tuple `(val, move)`. -/
def yieldVal (y : Yield) : RVal := .tuple #[y.val, y.move]

/-- **What the consumer makes of one yield.** Branches 1–4 and the SECOND arm
of branch 5 all end at a score plus a `live` contribution; branch 5's FIRST
arm folds a cap and leaves. Two constructors are the smallest thing that keeps
those apart, and keeping them apart is the point: a settled round writes no
killer, sets no `live`, and answers for every yield after it. -/
inductive Round where
  /-- Branches 1–4 and branch 5b: a score, and whether the round witnesses
  legality. -/
  | report (score : Int) (live : Bool)
  /-- Branch 5a: `cap < gamma` on the sorted stream — fold the cap with `max`
  and BREAK. -/
  | settle (cap : Int)
  deriving DecidableEq, Repr

/-- How the shipped fold LEFT the loop. `cut` is the beta cutoff at the bottom
of a round; `settled` is #236's early break; `ran` is `moves()` exhausted. -/
inductive Exit where
  /-- `moves()` ran out. -/
  | ran
  /-- `best >= gamma` at the bottom of a round. -/
  | cut
  /-- `cap < gamma` — the settled-cap break. -/
  | settled
  deriving DecidableEq, Repr

/-- **The walk the shipped fold performs.** Per round: a `settle` folds its cap
and leaves; a `report` raises `best` to the running maximum and `live` by its
own contribution, and STOPS if that lifts `best` to `gamma`. `.1` is the `best`
it ends with, `.2.1` the `live`, `.2.2` HOW it left.

This is the shipped loop and nothing else: the killer store inside the cutoff
is depth-gated (`sbKill_lit`) and does not run at a QS node, and the
correction and the table store are the tail's business, not the fold's. -/
def fold (gamma : Int) : Int → Bool → List Round → Int × Bool × Exit
  | best, live, [] => (best, live, .ran)
  | best, live, .settle cap :: _ => (max best cap, live, .settled)
  | best, live, .report sc lv :: rs =>
      if gamma ≤ max best sc then (max best sc, live || lv, .cut)
      else fold gamma (max best sc) (live || lv) rs

/-- The same walk from a running state — the loop invariant's handle on "what
the rounds still to come will answer". -/
def foldFrom (gamma best : Int) (live : Bool) (rs : List Round) : Int × Bool × Exit :=
  fold gamma best live rs

theorem foldFrom_nil (gamma best : Int) (live : Bool) :
    foldFrom gamma best live [] = (best, live, .ran) := rfl

theorem foldFrom_cons_next (gamma best : Int) (live lv : Bool) (sc : Int) (rs : List Round)
    (h : ¬ gamma ≤ max best sc) :
    foldFrom gamma best live (.report sc lv :: rs)
      = foldFrom gamma (max best sc) (live || lv) rs := by
  simp [foldFrom, fold, h]

theorem foldFrom_cons_cut (gamma best : Int) (live lv : Bool) (sc : Int) (rs : List Round)
    (h : gamma ≤ max best sc) :
    foldFrom gamma best live (.report sc lv :: rs) = (max best sc, live || lv, .cut) := by
  simp [foldFrom, fold, h]

/-- **The settled-cap break, spec-side.** It takes no hypothesis at all: the
round leaves whatever `gamma` is, because the shipped guard `cap < gamma` was
already decided when the round was CLASSIFIED. Nothing after it is looked at,
which is the sorted stream's payoff. -/
theorem foldFrom_cons_settle (gamma best cap : Int) (live : Bool) (rs : List Round) :
    foldFrom gamma best live (.settle cap :: rs) = (max best cap, live, .settled) := rfl

/-! ### The five branches, named

Each constructor below is one arm of `sbScore`, read off its pin. Together
they are the classification a `Hands` schedule has to supply for the fold to
be a statement about the shipped program rather than about a list. -/

/-- Branch 1 (`move is None and depth == 0`) — the QS stand-pat: the static
evaluation, and NO legality (a pass is not a move). -/
def standPat (sc : Int) : Round := .report sc false

/-- Branch 3 (`move is None`, `cap < gamma`) — the pass whose cap is already
below the window answers with the cap and needs no child report. -/
def cappedPass (cap : Int) : Round := .report cap false

/-- Branch 2 (`move is None`, `cap >= gamma`) — the pass that must be checked:
`min(cap, -child)`, and if that still meets the window AND `pos.king_capture()`
returns a move, the exact `MATE_UPPER` token replaces it and `live` is set.

**One effect this constructor does NOT carry**, recorded rather than hidden:
the shipped line is `move, score, live = proof, MATE_UPPER, True`, so it also
rebinds `move` — a virtual yield becomes a REAL one, and the cutoff block's
`move is not None and depth` gate can then fire and write `tp_move[pos]`. A
`Round` is what the FOLD sees (`best`, `live`, how it left), and the killer
store is a heap effect beside it, so the rebinding belongs to the depth-≥1
world-threading obligation (§5's list, item 1), not here. At depth 0 it cannot
arise at all: branch 1 takes every virtual yield. -/
def searchedPass (gamma cap child : Int) (proof : Bool) : Round :=
  if decide (gamma ≤ min cap (-child)) && proof then .report mateUpper true
  else .report (min cap (-child)) false

/-- Branch 4 (`val >= MATE_LOWER`) — an intrinsic mate-band value IS a king
capture: the exact token, never a search, and `live` outright. -/
def intrinsicMate : Round := .report mateUpper true

/-- Branch 5b — the searched real move: `min(cap, -child)`, and `live` iff the
report clears the illegal-move sentinel. -/
def searchedMove (cap child : Int) : Round :=
  .report (min cap (-child)) (decide (-mateUpper < min cap (-child)))

/-- Branch 5a — the settled cap. -/
def settledCap (cap : Int) : Round := .settle cap

/-- `live |= score > -MATE_UPPER`, spec-side — pass 7's `isLive` had to test
the MOVE as well because the score alone did not say whether a yield was
virtual. #236's branches decide that structurally, so the predicate is just
the sentinel test. -/
def isLive (sc : Int) : Bool := decide (-mateUpper < sc)

theorem searchedMove_live (cap child : Int) :
    searchedMove cap child = .report (min cap (-child)) (isLive (min cap (-child))) := rfl

/-! ### The two arithmetic shapes the branches carry -/

/-- A boolean in arithmetic position, CPython's coercion. -/
def bit (b : Bool) : Int := if b then 1 else 0

theorem bit_bounds (b : Bool) : 0 ≤ bit b ∧ bit b ≤ 1 := by cases b <;> simp [bit]

/-- **The futility cap** (`sbCapLine_lit`): no cap above depth 3, else the
static estimate `pos.score + val + max(depth - 1, 0) * QS_A`. -/
def moveCap (depth score val : Int) : Int :=
  if 3 < depth then mateUpper else score + val + max (depth - 1) 0 * qsA

/-- At a QS node the slope term vanishes and the cap is the plain sum — which
is what makes the depth-0 branch-5 arithmetic table-free. -/
theorem moveCap_qs (score val : Int) : moveCap 0 score val = score + val := by
  unfold moveCap
  rw [if_neg (by omega : ¬ ((3:Int) < 0)), show max ((0:Int) - 1) 0 = 0 from by omega]
  omega

/-- **The child's depth** (`sbMoveDepth_lit`): `depth - 1` minus the LMR bit
minus `int(nmr)`. -/
def moveDepth (depth : Int) (lmr nmr : Bool) : Int := depth - 1 - bit lmr - bit nmr

/-- **The child's KEY depth is strictly below the parent's — at every depth
≥ 1.** The child refloors with `depth = max(depth, 0)`, so what it stores
under is `max (moveDepth …) 0`, and both reductions only ever lower it. This
is the side condition `Bracket.SubtreeWrites`'s depth-separation arm needs
(§6), discharged for every reduction the shipped code can apply. -/
theorem child_depth_lt {depth : Int} (lmr nmr : Bool) (h : 1 ≤ depth) :
    max (moveDepth depth lmr nmr) 0 < depth := by
  have h1 := bit_bounds lmr
  have h2 := bit_bounds nmr
  unfold moveDepth
  omega

/-- The two null probes lower it too: the pass searches `depth - 3` and the
fuel probe `depth - 7`. -/
theorem pass_depth_lt {depth : Int} (h : 1 ≤ depth) : max (depth - 3) 0 < depth := by omega
theorem nmr_depth_lt {depth : Int} (h : 1 ≤ depth) : max (depth - 7) 0 < depth := by omega

/-- **And at depth 0 it is NOT.** `moveDepth 0 false false = -1`, which the
refloor sends straight back to `0`: a QS node's children store under the QS
node's OWN key. `SubtreeWrites`'s separation arm does not cover them, and that
is precisely why the depth-0 gate below carries a stand-pat hypothesis — it
cuts before any child runs, so there is nothing to separate. -/
theorem qs_child_depth_eq : max (moveDepth 0 false false) 0 = 0 := by
  unfold moveDepth bit; omega

/-- **The stand-pat cut, spec-side.** A schedule whose FIRST round already
meets the window ends there, whatever follows — which is the depth-0 arm the
model's `qsStrat` writes as `if gamma ≤ eval p then eval p`
(formal/Sunfish/Stalemate.lean). The fold never looks past it, so no statement
about the rest of `moves()` is needed to know the answer. -/
theorem fold_standpat (gamma sc : Int) (rs : List Round) (h : gamma ≤ sc) :
    foldFrom gamma (-mateUpper) false (standPat sc :: rs)
      = (max (-mateUpper) sc, false, .cut) := by
  have := foldFrom_cons_cut gamma (-mateUpper) false false sc rs (by omega)
  simpa [standPat] using this

/-- **The object's yield schedule**, world-threaded: stepping the generator at
`a` from world `w` hands over exactly `ys`, one `IterSteps` at a time, and
lands at `w'`.

The worlds are the whole point at depth ≥ 1. Under #236 the generator itself
is cheaper — it yields a static `(value, move)` and never recurses — but
`Hands` is unchanged, because the recursion moved into the CONSUMER and the
consumer's rounds are threaded by the same worlds. An induction hypothesis at
depth `d-1` is still consumed one `cons` at a time (docs/backlog.md §L9
finding 1, §L10 §the template); what changed is which side of the pair carries
the child's report. -/
inductive Hands (m : Module) (a : Addr) : World → List Yield → World → Prop
  /-- The empty schedule: no step taken, the world is where it was. -/
  | nil {w : World} : Hands m a w [] w
  /-- One yield, then the rest. -/
  | cons {w w₁ w₂ : World} {y : Yield} {ys : List Yield} :
      IterSteps m w a (some (yieldVal y)) w₁ → Hands m a w₁ ys w₂ →
      Hands m a w (y :: ys) w₂

/-- The frame slots the QS fold reads, as LOOKUPS, so every gate is blind to
the rest of the frame. `depth` is one of them: the killer store inside the
cutoff is gated on it, and pinning it to `0` is what makes the QS fold
heap-free. `nmr` joined the list with #236 — branch 5's `move_depth` reads it,
and at a QS node it is `False` because `depth >= 6` short-circuits the `and`
(`sbNmr_lit`). -/
def LoopFrame (e : REnv) (gamma best : Int) (live : Bool) : Prop :=
  Env.lookup e "gamma" = some (.int gamma) ∧
  Env.lookup e "best" = some (.int best) ∧
  Env.lookup e "live" = some (.bool live) ∧
  Env.lookup e "depth" = some (.int 0) ∧
  Env.lookup e "nmr" = some (.bool false)

/-- The frame with the loop target bound to a yield — `val` first, then
`move`, which is the order `sbTarget_lit` pins. -/
def bindYield (e : REnv) (y : Yield) : REnv :=
  Env.set (Env.set e "val" y.val) "move" y.move

/-- Binding `(val, move)` — an `rfl` on the projected target. -/
theorem bind_eq (h : Heap) (e : REnv) (y : Yield) :
    assignToH h e sbTarget (yieldVal y) = .ok (bindYield e y) := rfl

theorem lookup_bind_move (e : REnv) (y : Yield) :
    Env.lookup (bindYield e y) "move" = some y.move := by
  simp [bindYield, Env.lookup_set_self]
theorem lookup_bind_val (e : REnv) (y : Yield) :
    Env.lookup (bindYield e y) "val" = some y.val := by
  simp [bindYield, Env.lookup_set_self, Env.lookup_set_ne]
theorem lookup_bind_ne {e : REnv} {x : String} {v : RVal} (y : Yield)
    (hm : x ≠ "move") (hs : x ≠ "val") (h : Env.lookup e x = some v) :
    Env.lookup (bindYield e y) x = some v := by
  simp [bindYield, Env.lookup_set_ne, hm, hs, h]

/-! ## §4 Two gates on the shipped body

`bound_enters` is the head's first three statements; `max_evals` is the
fold's `best = max(best, score)`. Both are stated over a FREE world and a free
frame, both are what the depth-bounded gates compose, and both survived the
re-pin UNCHANGED — the statements they are about are byte-identical to pass
7's, which is the cheapest possible evidence that #236's blast radius is the
fold and not the head. -/

/-- **GATE 1 — entering `bound` counts a node and does NOT read the clock.**

`self.nodes += 1` is an attribute store through the receiver, and the very
next statement is `if self.nodes % 2048 == 0 and time.time() > self.deadline:
raise Stop`. `time.time()` sits behind the `and`, so a node count that is not
a multiple of 2048 never consults the world's clock trace — the trace is an
INPUT (docs/memory-model.md §the trace clock) and an empty one refuses
loudly, so this is the statement that says the refusal cannot happen below
the frontier. The frame is untouched and the only heap change is the counter. -/
theorem bound_enters (w : World) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma d : Int) (pv : RVal) (h' : Heap)
    (hself : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hupd : Heap.update w.heap sa (searcherObj ci ts tm hs (n + 1) dl sf) = some h')
    (hclk : ¬ ((n + 1).fmod 2048 = 0)) :
    execStmts sunfish 16 ⟨w, sbEnv0 (.ref sa) pv gamma d⟩ [sbDoc, sbNodes, sbClock]
      = .ok ⟨{ w with heap := h' }, sbEnv0 (.ref sa) pv gamma d⟩ .next := by
  obtain ⟨c, e₁, e₂, hdoc⟩ := sbDoc_lit
  obtain ⟨q0, q1, q2, q3, hn⟩ := sbNodes_lit
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, hck⟩ :=
    sbClock_lit
  have hself2 := Heap.get?_update_self hupd
  simp only [Heap.get?] at hself hself2
  simp only [Heap.update, searcherObj] at hupd
  rw [hdoc, hn, hck]
  py_simp [sbEnv0, hself, hself2, searcherObj, hupd, hclk]

/-- The fold's `max(best, score)` call, projected. -/
def maxE : Expr := match sbMax with | .assign _ v _ => v | _ => .constant .none nowhere

/-- **GATE 2 — the fold's running maximum.** `best = max(best, score)` on the
shipped file: the builtin resolution walks the constant fold, the function
table, the class table and the namedtuple table, and every step is a pinned
residue above rather than an unfolding of the 1MB literal. `hnomax` is the
frame's own honesty condition — `bound`'s body binds no name `max`, so the
builtin is what the call reaches. -/
theorem max_evals (w : World) (e : REnv) (b sc : Int)
    (hnomax : Env.lookup e "max" = Option.none)
    (hb : Env.lookup e "best" = some (.int b))
    (hs : Env.lookup e "score" = some (.int sc)) :
    evalExpr sunfish 8 ⟨w, e⟩ maxE = .ok ⟨w, e⟩ (.int (max b sc)) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, hmax⟩ := sbMax_lit
  have hme : maxE = .call (.name "max" x1) #[.name "best" x2, .name "score" x3] #[]
      Option.none x4 := by simp only [maxE, hmax]
  rw [hme]
  py_simp [-globalsFold, -globalsStep, hnomax, hb, hs, maxG, maxNotFun, maxCls, maxNT]

/-! ### The head's remaining statements, and the probe block

§L10 priced the rest of the head as *"one gate per statement, each with its
module-level residues pinned"*, and measured the probe block as the expensive
one — over 4M heartbeats as a single block. Split per statement it is not
expensive at all: the six gates below elaborate in about 3 s TOGETHER. The
measurement that mattered was never the total work, it was the SHAPE.

Each is stated over a free world and a free frame, like the two above, and
each hypothesis is one the shipped code forces. Together with `bound_enters`
they are statements 1–5 of the eighteen, plus the four inside `if not root:`. -/

/-- **GATE 3 — `depth = max(depth, 0)`.** The QS refloor, and the same builtin
resolution `max_evals` pays for: the constant fold, the function table, the
class table and the namedtuple table, all pinned residues. -/
theorem depth_refloors (w : World) (e : REnv) (d : Int)
    (hnomax : Env.lookup e "max" = Option.none)
    (hd : Env.lookup e "depth" = some (.int d)) :
    execStmts sunfish 8 ⟨w, e⟩ [sbDepth]
      = .ok ⟨w, Env.set e "depth" (.int (max d 0))⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, hdep⟩ := sbDepth_lit
  rw [hdep]
  py_simp [-globalsFold, -globalsStep, hnomax, hd, maxG, maxNotFun, maxCls, maxNT]

/-- **GATE 4 — the king-capture check falls through.** `if pos.score <=
-MATE_LOWER: return -MATE_UPPER` is the engine's ONLY termination check, so
every later gate needs it to have passed. `-MATE_LOWER < pos.score` is the
condition, and it is `QSStandPat`'s third hypothesis.

The `pos.score` read is where the `Position` class projection above is spent:
`posCAux` puts the residue in the pinned shape and `posCls_methods` decides it,
so the field read never opens the 1MB literal. `MATE_LOWER` is statically
POISONED (`mlG`), so the live view decides — hence `hml` on `w.globals`. -/
theorem mate_check_passes (w : World) (e : REnv) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hnoml : Env.lookup e "MATE_LOWER" = Option.none)
    (hml : Env.lookup w.globals "MATE_LOWER" = some (.int mateLower))
    (hsc : -mateLower < sc) :
    execStmts sunfish 8 ⟨w, e⟩ [sbMate] = .ok ⟨w, e⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, hm⟩ := sbMate_lit
  rw [hm]
  py_simp [-globalsFold, -globalsStep, hpos, hnoml, hml, mlG, posOf, posCAux,
    posCls_methods]
  rw [if_neg (show ¬ (sc ≤ -mateLower) by omega)]
  py_simp [-globalsFold, -globalsStep]

/-- **GATE 5 — the probe MISSES on a cleared table**, and the miss is the
shipped default. This is `sf_probe`'s left disjunct as an interpreter run:
`entry = self.tp_score.get((pos, depth), Entry(-MATE_UPPER, MATE_UPPER))` off
an empty dict binds `entry` to `entryDefault` and touches nothing.

`hk` is the probe's own hashability, which the shipped `.get` checks before it
compares — a Position value satisfies it and the `#guard`s below say so. The
world is unchanged: a `.get` allocates nothing, so this gate is heap-free. -/
theorem probe_misses (w : World) (e : REnv) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf d : Int) (pv : RVal) (sv : Nat)
    (hslf : Env.lookup e "self" = some (.ref sa))
    (hpos : Env.lookup e "pos" = some pv)
    (hd : Env.lookup e "depth" = some (.int d))
    (hnoe : Env.lookup e "Entry" = Option.none)
    (hnomu : Env.lookup e "MATE_UPPER" = Option.none)
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hobj : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict : Heap.get? w.heap ts = some (.dict #[] sv))
    (hk : hashableKey pv = true) :
    execStmts sunfish 16 ⟨w, e⟩ [sbEntry]
      = .ok ⟨w, Env.set e "entry" entryDefault⟩ .next := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, hen⟩ := sbEntry_lit
  obtain ⟨sp, hnt⟩ := entryNTAux
  simp only [Heap.get?] at hobj hdict
  rw [hen]
  py_simp [-globalsFold, -globalsStep, hslf, hpos, hd, hnoe, hmu, hnomu, muG,
    entryG, entryNotFun, entryClsAux, hnt, hobj, hdict, searcherObj, entryDefault,
    tpKey, hk]

/-- **GATE 6 — the lower-bound return is unreachable at the default.**
`if entry.lower >= gamma: return entry.lower` with `entry.lower = -MATE_UPPER`
needs exactly the docstring's own window precondition. This is one half of
what the mate-band audit calls `tt_sentinel_defaults_never_returned`.

`entryClsAux` is the residue here: an attribute read consults the class table
even for a plain namedtuple, and `Entry` is not in it. -/
theorem probe_lower_passes (w : World) (e : REnv) (gamma : Int)
    (hen : Env.lookup e "entry" = some entryDefault)
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hlo : -mateUpper < gamma) :
    execStmts sunfish 8 ⟨w, e⟩ [sbLo] = .ok ⟨w, e⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, h⟩ := sbLo_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hen, hg, entryDefault, entryClsAux]
  rw [if_neg (show ¬ (gamma ≤ -mateUpper) by omega)]
  py_simp [-globalsFold, -globalsStep]

/-- **GATE 7 — and so is the upper-bound return.** The other half:
`gamma <= MATE_UPPER`. With GATE 6 this is the whole sentinel reservation, and
it is a PRECONDITION rather than an invariant (§L10 (a)). -/
theorem probe_upper_passes (w : World) (e : REnv) (gamma : Int)
    (hen : Env.lookup e "entry" = some entryDefault)
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hup : gamma ≤ mateUpper) :
    execStmts sunfish 8 ⟨w, e⟩ [sbUp] = .ok ⟨w, e⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, h⟩ := sbUp_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hen, hg, entryDefault, entryClsAux]
  rw [if_neg (show ¬ (mateUpper < gamma) by omega)]
  py_simp [-globalsFold, -globalsStep]

/-- **GATE 8 — the repetition test is SHORT-CIRCUITED at a QS node.**
`if depth > 0 and pos in self.history: return 0` — at `depth = 0` the left
conjunct is false and the membership test never runs, so the gate needs
nothing about the history set at all. The shipped comment says why the test is
skipped there (*"at depth=0, since it would be expensive and break futility
pruning"*), and the interpreter agrees for the same reason CPython does: `and`
does not evaluate its right operand.

At `depth ≥ 1` this is the one head statement that reads `self.history`, and a
depth-`d` gate owes a hypothesis about it. -/
theorem probe_repetition_skipped (w : World) (e : REnv)
    (hd : Env.lookup e "depth" = some (.int 0)) :
    execStmts sunfish 8 ⟨w, e⟩ [sbRep] = .ok ⟨w, e⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, h⟩ := sbRep_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hd]

theorem execStmt_if_true {m : Module} {F : Nat} {st st₁ : FrameState}
    {cond : Expr} {body orelse : Array Stmt} {sp : Span} {v : RVal}
    (hc : evalExpr m F st cond = .ok st₁ v)
    (hb : truthyH st₁.world.heap v = .ok true) :
    execStmt m (F + 1) st (.ifStmt cond body orelse sp)
      = execStmts m F st₁ body.toList := by
  rw [execStmt, hc]
  simp only [Run.bind, Run.liftRes, hb, if_true]

theorem execStmt_if_false {m : Module} {F : Nat} {st st₁ : FrameState}
    {cond : Expr} {body orelse : Array Stmt} {sp : Span} {v : RVal}
    (hc : evalExpr m F st cond = .ok st₁ v)
    (hb : truthyH st₁.world.heap v = .ok false) :
    execStmt m (F + 1) st (.ifStmt cond body orelse sp)
      = execStmts m F st₁ orelse.toList := by
  rw [execStmt, hc]
  simp only [Run.bind, Run.liftRes, hb, Bool.false_eq_true, if_false]

/-- **An expression gate, wrapped as a statement.** `name = <expr>` binds the
value the expression evaluates to — the one `assign` arm, so an EXPRESSION gate
(`calm_evals`, `nmr_evals`) becomes a statement gate for free. -/
theorem execStmt_assign_name {m : Module} {F : Nat} {st st₁ : FrameState}
    {nm : String} {rhs : Expr} {v : RVal} {sp p : Span}
    (h : evalExpr m F st rhs = .ok st₁ v) :
    execStmt m (F + 1) st (.assign #[.name nm p] rhs sp)
      = .ok ⟨st₁.world, Env.set st₁.locals nm v⟩ .next := by
  rw [execStmt, h]
  simp only [Run.bind, Run.liftRes, assignToH, assignTo]

/-- **A statement triple, read back as a decided run.** Every arm but `next` is
`False`, so the run cannot have escaped — the extraction the fold gate needs
before it can join the chain. -/
theorem execStmt_of_stmtTriple {m : Module} {P : FrameState → Prop} {s : Stmt}
    {w' : World} {e' : REnv}
    (h : PyStmtTriple m P s { next := fun st => st = ⟨w', e'⟩ })
    (st : FrameState) (hP : P st) :
    ∃ f, execStmt m f st s = .ok ⟨w', e'⟩ .next := by
  obtain ⟨t, ht⟩ := h st hP
  refine ⟨t, ?_⟩
  have hh := ht t (Nat.le_refl t)
  cases hx : execStmt m t st s with
  | ok st'' flow =>
      rw [hx] at hh
      cases flow with
      | next => rw [show st'' = (⟨w', e'⟩ : FrameState) from hh]
      | brk => exact absurd hh (by simp [PyPost.holds])
      | cont => exact absurd hh (by simp [PyPost.holds])
      | ret v => exact absurd hh (by simp [PyPost.holds])
  | exn st'' er => rw [hx] at hh; exact absurd hh (by simp [PyPost.holds])
  | timeout => rw [hx] at hh; exact absurd hh (by simp [PyPost.holds])
  | unsupported msg => rw [hx] at hh; exact absurd hh (by simp [PyPost.holds])

/-- The flow-generic singleton wrapper. `execStmts_singleton` covers `.next`,
which is every statement but the LAST: `return best` lands `.ret`, and the
chain's final link needs a wrapper that does not assume otherwise. -/
theorem execStmts_singleton_flow {m : Module} {F : Nat} {st st' : FrameState} {s : Stmt}
    {flow : RFlow} (h : execStmt m (F + 1) st s = .ok st' flow) :
    execStmts m (F + 2) st [s] = .ok st' flow := by
  rw [execStmts, h, Run.bind]
  cases flow with
  | next => rw [execStmts]
  | brk => rfl
  | cont => rfl
  | ret v => rfl

/-- **THE COMPOSABILITY ENGINE.** Two decided runs in sequence are one decided
run of the concatenation, in the ∃-fuel form `QSStandPat` is itself stated in —
so the fuel bookkeeping is internal (`execStmt_mono`/`execStmts_mono` at a summed
witness) and a caller never counts interpreter steps.

`VCTactic.lean` has this as the PRIVATE `execStmts_append_run`, the engine of
`PyTriple.run_seq`; the assembly needs it at the raw `execStmts` level, so here
it is public. Note `++` is LEFT-associative: the segments nest first-innermost. -/
theorem execStmts_append {m : Module} {l₁ l₂ : List Stmt} {st st' : FrameState}
    {r : Run FrameState RFlow}
    (h1 : ∃ f, execStmts m f st l₁ = .ok st' .next)
    (h2 : ∃ f, execStmts m f st' l₂ = r) (hr : r ≠ .timeout) :
    ∃ f, execStmts m f st (l₁ ++ l₂) = r := by
  induction l₁ generalizing st with
  | nil =>
    obtain ⟨f, hf⟩ := h1
    match f, hf with
    | f + 1, hf =>
      rw [execStmts] at hf
      have henv : st = st' := (Run.ok.inj hf).1
      subst henv
      simpa using h2
  | cons s l₁' ih =>
    obtain ⟨f, hf⟩ := h1
    match f, hf with
    | f + 1, hf =>
      rw [execStmts] at hf
      cases hx : execStmt m f st s with
      | ok st₁ flow =>
        rw [hx, Run.bind] at hf
        cases flow with
        | next =>
          obtain ⟨g, hg⟩ := ih ⟨f, hf⟩
          refine ⟨(f + g) + 1, ?_⟩
          rw [List.cons_append, execStmts,
            execStmt_mono hx (by simp) (f + g) (by omega), Run.bind]
          exact execStmts_mono hg (by simpa using hr) _ (by omega)
        | brk => exact absurd hf (by simp)
        | cont => exact absurd hf (by simp)
        | ret v => exact absurd hf (by simp)
      | exn st₁ er => rw [hx, Run.bind] at hf; exact absurd hf (by simp)
      | timeout => rw [hx, Run.bind] at hf; exact absurd hf (by simp)
      | unsupported msg => rw [hx, Run.bind] at hf; exact absurd hf (by simp)

/-- The converse of `execStmt_of_singleton`: a statement gate read as a
one-element list, which is what `execStmts_append` consumes. -/
theorem execStmts_singleton {m : Module} {F : Nat} {st st' : FrameState} {s : Stmt}
    (h : execStmt m (F + 1) st s = .ok st' .next) :
    execStmts m (F + 2) st [s] = .ok st' .next := by
  rw [execStmts, h, Run.bind, execStmts]

/-- **A singleton `execStmts` gate, read back at `execStmt`.** The gates above
are stated over one-statement LISTS, which is the shape a reader wants and the
WRONG shape for composition: chaining statements needs `execStmt`, because
`execStmts` peels one off at a time. This bridge is the conversion, and landing
it is what made the probe block below composable — a finding for anyone stating
the next batch of gates. -/
theorem execStmt_of_singleton {m : Module} {F : Nat} {st st' : FrameState} {s : Stmt}
    (h : execStmts m (F + 2) st [s] = .ok st' .next) :
    execStmt m (F + 1) st s = .ok st' .next := by
  rw [execStmts] at h
  cases hx : execStmt m (F + 1) st s with
  | ok st₁ flow =>
      rw [hx] at h
      cases flow with
      | next =>
          rw [Run.bind, execStmts] at h
          cases h
          rfl
      | brk => rw [Run.bind] at h; exact absurd h (by simp)
      | cont => rw [Run.bind] at h; exact absurd h (by simp)
      | ret v => rw [Run.bind] at h; exact absurd h (by simp)
  | exn st₁ er => rw [hx, Run.bind] at h; exact absurd h (by simp)
  | timeout => rw [hx, Run.bind] at h; exact absurd h (by simp)
  | unsupported msg => rw [hx, Run.bind] at h; exact absurd h (by simp)

/-! The four probe statements composed into one gate, with the `if not root:`
wrapper. The two `simp only [Run.bind]` steps are load-bearing exactly as in
`qs_body` — the linter disagrees and is wrong. -/
set_option linter.unusedSimpArgs false in
/-- **The probe BLOCK as one gate**: `if not root:` runs, the `.get` misses, and
neither bound return nor the repetition test fires — so the whole block is a
single binding of `entry` and nothing else. The four statement gates composed at
their own fuels by `execStmt_mono`, plus the wrapper's guard. -/
theorem probe_block_runs (w : World) (e : REnv) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma : Int) (pv : RVal) (sv : Nat)
    (hroot : Env.lookup e "root" = some (.bool false))
    (hslf : Env.lookup e "self" = some (.ref sa))
    (hpos : Env.lookup e "pos" = some pv)
    (hd : Env.lookup e "depth" = some (.int 0))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hnoe : Env.lookup e "Entry" = Option.none)
    (hnomu : Env.lookup e "MATE_UPPER" = Option.none)
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hobj : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict : Heap.get? w.heap ts = some (.dict #[] sv))
    (hk : hashableKey pv = true)
    (hlo : -mateUpper < gamma) (hup : gamma ≤ mateUpper) :
    execStmt sunfish 40 ⟨w, e⟩ sbProbe
      = .ok ⟨w, Env.set e "entry" entryDefault⟩ .next := by
  obtain ⟨p0, p1, p2, hpr⟩ := sbProbe_lit
  have hc : evalExpr sunfish 39 ⟨w, e⟩ (.unaryOp .not (.name "root" p0) p1)
      = .ok ⟨w, e⟩ (.bool true) := by
    py_simp [-globalsFold, -globalsStep, hroot]
  rw [hpr, execStmt_if_true hc rfl]
  have hE := probe_misses w e ci sa ts tm hs n dl sf 0 pv sv hslf hpos hd hnoe hnomu hmu
    hobj hdict hk
  have hen : Env.lookup (Env.set e "entry" entryDefault) "entry" = some entryDefault := by
    simp [Env.lookup_set_self]
  have hg' : Env.lookup (Env.set e "entry" entryDefault) "gamma" = some (.int gamma) := by
    simp [Env.lookup_set_ne, hg]
  have hd' : Env.lookup (Env.set e "entry" entryDefault) "depth" = some (.int 0) := by
    simp [Env.lookup_set_ne, hd]
  rw [show sbProbeB.toArray.toList = sbProbeB from rfl, sbProbeB_split]
  simp only [execStmts]
  rw [execStmt_mono (execStmt_of_singleton (F := 14) hE) (by simp) 38 (by omega)]
  simp only [Run.bind]
  rw [execStmt_mono (execStmt_of_singleton (F := 6)
    (probe_lower_passes w (Env.set e "entry" entryDefault) gamma hen hg' hlo)) (by simp) 37
    (by omega)]
  simp only [Run.bind]
  rw [execStmt_mono (execStmt_of_singleton (F := 6)
    (probe_upper_passes w (Env.set e "entry" entryDefault) gamma hen hg' hup)) (by simp) 36
    (by omega)]
  simp only [Run.bind]
  rw [execStmt_mono (execStmt_of_singleton (F := 6)
    (probe_repetition_skipped w (Env.set e "entry" entryDefault) hd')) (by simp) 35 (by omega)]

/-! ### THE ASSEMBLY, demonstrated on the head

The frame chain §L20 priced, run for real on statements 0–5. Three things it
establishes, and they are what make the rest bookkeeping:

* **the frame lookups are FREE** — `sbEnv0` is a concrete five-element list and
  every gate's hypothesis about it is `rfl`, and stays `rfl` through the
  `Env.set` chain because every key is a literal (all seven of
  `probe_block_runs`' frame premises below are discharged by `rfl`);
* **the world chain threads through the gates' own conclusions** — the counter
  bump is `bound_enters`' output, and the dict survives it by
  `Heap.get?_update_ne` at `ts ≠ sa`, one premise;
* **the segments compose by `execStmts_append`** with no fuel arithmetic on the
  caller's side.

What remains for `QSStandPat` is twelve more statements of exactly this, plus
the three premises §L20 named. -/

/-- The frame after the QS refloor: `depth` rebound to `max 0 0 = 0`. -/
abbrev EA (sa : Addr) (pv : RVal) (gamma : Int) : REnv :=
  Env.set (sbEnv0 (.ref sa) pv gamma 0) "depth" (.int 0)

/-- **THE HEAD, COMPOSED.** Statements 0–5: the docstring, the node count, the
clock guard, the refloor, the king-capture check and the whole probe block —
one gate, in the ∃-fuel form `QSStandPat` is stated in. -/
theorem head_runs (w : World) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma sc : Int) (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (sv : Nat) (h' : Heap)
    (hself : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hupd : Heap.update w.heap sa (searcherObj ci ts tm hs (n + 1) dl sf) = some h')
    (hclk : ¬ ((n + 1).fmod 2048 = 0))
    (hts : ts ≠ sa)
    (hdict : Heap.get? w.heap ts = some (.dict #[] sv))
    (hml : Env.lookup w.globals "MATE_LOWER" = some (.int mateLower))
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hk : hashableKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) = true)
    (hsc : -mateLower < sc) (hlo : -mateUpper < gamma) (hup : gamma ≤ mateUpper) :
    ∃ f, execStmts sunfish f
        ⟨w, sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩
        ([sbDoc, sbNodes, sbClock] ++ [sbDepth] ++ [sbMate] ++ [sbProbe])
      = .ok ⟨{ w with heap := h' },
              Env.set (EA sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma) "entry" entryDefault⟩
          .next := by
  have hobj' : Heap.get? h' sa = some (searcherObj ci ts tm hs (n + 1) dl sf) :=
    Heap.get?_update_self hupd
  have hdict' : Heap.get? h' ts = some (.dict #[] sv) :=
    (Heap.get?_update_ne hupd hts).trans hdict
  have hD : execStmts sunfish 8 ⟨{ w with heap := h' }, sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩ [sbDepth]
      = .ok ⟨{ w with heap := h' }, EA sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma⟩ .next := by
    have := depth_refloors { w with heap := h' } (sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0) 0 rfl rfl
    simpa [EA, show max (0 : Int) 0 = 0 from by omega] using this
  have hA : ∃ f, execStmts sunfish f
      ⟨w, sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩ [sbDoc, sbNodes, sbClock]
        = .ok ⟨{ w with heap := h' }, sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩ .next :=
    ⟨16, bound_enters w ci sa ts tm hs n dl sf gamma 0 (posOf b sc wc0 wc1 bc0 bc1 ep kp) h' hself hupd hclk⟩
  have hAB := execStmts_append hA ⟨8, hD⟩ (by simp)
  have hABC := execStmts_append hAB
    ⟨8, mate_check_passes { w with heap := h' } (EA sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma) b sc wc0 wc1 bc0 bc1 ep kp
      rfl rfl hml hsc⟩ (by simp)
  exact execStmts_append hABC
    ⟨41, execStmts_singleton (F := 39)
      (probe_block_runs { w with heap := h' } (EA sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma) ci sa ts tm hs (n + 1) dl sf
        gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) sv rfl rfl rfl rfl rfl rfl rfl hmu hobj' hdict' hk hlo hup)⟩ (by simp)

/-! ### #236's four statements between the probe and the fold

`killer`, `calm`/`guard`, `t`, `nmr` — statements 6 and 8–11. Three of the four
are as cheap as the head; the fourth is the one statement in `bound()` that
carries a RECURSIVE CALL outside the fold, and it is a measured wall with a
measured fix. -/

/-- **GATE 9 — the killer probe misses too.** `killer = self.tp_move.get(pos)`
is the one-argument `.get`, so a miss is `None` rather than a default, and on a
cleared `tp_move` that is the answer. Read BEFORE the null-move probe, which
the shipped comment says is deliberate (*"in case the recursive probe evicts
it"*) — an ordering this gate does not depend on but the fold's killer branch
will. -/
theorem killer_misses (w : World) (e : REnv) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf : Int) (pv : RVal) (sv : Nat)
    (hslf : Env.lookup e "self" = some (.ref sa))
    (hpos : Env.lookup e "pos" = some pv)
    (hobj : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict : Heap.get? w.heap tm = some (.dict #[] sv))
    (hk : hashableKey pv = true) :
    execStmts sunfish 16 ⟨w, e⟩ [sbKiller]
      = .ok ⟨w, Env.set e "killer" .none⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, h⟩ := sbKiller_lit
  simp only [Heap.get?] at hobj hdict
  rw [h]
  py_simp [-globalsFold, -globalsStep, hslf, hpos, hobj, hdict, searcherObj, hk]

/-- **GATE 10 — `guard = not root and calm`** is `calm` itself away from the
root. The celled capture (§L14) is what makes this statement's POSITION legal:
it is written below `def moves():` and read at the call. -/
theorem guard_evals (w : World) (e : REnv) (cm : Bool)
    (hroot : Env.lookup e "root" = some (.bool false))
    (hcalm : Env.lookup e "calm" = some (.bool cm)) :
    execStmts sunfish 8 ⟨w, e⟩ [sbGuard]
      = .ok ⟨w, Env.set e "guard" (.bool cm)⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, h⟩ := sbGuard_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hroot, hcalm]

/-- **GATE 11 — `t = pos.score + NULL_MARGIN`.** The null-probe threshold, and
the measurement `nmarG` records is what makes it cheap: `NULL_MARGIN` resolves
statically, so this gate says nothing about `w.globals`. -/
theorem null_margin_adds (w : World) (e : REnv) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hnonm : Env.lookup e "NULL_MARGIN" = Option.none) :
    execStmts sunfish 8 ⟨w, e⟩ [sbT]
      = .ok ⟨w, Env.set e "t" (.int (sc + nullMargin))⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, h⟩ := sbT_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hpos, hnonm, nmarG, posOf, posCAux,
    posCls_methods]

/-! #### The `and`-chain short circuit, as a general lemma

**MEASURED WALL, and it is not the recursion — it is `evalExpr` at a SYMBOLIC
operand.** `nmr = calm and depth >= 6 and -self.bound(…) >= t` dies on its
second conjunct at every QS node, so the child never runs. But `py_simp`
normalizes the unreachable branch too: it unfolds `evalBoolChain` down to
`evalExpr sunfish _ st r` with `r` the opaque third operand `sbNmr_lit`
provides, and `evalExpr` at a free scrutinee splits into every arm of its
match, each carrying the 1MB literal. Measured: **2 min to the simp step
budget** at 8M heartbeats, with the diagnostics dominated by generic
propositional lemmas (`imp_false` 1242, `eq_self` tried 7868) — the signature
of a goal that has exploded, not of a hard fact.

The fix is to keep `evalExpr` away from `r` by proving the short circuit ONCE,
at the chain, with every operand symbolic. Neither lemma mentions a module, a
program or a fuel numeral, and with them the gate below is **1.7 s**. Both
belong in the general layer the moment a second consumer appears; they are
here because this is the first. -/

/-- A falsy FIRST operand ends an `and` chain at its own value — and it needs
no hypothesis about the rest, because the empty and non-empty tails agree. -/
theorem boolChain_and_falsy {m : Module} {F : Nat} {st st₁ : FrameState}
    {e1 : Expr} {es : List Expr} {v1 : RVal}
    (h1 : evalExpr m F st e1 = .ok st₁ v1)
    (hb1 : truthyH st₁.world.heap v1 = .ok false) :
    evalBoolChain m (F + 1) st .and e1 es = .ok st₁ v1 := by
  rw [evalBoolChain, h1]
  cases es <;>
    simp only [Run.bind, Run.liftRes, hb1, Bool.false_eq_true, if_false]

/-- **And a three-operand chain that dies on its SECOND operand never looks at
its third.** `e3` is universally quantified and appears in no hypothesis, which
is the whole point: the caller's third conjunct may be anything at all, a
recursive call included. -/
theorem boolChain_and3 {m : Module} {F : Nat} {st st₁ st₂ : FrameState}
    {e1 e2 e3 : Expr} {v1 v2 : RVal}
    (h1 : evalExpr m (F + 1) st e1 = .ok st₁ v1)
    (hb1 : truthyH st₁.world.heap v1 = .ok true)
    (h2 : evalExpr m F st₁ e2 = .ok st₂ v2)
    (hb2 : truthyH st₂.world.heap v2 = .ok false) :
    evalBoolChain m (F + 2) st .and e1 [e2, e3] = .ok st₂ v2 := by
  rw [evalBoolChain, h1]
  simp only [Run.bind, Run.liftRes, hb1]
  rw [evalBoolChain, h2]
  simp only [Run.bind, Run.liftRes, hb2, if_true, Bool.false_eq_true, if_false]

/-- And a TWO-operand chain returns its last operand's value outright — the
`calm` shape, where the second operand is the one that decides. -/
theorem boolChain_and2 {m : Module} {F : Nat} {st st₁ st₂ : FrameState}
    {e1 e2 : Expr} {v1 v2 : RVal}
    (h1 : evalExpr m (F + 1) st e1 = .ok st₁ v1)
    (hb1 : truthyH st₁.world.heap v1 = .ok true)
    (h2 : evalExpr m F st₁ e2 = .ok st₂ v2) :
    evalBoolChain m (F + 2) st .and e1 [e2] = .ok st₂ v2 := by
  rw [evalBoolChain, h1]
  simp only [Run.bind, Run.liftRes, hb1, if_true]
  rw [evalBoolChain, h2]
  simp only [Run.bind]

/-- **GATE 12 — `nmr` is `False` at every QS node, and no child runs.**
An EXPRESSION gate rather than a statement gate, like `max_evals`: what has to
be said is that the chain's value is `False`, and it is `False` for two
different reasons depending on `calm` — the first operand when `calm` is falsy,
the second when it is not. Both land on `.bool false`, so the gate is stated
over a symbolic `calm` and proved by casing on it.

`r` is the shipped `-self.bound(pos.rotate(nullmove=True), 1 - t, depth - 7)`,
carried as a free expression. That it can be free is the statement's content:
**a depth-0 gate owes no child call.** At `depth ≥ 6` it does, and that is the
one recursive call `bound()` makes outside the fold. -/
theorem nmr_evals (w : World) (e : REnv) (cm : Bool) (r : Expr)
    (p1 p2 p3 p4 p5 p6 p7 : Span)
    (hcalm : Env.lookup e "calm" = some (.bool cm))
    (hd : Env.lookup e "depth" = some (.int 0)) :
    evalExpr sunfish 8 ⟨w, e⟩
        (.boolOp .and #[.name "calm" p1,
          .compare (.name "depth" p2) #[.gtE] #[.constant (.int 6) p3] p4,
          .compare r #[.gtE] #[.name "t" p5] p6] p7)
      = .ok ⟨w, e⟩ (.bool false) := by
  have h1 : evalExpr sunfish 6 ⟨w, e⟩ (.name "calm" p1) = .ok ⟨w, e⟩ (.bool cm) := by
    py_simp [-globalsFold, -globalsStep, hcalm]
  have h2 : evalExpr sunfish 5 ⟨w, e⟩
      (.compare (.name "depth" p2) #[.gtE] #[.constant (.int 6) p3] p4)
        = .ok ⟨w, e⟩ (.bool false) := by
    py_simp [-globalsFold, -globalsStep, hd]
  rw [evalExpr]
  cases cm
  · exact boolChain_and_falsy (F := 6) h1 rfl
  · exact boolChain_and3 (F := 5) h1 rfl h2 rfl

/-- **GATE 13 — the accumulators.** `best, live = -MATE_UPPER, False` is a
tuple-unpack assignment, and it is the fold's initial state: `Sound` holds of
it for free (`-MATE_UPPER < gamma` is the window precondition), which is
`fold_report`'s `hb`. -/
theorem acc_inits (w : World) (e : REnv)
    (hnomu : Env.lookup e "MATE_UPPER" = Option.none)
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper)) :
    execStmts sunfish 16 ⟨w, e⟩ [sbAcc]
      = .ok ⟨w, Env.set (Env.set e "best" (.int (-mateUpper))) "live" (.bool false)⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, h⟩ := sbAcc_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hnomu, hmu, muG]

/-! ### Statements 7 and 8 — the nested `def` with its CELL, and `calm`

The two the head batch left owed. Statement 7 is §L14's cell tier spent for the
first time on the shipped file; statement 8 is the head's only lowered genexp,
and its gate names the genexp's answer rather than deciding it. -/

/-- **The `def` statement, cell-aware.** `execStmt_nestedDef` (GenBound.lean)
requires `allocCells st caps = st` — NO cells — and the shipped `moves()`
captures `<cell>guard`, so it does not apply. This is the same theorem with the
post-allocation frame as its own variable; the snapshot-tier version is the
`st' = st` case. A strict generalization, so it belongs in GenBound at the
second consumer; it is here because this is the first. -/
theorem execStmt_nestedDef_cells {m : Module} {fuel : Nat} {st st' : FrameState}
    {name : String} {params : Array Param} {argsOk localsOk hasGlobal isGenerator : Bool}
    {body : Array Stmt} {captures : Array String} {cap : REnv} {sp : Span}
    (hnc : allocCells st captures.toList = st')
    (hcap : capturesSnapshot st'.locals captures.toList = some cap) :
    execStmt m (fuel + 1) st
        (.defStmt name params argsOk localsOk hasGlobal isGenerator body captures sp)
      = .ok ⟨{ st'.world with
                heap := st'.world.heap.push
                  (.closure name params argsOk localsOk hasGlobal isGenerator body cap) },
              Env.set st'.locals name (.ref st'.world.heap.size)⟩ .next := by
  rw [execStmt]
  simp only [hnc, hcap]

/-- **The cell the `def` allocates for `guard`, and it is EMPTY.** `guard` is
assigned at statement 9, BELOW the `def` at 7, so at allocation time the name
has no binding — which is exactly the shape the snapshot tier refused (§L13)
and the cell admits. A cell holding `none` is not a defect; it is the reason
the cell exists. -/
def guardCell : Obj := .cell Option.none

/-- **The allocation, computed.** Four captures are plain names and allocate
nothing; the fifth is the cell directory key and pushes one object. -/
theorem sbDef_cells (w : World) (e : REnv)
    (hnocell : Env.lookup e "<cell>guard" = Option.none)
    (hnoguard : Env.lookup e "guard" = Option.none) :
    allocCells ⟨w, e⟩ ["depth", "gamma", "<cell>guard", "killer", "pos"]
      = ⟨{ w with heap := w.heap.push guardCell },
          Env.set e "<cell>guard" (.ref w.heap.size)⟩ := by
  have k1 : isCellKey "depth" = false := by simp [isCellKey, String.isPrefixOf]
  have k2 : isCellKey "gamma" = false := by simp [isCellKey, String.isPrefixOf]
  have k3 : isCellKey "<cell>guard" = true := by simp [isCellKey, String.isPrefixOf]
  have k4 : isCellKey "killer" = false := by simp [isCellKey, String.isPrefixOf]
  have k5 : isCellKey "pos" = false := by simp [isCellKey, String.isPrefixOf]
  have kn : cellName "<cell>guard" = "guard" := by rfl
  simp only [allocCells, k1, k2, k3, k4, k5, kn, hnocell, hnoguard,
    Bool.false_eq_true, if_false, if_true, guardCell]

/-- The captures snapshot: four VALUES and one cell REF — the directory entry,
not `guard`'s value, which is the whole difference from a snapshot. -/
def sbMovesCap (a : Addr) (gamma d : Int) (kv pv : RVal) : REnv :=
  [("depth", .int d), ("gamma", .int gamma), ("<cell>guard", .ref a),
   ("killer", kv), ("pos", pv)]

/-- The closure object, projected off the statement so no component of the
shipped `def` is spelled by hand. -/
def sbMovesClosure (a : Addr) (gamma d : Int) (kv pv : RVal) : Obj :=
  match sbDef with
  | .defStmt nm ps ao lo hgl ig body _ _ =>
      .closure nm ps ao lo hgl ig body (sbMovesCap a gamma d kv pv)
  | _ => default

theorem sbDef_snapshot (w : World) (e : REnv) (gamma d : Int) (kv pv : RVal)
    (hd : Env.lookup e "depth" = some (.int d))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hk : Env.lookup e "killer" = some kv)
    (hp : Env.lookup e "pos" = some pv) :
    capturesSnapshot (Env.set e "<cell>guard" (.ref w.heap.size))
        ["depth", "gamma", "<cell>guard", "killer", "pos"]
      = some (sbMovesCap w.heap.size gamma d kv pv) := by
  simp [capturesSnapshot, sbMovesCap, Env.lookup_set_self, Env.lookup_set_ne,
    hd, hg, hk, hp]

/-- The world after the cell, and after the closure beside it. Named rather
than inlined because a structure-instance field value may not continue on a
less-indented line (§L9 finding 4). -/
def sbW1 (w : World) : World := { w with heap := w.heap.push guardCell }

def sbW2 (w : World) (gamma d : Int) (kv pv : RVal) : World :=
  { sbW1 w with heap := (sbW1 w).heap.push (sbMovesClosure w.heap.size gamma d kv pv) }

/-- The frame after the `def`: the cell directory entry, then the closure name. -/
def sbEnvDef (w : World) (e : REnv) : REnv :=
  Env.set (Env.set e "<cell>guard" (.ref w.heap.size)) "moves" (.ref (w.heap.size + 1))

/-- **GATE 14 — `def moves():` allocates the CELL and the closure**, in that
order, and binds the name. TWO heap objects where the snapshot tier pushed one,
and the extra one is what makes the shipped source order legal. -/
theorem moves_def_allocates (w : World) (e : REnv) (F : Nat) (gamma d : Int) (kv pv : RVal)
    (hd : Env.lookup e "depth" = some (.int d))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hk : Env.lookup e "killer" = some kv)
    (hp : Env.lookup e "pos" = some pv)
    (hnoguard : Env.lookup e "guard" = Option.none)
    (hnocell : Env.lookup e "<cell>guard" = Option.none) :
    execStmt sunfish (F + 1) ⟨w, e⟩ sbDef
      = .ok ⟨sbW2 w gamma d kv pv, sbEnvDef w e⟩ .next := by
  obtain ⟨ps, ao, lo, hgl, b, sp, hdef⟩ := sbDef_captures
  rw [hdef]
  have hcells := sbDef_cells w e hnocell hnoguard
  have hsnap := sbDef_snapshot w e gamma d kv pv hd hg hk hp
  rw [execStmt_nestedDef_cells (st' := ⟨sbW1 w, Env.set e "<cell>guard" (.ref w.heap.size)⟩)
    (by simpa [sbW1] using hcells) (by simpa using hsnap)]
  simp only [sbMovesClosure, hdef, sbW2, sbW1, sbEnvDef, Array.size_push]

/-- `abs(pos.score) < 750`, the calmness test's first conjunct — `abs`'s
resolution is `max`'s, and the field read is the `Position` projection again. -/
theorem abs_score_evals (w : World) (e : REnv) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (p1 p2 p3 p4 p5 p6 : Span)
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hnoabs : Env.lookup e "abs" = Option.none)
    (hlt : -750 < sc ∧ sc < 750) :
    evalExpr sunfish 6 ⟨w, e⟩
        (.compare (.call (.name "abs" p1) #[.attribute (.name "pos" p2) "score" p3] #[]
          Option.none p4) #[.lt] #[.constant (.int 750) p5] p6)
      = .ok ⟨w, e⟩ (.bool true) := by
  py_simp [-globalsFold, -globalsStep, hpos, hnoabs, absG, absNotFun, absCls, absNT,
    posOf, posCAux, posCls_methods]
  omega

/-- **GATE 15 — `calm` is whatever the BOARD says, and the gate says exactly
that.** The second conjunct is `any(<genexpr@3>("RBNQ", pos))` — the head's one
lowered genexp, drained by `any` — and its value depends on which piece letters
the board carries. So `hg` names that answer instead of deciding it: one
`evalExpr` premise, discharged per board, and the chain's value IS it.

That the premise can stay open is a fact about depth 0, not a shortcut: `calm`
reaches the fold only through `guard`, and `guard` is read at `2 < depth < 6`
(the scoring null) and at `guard and depth >= 6` (intrinsic LMR). Both are
false at a QS node, so the depth-0 statement never consults it. A depth-≥2 gate
owes the genexp its own drain. -/
theorem calm_evals (w : World) (e : REnv) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (g : Expr) (av : Bool)
    (p1 p2 p3 p4 p5 p6 p7 : Span)
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hnoabs : Env.lookup e "abs" = Option.none)
    (hlt : -750 < sc ∧ sc < 750)
    (hg : evalExpr sunfish 5 ⟨w, e⟩ g = .ok ⟨w, e⟩ (.bool av)) :
    evalExpr sunfish 8 ⟨w, e⟩
        (.boolOp .and
          #[.compare (.call (.name "abs" p1) #[.attribute (.name "pos" p2) "score" p3] #[]
              Option.none p4) #[.lt] #[.constant (.int 750) p5] p6, g] p7)
      = .ok ⟨w, e⟩ (.bool av) := by
  rw [evalExpr]
  exact boolChain_and2 (F := 5)
    (abs_score_evals w e b sc wc0 wc1 bc0 bc1 ep kp p1 p2 p3 p4 p5 p6 hpos hnoabs hlt) rfl hg

/-! ### The two EXPRESSION gates, wrapped

§L21's wrinkles 8 and 11, one line each as priced: `execStmt_assign_name` turns
`calm_evals`/`nmr_evals` into statement gates, so every statement of the
eighteen now has a gate of the SAME shape and the chain is uniform. -/

/-- The calmness test's SECOND conjunct, projected: `any(<genexpr@3>("RBNQ",
pos))`. Its value is the board's business, so it is a premise everywhere. -/
def calmG : Expr :=
  match sbCalm with
  | .assign _ (.boolOp _ vs _) _ =>
      (match vs.toList with | _ :: g :: _ => g | _ => .constant .none nowhere)
  | _ => .constant .none nowhere

/-- Statement 8 as a statement gate: the expression gate through the `assign`
wrapper, with the genexp's answer named. -/
theorem calm_binds (w : World) (e : REnv) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (av : Bool)
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hnoabs : Env.lookup e "abs" = Option.none)
    (hlt : -750 < sc ∧ sc < 750)
    (hg : evalExpr sunfish 5 ⟨w, e⟩ calmG = .ok ⟨w, e⟩ (.bool av)) :
    execStmt sunfish 9 ⟨w, e⟩ sbCalm = .ok ⟨w, Env.set e "calm" (.bool av)⟩ .next := by
  obtain ⟨g, p0, p1, p2, p3, p4, p5, p6, p7, p8, hcalm⟩ := sbCalm_lit
  have hgg : calmG = g := by rw [calmG, hcalm]
  rw [hcalm]
  exact execStmt_assign_name (F := 8)
    (calm_evals w e b sc wc0 wc1 bc0 bc1 ep kp g av p1 p2 p3 p4 p5 p6 p7 hpos hnoabs hlt
      (by rw [← hgg]; exact hg))

/-- Statement 11 the same way. -/
theorem nmr_binds (w : World) (e : REnv) (cm : Bool)
    (hcalm : Env.lookup e "calm" = some (.bool cm))
    (hd : Env.lookup e "depth" = some (.int 0)) :
    execStmt sunfish 9 ⟨w, e⟩ sbNmr = .ok ⟨w, Env.set e "nmr" (.bool false)⟩ .next := by
  obtain ⟨r, p0, p1, p2, p3, p4, p5, p6, p7, p8, hn⟩ := sbNmr_lit
  rw [hn]
  exact execStmt_assign_name (F := 8) (nmr_evals w e cm r p1 p2 p3 p4 p5 p6 p7 hcalm hd)

/-! ### Statement 13 — THE FOLD, via `PyStmtTriple.forGen`

§L10's item 4, and §L16's `fold_report` is what it feeds. The loop is
`for val, move in moves():` over three body statements, and at a QS stand-pat
node it runs **exactly one round and breaks** — which the engine confirms:
`bd_probe (posH 0) 0 0` is `(0, ONE node)`.

Two general lemmas first, and they are the `nmr` fix again. `sbScore`'s `elif`
chain — four more branches, two of them recursive — is a DEFINED projection
(`sbElse1`), not an opaque variable, so `py_simp` will walk it and explode
exactly as it did on `nmr`'s third operand. `execStmt_if_true` keeps it out by
deciding the branch at the `ifStmt` rather than inside it. -/

/-- Branch 1's guard: `move is None and depth == 0`, both true at a QS node on
a virtual yield. -/
theorem score_guard_true (w : World) (e : REnv) (p0 p1 p2 p3 p4 p5 p6 : Span)
    (hm : Env.lookup e "move" = some .none)
    (hd : Env.lookup e "depth" = some (.int 0)) :
    evalExpr sunfish 8 ⟨w, e⟩
        (.boolOp .and
          #[.compare (.name "move" p0) #[.is] #[.constant Const.none p1] p2,
            .compare (.name "depth" p3) #[.eq] #[.constant (.int 0) p4] p5] p6)
      = .ok ⟨w, e⟩ (.bool true) := by
  have h1 : evalExpr sunfish 6 ⟨w, e⟩
      (.compare (.name "move" p0) #[.is] #[.constant Const.none p1] p2)
        = .ok ⟨w, e⟩ (.bool true) := by
    py_simp [-globalsFold, -globalsStep, hm]
  have h2 : evalExpr sunfish 5 ⟨w, e⟩
      (.compare (.name "depth" p3) #[.eq] #[.constant (.int 0) p4] p5)
        = .ok ⟨w, e⟩ (.bool true) := by
    py_simp [-globalsFold, -globalsStep, hd]
  rw [evalExpr]
  exact boolChain_and2 (F := 5) h1 rfl h2

/-- **The QS round's score: branch 1 fires and `score = pos.score`.** The
`elif` chain below it — four branches, two of them recursive — is never
evaluated, and `execStmt_if_true` is what keeps `py_simp` out of it. -/
theorem qs_score (w : World) (e : REnv) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (hm : Env.lookup e "move" = some .none)
    (hd : Env.lookup e "depth" = some (.int 0))
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp)) :
    execStmt sunfish 9 ⟨w, e⟩ sbScore
      = .ok ⟨w, Env.set e "score" (.int sc)⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, hs⟩ := sbScore_lit
  obtain ⟨q0, q1, q2, q3, hb1⟩ := sbB1_lit
  rw [hs, execStmt_if_true (score_guard_true w e p0 p1 p2 p3 p4 p5 p6 hm hd) rfl, hb1]
  py_simp [-globalsFold, -globalsStep, hpos, posOf, posCAux, posCls_methods]


/-- `best = max(best, score)` as a STATEMENT — `max_evals` is the expression. -/
theorem qs_max (w : World) (e : REnv) (bst sc : Int)
    (hnomax : Env.lookup e "max" = Option.none)
    (hb : Env.lookup e "best" = some (.int bst))
    (hs : Env.lookup e "score" = some (.int sc)) :
    execStmt sunfish 9 ⟨w, e⟩ sbMax
      = .ok ⟨w, Env.set e "best" (.int (max bst sc))⟩ .next := by
  obtain ⟨x0, x1, x2, x3, x4, x5, hmax⟩ := sbMax_lit
  rw [hmax]
  py_simp [-globalsFold, -globalsStep, hnomax, hb, hs, maxG, maxNotFun, maxCls, maxNT]

/-- The killer store's guard is FALSE on a virtual yield: `move is not None`
fails, so the `and` never reaches the `depth` conjunct — which is why the QS
fold stores no killer and stays heap-free. -/
theorem kill_guard_false (w : World) (e : REnv) (p0 p1 p2 p3 p4 : Span)
    (hm : Env.lookup e "move" = some .none) :
    evalExpr sunfish 9 ⟨w, e⟩
        (.boolOp .and
          #[.compare (.name "move" p0) #[.isNot] #[.constant Const.none p1] p2,
            .name "depth" p3] p4)
      = .ok ⟨w, e⟩ (.bool false) := by
  have h1 : evalExpr sunfish 7 ⟨w, e⟩
      (.compare (.name "move" p0) #[.isNot] #[.constant Const.none p1] p2)
        = .ok ⟨w, e⟩ (.bool false) := by
    py_simp [-globalsFold, -globalsStep, hm]
  rw [evalExpr]
  exact boolChain_and_falsy (F := 7) h1 rfl

/-- **The cutoff fires and the loop BREAKS**, storing nothing: the killer guard
is false on a virtual yield, so the `if len(self.tp_move) > TABLE_SIZE` eviction
inside it is never reached either. -/
theorem qs_cut (w : World) (e : REnv) (bst gamma : Int)
    (hb : Env.lookup e "best" = some (.int bst))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hm : Env.lookup e "move" = some .none)
    (hge : gamma ≤ bst) :
    execStmt sunfish 12 ⟨w, e⟩ sbCut = .ok ⟨w, e⟩ .brk := by
  obtain ⟨c0, c1, c2, c3, hcut⟩ := sbCut_lit
  obtain ⟨ks, hcb⟩ := sbCutB_split
  obtain ⟨k0, k1, k2, k3, k4, k5, hkill⟩ := sbKill_lit
  have hcond : evalExpr sunfish 11 ⟨w, e⟩
      (.compare (.name "best" c0) #[.gtE] #[.name "gamma" c1] c2)
        = .ok ⟨w, e⟩ (.bool true) := by
    py_simp [-globalsFold, -globalsStep, hb, hg]
    omega
  rw [hcut, execStmt_if_true hcond rfl, hcb]
  simp only [execStmts]
  rw [hkill, execStmt_if_false (kill_guard_false w e k0 k1 k2 k3 k4 hm) rfl]
  simp only [execStmts, Run.bind]
  rfl

def qsY : Yield := ⟨.none, .none⟩

def qsEnvEnd (e : REnv) (sc : Int) : REnv :=
  Env.set (Env.set (bindYield e qsY) "score" (.int sc)) "best" (.int sc)

/-! The three body statements composed. The two `simp only [Run.bind]` steps
below are flagged unused by the linter and are NOT: removing either one leaves
the following `rw` without its pattern (measured). -/
set_option linter.unusedSimpArgs false in
theorem qs_body (w : World) (e : REnv) (b : String) (sc gamma : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (hd : Env.lookup e "depth" = some (.int 0))
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hnomax : Env.lookup e "max" = Option.none)
    (hb : Env.lookup e "best" = some (.int (-mateUpper)))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hge : gamma ≤ sc) (hsc : -mateUpper < sc) :
    execStmts sunfish 20 ⟨w, bindYield e qsY⟩ sbBody
      = .ok ⟨w, qsEnvEnd e sc⟩ .brk := by
  have hm : Env.lookup (bindYield e qsY) "move" = some .none := lookup_bind_move e qsY
  have hd' : Env.lookup (bindYield e qsY) "depth" = some (.int 0) :=
    lookup_bind_ne qsY (by decide) (by decide) hd
  have hp' : Env.lookup (bindYield e qsY) "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp) :=
    lookup_bind_ne qsY (by decide) (by decide) hpos
  have hx' : Env.lookup (bindYield e qsY) "max" = Option.none := by
    simp [bindYield, Env.lookup_set_ne, hnomax]
  have hb' : Env.lookup (bindYield e qsY) "best" = some (.int (-mateUpper)) :=
    lookup_bind_ne qsY (by decide) (by decide) hb
  have hg' : Env.lookup (bindYield e qsY) "gamma" = some (.int gamma) :=
    lookup_bind_ne qsY (by decide) (by decide) hg
  rw [sbBody_split]
  simp only [execStmts]
  rw [execStmt_mono (qs_score w (bindYield e qsY) b sc wc0 wc1 bc0 bc1 ep kp hm hd' hp')
    (by simp) 19 (by omega)]
  simp only [Run.bind]
  rw [execStmt_mono (qs_max w (Env.set (bindYield e qsY) "score" (.int sc)) (-mateUpper) sc
    (by simp [Env.lookup_set_ne, hx']) (by simp [Env.lookup_set_ne, hb'])
    (by simp [Env.lookup_set_self])) (by simp) 18 (by omega)]
  simp only [Run.bind]
  have hmax : max (-mateUpper) sc = sc := by omega
  rw [hmax]
  rw [execStmt_mono (qs_cut w (Env.set (Env.set (bindYield e qsY) "score" (.int sc))
    "best" (.int sc)) sc gamma (by simp [Env.lookup_set_self])
    (by simp [Env.lookup_set_ne, hg']) (by simp [Env.lookup_set_ne, hm]) hge)
    (by simp) 17 (by omega)]
  simp only [Run.bind, qsEnvEnd]

def QSInv (w₁ : World) (e : REnv) : List Yield → FrameState → Prop
  | [y] => fun st => st = ⟨w₁, e⟩ ∧ y = qsY
  | _ => fun _ => False

theorem qs_fold_breaks (w₀ w₁ w' : World) (e : REnv) (a : Addr) (b : String)
    (sc gamma : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (sp : Span)
    (hev : EvalsIn sunfish ⟨w₀, e⟩ sbMovesCall (.ref a) ⟨w₁, e⟩)
    (hobj : ∃ qn lo ct stt, Heap.get? w₁.heap a = some (.generator qn lo ct stt))
    (hyield : IterSteps sunfish w₁ a (some (yieldVal qsY)) w')
    (hd : Env.lookup e "depth" = some (.int 0))
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hnomax : Env.lookup e "max" = Option.none)
    (hb : Env.lookup e "best" = some (.int (-mateUpper)))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hge : gamma ≤ sc) (hsc : -mateUpper < sc) :
    PyStmtTriple sunfish (fun st => st = ⟨w₀, e⟩)
      (.forStmt sbTarget sbMovesCall sbBody.toArray #[] sp)
      { next := fun st => st = ⟨w', qsEnvEnd e sc⟩ } := by
  obtain ⟨qn, lo, ct, stt, hgo⟩ := hobj
  refine PyStmtTriple.forGen (a := a) yieldVal (QSInv w₁ e) [qsY] rfl ?_ ?_ ?_
  · rintro st rfl
    exact ⟨⟨w₁, e⟩, qn, lo, ct, stt, hev, hgo, ⟨rfl, rfl⟩⟩
  · rintro st hI; exact absurd hI (by simp [QSInv])
  · rintro x rest st hI
    match rest with
    | [] =>
      obtain ⟨hst, rfl⟩ := hI
      cases hst
      refine ⟨w', bindYield e qsY, hyield, bind_eq _ _ qsY, ?_⟩
      refine PyTriple.of_exec ?_
      rintro st' rfl
      refine ⟨20, ?_⟩
      show PyPost.holds _ (execStmts sunfish 20 ⟨w', bindYield e qsY⟩ sbBody.toArray.toList)
      rw [show sbBody.toArray.toList = sbBody from rfl,
        qs_body w' e b sc gamma wc0 wc1 bc0 bc1 ep kp hd hpos hnomax hb hg hge hsc]
      exact rfl
    | _ :: _ => exact absurd hI (by simp [QSInv])

/-- **The interpreter's answer IS the spec-side fold's.** `qs_fold_breaks`
leaves `best = pos.score`; `fold_standpat` (§3) says the round schedule
`[standPat sc]` folds to exactly that, with the `cut` terminal. This one line
is the bridge between §4's interpreter gates and §7's `fold_report`, and it is
what makes the fold's landing mean something rather than merely typecheck. -/
theorem qs_fold_agrees (gamma sc : Int) (hge : gamma ≤ sc) (hsc : -mateUpper < sc) :
    foldFrom gamma (-mateUpper) false [standPat sc] = (sc, false, .cut) := by
  rw [fold_standpat gamma sc [] hge, show max (-mateUpper) sc = sc from by omega]

/-! ### Statements 14, 16 and 17 — three quarters of the tail

The correction is DEAD at depth 0, the eviction never fires, and the return
hands back `best`. What is left of `QSStandPat` after these is statement 15,
the table STORE — the one tail statement that changes the heap, and the one
§6's `sf_store` is waiting for. -/

/-- The correction has NO `else` — sharper than `sbCorr_lit`, which left the
arm existential, and needed because the dead branch must REDUCE. -/
theorem sbCorr_noElse : ∃ (bx : Expr) (bd : Array Stmt) (p0 p1 p2 p3 p4 p5 p6 : Span),
    sbCorr = .ifStmt (.boolOp .and
        #[.name "depth" p0, .unaryOp .not (.name "live" p1) p2,
          .call (.name "all" p3) #[bx] #[] Option.none p4] p5) bd #[] p6 :=
  ⟨_, _, _, _, _, _, _, _, _, rfl⟩

/-- **GATE — the terminality correction is DEAD at depth 0.** -/
theorem corr_dead (w : World) (e : REnv)
    (hd : Env.lookup e "depth" = some (.int 0)) :
    execStmt sunfish 10 ⟨w, e⟩ sbCorr = .ok ⟨w, e⟩ .next := by
  obtain ⟨bx, bd, p0, p1, p2, p3, p4, p5, p6, h⟩ := sbCorr_noElse
  have hc : evalExpr sunfish 9 ⟨w, e⟩
      (.boolOp .and
        #[.name "depth" p0, .unaryOp .not (.name "live" p1) p2,
          .call (.name "all" p3) #[bx] #[] Option.none p4] p5)
        = .ok ⟨w, e⟩ (.int 0) := by
    have h1 : evalExpr sunfish 7 ⟨w, e⟩ (.name "depth" p0) = .ok ⟨w, e⟩ (.int 0) := by
      py_simp [-globalsFold, -globalsStep, hd]
    rw [evalExpr]
    exact boolChain_and_falsy (F := 7) h1 rfl
  rw [h, execStmt_if_false hc rfl]
  simp only [execStmts]

/-- **GATE — `return best`. -/
theorem ret_best (w : World) (e : REnv) (bst : Int)
    (hb : Env.lookup e "best" = some (.int bst)) :
    execStmt sunfish 8 ⟨w, e⟩ sbRet = .ok ⟨w, e⟩ (.ret (.int bst)) := by
  obtain ⟨p0, p1, h⟩ := sbRet_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hb]

theorem tsG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst
    "TABLE_SIZE" = some (some (.int tableSize)) := rfl
theorem lenG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "len"
    = Option.none := rfl
theorem lenF : findFunction sunfish "len" = Option.none := rfl
theorem lenNotFun : ¬ ∃ x, x ∈ sunfish.functions ∧ x.name = "len" := by
  simpa [findFunction] using lenF
theorem lenCls : findClassAux sunfish.classes.toList "len" 0 = Option.none := rfl
theorem lenNT : findNamedTupleAux sunfish.namedtuples.toList "len" = Option.none := rfl

/-- **GATE — the eviction never fires**: a table holding `n <= TABLE_SIZE`
entries is not over the cap, and after a QS node's single store it holds one. -/
theorem evict_dead (w : World) (e : REnv) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf : Int) (es : Array (RVal × RVal)) (sv : Nat)
    (hslf : Env.lookup e "self" = some (.ref sa))
    (hnolen : Env.lookup e "len" = Option.none)
    (hnots : Env.lookup e "TABLE_SIZE" = Option.none)
    (hobj : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict : Heap.get? w.heap ts = some (.dict es sv))
    (hsz : (es.size : Int) ≤ tableSize) :
    execStmt sunfish 12 ⟨w, e⟩ sbEvict = .ok ⟨w, e⟩ .next := by
  obtain ⟨bd, p0, p1, p2, p3, p4, p5, p6, h⟩ := sbEvict_lit
  simp only [Heap.get?] at hobj hdict
  have hc : evalExpr sunfish 11 ⟨w, e⟩
      (.compare (.call (.name "len" p0) #[.attribute (.name "self" p1) "tp_score" p2] #[]
        Option.none p3) #[.gt] #[.name "TABLE_SIZE" p4] p5)
        = .ok ⟨w, e⟩ (.bool false) := by
    py_simp [-globalsFold, -globalsStep, hslf, hnolen, hnots, lenG, lenNotFun, lenCls,
      lenNT, tsG, hobj, hdict, searcherObj]
    omega
  rw [h, execStmt_if_false hc rfl]
  simp only [execStmts]

/-! ### Statement 15 — THE TABLE STORE, and where the two halves meet

The last of the eighteen. `self.tp_score[pos, depth] = Entry(best, entry.upper)
if best >= gamma else Entry(entry.lower, best)` — the only tail statement that
changes the heap, and at a stand-pat node the conditional takes its `best >=
gamma` arm, so what lands is `Entry(pos.score, MATE_UPPER)`.

The gate concludes with the COMPUTED heap rather than an abstract `h'`: the
subscript-store path inlines past `heapStore` into `Heap.update`'s `dif`, so a
`heapStore` premise cannot match what `py_simp` leaves. `bound_enters` took the
same shape for the same reason. The two `Array.set` terms then differ only in
their liveness PROOF, and proof irrelevance closes it — one `rfl`.

**And this is where §4 and §7 meet.** `sf_store` (§6) needs `lo ≤ V p d ∧ V p d
≤ up`: the invariant half, proved since §L15, waiting for someone to discharge
its hypothesis. `fold_report` (§7) produces `Report gamma best (V p d)`: the
arithmetic half, proved since §L16, with nothing to hand it to.
`sf_store_from_report` is the join, and it is stated in §7 where both halves are
in scope: a fail-high report IS the lower bound the store's entry needs, and
`gamma ≤ best` is what forces `Report`'s right disjunct. The upper bound is the
mate band, which stays a model-side premise. -/

/-- The dict object the QS store leaves at `tp_score`: the table plus one
`(pos, 0) |-> Entry(best, MATE_UPPER)` entry, with the shape version bumped iff
the key was new. -/
def sbStored (es : Array (RVal × RVal)) (sv : Nat) (pv : RVal) (sc : Int) : Obj :=
  .dict (dictStore es.toList (tpKey pv 0) (entryOf sc mateUpper)).1.toArray
    (if (dictStore es.toList (tpKey pv 0) (entryOf sc mateUpper)).2 = true then sv + 1 else sv)

theorem store_runs (w : World) (e : REnv) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf sc gamma : Int) (pv : RVal) (es : Array (RVal × RVal)) (sv : Nat)
    (hslf : Env.lookup e "self" = some (.ref sa))
    (hpos : Env.lookup e "pos" = some pv)
    (hd : Env.lookup e "depth" = some (.int 0))
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
      = .ok ⟨{ w with heap := w.heap.set ts (sbStored es sv pv sc) hlt }, e⟩ .next := by
  obtain ⟨p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,
    hs'⟩ := sbStore_lit
  obtain ⟨sp, hnt⟩ := entryNTAux
  simp only [Heap.get?] at hobj hdict
  have hc : evalExpr sunfish 19 ⟨w, e⟩ (.unaryOp .not (.name "root" p0) p1)
      = .ok ⟨w, e⟩ (.bool true) := by
    py_simp [-globalsFold, -globalsStep, hroot]
  rw [hs', execStmt_if_true hc rfl]
  simp only [execStmts]
  py_simp [-globalsFold, -globalsStep, -heapStore, hk, hslf, hpos, hd, hb, hg, hen, hnoe, entryDefault,
    entryG, entryNotFun, entryClsAux, hnt, hobj, hdict, searcherObj, entryOf, tpKey, sbStored, dif_pos hlt]
  rw [if_pos hge]
  py_simp [-globalsFold, -globalsStep, -heapStore, hk, hslf, hpos, hd, hb, hg, hen, hnoe, entryDefault,
    entryG, entryNotFun, entryClsAux, hnt, hobj, hdict, searcherObj, entryOf, tpKey, sbStored, dif_pos hlt]
  rfl

/-! ### The chain: statements 6–12 and 13–17

`head_runs`' pattern, applied. Both segments are stated over an ABSTRACT entry
frame with its lookup facts as hypotheses — more general than the concrete
frame, and the through-chain lookups are then `Env.lookup_set_ne` by `simp`
rather than `rfl`, which is the only place the concrete/abstract choice shows.

Three things cost a cycle each and are worth keeping. **Frame abbreviations
must be `def`, not `abbrev`**: a reducible frame lets `isDefEq` unfold into
`sbW2`, whose `sbMovesClosure` projects off the 1MB literal, and the
elaboration diverges. **Pass the WORLD explicitly** at every link for the same
reason — a `_` hole makes unification search where a term would not. And every
`execStmts_singleton (F := k)` must have `k + 1` equal to its gate's own fuel;
three off-by-ones here each presented as a `whnf` timeout, not as a type error,
which is a genuinely misleading symptom worth recognising by shape. -/

/-- The frame after statement 7, and the ones after 8-12. -/
def G3 (e : REnv) : REnv := Env.set e "killer" .none
def G4 (w : World) (e : REnv) : REnv := sbEnvDef w (G3 e)
def G5 (w : World) (e : REnv) (av : Bool) : REnv := Env.set (G4 w e) "calm" (.bool av)
def G6 (w : World) (e : REnv) (av : Bool) : REnv := Env.set (G5 w e av) "guard" (.bool av)
def G7 (w : World) (e : REnv) (av : Bool) (sc : Int) : REnv :=
  Env.set (G6 w e av) "t" (.int (sc + nullMargin))
def G8 (w : World) (e : REnv) (av : Bool) (sc : Int) : REnv :=
  Env.set (G7 w e av sc) "nmr" (.bool false)
def G9 (w : World) (e : REnv) (av : Bool) (sc : Int) : REnv :=
  Env.set (Env.set (G8 w e av sc) "best" (.int (-mateUpper))) "live" (.bool false)

theorem mid_runs (w : World) (e : REnv) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma sc : Int) (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (av : Bool) (sv : Nat)
    (hobj : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hmove : Heap.get? w.heap tm = some (.dict #[] sv))
    (hk : hashableKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) = true)
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hslf : Env.lookup e "self" = some (.ref sa))
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hd : Env.lookup e "depth" = some (.int 0))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hroot : Env.lookup e "root" = some (.bool false))
    (_hnmax : Env.lookup e "max" = Option.none)
    (hnabs : Env.lookup e "abs" = Option.none)
    (hnnm : Env.lookup e "NULL_MARGIN" = Option.none)
    (hnmu : Env.lookup e "MATE_UPPER" = Option.none)
    (hng : Env.lookup e "guard" = Option.none)
    (hnc : Env.lookup e "<cell>guard" = Option.none)
    (hband : -750 < sc ∧ sc < 750)
    (hgen : evalExpr sunfish 5
        ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G4 w e⟩ calmG
      = .ok ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G4 w e⟩ (.bool av)) :
    ∃ f, execStmts sunfish f ⟨w, e⟩
        ([sbKiller] ++ [sbDef] ++ [sbCalm] ++ [sbGuard] ++ [sbT] ++ [sbNmr] ++ [sbAcc])
      = .ok ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp),
              G9 w e av sc⟩ .next := by
  have h6 : ∃ f, execStmts sunfish f ⟨w, e⟩ [sbKiller] = .ok ⟨w, G3 e⟩ .next :=
    ⟨16, killer_misses w e ci sa ts tm hs n dl sf (posOf b sc wc0 wc1 bc0 bc1 ep kp) sv
      hslf hpos hobj hmove hk⟩
  have h7 : ∃ f, execStmts sunfish f ⟨w, G3 e⟩ [sbDef]
      = .ok ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G4 w e⟩ .next :=
    ⟨2, execStmts_singleton (F := 0) (moves_def_allocates w (G3 e) 0 gamma 0 .none
      (posOf b sc wc0 wc1 bc0 bc1 ep kp)
      (by simp [G3, Env.lookup_set_ne, hd]) (by simp [G3, Env.lookup_set_ne, hg])
      (by simp [G3, Env.lookup_set_self]) (by simp [G3, Env.lookup_set_ne, hpos])
      (by simp [G3, Env.lookup_set_ne, hng]) (by simp [G3, Env.lookup_set_ne, hnc]))⟩
  have h8 : ∃ f, execStmts sunfish f
      ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G4 w e⟩ [sbCalm]
      = .ok ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G5 w e av⟩ .next :=
    ⟨10, execStmts_singleton (F := 8) (calm_binds (sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp)) (G4 w e) b sc wc0 wc1 bc0 bc1 ep kp av
      (by simp [G4, G3, sbEnvDef, Env.lookup_set_ne, hpos])
      (by simp [G4, G3, sbEnvDef, Env.lookup_set_ne, hnabs]) hband hgen)⟩
  have h9 : ∃ f, execStmts sunfish f
      ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G5 w e av⟩ [sbGuard]
      = .ok ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G6 w e av⟩ .next :=
    ⟨8, guard_evals (sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp)) (G5 w e av) av
      (by simp [G5, G4, G3, sbEnvDef, Env.lookup_set_ne, hroot])
      (by simp [G5, Env.lookup_set_self])⟩
  have h10 : ∃ f, execStmts sunfish f
      ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G6 w e av⟩ [sbT]
      = .ok ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G7 w e av sc⟩ .next :=
    ⟨8, null_margin_adds (sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp)) (G6 w e av) b sc wc0 wc1 bc0 bc1 ep kp
      (by simp [G6, G5, G4, G3, sbEnvDef, Env.lookup_set_ne, hpos])
      (by simp [G6, G5, G4, G3, sbEnvDef, Env.lookup_set_ne, hnnm])⟩
  have h11 : ∃ f, execStmts sunfish f
      ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G7 w e av sc⟩ [sbNmr]
      = .ok ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G8 w e av sc⟩ .next :=
    ⟨10, execStmts_singleton (F := 8) (nmr_binds (sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp)) (G7 w e av sc) av
      (by simp [G7, G6, G5, Env.lookup_set_ne, Env.lookup_set_self])
      (by simp [G7, G6, G5, G4, G3, sbEnvDef, Env.lookup_set_ne, hd]))⟩
  have h12 : ∃ f, execStmts sunfish f
      ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G8 w e av sc⟩ [sbAcc]
      = .ok ⟨sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp), G9 w e av sc⟩ .next :=
    ⟨16, acc_inits (sbW2 w gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp)) (G8 w e av sc)
      (by simp [G8, G7, G6, G5, G4, G3, sbEnvDef, Env.lookup_set_ne, hnmu]) hmu⟩
  exact execStmts_append (execStmts_append (execStmts_append (execStmts_append
    (execStmts_append (execStmts_append h6 h7 (by simp)) h8 (by simp)) h9 (by simp))
      h10 (by simp)) h11 (by simp)) h12 (by simp)

/-- The frame the fold leaves. -/
def T0 (e : REnv) (sc : Int) : REnv := qsEnvEnd e sc

/-- The world the store leaves. -/
def T1 (w4 : World) (ts : Addr) (es : Array (RVal × RVal)) (sv : Nat) (pv : RVal)
    (sc : Int) (hlt : ts < w4.heap.size) : World :=
  { w4 with heap := w4.heap.set ts (sbStored es sv pv sc) hlt }

theorem tail_runs (w2 w3 w4 : World) (e : REnv) (a : Addr) (ci : ClassId)
    (sa ts tm hs : Addr) (n dl sf gamma sc : Int)
    (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (es es' : Array (RVal × RVal)) (sv sv' : Nat)
    (hlt : ts < w4.heap.size)
    (hev : EvalsIn sunfish ⟨w2, e⟩ sbMovesCall (.ref a) ⟨w3, e⟩)
    (hgo : ∃ qn lo ct stt, Heap.get? w3.heap a = some (.generator qn lo ct stt))
    (hyield : IterSteps sunfish w3 a (some (yieldVal qsY)) w4)
    (hd : Env.lookup e "depth" = some (.int 0))
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hslf : Env.lookup e "self" = some (.ref sa))
    (hroot : Env.lookup e "root" = some (.bool false))
    (hen : Env.lookup e "entry" = some entryDefault)
    (hnmax : Env.lookup e "max" = Option.none)
    (hnoe : Env.lookup e "Entry" = Option.none)
    (hnlen : Env.lookup e "len" = Option.none)
    (hnts : Env.lookup e "TABLE_SIZE" = Option.none)
    (hb : Env.lookup e "best" = some (.int (-mateUpper)))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hobj4 : Heap.get? w4.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict4 : Heap.get? w4.heap ts = some (.dict es sv))
    (hobj5 : Heap.get? (T1 w4 ts es sv (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt).heap sa
      = some (searcherObj ci ts tm hs n dl sf))
    (hdict5 : Heap.get? (T1 w4 ts es sv (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt).heap ts
      = some (.dict es' sv'))
    (hsz : (es'.size : Int) ≤ tableSize)
    (hk : hashableKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) = true)
    (hge : gamma ≤ sc) (hsc : -mateUpper < sc) :
    ∃ f, execStmts sunfish f ⟨w2, e⟩
        ([sbFor] ++ [sbCorr] ++ [sbStore] ++ [sbEvict] ++ [sbRet])
      = .ok ⟨T1 w4 ts es sv (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt, T0 e sc⟩
          (.ret (.int sc)) := by
  have h13 : ∃ f, execStmts sunfish f ⟨w2, e⟩ [sbFor] = .ok ⟨w4, T0 e sc⟩ .next := by
    obtain ⟨sp, hfor⟩ := sbFor_lit
    rw [hfor]
    obtain ⟨f, hf⟩ := execStmt_of_stmtTriple
      (qs_fold_breaks w2 w3 w4 e a b sc gamma wc0 wc1 bc0 bc1 ep kp sp hev hgo
        hyield hd hpos hnmax hb hg hge hsc) ⟨w2, e⟩ rfl
    exact ⟨f + 2, execStmts_singleton (F := f) (execStmt_mono hf (by simp) (f + 1) (by omega))⟩
  have h14 : ∃ f, execStmts sunfish f ⟨w4, T0 e sc⟩ [sbCorr] = .ok ⟨w4, T0 e sc⟩ .next :=
    ⟨11, execStmts_singleton (F := 9) (corr_dead w4 (T0 e sc)
      (by simp [T0, qsEnvEnd, bindYield, Env.lookup_set_ne, hd]))⟩
  have h15 : ∃ f, execStmts sunfish f ⟨w4, T0 e sc⟩ [sbStore]
      = .ok ⟨T1 w4 ts es sv (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt, T0 e sc⟩ .next :=
    ⟨21, execStmts_singleton (F := 19) (store_runs w4 (T0 e sc) ci sa ts tm hs n dl sf sc gamma
      (posOf b sc wc0 wc1 bc0 bc1 ep kp) es sv
      (by simp [T0, qsEnvEnd, bindYield, Env.lookup_set_ne, hslf])
      (by simp [T0, qsEnvEnd, bindYield, Env.lookup_set_ne, hpos])
      (by simp [T0, qsEnvEnd, bindYield, Env.lookup_set_ne, hd])
      (by simp [T0, qsEnvEnd, Env.lookup_set_self])
      (by simp [T0, qsEnvEnd, bindYield, Env.lookup_set_ne, hg])
      (by simp [T0, qsEnvEnd, bindYield, Env.lookup_set_ne, hen])
      (by simp [T0, qsEnvEnd, bindYield, Env.lookup_set_ne, hroot])
      (by simp [T0, qsEnvEnd, bindYield, Env.lookup_set_ne, hnoe])
      hobj4 hdict4 hlt hge hk)⟩
  have h16 : ∃ f, execStmts sunfish f
      ⟨T1 w4 ts es sv (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt, T0 e sc⟩ [sbEvict]
      = .ok ⟨T1 w4 ts es sv (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt, T0 e sc⟩ .next :=
    ⟨13, execStmts_singleton (F := 11)
      (evict_dead (T1 w4 ts es sv (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt) (T0 e sc)
        ci sa ts tm hs n dl sf es' sv'
        (by simp [T0, qsEnvEnd, bindYield, Env.lookup_set_ne, hslf])
        (by simp [T0, qsEnvEnd, bindYield, Env.lookup_set_ne, hnlen])
        (by simp [T0, qsEnvEnd, bindYield, Env.lookup_set_ne, hnts])
        hobj5 hdict5 hsz)⟩
  have h17 : ∃ f, execStmts sunfish f
      ⟨T1 w4 ts es sv (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt, T0 e sc⟩ [sbRet]
      = .ok ⟨T1 w4 ts es sv (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt, T0 e sc⟩
          (.ret (.int sc)) :=
    ⟨9, execStmts_singleton_flow (F := 7)
      (ret_best (T1 w4 ts es sv (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt) (T0 e sc) sc
        (by simp [T0, qsEnvEnd, Env.lookup_set_self]))⟩
  exact execStmts_append (execStmts_append (execStmts_append
    (execStmts_append h13 h14 (by simp)) h15 (by simp)) h16 (by simp)) h17 (by simp)

/-! ### THE BODY, AND THE CLOSE

`head_runs ++ mid_runs ++ tail_runs = sbB`, then `callIn`. The joins cost
nothing: all 22 frame lookups at the two join points are `rfl`, because the
chain is literal keys over `sbEnv0`'s concrete list. `sbB_split` bridges the
flat eighteen to the left-nested appends by `rfl`.

**`qs_stand_pat` is `QSStandPat`'s statement with the premises it actually
needs, and the delta is recorded rather than hidden.** §L10 wrote `QSStandPat`
before the interpreter work existed, so its premise list was a good-faith
estimate; running the chain says it is short by five:

* `ts ≠ sa` — the table is not the receiver. `QSStandPat` gives both slots'
  contents but never says they differ, so the counter bump could have clobbered
  the table.
* `-750 < pos.score < 750` — the calmness test's own band, which statement 8
  needs and the depth-0 window does not imply.
* `hev`/`hyield` — `moves()` allocating its generator and that generator's first
  step. By design, and named since §L20.
* `calmG`'s genexp answer. By design, and named since §L18.
* the post-yield and post-store heap facts — the generator step and the store
  leave the receiver and the table where the tail expects them.

`QSStandPat` itself is left EXACTLY as recorded (sharper pins never weaken), and
what it would take to close IT rather than this is one more theorem deriving the
five: three are by-design premises that belong in any honest statement, and two
(`ts ≠ sa`, the score band) are genuine omissions in the §L10 text. -/

def W1 (w : World) (h' : Heap) : World := { w with heap := h' }
def FH (sa : Addr) (pv : RVal) (gamma : Int) : REnv :=
  Env.set (EA sa pv gamma) "entry" entryDefault

set_option linter.unusedVariables false in
/-- **THE WHOLE BODY.** All eighteen statements of the shipped `Searcher.bound`,
from the entry frame to the `return`. -/
theorem body_runs (w : World) (w3 w4 : World) (h' : Heap) (a : Addr) (ci : ClassId)
    (sa ts tm hs : Addr) (n dl sf gamma sc : Int)
    (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (av : Bool)
    (sv svm : Nat) (es es' : Array (RVal × RVal)) (svs sv' : Nat)
    (hlt : ts < w4.heap.size)
    -- the head
    (hself : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hupd : Heap.update w.heap sa (searcherObj ci ts tm hs (n + 1) dl sf) = some h')
    (hclk : ¬ ((n + 1).fmod 2048 = 0))
    (hts : ts ≠ sa)
    (hdict : Heap.get? w.heap ts = some (.dict #[] sv))
    (hml : Env.lookup w.globals "MATE_LOWER" = some (.int mateLower))
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hk : hashableKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) = true)
    (hsc : -mateLower < sc) (hlo : -mateUpper < gamma) (hup : gamma ≤ mateUpper)
    -- the middle
    (hobj1 : Heap.get? (W1 w h').heap sa = some (searcherObj ci ts tm hs (n + 1) dl sf))
    (hmove1 : Heap.get? (W1 w h').heap tm = some (.dict #[] svm))
    (hmu1 : Env.lookup (W1 w h').globals "MATE_UPPER" = some (.int mateUpper))
    (hband : -750 < sc ∧ sc < 750)
    (hgen : evalExpr sunfish 5
        ⟨sbW2 (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp),
         G4 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma)⟩ calmG
      = .ok ⟨sbW2 (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp),
             G4 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma)⟩ (.bool av))
    -- the tail
    (hev : EvalsIn sunfish
      ⟨sbW2 (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp),
       G9 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma) av sc⟩
      sbMovesCall (.ref a)
      ⟨w3, G9 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma) av sc⟩)
    (hgo : ∃ qn lo ct stt, Heap.get? w3.heap a = some (.generator qn lo ct stt))
    (hyield : IterSteps sunfish w3 a (some (yieldVal qsY)) w4)
    (hobj4 : Heap.get? w4.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict4 : Heap.get? w4.heap ts = some (.dict es svs))
    (hobj5 : Heap.get? (T1 w4 ts es svs (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt).heap sa
      = some (searcherObj ci ts tm hs n dl sf))
    (hdict5 : Heap.get? (T1 w4 ts es svs (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt).heap ts
      = some (.dict es' sv'))
    (hsz : (es'.size : Int) ≤ tableSize)
    (hge : gamma ≤ sc) (hmus : -mateUpper < sc) :
    ∃ f, execStmts sunfish f
        ⟨w, sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩ sbB
      = .ok ⟨T1 w4 ts es svs (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt,
              T0 (G9 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma) av sc) sc⟩
          (.ret (.int sc)) := by
  have hH := head_runs w ci sa ts tm hs n dl sf gamma sc b wc0 wc1 bc0 bc1 ep kp sv h'
    hself hupd hclk hts hdict hml hmu hk hsc hlo hup
  have hM := mid_runs (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma) ci sa ts tm hs
    (n + 1) dl sf gamma sc b wc0 wc1 bc0 bc1 ep kp av svm hobj1 hmove1 hk hmu1
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hband hgen
  have hT := tail_runs (sbW2 (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp)) w3 w4
    (G9 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma) av sc) a ci sa ts tm hs
    n dl sf gamma sc b wc0 wc1 bc0 bc1 ep kp es es' svs sv' hlt hev hgo hyield
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hobj4 hdict4 hobj5 hdict5 hsz hk hge hmus
  rw [sbB_split]
  exact execStmts_append (execStmts_append hH hM (by simp)) hT (by simp)

theorem sbArity : arityOk sbF.params 4 = true := rfl

/-- **The boundary**: `callIn` reaches the body and carries `.ret` out. -/
theorem callIn_of_body {w w' : World} {sa : Addr} {pv : RVal} {gamma d : Int}
    {e' : REnv} {v : RVal} {F : Nat}
    (h : execStmts sunfish F ⟨w, sbEnv0 (.ref sa) pv gamma d⟩ sbB = .ok ⟨w', e'⟩ (.ret v)) :
    callIn sunfish (F + 1) w "Searcher.bound" #[.ref sa, pv, .int gamma, .int d]
      = .ok w' v := by
  obtain ⟨hfind, hargs, hloc, hgen, hbody, harity⟩ := sbF_lit
  rw [callIn, hfind]
  simp only [hargs, hloc, hgen, Bool.not_true, Bool.false_eq_true, if_neg,
    not_false_eq_true, hbody, sbCallEnv, h, Run.bind, Run.toWorld,
    show (#[RVal.ref sa, pv, RVal.int gamma, RVal.int d] : Array RVal).size = 4 from rfl,
    sbArity]

set_option linter.unusedVariables false in
/-- **QSStandPat, CLOSED** — with the premises it actually needs. -/
theorem qs_stand_pat (w : World) (w3 w4 : World) (h' : Heap) (a : Addr) (ci : ClassId)
    (sa ts tm hs : Addr) (n dl sf gamma sc : Int)
    (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (av : Bool)
    (sv svm : Nat) (es es' : Array (RVal × RVal)) (svs sv' : Nat)
    (hlt : ts < w4.heap.size)
    -- the head
    (hself : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hupd : Heap.update w.heap sa (searcherObj ci ts tm hs (n + 1) dl sf) = some h')
    (hclk : ¬ ((n + 1).fmod 2048 = 0))
    (hts : ts ≠ sa)
    (hdict : Heap.get? w.heap ts = some (.dict #[] sv))
    (hml : Env.lookup w.globals "MATE_LOWER" = some (.int mateLower))
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hk : hashableKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) = true)
    (hsc : -mateLower < sc) (hlo : -mateUpper < gamma) (hup : gamma ≤ mateUpper)
    -- the middle
    (hobj1 : Heap.get? (W1 w h').heap sa = some (searcherObj ci ts tm hs (n + 1) dl sf))
    (hmove1 : Heap.get? (W1 w h').heap tm = some (.dict #[] svm))
    (hmu1 : Env.lookup (W1 w h').globals "MATE_UPPER" = some (.int mateUpper))
    (hband : -750 < sc ∧ sc < 750)
    (hgen : evalExpr sunfish 5
        ⟨sbW2 (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp),
         G4 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma)⟩ calmG
      = .ok ⟨sbW2 (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp),
             G4 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma)⟩ (.bool av))
    -- the tail
    (hev : EvalsIn sunfish
      ⟨sbW2 (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp),
       G9 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma) av sc⟩
      sbMovesCall (.ref a)
      ⟨w3, G9 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma) av sc⟩)
    (hgo : ∃ qn lo ct stt, Heap.get? w3.heap a = some (.generator qn lo ct stt))
    (hyield : IterSteps sunfish w3 a (some (yieldVal qsY)) w4)
    (hobj4 : Heap.get? w4.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict4 : Heap.get? w4.heap ts = some (.dict es svs))
    (hobj5 : Heap.get? (T1 w4 ts es svs (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt).heap sa
      = some (searcherObj ci ts tm hs n dl sf))
    (hdict5 : Heap.get? (T1 w4 ts es svs (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt).heap ts
      = some (.dict es' sv'))
    (hsz : (es'.size : Int) ≤ tableSize)
    (hge : gamma ≤ sc) (hmus : -mateUpper < sc) :
    ∃ w' t, ∀ F ≥ t, callIn sunfish F w "Searcher.bound"
      #[.ref sa, posOf b sc wc0 wc1 bc0 bc1 ep kp, .int gamma, .int 0]
        = .ok w' (.int sc) := by
  obtain ⟨f, hf⟩ := body_runs w w3 w4 h' a ci sa ts tm hs n dl sf gamma sc b wc0 wc1 bc0 bc1
    ep kp av sv svm es es' svs sv' hlt hself hupd hclk hts hdict hml hmu hk hsc hlo hup
    hobj1 hmove1 hmu1 hband hgen hev hgo hyield hobj4 hdict4 hobj5 hdict5 hsz hge hmus
  refine ⟨T1 w4 ts es svs (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt, f + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ : ∃ F', F = F' + 1 ∧ f ≤ F' := ⟨F - 1, by omega, by omega⟩
  exact callIn_of_body (execStmts_mono hf (by simp) F' hF')

/-! ### Toward `hev`: the cell resolves at the CALL

The first of `qs_stand_pat`'s two generator premises. Both pieces below are
about the CELL — the thing that made the shipped `moves()` untypeable before
§L14 — and together they are what a `moves()` call does to the heap, minus the
address pins. -/

/-- **Calling a generator closure whose captures include a CELL.**
`EvalsIn.closureGenCall` (GenBound.lean) requires `cellsFor … cap = .ok cap` —
no cells. The shipped `moves()` has one, and its whole point is that the cell
RESOLVES at the call: the object the call allocates holds the resolved env, not
the directory. Same proof, one variable apart. -/
theorem EvalsIn.closureGenCall_cells {m : Module} {st : FrameState} {fname : String}
    {a : Addr} {nm : String} {ps : Array Param} {hg : Bool} {bd : Array Stmt}
    {cap cap' : REnv} {argEs : Array Expr} {vs : List RVal} {sp sp' : Span}
    (hlocal : Env.lookup st.locals fname = some (.ref a))
    (hnotfree : (funsHeapFree m.functions.toList && topLevelDefFree m) = false)
    (hobj : Heap.get? st.world.heap a = some (.closure nm ps true true hg true bd cap))
    (hnc : cellsFor st.world.heap st.locals cap = .ok cap')
    (harity : arityOk ps vs.length = true)
    (hargs : EvalsToList m st argEs.toList vs) :
    EvalsIn m st (.call (.name fname sp) argEs #[] Option.none sp')
      (.ref st.world.heap.size)
      ⟨{ st.world with heap :=
            st.world.heap.push (closureGenObj nm ps bd cap' vs.toArray) }, st.locals⟩ := by
  obtain ⟨ta, ha⟩ := hargs.at_least
  refine ⟨ta + 2, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ : ∃ F', F = F' + 1 ∧ ta + 1 ≤ F' := ⟨F - 1, by omega, by omega⟩
  obtain ⟨F'', rfl, hF''⟩ : ∃ F'', F' = F'' + 1 ∧ ta ≤ F'' := ⟨F' - 1, by omega, by omega⟩
  have hcall := callClosure_genCall (m := m) (fuel := F'') (w := st.world) (name := nm)
    (params := ps) (body := bd) (captured := cap') (args := vs.toArray)
    (by simpa using harity)
  rw [evalExpr]
  simp only [Array.isEmpty, Array.size_empty, hlocal, ha (F'' + 1) (by omega),
    Run.ok_bind, hnotfree, if_neg, Bool.false_eq_true, not_false_eq_true, hobj,
    Run.withLocals]
  simp only [hnc, Run.liftRes, Run.ok_bind, hcall]
  simp

/-- **The cell RESOLVES at the call, and this is the theorem that says so.**
`cellsFor` walks the closure's captures: the four plain names pass through, and
`<cell>guard` is replaced by the CALLING frame's current `guard`. The value the
`def` could not see — `guard` is assigned at statement 9, below the `def` at 7 —
arrives here, which is the entire difference between §L14's cells and the
snapshot tier they replaced. -/
theorem sbMovesCap_cells (h : Heap) (env : REnv) (acell : Addr) (gamma : Int)
    (kv pv : RVal) (av : Bool) (c : Option RVal)
    (hcell : Heap.get? h acell = some (.cell c))
    (hguard : Env.lookup env "guard" = some (.bool av)) :
    cellsFor h env (sbMovesCap acell gamma 0 kv pv)
      = .ok [("depth", .int 0), ("gamma", .int gamma), ("guard", .bool av),
             ("killer", kv), ("pos", pv)] := by
  have k1 : isCellKey "depth" = false := by simp [isCellKey, String.isPrefixOf]
  have k2 : isCellKey "gamma" = false := by simp [isCellKey, String.isPrefixOf]
  have k3 : isCellKey "<cell>guard" = true := by simp [isCellKey, String.isPrefixOf]
  have k4 : isCellKey "killer" = false := by simp [isCellKey, String.isPrefixOf]
  have k5 : isCellKey "pos" = false := by simp [isCellKey, String.isPrefixOf]
  have kn : cellName "<cell>guard" = "guard" := by rfl
  simp only [sbMovesCap, cellsFor, k1, k2, k3, k4, k5, kn, hcell, hguard,
    Bool.false_eq_true, if_false, if_true]
  rfl

/-! ## §5 The depth-bounded statements — what step 3 closes

The SPEC side is `formal/`'s fuel model, and the first thing to read off it is
that the model is **table-free**: `fuelValueD2 : Nat → Pos → Int` takes no
`gamma` and no table (`formal/Sunfish/EventuallyWide.lean`), and the bracket
it is meant to meet, `FuelBracketSpec`, quantifies a `search : Nat → Pos → Int
→ Int` with no table parameter — and is STATED, not proven. So a refinement at
a fixed depth cannot mention the table on the model side. It has two honest
forms: quantify over all table states and land on the same `(pos, depth)`
value, or restrict to a CLEARED table. This lane takes the second — the clean
initial-call case — and the general stale-table case is step 3's.

The model's depth 0 is a three-way LEAF: no fold, no window, no recursion. The
gamma-aware depth-0 quiescence lives on `formal/`'s search side as `qsStrat`,
whose second clause is `if gamma ≤ eval p then eval p`. **That clause is the
raw code's stand-pat cut**, and `fold_standpat` above is it, spec-side. -/

/-- **The depth-0 statement.** From a cleared searcher, inside the documented
window, at a position whose stand-pat already meets `gamma`, the shipped
`Searcher.bound` answers exactly `pos.score`.

Every hypothesis is one the shipped code forces:
* the three cleared tables — the model has none, so this is the case in which
  a table-free spec is meetable at all;
* `-MATE_UPPER < gamma ≤ MATE_UPPER` — the docstring's own precondition, and
  exactly what makes the two default-entry returns unreachable (the mate-band
  audit states this as `tt_sentinel_defaults_never_returned`);
* `-MATE_LOWER < pos.score` — the king-capture termination check falls through;
* `(nodes + 1) % 2048 ≠ 0` — the clock trace is an INPUT and is not consulted
  below the frontier (`bound_enters` is that half, proved);
* `NULL_MARGIN` on the globals — #236's `t = pos.score + NULL_MARGIN` runs
  before the fold even at depth 0, so the name has to resolve. `QS`, `QS_A`,
  `LMR` and `EVAL_ROUGHNESS` do NOT appear: the stand-pat cut leaves on the
  first round, and none of the four is reached before it;
* `gamma ≤ pos.score` — the stand-pat cut.

`bound_enters`, `max_evals`, `fold_standpat`, `bind_eq` and the §0 pins are the
pieces; what is NOT yet paid is the table probe's `.get` miss, the nested
`def`'s five-capture closure (one of them now a CELL), the generator's first
`IterSteps`, and the table store. Their price is measured in docs/backlog.md
§L10, and the cell's own cost in §L14. -/
def QSStandPat : Prop :=
  ∀ (w : World) (ci : ClassId) (sa ts tm hs : Addr) (n dl sf gamma sc : Int)
    (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (sv sv' : Nat),
    Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf) →
    Heap.get? w.heap ts = some (.dict #[] sv) →
    Heap.get? w.heap tm = some (.dict #[] sv') →
    Heap.get? w.heap hs = some (.pyset #[]) →
    Env.lookup w.globals "MATE_LOWER" = some (.int mateLower) →
    Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper) →
    Env.lookup w.globals "NULL_MARGIN" = some (.int nullMargin) →
    ¬ ((n + 1).fmod 2048 = 0) →
    -mateLower < sc → -mateUpper < gamma → gamma ≤ mateUpper → gamma ≤ sc →
    ∃ w' t, ∀ F ≥ t, callIn sunfish F w "Searcher.bound"
      #[.ref sa, posOf b sc wc0 wc1 bc0 bc1 ep kp, .int gamma, .int 0]
        = .ok w' (.int sc)

/-! ### The template depth 1 and depth 2 instantiate

`Hands` is world-threaded, and that is the whole induction. At depth `d` the
fold consumes a schedule `ys : List Yield`; under #236 the SCHEDULE is cheap
(static `(value, move)` pairs) and the CONSUMER is what recurses — branch 2's
null probe, branch 5b's searched move — so the child call runs between
`Hands.cons`'s `IterSteps` and the round's `Round.report`, not inside the
generator. The template survives that move intact: `Hands.cons` still carries
the world change, and the induction hypothesis at depth `d - 1` — a statement
of the form `callIn … (d-1) … = .ok w₁ (.int r)` — is still consumed one round
at a time, now as `searchedMove cap r` rather than as `y.score = -r`.

Nothing else changes: the fold, the algebra lemmas
(`foldFrom_nil`/`_cons_next`/`_cons_cut`/`_cons_settle`), the boundary bridge
and the `bind_eq` transport are depth-independent and are reused verbatim.

Four things DO change with depth and must be discharged per level:
1. the killer store inside the cutoff is gated on `depth` (`sbKill_lit`), so at
   `d ≥ 1` a real cutting move WRITES `tp_move[pos]` and the fold is no longer
   heap-free;
2. the terminality correction is gated on `depth` too (`sbCorr_lit`), so at
   `d ≥ 1` the `all(… for m in pos.gen_moves())` scan runs whenever `live` is
   false — which is where `gen_moves_drains_ref` (Examples/python/sunfish/
   genmoves_drain.lean) enters this arc, and it is already at THIS module
   literal;
3. #236's `nmr` probe recurses at `d ≥ 6` BEFORE the fold (`sbNmr_lit`), so a
   depth-6 gate owes one child call that no round accounts for;
4. the cap `moveCap` is `MATE_UPPER` above depth 3 and a static estimate at or
   below it, so the settled-cap terminal is REACHABLE only for `d ≤ 3` — above
   it branch 5a is dead and the fold has one terminal again. -/

/-! ## §6 The table lines, wired to step 3's calculus

§L13 built `LeanModels/Python/DictCalc.lean` in the general layer precisely so
that a re-pin would not touch it, and this section is the receipt. The three
lines it models —

* the probe `entry = self.tp_score.get((pos, depth), Entry(-MATE_UPPER,
  MATE_UPPER))` (`sbEntry_lit`),
* the store `self.tp_score[pos, depth] = Entry(best, entry.upper) if best >=
  gamma else Entry(entry.lower, best)` (`sbStore_lit`),
* and `Entry = namedtuple("Entry", "lower upper")` (`entryNTAux`)

— are byte-identical between the pass-7 fixture and engine master, measured
span-blind before this file was rewritten. So the wiring below is instantiation
and nothing else: no lemma in `DictCalc` was restated, and its choice-free
axiom profile is untouched. -/

/-- The decoder reads the shipped spelling. `entryBounds` goes through
`xs.toList` rather than an array-literal pattern (§L11 finding 1), so this is
an `rfl`. -/
theorem entryBounds_entryOf (lo up : Int) : entryBounds (entryOf lo up) = some (lo, up) := rfl

/-- The default decodes to the widest possible bracket — which is why a miss
is never mistaken for a bound. -/
theorem entryBounds_default : entryBounds entryDefault = some (-mateUpper, mateUpper) := rfl

/-- The shipped key is in `pairKey`'s domain, at the plain-tuple spelling. -/
theorem pairKey_tpKey (p : RVal) (d : Int) : pairKey (tpKey p d) = some (p, d) := rfl

/-- **The schema, at the engine's own `Entry`.** `V` is the value function the
docstring calls `s*` — determined by `(pos, depth)` alone, which is the
property the store's comment says a change must not break. -/
def sfBracket (V : RVal → Int → Int) : Bracket := tpBracket V

/-- It is key-determined as soon as `V` is blind to what a dict cannot tell
apart, which is the hypothesis the shipped comment already asserts. -/
theorem sfBracket_keyDetermined {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d) : (sfBracket V).KeyDetermined :=
  tpBracket_keyDetermined hV

/-- **The probe, consumed.** Off a table satisfying the schema, the shipped
`.get` answers the DEFAULT or a genuine bracket on `(pos, depth)`'s value —
`Bracket.TableAt.get` at the engine's own default. The two returns above it
(`entry.lower >= gamma`, `entry.upper < gamma`) read exactly this disjunction. -/
theorem sf_probe {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d)
    {h : Heap} {a : Addr} {p v : RVal} {d : Int}
    (ht : (sfBracket V).TableAt h a)
    (hg : heapGet h a (tpKey p d) entryDefault = .ok v) :
    v = entryDefault ∨ (sfBracket V).Holds (tpKey p d) v :=
  Bracket.TableAt.get (sfBracket_keyDetermined hV) ht hg

/-- **The store, preserved.** Writing `Entry(lo, up)` at `(pos, depth)` keeps
the invariant exactly when the entry brackets the key's value — which is
`TableOK.store`'s hypothesis, not a conjunct of the invariant (§L13 finding
2). The shipped statement ORDER is what discharges it: `best` is final by the
time this line runs, the correction included. -/
theorem sf_store {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d)
    {h h' : Heap} {a : Addr} {p : RVal} {d lo up : Int}
    (ht : (sfBracket V).TableAt h a)
    (hb : lo ≤ V p d ∧ V p d ≤ up)
    (hs : heapStore h a (tpKey p d) (entryOf lo up) = .ok h') :
    (sfBracket V).TableAt h' a := by
  refine Bracket.TableAt.store (sfBracket_keyDetermined hV) ht ?_ hs
  refine ⟨lo, up, V p d, ?_, ?_, hb.1, hb.2⟩
  · exact entryBounds_entryOf lo up
  · show (pairKey (tpKey p d)).map (fun pd => V pd.1 pd.2) = some (V p d)
    rw [pairKey_tpKey]; rfl

/-- **The recursion, absorbed.** A depth-`d` probe is blind to everything its
children write, and the invariant survives them — `SubtreeWrites`'s two
theorems at the shipped slot. `child_depth_lt` (§3) is what supplies the
`d ≠ e` side condition for every reduction the shipped code applies, at every
`depth ≥ 1`; at depth 0 it does not hold and the QS gate cuts instead. -/
theorem sf_subtree_probe {V : RVal → Int → Int} {a : Addr} {e : Int} {q : RVal}
    (hq : hashableKey q = true) {h h' : Heap}
    (hw : (sfBracket V).SubtreeWrites a e h h') :
    heapGet h' a (tpKey q e) entryDefault = heapGet h a (tpKey q e) entryDefault :=
  Bracket.SubtreeWrites.probe_stable hq hw

theorem sf_subtree_tableAt {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d) {a : Addr} {e : Int}
    {h h' : Heap} (hw : (sfBracket V).SubtreeWrites a e h h') :
    (sfBracket V).TableAt h a → (sfBracket V).TableAt h' a :=
  Bracket.SubtreeWrites.tableAt (sfBracket_keyDetermined hV) hw

/-! ## §7 THE RECURSION RULE — its spec side, paid

§L10 (c) wrote the rule's shape (*an induction hypothesis at depth `d-1`
consumed one round at a time at depth `d`*) and §L13 §8 paid its TABLE half in
the general layer. Two halves were left unwritten, and both are here:

* **what the fold does to a CHILD'S REPORT** — the arithmetic that makes a
  null-window search compose at all, and
* **what the composed statement IS** — `BoundRefines`, the depth-indexed
  proposition the induction runs on.

Everything below is arithmetic over §3's vocabulary and §6's wiring. No
interpreter, no module literal, no run: it is the layer that says what the
per-statement gates are FOR. What it does NOT contain is those gates — §L10's
remaining step-2 list, items 1–5, at the measured unit cost of one `py_simp`
per statement. `BoundRefines` is therefore STATED, in the manner of §5's
`QSStandPat`, and the step lemma that consumes it is stated too. -/

/-- **The zero-window contract, in the model's own words.**
`formal/Sunfish/CappedNull.lean` (engine repo) spells it

    def WindowReport (gamma report value : Int) : Prop :=
      (report < gamma ∧ value ≤ report) ∨ (gamma ≤ report ∧ report ≤ value)

and this is that predicate, RESTATED rather than imported: `formal/` lives in
the engine repository and this lane depends on no package. The two definitions
are deliberately identical, so a bridge between them is a rename and not an
argument. -/
def Report (gamma report value : Int) : Prop :=
  (report < gamma ∧ value ≤ report) ∨ (gamma ≤ report ∧ report ≤ value)

/-- **`Report` IS the shipped docstring**, which promises

    if gamma >  s* then s* <= r < gamma  (A better upper bound)
    if gamma <= s* then gamma <= r <= s* (A better lower bound)

— two implications keyed on where the VALUE sits, where `Report` is a
disjunction keyed on where the REPORT sits. The equivalence is what says this
lane is proving the promise the engine makes rather than a neighbouring one,
and it is not free: each direction needs the trichotomy the other side hides. -/
theorem report_iff_docstring (gamma r v : Int) :
    Report gamma r v ↔ ((v < gamma → v ≤ r ∧ r < gamma) ∧ (gamma ≤ v → gamma ≤ r ∧ r ≤ v)) := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      exact ⟨fun hv => ⟨by omega, by omega⟩, fun hv => ⟨by omega, by omega⟩⟩
  · intro h
    by_cases hv : v < gamma
    · have hd := h.1 hv; exact Or.inl ⟨by omega, by omega⟩
    · have hd := h.2 (by omega); exact Or.inr ⟨by omega, by omega⟩

/-- Negating a child's report carries it to the parent's window — the integer
zero-window convention, and `formal/`'s `WindowReport.negate` verbatim. -/
theorem Report.negate {gamma r v : Int} (h : Report (1 - gamma) r v) :
    Report gamma (-r) (-v) := by
  rcases h with h | h
  · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inl ⟨by omega, by omega⟩

/-- And a `min` with a fixed cap survives it — `formal/`'s `WindowReport.cap`.
Together with `negate` this is the whole of `min(cap, -self.bound(…))`. -/
theorem Report.cap (cap : Int) {gamma r v : Int} (h : Report gamma r v) :
    Report gamma (min cap r) (min cap v) := by
  rcases h with h | h <;> simp only [Report, Int.min_def] <;> split <;> split <;> omega

/-! ### The fold's bracket algebra

`fold` walks `Round`s; the contract is about the number it ends with. These
are the five facts that connect the two, one induction each. -/

/-- The number a round contributes to `best`. Both terminals fold with `max`,
so both have one. -/
def Round.score : Round → Int
  | .report sc _ => sc
  | .settle cap => cap

/-- **The fail-high invariant.** A number the fold may hold is either below
the window — where the contract says nothing about it — or a genuine lower
bound on the node's value.

This predicate is exactly why a null-window search COMPOSES. A child that
fails HIGH at `1 - gamma` reports `child ≥ 1 - gamma`, so its negation is at
most `gamma - 1`: strictly below the parent's window, a number the parent can
never fail high on. A child that fails LOW reports an upper bound, whose
negation is a genuine lower bound. Both land in `Sound`, `Sound` is closed
under `max`, and `max` is the whole fold. -/
def Sound (gamma value x : Int) : Prop := x < gamma ∨ x ≤ value

theorem Sound.max {gamma value x y : Int} (hx : Sound gamma value x)
    (hy : Sound gamma value y) : Sound gamma value (max x y) := by
  simp only [Sound] at hx hy ⊢; omega

/-- **The fold preserves it**, through both terminals and the cut. -/
theorem foldFrom_sound {gamma value : Int} : ∀ (rs : List Round) (best : Int) (live : Bool),
    Sound gamma value best → (∀ r ∈ rs, Sound gamma value r.score) →
    Sound gamma value (foldFrom gamma best live rs).1
  | [], best, live, hb, _ => by rw [foldFrom_nil]; exact hb
  | .settle cap :: rs, best, live, hb, hrs => by
      rw [foldFrom_cons_settle]
      exact hb.max (hrs (.settle cap) (by simp))
  | .report sc lv :: rs, best, live, hb, hrs => by
      by_cases hc : gamma ≤ max best sc
      · rw [foldFrom_cons_cut gamma best live lv sc rs hc]
        exact hb.max (hrs (.report sc lv) (by simp))
      · rw [foldFrom_cons_next gamma best live lv sc rs hc]
        exact foldFrom_sound rs _ _ (hb.max (hrs (.report sc lv) (by simp)))
          (fun r hr => hrs r (by simp [hr]))

/-- **The fold never lowers `best`.** -/
theorem foldFrom_ge {gamma : Int} : ∀ (rs : List Round) (best : Int) (live : Bool),
    best ≤ (foldFrom gamma best live rs).1
  | [], best, live => by rw [foldFrom_nil]; exact Int.le_refl best
  | .settle cap :: rs, best, live => by
      rw [foldFrom_cons_settle]; show best ≤ max best cap; omega
  | .report sc lv :: rs, best, live => by
      by_cases hc : gamma ≤ max best sc
      · rw [foldFrom_cons_cut gamma best live lv sc rs hc]; show best ≤ max best sc; omega
      · rw [foldFrom_cons_next gamma best live lv sc rs hc]
        have h := foldFrom_ge (gamma := gamma) rs (max best sc) (live || lv)
        omega

/-- **The `cut` terminal really is a fail-high.** -/
theorem foldFrom_cut_ge {gamma : Int} : ∀ (rs : List Round) (best : Int) (live : Bool),
    (foldFrom gamma best live rs).2.2 = Exit.cut → gamma ≤ (foldFrom gamma best live rs).1
  | [], best, live, h => by rw [foldFrom_nil] at h; simp at h
  | .settle cap :: rs, best, live, h => by
      rw [foldFrom_cons_settle] at h; simp at h
  | .report sc lv :: rs, best, live, h => by
      by_cases hc : gamma ≤ max best sc
      · rw [foldFrom_cons_cut gamma best live lv sc rs hc]; exact hc
      · rw [foldFrom_cons_next gamma best live lv sc rs hc] at h ⊢
        exact foldFrom_cut_ge rs _ _ h

/-- **When the fold RAN OUT it consumed every round**, so every round's score
is under the answer. This is the fail-low half's only ingredient at the `ran`
terminal. -/
theorem foldFrom_ran_ge {gamma : Int} : ∀ (rs : List Round) (best : Int) (live : Bool),
    (foldFrom gamma best live rs).2.2 = Exit.ran →
    ∀ r ∈ rs, r.score ≤ (foldFrom gamma best live rs).1
  | [], best, live, _, r, hr => by simp at hr
  | .settle cap :: rs, best, live, h, r, hr => by
      rw [foldFrom_cons_settle] at h; simp at h
  | .report sc lv :: rs, best, live, h, r, hr => by
      by_cases hc : gamma ≤ max best sc
      · rw [foldFrom_cons_cut gamma best live lv sc rs hc] at h; simp at h
      · rw [foldFrom_cons_next gamma best live lv sc rs hc] at h ⊢
        rcases List.mem_cons.mp hr with rfl | hr'
        · have hg := foldFrom_ge (gamma := gamma) rs (max best sc) (live || lv)
          show sc ≤ (foldFrom gamma (max best sc) (live || lv) rs).1
          omega
        · exact foldFrom_ran_ge rs _ _ h r hr'

/-- **And when it SETTLED, the cap it folded is under the answer** — and the
cap is one of the schedule's own rounds, which is what lets a caller state the
futility premise over `rs` rather than over the fold's internals. -/
theorem foldFrom_settled_ge {gamma : Int} : ∀ (rs : List Round) (best : Int) (live : Bool),
    (foldFrom gamma best live rs).2.2 = Exit.settled →
    ∃ cap, Round.settle cap ∈ rs ∧ cap ≤ (foldFrom gamma best live rs).1
  | [], best, live, h => by rw [foldFrom_nil] at h; simp at h
  | .settle cap :: rs, best, live, _ => by
      refine ⟨cap, by simp, ?_⟩
      rw [foldFrom_cons_settle]; show cap ≤ max best cap; omega
  | .report sc lv :: rs, best, live, h => by
      by_cases hc : gamma ≤ max best sc
      · rw [foldFrom_cons_cut gamma best live lv sc rs hc] at h; simp at h
      · rw [foldFrom_cons_next gamma best live lv sc rs hc] at h ⊢
        obtain ⟨cap, hm, hle⟩ := foldFrom_settled_ge rs _ _ h
        exact ⟨cap, by simp [hm], hle⟩

/-! ### The two halves of the contract -/

/-- **FAIL-HIGH SOUNDNESS.** If every round the schedule can produce is
`Sound` and the fold ends at or above the window, its answer is a real lower
bound. No exhaustiveness, no futility, no depth: this half is free. -/
theorem fold_failHigh {gamma value best : Int} {live : Bool} {rs : List Round}
    (hb : Sound gamma value best) (hrs : ∀ r ∈ rs, Sound gamma value r.score)
    (hge : gamma ≤ (foldFrom gamma best live rs).1) :
    (foldFrom gamma best live rs).1 ≤ value := by
  rcases foldFrom_sound rs best live hb hrs with h | h
  · omega
  · exact h

/-- **FAIL-LOW COMPLETENESS**, and it is the half that costs. Below the window
the contract claims the answer is an UPPER bound, and a fold that left early
has not looked at everything. Two premises pay for the two early exits:

* `hattain` — the schedule ATTAINS the value somewhere (the model's negamax
  maximum is reached by some move), which covers the `ran` terminal;
* `hfut` — the FUTILITY BET: a settled cap bounds the value. On the shipped
  stream that is the sorted order's promise, and it is not a fact about the
  fold — see `settle_needs_futility`.

The `cut` terminal is excluded by hypothesis rather than paid for: there the
answer is at or above the window and the other half applies. -/
theorem fold_failLow {gamma value best : Int} {live : Bool} {rs : List Round}
    (hattain : value ≤ best ∨ ∃ r ∈ rs, value ≤ r.score)
    (hfut : ∀ cap, Round.settle cap ∈ rs → value ≤ cap)
    (hnc : (foldFrom gamma best live rs).2.2 ≠ Exit.cut) :
    value ≤ (foldFrom gamma best live rs).1 := by
  cases hex : (foldFrom gamma best live rs).2.2 with
  | cut => exact absurd hex hnc
  | settled =>
      obtain ⟨cap, hm, hle⟩ := foldFrom_settled_ge rs best live hex
      exact Int.le_trans (hfut cap hm) hle
  | ran =>
      rcases hattain with h | ⟨r, hr, hv⟩
      · exact Int.le_trans h (foldFrom_ge rs best live)
      · exact Int.le_trans hv (foldFrom_ran_ge rs best live hex r hr)

/-- **THE FOLD'S HALF OF THE RECURSION RULE.** The two halves assembled: the
shipped contract at one node, from a classified schedule.

Read against the source this is the whole of `for val, move in moves(): …`
plus `return best`, with the correction and the store elsewhere — and the
hypotheses are, in order, the accumulator's initialisation, the branch
classification (§3, and `searchedMove_sound` below is how a child pays it),
the model's negamax maximum, and the sorted stream's futility bet. -/
theorem fold_report {gamma value best : Int} {live : Bool} {rs : List Round}
    (hb : Sound gamma value best) (hrs : ∀ r ∈ rs, Sound gamma value r.score)
    (hattain : value ≤ best ∨ ∃ r ∈ rs, value ≤ r.score)
    (hfut : ∀ cap, Round.settle cap ∈ rs → value ≤ cap) :
    Report gamma (foldFrom gamma best live rs).1 value := by
  by_cases hge : gamma ≤ (foldFrom gamma best live rs).1
  · exact Or.inr ⟨hge, fold_failHigh hb hrs hge⟩
  · refine Or.inl ⟨by omega, fold_failLow hattain hfut ?_⟩
    intro hcut
    exact hge (foldFrom_cut_ge rs best live hcut)

/-- **The futility premise cannot be dropped, and here is the schedule that
drops it.** Window 100, value 50, a settled cap of 10 ahead of a round worth
exactly 50: every round is `Sound`, the value IS attained by the schedule, and
the fold still answers 10 — a number that is neither a lower bound (it is
below the window) nor an upper bound (the value is 50).

So `bound_refines_fuelModel` is **false without a futility side condition**.
The shipped code's own justification is the comment on the break — *"the
stream being sorted, [the cap answers] for everything after it"* — which is a
property of `moves()`'s ordering, not of the fold; the fold cannot supply it
and this lane must not pretend otherwise. `hfut` is where it enters. -/
theorem settle_needs_futility :
    ∃ (gamma value best : Int) (live : Bool) (rs : List Round),
      Sound gamma value best ∧ (∀ r ∈ rs, Sound gamma value r.score) ∧
      (value ≤ best ∨ ∃ r ∈ rs, value ≤ r.score) ∧
      (foldFrom gamma best live rs).2.2 = Exit.settled ∧
      ¬ Report gamma (foldFrom gamma best live rs).1 value := by
  refine ⟨100, 50, 0, false, [settledCap 10, standPat 50], Or.inl (by decide), ?_,
    Or.inr ⟨standPat 50, by simp, by decide⟩, rfl, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)
  · have hf : (foldFrom 100 0 false [settledCap 10, standPat 50]).1 = 10 := by decide
    rw [hf]
    rintro (⟨-, h2⟩ | ⟨h1, -⟩)
    · exact absurd h2 (by decide)
    · exact absurd h1 (by decide)

/-! #### Pricing the futility premise as a THEOREM

`hfut` is a hypothesis today. The question is whether it can be a theorem, and
reading the shipped ordering line answers it — in two halves, only one of which
this lane can pay.

    yield from sorted(((v, m) for m in pos.gen_moves()
                       if (v := pos.value(m)) >= QS or depth), reverse=True)

**(a) The SORTEDNESS half is provable, and its core is below.** The stream is
descending in `val`, and `moveCap` is MONOTONE in `val`, so a cap under the
window stays under it for every later move — which is exactly the *"the stream
being sorted, [the cap answers] for everything after it"* the source claims.
`moveCap_mono` and `moveCap_lt_of_tail` are that claim at the cap; what remains
is to carry it from one cap to the fold's TAIL, which needs the drained ordered
list — an object `sf_order` already produces and `gen_moves_drains_ref` already
specifies. A session's work in this lane, not a research question.

**(b) The PER-MOVE bound is not provable here, and naming it is the point.**
Sortedness says the tail's caps are low; it does not say a cap bounds the
tail's true VALUES. That step is `-V(child m) ≤ moveCap depth pos.score (value
m)` — a property of the evaluation function against the search value, which no
amount of reading `bound()` establishes. The shipped comment points at exactly
this (`CapInBand in CappedMove.lean`, *"and its caveat if piece["Q"] ever grows
past ~2400"*).

**So the answer to "can `bound_refines_fuelModel` drop its futility premise" is
YES BY DEFINITION and NO BY THEOREM**, and which one holds is a choice about
the model, not about the code: the docstring DEFINES `s*` to include *"null
moves, QS, futility and the reductions"*, and under that definition (b) is
definitional and (a) is the whole content. Against a model whose value is the
unreduced, unpruned negamax, (b) is a genuine axiom and belongs in `formal/`.
Either way the premise stays VISIBLE, which is what `settle_needs_futility`
bought.

**THE CHOICE, TAKEN (default, pending ratification — docs/backlog.md §L18).**
`bound_refines_fuelModel` is stated against the DOCSTRING's `s*`: the promise
`report_iff_docstring` already pins, where (b) is definitional. `formal/`'s
`CapInBand` (`formal/Sunfish/CappedMove.lean`) is the recorded axiom for the
unreduced-negamax gap, and the two repositories split the claim cleanly — this
lane proves the CODE KEEPS ITS OWN DOCUMENTED PROMISE, `formal/` carries the
search-theory content. The premise STRUCTURE below is deliberately unchanged by
the choice: `hneg` and `hfut` are hypotheses either way, so the two readings are
one definition of `V` apart and restating is a rename, not a reproof. -/

/-- The futility cap is monotone in the move's static value — the first half of
what the sorted stream buys. -/
theorem moveCap_mono {depth score v1 v2 : Int} (h : v1 ≤ v2) :
    moveCap depth score v1 ≤ moveCap depth score v2 := by
  unfold moveCap; split <;> omega

/-- And so a cap below the window stays below it for every LATER move on a
descending stream. This is the shipped break's own justification, at one step. -/
theorem moveCap_lt_of_tail {depth score v v' gamma : Int} (hle : v' ≤ v)
    (h : moveCap depth score v < gamma) : moveCap depth score v' < gamma :=
  Int.lt_of_le_of_lt (moveCap_mono hle) h

/-! ### Consuming the induction hypothesis

The rounds a depth-`d` node can produce are §3's five branch constructors.
Three of them need no child; two are where the recursion enters, and both take
the same route — `Report.negate` then `Report.cap`, which is `formal/`'s
`cappedNull_report` at the parent's window. -/

/-- **The recursion's consumption step: one searched move** (branch 5b,
`score = min(cap, -self.bound(pos.move(move), 1 - gamma, move_depth))`).

The child runs at the COMPLEMENTARY window `1 - gamma`; `hchild` is the
induction hypothesis at depth `d-1` read through `BoundRefines`, and `hneg` is
the model's negamax step — the parent's value is at least the negation of this
child's. Nothing else is needed: the futility cap cannot break the direction
the contract needs, because `min` only lowers.

**`hneg` is where the REDUCTIONS enter, and it is the same kind of premise as
`hfut`.** The child is searched at `moveDepth depth lmr nmr`, not at `depth -
1`, so `-childValue ≤ value` is not the textbook negamax inequality — it holds
because the docstring DEFINES `s*` to include *"null moves, QS, futility and
the reductions"*, i.e. `V pos d` is the value of the tree the code actually
walks. That definition is what makes `s*` a function of `(pos, depth)` alone
rather than of the reduction flags, and it is also what a bridge to `formal/`'s
`fuelValueD2` has to check: a model whose value is the UNREDUCED negamax owes
`hneg` a proof, not a definition. -/
theorem searchedMove_sound {gamma cap childReport childValue value : Int}
    (hchild : Report (1 - gamma) childReport childValue)
    (hneg : -childValue ≤ value) :
    Sound gamma value (searchedMove cap childReport).score := by
  rcases (hchild.negate).cap cap with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact Or.inl h1
  · refine Or.inr ?_
    show min cap (-childReport) ≤ value
    omega

/-- **And one null-move pass** (branch 2). Same route, one extra arm: when the
capped report still meets the window AND `pos.king_capture()` produced a move,
the shipped line substitutes the exact `MATE_UPPER` token. That substitution
is not a bound the search computed — it is the docstring's *"if the opponent
king capturable: r = MATE_UPPER"* promise — so it enters as its own
hypothesis, discharged by the king-capture fact and never by arithmetic. -/
theorem searchedPass_sound {gamma cap childReport childValue value : Int} {proof : Bool}
    (hchild : Report (1 - gamma) childReport childValue)
    (hneg : -childValue ≤ value)
    (hproof : proof = true → mateUpper ≤ value) :
    Sound gamma value (searchedPass gamma cap childReport proof).score := by
  unfold searchedPass
  split
  · rename_i hguard
    exact Or.inr (hproof ((Bool.and_eq_true _ _).mp hguard).2)
  · exact searchedMove_sound (cap := cap) hchild hneg

/-- Branches 1 and 4 need no child, only the model's own clause about the
position: the QS stand-pat is a lower bound (`qsStrat`'s second clause), and an
intrinsic mate-band value IS a king capture. -/
theorem report_sound {gamma value sc : Int} {lv : Bool} (h : sc ≤ value) :
    Sound gamma value (Round.report sc lv).score := Or.inr h

/-- **Branch 3 and branch 5a need NOTHING at all.** Both fire under a shipped
guard of the form `cap < gamma`, so both are `Sound` by the LEFT disjunct: a
static estimate below the window is a number the contract is simply blind to.

That is the asymmetry worth naming — the futility estimates are free for the
fail-HIGH half and are exactly what `fold_failLow` has to buy back. -/
theorem cappedPass_sound {gamma value cap : Int} (h : cap < gamma) :
    Sound gamma value (cappedPass cap).score := Or.inl h

theorem settledCap_sound {gamma value cap : Int} (h : cap < gamma) :
    Sound gamma value (settledCap cap).score := Or.inl h

/-! ### The table, threaded through the whole body -/

/-- **The body's table effect, end to end**: the children write, then the node
stores its own entry. `Bracket.SubtreeWrites.trans` is what makes the fold's
whole schedule ONE subtree — the relation is already a chain, so composing
rounds costs an append — and this is `TableOK` threaded beside `LoopFrame`,
which is what §L13's "what step 3 still owes" listed third.

`e` is the depth the parent's own key uses; `hkids` at `e` is exactly what
`child_depth_lt` supplies at every `depth ≥ 1`. -/
theorem sf_body_tableAt {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d)
    {ts : Addr} {e : Int} {h h₁ h₂ : Heap} {p : RVal} {d lo up : Int}
    (ht : (sfBracket V).TableAt h ts)
    (hkids : (sfBracket V).SubtreeWrites ts e h h₁)
    (hb : lo ≤ V p d ∧ V p d ≤ up)
    (hs : heapStore h₁ ts (tpKey p d) (entryOf lo up) = .ok h₂) :
    (sfBracket V).TableAt h₂ ts :=
  sf_store hV (sf_subtree_tableAt hV hkids ht) hb hs

/-- And the probe at the top of the body is blind to all of it — `n` children
compose by `trans`, so this needs no theorem beyond §6's. -/
theorem sf_rounds_probe {V : RVal → Int → Int} {ts : Addr} {e : Int} {q : RVal}
    (hq : hashableKey q = true) {h h₁ h₂ : Heap}
    (c₁ : (sfBracket V).SubtreeWrites ts e h h₁)
    (c₂ : (sfBracket V).SubtreeWrites ts e h₁ h₂) :
    heapGet h₂ ts (tpKey q e) entryDefault = heapGet h ts (tpKey q e) entryDefault :=
  sf_subtree_probe hq (c₁.trans c₂)

/-- **WHERE THE TWO HALVES MEET.** `sf_store` (§6) has needed `lo ≤ V p d ∧ V p
d ≤ up` since §L15 with nothing to discharge it; `fold_report` (§7) has produced
`Report gamma best (V p d)` since §L16 with nothing to hand it to. This is the
join: a FAIL-HIGH report is exactly the lower bound the store's entry claims,
because `gamma ≤ best` forces `Report`'s right disjunct. `store_runs` (§4) is
the interpreter run that puts the entry there, so the three sections close a
circle — the code stores a bound, the fold proves it is one, and the calculus
keeps the table's invariant across it.

`hband` stays a premise: `V p d ≤ MATE_UPPER` is the mate band, a model-side
fact about the value function and not something the store can establish. -/
theorem sf_store_from_report {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d)
    {h h' : Heap} {ts : Addr} {p : RVal} {d gamma sc : Int}
    (ht : (sfBracket V).TableAt h ts)
    (hrep : Report gamma sc (V p d))
    (hge : gamma ≤ sc)
    (hband : V p d ≤ mateUpper)
    (hs : heapStore h ts (tpKey p d) (entryOf sc mateUpper) = .ok h') :
    (sfBracket V).TableAt h' ts := by
  refine sf_store hV ht ⟨?_, hband⟩ hs
  rcases hrep with ⟨h1, -⟩ | ⟨-, h2⟩
  · omega
  · exact h2

/-- §3's `LoopFrame` is the QS SPECIALIZATION — it pins `depth = 0` and `nmr =
false`, which is what makes the QS fold heap-free. The recursion rule needs the
same slots at an arbitrary depth, so here they are with both carried. -/
def LoopFrameAt (e : REnv) (gamma best d : Int) (live nmr : Bool) : Prop :=
  Env.lookup e "gamma" = some (.int gamma) ∧
  Env.lookup e "best" = some (.int best) ∧
  Env.lookup e "live" = some (.bool live) ∧
  Env.lookup e "depth" = some (.int d) ∧
  Env.lookup e "nmr" = some (.bool nmr)

/-- And it IS the specialization, definitionally — so no §3 statement moves. -/
theorem loopFrame_eq (e : REnv) (gamma best : Int) (live : Bool) :
    LoopFrame e gamma best live = LoopFrameAt e gamma best 0 live false := rfl

/-- **THE FOLD'S INVARIANT, both halves** — the frame slots the rounds read and
the table the children write, in one proposition. This is §L13's "`TableOK`
threaded through the fold beside `LoopFrame`", spelled. -/
def FoldInv (V : RVal → Int → Int) (ts : Addr) (w : World) (e : REnv)
    (gamma best d : Int) (live nmr : Bool) : Prop :=
  LoopFrameAt e gamma best d live nmr ∧ (sfBracket V).TableAt w.heap ts

/-- **Binding the loop target preserves the frame half.** `for val, move in
moves():` rebinds `val` and `move`, and neither is a slot the invariant reads —
`bind_eq` is the transport, `lookup_bind_ne` the reason. -/
theorem LoopFrameAt.bindYield {e : REnv} {gamma best d : Int} {live nmr : Bool}
    (y : Yield) (h : LoopFrameAt e gamma best d live nmr) :
    LoopFrameAt (bindYield e y) gamma best d live nmr :=
  ⟨lookup_bind_ne y (by decide) (by decide) h.1,
   lookup_bind_ne y (by decide) (by decide) h.2.1,
   lookup_bind_ne y (by decide) (by decide) h.2.2.1,
   lookup_bind_ne y (by decide) (by decide) h.2.2.2.1,
   lookup_bind_ne y (by decide) (by decide) h.2.2.2.2⟩

/-- **A child call preserves the table half**, at every depth the child can key
under. Together with the previous theorem this is one round of the invariant,
with only the accumulator updates — interpreter work — left to pay. -/
theorem FoldInv.subtree {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d) {ts : Addr} {w w' : World}
    {e : REnv} {gamma best d : Int} {live nmr : Bool}
    (hw : (sfBracket V).SubtreeWrites ts d w.heap w'.heap)
    (h : FoldInv V ts w e gamma best d live nmr) :
    FoldInv V ts w' e gamma best d live nmr :=
  ⟨h.1, sf_subtree_tableAt hV hw h.2⟩

/-! ### The rule -/

/-- **THE RECURSION RULE, as a statement.** The depth-indexed proposition the
induction runs on, at the shipped module literal and the shipped receiver
shape.

Four conjuncts, and each earns its place:

* the run itself, in threshold form (`∀ F ≥ t`), as `QSStandPat` states it;
* `TableAt` OUT — the invariant is preserved, so a sibling call may assume it;
* **`SubtreeWrites` at every strictly greater depth** — what an ANCESTOR sees.
  A call at `d` stores under `(pos, d)` and its descendants under smaller
  depths still, so every ancestor probing at `e > d` is blind to the lot. This
  is the conjunct that makes the rule compose, and it is also the conjunct
  that needed `SubtreeWrites`'s allocation arm: a `bound()` call allocates on
  every visit (the `moves()` generator, the `sorted(…)` list), so with three
  arms this conjunct would have been unprovable and the whole rule vacuous;
* `Report` — the docstring's promise, at the value function the table's schema
  is instantiated on.

What it deliberately does NOT say: nothing about the CLOCK (the trace is an
input and the empty-trace frontier is `pins_search`'s business), nothing about
`root=True` (a driver probe skips the table in both directions), and nothing
about `live` or `tp_move` (the killer is a heuristic — the docstring promises
only that its moves are legal). -/
def BoundRefines (V : RVal → Int → Int) (d : Int) : Prop :=
  ∀ (w : World) (ci : ClassId) (sa ts tm hs : Addr) (n dl sf gamma : Int) (pos : RVal),
    Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf) →
    (sfBracket V).TableAt w.heap ts →
    -mateUpper < gamma → gamma ≤ mateUpper →
    ∃ (w' : World) (r : Int) (t : Nat),
      (∀ F ≥ t, callIn sunfish F w "Searcher.bound"
          #[.ref sa, pos, .int gamma, .int d] = .ok w' (.int r))
      ∧ (sfBracket V).TableAt w'.heap ts
      ∧ (∀ e : Int, d < e → (sfBracket V).SubtreeWrites ts e w.heap w'.heap)
      ∧ Report gamma r (V pos d)

/-- **The step the rule owes**, and the one thing in this file that is neither
proved nor provable yet: turning §3's `Round` list into a run of the shipped
loop is §L10's step-2 items 1–5, at one `py_simp` per statement.

Everything the step needs on the SPEC side is above it — `fold_report` for the
fold, `searchedMove_sound`/`searchedPass_sound` for the two recursive
branches, `sf_body_tableAt` for the invariant, `sf_rounds_probe` for the
probe, and `child_depth_lt` (§3) for the depth separation the third conjunct
of `BoundRefines` needs. What is missing is the bridge from `callIn` to those
objects, which is interpreter work and is priced. -/
def RecursionStep (V : RVal → Int → Int) : Prop :=
  ∀ d : Int, 1 ≤ d → BoundRefines V (d - 1) → BoundRefines V d

/-! ## §8 Non-vacuity, and the axioms

The gates are stated over a free world, a free window and a free board, so the
question is whether their hypotheses are ever satisfied and whether `fold` —
the spec-side walk — reproduces what the shipped program DOES. These `#guard`s
answer both by RUNNING `Searcher().bound` on the shipped opening board, on the
CURRENT engine. -/

private def bd_probe (pos : RVal) (gamma depth : Int) : Option (Int × Int) :=
  match searcherW with
  | some (w, a) =>
    (match callIn sunfish 1000000 w "Searcher.bound"
        #[.ref a, pos, .int gamma, .int depth] with
     | .ok w' (.int r) =>
       (match Heap.get? w'.heap a with
        | some (.instance _ attrs) =>
          (match Env.lookup attrs.toList "nodes" with
           | some (.int n) => some (r, n)
           | _ => Option.none)
        | _ => Option.none)
     | _ => Option.none)
  | Option.none => Option.none

/-! **The stand-pat cut is ONE node.** At `depth = 0` on the opening board
(`pos.score = 0`) with a window the stand-pat already meets, `bound` answers
`0` after a single entry: `moves()`'s first yield is `(None, None)`, the
consumer's branch 1 reads `score = pos.score`, and the fold cuts there — so
`pos.gen_moves()`, the sort and the killer test are never reached. -/
#guard bd_probe (posH 0) 0 0 == some (0, 1)
#guard bd_probe (posH 0) (-100) 0 == some (0, 1)
#guard bd_probe (posH 0) (-40) 0 == some (0, 1)

/-! **And depth 0 is NOT recursion-free in general** — the reason the rows
above carry a `gamma ≤ pos.score` hypothesis. Above the stand-pat the QS node
searches, and `max(depth, 0)` REFLOORS every child back to a QS node
(`qs_child_depth_eq`): 34 entries at `gamma = 40`, 4 at `gamma = 1`. The 34 is
one BELOW pass 7's 35 — #236's settled-cap break leaves the fold one yield
earlier on this board, which is the cheapest visible evidence that `Round`'s
second terminal is a real arm and not bookkeeping. -/
#guard bd_probe (posH 0) 40 0 == some (4, 34)
#guard bd_probe (posH 0) 1 0 == some (4, 4)

/-! Depth 1, for the same two windows — the row §L14 measured against CPython
on the same driver (`(0,1) ↦ 0`, `(40,1) ↦ 37`). -/
#guard bd_probe (posH 0) 0 1 == some (0, 2)
#guard bd_probe (posH 0) 40 1 == some (37, 34)

/-! **`fold` reproduces the stand-pat rows**, from the accumulator the shipped
`best, live = -MATE_UPPER, False` sets up, through `standPat` — branch 1. -/
#guard fold 0 (-mateUpper) false [standPat 0] == (0, false, Exit.cut)
#guard fold (-100) (-mateUpper) false [standPat 0] == (0, false, Exit.cut)

/-! **And the second terminal is reachable and distinguishable.** A settled cap
folds with `max` and leaves; nothing after it is read, and `live` does not
move — the three facts `sbBreak_lit` pins. -/
#guard fold 40 (-mateUpper) false [settledCap 7, standPat 100] == (7, false, Exit.settled)
#guard fold 40 (-mateUpper) true [settledCap (-mateUpper - 5)]
    == (-mateUpper, true, Exit.settled)
#guard fold 40 (-mateUpper) false [] == (-mateUpper, false, Exit.ran)

/-! The four scoring branches, as the consumer computes them: the QS cap has no
slope term, an intrinsic mate-band value is the exact token, and a searched
move is `min(cap, -child)` with the sentinel test for `live`. -/
#guard moveCap 0 12 30 == 42
#guard moveCap 2 12 30 == 12 + 30 + 140
#guard moveCap 4 12 30 == mateUpper
#guard intrinsicMate == Round.report mateUpper true
#guard searchedMove 500 (-120) == Round.report 120 true
#guard searchedMove 90 (-120) == Round.report 90 true
#guard searchedMove 500 mateUpper == Round.report (-mateUpper) false
#guard searchedPass 40 500 (-120) true == Round.report mateUpper true
#guard searchedPass 40 500 (-120) false == Round.report 120 false
#guard searchedPass 400 500 (-120) true == Round.report 120 false

/-! **What the depth-0 call leaves on the tables**, and it is what §5 claims:
`tp_move` stays EMPTY (the killer store is depth-gated off) and `tp_score`
gains exactly one entry, `(pos, 0) ↦ Entry(best, MATE_UPPER)` — the fail-high
half of the store, with the probe's own default upper. Byte-for-byte the same
answer as pass 7's, on a rewritten `bound()`: the table lines did not move. -/
#guard (match searcherW with
  | some (w, a) =>
    (match callIn sunfish 1000000 w "Searcher.bound"
        #[.ref a, posH 0, .int 0, .int 0] with
     | .ok w' _ =>
       (match Heap.get? w'.heap a with
        | some (.instance _ attrs) =>
          (match Env.lookup attrs.toList "tp_score", Env.lookup attrs.toList "tp_move" with
           | some (.ref sa), some (.ref ma) =>
             (match Heap.get? w'.heap sa, Heap.get? w'.heap ma with
              | some (.dict es _), some (.dict fs _) =>
                fs.size == 0 && es.size == 1
                  && (match es[0]! with
                      | (.tuple #[_, .int dk], .ntuple "Entry" _ #[.int lo, .int up]) =>
                        dk == 0 && lo == 0 && up == 69290
                      | _ => false)
              | _, _ => false)
           | _, _ => false)
        | _ => false)
     | _ => false)
  | Option.none => false)

/-! And the same entry, read through §6's decoder rather than by hand — the
one line that says the calculus and the interpreter agree about the shipped
`Entry`. -/
#guard entryBounds (entryOf 0 mateUpper) == some (0, mateUpper)
#guard pairKey (tpKey (posH 0) 0) == some (posH 0, 0)
#guard entryBounds entryDefault == some (-mateUpper, mateUpper)

/-! ### §7's contract, checked against the ENGINE

`Report` is a claim about a value function this file does not compute, so the
honest non-vacuity check is CONSISTENCY. Run the shipped `bound` at several
windows on one `(pos, depth)` and intersect what its answers claim: a
fail-high report is a lower bound on `s*`, a fail-low report an upper bound.
If the code meets its docstring the intersection is non-empty; if the windows
straddle the value it collapses to a single number, and that number IS `s*`
for that key — measured, not modelled. A row that cannot run answers with the
EMPTY interval, so a broken probe can never look consistent. -/
private def bd_claim (pos : RVal) (depth : Int) : List Int → Int × Int
  | [] => (-mateUpper, mateUpper)
  | g :: gs =>
      match bd_claim pos depth gs, bd_probe pos g depth with
      | (lo, up), some (r, _) => if g ≤ r then (max lo r, up) else (lo, min up r)
      | _, Option.none => (mateUpper, -mateUpper)

/-! At depth 0 the five windows already pinned above straddle the answer, and
they pin it exactly: the shipped QS value of the opening board is **4**. The
gamma-1 run fails high at 4 (so `4 ≤ s*`) and the gamma-40 run fails low at 4
(so `s* ≤ 4`) — two reports from two different searches, agreeing to the
integer. That is what a satisfied `Report` looks like on real numbers. -/
#guard bd_claim (posH 0) 0 [-100, -40, 0, 1, 40] == (4, 4)

/-! Depth 1, the same way, and it collapses too: **37**. Four windows, three
of them fail high (`0`, `20`, `37`) and one fails low (`40`), and the four
answers have exactly one common value. The two new probes cost 41 nodes each. -/
#guard bd_claim (posH 0) 1 [0, 20, 37, 40] == (37, 37)
#guard bd_probe (posH 0) 20 1 == some (37, 41)
#guard bd_probe (posH 0) 37 1 == some (37, 41)

/-! **The settled terminal, and why `settle_needs_futility` is about ORDER.**
The same two rounds, the settle first and the settle second: the first answers
10 (below the window, and not an upper bound on the value 50), the second
answers 50. The sorted stream is not a convenience — it is the entire content
of the futility bet, and the fold sees only the order. -/
#guard foldFrom 100 0 false [settledCap 10, standPat 50] == (10, false, Exit.settled)
#guard foldFrom 100 0 false [standPat 50, settledCap 10] == (50, false, Exit.settled)

/-! Both terminals carry a score, and it is the number the fold folds. -/
#guard (Round.report 7 true).score == 7
#guard (Round.settle 7).score == 7
#guard (searchedMove 500 (-120)).score == 120
#guard (searchedPass 40 500 (-120) true).score == mateUpper

/-! ### What the head gates stand on

`probe_misses` assumes the table is CLEARED and the key HASHABLE. Both are
facts about the real objects, not conveniences: a fresh `Searcher()` over the
real `initWorld` has an empty `tp_score`, and a real `Position` is hashable at
both the bare and the `(pos, depth)` spelling. `probe_repetition_skipped`
assumes only `depth = 0`, which `depth_refloors` produces from any `depth ≤ 0`. -/
#guard (match searcherW with
  | some (w, a) =>
    (match Heap.get? w.heap a with
     | some (.instance _ attrs) =>
       (match Env.lookup attrs.toList "tp_score" with
        | some (.ref ts) =>
          (match Heap.get? w.heap ts with
           | some (.dict es _) => es.size == 0
           | _ => false)
        | _ => false)
     | _ => false)
  | Option.none => false)
#guard (match searcherW with
  | some (w, a) =>
    (match Heap.get? w.heap a with
     | some (.instance _ attrs) =>
       (match Env.lookup attrs.toList "tp_move" with
        | some (.ref tm) =>
          (match Heap.get? w.heap tm with
           | some (.dict es _) => es.size == 0
           | _ => false)
        | _ => false)
     | _ => false)
  | Option.none => false)
#guard hashableKey (posH 0) == true
#guard hashableKey (tpKey (posH 0) 0) == true

/-! **`<genexpr@3>` is real**, and `calm_evals`' premise is about a function the
census actually carries — the lowered `any(c in pos.board for c in "RBNQ")`.
The cell directory key is the tier's own spelling, and `guard` is not a plain
capture: both pinned, so neither can drift silently. -/
#guard sunfish.functions.toList.any (fun f => f.name == "<genexpr@3>")
#guard isCellKey "<cell>guard" && !isCellKey "guard"
#guard cellName "<cell>guard" == "guard"
#guard guardCell == Obj.cell Option.none

/-! **The fold's one round, both sides.** The engine answers at ONE node, and
the spec-side fold reproduces it from the schedule `[standPat 0]` — the same
pair `qs_fold_agrees` relates symbolically. -/
#guard bd_probe (posH 0) 0 0 == some (0, 1)
#guard foldFrom 0 (-mateUpper) false [standPat 0] == (0, false, Exit.cut)
#guard yieldVal qsY == RVal.tuple #[RVal.none, RVal.none]

/-! **The tail's three dead-or-trivial statements, grounded.** `TABLE_SIZE`
resolves statically like `NULL_MARGIN` (so `evict_dead` says nothing about
`w.globals`), and one entry is nowhere near the cap. -/
#guard tableSize == 1000000
#guard decide ((1 : Int) ≤ tableSize)

/-! **What the store leaves, on the live engine.** The depth-0 call's own
`tp_score` entry after the stand-pat cut — `(pos, 0) |-> Entry(0, MATE_UPPER)` —
is what §5's `#guard` below already reads off a real run, and `sbStored` is that
object's shape. The decoder agrees with the interpreter on it. -/
#guard entryBounds (entryOf 0 mateUpper) == some (0, mateUpper)
#guard (dictStore [] (tpKey (posH 0) 0) (entryOf 0 mateUpper)).2 == true
#guard (max (-3 : Int) 0, max (0 : Int) 0, max (5 : Int) 0) == (0, 0, 5)

#print axioms bound_enters
#print axioms max_evals
#print axioms fold_standpat
#print axioms foldFrom_cons_settle
#print axioms bind_eq
#print axioms sbCallEnv
#print axioms child_depth_lt
#print axioms sf_probe
#print axioms sf_store
#print axioms sf_subtree_probe
#print axioms sf_subtree_tableAt
#print axioms report_iff_docstring
#print axioms Report.negate
#print axioms Report.cap
#print axioms Sound.max
#print axioms foldFrom_sound
#print axioms foldFrom_ge
#print axioms foldFrom_cut_ge
#print axioms foldFrom_ran_ge
#print axioms foldFrom_settled_ge
#print axioms fold_failHigh
#print axioms fold_failLow
#print axioms fold_report
#print axioms settle_needs_futility
#print axioms moveCap_mono
#print axioms moveCap_lt_of_tail
#print axioms searchedMove_sound
#print axioms searchedPass_sound
#print axioms report_sound
#print axioms cappedPass_sound
#print axioms settledCap_sound
#print axioms depth_refloors
#print axioms mate_check_passes
#print axioms probe_misses
#print axioms probe_lower_passes
#print axioms probe_upper_passes
#print axioms probe_repetition_skipped
#print axioms execStmt_of_singleton
#print axioms probe_block_runs
#print axioms execStmts_append
#print axioms execStmts_singleton
#print axioms head_runs
#print axioms execStmt_assign_name
#print axioms execStmt_of_stmtTriple
#print axioms calm_binds
#print axioms nmr_binds
#print axioms execStmts_singleton_flow
#print axioms mid_runs
#print axioms tail_runs
#print axioms sbArity
#print axioms callIn_of_body
#print axioms body_runs
#print axioms qs_stand_pat
#print axioms EvalsIn.closureGenCall_cells
#print axioms sbMovesCap_cells
#print axioms killer_misses
#print axioms guard_evals
#print axioms null_margin_adds
#print axioms boolChain_and_falsy
#print axioms boolChain_and3
#print axioms nmr_evals
#print axioms acc_inits
#print axioms boolChain_and2
#print axioms execStmt_nestedDef_cells
#print axioms sbDef_cells
#print axioms sbDef_snapshot
#print axioms moves_def_allocates
#print axioms abs_score_evals
#print axioms calm_evals
#print axioms execStmt_if_true
#print axioms execStmt_if_false
#print axioms score_guard_true
#print axioms qs_score
#print axioms qs_max
#print axioms kill_guard_false
#print axioms qs_cut
#print axioms qs_body
#print axioms qs_fold_breaks
#print axioms qs_fold_agrees
#print axioms sbCorr_noElse
#print axioms corr_dead
#print axioms ret_best
#print axioms evict_dead
#print axioms tsG
#print axioms store_runs
#print axioms sf_store_from_report
#print axioms absNotFun
#print axioms nmarG
#print axioms posCls_ntBase_isSome
#print axioms sf_body_tableAt
#print axioms sf_rounds_probe
#print axioms loopFrame_eq
#print axioms LoopFrameAt.bindYield
#print axioms FoldInv.subtree

end Examples.python.sunfish.bound_depth
