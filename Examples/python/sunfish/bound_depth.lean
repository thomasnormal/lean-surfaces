/-
**Depth-bounded equivalences for the RAW shipped `bound()`** — step 2 of the
model-removal roadmap (docs/backlog.md §L10).

`Examples/python/sf_order/bound.lean` (§L9) proved `bound_probe`'s own fold on
the `sf_order` fixture and recorded the consumption note: *the fold's shape IS
the recursion shape* — an induction hypothesis at depth `d-1` is consumed as a
`Hands` schedule at depth `d`. This file takes that shape to the **shipped**
`Searcher.bound`, on `Examples/python/sunfish/sunfish.py`, which is
BYTE-IDENTICAL to the engine's `sunfish.py` (§L9 measured it; `sf_order.py` is
not, which is why the arc moves here).

The object is the real thing: thirteen statements, a node counter and a wall
clock on the receiver, two transposition dicts and a history set behind
attributes, a five-capture nested generator that RE-ENTERS `bound` on every
searched move, a fold with a table write inside its cutoff, a terminality
correction and a table store.
-/
import Examples.python.sunfish.genmoves_drain

namespace Examples.python.sunfish.bound_depth

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)

set_option maxRecDepth 100000

/-! ## §0 The program, projected

`Searcher.bound`'s thirteen statements, each READ OUT of the shipped module
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

/-- Its body — thirteen statements. -/
def sbB : List Stmt := sbF.body.toList

/-- The docstring. -/
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
/-- `def moves(): …` — the nested generator, five captures. -/
def sbDef : Stmt := nth 6 sbB
/-- `best, live = -MATE_UPPER, False`. -/
def sbAcc : Stmt := nth 7 sbB
/-- `for move, score in moves():` — the fold. -/
def sbFor : Stmt := nth 8 sbB
/-- `if depth and not live and all(…): …` — the terminality correction. -/
def sbCorr : Stmt := nth 9 sbB
/-- `if not root: self.tp_score[pos, depth] = …` — the table store. -/
def sbStore : Stmt := nth 10 sbB
/-- `if len(self.tp_score) > TABLE_SIZE: del …` — the FIFO eviction. -/
def sbEvict : Stmt := nth 11 sbB
/-- `return best`. -/
def sbRet : Stmt := nth 12 sbB

theorem sbB_split : sbB =
    [sbDoc, sbNodes, sbClock, sbDepth, sbMate, sbProbe, sbDef, sbAcc, sbFor,
     sbCorr, sbStore, sbEvict, sbRet] := rfl

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
case-split on the two bound returns and on the repetition test. -/

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

/-! ### The accumulators, the fold, and the tail -/

theorem sbAcc_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7, sbAcc =
    .assign #[.tuple #[.name "best" p0, .name "live" p1] p2]
      (.tuple #[.unaryOp .usub (.name "MATE_UPPER" p3) p4, .constant (.bool false) p5] p6) p7 := ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- The fold's target, `(move, score)`. -/
def sbTarget : Expr :=
  match sbFor with | .forStmt t _ _ _ _ => t | _ => .constant .none nowhere
/-- `moves()` — the closure call. -/
def sbMovesCall : Expr :=
  match sbFor with | .forStmt _ it _ _ _ => it | _ => .constant .none nowhere
/-- The fold's body — three statements. -/
def sbBody : List Stmt :=
  match sbFor with | .forStmt _ _ b _ _ => b.toList | _ => []
/-- `best = max(best, score)`. -/
def sbMax : Stmt := nth 0 sbBody
/-- `live |= move is not None and score > -MATE_UPPER`. -/
def sbLive : Stmt := nth 1 sbBody
/-- `if best >= gamma: …; break` — the beta cutoff. -/
def sbCut : Stmt := nth 2 sbBody
/-- The cutoff's body: the killer store, then `break`. -/
def sbCutB : List Stmt :=
  match sbCut with | .ifStmt _ b _ _ => b.toList | _ => []
/-- `if move is not None and depth:` — the DEPTH-GATED killer store. -/
def sbKill : Stmt := nth 0 sbCutB
/-- The killer store's body: the write, then the eviction guard. -/
def sbKillB : List Stmt :=
  match sbKill with | .ifStmt _ b _ _ => b.toList | _ => []

theorem sbBody_split : sbBody = [sbMax, sbLive, sbCut] := rfl
theorem sbCutB_split : ∃ s, sbCutB = [sbKill, .brk s] := ⟨_, rfl⟩

theorem sbFor_lit : ∃ sp, sbFor = .forStmt sbTarget sbMovesCall sbBody.toArray #[] sp :=
  ⟨_, rfl⟩
theorem sbTarget_lit : ∃ p0 p1 p2, sbTarget =
    .tuple #[.name "move" p0, .name "score" p1] p2 := ⟨_, _, _, rfl⟩
/-- The killer store's GATE: `move is not None` **and `depth`** — at a QS node
(`depth == 0`) the second conjunct is falsy and the store never runs, which is
what makes the depth-0 fold heap-free. -/
theorem sbMovesCall_lit : ∃ p0 p1, sbMovesCall =
    .call (.name "moves" p0) #[] #[] Option.none p1 := ⟨_, _, rfl⟩

theorem sbMax_lit : ∃ p0 p1 p2 p3 p4 p5, sbMax =
    .assign #[.name "best" p0]
      (.call (.name "max" p1) #[.name "best" p2, .name "score" p3] #[] Option.none p4) p5 :=
  ⟨_, _, _, _, _, _, rfl⟩

theorem sbLive_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9, sbLive =
    .augAssign (.name "live" p0) .bitOr
      (.boolOp .and
        #[.compare (.name "move" p1) #[.isNot] #[.constant Const.none p2] p3,
          .compare (.name "score" p4) #[.gt]
            #[.unaryOp .usub (.name "MATE_UPPER" p5) p6] p7] p8) p9 :=
  ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩

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
`TABLE_SIZE = 10**6` buys. -/
theorem sbEvict_lit : ∃ (b : Array Stmt) (p0 p1 p2 p3 p4 p5 p6 : Span), sbEvict =
    .ifStmt (.compare (.call (.name "len" p0)
        #[.attribute (.name "self" p1) "tp_score" p2] #[] Option.none p3) #[.gt]
        #[.name "TABLE_SIZE" p4] p5) b #[] p6 :=
  ⟨_, _, _, _, _, _, _, _, rfl⟩

theorem sbRet_lit : ∃ p0 p1, sbRet = .ret (some (.name "best" p0)) p1 := ⟨_, _, rfl⟩

/-- The five facts `callIn`'s function arm tests, and the two shapes the body
gates are stated in: the parameter list is `self, pos, gamma, depth, root` and
`root` carries its literal default `False`. -/
theorem sbF_lit : findFunction sunfish "Searcher.bound" = some sbF ∧
    sbF.argsOk = true ∧ sbF.localsOk = true ∧ sbF.isGenerator = false ∧
    sbF.body.toList = sbB ∧ (5 : Nat) = sbF.params.size :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-! The three values are the shipped file's own. They are checked by RUNNING
module init (`#guard`, the compiled evaluator) rather than pinned by a kernel
`rfl`: `initWorld sunfish` executes the 1MB top level, and reducing that in
the kernel is measured at over 4M heartbeats and an out-of-memory kill
(docs/backlog.md §L10 §the price). -/
#guard Env.lookup (initWorld sunfish).globals "MATE_LOWER" == some (.int mateLower)
#guard Env.lookup (initWorld sunfish).globals "MATE_UPPER" == some (.int mateUpper)
#guard Env.lookup (initWorld sunfish).globals "TABLE_SIZE" == some (.int tableSize)

/-! ### The pinned residues

§L8 finding 2: pin the residue the unfold set leaves rather than let it
unfold. `max` and `Entry` are the two names the head and the fold resolve;
each resolution walks the constant fold, the function table, the class table
and the namedtuple table, and each of those steps is an `rfl` here. -/

theorem maxG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "max"
    = Option.none := rfl
theorem maxF : findFunction sunfish "max" = Option.none := rfl
theorem maxNotFun : ¬ ∃ x, x ∈ sunfish.functions ∧ x.name = "max" := by
  simpa [findFunction] using maxF
theorem maxCls : findClassAux sunfish.classes.toList "max" 0 = Option.none := rfl
theorem maxNT : findNamedTupleAux sunfish.namedtuples.toList "max" = Option.none := rfl

theorem mlG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst
    "MATE_LOWER" = some Option.none := rfl
theorem muG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst
    "MATE_UPPER" = some Option.none := rfl

theorem entryG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst
    "Entry" = Option.none := rfl
theorem entryF : findFunction sunfish "Entry" = Option.none := rfl
theorem entryNotFun : ¬ ∃ x, x ∈ sunfish.functions ∧ x.name = "Entry" := by
  simpa [findFunction] using entryF
theorem entryClsAux : findClassAux sunfish.classes.toList "Entry" 0 = Option.none := rfl
/-- `Entry` IS a namedtuple: `Entry = namedtuple("Entry", "lower upper")`, and
the table answers with the two fields the table probe reads. -/
theorem entryNTAux : ∃ sp, findNamedTupleAux sunfish.namedtuples.toList "Entry"
    = some ⟨"Entry", "Entry", #["lower", "upper"], sp⟩ := ⟨_, rfl⟩

/-! ## §2 The receiver, and the frame

`Searcher.__init__` binds five attributes in this order; the two
transposition tables and the history set are heap objects behind them, so a
gate that says what `bound` does to the table says it about `ts`/`tm`, never
about the instance. -/

/-- The receiver as the gates see it. -/
def searcherObj (ci : ClassId) (ts tm hs : Addr) (nodes dl : Int) : Obj :=
  .instance ci #[("tp_score", .ref ts), ("tp_move", .ref tm), ("history", .ref hs),
                 ("nodes", .int nodes), ("deadline", .int dl)]

/-- `Searcher.bound`'s entry frame: its five parameters, `root` filled from
its literal default. -/
def sbEnv0 (slf pv : RVal) (gamma depth : Int) : REnv :=
  [("self", slf), ("pos", pv), ("gamma", .int gamma), ("depth", .int depth),
   ("root", .bool false)]

/-- The entry frame IS what `callIn` builds for a four-argument call: the
default-filled `root` is the shipped signature's own, not a choice here. -/
theorem sbCallEnv (slf pv : RVal) (gamma depth : Int) :
    mkCallEnv sbF.params #[slf, pv, .int gamma, .int depth] = sbEnv0 slf pv gamma depth := rfl

/-! ## §3 The vocabulary of a QS fold

What `moves()` hands over, what the fold does with it, and the walk that is
the SPEC side of every depth-bounded gate below. -/

/-- One yield of the shipped `moves()`: `yield <move>, <score>`. The move is
`None` for a VIRTUAL yield — the null-move pass, the QS stand-pat, a futility
estimate — and a `Move` for a searched one, which is exactly the distinction
`live` tracks. -/
structure Yield where
  /-- The move, or `None` for a virtual yield. -/
  move : RVal
  /-- The score the yield carries. -/
  score : Int

/-- The yield as the interpreter's value: the shipped tuple `(move, score)`. -/
def yieldVal (y : Yield) : RVal := .tuple #[y.move, .int y.score]

/-- `live |= move is not None and score > -MATE_UPPER`, spec-side. -/
def isLive (y : Yield) : Bool := (!y.move.isNone) && decide (-mateUpper < y.score)

/-- **The walk the shipped fold performs.** Raise `best` to the running
maximum, or `live` if the yield is real evidence, and STOP at the first yield
that lifts `best` to `gamma`: `.1` is the `best` it ends with, `.2.1` the
`live` it ends with, `.2.2` whether it CUT rather than running `moves()` out.

This is the shipped loop and nothing else: the killer store inside the cutoff
is depth-gated (`sbKill_lit`) and does not run at a QS node, and the
correction and the table store are the tail's business, not the fold's. -/
def fold (gamma : Int) : Int → Bool → List Yield → Int × Bool × Bool
  | best, live, [] => (best, live, false)
  | best, live, y :: ys =>
      if gamma ≤ max best y.score then (max best y.score, live || isLive y, true)
      else fold gamma (max best y.score) (live || isLive y) ys

/-- The same walk from a running state — the loop invariant's handle on "what
the rounds still to come will answer". -/
def foldFrom (gamma best : Int) (live : Bool) (ys : List Yield) : Int × Bool × Bool :=
  fold gamma best live ys

theorem foldFrom_nil (gamma best : Int) (live : Bool) :
    foldFrom gamma best live [] = (best, live, false) := rfl

theorem foldFrom_cons_next (gamma best : Int) (live : Bool) (y : Yield) (ys : List Yield)
    (h : ¬ gamma ≤ max best y.score) :
    foldFrom gamma best live (y :: ys)
      = foldFrom gamma (max best y.score) (live || isLive y) ys := by
  simp [foldFrom, fold, h]

theorem foldFrom_cons_cut (gamma best : Int) (live : Bool) (y : Yield) (ys : List Yield)
    (h : gamma ≤ max best y.score) :
    foldFrom gamma best live (y :: ys) = (max best y.score, live || isLive y, true) := by
  simp [foldFrom, fold, h]

/-- **The stand-pat cut, spec-side.** A schedule whose FIRST yield already
meets the window ends there, whatever follows — which is the depth-0 arm the
model's `qsStrat` writes as `if gamma ≤ eval p then eval p`
(formal/Sunfish/Stalemate.lean). The fold never looks past it, so no
statement about the rest of `moves()` is needed to know the answer. -/
theorem fold_standpat (gamma sc : Int) (ys : List Yield) (h : gamma ≤ sc) :
    foldFrom gamma (-mateUpper) false (⟨.none, sc⟩ :: ys)
      = (max (-mateUpper) sc, false, true) := by
  refine foldFrom_cons_cut gamma (-mateUpper) false ⟨.none, sc⟩ ys ?_
  simp only []
  omega

/-- **The object's yield schedule**, world-threaded: stepping the generator at
`a` from world `w` hands over exactly `ys`, one `IterSteps` at a time, and
lands at `w'`.

The worlds are the whole point at depth ≥ 1. A searched yield's score is
`-self.bound(pos.move(move), 1 - gamma, depth - 1)`, so producing it RUNS a
child call: it bumps `self.nodes`, it may write `tp_move`, and it stores into
`tp_score`. `IterSteps` carries that world change, which is exactly why an
induction hypothesis at depth `d-1` can be CONSUMED as one `cons` of this
schedule at depth `d` (docs/backlog.md §L9 finding 1, §L10 §the template). -/
inductive Hands (m : Module) (a : Addr) : World → List Yield → World → Prop
  /-- The empty schedule: no step taken, the world is where it was. -/
  | nil {w : World} : Hands m a w [] w
  /-- One yield, then the rest. -/
  | cons {w w₁ w₂ : World} {y : Yield} {ys : List Yield} :
      IterSteps m w a (some (yieldVal y)) w₁ → Hands m a w₁ ys w₂ →
      Hands m a w (y :: ys) w₂

/-- The four frame slots the QS fold reads, as LOOKUPS, so every gate is blind
to the rest of the frame. `depth` is one of them: the killer store inside the
cutoff is gated on it, and pinning it to `0` is what makes the QS fold
heap-free. -/
def LoopFrame (e : REnv) (gamma best : Int) (live : Bool) : Prop :=
  Env.lookup e "gamma" = some (.int gamma) ∧
  Env.lookup e "best" = some (.int best) ∧
  Env.lookup e "live" = some (.bool live) ∧
  Env.lookup e "depth" = some (.int 0)

/-- The frame with the loop target bound to a yield. -/
def bindYield (e : REnv) (y : Yield) : REnv :=
  Env.set (Env.set e "move" y.move) "score" (.int y.score)

/-- Binding `(move, score)` — an `rfl` on the projected target. -/
theorem bind_eq (h : Heap) (e : REnv) (y : Yield) :
    assignToH h e sbTarget (yieldVal y) = .ok (bindYield e y) := rfl

theorem lookup_bind_move (e : REnv) (y : Yield) :
    Env.lookup (bindYield e y) "move" = some y.move := by
  simp [bindYield, Env.lookup_set_self, Env.lookup_set_ne]
theorem lookup_bind_score (e : REnv) (y : Yield) :
    Env.lookup (bindYield e y) "score" = some (.int y.score) := by
  simp [bindYield, Env.lookup_set_self]
theorem lookup_bind_ne {e : REnv} {x : String} {v : RVal} (y : Yield)
    (hm : x ≠ "move") (hs : x ≠ "score") (h : Env.lookup e x = some v) :
    Env.lookup (bindYield e y) x = some v := by
  simp [bindYield, Env.lookup_set_ne, hm, hs, h]

/-! ## §4 Two gates on the shipped body

`bound_enters` is the head's first three statements; `max_evals` is the
fold's first. Both are stated over a FREE world and a free frame, and both
are what the depth-bounded gates compose. -/

/-- **GATE 1 — entering `bound` counts a node and does NOT read the clock.**

`self.nodes += 1` is an attribute store through the receiver, and the very
next statement is `if self.nodes % 2048 == 0 and time.time() > self.deadline:
raise Stop`. `time.time()` sits behind the `and`, so a node count that is not
a multiple of 2048 never consults the world's clock trace — the trace is an
INPUT (docs/memory-model.md §the trace clock) and an empty one refuses
loudly, so this is the statement that says the refusal cannot happen below
the frontier. The frame is untouched and the only heap change is the counter. -/
theorem bound_enters (w : World) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl gamma d : Int) (pv : RVal) (h' : Heap)
    (hself : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl))
    (hupd : Heap.update w.heap sa (searcherObj ci ts tm hs (n + 1) dl) = some h')
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
* `gamma ≤ pos.score` — the stand-pat cut.

`bound_enters`, `max_evals`, `fold_standpat`, `bind_eq` and the §0 pins are the
pieces; what is NOT yet paid is the table probe's `.get` miss, the nested
`def`'s five-capture closure, the generator's first `IterSteps`, and the table
store. Their price is measured in docs/backlog.md §L10. -/
def QSStandPat : Prop :=
  ∀ (w : World) (ci : ClassId) (sa ts tm hs : Addr) (n dl gamma sc : Int)
    (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (sv sv' : Nat),
    Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl) →
    Heap.get? w.heap ts = some (.dict #[] sv) →
    Heap.get? w.heap tm = some (.dict #[] sv') →
    Heap.get? w.heap hs = some (.pyset #[]) →
    Env.lookup w.globals "MATE_LOWER" = some (.int mateLower) →
    Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper) →
    ¬ ((n + 1).fmod 2048 = 0) →
    -mateLower < sc → -mateUpper < gamma → gamma ≤ mateUpper → gamma ≤ sc →
    ∃ w' t, ∀ F ≥ t, callIn sunfish F w "Searcher.bound"
      #[.ref sa, posOf b sc wc0 wc1 bc0 bc1 ep kp, .int gamma, .int 0]
        = .ok w' (.int sc)

/-! ### The template depth 1 and depth 2 instantiate

`Hands` is world-threaded, and that is the whole induction. At depth `d` the
fold consumes a schedule `ys : List Yield`; a SEARCHED entry of that schedule
carries `score = -self.bound(pos.move(move), 1 - gamma, d - 1)`, so producing
it runs a child call — which bumps `self.nodes`, may write `tp_move`, and
stores into `tp_score`. `Hands.cons` is exactly the shape that carries a
child's world change: its `IterSteps m w a (some (yieldVal y)) w₁` says
"resuming the generator at `w` hands over `y` and lands at `w₁`", and `w₁` is
`w` plus the child's writes.

So the induction hypothesis at depth `d - 1` — a statement of the form
`callIn … (d-1) … = .ok w₁ (.int r)` — is CONSUMED as one `Hands.cons` at
depth `d`, with `y.score = -r`. Nothing else changes: the fold, the algebra
lemmas (`foldFrom_nil`/`_cons_next`/`_cons_cut`), the boundary bridge and the
`bind_eq` transport are depth-independent and are reused verbatim.

Two things DO change with depth and must be discharged per level:
1. the killer store inside the cutoff is gated on `depth` (`sbKill_lit`), so at
   `d ≥ 1` a real cutting move WRITES `tp_move[pos]` and the fold is no longer
   heap-free;
2. the terminality correction is gated on `depth` too (`sbCorr_lit`), so at
   `d ≥ 1` the `all(… for m in pos.gen_moves())` scan runs whenever `live` is
   false — which is where `gen_moves_drains_ref` (Examples/python/sunfish/
   genmoves_drain.lean) enters this arc, and it is already at THIS module
   literal. -/

/-! ## §6 Non-vacuity, and the axioms

The gates are stated over a free world, a free window and a free board, so the
question is whether their hypotheses are ever satisfied and whether `fold` —
the spec-side walk — reproduces what the shipped program DOES. These `#guard`s
answer both by RUNNING `Searcher().bound` on the shipped opening board. -/

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
`0` after a single entry: the generator's first yield is `(None, pos.score)`
and the fold cuts there, so `pos.gen_moves()` is never reached. -/
#guard bd_probe (posH 0) 0 0 == some (0, 1)
#guard bd_probe (posH 0) (-100) 0 == some (0, 1)

/-! **And depth 0 is NOT recursion-free in general** — the reason the two rows
above carry a `gamma ≤ pos.score` hypothesis. Above the stand-pat the QS node
searches, and `max(depth, 0)` makes every child a QS node again: 35 entries at
`gamma = 40`, 4 at `gamma = 1`. -/
#guard bd_probe (posH 0) 40 0 == some (4, 35)
#guard bd_probe (posH 0) 1 0 == some (4, 4)

/-! **`fold` reproduces the stand-pat rows**, from the accumulator the shipped
`best, live = -MATE_UPPER, False` sets up. -/
#guard fold 0 (-mateUpper) false [⟨.none, 0⟩] == (0, false, true)
#guard fold (-100) (-mateUpper) false [⟨.none, 0⟩] == (0, false, true)

/-! **What the depth-0 call leaves on the tables**, and it is what §5 claims:
`tp_move` stays EMPTY (the killer store is depth-gated off) and `tp_score`
gains exactly one entry, `(pos, 0) ↦ Entry(best, MATE_UPPER)` — the fail-high
half of the store, with the probe's own default upper. -/
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

#print axioms bound_enters
#print axioms max_evals
#print axioms fold_standpat
#print axioms bind_eq
#print axioms sbCallEnv

end Examples.python.sunfish.bound_depth


