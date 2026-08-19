/-
**`Position.value` DECIDES, and it is heap-free** — inch R1 of the
`RecursionStep` campaign (docs/backlog.md §L25).

The move-ordering heuristic is what the shipped `moves()` sorts on, so the
depth-≥1 fold cannot run without it. What the campaign needs from it is
**not** its number: nothing downstream computes a move's value —
`moveCap`, the futility premise, `Report` and the fold are all stated over a
free `val` that is THREADED from the yield to the cap. What is needed is that
the method decides, without raising and without moving the world, on the
boards and moves `gen_moves` produces.

That is why this file has no reference function and no retyped table. §L25
records the re-sequencing: reference AGREEMENT is R1′ and is wanted only if a
later theorem must compute a value.

**Measured before anything here was written** (§L24's exit law):

* `callIn sunfish 8192 (initWorld sunfish) "Position.value" #[posH 0, Move(84, 64, "")]`
  answers `46` and leaves the heap at **66 → 66** — so a `= .ok w (.int v)`
  conclusion is honest, unlike `calmG`'s;
* the minimum fuel is **16**, so no gate below pins a numeral it has not
  measured;
* the `pst` global is a six-key dict at address 1 whose rows are all **120**
  wide.
-/
import Examples.python.sunfish.bound_depth

namespace Examples.python.sunfish.value_bound

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)
open Examples.python.sunfish.bound_depth (posCAux posCls_methods)

set_option maxRecDepth 100000

/-! ## §0 The method, projected

Eight statements, each READ OUT of the shipped module and pinned by `rfl`. -/

private def nowhere : Span := ⟨0, 0, 0, 0⟩

private def nth (n : Nat) (ss : List Stmt) : Stmt :=
  match ss.drop n with | s :: _ => s | [] => .pass nowhere

/-- `Position.value`'s own `FunctionDefn`, projected. -/
def vlF : FunctionDefn :=
  match findFunction sunfish "Position.value" with | some f => f | none => default

/-- Its body — eight statements. -/
def vlB : List Stmt := vlF.body.toList

/-- `i, j, prom = move`. -/
def vlUnpack : Stmt := nth 0 vlB
/-- `p, q = self.board[i], self.board[j]`. -/
def vlPQ : Stmt := nth 1 vlB
/-- `score = pst[p][j] - pst[p][i]` — the move's own table delta. -/
def vlScore : Stmt := nth 2 vlB
/-- `if q in "pnbrqk": score += pst[q.upper()][119 - j]` — the capture. -/
def vlCap : Stmt := nth 3 vlB
/-- `if abs(j - self.kp) < 2: score += pst["K"][119 - j]` — castling check
detection. -/
def vlKp : Stmt := nth 4 vlB
/-- `if p == "K" and abs(i - j) == 2:` — the castle itself, two statements. -/
def vlCastle : Stmt := nth 5 vlB
/-- `if p == "P":` — promotion and en passant, two statements. -/
def vlPawn : Stmt := nth 6 vlB
/-- `return score`. -/
def vlRet : Stmt := nth 7 vlB

theorem vlB_split :
    vlB = [vlUnpack, vlPQ, vlScore, vlCap, vlKp, vlCastle, vlPawn, vlRet] := rfl

/-- The method's own frame shape, pinned the way `sbF_lit` pins `bound`'s:
`argsOk`/`localsOk` TRUE and NOT a generator, which is what the ordinary call
bridge requires. -/
theorem vlF_lit : findFunction sunfish "Position.value" = some vlF ∧
    vlF.argsOk = true ∧ vlF.localsOk = true ∧ vlF.isGenerator = false ∧
    vlF.body.toList = vlB ∧ vlF.hasGlobal = false ∧ (2 : Nat) = vlF.params.size :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem vlUnpack_lit : ∃ p0 p1 p2 p3 p4 p5, vlUnpack =
    .assign #[.tuple #[.name "i" p0, .name "j" p1, .name "prom" p2] p3]
      (.name "move" p4) p5 := ⟨_, _, _, _, _, _, rfl⟩

theorem vlRet_lit : ∃ p0 p1, vlRet = .ret (some (.name "score" p0)) p1 := ⟨_, _, rfl⟩

/-! ## §1 What the method needs of `pst`, and nothing more

`pst[p][j]` cannot reduce at a free piece letter, so every gate below cases on
the letter — and what it needs at each is only that the row is THERE and is
120 integers wide. `PstRows` is that shape as a decidable predicate; the shipped
world satisfies it (`#guard` below), and no table value is spelled here. -/

/-- One row of `pst`: present, 120 wide, and all integers. -/
def pstRowOk (es : List (RVal × RVal)) (c : String) : Bool :=
  match dictFind es (.str c) with
  | some (.tuple xs) => xs.size == 120 && xs.all (fun v => match v with | .int _ => true | _ => false)
  | _ => false

/-- The six rows `Position.value` can index. `prom` is `""` on every
non-promotion move, and the promotion arm reads `pst[prom]` — so the
promotion letters are the same six and no seventh key is owed. -/
def pstKeys : List String := ["P", "N", "B", "R", "Q", "K"]

/-- The shape hypothesis every gate in this file takes, in the `hashableKey`
style: decidable, so a concrete world discharges it by `rfl`. -/
def PstRows (h : Heap) (pa : Addr) : Bool :=
  match Heap.get? h pa with
  | some (.dict es _) => pstKeys.all (pstRowOk es.toList)
  | _ => false

/-! ### Non-vacuity: the SHIPPED world satisfies it

Module init computes `pst` from the base tables and the padding; these guards
are what make every hypothesis below satisfiable rather than merely plausible,
and they read the live `initWorld` rather than any table written by hand. -/

#guard (match Env.lookup (initWorld sunfish).globals "pst" with
  | some (.ref pa) => PstRows (initWorld sunfish).heap pa
  | _ => false)

/-! **And `Position.value` itself, on the live engine.** The three CPython
answers `pins_init` pins, plus the two facts §L25's plan is priced on: the
method is HEAP-FREE, and sixteen fuel is enough. -/

private def mvOf (i j : Int) (prom : String) : RVal :=
  .ntuple "Move" #["i", "j", "prom"] #[.int i, .int j, .str prom]

/-! Heap-free: the world in is the world out — the premise shape `value_runs`
will carry, checked before it is written. -/
#guard (match callIn sunfish 16 (initWorld sunfish) "Position.value"
          #[posH 0, mvOf 84 64 ""] with
        | .ok w v => v == .int 46 && w.heap.size == (initWorld sunfish).heap.size
        | _ => false)

/-! And sixteen is the MINIMUM: fifteen times out. -/
#guard (match callIn sunfish 15 (initWorld sunfish) "Position.value"
          #[posH 0, mvOf 84 64 ""] with
        | .timeout => true | _ => false)

#guard (match callIn sunfish 64 (initWorld sunfish) "Position.value"
          #[posH 0, mvOf 85 65 ""] with
        | .ok _ v => v == .int 42 | _ => false)
#guard (match callIn sunfish 64 (initWorld sunfish) "Position.value"
          #[posH 0, mvOf 92 71 ""] with
        | .ok _ v => v == .int 5 | _ => false)

/-! ### The frame a call builds

`callIn`'s entry frame for the two-argument method, so the body gates start
where the interpreter starts. -/

def vlEnv (pv mv : RVal) : REnv := [("self", pv), ("move", mv)]

theorem vlArity : arityOk vlF.params 2 = true := rfl

theorem vlCallEnv (pv mv : RVal) : mkCallEnv vlF.params #[pv, mv] = vlEnv pv mv := rfl

/-! ## §2 The first statement, and the shape every later one takes

`i, j, prom = move` over a `Move` namedtuple VALUE: the unpack reads the
tuple's three fields into the frame and touches nothing else. Stated at a free
world, with the fuel a PARAMETER (§L24's law) rather than the numeral the
measurement happens to allow. -/

/-- The frame after the unpack. -/
def vlEnv1 (pv : RVal) (i j : Int) (prom : String) : REnv :=
  Env.set (Env.set (Env.set (vlEnv pv (mvOf i j prom)) "i" (.int i)) "j" (.int j))
    "prom" (.str prom)

/-- **GATE 1 — the move unpacks.** Heap-free, and the world rides through. -/
theorem value_unpacks (w : World) (pv : RVal) (i j : Int) (prom : String) (F : Nat) :
    execStmts sunfish (F + 4) ⟨w, vlEnv pv (mvOf i j prom)⟩ [vlUnpack]
      = .ok ⟨w, vlEnv1 pv i j prom⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, h⟩ := vlUnpack_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, vlEnv, vlEnv1, mvOf, Env.lookup]

/-- **GATE 8 — `return score`.** The tail, and the arm the boundary reads. -/
theorem value_returns (w : World) (e : REnv) (v : Int) (F : Nat)
    (hs : Env.lookup e "score" = some (.int v)) :
    execStmts sunfish (F + 4) ⟨w, e⟩ [vlRet] = .ok ⟨w, e⟩ (.ret (.int v)) := by
  obtain ⟨p0, p1, h⟩ := vlRet_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hs]

/-! ### The second statement — pinned, and its gate BLOCKED on one measured fact

`p, q = self.board[i], self.board[j]`, pinned below. Its gate is **not** here,
and the reason is worth the lines because it is §L20's `heapStore` finding one
tier down and it will govern every remaining gate in this file.

`evalExpr`'s subscript path **inlines past `indexVal` AND past `normIndex`**:
what `py_simp` leaves is the raw
`if (0 ≤ k) ∧ (k < b.length) then some k.toNat else none` with
`k = if i < 0 then i + b.length else i`, so neither
`indexVal (.str b) (.int i) = .ok (.str pc)` nor
`normIndex i b.length = some ni` can match it — measured, both forms tried, and
`-normIndex` in the simp set does not stop the unfolding.

**The shape the gate must take**, by the same law that fixed `store_runs`: state
the premise in the COMPUTED form (the two `if`s spelled out, or a local
`boardAt` definition that reduces to them), and conclude with the computed
character rather than a named one. That is one scratch cycle and it is the first
thing the next pass should do — the pin below is what it starts from. -/

theorem vlPQ_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12, vlPQ =
    .assign #[.tuple #[.name "p" p0, .name "q" p1] p2]
      (.tuple #[.subscript (.attribute (.name "self" p3) "board" p4) (.name "i" p5) p6,
                .subscript (.attribute (.name "self" p7) "board" p8) (.name "j" p9) p10]
        p11) p12 :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

#print axioms vlF_lit
#print axioms vlB_split
#print axioms vlUnpack_lit
#print axioms vlRet_lit
#print axioms vlCallEnv
#print axioms vlArity
#print axioms vlPQ_lit
#print axioms value_unpacks
#print axioms value_returns

/-! ## What R1 still owes, in order

`vlPQ`, `vlScore`, `vlCap`, `vlKp`, `vlCastle`, `vlPawn` — six gates. `vlPQ` is
pinned and blocked only on the computed-shape restatement above; the six-way
case split on the piece letter lives in `vlScore` and `vlCap`. The
premises they will need, read off the shipped body and to be measured before
each is written:

* `board[i]` and `board[j]` in range — `gen_moves` supplies both;
* `board[i] ∈ pstKeys` — else `pst[p]` is a genuine `KeyError`, and the
  reference declines rather than guesses;
* `q ∈ "pnbrqk" → q.upper() ∈ pstKeys` for the capture arm;
* `0 ≤ j ≤ 119` and `0 ≤ 119 - j ≤ 119` for every table index;
* `prom ∈ pstKeys` on the promotion arm only, which the `A8 ≤ j ≤ H8` guard
  is what restricts.

Then `value_runs` composes them at `callIn`, in the ∃-fuel form, with the
answer EXISTENTIAL — §L25's re-sequencing. -/

end Examples.python.sunfish.value_bound
