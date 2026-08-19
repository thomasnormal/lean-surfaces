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
open Examples.python.sunfish.genmoves_theorem (posOf genMovesOf)
open Examples.python.sunfish.bound_depth (posCAux posCls_methods absG absNotFun absCls absNT
  execStmt_if_true execStmt_if_false execStmts_singleton compare_one
  execStmts_append execStmts_singleton_flow)

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

/-! ### The second statement — the two board reads, in the COMPUTED shape

`p, q = self.board[i], self.board[j]`, and the shape of its gate is the whole
lesson of this file. `evalExpr`'s subscript path **inlines past `indexVal` AND
past `normIndex`**: what `py_simp` leaves is the raw
`if (0 ≤ k) ∧ (k < b.length) then some k.toNat else none` with
`k = if i < 0 then i + b.length else i`. A premise stated at either helper
cannot match it, and `-normIndex` in the simp set does not stop the unfolding —
both measured. So the gate does what `store_runs` did with `heapStore` (§L20):
it takes the premise the CONDITIONALS need (the index is in range, which is what
`gen_moves` supplies for every square it yields) and CONCLUDES with the computed
character.

`boardAt` is that character, and nothing about it is a choice: it is the term
the interpreter leaves, written down. **This governs gates 3–7 as well** — every
one of them indexes something. -/

theorem vlPQ_lit : ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12, vlPQ =
    .assign #[.tuple #[.name "p" p0, .name "q" p1] p2]
      (.tuple #[.subscript (.attribute (.name "self" p3) "board" p4) (.name "i" p5) p6,
                .subscript (.attribute (.name "self" p7) "board" p8) (.name "j" p9) p10]
        p11) p12 :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- `board[i]` at an in-range index, as the interpreter computes it. -/
def boardAt (b : String) (i : Int) : String :=
  String.singleton (b.toList[i.toNat]?.getD ' ')

/-- The frame after the two board reads. -/
def vlEnv2 (pv : RVal) (i j : Int) (prom pc qc : String) : REnv :=
  Env.set (Env.set (vlEnv1 pv i j prom) "p" (.str pc)) "q" (.str qc)

/-- **GATE 2 — the two board reads.** Heap-free; `board` is a FIELD and not a
method (`posCls_methods` decides the namedtuple-subclass fork, §L17's second
residue); and both indices are in range, which is `gen_moves`' own guarantee. -/
theorem value_reads_pq (w : World) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp i j : Int) (prom : String) (F : Nat)
    (hi : 0 ≤ i) (hi' : i < (b.length : Int))
    (hj : 0 ≤ j) (hj' : j < (b.length : Int)) :
    execStmts sunfish (F + 8)
        ⟨w, vlEnv1 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom⟩ [vlPQ]
      = .ok ⟨w, vlEnv2 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
                (boardAt b i) (boardAt b j)⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, h⟩ := vlPQ_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, vlEnv1, vlEnv2, vlEnv, mvOf, Env.lookup,
    posOf, posCAux, posCls_methods, boardAt, normIndex, if_neg (show ¬ i < 0 by omega),
    if_neg (show ¬ j < 0 by omega), if_pos (show (0 ≤ i ∧ i < (b.length : Int)) from ⟨hi, hi'⟩),
    if_pos (show (0 ≤ j ∧ j < (b.length : Int)) from ⟨hj, hj'⟩)]

/-! ### The third statement — `score = pst[p][j] - pst[p][i]`

The move's own table delta, and the first statement that reads a GLOBAL. `pst`
is dirtied by the module's own `for k, table in pst.items()` loop, so the static
fold declines and the LIVE view decides — the gate therefore takes the global as
a world hypothesis, exactly as `gen_moves_drains_ref` takes `directions`.

**The row is a premise, not a table.** `pst[p]` cannot reduce at a free piece
letter, so the caller supplies the row it found; what the gate then needs of it
is only that the two squares hold integers. That is what makes this gate say
`zj - zi` — an AGREEMENT, at this statement, with no 120-wide constant written
down anywhere. -/

theorem vlScore_lit : ∃ a b c d e f g h i k l m n, vlScore =
    .assign #[.name "score" a]
      (.binOp (.subscript (.subscript (.name "pst" b) (.name "p" c) d) (.name "j" e) f)
        .sub
        (.subscript (.subscript (.name "pst" g) (.name "p" h) i) (.name "i" k) l) m) n :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- `pst` is BOUND but DIRTY in the static fold — the module's own
`for k, table in pst.items()` loop writes it — so every gate below reads it
from the world's globals and none of them says anything about the fold. -/
theorem pstG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "pst"
    = some Option.none := rfl

/-- **GATE 3 — `score = pst[p][j] - pst[p][i]`.** The row arrives as a premise
and the answer is stated in the row's own entries, so the gate AGREES with the
table without naming one. -/
theorem value_scores (w : World) (e : REnv) (pa : Addr) (pc : String)
    (es : Array (RVal × RVal)) (sv : Nat) (xs : Array RVal) (i j zi zj : Int) (F : Nat)
    (hnp : Env.lookup e "pst" = Option.none)
    (hp : Env.lookup e "p" = some (.str pc))
    (hei : Env.lookup e "i" = some (.int i))
    (hej : Env.lookup e "j" = some (.int j))
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es sv))
    (hrow : dictFind es.toList (.str pc) = some (.tuple xs))
    (hsz : xs.size = 120)
    (hi : 0 ≤ i) (hi' : i < 120) (hj : 0 ≤ j) (hj' : j < 120)
    (hxi : xs[i.toNat]?.getD .none = .int zi)
    (hxj : xs[j.toNat]?.getD .none = .int zj) :
    execStmts sunfish (F + 10) ⟨w, e⟩ [vlScore]
      = .ok ⟨w, Env.set e "score" (.int (zj - zi))⟩ .next := by
  obtain ⟨a, b, c, d, e', f, g, h, i', k, l, m, n, hlit⟩ := vlScore_lit
  simp only [Heap.get?] at hd
  rw [hlit]
  py_simp [-globalsFold, -globalsStep, hnp, hp, hei, hej, hg, hd, hrow, pstG,
    normIndex, hsz, hxi, hxj,
    if_neg (show ¬ i < 0 by omega), if_neg (show ¬ j < 0 by omega),
    if_pos (show (0 ≤ i ∧ i < (120 : Int)) from ⟨hi, hi'⟩),
    if_pos (show (0 ≤ j ∧ j < (120 : Int)) from ⟨hj, hj'⟩)]

theorem vlCap_lit : ∃ a b c d e f g h i k l m n o p, vlCap =
    .ifStmt (.compare (.name "q" a) #[.inOp] #[.constant (.str "pnbrqk") b] c)
      #[.augAssign (.name "score" d) .add
          (.subscript
            (.subscript (.name "pst" e)
              (.call (.attribute (.name "q" f) "upper" g) #[] #[] Option.none h) i)
            (.binOp (.constant (.int 119) k) .sub (.name "j" l) m) n) o]
      #[] p :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- **GATE 4a — a NON-capture skips the arm.** The destination square holds no
black piece, so `pst[q.upper()]` is never reached — which matters, because for a
`q` outside `"pnbrqk"` there is no row to reach: `pst['.']` is a genuine
`KeyError`. That is why this statement gets TWO gates and not one existential:
a single gate carrying the row premise unconditionally would be UNSATISFIABLE on
every quiet move, which is §L24's trap exactly. -/
theorem value_cap_skips (w : World) (e : REnv) (qc : String) (F : Nat)
    (hq : Env.lookup e "q" = some (.str qc))
    (hno : strContains "pnbrqk" qc = false) :
    execStmts sunfish (F + 10) ⟨w, e⟩ [vlCap] = .ok ⟨w, e⟩ .next := by
  obtain ⟨a, b, c, d, e', f, g, h, i, k, l, m, n, o, p, hlit⟩ := vlCap_lit
  rw [hlit]
  py_simp [-globalsFold, -globalsStep, hq, hno]

/-- **GATE 4b — a CAPTURE adds the taken piece's table value.** `q.upper()` is
the row key, and the answer is again in the row's own entries. -/
theorem value_cap_adds (w : World) (e : REnv) (pa : Addr) (qc uc : String)
    (es : Array (RVal × RVal)) (svv : Nat) (xs : Array RVal) (j s z : Int) (F : Nat)
    (hq : Env.lookup e "q" = some (.str qc))
    (hyes : strContains "pnbrqk" qc = true)
    (hup : strUpper qc = .ok (.str uc))
    (hnp : Env.lookup e "pst" = Option.none)
    (hej : Env.lookup e "j" = some (.int j))
    (hs : Env.lookup e "score" = some (.int s))
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hrow : dictFind es.toList (.str uc) = some (.tuple xs))
    (hsz : xs.size = 120)
    (hlo : 0 ≤ 119 - j) (hhi : 119 - j < 120)
    (hx : xs[(119 - j).toNat]?.getD .none = .int z) :
    execStmts sunfish (F + 14) ⟨w, e⟩ [vlCap]
      = .ok ⟨w, Env.set e "score" (.int (s + z))⟩ .next := by
  obtain ⟨a, b, c, d, e', f, g, h, i, k, l, m, n, o, p, hlit⟩ := vlCap_lit
  simp only [Heap.get?] at hd
  rw [hlit]
  py_simp [-globalsFold, -globalsStep, hq, hyes, hup, hnp, hej, hs, hg, hd, hrow, pstG,
    normIndex, hsz, hx,
    if_neg (show ¬ (119 - j) < 0 by omega),
    if_pos (show (j ≤ 119 ∧ 119 - j < (120 : Int)) from ⟨by omega, hhi⟩)]

theorem vlKp_lit : ∃ a b c d e f g h i k l m n o p q r t, vlKp =
    .ifStmt (.compare
        (.call (.name "abs" a)
          #[.binOp (.name "j" b) .sub (.attribute (.name "self" c) "kp" d) e] #[] Option.none f)
        #[.lt] #[.constant (.int 2) g] h)
      #[.augAssign (.name "score" i) .add
          (.subscript (.subscript (.name "pst" k) (.constant (.str "K") l) m)
            (.binOp (.constant (.int 119) n) .sub (.name "j" o) p) q) r]
      #[] t :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-! ### The fourth statement — the castling-check detection

`if abs(j - self.kp) < 2: score += pst["K"][119 - j]`. Two arms again, and here
the row key is the LITERAL `"K"`, so the row premise would be safe in both — the
split is kept because the score changes in only one, and because a caller that
knows which arm it is in should not have to carry a table row it never reads.

`abs` leaves `if j - kp < 0 then -(j - kp) else j - kp`, so the premises below
are ordinary arithmetic and the proof `split`s the interpreter's own `if`. -/

/-- **GATE 5a — the destination is far from the king square**, and the arm is
skipped. -/
theorem value_kp_skips (w : World) (e : REnv) (b : String) (scv : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp j : Int) (F : Nat)
    (hself : Env.lookup e "self" = some (posOf b scv wc0 wc1 bc0 bc1 ep kp))
    (hej : Env.lookup e "j" = some (.int j))
    (hna : Env.lookup e "abs" = Option.none)
    (hfar : 2 ≤ j - kp ∨ j - kp ≤ -2) :
    execStmts sunfish (F + 14) ⟨w, e⟩ [vlKp] = .ok ⟨w, e⟩ .next := by
  obtain ⟨a, b', c, d, e', f, g, h, i, k, l, m, n, o, p, q, r, t, hlit⟩ := vlKp_lit
  have hif : ¬ ((if j - kp < 0 then -(j - kp) else j - kp) < 2) := by
    split <;> omega
  rw [hlit]
  py_simp [-globalsFold, -globalsStep, hself, hej, hna, absG, absNotFun, absCls, absNT,
    posOf, posCAux, posCls_methods, if_neg hif]

/-- **GATE 5b — the destination is beside the king square**, and the king
table's value at the mirrored square is added. -/
theorem value_kp_adds (w : World) (e : REnv) (pa : Addr) (b : String) (scv : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp j s z : Int)
    (es : Array (RVal × RVal)) (svv : Nat) (xs : Array RVal) (F : Nat)
    (hself : Env.lookup e "self" = some (posOf b scv wc0 wc1 bc0 bc1 ep kp))
    (hej : Env.lookup e "j" = some (.int j))
    (hna : Env.lookup e "abs" = Option.none)
    (hnp : Env.lookup e "pst" = Option.none)
    (hs : Env.lookup e "score" = some (.int s))
    (hnear : -2 < j - kp ∧ j - kp < 2)
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hrow : dictFind es.toList (.str "K") = some (.tuple xs))
    (hsz : xs.size = 120)
    (hlo : j ≤ 119) (hhi : 119 - j < 120)
    (hx : xs[(119 - j).toNat]?.getD .none = .int z) :
    execStmts sunfish (F + 16) ⟨w, e⟩ [vlKp]
      = .ok ⟨w, Env.set e "score" (.int (s + z))⟩ .next := by
  obtain ⟨a, b', c, d, e', f, g, h, i, k, l, m, n, o, p, q, r, t, hlit⟩ := vlKp_lit
  have hif : (if j - kp < 0 then -(j - kp) else j - kp) < 2 := by
    split <;> omega
  simp only [Heap.get?] at hd
  rw [hlit]
  py_simp [-globalsFold, -globalsStep, hself, hej, hna, hnp, hs, hg, hd, hrow, pstG,
    absG, absNotFun, absCls, absNT, posOf, posCAux, posCls_methods,
    normIndex, hsz, hx, if_pos hif,
    if_neg (show ¬ (119 - j) < 0 by omega),
    if_pos (show (j ≤ 119 ∧ 119 - j < (120 : Int)) from ⟨hlo, hhi⟩)]

/-! ### The fifth statement — the castle itself

`if p == "K" and abs(i - j) == 2: score += pst["R"][(i + j) // 2];
score -= pst["R"][A1 if j < i else H1]`.

**CENSUS FIRST, as the plan ordered.** `A1`, `H1`, `A8`, `H8` and `S` all resolve
STATICALLY in the globals fold (`some (some (.int 91))`, `98`, `21`, `28`, `10`)
— the dirty-name pass admits them, exactly as it does `TABLE_SIZE` for
`evict_dead`. **So this gate says nothing about `w.globals` beyond `pst`**, which
is what the census was for and it came out the way §L25 predicted.

Two shapes here are new: a floor DIVISION in an index, and a conditional
EXPRESSION in an index whose test (`j < i`) is symbolic. -/

theorem vlCastle_lit : ∃ s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34 s35, vlCastle =
    .ifStmt
      (.boolOp .and
        #[.compare (.name "p" s1) #[.eq] #[.constant (.str "K") s2] s3,
          .compare (.call (.name "abs" s4)
              #[.binOp (.name "i" s5) .sub (.name "j" s6) s7] #[] Option.none s8)
            #[.eq] #[.constant (.int 2) s9] s10] s11)
      #[.augAssign (.name "score" s12) .add
          (.subscript (.subscript (.name "pst" s13) (.constant (.str "R") s14) s15)
            (.binOp (.binOp (.name "i" s16) .add (.name "j" s17) s18) .floorDiv
              (.constant (.int 2) s19) s20) s21) s22,
        .augAssign (.name "score" s23) .sub
          (.subscript (.subscript (.name "pst" s24) (.constant (.str "R") s25) s26)
            (.ifExp (.compare (.name "j" s27) #[.lt] #[.name "i" s28] s29)
              (.name "A1" s30) (.name "H1" s31) s32) s33) s34]
      #[] s35 :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- **GATE 6a — the moved piece is not the king**, so the castle arm is dead.
The overwhelmingly common case, and it is one `if_neg`: the chain dies on its
FIRST operand and never looks at `abs(i - j)`. -/
theorem value_castle_skips (w : World) (e : REnv) (pc : String) (F : Nat)
    (hp : Env.lookup e "p" = some (.str pc)) (hne : pc ≠ "K") :
    execStmts sunfish (F + 20) ⟨w, e⟩ [vlCastle] = .ok ⟨w, e⟩ .next := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, hlit⟩ := vlCastle_lit
  rw [hlit]
  py_simp [-globalsFold, -globalsStep, hp, if_neg hne]

/-- **GATE 6b — the king moved, but only one square**, so the arm is dead for
the other reason. -/
theorem value_castle_skips_short (w : World) (e : REnv) (i j : Int) (F : Nat)
    (hp : Env.lookup e "p" = some (.str "K"))
    (hei : Env.lookup e "i" = some (.int i))
    (hej : Env.lookup e "j" = some (.int j))
    (hna : Env.lookup e "abs" = Option.none)
    (hshort : i - j ≠ 2 ∧ i - j ≠ -2) :
    execStmts sunfish (F + 20) ⟨w, e⟩ [vlCastle] = .ok ⟨w, e⟩ .next := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, hlit⟩ := vlCastle_lit
  have habs : ¬ ((if i - j < 0 then -(i - j) else i - j) = 2) := by
    obtain ⟨h1, h2⟩ := hshort; split <;> omega
  rw [hlit]
  py_simp [-globalsFold, -globalsStep, hp, hei, hej, hna, absG, absNotFun, absCls, absNT,
    if_neg habs]

/-- `A1` and `H1` resolve STATICALLY — the census this gate was priced on. -/
theorem a1G : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "A1"
    = some (some (.int 91)) := rfl
theorem h1G : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "H1"
    = some (some (.int 98)) := rfl

/-- **GATE 6c — the castle itself.** Two table reads: the rook's new square at
`(i + j) // 2` — Python floor division, which the interpreter leaves as
`Int.fdiv` — and the rook's old corner at `A1 if j < i else H1`, whose test is
symbolic, so the CONDITIONAL rides into the index term rather than splitting the
gate. Both are the computed-shape law: the premise names what the path leaves. -/
theorem value_castles (w : World) (e : REnv) (pa : Addr) (i j sv0 z1 z2 : Int)
    (es : Array (RVal × RVal)) (svv : Nat) (xs : Array RVal) (F : Nat)
    (hp : Env.lookup e "p" = some (.str "K"))
    (hei : Env.lookup e "i" = some (.int i))
    (hej : Env.lookup e "j" = some (.int j))
    (hna : Env.lookup e "abs" = Option.none)
    (hnp : Env.lookup e "pst" = Option.none)
    (hna1 : Env.lookup e "A1" = Option.none)
    (hnh1 : Env.lookup e "H1" = Option.none)
    (hs : Env.lookup e "score" = some (.int sv0))
    (hlong : i - j = 2 ∨ i - j = -2)
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hrow : dictFind es.toList (.str "R") = some (.tuple xs))
    (hsz : xs.size = 120)
    (hm1 : 0 ≤ (i + j).fdiv 2) (hm2 : (i + j).fdiv 2 < (xs.size : Int))
    (hx1 : xs[((i + j).fdiv 2).toNat]?.getD .none = .int z1)
    (hx2 : xs[(if j < i then (91 : Nat) else 98)]?.getD .none = .int z2) :
    execStmts sunfish (F + 24) ⟨w, e⟩ [vlCastle]
      = .ok ⟨w, Env.set (Env.set e "score" (.int (sv0 + z1))) "score"
              (.int (sv0 + z1 - z2))⟩ .next := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, hlit⟩ := vlCastle_lit
  have habs : ((if i - j < 0 then -(i - j) else i - j) = 2) := by
    rcases hlong with h | h <;> split <;> omega
  have hfd : ¬ ((i + j).fdiv 2 < 0) := by omega
  simp only [Heap.get?] at hd
  rw [hlit]
  by_cases hji : j < i
  · simp only [if_pos hji] at hx2
    py_simp [-globalsFold, -globalsStep, hp, hei, hej, hna, hnp, hna1, hnh1, hs, hg, hd, hrow,
      pstG, a1G, h1G, absG, absNotFun, absCls, absNT, normIndex, hx1, hx2,
      Env.lookup_set_self, Env.lookup_set_ne, if_pos habs, if_neg hfd, if_pos hji,
      if_neg (show ¬ (91 : Int) < 0 by decide),
      if_pos (show (91 : Int) < (xs.size : Int) by omega),
      if_pos (show (0 ≤ (i + j).fdiv 2 ∧ (i + j).fdiv 2 < (xs.size : Int)) from ⟨hm1, hm2⟩)]
  · simp only [if_neg hji] at hx2
    py_simp [-globalsFold, -globalsStep, hp, hei, hej, hna, hnp, hna1, hnh1, hs, hg, hd, hrow,
      pstG, a1G, h1G, absG, absNotFun, absCls, absNT, normIndex, hx1, hx2,
      Env.lookup_set_self, Env.lookup_set_ne, if_pos habs, if_neg hfd, if_neg hji,
      if_neg (show ¬ (98 : Int) < 0 by decide),
      if_pos (show (98 : Int) < (xs.size : Int) by omega),
      if_pos (show (0 ≤ (i + j).fdiv 2 ∧ (i + j).fdiv 2 < (xs.size : Int)) from ⟨hm1, hm2⟩)]

/-! ### The sixth statement — the pawn block, and A FIFTH ARM NOBODY PREDICTED

`if p == "P":` with TWO SIBLING `if`s inside — promotion and en passant — not
one nest. That matters: sibling tests give **four** pawn combinations, not
three, and the fourth is *promotion AND en passant at once*. It is physically
impossible (an en-passant square is on rank 3 or 6, a promotion square on rank
8), but it is REACHABLE IN THE CONTROL FLOW, so a four-arm enumeration would
have missed it and a five-arm one would spell out a case chess forbids.

**The factoring answers it without enumerating anything**: gate the outer `if`
as a PEEL and each sibling separately, and the caller composes with
`execStmts_append`. Every combination is then covered by construction, the
impossible one included, and nothing in this file has to claim it cannot happen.

`A8`/`H8`/`S` resolve statically (censused with `A1`/`H1`), so like GATE 6 this
says nothing about `w.globals` beyond `pst`. -/

theorem a8G : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "A8"
    = some (some (.int 21)) := rfl
theorem h8G : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "H8"
    = some (some (.int 28)) := rfl
theorem sG : lookupG (globalsFold #[] [] true false sunfish.topLevel.toList).snd.fst "S"
    = some (some (.int 10)) := rfl

/-- The pawn block's two sibling statements. -/
def vlPawnB : List Stmt := match vlPawn with | .ifStmt _ b _ _ => b.toList | _ => []
/-- `if A8 <= j <= H8: score += pst[prom][j] - pst["P"][j]` — promotion. -/
def vlProm : Stmt := nth 0 vlPawnB
/-- `if j == self.ep: score += pst["P"][119 - (j + S)]` — en passant. -/
def vlEp : Stmt := nth 1 vlPawnB

theorem vlPawnB_split : vlPawnB = [vlProm, vlEp] := rfl

theorem vlPawn_lit : ∃ a b c d, vlPawn =
    .ifStmt (.compare (.name "p" a) #[.eq] #[.constant (.str "P") b] c)
      vlPawnB.toArray #[] d :=
  ⟨_, _, _, _, rfl⟩

/-- **GATE 7a — not a pawn**, and the whole block is dead. -/
theorem value_pawn_skips (w : World) (e : REnv) (pc : String) (F : Nat)
    (hp : Env.lookup e "p" = some (.str pc)) (hne : pc ≠ "P") :
    execStmts sunfish (F + 8) ⟨w, e⟩ [vlPawn] = .ok ⟨w, e⟩ .next := by
  obtain ⟨a, b, c, d, hlit⟩ := vlPawn_lit
  have hc : evalExpr sunfish (F + 6) ⟨w, e⟩
      (.compare (.name "p" a) #[.eq] #[.constant (.str "P") b] c)
        = .ok ⟨w, e⟩ (.bool false) := by
    py_simp [-globalsFold, -globalsStep, hp, if_neg hne]
  have hs : execStmt sunfish (F + 7) ⟨w, e⟩ vlPawn = .ok ⟨w, e⟩ .next := by
    rw [hlit, execStmt_if_false hc rfl]
    rfl
  exact execStmts_singleton (F := F + 6) (by simpa using hs)

/-- **GATE 7b — the PEEL.** A pawn enters the block, and what is left is the two
sibling statements — each with its own gate below, so the four combinations
compose rather than being enumerated. -/
theorem value_pawn_enters (w : World) (e : REnv) (F : Nat)
    (hp : Env.lookup e "p" = some (.str "P")) :
    execStmt sunfish (F + 7) ⟨w, e⟩ vlPawn
      = execStmts sunfish (F + 6) ⟨w, e⟩ [vlProm, vlEp] := by
  obtain ⟨a, b, c, d, hlit⟩ := vlPawn_lit
  have hc : evalExpr sunfish (F + 6) ⟨w, e⟩
      (.compare (.name "p" a) #[.eq] #[.constant (.str "P") b] c)
        = .ok ⟨w, e⟩ (.bool true) := by
    py_simp [-globalsFold, -globalsStep, hp]
  have hL : vlPawnB.toArray.toList = [vlProm, vlEp] := by simp [vlPawnB_split]
  rw [hlit, execStmt_if_true hc rfl, hL]

/-- The promotion test, pinned with its body EXISTENTIAL — the skip arm never
enters it, and `sbCorr_noElse`'s law (§L19) says pin the shape you compute
with: here that is the `else`, which is empty. -/
theorem vlProm_lit : ∃ (bd : Array Stmt) (a b c d e : Span), vlProm =
    .ifStmt (.compare (.name "A8" a) #[.ltE, .ltE] #[.name "j" b, .name "H8" c] d) bd #[] e :=
  ⟨_, _, _, _, _, _, rfl⟩

theorem vlEp_lit : ∃ (bd : Array Stmt) (a b c d e : Span), vlEp =
    .ifStmt (.compare (.name "j" a) #[.eq] #[.attribute (.name "self" b) "ep" c] d) bd #[] e :=
  ⟨_, _, _, _, _, _, rfl⟩

/-- **GATE 7c — the pawn does not reach the last rank**, so the promotion arm is
dead — and this is the arm that makes the whole split MANDATORY: `prom` is `""`
on every non-promotion move, and `pst[""]` is a `KeyError`, so a gate carrying
the `prom` row unconditionally would be unsatisfiable here. The chained compare
`A8 <= j <= H8` reduces to plain arithmetic once `A8`/`H8` are resolved. -/
theorem value_prom_skips (w : World) (e : REnv) (j : Int) (F : Nat)
    (hej : Env.lookup e "j" = some (.int j))
    (hna : Env.lookup e "A8" = Option.none)
    (hnh : Env.lookup e "H8" = Option.none)
    (hout : j < 21 ∨ 28 < j) :
    execStmt sunfish (F + 7) ⟨w, e⟩ vlProm = .ok ⟨w, e⟩ .next := by
  obtain ⟨bd, a, b, c, d, e', hlit⟩ := vlProm_lit
  have hc : evalExpr sunfish (F + 6) ⟨w, e⟩
      (.compare (.name "A8" a) #[.ltE, .ltE] #[.name "j" b, .name "H8" c] d)
        = .ok ⟨w, e⟩ (.bool false) := by
    py_simp [-globalsFold, -globalsStep, hej, hna, hnh, a8G, h8G]
    omega
  rw [hlit, execStmt_if_false hc rfl]
  rfl

/-! ### GATE 7d — the en-passant arm, and it took a GENERAL LEMMA

Two fix attempts failed before the diagnosis landed, and the diagnosis is the
useful output. **Attempt 1, inline**: `py_simp` closed the branch and the KERNEL
refused it — `id (Eq.refl (match RVal.int j, rhs with …))`, a `rfl` under a match
BINDER, because `==` cases on both `RVal` operands at once. **Attempt 2,
sequence the read**: a `have` for `self.ep` does not FIRE, because the fuel the
compare's unfolding exposes is not the one the `have` was stated at.

**Neither was a premise-spelling problem; it was an ALTITUDE gap.** §L17 fixed
the same wall for `and` chains with `boolChain_and_falsy` — a lemma that proves
the outcome at the CHAIN with every operand universally quantified, so `evalExpr`
is never applied to an operand. `compare` had no such lemma. `compare_one`
(bound_depth.lean, added beside the three `boolChain_*`) is it, and with it this
gate is four lines: two operand facts, one `evalCompareOpH` fact, done. The
kernel never sees a `rfl` under a binder because nothing reduces under one.

**Carry this shape:** when `py_simp` produces a proof the ELABORATOR accepts and
the KERNEL refuses, do not hunt for a better premise — look for the construct
that has no altitude lemma yet. -/

/-- **GATE 7d — the destination is not the en-passant square**, so that arm is
dead. -/
theorem value_ep_skips (w : World) (e : REnv) (bd0 : String) (scv : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp j : Int) (F : Nat)
    (hself : Env.lookup e "self" = some (posOf bd0 scv wc0 wc1 bc0 bc1 ep kp))
    (hej : Env.lookup e "j" = some (.int j))
    (hne : j ≠ ep) :
    execStmt sunfish (F + 6) ⟨w, e⟩ vlEp = .ok ⟨w, e⟩ .next := by
  obtain ⟨bd, a, b, c, d, e', hlit⟩ := vlEp_lit
  have h1 : evalExpr sunfish (F + 4) ⟨w, e⟩ (.name "j" a) = .ok ⟨w, e⟩ (.int j) := by
    py_simp [-globalsFold, -globalsStep, hej]
  have h2 : evalExpr sunfish (F + 3) ⟨w, e⟩ (.attribute (.name "self" b) "ep" c)
      = .ok ⟨w, e⟩ (.int ep) := by
    py_simp [-globalsFold, -globalsStep, hself, posOf, posCAux, posCls_methods]
  have hop : evalCompareOpH w.heap (F + 3) .eq (.int j) (.int ep) = .ok false := by
    simp [evalCompareOpH, RVal.refFree, valEq, hne]
  rw [hlit, execStmt_if_false (compare_one (F := F + 2) h1 h2 hop) rfl]
  rfl

/-! ### GATE 7e/7f — the two pawn ADD arms, and why they need a SECOND pin

`vlProm_lit` and `vlEp_lit` leave the body EXISTENTIAL, which is right for the
skip arms — they never enter it, and §L19's law says pin the shape you compute
with. **An ADD arm computes with the body**, so an existential `bd` cannot
reduce and the pin has to spell it. That is the whole difference, and the trap
inside it is span arithmetic: the promotion body has **three** distinct trailing
spans (the `binOp`'s, the `augAssign`'s and the `ifStmt`'s), which is one more
than the shape reads at a glance.

Both pins are kept. Sharpening the skip arms' pin would say the same thing in a
worse place: those gates prove the body is never reached, and a statement that
spells what is not reached is a statement about the wrong thing. -/

/-- The promotion arm, body SPELLED — `score += pst[prom][j] - pst["P"][j]`. -/
theorem vlProm_body_lit : ∃ a b c d e f g h i k l m n o p q r s, vlProm =
    .ifStmt (.compare (.name "A8" a) #[.ltE, .ltE] #[.name "j" b, .name "H8" c] d)
      #[.augAssign (.name "score" e) .add
          (.binOp
            (.subscript (.subscript (.name "pst" f) (.name "prom" g) h) (.name "j" i) k)
            .sub
            (.subscript (.subscript (.name "pst" l) (.constant (.str "P") m) n)
              (.name "j" o) p)
            q)
          r]
      #[] s :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- The en-passant arm, body SPELLED — `score += pst["P"][119 - (j + S)]`. -/
theorem vlEp_body_lit : ∃ a b c d e f g h i k l m n o p q, vlEp =
    .ifStmt (.compare (.name "j" a) #[.eq] #[.attribute (.name "self" b) "ep" c] d)
      #[.augAssign (.name "score" e) .add
          (.subscript (.subscript (.name "pst" f) (.constant (.str "P") g) h)
            (.binOp (.constant (.int 119) i) .sub
              (.binOp (.name "j" k) .add (.name "S" l) m) n) o)
          p]
      #[] q :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- **GATE 7e — the pawn PROMOTES.** `A8 <= j <= H8`, so `prom` is a real piece
letter and `pst[prom]` is a legal key — which is the arm's whole reason for
existing separately (`value_prom_skips`' docstring: at `prom = ""` there is no
row). TWO rows are read, the promoted piece's and the pawn's, so the gate takes
two row premises and answers in their own entries.

The guard's chained compare leaves NESTED `if`s once `A8`/`H8` resolve — not a
conjunction — so it closes on two `if_pos`, and the destination's range premises
come free from `21 ≤ j ≤ 28` rather than being carried. -/
theorem value_prom_adds (w : World) (e : REnv) (pa : Addr) (pr : String)
    (es : Array (RVal × RVal)) (svv : Nat) (xs ys : Array RVal) (j s z1 z2 : Int) (F : Nat)
    (hej : Env.lookup e "j" = some (.int j))
    (hna : Env.lookup e "A8" = Option.none)
    (hnh : Env.lookup e "H8" = Option.none)
    (hnp : Env.lookup e "pst" = Option.none)
    (hpr : Env.lookup e "prom" = some (.str pr))
    (hs : Env.lookup e "score" = some (.int s))
    (hin : 21 ≤ j ∧ j ≤ 28)
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hrowp : dictFind es.toList (.str pr) = some (.tuple xs))
    (hrowP : dictFind es.toList (.str "P") = some (.tuple ys))
    (hszx : xs.size = 120) (hszy : ys.size = 120)
    (hx1 : xs[j.toNat]?.getD .none = .int z1)
    (hx2 : ys[j.toNat]?.getD .none = .int z2) :
    execStmt sunfish (F + 7) ⟨w, e⟩ vlProm
      = .ok ⟨w, Env.set e "score" (.int (s + (z1 - z2)))⟩ .next := by
  obtain ⟨a, b, c, d, e', f, g, h, i, k, l, m, n, o, p, q, r, s', hlit⟩ := vlProm_body_lit
  obtain ⟨hlo, hhi⟩ := hin
  have hc : evalExpr sunfish (F + 6) ⟨w, e⟩
      (.compare (.name "A8" a) #[.ltE, .ltE] #[.name "j" b, .name "H8" c] d)
        = .ok ⟨w, e⟩ (.bool true) := by
    py_simp [-globalsFold, -globalsStep, hej, hna, hnh, a8G, h8G,
      if_pos hlo, if_pos hhi]
  simp only [Heap.get?] at hd
  rw [hlit, execStmt_if_true hc rfl]
  py_simp [-globalsFold, -globalsStep, hnp, hpr, hej, hs, hg, hd, hrowp, hrowP, pstG,
    normIndex, hszx, hszy, hx1, hx2,
    if_neg (show ¬ j < 0 by omega),
    if_pos (show (0 ≤ j ∧ j < (120 : Int)) from ⟨by omega, by omega⟩)]

/-- **GATE 7f — the pawn takes EN PASSANT.** `j == self.ep`, and the captured
pawn's table value is read at the MIRROR of the square behind the destination.
`S` resolves statically (`sG`), so like GATE 6 this says nothing about
`w.globals` beyond `pst`; `compare_one` supplies the guard, which is the same
altitude gap GATE 7d hit and the reason that lemma was written.

The index premises are in the residue's OWN spelling — `119 - (j + S)` with `S`
already folded to `10` and no arithmetic done — because a premise stated at the
equivalent `109 - j` does not match what the path leaves. -/
theorem value_ep_adds (w : World) (e : REnv) (pa : Addr) (bd0 : String) (scv : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp j s z : Int)
    (es : Array (RVal × RVal)) (svv : Nat) (xs : Array RVal) (F : Nat)
    (hself : Env.lookup e "self" = some (posOf bd0 scv wc0 wc1 bc0 bc1 ep kp))
    (hej : Env.lookup e "j" = some (.int j))
    (hnp : Env.lookup e "pst" = Option.none)
    (hnS : Env.lookup e "S" = Option.none)
    (hs : Env.lookup e "score" = some (.int s))
    (heq : j = ep)
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hrow : dictFind es.toList (.str "P") = some (.tuple xs))
    (hsz : xs.size = 120)
    (hlo : j ≤ 109) (hhi : -10 ≤ j)
    (hx : xs[(119 - (j + 10)).toNat]?.getD .none = .int z) :
    execStmt sunfish (F + 7) ⟨w, e⟩ vlEp
      = .ok ⟨w, Env.set e "score" (.int (s + z))⟩ .next := by
  obtain ⟨a, b, c, d, e', f, g, h, i, k, l, m, n, o, p, q, hlit⟩ := vlEp_body_lit
  have h1 : evalExpr sunfish (F + 5) ⟨w, e⟩ (.name "j" a) = .ok ⟨w, e⟩ (.int j) := by
    py_simp [-globalsFold, -globalsStep, hej]
  have h2 : evalExpr sunfish (F + 4) ⟨w, e⟩ (.attribute (.name "self" b) "ep" c)
      = .ok ⟨w, e⟩ (.int ep) := by
    py_simp [-globalsFold, -globalsStep, hself, posOf, posCAux, posCls_methods]
  have hop : evalCompareOpH w.heap (F + 4) .eq (.int j) (.int ep) = .ok true := by
    simp [evalCompareOpH, RVal.refFree, valEq, heq]
  simp only [Heap.get?] at hd
  rw [hlit, execStmt_if_true (compare_one (F := F + 3) h1 h2 hop) rfl]
  py_simp [-globalsFold, -globalsStep, hnp, hnS, hej, hs, hg, hd, hrow, pstG, sG,
    normIndex, hsz, hx,
    if_neg (show ¬ (119 - (j + 10)) < 0 by omega),
    if_pos (show (j + 10 ≤ 119 ∧ 119 - (j + 10) < (120 : Int)) from ⟨by omega, by omega⟩)]

/-! ## §3 THE COMPOSITION, on the quiet move

The eight gates, chained. Stated for the **quiet** configuration — not a
capture, not beside the king square, not a castle, not a pawn special — because
that is the arm set `gen_moves` produces for most of its stream and the one the
fold consumes most; every `if` takes its SKIP arm, all four of which are proved
above. The capture/castle/promotion/en-passant configurations reuse the same
chain with the corresponding ADD gate swapped in, which is why the arms were
split rather than folded into existentials.

The answer is `zj - zi` — stated in the `pst` row's OWN entries, so the whole
theorem names no table constant. -/

/-- The frame the score assignment leaves. -/
def vlEnv3 (pv : RVal) (i j : Int) (prom pc qc : String) (s : Int) : REnv :=
  Env.set (vlEnv2 pv i j prom pc qc) "score" (.int s)

theorem vlArity2 : arityOk vlF.params 2 = true := rfl

/-- **The boundary**: `callIn` reaches `Position.value`'s body and carries the
`.ret` out. `callIn_of_body`'s twin for the two-argument method. -/
theorem callIn_of_value_body {w : World} {pv mv : RVal} {e' : REnv} {v : RVal} {F : Nat}
    (h : execStmts sunfish F ⟨w, vlEnv pv mv⟩ vlB = .ok ⟨w, e'⟩ (.ret v)) :
    callIn sunfish (F + 1) w "Position.value" #[pv, mv] = .ok w v := by
  obtain ⟨hfind, hargs, hloc, hgen, hbody, hglob, harity⟩ := vlF_lit
  rw [callIn, hfind]
  simp only [hargs, hloc, hgen, Bool.not_true, Bool.false_eq_true, if_neg,
    not_false_eq_true, hbody, vlCallEnv, h, Run.bind, Run.toWorld,
    show (#[pv, mv] : Array RVal).size = 2 from rfl, vlArity2]

theorem vlB_appends : vlB =
    ((((((([vlUnpack] ++ [vlPQ]) ++ [vlScore]) ++ [vlCap]) ++ [vlKp]) ++ [vlCastle])
      ++ [vlPawn]) ++ [vlRet]) := rfl

set_option linter.unusedVariables false in
/-- **THE WHOLE METHOD, on a quiet move.** All eight statements of the shipped
`Position.value`, from the entry frame to the `return`. -/
theorem value_body_quiet (w : World) (pa : Addr) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp i j zi zj : Int) (prom : String)
    (es : Array (RVal × RVal)) (svv : Nat) (xs : Array RVal)
    (hi : 0 ≤ i) (hib : i < (b.length : Int)) (hi2 : i < 120)
    (hj : 0 ≤ j) (hjb : j < (b.length : Int)) (hj2 : j < 120)
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hrow : dictFind es.toList (.str (boardAt b i)) = some (.tuple xs))
    (hsz : xs.size = 120)
    (hxi : xs[i.toNat]?.getD .none = .int zi)
    (hxj : xs[j.toNat]?.getD .none = .int zj)
    (hquiet : strContains "pnbrqk" (boardAt b j) = false)
    (hfar : 2 ≤ j - kp ∨ j - kp ≤ -2)
    (hnk : boardAt b i ≠ "K") (hnpw : boardAt b i ≠ "P") :
    ∃ f, execStmts sunfish f
        ⟨w, vlEnv (posOf b sc wc0 wc1 bc0 bc1 ep kp) (mvOf i j prom)⟩ vlB
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ (.ret (.int (zj - zi))) := by
  have h1 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv (posOf b sc wc0 wc1 bc0 bc1 ep kp) (mvOf i j prom)⟩ [vlUnpack]
      = .ok ⟨w, vlEnv1 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom⟩ .next :=
    ⟨4, value_unpacks w (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom 0⟩
  have h2 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv1 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom⟩ [vlPQ]
      = .ok ⟨w, vlEnv2 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j)⟩ .next :=
    ⟨8, value_reads_pq w b sc wc0 wc1 bc0 bc1 ep kp i j prom 0 hi hib hj hjb⟩
  have h3 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv2 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j)⟩ [vlScore]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ .next :=
    ⟨10, value_scores w _ pa (boardAt b i) es svv xs i j zi zj 0
      (by simp [vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
      (by simp [vlEnv2, Env.lookup_set_ne, Env.lookup_set_self])
      (by simp [vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
      (by simp [vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
      hg hd hrow hsz hi hi2 hj hj2 hxi hxj⟩
  have h4 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi)⟩ [vlCap]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ .next :=
    ⟨10, value_cap_skips w _ (boardAt b j) 0
      (by simp [vlEnv3, vlEnv2, Env.lookup_set_ne, Env.lookup_set_self]) hquiet⟩
  have h5 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi)⟩ [vlKp]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ .next :=
    ⟨14, value_kp_skips w _ b sc wc0 wc1 bc0 bc1 ep kp j 0
      (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
      (by simp [vlEnv3, vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
      (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf]) hfar⟩
  have h6 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi)⟩ [vlCastle]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ .next :=
    ⟨20, value_castle_skips w _ (boardAt b i) 0
      (by simp [vlEnv3, vlEnv2, Env.lookup_set_ne, Env.lookup_set_self]) hnk⟩
  have h7 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi)⟩ [vlPawn]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ .next :=
    ⟨8, value_pawn_skips w _ (boardAt b i) 0
      (by simp [vlEnv3, vlEnv2, Env.lookup_set_ne, Env.lookup_set_self]) hnpw⟩
  have h8 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi)⟩ [vlRet]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ (.ret (.int (zj - zi))) :=
    ⟨4, value_returns w _ (zj - zi) 0 (by simp [vlEnv3, Env.lookup_set_self])⟩
  rw [vlB_appends]
  exact execStmts_append (execStmts_append (execStmts_append (execStmts_append
    (execStmts_append (execStmts_append (execStmts_append h1 h2 (by simp)) h3 (by simp))
      h4 (by simp)) h5 (by simp)) h6 (by simp)) h7 (by simp)) h8 (by simp)

set_option linter.unusedVariables false in
/-- **`value_runs` — `Position.value` DECIDES, heap-free, on a quiet move.**
Inch R1 of the campaign, in the ∃-fuel form every other closing theorem in this
tree uses. The world in is the world out, which is what the fixture measurement
said before a line of this file was written. -/
theorem value_runs_quiet (w : World) (pa : Addr) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp i j zi zj : Int) (prom : String)
    (es : Array (RVal × RVal)) (svv : Nat) (xs : Array RVal)
    (hi : 0 ≤ i) (hib : i < (b.length : Int)) (hi2 : i < 120)
    (hj : 0 ≤ j) (hjb : j < (b.length : Int)) (hj2 : j < 120)
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hrow : dictFind es.toList (.str (boardAt b i)) = some (.tuple xs))
    (hsz : xs.size = 120)
    (hxi : xs[i.toNat]?.getD .none = .int zi)
    (hxj : xs[j.toNat]?.getD .none = .int zj)
    (hquiet : strContains "pnbrqk" (boardAt b j) = false)
    (hfar : 2 ≤ j - kp ∨ j - kp ≤ -2)
    (hnk : boardAt b i ≠ "K") (hnpw : boardAt b i ≠ "P") :
    ∃ t, ∀ F ≥ t, callIn sunfish F w "Position.value"
        #[posOf b sc wc0 wc1 bc0 bc1 ep kp, mvOf i j prom]
      = .ok w (.int (zj - zi)) := by
  obtain ⟨f, hf⟩ := value_body_quiet w pa b sc wc0 wc1 bc0 bc1 ep kp i j zi zj prom
    es svv xs hi hib hi2 hj hjb hj2 hg hd hrow hsz hxi hxj hquiet hfar hnk hnpw
  refine ⟨f + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ : ∃ F', F = F' + 1 ∧ f ≤ F' := ⟨F - 1, by omega, by omega⟩
  exact callIn_of_value_body (execStmts_mono hf (by simp) F' hF')

/-! ### THE INSTANTIATION — run it, do not admire it

`value_runs_quiet` is stated over a free board and a free `pst`, so the question
a reader must ask is whether its premises are ever MET. These guards answer it on
the shipped fixture at `Move(92, 71)` — the knight move `pins_init` pins CPython's
`5` for — by checking **each premise separately** and then the conclusion.

Every one of them reads the live `initWorld`; none is a constant written by
hand. The last two are the theorem's own arithmetic against the engine's answer,
which is what makes this an instantiation rather than a restatement. -/

private def fxRow : Option (Array RVal) :=
  match Env.lookup (initWorld sunfish).globals "pst" with
  | some (.ref pa) =>
    (match Heap.get? (initWorld sunfish).heap pa with
     | some (.dict es _) =>
       (match dictFind es.toList (.str (boardAt board0 92)) with
        | some (.tuple xs) => some xs | _ => Option.none)
     | _ => Option.none)
  | _ => Option.none

/-! The moved piece is a knight, the destination is empty, and the board is 120
wide — so `boardAt` names the two squares the premises are about. -/
#guard boardAt board0 92 == "N" && boardAt board0 71 == "." && board0.length == 120

/-! The QUIET premises, each on the live board. -/
#guard strContains "pnbrqk" (boardAt board0 71) == false
#guard boardAt board0 92 != "K" && boardAt board0 92 != "P"
#guard (decide (2 ≤ (71 : Int) - 0) : Bool)

/-! The `pst` premises, from the live world: the row is there and 120 wide. -/
#guard (match fxRow with | some xs => xs.size == 120 | _ => false)

/-! And the CONCLUSION: the row's own two entries differ by exactly the number
the engine answers, so `zj - zi` is not an artifact of the statement. -/
#guard (match fxRow with
  | some xs =>
    (match xs[(71 : Nat)]?.getD .none, xs[(92 : Nat)]?.getD .none with
     | .int zj, .int zi => zj - zi == 5
     | _, _ => false)
  | _ => false)

#guard (match callIn sunfish 64 (initWorld sunfish) "Position.value"
          #[posH 0, mvOf 92 71 ""] with
        | .ok w v => v == .int 5 && w.heap.size == (initWorld sunfish).heap.size
        | _ => false)

/-! ## §4 THE THREE NON-QUIET COMPOSITIONS

Each is §3's chain with **one gate swapped**, which is what the two-gates-per-`if`
factoring (law 2) was for: the ADD gates are already proved, so nothing here is
discovery. The three swaps are `value_cap_adds` for `value_cap_skips`,
`value_kp_adds` for `value_kp_skips`, and `value_castles` for
`value_castle_skips`.

One bridge is owed and it is the only new lemma: an arm that fires WRITES
`score`, and the frame `vlEnv3` already has a `score` slot, so the second write
has to be recognised as a replacement rather than a second binding. -/

/-- The score slot is written once per arm, so a later write REPLACES it — which
is what lets an ADD arm's output frame be `vlEnv3` again rather than a tower of
`Env.set`s. `value_castles` writes twice, so the castle composition spends this
twice. -/
theorem vlEnv3_rescore (pv : RVal) (i j : Int) (prom pc qc : String) (s t : Int) :
    Env.set (vlEnv3 pv i j prom pc qc s) "score" (.int t)
      = vlEnv3 pv i j prom pc qc t := by
  simp [vlEnv3, Env.set_set]

set_option linter.unusedVariables false in
/-- **THE METHOD ON A CAPTURE.** `value_cap_adds` in place of
`value_cap_skips`; every other arm is the quiet chain's. The captured piece's
row is a SECOND row premise, keyed by `q.upper()`, and the answer carries its
mirrored-square entry. -/
theorem value_body_capture (w : World) (pa : Addr) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp i j zi zj zc : Int) (prom uc : String)
    (es : Array (RVal × RVal)) (svv : Nat) (xs ys : Array RVal)
    (hi : 0 ≤ i) (hib : i < (b.length : Int)) (hi2 : i < 120)
    (hj : 0 ≤ j) (hjb : j < (b.length : Int)) (hj2 : j < 120)
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hrow : dictFind es.toList (.str (boardAt b i)) = some (.tuple xs))
    (hsz : xs.size = 120)
    (hxi : xs[i.toNat]?.getD .none = .int zi)
    (hxj : xs[j.toNat]?.getD .none = .int zj)
    (hcap : strContains "pnbrqk" (boardAt b j) = true)
    (hup : strUpper (boardAt b j) = .ok (.str uc))
    (hcrow : dictFind es.toList (.str uc) = some (.tuple ys))
    (hcsz : ys.size = 120)
    (hcx : ys[(119 - j).toNat]?.getD .none = .int zc)
    (hfar : 2 ≤ j - kp ∨ j - kp ≤ -2)
    (hnk : boardAt b i ≠ "K") (hnpw : boardAt b i ≠ "P") :
    ∃ f, execStmts sunfish f
        ⟨w, vlEnv (posOf b sc wc0 wc1 bc0 bc1 ep kp) (mvOf i j prom)⟩ vlB
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + zc)⟩ (.ret (.int (zj - zi + zc))) := by
  have h1 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv (posOf b sc wc0 wc1 bc0 bc1 ep kp) (mvOf i j prom)⟩ [vlUnpack]
      = .ok ⟨w, vlEnv1 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom⟩ .next :=
    ⟨4, value_unpacks w (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom 0⟩
  have h2 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv1 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom⟩ [vlPQ]
      = .ok ⟨w, vlEnv2 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j)⟩ .next :=
    ⟨8, value_reads_pq w b sc wc0 wc1 bc0 bc1 ep kp i j prom 0 hi hib hj hjb⟩
  have h3 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv2 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j)⟩ [vlScore]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ .next :=
    ⟨10, value_scores w _ pa (boardAt b i) es svv xs i j zi zj 0
      (by simp [vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
      (by simp [vlEnv2, Env.lookup_set_ne, Env.lookup_set_self])
      (by simp [vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
      (by simp [vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
      hg hd hrow hsz hi hi2 hj hj2 hxi hxj⟩
  have h4 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi)⟩ [vlCap]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + zc)⟩ .next :=
    ⟨14, by
      have h := value_cap_adds w (vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
          (boardAt b i) (boardAt b j) (zj - zi)) pa (boardAt b j) uc es svv ys j
          (zj - zi) zc 0
        (by simp [vlEnv3, vlEnv2, Env.lookup_set_ne, Env.lookup_set_self]) hcap hup
        (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
        (by simp [vlEnv3, vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
        (by simp [vlEnv3, Env.lookup_set_self])
        hg hd hcrow hcsz (by omega) (by omega) hcx
      rwa [vlEnv3_rescore] at h⟩
  have h5 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi + zc)⟩ [vlKp]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + zc)⟩ .next :=
    ⟨14, value_kp_skips w _ b sc wc0 wc1 bc0 bc1 ep kp j 0
      (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
      (by simp [vlEnv3, vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
      (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf]) hfar⟩
  have h6 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi + zc)⟩ [vlCastle]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + zc)⟩ .next :=
    ⟨20, value_castle_skips w _ (boardAt b i) 0
      (by simp [vlEnv3, vlEnv2, Env.lookup_set_ne, Env.lookup_set_self]) hnk⟩
  have h7 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi + zc)⟩ [vlPawn]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + zc)⟩ .next :=
    ⟨8, value_pawn_skips w _ (boardAt b i) 0
      (by simp [vlEnv3, vlEnv2, Env.lookup_set_ne, Env.lookup_set_self]) hnpw⟩
  have h8 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi + zc)⟩ [vlRet]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + zc)⟩ (.ret (.int (zj - zi + zc))) :=
    ⟨4, value_returns w _ (zj - zi + zc) 0 (by simp [vlEnv3, Env.lookup_set_self])⟩
  rw [vlB_appends]
  exact execStmts_append (execStmts_append (execStmts_append (execStmts_append
    (execStmts_append (execStmts_append (execStmts_append h1 h2 (by simp)) h3 (by simp))
      h4 (by simp)) h5 (by simp)) h6 (by simp)) h7 (by simp)) h8 (by simp)

set_option linter.unusedVariables false in
/-- **THE METHOD BESIDE THE KING SQUARE.** `value_kp_adds` in place of
`value_kp_skips`. The row read here is the KING's at the mirrored destination,
and the arm is the shipped castling-through-check detection: it fires exactly
when the destination is within one of the opponent's king-passant square. -/
theorem value_body_kp (w : World) (pa : Addr) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp i j zi zj zk : Int) (prom : String)
    (es : Array (RVal × RVal)) (svv : Nat) (xs ks : Array RVal)
    (hi : 0 ≤ i) (hib : i < (b.length : Int)) (hi2 : i < 120)
    (hj : 0 ≤ j) (hjb : j < (b.length : Int)) (hj2 : j < 120)
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hrow : dictFind es.toList (.str (boardAt b i)) = some (.tuple xs))
    (hsz : xs.size = 120)
    (hxi : xs[i.toNat]?.getD .none = .int zi)
    (hxj : xs[j.toNat]?.getD .none = .int zj)
    (hquiet : strContains "pnbrqk" (boardAt b j) = false)
    (hnear : -2 < j - kp ∧ j - kp < 2)
    (hkrow : dictFind es.toList (.str "K") = some (.tuple ks))
    (hksz : ks.size = 120)
    (hkx : ks[(119 - j).toNat]?.getD .none = .int zk)
    (hnk : boardAt b i ≠ "K") (hnpw : boardAt b i ≠ "P") :
    ∃ f, execStmts sunfish f
        ⟨w, vlEnv (posOf b sc wc0 wc1 bc0 bc1 ep kp) (mvOf i j prom)⟩ vlB
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + zk)⟩ (.ret (.int (zj - zi + zk))) := by
  have h1 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv (posOf b sc wc0 wc1 bc0 bc1 ep kp) (mvOf i j prom)⟩ [vlUnpack]
      = .ok ⟨w, vlEnv1 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom⟩ .next :=
    ⟨4, value_unpacks w (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom 0⟩
  have h2 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv1 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom⟩ [vlPQ]
      = .ok ⟨w, vlEnv2 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j)⟩ .next :=
    ⟨8, value_reads_pq w b sc wc0 wc1 bc0 bc1 ep kp i j prom 0 hi hib hj hjb⟩
  have h3 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv2 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j)⟩ [vlScore]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ .next :=
    ⟨10, value_scores w _ pa (boardAt b i) es svv xs i j zi zj 0
      (by simp [vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
      (by simp [vlEnv2, Env.lookup_set_ne, Env.lookup_set_self])
      (by simp [vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
      (by simp [vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
      hg hd hrow hsz hi hi2 hj hj2 hxi hxj⟩
  have h4 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi)⟩ [vlCap]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ .next :=
    ⟨10, value_cap_skips w _ (boardAt b j) 0
      (by simp [vlEnv3, vlEnv2, Env.lookup_set_ne, Env.lookup_set_self]) hquiet⟩
  have h5 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi)⟩ [vlKp]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + zk)⟩ .next :=
    ⟨16, by
      have h := value_kp_adds w (vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
          (boardAt b i) (boardAt b j) (zj - zi)) pa b sc wc0 wc1 bc0 bc1 ep kp j
          (zj - zi) zk es svv ks 0
        (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
        (by simp [vlEnv3, vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
        (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
        (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
        (by simp [vlEnv3, Env.lookup_set_self])
        hnear hg hd hkrow hksz (by omega) (by omega) hkx
      rwa [vlEnv3_rescore] at h⟩
  have h6 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi + zk)⟩ [vlCastle]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + zk)⟩ .next :=
    ⟨20, value_castle_skips w _ (boardAt b i) 0
      (by simp [vlEnv3, vlEnv2, Env.lookup_set_ne, Env.lookup_set_self]) hnk⟩
  have h7 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi + zk)⟩ [vlPawn]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + zk)⟩ .next :=
    ⟨8, value_pawn_skips w _ (boardAt b i) 0
      (by simp [vlEnv3, vlEnv2, Env.lookup_set_ne, Env.lookup_set_self]) hnpw⟩
  have h8 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi + zk)⟩ [vlRet]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + zk)⟩ (.ret (.int (zj - zi + zk))) :=
    ⟨4, value_returns w _ (zj - zi + zk) 0 (by simp [vlEnv3, Env.lookup_set_self])⟩
  rw [vlB_appends]
  exact execStmts_append (execStmts_append (execStmts_append (execStmts_append
    (execStmts_append (execStmts_append (execStmts_append h1 h2 (by simp)) h3 (by simp))
      h4 (by simp)) h5 (by simp)) h6 (by simp)) h7 (by simp)) h8 (by simp)

set_option linter.unusedVariables false in
/-- **THE METHOD ON A CASTLE.** `value_castles` in place of
`value_castle_skips`, and the moved piece is the KING — so the mover's own row
premise is `pst["K"]` and `boardAt b i ≠ "P"` is no longer a hypothesis but a
consequence. Two table reads fire in this arm, so `vlEnv3_rescore` is spent
twice and the answer carries the rook's new square minus its old corner. -/
theorem value_body_castle (w : World) (pa : Addr) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp i j zi zj z1 z2 : Int) (prom : String)
    (es : Array (RVal × RVal)) (svv : Nat) (xs rs : Array RVal)
    (hi : 0 ≤ i) (hib : i < (b.length : Int)) (hi2 : i < 120)
    (hj : 0 ≤ j) (hjb : j < (b.length : Int)) (hj2 : j < 120)
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hk : boardAt b i = "K")
    (hrow : dictFind es.toList (.str "K") = some (.tuple xs))
    (hsz : xs.size = 120)
    (hxi : xs[i.toNat]?.getD .none = .int zi)
    (hxj : xs[j.toNat]?.getD .none = .int zj)
    (hquiet : strContains "pnbrqk" (boardAt b j) = false)
    (hfar : 2 ≤ j - kp ∨ j - kp ≤ -2)
    (hlong : i - j = 2 ∨ i - j = -2)
    (hrrow : dictFind es.toList (.str "R") = some (.tuple rs))
    (hrsz : rs.size = 120)
    (hm1 : 0 ≤ (i + j).fdiv 2) (hm2 : (i + j).fdiv 2 < (rs.size : Int))
    (hy1 : rs[((i + j).fdiv 2).toNat]?.getD .none = .int z1)
    (hy2 : rs[(if j < i then (91 : Nat) else 98)]?.getD .none = .int z2) :
    ∃ f, execStmts sunfish f
        ⟨w, vlEnv (posOf b sc wc0 wc1 bc0 bc1 ep kp) (mvOf i j prom)⟩ vlB
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + z1 - z2)⟩
          (.ret (.int (zj - zi + z1 - z2))) := by
  have hnpw : boardAt b i ≠ "P" := by rw [hk]; decide
  have h1 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv (posOf b sc wc0 wc1 bc0 bc1 ep kp) (mvOf i j prom)⟩ [vlUnpack]
      = .ok ⟨w, vlEnv1 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom⟩ .next :=
    ⟨4, value_unpacks w (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom 0⟩
  have h2 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv1 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom⟩ [vlPQ]
      = .ok ⟨w, vlEnv2 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j)⟩ .next :=
    ⟨8, value_reads_pq w b sc wc0 wc1 bc0 bc1 ep kp i j prom 0 hi hib hj hjb⟩
  have h3 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv2 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j)⟩ [vlScore]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ .next :=
    ⟨10, value_scores w _ pa (boardAt b i) es svv xs i j zi zj 0
      (by simp [vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
      (by simp [vlEnv2, Env.lookup_set_ne, Env.lookup_set_self])
      (by simp [vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
      (by simp [vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
      hg hd (by rw [hk]; exact hrow) hsz hi hi2 hj hj2 hxi hxj⟩
  have h4 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi)⟩ [vlCap]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ .next :=
    ⟨10, value_cap_skips w _ (boardAt b j) 0
      (by simp [vlEnv3, vlEnv2, Env.lookup_set_ne, Env.lookup_set_self]) hquiet⟩
  have h5 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi)⟩ [vlKp]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi)⟩ .next :=
    ⟨14, value_kp_skips w _ b sc wc0 wc1 bc0 bc1 ep kp j 0
      (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
      (by simp [vlEnv3, vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
      (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf]) hfar⟩
  have h6 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi)⟩ [vlCastle]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + z1 - z2)⟩ .next :=
    ⟨24, by
      have h := value_castles w (vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
          (boardAt b i) (boardAt b j) (zj - zi)) pa i j (zj - zi) z1 z2 es svv rs 0
        (by simp [vlEnv3, vlEnv2, Env.lookup_set_ne, Env.lookup_set_self, hk])
        (by simp [vlEnv3, vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
        (by simp [vlEnv3, vlEnv2, vlEnv1, Env.lookup_set_ne, Env.lookup_set_self])
        (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
        (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
        (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
        (by simp [vlEnv3, vlEnv2, vlEnv1, vlEnv, Env.lookup_set_ne, Env.lookup, mvOf])
        (by simp [vlEnv3, Env.lookup_set_self])
        hlong hg hd hrrow hrsz hm1 hm2 hy1 hy2
      rwa [vlEnv3_rescore, vlEnv3_rescore] at h⟩
  have h7 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi + z1 - z2)⟩ [vlPawn]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + z1 - z2)⟩ .next :=
    ⟨8, value_pawn_skips w _ (boardAt b i) 0
      (by simp [vlEnv3, vlEnv2, Env.lookup_set_ne, Env.lookup_set_self]) hnpw⟩
  have h8 : ∃ f, execStmts sunfish f
      ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
        (boardAt b i) (boardAt b j) (zj - zi + z1 - z2)⟩ [vlRet]
      = .ok ⟨w, vlEnv3 (posOf b sc wc0 wc1 bc0 bc1 ep kp) i j prom
              (boardAt b i) (boardAt b j) (zj - zi + z1 - z2)⟩
          (.ret (.int (zj - zi + z1 - z2))) :=
    ⟨4, value_returns w _ (zj - zi + z1 - z2) 0 (by simp [vlEnv3, Env.lookup_set_self])⟩
  rw [vlB_appends]
  exact execStmts_append (execStmts_append (execStmts_append (execStmts_append
    (execStmts_append (execStmts_append (execStmts_append h1 h2 (by simp)) h3 (by simp))
      h4 (by simp)) h5 (by simp)) h6 (by simp)) h7 (by simp)) h8 (by simp)

/-! ### The three closing theorems, in `value_runs_quiet`'s own shape

`callIn_of_value_body` plus `execStmts_mono` at a summed witness, three times —
so each arm gets the `∃ t, ∀ F ≥ t` total-correctness form the rest of this tree
speaks, and the world in is the world out in every one of them. -/

set_option linter.unusedVariables false in
/-- **`Position.value` DECIDES on a CAPTURE, heap-free.** -/
theorem value_runs_capture (w : World) (pa : Addr) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp i j zi zj zc : Int) (prom uc : String)
    (es : Array (RVal × RVal)) (svv : Nat) (xs ys : Array RVal)
    (hi : 0 ≤ i) (hib : i < (b.length : Int)) (hi2 : i < 120)
    (hj : 0 ≤ j) (hjb : j < (b.length : Int)) (hj2 : j < 120)
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hrow : dictFind es.toList (.str (boardAt b i)) = some (.tuple xs))
    (hsz : xs.size = 120)
    (hxi : xs[i.toNat]?.getD .none = .int zi)
    (hxj : xs[j.toNat]?.getD .none = .int zj)
    (hcap : strContains "pnbrqk" (boardAt b j) = true)
    (hup : strUpper (boardAt b j) = .ok (.str uc))
    (hcrow : dictFind es.toList (.str uc) = some (.tuple ys))
    (hcsz : ys.size = 120)
    (hcx : ys[(119 - j).toNat]?.getD .none = .int zc)
    (hfar : 2 ≤ j - kp ∨ j - kp ≤ -2)
    (hnk : boardAt b i ≠ "K") (hnpw : boardAt b i ≠ "P") :
    ∃ t, ∀ F ≥ t, callIn sunfish F w "Position.value"
        #[posOf b sc wc0 wc1 bc0 bc1 ep kp, mvOf i j prom]
      = .ok w (.int (zj - zi + zc)) := by
  obtain ⟨f, hf⟩ := value_body_capture w pa b sc wc0 wc1 bc0 bc1 ep kp i j zi zj zc prom uc
    es svv xs ys hi hib hi2 hj hjb hj2 hg hd hrow hsz hxi hxj hcap hup hcrow hcsz hcx
    hfar hnk hnpw
  refine ⟨f + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ : ∃ F', F = F' + 1 ∧ f ≤ F' := ⟨F - 1, by omega, by omega⟩
  exact callIn_of_value_body (execStmts_mono hf (by simp) F' hF')

set_option linter.unusedVariables false in
/-- **`Position.value` DECIDES beside the king square, heap-free.** -/
theorem value_runs_kp (w : World) (pa : Addr) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp i j zi zj zk : Int) (prom : String)
    (es : Array (RVal × RVal)) (svv : Nat) (xs ks : Array RVal)
    (hi : 0 ≤ i) (hib : i < (b.length : Int)) (hi2 : i < 120)
    (hj : 0 ≤ j) (hjb : j < (b.length : Int)) (hj2 : j < 120)
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hrow : dictFind es.toList (.str (boardAt b i)) = some (.tuple xs))
    (hsz : xs.size = 120)
    (hxi : xs[i.toNat]?.getD .none = .int zi)
    (hxj : xs[j.toNat]?.getD .none = .int zj)
    (hquiet : strContains "pnbrqk" (boardAt b j) = false)
    (hnear : -2 < j - kp ∧ j - kp < 2)
    (hkrow : dictFind es.toList (.str "K") = some (.tuple ks))
    (hksz : ks.size = 120)
    (hkx : ks[(119 - j).toNat]?.getD .none = .int zk)
    (hnk : boardAt b i ≠ "K") (hnpw : boardAt b i ≠ "P") :
    ∃ t, ∀ F ≥ t, callIn sunfish F w "Position.value"
        #[posOf b sc wc0 wc1 bc0 bc1 ep kp, mvOf i j prom]
      = .ok w (.int (zj - zi + zk)) := by
  obtain ⟨f, hf⟩ := value_body_kp w pa b sc wc0 wc1 bc0 bc1 ep kp i j zi zj zk prom
    es svv xs ks hi hib hi2 hj hjb hj2 hg hd hrow hsz hxi hxj hquiet hnear hkrow hksz hkx
    hnk hnpw
  refine ⟨f + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ : ∃ F', F = F' + 1 ∧ f ≤ F' := ⟨F - 1, by omega, by omega⟩
  exact callIn_of_value_body (execStmts_mono hf (by simp) F' hF')

set_option linter.unusedVariables false in
/-- **`Position.value` DECIDES on a CASTLE, heap-free.** -/
theorem value_runs_castle (w : World) (pa : Addr) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp i j zi zj z1 z2 : Int) (prom : String)
    (es : Array (RVal × RVal)) (svv : Nat) (xs rs : Array RVal)
    (hi : 0 ≤ i) (hib : i < (b.length : Int)) (hi2 : i < 120)
    (hj : 0 ≤ j) (hjb : j < (b.length : Int)) (hj2 : j < 120)
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es svv))
    (hk : boardAt b i = "K")
    (hrow : dictFind es.toList (.str "K") = some (.tuple xs))
    (hsz : xs.size = 120)
    (hxi : xs[i.toNat]?.getD .none = .int zi)
    (hxj : xs[j.toNat]?.getD .none = .int zj)
    (hquiet : strContains "pnbrqk" (boardAt b j) = false)
    (hfar : 2 ≤ j - kp ∨ j - kp ≤ -2)
    (hlong : i - j = 2 ∨ i - j = -2)
    (hrrow : dictFind es.toList (.str "R") = some (.tuple rs))
    (hrsz : rs.size = 120)
    (hm1 : 0 ≤ (i + j).fdiv 2) (hm2 : (i + j).fdiv 2 < (rs.size : Int))
    (hy1 : rs[((i + j).fdiv 2).toNat]?.getD .none = .int z1)
    (hy2 : rs[(if j < i then (91 : Nat) else 98)]?.getD .none = .int z2) :
    ∃ t, ∀ F ≥ t, callIn sunfish F w "Position.value"
        #[posOf b sc wc0 wc1 bc0 bc1 ep kp, mvOf i j prom]
      = .ok w (.int (zj - zi + z1 - z2)) := by
  obtain ⟨f, hf⟩ := value_body_castle w pa b sc wc0 wc1 bc0 bc1 ep kp i j zi zj z1 z2 prom
    es svv xs rs hi hib hi2 hj hjb hj2 hg hd hk hrow hsz hxi hxj hquiet hfar hlong
    hrrow hrsz hm1 hm2 hy1 hy2
  refine ⟨f + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ : ∃ F', F = F' + 1 ∧ f ≤ F' := ⟨F - 1, by omega, by omega⟩
  exact callIn_of_value_body (execStmts_mono hf (by simp) F' hF')

/-! ### THE INSTANTIATIONS — three arms, on positions the ENGINE reached

§3's fixture answered "are these premises ever met?" for the quiet chain. The
question is sharper here, because the non-quiet arms are the ones a hand-written
board can fake. So no board below is invented: each is the result of running the
shipped `Position.move` from the shipped opening position, ply by ply, and **two
of the three moves are moves the shipped `gen_moves` produces from the position
they are scored in.**

* the CAPTURE fixture is `1. e4 d5 2. Nc3 h6`, and `Nc3xd5` — `Move(73, 54)` — is
  in `gen_moves`' own output there. A KNIGHT capture and not a pawn's, because a
  pawn would enter the pawn block too and this composition swaps ONE gate;
* the CASTLE fixture is `1. e4 e5 2. Nf3 Nf6 3. Be2 Be7`, and `O-O` —
  `Move(95, 97)` — is in `gen_moves`' output there;
* the KP fixture is the position that castle LEAVES, so its `kp = 23` is a number
  the ENGINE computed (`119 - (95 + 97) / 2`). Its move is the only synthetic
  pair in this file, and the reason is a finding: **the king-passant arm fires
  only when the mover attacks the square the opponent's king just crossed**, and
  no move `gen_moves` yields from this position reaches the opponent's back rank.
  That filter is checked below and it is EMPTY. The premises are met and the
  arithmetic agrees; what is not claimed is that this pair is a legal move.

Every `pst` row still comes from the live `initWorld`. -/

/-- One ply of the shipped `Position.move`, threaded through `Option` so a ply
that fails to decide cannot be mistaken for a position. 256 fuel is measured —
64 already decides. -/
private def vlPly (p : Option RVal) (i j : Int) : Option RVal :=
  match p with
  | some p0 =>
    (match callIn sunfish 256 (initWorld sunfish) "Position.move" #[p0, mvOf i j ""] with
     | .ok _ v => some v
     | _ => Option.none)
  | none => Option.none

private def fxOpen : Option RVal := vlPly (vlPly (some (posH 0)) 85 65) 85 65
/-- `1. e4 d5 2. Nc3 h6` — white to move, `Nc3xd5` available. -/
private def fxCap : Option RVal := vlPly (vlPly fxOpen 92 73) 81 71
/-- `1. e4 e5 2. Nf3 Nf6 3. Be2 Be7` — white to move, `O-O` available. -/
private def fxCastle : Option RVal :=
  vlPly (vlPly (vlPly (vlPly fxOpen 97 76) 97 76) 96 85) 96 85
/-- And the position `O-O` leaves, whose `kp` the engine set. -/
private def fxKp : Option RVal := vlPly fxCastle 95 97

/-! **The three boards, written down as a CACHE.** Each is pinned to the plies
above by one `#guard`, so nothing here is a claim about chess — and the reason to
cache at all is measured: a nullary `def` is re-evaluated by every `#guard` that
mentions it, so reading the plies from twenty premise checks costs twenty seconds
where reading a literal costs none. -/

private def capB : String :=
  "         \n         \n rnbqkbnr\n ppp.ppp.\n .......p\n ...p....\n ....P...\n ..N.....\n PPPP.PPP\n R.BQKBNR\n         \n         \n"
private def castleB : String :=
  "         \n         \n r..qkbnr\n pppbpppp\n ..n.....\n ...p....\n ....P...\n .....N..\n PPPPBPPP\n RNBQK..R\n         \n         \n"
private def kpB : String :=
  "\n         \n         \n.kr.qbnr \npppbpppp \n..n..... \n...p.... \n....P... \n.....N.. \nPPPPBPPP \nRNBKQ..R \n         \n         "

private def capPos : RVal := posOf capB 27 true true true true 0 0
private def castlePos : RVal := posOf castleB 0 true true true true 0 0
private def kpPos : RVal := posOf kpB (-48) true true false false 0 23

/-! The pins: the literals ARE what the shipped `Position.move` computes, fields
and all — and being `posOf`-shaped is what every theorem above quantifies over. -/
#guard fxCap == some capPos
#guard fxCastle == some castlePos
#guard fxKp == some kpPos
#guard capB.length == 120 && castleB.length == 120 && kpB.length == 120

private def fxRowOf (c : String) : Option (Array RVal) :=
  match Env.lookup (initWorld sunfish).globals "pst" with
  | some (RVal.ref pa) =>
    (match Heap.get? (initWorld sunfish).heap pa with
     | some (Obj.dict es _) =>
       (match dictFind es.toList (RVal.str c) with
        | some (RVal.tuple xs) => some xs | _ => Option.none)
     | _ => Option.none)
  | _ => Option.none

private def fxEnt (xs : Option (Array RVal)) (n : Nat) : Option Int :=
  match xs with
  | some a => (match a[n]?.getD RVal.none with | RVal.int z => some z | _ => Option.none)
  | none => Option.none

private def fxRow120 (c : String) : Bool :=
  match fxRowOf c with | some xs => xs.size == 120 | _ => false

/-- The engine's own answer for a move scored in a fixture position — and the
heap check, so the instantiation confirms heap-freeness rather than assuming it. -/
private def fxValue (p : RVal) (i j : Int) : Option Int :=
  match callIn sunfish 64 (initWorld sunfish) "Position.value" #[p, mvOf i j ""] with
  | .ok w (RVal.int v) =>
    if w.heap.size == (initWorld sunfish).heap.size then some v else Option.none
  | _ => Option.none

/-! #### The CAPTURE arm at `Nc3xd5` — `Move(73, 54)`

The move is one `gen_moves` PRODUCES from this very position, which is the
premise set's real source: `value_body_capture`'s index and row hypotheses are
exactly what a generated move guarantees. -/
#guard (match genMovesOf 512 capPos with
        | some ms => ms.contains ((73 : Int), (54 : Int), "")
        | none => false)
/-! The moved piece is a knight and the destination holds a black pawn. -/
#guard boardAt capB 73 == "N" && boardAt capB 54 == "p"
#guard strContains "pnbrqk" (boardAt capB 54) == true
#guard (match strUpper (boardAt capB 54) with
        | .ok (RVal.str u) => u == "P" | _ => false)
#guard boardAt capB 73 != "K" && boardAt capB 73 != "P"
/-! `hfar` — the destination is nowhere near the king-passant square, which the
engine left at `0` in this position. -/
#guard (decide ((2 : Int) ≤ 54 - 0) : Bool)
/-! Both rows are present and 120 wide: the mover's and the captured piece's. -/
#guard fxRow120 "N" && fxRow120 "P"
/-! **And the CONCLUSION**: `zj - zi + zc` in the rows' own entries is exactly
what the shipped method answers, heap-free. -/
#guard (match fxEnt (fxRowOf "N") 54, fxEnt (fxRowOf "N") 73, fxEnt (fxRowOf "P") 65,
              fxValue capPos 73 54 with
        | some zj, some zi, some zc, some v => zj - zi + zc == v
        | _, _, _, _ => false)

/-! #### The CASTLE arm at `O-O` — `Move(95, 97)`, also a generated move -/
#guard (match genMovesOf 512 castlePos with
        | some ms => ms.contains ((95 : Int), (97 : Int), "")
        | none => false)
#guard boardAt castleB 95 == "K" && boardAt castleB 97 == "."
#guard strContains "pnbrqk" (boardAt castleB 97) == false
#guard (decide ((2 : Int) ≤ 97 - 0) : Bool)
/-! `hlong`, and the two rook indices the arm computes: the transit square by
FLOOR DIVISION and the corner by the conditional, at `Nat` (law 3). -/
#guard (decide (((95 : Int) - 97 = 2) ∨ ((95 : Int) - 97 = -2)) : Bool)
#guard ((95 + 97 : Int)).fdiv 2 == 96 && (if (97 : Int) < 95 then (91 : Nat) else 98) == 98
#guard fxRow120 "K" && fxRow120 "R"
#guard (match fxEnt (fxRowOf "K") 97, fxEnt (fxRowOf "K") 95, fxEnt (fxRowOf "R") 96,
              fxEnt (fxRowOf "R") 98, fxValue castlePos 95 97 with
        | some zj, some zi, some z1, some z2, some v => zj - zi + z1 - z2 == v
        | _, _, _, _, _ => false)

/-! #### The KP arm, in the position the castle LEFT

`kp = 23` is the engine's own number and the arm's premise `-2 < j - kp < 2` is
met at `j = 24`. The empty filter is the honest half. -/
#guard (match genMovesOf 512 kpPos with
        | some ms => (ms.filter (fun t : Int × Int × String =>
            (t.2.1 - 23).natAbs < 2)).isEmpty
        | none => false)
#guard boardAt kpB 98 == "R" && boardAt kpB 24 == "."
#guard strContains "pnbrqk" (boardAt kpB 24) == false
#guard boardAt kpB 98 != "K" && boardAt kpB 98 != "P"
#guard (decide (-2 < (24 : Int) - 23 ∧ (24 : Int) - 23 < 2) : Bool)
#guard fxRow120 "R" && fxRow120 "K"
#guard (match fxEnt (fxRowOf "R") 24, fxEnt (fxRowOf "R") 98, fxEnt (fxRowOf "K") 95,
              fxValue kpPos 98 24 with
        | some zj, some zi, some zk, some v => zj - zi + zk == v
        | _, _, _, _ => false)

#print axioms vlF_lit
#print axioms vlB_split
#print axioms vlUnpack_lit
#print axioms vlRet_lit
#print axioms vlCallEnv
#print axioms vlArity
#print axioms vlPQ_lit
#print axioms value_reads_pq
#print axioms pstG
#print axioms value_scores
#print axioms vlCap_lit
#print axioms value_cap_skips
#print axioms value_cap_adds
#print axioms vlKp_lit
#print axioms value_kp_skips
#print axioms value_kp_adds
#print axioms vlCastle_lit
#print axioms value_castle_skips
#print axioms value_castle_skips_short
#print axioms a1G
#print axioms h1G
#print axioms value_castles
#print axioms a8G
#print axioms h8G
#print axioms sG
#print axioms vlPawn_lit
#print axioms value_pawn_skips
#print axioms value_pawn_enters
#print axioms vlProm_lit
#print axioms vlEp_lit
#print axioms value_prom_skips
#print axioms value_ep_skips
#print axioms value_unpacks
#print axioms value_returns
#print axioms vlArity2
#print axioms callIn_of_value_body
#print axioms vlB_appends
#print axioms value_body_quiet
#print axioms value_runs_quiet
#print axioms vlProm_body_lit
#print axioms vlEp_body_lit
#print axioms value_prom_adds
#print axioms value_ep_adds
#print axioms vlEnv3_rescore
#print axioms value_body_capture
#print axioms value_body_kp
#print axioms value_body_castle
#print axioms value_runs_capture
#print axioms value_runs_kp
#print axioms value_runs_castle

/-! ## INCH R1 IS CLOSED

`Position.value` decides, heap-free, on **every configuration the method has**:

| configuration | run gate | composition |
|---|---|---|
| quiet | eight skip/plain gates | `value_runs_quiet` |
| capture | `value_cap_adds` | `value_runs_capture` |
| beside the king square | `value_kp_adds` | `value_runs_kp` |
| the castle | `value_castles` | `value_runs_castle` |
| promotion | `value_prom_adds` | *(gate only — see below)* |
| en passant | `value_ep_adds` | *(gate only — see below)* |

Every one of the twelve statement gates is proved, all four compositions are
INSTANTIATED on positions the shipped `Position.move` reached ply by ply, and
two of the four moves are moves the shipped `gen_moves` produces from the
position they are scored in. No table constant is written down anywhere in the
file: every answer is stated in the `pst` row's own entries and every row comes
from the live `initWorld`.

**What is deliberately not here.** The two pawn arms are gated but not composed,
and that is a choice rather than a remainder: `value_pawn_enters` PEELS the block
and the two siblings are independent, so the four pawn combinations — including
the physically impossible promote-and-en-passant one — compose from the gates by
`execStmts_append` without a new statement. Writing four more chains would spell
out what the peel already says. A consumer that needs a pawn move's number takes
the peel and the two sibling gates; nothing is owed to make that possible.

**R1′ still stands unwanted.** Nothing downstream computes a value (§L25), so a
reference function naming the NUMBER is priced and unbuilt. The next inch is
R2a: the ordering genexp's drain, and what it needs from here is exactly the
`∃ t, ∀ F ≥ t` decidability these four theorems give it.

**The laws this file paid for**, in the order they were learned:

1. *The computed-shape law.* `evalExpr` inlines past `indexVal`, `normIndex` and
   `Heap.get?` alike, so a premise stated at a helper cannot match. State it in
   the shape the path leaves, and conclude with the computed term.
2. *Two gates per `if`, not one existential.* Every `if` here guards a `pst`
   lookup whose key the guard is what makes legal, so a single gate carrying the
   row premise unconditionally is UNSATISFIABLE on the common path.
3. *simp normalizes the CONDITION too.* `0 ≤ 119 - j` becomes `j ≤ 119`; a
   trivially-true conjunct is discharged, not kept; `getElem?` collapses to
   `getElem` once the size is known; a conditional index must be stated at `Nat`.
   After the first failed `py_simp`, copy the residue's spelling — do not write
   the premise you believe is equivalent. **The en-passant arm is the sharpest
   case**: the residue keeps `119 - (j + 10)` with the global already folded and
   no arithmetic done, so `109 - j` — the same number — does not match.
4. *An elaborator-accepted, KERNEL-refused proof means a missing ALTITUDE
   lemma*, not a worse premise. `compare_one` is `boolChain_and_falsy` for
   comparisons, and it was owed.
5. *A SKIP arm pins its body existentially; an ADD arm must spell it.* §L19's law
   says pin the shape you compute with, and the two arms of one `if` compute with
   different shapes — so one statement gets two pins and neither is redundant.
   The trap inside the spelled pin is span arithmetic: the promotion body has
   THREE distinct trailing spans (`binOp`, `augAssign`, `ifStmt`), one more than
   it reads at a glance, and a pin short by one fails as a type mismatch on the
   final `rfl` rather than as a shape error.
6. *A chained compare's TRUE arm leaves NESTED `if`s, not a conjunction.*
   `A8 <= j <= H8` closes on two `if_pos`, where its false arm closed on `omega`
   — the same expression, two different residues, because `simp` splits what it
   can decide and leaves what it cannot.
7. *An arm that fires REWRITES the frame slot it already has.* `Env.set_set` is
   in `py_simp`'s default set, so a gate's own proof never sees the tower — but a
   COMPOSITION does, because the gate's statement is literal. One three-line
   bridge (`vlEnv3_rescore`) is what keeps every arm's output frame `vlEnv3`
   instead of a stack of writes, and the castle spends it twice.
8. *A nullary `def` is re-evaluated by every `#guard` that mentions it.* Reading
   the fixture positions straight from the plies cost twenty seconds across
   twenty premise checks; caching each derived board as a literal PINNED to the
   plies by one guard costs none and claims exactly as much.

And one prediction corrected: §L25 expected a conditional expression to ride into
its index term. It does not — it SPLITS the run. -/

end Examples.python.sunfish.value_bound
