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

/-! ## What R1 still owes

**Inch R1 is CLOSED for the quiet move**, which is the configuration the fold
consumes most and the one R2's ordering line needs first: all eight statements
gated, composed through `callIn`, and INSTANTIATED on the shipped fixture — the
premises checked one by one at `Move(92, 71)` and the conclusion's `zj - zi`
checked against CPython's own `5`.

What is left is the three non-quiet configurations, and each is the SAME chain
with one gate swapped:

* **capture** — `value_cap_adds` in place of `value_cap_skips`;
* **beside the king square** — `value_kp_adds` for `value_kp_skips`;
* **the castle** — `value_castles` for `value_castle_skips`.

All three ADD gates are already proved, so these are compositions and not new
work. The two pawn ADD arms (promotion, en passant) are the only gates still
unwritten in this file; both need a sharper pin of their statement with the body
spelled (the current pins leave it existential — right for the skip arms, wrong
for these, §L19's law), and `compare_one` now unblocks their guards.

**The four laws this file paid for**, in the order they were learned:

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
   the premise you believe is equivalent.
4. *An elaborator-accepted, KERNEL-refused proof means a missing ALTITUDE
   lemma*, not a worse premise. `compare_one` is `boolChain_and_falsy` for
   comparisons, and it was owed.

And one prediction corrected: §L25 expected a conditional expression to ride
into its index term. It does not — it SPLITS the run. -/

end Examples.python.sunfish.value_bound
