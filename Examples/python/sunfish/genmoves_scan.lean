/-
**The two SCANS above the ray, and the flagship** — landing L5 of
docs/generator-tier-architecture.md.

`genmoves_ray.lean` finished the ray: every ray `Position.gen_moves` can
enter emits exactly what `Ref.ray` reports, over an arbitrary board, and
hands the frame back (`RayExit`). What is left of the shipped generator is
the two loops ABOVE the ray, and they are not more of the same:

* the **direction scan** `for d in directions[p]` reads a module-global
  DICT — the first heap read on the path that is not a board square — and
  iterates a value tuple, so it is a `forSeq` frame whose body ALLOCATES
  (each ray's `count(i + d, d)` object) before the ray theorem applies;
* the **board scan** `for i, p in enumerate(self.board)` is a `forGen`
  frame over an `<enumerate>` OBJECT (§L4 PARTIAL's correction), it binds a
  TUPLE target, and it carries the tier's first `continue`.

Both scans have to know what a ray did to the WORLD, not just what it
emitted: the direction scan re-reads the dict after every ray and the board
scan holds a live enumerate object across all of them. That is what
`RayExit`'s `SlotOnly` conjunct is for, and `WorldFacts` below is the
predicate the scans actually carry.

The file ends at `gen_moves_yields_ref`: the shipped `Position.gen_moves`,
as a suspended machine over the shipped AST, yields exactly `Ref.refMoves`'
moves in `Ref.refMoves`' order, on an arbitrary board. The one step from
there to `GenMovesEqRef` (genmoves_theorem.lean) is the OBJECT-level drain,
and the closing section of this file records exactly what that costs and
why it is not here.
-/
import Examples.python.sunfish.genmoves_ray

namespace Examples.python.sunfish.genmoves_scan

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.pins_genmoves
open Examples.python.sunfish.genmoves_theorem
open Examples.python.sunfish.genmoves_ray

/-! ## The two scans, projected

Never retyped: the statements come out of `sunfish` exactly as the ray's
did, so a changed PROGRAM stops the `rfl`s loudly. -/

def gmB : List Stmt :=
  match findFunction sunfish "Position.gen_moves" with
  | some f => f.body.toList
  | none => []

/-- `for i, p in enumerate(self.board)` — the whole method body. -/
def bScan : Stmt := nth 0 gmB
/-- The board scan's body: the `continue` guard and the direction scan. -/
def sBody : List Stmt := planForBody bScan
def bTarget : Expr := planForTarget bScan
def bIter : Expr := planForIter bScan
/-- `if p not in "PNBRQK": continue` — the tier's first `continue`. -/
def contS : Stmt := nth 0 sBody
/-- `for d in directions[p]:` — the direction scan. -/
def dScan : Stmt := nth 1 sBody
def dTarget : Expr := planForTarget dScan
def dIter : Expr := planForIter dScan
def dBody : List Stmt := planForBody dScan

theorem gmB_split : gmB = [bScan] := rfl
theorem sBody_split : sBody = [contS, dScan] := rfl
theorem bScan_plan : genPlan bScan = .forHere bTarget bIter sBody := rfl
theorem contS_plan : genPlan contS = .delegate := rfl
theorem dScan_plan : genPlan dScan = .forHere dTarget dIter dBody := rfl
theorem dBody_split : dBody = [gmRayS] := rfl

theorem bTarget_lit : ∃ s1 s2 s3, bTarget =
    .tuple #[.name "i" s1, .name "p" s2] s3 := ⟨_, _, _, rfl⟩

theorem bIter_lit : ∃ s1 s2 s3 s4, bIter =
    .call (.name "enumerate" s1) #[.attribute (.name "self" s2) "board" s3] #[]
      Option.none s4 := ⟨_, _, _, _, rfl⟩

theorem contS_lit : ∃ s1 s2 s3 s4 s5, contS =
    .ifStmt (.compare (.name "p" s1) #[.notIn] #[.constant (.str "PNBRQK") s2] s3)
      #[.cont s4] #[] s5 := ⟨_, _, _, _, _, rfl⟩

theorem dTarget_lit : ∃ s, dTarget = .name "d" s := ⟨_, rfl⟩

theorem dIter_lit : ∃ s1 s2 s3, dIter =
    .subscript (.name "directions" s1) (.name "p" s2) s3 := ⟨_, _, _, rfl⟩

theorem rayIter_lit : ∃ s1 s2 s3 s4 s5 s6, planForIter gmRayS =
    .call (.name "count" s1)
      #[.binOp (.name "i" s2) .add (.name "d" s3) s4, .name "d" s6] #[]
      Option.none s5 := ⟨_, _, _, _, _, _, rfl⟩

/-! ## The rules the scans need, and the ray did not

Two frame rules and one composition, stated module-polymorphically: they
belong beside VCGen.lean §L4's, and they live here only because touching
VCGen re-elaborates the pinned modules. (`enumObj` and the two
`iterSteps_enum…` rules DID move, at L6 — the whole-drain bridge wanted
them, which is the condition this note set for moving them.) -/

/-- **Pushing a `forGen` frame**: `for x in <expression that allocates a
generator>`. The `forHere` twin of `genSilent_forHere` (VCGen §L2) for the
arm that dispatches on the HEAP — the iterable evaluates to a `.ref` at a
generator object, so the frame is a `forGen` and the evaluation is an
`EvalsIn` (it moved the world: the object is new). -/
theorem genSilent_forHereGen {m : Module} {st st₁ : FrameState} {s : Stmt}
    {target iter : Expr} {body ss : List Stmt} {k : GenCont} {ad : Addr}
    {qname : String} {locals : REnv} {cont : GenCont} {status : GenStatus}
    (hplan : genPlan s = .forHere target iter body)
    (hv : EvalsIn m st iter (.ref ad) st₁)
    (hobj : Heap.get? st₁.world.heap ad = some (.generator qname locals cont status)) :
    GenSilent m st (.block (s :: ss) :: k) st₁
      (.forGen target ad body :: .block ss :: k) := by
  obtain ⟨t, ht⟩ := hv
  refine ⟨1, t, fun F hF => ?_⟩
  rw [execGen]
  simp only [hplan, ht F hF, Run.ok_bind, hobj]

/-- **A silent transition that returns to the SAME frame prefix carries the
rest of the loop** — which is what a `continue` round is: the interpreter
stepped the iterator, ran the guard, unwound to the loop frame it started
at, and emitted nothing on the way. -/
theorem genEmits_silentLoop {m : Module} {pre : GenCont} {st st₂ st₃ : FrameState}
    {ws : List RVal} (hs : ∀ k, GenSilent m st (pre ++ k) st₂ (pre ++ k))
    (hrest : GenEmits m st₂ pre ws st₃) : GenEmits m st pre ws st₃ :=
  fun k vs st' hk => GenYields.silent (hs k) (hrest k vs st' hk)

/-! ## The world the scans carry

A ray moves the world (it allocates a `count` object and writes it every
round). What the scans need back is not that nothing moved but that THEIR
three facts survived, and both ways a ray moves the world keep them: an
allocation lands past every live address, and `RayExit`'s `SlotOnly` writes
only the fresh object's own slot. -/

/-- The shipped `directions` dict, PRINTED off the module (the `_lit`
discipline: `#guard`ed against `initWorld sunfish` below, never
hand-transcribed). -/
def dirsObj : Obj := .dict
  #[(.str "P", .tuple #[.int (-10), .int (-20), .int (-11), .int (-9)]),
    (.str "N", .tuple #[.int (-19), .int (-8), .int 12, .int 21, .int 19, .int 8,
      .int (-12), .int (-21)]),
    (.str "B", .tuple #[.int (-9), .int 11, .int 9, .int (-11)]),
    (.str "R", .tuple #[.int (-10), .int 1, .int 10, .int (-1)]),
    (.str "Q", .tuple #[.int (-10), .int 1, .int 10, .int (-1), .int (-9), .int 11,
      .int 9, .int (-11)]),
    (.str "K", .tuple #[.int (-10), .int 1, .int 10, .int (-1), .int (-9), .int 11,
      .int 9, .int (-11)])]
  0

#guard Env.lookup (initWorld sunfish).globals "directions" == some (.ref 63)
#guard Heap.get? (initWorld sunfish).heap 63 == some dirsObj

/-- **What both scans hold about the world**: the module-global
`directions` binding, the dict it points at, and the board scan's own
`<enumerate>` object with its remaining squares. -/
def WorldFacts (dad a : Addr) (i : Int) (xs : List RVal) (w : World) : Prop :=
  Env.lookup w.globals "directions" = some (.ref dad) ∧
  Heap.get? w.heap dad = some dirsObj ∧
  Heap.get? w.heap a = some (enumObj i xs)

theorem WorldFacts.dad_lt {dad a : Addr} {i : Int} {xs : List RVal} {w : World}
    (h : WorldFacts dad a i xs w) : dad < w.heap.size :=
  Heap.lt_size_of_get? h.2.1

theorem WorldFacts.a_lt {dad a : Addr} {i : Int} {xs : List RVal} {w : World}
    (h : WorldFacts dad a i xs w) : a < w.heap.size :=
  Heap.lt_size_of_get? h.2.2

/-- The dict and the enumerate object are different OBJECTS, so they are
different addresses — the disjointness the scan needs is a consequence of
the facts themselves, not an extra hypothesis. -/
theorem WorldFacts.ne {dad a : Addr} {i : Int} {xs : List RVal} {w : World}
    (h : WorldFacts dad a i xs w) : dad ≠ a := by
  intro hh
  have hd := h.2.1
  rw [hh, h.2.2] at hd
  simp [dirsObj, enumObj] at hd

/-- An ALLOCATION preserves them (the fresh address is past both). -/
theorem WorldFacts.push {dad a : Addr} {i : Int} {xs : List RVal} {w : World}
    (h : WorldFacts dad a i xs w) (o : Obj) :
    WorldFacts dad a i xs { w with heap := w.heap.push o } :=
  ⟨h.1, by rw [show ({ w with heap := w.heap.push o } : World).heap = w.heap.push o from rfl,
      Heap.get?_push_lt h.dad_lt]; exact h.2.1,
    by rw [show ({ w with heap := w.heap.push o } : World).heap = w.heap.push o from rfl,
      Heap.get?_push_lt h.a_lt]; exact h.2.2⟩

/-- A RAY preserves them: it wrote one slot, and that slot is neither. -/
theorem WorldFacts.slotOnly {dad a a₁ : Addr} {i : Int} {xs : List RVal} {w w' : World}
    (h : WorldFacts dad a i xs w) (hs : SlotOnly a₁ w w')
    (hd : dad ≠ a₁) (ha : a ≠ a₁) : WorldFacts dad a i xs w' :=
  ⟨by rw [hs.1]; exact h.1, (hs.2 dad hd).trans h.2.1, (hs.2 a ha).trans h.2.2⟩

/-! ## The captured runs

Four, and every one of them is a first: the module-global DICT read, the
two ALLOCATING calls (`count`, `enumerate`), and the `continue` guard. -/

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
/-- **`count(i + d, d)`** — the ray's own generator, allocated. The value
is a `.ref` at the heap's END and the object is `countObj`, so the ray
theorem's `hcount` is `Heap.get?_push_size` at the state this leaves. -/
theorem count_evals (w : World) (env : REnv) (iv dv : Int) (hloc : RayLocals env)
    (hi : Env.lookup env "i" = some (.int iv))
    (hd : Env.lookup env "d" = some (.int dv)) :
    EvalsIn sunfish ⟨w, env⟩ (planForIter gmRayS) (.ref w.heap.size)
      ⟨{ w with heap := w.heap.push (countObj (iv + dv) dv) }, env⟩ := by
  obtain ⟨s1, s2, s3, s4, s5, s6, hlit⟩ := rayIter_lit
  rw [hlit]
  refine EvalsIn.of_eval (fuel := 8) ?_
  py_simp [sunfish, countObj, hloc.miss "count", hi, hd]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
/-- **`enumerate(self.board)`** — the board scan's generator, allocated
over the board's characters as a SNAPSHOT (`strCharVals`), which is what
makes the scan's induction a list induction. -/
theorem enum_evals (w : World) (env : REnv) (b : String) (score ep kp : Int)
    (wc0 wc1 bc0 bc1 : Bool) (hloc : RayLocals env)
    (hself : Env.lookup env "self" = some (posOf b score wc0 wc1 bc0 bc1 ep kp)) :
    EvalsIn sunfish ⟨w, env⟩ bIter (.ref w.heap.size)
      ⟨{ w with heap := w.heap.push (enumObj 0 (strCharVals b)) }, env⟩ := by
  obtain ⟨s1, s2, s3, s4, hlit⟩ := bIter_lit
  rw [hlit]
  refine EvalsIn.of_eval (fuel := 8) ?_
  py_simp [sunfish, posOf, enumObj, hloc.miss "enumerate", hself]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
/-- **`if p not in "PNBRQK": continue`**, both arms at once — the same
`strContains_singleton` collapse as the ray's stop guard, and the reference
side is `Ref.inStr` definitionally. -/
theorem cont_run (w : World) (env : REnv) (p : Char) (bp : Bool)
    (hp : Env.lookup env "p" = some (.str (String.singleton p)))
    (hbp : Ref.inStr p "PNBRQK" = bp) :
    execStmt sunfish 16 ⟨w, env⟩ contS
      = .ok ⟨w, env⟩ (if bp then .next else .cont) := by
  obtain ⟨s1, s2, s3, s4, s5, hlit⟩ := contS_lit
  rw [hlit]
  have h1 : strContains "PNBRQK" (String.singleton p) = bp := by
    rw [strContains_singleton]; exact hbp
  cases bp <;> py_simp [hp, h1]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
/-- **`directions[p]`**, at all six keys — the first module-global HEAP
read on the path. `directions` is a dict LITERAL, so the static globals
table declines it (`g1HeapPure` refuses a ref) and the name resolves
through the LIVE `World.globals`; that is why the world facts are
hypotheses rather than a computation. The residual is packaged the way
`board_read_facts` packages the board's: the `interpUnfolds` delta beats a
`Heap.get?`-headed rewrite, so what goes in is the bound and the element. -/
theorem dirs_evals (w : World) (env : REnv) (dad : Addr) (p : Char)
    (hloc : RayLocals env)
    (hp : Env.lookup env "p" = some (.str (String.singleton p)))
    (hg : Env.lookup w.globals "directions" = some (.ref dad))
    (hobj : Heap.get? w.heap dad = some dirsObj)
    (hmem : p = 'P' ∨ p = 'N' ∨ p = 'B' ∨ p = 'R' ∨ p = 'Q' ∨ p = 'K') :
    EvalsTo sunfish ⟨w, env⟩ dIter
      (.tuple ((Ref.directions p).map (fun d => RVal.int d)).toArray) := by
  obtain ⟨s1, s2, s3, hlit⟩ := dIter_lit
  rw [hlit]
  refine EvalsTo.of_eval (fuel := 8) ?_
  have hlt : dad < Array.size w.heap := Heap.lt_size_of_get? hobj
  have hget : w.heap[dad] = dirsObj := by
    rw [Heap.get?, dif_pos hlt] at hobj; exact Option.some.inj hobj
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
    py_simp [sunfish, dirsObj, Ref.directions, Ref.N, Ref.E, Ref.S, Ref.W,
      hloc.miss "directions", hp, hg, hlt, hget]

/-! ## The two ray shapes the scans need and L4 did not have

`Ref.directions 'P'` has four entries and the promotion test is a property
of the SQUARE, so a pawn's ray comes in eight configurations, not four.
L4 landed six of them; these are the two it did not reach, and both are
real chess: a capture that PROMOTES (the pins' "promotion captures" board),
and a double push whose landing square is on the last row — which can only
happen from a square the double-move guard refuses outright. -/

open Ref in
/-- The reference's capture-and-promote leaf: the guard falls through and
the square is on the last row, so the four promotions come out. -/
theorem rayBody_cap_prom_const (b : List Char) (wc0 wc1 : Bool) (ep kp i j dv : Int)
    (c : Char) (hdv : dv = N + W ∨ dv = N + E)
    (href : at? b j = .ok c) (hopen : inStr c " \nPNBRQK" = false)
    (hgo : ((c == '.') && (j != ep) && decide (1 < (j - kp).natAbs)) = false)
    (hprom : (decide (A8 ≤ j) && decide (j ≤ H8)) = true) :
    ∀ t, rayBody b wc0 wc1 ep kp i 'P' dv j t = .ok (promMoves i j) := by
  intro t
  have h1 : A8 ≤ j ∧ j ≤ H8 := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hprom; exact hprom
  have hgo' : ¬ (c = '.') ∨ ¬ (j ≠ ep) ∨ ¬ (1 < (j - kp).natAbs) := by
    by_cases hdot : c = '.'
    · by_cases hje : j = ep
      · exact Or.inr (Or.inl (fun hh => hh hje))
      · refine Or.inr (Or.inr ?_)
        simp [hdot, hje] at hgo
        omega
    · exact Or.inl hdot
  rcases hdv with rfl | rfl <;> rcases hgo' with h | h | h <;>
    (unfold rayBody pawnBreak
     simp [bind, Except.bind, href, hopen, h1.1, h1.2, h, pure, Except.pure, N, W, E,
       promMoves])

open Ref in
/-- **A PROMOTING capture direction ends the ray in exactly three ways**:
the square is a blocker, the capture guard breaks, or four promotions come
out. `ray_pawn_cap_leaf`'s twin above the last row. -/
theorem ray_pawn_cap_prom_leaf (b : List Char) (wc0 wc1 : Bool) (ep kp i j dv : Int)
    (c : Char) (r : List RefMove) (hdv : dv = N + W ∨ dv = N + E)
    (href : at? b j = .ok c)
    (hprom : (decide (A8 ≤ j) && decide (j ≤ H8)) = true)
    (hbody : ∀ t, rayBody b wc0 wc1 ep kp i 'P' dv j t = .ok r) :
    (inStr c " \nPNBRQK" = true ∧ r = []) ∨
    (inStr c " \nPNBRQK" = false ∧
      ((c == '.') && (j != ep) && decide (1 < (j - kp).natAbs)) = true ∧ r = []) ∨
    (inStr c " \nPNBRQK" = false ∧
      ((c == '.') && (j != ep) && decide (1 < (j - kp).natAbs)) = false ∧
      r = promMoves i j) := by
  by_cases hstop : inStr c " \nPNBRQK" = true
  · exact Or.inl ⟨hstop, Except.ok.inj ((hbody (.ok [])).symm.trans
      (rayBody_stop_const b wc0 wc1 ep kp i 'P' dv j c href hstop (.ok [])))⟩
  · simp only [Bool.not_eq_true] at hstop
    by_cases hbrk : ((c == '.') && (j != ep) && decide (1 < (j - kp).natAbs)) = true
    · exact Or.inr (Or.inl ⟨hstop, hbrk, Except.ok.inj ((hbody (.ok [])).symm.trans
        (rayBody_cap_break_const b wc0 wc1 ep kp i j dv c hdv href hstop hbrk (.ok [])))⟩)
    · simp only [Bool.not_eq_true] at hbrk
      exact Or.inr (Or.inr ⟨hstop, hbrk, Except.ok.inj ((hbody (.ok [])).symm.trans
        (rayBody_cap_prom_const b wc0 wc1 ep kp i j dv c hdv href hstop hbrk hprom
          (.ok [])))⟩)

open Ref in
/-- **A double push from a square the guard refuses reports NOTHING**,
whatever is on the landing square — the three ways it can refuse. -/
theorem ray_pawn_dbl_near_leaf (b : List Char) (wc0 wc1 : Bool) (ep kp i j : Int)
    (c : Char) (r : List RefMove) (href : at? b j = .ok c) (hnear : i < A1 + N)
    (hbody : ∀ t, rayBody b wc0 wc1 ep kp i 'P' (N + N) j t = .ok r) :
    (inStr c " \nPNBRQK" = true ∧ r = []) ∨
    (inStr c " \nPNBRQK" = false ∧ c ≠ '.' ∧ r = []) ∨
    (c = '.' ∧ r = []) := by
  by_cases hstop : inStr c " \nPNBRQK" = true
  · exact Or.inl ⟨hstop, Except.ok.inj ((hbody (.ok [])).symm.trans
      (rayBody_stop_const b wc0 wc1 ep kp i 'P' (N + N) j c href hstop (.ok [])))⟩
  · simp only [Bool.not_eq_true] at hstop
    by_cases hdot : c = '.'
    · subst hdot
      exact Or.inr (Or.inr ⟨rfl, Except.ok.inj ((hbody (.ok [])).symm.trans
        (rayBody_dbl_near_const b wc0 wc1 ep kp i j href hnear (.ok [])))⟩)
    · exact Or.inr (Or.inl ⟨hstop, hdot, Except.ok.inj ((hbody (.ok [])).symm.trans
        (rayBody_dbl_land_const b wc0 wc1 ep kp i j c href hstop hdot (.ok [])))⟩)

/-- **The model side of a capture that PROMOTES**: the pawn block's three
guards fall through on a capture direction and the promotion branch runs —
`pawn_promotes_round` with the diagonal's segments in place of the push's,
and a symbolic landing character instead of `'.'`. -/
theorem pawn_cap_promotes_round (w : World) (env : REnv) (b : String) (dv : Int)
    (score ep kp iv jv : Int) (wc0 wc1 bc0 bc1 : Bool) (c : Char) (a : Addr)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' env)
    (hdv : dv = Ref.N + Ref.W ∨ dv = Ref.N + Ref.E)
    (hd : Env.lookup env "d" = some (.int dv))
    (hj : Env.lookup env "j" = some (.int jv))
    (href : Ref.at? b.toList jv = .ok c)
    (hopen : Ref.inStr c " \nPNBRQK" = false)
    (hgo : ((c == '.') && (jv != ep) && decide (1 < (jv - kp).natAbs)) = false)
    (hprom : (decide (Ref.A8 ≤ jv) && decide (jv ≤ Ref.H8)) = true) :
    ∃ env₂, RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' env₂ ∧
      GenEmits sunfish ⟨w, env⟩ [.block gmRay, .forGen gmRayTarget a gmRay]
        ("NBRQ".toList.map (fun pr => moveVal ⟨iv, jv, pr.toString⟩)) ⟨w, env₂⟩ := by
  obtain ⟨hloc₁, hfr₁, hq₁, hp₁, hi₁, hj₁, hd₁⟩ := pawnQ_facts c hframe hd hj
  obtain ⟨env₂, hfr₂, hj₂, hloop⟩ :=
    prom_loop_emits w (Env.set env "q" (.str (String.singleton c))) b score ep kp iv jv
      wc0 wc1 bc0 bc1 hfr₁ hj₁
  refine ⟨env₂, hfr₂, ?_⟩
  refine q_falls (pre := [GenFrame.forGen gmRayTarget a gmRay])
    w env b score ep kp jv wc0 wc1 bc0 bc1 c hframe.2.1 hj href ?_
  refine stop_falls (pre := [GenFrame.forGen gmRayTarget a gmRay]) w _ c hq₁ hopen ?_
  refine pawn_enters (pre := [GenFrame.forGen gmRayTarget a gmRay]) w _ hp₁ ?_
  refine pB0_falls_diag (pre := [GenFrame.block [rYield, rCrawl, rCastA, rCastH],
    GenFrame.forGen gmRayTarget a gmRay]) w _ dv hloc₁ hdv hd₁ ?_
  refine pB1_falls_diag (pre := [GenFrame.block [rYield, rCrawl, rCastA, rCastH],
    GenFrame.forGen gmRayTarget a gmRay]) w _ dv hloc₁ hdv hd₁ ?_
  refine pB2_falls_cap (pre := [GenFrame.block [rYield, rCrawl, rCastA, rCastH],
    GenFrame.forGen gmRayTarget a gmRay]) w _ b dv score ep kp jv wc0 wc1 bc0 bc1 c
    hloc₁ hdv hfr₁.2.1 hd₁ hj₁ hq₁ hgo ?_
  refine pB3_enters (pre := [GenFrame.block [rYield, rCrawl, rCastA, rCastH],
    GenFrame.forGen gmRayTarget a gmRay]) w _ jv hloc₁ hj₁ hprom ?_
  refine GenEmits.silent
    (pre₁ := [GenFrame.forSeq (planForTarget pProm) (strCharVals "NBRQ") (planForBody pProm),
      GenFrame.block [pPromBrk], GenFrame.block ([] : List Stmt),
      GenFrame.block [rYield, rCrawl, rCastA, rCastH],
      GenFrame.forGen gmRayTarget a gmRay])
    (fun k => by
      simpa using genSilent_forHere (m := sunfish) (s := pProm) (ss := [pPromBrk])
        (k := [GenFrame.block ([] : List Stmt),
          GenFrame.block [rYield, rCrawl, rCastA, rCastH],
          GenFrame.forGen gmRayTarget a gmRay] ++ k)
        pProm_plan (promIter_evals _ _) (IterVals.str "NBRQ")) ?_
  have hbreak : GenEmits sunfish ⟨w, env₂⟩
      [GenFrame.block [pPromBrk], GenFrame.block ([] : List Stmt),
        GenFrame.block [rYield, rCrawl, rCastA, rCastH],
        GenFrame.forGen gmRayTarget a gmRay] [] ⟨w, env₂⟩ :=
    GenEmits.blockBreak (pre := [GenFrame.block ([] : List Stmt),
        GenFrame.block [rYield, rCrawl, rCastA, rCastH],
        GenFrame.forGen gmRayTarget a gmRay]) pPromBrk_plan (fun _ => rfl)
      (run_at_least (promBrk_run ⟨w, env₂⟩))
  simpa using GenEmits.trans hloop hbreak

set_option maxHeartbeats 800000 in
/-- **RAY AGREEMENT FOR A PROMOTING CAPTURE, WHOLE, OVER AN ARBITRARY
BOARD.** -/
theorem ray_pawn_cap_prom_agrees (w : World) (env : REnv) (a : Addr)
    (b : String) (dv : Int) (score ep kp iv : Int) (wc0 wc1 bc0 bc1 : Bool)
    (f : Nat) (jv : Int) (ms : List Ref.RefMove)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' env)
    (hdv : dv = Ref.N + Ref.W ∨ dv = Ref.N + Ref.E)
    (hcount : Heap.get? w.heap a = some (countObj jv dv))
    (hd : Env.lookup env "d" = some (.int dv))
    (hprom : (decide (Ref.A8 ≤ jv) && decide (jv ≤ Ref.H8)) = true)
    (hray : Ref.ray b.toList wc0 wc1 ep kp iv 'P' dv f jv = .ok ms) :
    ∃ st', RayExit b score ep kp iv wc0 wc1 bc0 bc1 'P' a w st' ∧
      GenEmits sunfish ⟨w, env⟩ [.forGen gmRayTarget a gmRay] (ms.map moveVal) st' := by
  refine ray_rounds
    (Inv := fun j st => RayExit b score ep kp iv wc0 wc1 bc0 bc1 'P' a w st ∧
      Heap.get? st.world.heap a = some (countObj j dv) ∧
      Env.lookup st.locals "d" = some (.int dv) ∧
      (decide (Ref.A8 ≤ j) && decide (j ≤ Ref.H8)) = true)
    (Out := RayExit b score ep kp iv wc0 wc1 bc0 bc1 'P' a w)
    ?_ ?_ f jv ms ⟨w, env⟩ ⟨⟨hframe, SlotOnly.refl a w⟩, hcount, hd, hprom⟩ hray
  · rintro j ⟨w₁, env₁⟩ r ⟨⟨hfr, hsl⟩, hcnt, hdd, hpr⟩ hbody
    obtain ⟨h₂, hback⟩ := Heap.update_of_get? (countObj (j + dv) dv) hcnt
    obtain ⟨sj, htgt⟩ := gmRayTarget_lit
    have hfr₁ : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' (Env.set env₁ "j" (.int j)) :=
      hfr.set (x := "j") (by decide) _
    have hj₁ : Env.lookup (Env.set env₁ "j" (.int j)) "j" = some (.int j) :=
      Env.lookup_set_self _ _ _
    have hd₁ : Env.lookup (Env.set env₁ "j" (.int j)) "d" = some (.int dv) := by
      rw [Env.lookup_set_ne _ (by decide)]; exact hdd
    have hat : ∃ c, Ref.at? b.toList j = .ok c := by
      cases hr : Ref.at? b.toList j with
      | ok c => exact ⟨c, rfl⟩
      | error e =>
        exfalso
        have h := hbody (Except.error "unused")
        rw [rayBody] at h
        simp [bind, Except.bind, hr] at h
    obtain ⟨c, href⟩ := hat
    obtain ⟨hstop, rfl⟩ | ⟨hopen, hbrk, rfl⟩ | ⟨hopen, hgo, rfl⟩ :=
      ray_pawn_cap_prom_leaf b.toList wc0 wc1 ep kp iv j dv c r hdv href hpr hbody
    · refine ⟨⟨{ w₁ with heap := h₂ },
          Env.set (Env.set env₁ "j" (.int j)) "q" (.str (String.singleton c))⟩,
        ⟨hfr₁.set (x := "q") (by decide) _, hsl.update hback⟩, ?_⟩
      refine GenEmits.forGenBreak (v := .int j) (w' := { w₁ with heap := h₂ })
        (env₁ := Env.set env₁ "j" (.int j)) (iterSteps_countFrom hcnt hback)
        (by rw [htgt]; rfl) ?_
      obtain ⟨hloc, hself, hi, hp⟩ := hfr₁
      simpa using q_falls (pre := [GenFrame.forGen gmRayTarget a gmRay])
        { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j)) b score ep kp j
        wc0 wc1 bc0 bc1 c hself hj₁ href
        (stop_breaks _ _ c a (Env.lookup_set_self _ _ _) hstop)
    · refine ⟨⟨{ w₁ with heap := h₂ },
          Env.set (Env.set env₁ "j" (.int j)) "q" (.str (String.singleton c))⟩,
        ⟨hfr₁.set (x := "q") (by decide) _, hsl.update hback⟩, ?_⟩
      refine GenEmits.forGenBreak (v := .int j) (w' := { w₁ with heap := h₂ })
        (env₁ := Env.set env₁ "j" (.int j)) (iterSteps_countFrom hcnt hback)
        (by rw [htgt]; rfl) ?_
      simpa using pawn_cap_break_round { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j))
        b dv score ep kp iv j wc0 wc1 bc0 bc1 c a hfr₁ hdv hd₁ hj₁ href hopen hbrk
    · obtain ⟨env₂, hfr₂, hemit⟩ := pawn_cap_promotes_round { w₁ with heap := h₂ }
        (Env.set env₁ "j" (.int j)) b dv score ep kp iv j wc0 wc1 bc0 bc1 c a
        hfr₁ hdv hd₁ hj₁ href hopen hgo hpr
      refine ⟨⟨{ w₁ with heap := h₂ }, env₂⟩, ⟨hfr₂, hsl.update hback⟩, ?_⟩
      refine GenEmits.forGenBreak (v := .int j) (w' := { w₁ with heap := h₂ })
        (env₁ := Env.set env₁ "j" (.int j)) (iterSteps_countFrom hcnt hback)
        (by rw [htgt]; rfl) ?_
      simpa [promMoves, List.map_map] using hemit
  · rintro j st pre _ hmap
    exfalso
    have h := rayBody_pawn_indep b.toList wc0 wc1 ep kp iv dv j
      (Except.ok []) (Except.ok [⟨iv, j, ""⟩])
    rw [hmap (Except.ok []), hmap (Except.ok [⟨iv, j, ""⟩])] at h
    simp only [Functor.map, Except.map] at h
    have h' : pre ++ ([] : List Ref.RefMove) = pre ++ [⟨iv, j, ""⟩] := Except.ok.inj h
    have hl := congrArg List.length h'
    simp at hl

set_option maxHeartbeats 800000 in
/-- **RAY AGREEMENT FOR A DOUBLE PUSH THE GUARD REFUSES, WHOLE, OVER AN
ARBITRARY BOARD.** The configuration `ray_pawn_double_agrees` cannot state:
a landing square on the last row forces `i` onto the sixth rank, where the
double-move guard breaks before the promotion test is ever reached. -/
theorem ray_pawn_double_near_agrees (w : World) (env : REnv) (a : Addr)
    (b : String) (score ep kp iv : Int) (wc0 wc1 bc0 bc1 : Bool)
    (f : Nat) (jv : Int) (ms : List Ref.RefMove)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' env)
    (hcount : Heap.get? w.heap a = some (countObj jv (Ref.N + Ref.N)))
    (hd : Env.lookup env "d" = some (.int (Ref.N + Ref.N)))
    (hnear : iv < Ref.A1 + Ref.N)
    (hray : Ref.ray b.toList wc0 wc1 ep kp iv 'P' (Ref.N + Ref.N) f jv = .ok ms) :
    ∃ st', RayExit b score ep kp iv wc0 wc1 bc0 bc1 'P' a w st' ∧
      GenEmits sunfish ⟨w, env⟩ [.forGen gmRayTarget a gmRay] (ms.map moveVal) st' := by
  refine ray_rounds
    (Inv := fun j st => RayExit b score ep kp iv wc0 wc1 bc0 bc1 'P' a w st ∧
      Heap.get? st.world.heap a = some (countObj j (Ref.N + Ref.N)) ∧
      Env.lookup st.locals "d" = some (.int (Ref.N + Ref.N)))
    (Out := RayExit b score ep kp iv wc0 wc1 bc0 bc1 'P' a w)
    ?_ ?_ f jv ms ⟨w, env⟩ ⟨⟨hframe, SlotOnly.refl a w⟩, hcount, hd⟩ hray
  · rintro j ⟨w₁, env₁⟩ r ⟨⟨hfr, hsl⟩, hcnt, hdd⟩ hbody
    obtain ⟨h₂, hback⟩ :=
      Heap.update_of_get? (countObj (j + (Ref.N + Ref.N)) (Ref.N + Ref.N)) hcnt
    obtain ⟨sj, htgt⟩ := gmRayTarget_lit
    have hfr₁ : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' (Env.set env₁ "j" (.int j)) :=
      hfr.set (x := "j") (by decide) _
    have hj₁ : Env.lookup (Env.set env₁ "j" (.int j)) "j" = some (.int j) :=
      Env.lookup_set_self _ _ _
    have hd₁ : Env.lookup (Env.set env₁ "j" (.int j)) "d"
        = some (.int (Ref.N + Ref.N)) := by
      rw [Env.lookup_set_ne _ (by decide)]; exact hdd
    have hat : ∃ c, Ref.at? b.toList j = .ok c := by
      cases hr : Ref.at? b.toList j with
      | ok c => exact ⟨c, rfl⟩
      | error e =>
        exfalso
        have h := hbody (Except.error "unused")
        rw [rayBody] at h
        simp [bind, Except.bind, hr] at h
    obtain ⟨c, href⟩ := hat
    refine ⟨⟨{ w₁ with heap := h₂ },
        Env.set (Env.set env₁ "j" (.int j)) "q" (.str (String.singleton c))⟩,
      ⟨hfr₁.set (x := "q") (by decide) _, hsl.update hback⟩, ?_⟩
    refine GenEmits.forGenBreak (v := .int j) (w' := { w₁ with heap := h₂ })
      (env₁ := Env.set env₁ "j" (.int j)) (iterSteps_countFrom hcnt hback)
      (by rw [htgt]; rfl) ?_
    obtain ⟨hstop, rfl⟩ | ⟨hopen, hne, rfl⟩ | ⟨rfl, rfl⟩ :=
      ray_pawn_dbl_near_leaf b.toList wc0 wc1 ep kp iv j c r href hnear hbody
    · obtain ⟨hloc, hself, hi, hp⟩ := hfr₁
      simpa using q_falls (pre := [GenFrame.forGen gmRayTarget a gmRay])
        { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j)) b score ep kp j
        wc0 wc1 bc0 bc1 c hself hj₁ href
        (stop_breaks _ _ c a (Env.lookup_set_self _ _ _) hstop)
    · simpa using pawn_dbl_land_round { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j))
        b score ep kp iv j wc0 wc1 bc0 bc1 c a hfr₁ hd₁ hj₁ href hopen hne
    · simpa using pawn_dbl_near_round { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j))
        b score ep kp iv j wc0 wc1 bc0 bc1 a hfr₁ hd₁ hj₁ href hnear
  · rintro j st pre _ hmap
    exfalso
    have h := rayBody_pawn_indep b.toList wc0 wc1 ep kp iv (Ref.N + Ref.N) j
      (Except.ok []) (Except.ok [⟨iv, j, ""⟩])
    rw [hmap (Except.ok []), hmap (Except.ok [⟨iv, j, ""⟩])] at h
    simp only [Functor.map, Except.map] at h
    have h' : pre ++ ([] : List Ref.RefMove) = pre ++ [⟨iv, j, ""⟩] := Except.ok.inj h
    have hl := congrArg List.length h'
    simp at hl

/-! ## Every ray a piece can take, in ONE statement

The direction scan holds a `p` and a `d` it knows nothing about beyond
`d ∈ directions[p]`, so what it needs is not nine ray theorems but one.
This is the dispatch, and its case analysis is the shipped loop's own: six
pieces, and for a pawn four directions each split by whether the landing
square is on the last row. -/

/-- The three sliders, corners included: which of the three slider
theorems applies is decided by the square, not by the piece. -/
theorem ray_slider_agrees (w : World) (env : REnv) (a : Addr)
    (b : String) (score ep kp iv dv : Int) (wc0 wc1 bc0 bc1 : Bool) (p : Char)
    (f : Nat) (jv : Int) (ms : List Ref.RefMove)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p env)
    (hcount : Heap.get? w.heap a = some (countObj jv dv))
    (hnp : p ≠ 'P') (hslide : Ref.inStr p "PNK" = false)
    (hray : Ref.ray b.toList wc0 wc1 ep kp iv p dv f jv = .ok ms) :
    ∃ st', RayExit b score ep kp iv wc0 wc1 bc0 bc1 p a w st' ∧
      GenEmits sunfish ⟨w, env⟩ [.forGen gmRayTarget a gmRay] (ms.map moveVal) st' := by
  by_cases hA : iv = Ref.A1
  · subst hA
    exact ray_castA_agrees w env a b score ep kp dv wc0 wc1 bc0 bc1 p f jv ms
      hframe hcount hnp hslide hray
  · by_cases hH : iv = Ref.H1
    · subst hH
      exact ray_castH_agrees w env a b score ep kp dv wc0 wc1 bc0 bc1 p f jv ms
        hframe hcount hnp hslide hray
    · exact ray_slide_agrees w env a b score ep kp iv dv wc0 wc1 bc0 bc1 p f jv ms
        hframe hcount hnp hslide hA hH hray

set_option maxHeartbeats 800000 in
/-- **RAY AGREEMENT, DISPATCHED.** For any of our pieces and any direction
of its own, the ray from `i + d` emits exactly `Ref.ray`'s moves and hands
the frame and the world back. -/
theorem ray_agrees (w : World) (env : REnv) (a : Addr)
    (b : String) (score ep kp iv dv : Int) (wc0 wc1 bc0 bc1 : Bool) (p : Char)
    (f : Nat) (ms : List Ref.RefMove)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p env)
    (hd : Env.lookup env "d" = some (.int dv))
    (hcount : Heap.get? w.heap a = some (countObj (iv + dv) dv))
    (hp : Ref.inStr p "PNBRQK" = true)
    (hdir : dv ∈ Ref.directions p)
    (hray : Ref.ray b.toList wc0 wc1 ep kp iv p dv f (iv + dv) = .ok ms) :
    ∃ st', RayExit b score ep kp iv wc0 wc1 bc0 bc1 p a w st' ∧
      GenEmits sunfish ⟨w, env⟩ [.forGen gmRayTarget a gmRay] (ms.map moveVal) st' := by
  have hcases : p = 'P' ∨ p = 'N' ∨ p = 'B' ∨ p = 'R' ∨ p = 'Q' ∨ p = 'K' := by
    rw [Ref.inStr, show "PNBRQK".toList = ['P', 'N', 'B', 'R', 'Q', 'K'] from by decide] at hp
    simpa using hp
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  -- the PAWN: four directions, each split by the promotion test
  · have hdd : dv = Ref.N ∨ dv = Ref.N + Ref.N ∨ dv = Ref.N + Ref.W ∨ dv = Ref.N + Ref.E := by
      simpa [Ref.directions] using hdir
    by_cases hprom : (decide (Ref.A8 ≤ iv + dv) && decide (iv + dv ≤ Ref.H8)) = true
    · rcases hdd with rfl | rfl | rfl | rfl
      · exact ray_pawn_prom_agrees w env a b score ep kp iv wc0 wc1 bc0 bc1 f (iv + Ref.N)
          ms hframe hcount hd hprom hray
      · refine ray_pawn_double_near_agrees w env a b score ep kp iv wc0 wc1 bc0 bc1 f
          (iv + (Ref.N + Ref.N)) ms hframe hcount hd ?_ hray
        have h1 : Ref.A8 ≤ iv + (Ref.N + Ref.N) ∧ iv + (Ref.N + Ref.N) ≤ Ref.H8 := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hprom; exact hprom
        simp only [Ref.A8, Ref.H8, Ref.N, Ref.A1] at h1 ⊢
        omega
      · exact ray_pawn_cap_prom_agrees w env a b (Ref.N + Ref.W) score ep kp iv
          wc0 wc1 bc0 bc1 f (iv + (Ref.N + Ref.W)) ms hframe (Or.inl rfl) hcount hd
          hprom hray
      · exact ray_pawn_cap_prom_agrees w env a b (Ref.N + Ref.E) score ep kp iv
          wc0 wc1 bc0 bc1 f (iv + (Ref.N + Ref.E)) ms hframe (Or.inr rfl) hcount hd
          hprom hray
    · simp only [Bool.not_eq_true] at hprom
      rcases hdd with rfl | rfl | rfl | rfl
      · exact ray_pawn_push_agrees w env a b score ep kp iv wc0 wc1 bc0 bc1 f
          (iv + Ref.N) ms hframe hcount hd hprom hray
      · exact ray_pawn_double_agrees w env a b score ep kp iv wc0 wc1 bc0 bc1 f
          (iv + (Ref.N + Ref.N)) ms hframe hcount hd hprom hray
      · exact ray_pawn_capture_agrees w env a b (Ref.N + Ref.W) score ep kp iv
          wc0 wc1 bc0 bc1 f (iv + (Ref.N + Ref.W)) ms hframe (Or.inl rfl) hcount hd
          hprom hray
      · exact ray_pawn_capture_agrees w env a b (Ref.N + Ref.E) score ep kp iv
          wc0 wc1 bc0 bc1 f (iv + (Ref.N + Ref.E)) ms hframe (Or.inr rfl) hcount hd
          hprom hray
  -- the KNIGHT, a crawler
  · exact ray_crawl_agrees w env a b score ep kp iv dv wc0 wc1 bc0 bc1 'N' f (iv + dv)
      ms hframe hcount (by decide) (by decide) hray
  -- the BISHOP, ROOK and QUEEN slide; the corners are the slider theorem's own split
  · exact ray_slider_agrees w env a b score ep kp iv dv wc0 wc1 bc0 bc1 'B' f (iv + dv)
      ms hframe hcount (by decide) (by decide) hray
  · exact ray_slider_agrees w env a b score ep kp iv dv wc0 wc1 bc0 bc1 'R' f (iv + dv)
      ms hframe hcount (by decide) (by decide) hray
  · exact ray_slider_agrees w env a b score ep kp iv dv wc0 wc1 bc0 bc1 'Q' f (iv + dv)
      ms hframe hcount (by decide) (by decide) hray
  -- the KING, a crawler
  · exact ray_crawl_agrees w env a b score ep kp iv dv wc0 wc1 bc0 bc1 'K' f (iv + dv)
      ms hframe hcount (by decide) (by decide) hray

/-! ## The DIRECTION scan

`for d in directions[p]` over a value TUPLE, so the frame is a `forSeq` and
the induction is `GenEmits.forSeq`'s — except that the per-element output
is not a function of the element: it is what the REFERENCE answered for
that direction, and those answers arrive together as one `mapM`. The scan
therefore runs its own induction over the direction list and the answer
list at once, exactly as `ray_rounds` runs over the reference's fuel. -/

theorem gmRayS_plan : genPlan gmRayS = .forHere gmRayTarget (planForIter gmRayS) gmRay :=
  rfl

theorem dTarget_assign (h : Heap) (env : REnv) (v : RVal) :
    assignToH h env dTarget v = .ok (Env.set env "d" v) := by
  obtain ⟨s, hlit⟩ := dTarget_lit
  rw [hlit]; rfl

theorem bTarget_assign (h : Heap) (env : REnv) (v₁ v₂ : RVal) :
    assignToH h env bTarget (.tuple #[v₁, v₂])
      = .ok (Env.set (Env.set env "i" v₁) "p" v₂) := by
  obtain ⟨s1, s2, s3, hlit⟩ := bTarget_lit
  rw [hlit]; rfl

/-- **One direction, whole**: the ray's `count` object is allocated, the
`forGen` frame goes on, the ray runs, and the empty remainder of the
direction body pops. The world the scan cares about comes back untouched —
the allocation landed past its slots and the ray wrote only its own. -/
theorem dir_body_emits (w : World) (env : REnv) (dad a₂ : Addr) (ib : Int)
    (xs : List RVal) (b : String) (score ep kp iv dv : Int)
    (wc0 wc1 bc0 bc1 : Bool) (p : Char) (f : Nat) (ms : List Ref.RefMove)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p env)
    (hwf : WorldFacts dad a₂ ib xs w)
    (hd : Env.lookup env "d" = some (.int dv))
    (hp : Ref.inStr p "PNBRQK" = true)
    (hdir : dv ∈ Ref.directions p)
    (hray : Ref.ray b.toList wc0 wc1 ep kp iv p dv f (iv + dv) = .ok ms) :
    ∃ st', (RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p st'.locals ∧
        WorldFacts dad a₂ ib xs st'.world) ∧
      GenEmits sunfish ⟨w, env⟩ [.block dBody] (ms.map moveVal) st' := by
  have hpush : WorldFacts dad a₂ ib xs
      { w with heap := w.heap.push (countObj (iv + dv) dv) } := hwf.push _
  have hcount : Heap.get?
      ({ w with heap := w.heap.push (countObj (iv + dv) dv) } : World).heap w.heap.size
      = some (countObj (iv + dv) dv) := Heap.get?_push_size _ _
  obtain ⟨st', ⟨hfr', hsl'⟩, hem⟩ := ray_agrees
    { w with heap := w.heap.push (countObj (iv + dv) dv) } env w.heap.size b score ep kp
    iv dv wc0 wc1 bc0 bc1 p f ms hframe hd hcount hp hdir hray
  refine ⟨st', ⟨hfr', hpush.slotOnly hsl' (Nat.ne_of_lt hwf.dad_lt) (Nat.ne_of_lt hwf.a_lt)⟩, ?_⟩
  refine GenEmits.silent
    (pre₁ := [GenFrame.forGen gmRayTarget w.heap.size gmRay,
      GenFrame.block ([] : List Stmt)])
    (fun k => by
      simpa [dBody_split] using genSilent_forHereGen (m := sunfish) (s := gmRayS)
        (ss := ([] : List Stmt)) (k := k) gmRayS_plan
        (count_evals w env iv dv hframe.1 hframe.2.2.1 hd) hcount) ?_
  simpa using GenEmits.trans hem (block_done st')

/-- **THE DIRECTION SCAN.** Direction by direction, the `forSeq` frame
emits exactly what `Ref.piece`'s `mapM` collected, and the frame and the
world facts survive every ray. -/
theorem dir_scan (dad a₂ : Addr) (ib : Int) (xs : List RVal)
    (b : String) (score ep kp iv : Int) (wc0 wc1 bc0 bc1 : Bool) (p : Char) (f : Nat)
    (hp : Ref.inStr p "PNBRQK" = true) :
    ∀ (ds : List Int) (rss : List (List Ref.RefMove)) (st : FrameState),
      (∀ d ∈ ds, d ∈ Ref.directions p) →
      ds.mapM (fun d => Ref.ray b.toList wc0 wc1 ep kp iv p d f (iv + d)) = .ok rss →
      (RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p st.locals ∧
        WorldFacts dad a₂ ib xs st.world) →
      ∃ st', (RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p st'.locals ∧
          WorldFacts dad a₂ ib xs st'.world) ∧
        GenEmits sunfish st [.forSeq dTarget (ds.map (fun d => RVal.int d)) dBody]
          (rss.flatten.map moveVal) st' := by
  intro ds
  induction ds with
  | nil =>
    intro rss st _ hm hinv
    obtain rfl : rss = [] := by simpa [pure, Except.pure] using hm.symm
    refine ⟨st, hinv, ?_⟩
    simpa using GenEmits.silent (pre₁ := ([] : GenCont))
      (fun k => by simpa using genSilent_forSeqNil) GenEmits.nil
  | cons d rest ih =>
    intro rss st hmem hm hinv
    obtain ⟨r, hr, rss', hrest, rfl⟩ : ∃ r, Ref.ray b.toList wc0 wc1 ep kp iv p d f (iv + d)
        = .ok r ∧ ∃ rss', rest.mapM (fun d => Ref.ray b.toList wc0 wc1 ep kp iv p d f (iv + d))
        = .ok rss' ∧ rss = r :: rss' := by
      rw [List.mapM_cons] at hm
      obtain ⟨r, hr, hm⟩ := exceptBind_ok.mp hm
      obtain ⟨rss', hrss', hm⟩ := exceptBind_ok.mp hm
      exact ⟨r, hr, rss', hrss', by simpa [pure, Except.pure] using hm.symm⟩
    obtain ⟨hfr, hwf⟩ := hinv
    have hfr₁ : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p (Env.set st.locals "d" (.int d)) :=
      hfr.set (x := "d") (by decide) _
    obtain ⟨st₂, ⟨hfr₂, hwf₂⟩, hbody⟩ := dir_body_emits st.world (Env.set st.locals "d" (.int d))
      dad a₂ ib xs b score ep kp iv d wc0 wc1 bc0 bc1 p f r hfr₁ hwf
      (Env.lookup_set_self _ _ _) hp (hmem d (by simp)) hr
    obtain ⟨st₃, hinv₃, hloop⟩ := ih rss' st₂ (fun x hx => hmem x (by simp [hx])) hrest ⟨hfr₂, hwf₂⟩
    refine ⟨st₃, hinv₃, ?_⟩
    have hcomp : GenEmits sunfish { st with locals := Env.set st.locals "d" (.int d) }
        ([.block dBody] ++ [.forSeq dTarget (rest.map (fun d => RVal.int d)) dBody])
        (r.map moveVal ++ (rss'.flatten).map moveVal) st₃ := GenEmits.trans hbody hloop
    have := GenEmits.silent
      (pre := [GenFrame.forSeq dTarget ((d :: rest).map (fun d => RVal.int d)) dBody])
      (pre₁ := [GenFrame.block dBody,
        GenFrame.forSeq dTarget (rest.map (fun d => RVal.int d)) dBody])
      (fun k => by
        simpa using genSilent_forSeqCons (m := sunfish) (k := k) (dTarget_assign _ _ _))
      hcomp
    simpa [List.map_append] using this

/-- **SQUARE AGREEMENT** — one of our pieces, all of its rays: the shipped
generator emits exactly `Ref.piece`'s moves, in `directions[p]` order. -/
theorem piece_agrees (w : World) (env : REnv) (dad a₂ : Addr) (ib : Int) (xs : List RVal)
    (b : String) (score ep kp iv : Int) (wc0 wc1 bc0 bc1 : Bool) (p : Char) (f : Nat)
    (ms : List Ref.RefMove)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p env)
    (hwf : WorldFacts dad a₂ ib xs w)
    (hp : Ref.inStr p "PNBRQK" = true)
    (hpiece : Ref.piece b.toList wc0 wc1 ep kp f iv p = .ok ms) :
    ∃ st', (RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p st'.locals ∧
        WorldFacts dad a₂ ib xs st'.world) ∧
      GenEmits sunfish ⟨w, env⟩ [.block [dScan]] (ms.map moveVal) st' := by
  obtain ⟨rss, hmapM, rfl⟩ := exceptMap_ok.mp hpiece
  have hcases : p = 'P' ∨ p = 'N' ∨ p = 'B' ∨ p = 'R' ∨ p = 'Q' ∨ p = 'K' := by
    rw [Ref.inStr, show "PNBRQK".toList = ['P', 'N', 'B', 'R', 'Q', 'K'] from by decide] at hp
    simpa using hp
  obtain ⟨st', hinv, hloop⟩ := dir_scan dad a₂ ib xs b score ep kp iv wc0 wc1 bc0 bc1 p f
    hp (Ref.directions p) rss ⟨w, env⟩ (fun _ hx => hx) hmapM ⟨hframe, hwf⟩
  refine ⟨st', hinv, ?_⟩
  refine GenEmits.silent
    (pre₁ := [GenFrame.forSeq dTarget ((Ref.directions p).map (fun d => RVal.int d)) dBody,
      GenFrame.block ([] : List Stmt)])
    (fun k => by
      simpa using genSilent_forHere (m := sunfish) (s := dScan)
        (ss := ([] : List Stmt)) (k := k) dScan_plan
        (dirs_evals w env dad p hframe.1 hframe.2.2.2 hwf.1 hwf.2.1 hcases)
        (IterVals.tuple _)) ?_
  simpa using GenEmits.trans hloop (block_done st')

/-! ## The BOARD scan

`for i, p in enumerate(self.board)` — a `forGen` frame over the
`<enumerate>` OBJECT, a TUPLE target, and the tier's first `continue`.

The reference scans `List.range b.length` and reads `b[i]?` at each index;
the model holds the character list itself as the object's snapshot. The two
meet through `refScan`, which is the reference re-indexed off the list, so
the model's induction is an ordinary list induction and the re-indexing is
one pure lemma with no interpreter in it. -/

/-- The reference's answer at one square, exactly as `Ref.refMoves` spells
it. -/
def refSq (b : List Char) (wc0 wc1 : Bool) (ep kp : Int) (fuel : Nat) (i : Nat) :
    Except String (List Ref.RefMove) :=
  match b[i]? with
  | some p =>
    if Ref.inStr p "PNBRQK" then Ref.piece b wc0 wc1 ep kp fuel (i : Int) p else pure []
  | none => pure []

/-- The same scan, driven by the CHARACTER LIST instead of an index range —
the shape the model's `enumerate` snapshot has. -/
def refScan (b : List Char) (wc0 wc1 : Bool) (ep kp : Int) (fuel : Nat) :
    Nat → List Char → Except String (List (List Ref.RefMove))
  | _, [] => .ok []
  | i, c :: cs => do
    let here ←
      if Ref.inStr c "PNBRQK" then Ref.piece b wc0 wc1 ep kp fuel (i : Int) c else pure []
    let rest ← refScan b wc0 wc1 ep kp fuel (i + 1) cs
    return here :: rest

theorem refScan_eq (b : List Char) (wc0 wc1 : Bool) (ep kp : Int) (fuel : Nat) :
    ∀ (cs : List Char) (i₀ : Nat), b.drop i₀ = cs →
      (List.range' i₀ cs.length).mapM (refSq b wc0 wc1 ep kp fuel)
        = refScan b wc0 wc1 ep kp fuel i₀ cs := by
  intro cs
  induction cs with
  | nil => intro i₀ _; rfl
  | cons c cs ih =>
    intro i₀ hdrop
    have hget : b[i₀]? = some c := by
      have h : (b.drop i₀).head? = b[i₀]? := List.head?_drop
      rw [hdrop] at h
      simpa using h.symm
    have hdrop' : b.drop (i₀ + 1) = cs := by
      have hd1 : b.drop (i₀ + 1) = (b.drop i₀).drop 1 := by
        rw [List.drop_drop]
      rw [hd1, hdrop]; rfl
    rw [show (c :: cs).length = cs.length + 1 from rfl, List.range'_succ, List.mapM_cons,
      ih (i₀ + 1) hdrop']
    simp only [refScan, refSq, hget]
    split <;> rfl

theorem refMoves_eq_refScan (b : List Char) (wc0 wc1 : Bool) (ep kp : Int) (fuel : Nat) :
    Ref.refMoves b wc0 wc1 ep kp fuel
      = List.flatten <$> refScan b wc0 wc1 ep kp fuel 0 b := by
  have h0 : Ref.refMoves b wc0 wc1 ep kp fuel
      = List.flatten <$> (List.range b.length).mapM (refSq b wc0 wc1 ep kp fuel) := rfl
  rw [h0, show List.range b.length = List.range' 0 b.length from by
      simp [List.range_eq_range'], refScan_eq b wc0 wc1 ep kp fuel b 0 (by simp)]

/-- **What the board scan holds between squares**: the method's own frame
(`self` bound, nothing shadowed) and the three world facts. `i` and `p` are
NOT here — they are rebound by every round, which is exactly why the ray's
`RayFrame` is built fresh at each square. -/
def BoardFrame (b : String) (score ep kp : Int) (wc0 wc1 bc0 bc1 : Bool)
    (dad a₂ : Addr) (i : Int) (xs : List RVal) (st : FrameState) : Prop :=
  RayLocals st.locals ∧
  Env.lookup st.locals "self" = some (posOf b score wc0 wc1 bc0 bc1 ep kp) ∧
  WorldFacts dad a₂ i xs st.world

/-- **THE BOARD SCAN.** Square by square — skipping every square that does
not hold one of ours, running every ray of every square that does — the
generator emits exactly what the reference's per-square answers flatten to.

The induction is over the enumerate object's REMAINING snapshot, which is
the board's character list; the reference rides along as `refScan` at the
same index. Nothing in it is an induction over the generator: the object's
own exhaustion is what ends it (`GenEmits.forGenDone`, unreachable on a
ray, reachable here). -/
theorem board_scan (dad a₂ : Addr) (b : String) (score ep kp : Int)
    (wc0 wc1 bc0 bc1 : Bool) (f : Nat) :
    ∀ (cs : List Char) (i₀ : Nat) (rss : List (List Ref.RefMove)) (st : FrameState),
      refScan b.toList wc0 wc1 ep kp f i₀ cs = .ok rss →
      BoardFrame b score ep kp wc0 wc1 bc0 bc1 dad a₂ (i₀ : Int)
        (cs.map (fun c => RVal.str (String.singleton c))) st →
      ∃ st', GenEmits sunfish st [.forGen bTarget a₂ sBody]
        ((rss.flatten).map moveVal) st' := by
  intro cs
  induction cs with
  | nil =>
    intro i₀ rss st hscan ⟨hloc, hself, hwf⟩
    obtain rfl : rss = [] := by rw [refScan] at hscan; exact (Except.ok.inj hscan).symm
    obtain ⟨h₂, hback⟩ := Heap.update_of_get?
      (.generator "<enumerate>" [] [] .closed) hwf.2.2
    exact ⟨⟨{ st.world with heap := h₂ }, st.locals⟩, by
      simpa using GenEmits.forGenDone (target := bTarget) (body := sBody)
        (iterSteps_enumDone (by simpa using hwf.2.2) hback)⟩
  | cons c cs ih =>
    intro i₀ rss st hscan ⟨hloc, hself, hwf⟩
    rw [refScan] at hscan
    -- the object hands over `(i₀, c)` and advances
    obtain ⟨h₂, hback⟩ := Heap.update_of_get?
      (enumObj ((i₀ : Int) + 1) (cs.map (fun c => RVal.str (String.singleton c)))) hwf.2.2
    have hiter : IterSteps sunfish st.world a₂
        (some (.tuple #[.int (i₀ : Int), .str (String.singleton c)]))
        { st.world with heap := h₂ } :=
      iterSteps_enumSeq (by simpa using hwf.2.2) (by simpa using hback)
    have hwf₂ : WorldFacts dad a₂ ((i₀ : Int) + 1)
        (cs.map (fun c => RVal.str (String.singleton c))) { st.world with heap := h₂ } :=
      ⟨hwf.1, (Heap.get?_update_ne hback hwf.ne).trans hwf.2.1, heap_readback hback⟩
    -- the tuple target binds the square and the piece
    have hasg : assignToH ({ st.world with heap := h₂ } : World).heap st.locals bTarget
        (.tuple #[.int (i₀ : Int), .str (String.singleton c)])
        = .ok (Env.set (Env.set st.locals "i" (.int (i₀ : Int)))
            "p" (.str (String.singleton c))) := bTarget_assign _ _ _ _
    have hloc₁ : RayLocals (Env.set (Env.set st.locals "i" (.int (i₀ : Int)))
        "p" (.str (String.singleton c))) := (hloc.set (x := "i") (by decide) _).set
          (x := "p") (by decide) _
    have hself₁ : Env.lookup (Env.set (Env.set st.locals "i" (.int (i₀ : Int)))
        "p" (.str (String.singleton c))) "self"
        = some (posOf b score wc0 wc1 bc0 bc1 ep kp) := by
      rw [Env.lookup_set_ne _ (by decide), Env.lookup_set_ne _ (by decide)]; exact hself
    have hframe₁ : RayFrame b score ep kp (i₀ : Int) wc0 wc1 bc0 bc1 c
        (Env.set (Env.set st.locals "i" (.int (i₀ : Int)))
          "p" (.str (String.singleton c))) :=
      ⟨hloc₁, hself₁, by rw [Env.lookup_set_ne _ (by decide)]; exact Env.lookup_set_self _ _ _,
        Env.lookup_set_self _ _ _⟩
    by_cases hpc : Ref.inStr c "PNBRQK" = true
    · -- OUR PIECE: the guard falls through and every ray of this square runs
      rw [if_pos hpc] at hscan
      obtain ⟨here, hhere, hscan⟩ := exceptBind_ok.mp hscan
      obtain ⟨rest, hrest, hfin⟩ := exceptBind_ok.mp hscan
      obtain rfl : rss = here :: rest := by simpa [pure, Except.pure] using hfin.symm
      obtain ⟨st₂, ⟨hfr₂, hwf₃⟩, hpiece⟩ := piece_agrees { st.world with heap := h₂ }
        (Env.set (Env.set st.locals "i" (.int (i₀ : Int))) "p" (.str (String.singleton c)))
        dad a₂ ((i₀ : Int) + 1) (cs.map (fun c => RVal.str (String.singleton c)))
        b score ep kp (i₀ : Int) wc0 wc1 bc0 bc1 c f here hframe₁ hwf₂ hpc hhere
      obtain ⟨st₃, htail⟩ := ih (i₀ + 1) rest st₂ hrest
        ⟨hfr₂.1, hfr₂.2.1, by
          have : ((i₀ + 1 : Nat) : Int) = (i₀ : Int) + 1 := by omega
          rw [this]; exact hwf₃⟩
      refine ⟨st₃, ?_⟩
      have hbody : GenEmits sunfish ⟨{ st.world with heap := h₂ },
          Env.set (Env.set st.locals "i" (.int (i₀ : Int)))
            "p" (.str (String.singleton c))⟩
          [.block sBody] (here.map moveVal) st₂ := by
        refine GenEmits.silent (pre₁ := [GenFrame.block [dScan]]) (fun k => by
          simpa [sBody_split] using genSilent_delegate (m := sunfish) (s := contS)
            (ss := [dScan]) (k := k) contS_plan
            (run_at_least (by
              simpa [hpc] using cont_run { st.world with heap := h₂ } _ c true
                (Env.lookup_set_self _ _ _) hpc))) hpiece
      simpa [List.map_append] using
        GenEmits.forGenRound (target := bTarget) (body := sBody) hiter hasg hbody htail
    · -- NOT OURS: the `continue` ends the round, the loop frame stays
      simp only [Bool.not_eq_true] at hpc
      rw [if_neg (by simp [hpc])] at hscan
      obtain ⟨here, hhere, hscan⟩ := exceptBind_ok.mp hscan
      obtain rfl : here = ([] : List Ref.RefMove) := by
        simpa [pure, Except.pure] using hhere.symm
      obtain ⟨rest, hrest, hfin⟩ := exceptBind_ok.mp hscan
      obtain rfl : rss = [] :: rest := by simpa [pure, Except.pure] using hfin.symm
      obtain ⟨st₃, htail⟩ := ih (i₀ + 1) rest
        ⟨{ st.world with heap := h₂ }, Env.set (Env.set st.locals "i" (.int (i₀ : Int)))
          "p" (.str (String.singleton c))⟩ hrest
        ⟨hloc₁, hself₁, by
          have : ((i₀ + 1 : Nat) : Int) = (i₀ : Int) + 1 := by omega
          rw [this]; exact hwf₂⟩
      refine ⟨st₃, ?_⟩
      have hpush : ∀ k, GenSilent sunfish st ([GenFrame.forGen bTarget a₂ sBody] ++ k)
          ⟨{ st.world with heap := h₂ }, Env.set (Env.set st.locals "i" (.int (i₀ : Int)))
            "p" (.str (String.singleton c))⟩
          (GenFrame.block sBody :: ([GenFrame.forGen bTarget a₂ sBody] ++ k)) := by
        intro k
        simpa using
          genSilent_forGenCons (m := sunfish) (target := bTarget) (body := sBody)
            (k := k) hiter hasg
      have hcont : ∀ k, GenSilent sunfish
          ⟨{ st.world with heap := h₂ }, Env.set (Env.set st.locals "i" (.int (i₀ : Int)))
            "p" (.str (String.singleton c))⟩
          (GenFrame.block sBody :: ([GenFrame.forGen bTarget a₂ sBody] ++ k))
          ⟨{ st.world with heap := h₂ }, Env.set (Env.set st.locals "i" (.int (i₀ : Int)))
            "p" (.str (String.singleton c))⟩ ([GenFrame.forGen bTarget a₂ sBody] ++ k) := by
        intro k
        have hrun := cont_run { st.world with heap := h₂ }
          (Env.set (Env.set st.locals "i" (.int (i₀ : Int)))
            "p" (.str (String.singleton c))) c false (Env.lookup_set_self _ _ _) hpc
        simpa [sBody_split] using
          genSilent_delegateContinue (m := sunfish) (s := contS) (ss := [dScan])
            (pre := [GenFrame.forGen bTarget a₂ sBody])
            (pre₁ := [GenFrame.forGen bTarget a₂ sBody]) (k := k) contS_plan rfl
            (run_at_least (by simpa using hrun))
      have hsilent : ∀ k, GenSilent sunfish st ([GenFrame.forGen bTarget a₂ sBody] ++ k)
          ⟨{ st.world with heap := h₂ }, Env.set (Env.set st.locals "i" (.int (i₀ : Int)))
            "p" (.str (String.singleton c))⟩ ([GenFrame.forGen bTarget a₂ sBody] ++ k) :=
        fun k => GenSilent.trans (hpush k) (hcont k)
      simpa using genEmits_silentLoop (pre := [GenFrame.forGen bTarget a₂ sBody])
        hsilent htail

/-! ## THE FLAGSHIP

Everything above, assembled: the enumerate object is allocated, the board
scan runs it out, and what comes back is `Ref.refMoves`. -/

/-- **The machine the theorem below speaks about IS the object the call
returns.** `callIn`'s creation arm allocates
`genObj "Position.gen_moves" f #[self]` (VCGen.lean §L3), whose locals are
`mkCallEnv`'s and whose stored continuation is the method's body — so the
state `gen_moves_yields_ref` is stated at is the shipped call's own, and
this `rfl` is what says so instead of a reader having to check. -/
theorem gen_moves_genObj (b : String) (score ep kp : Int)
    (wc0 wc1 bc0 bc1 : Bool) :
    (match findFunction sunfish "Position.gen_moves" with
     | some f => genObj "Position.gen_moves" f #[posOf b score wc0 wc1 bc0 bc1 ep kp]
     | none => .dict #[] 0)
      = .generator "Position.gen_moves"
          [("self", posOf b score wc0 wc1 bc0 bc1 ep kp)] [.block gmB] .created := rfl

set_option maxHeartbeats 800000 in
/-- **`Position.gen_moves` AGREES WITH THE REFERENCE.**

The shipped `Position.gen_moves`, resumed as a suspended machine over the
shipped AST with `self` bound to an arbitrary `Position`, yields exactly
the moves `Ref.refMoves` reports, in `Ref.refMoves`' order — the same
board, the same castling rights, the same en-passant and king-passant
squares, at every fuel above a threshold.

Board free (an arbitrary `String`, padding and all), rights free, squares
free, and the reference's own budget free: the hypothesis is that the
reference HAS an answer, which is where the board's readability lives.

The two world hypotheses are the module's `directions` dict, which is a
dict LITERAL and therefore lives in the heap rather than in the static
globals table; `initWorld sunfish` satisfies both (`#guard`s above). -/
theorem gen_moves_yields_ref (w : World) (dad : Addr)
    (b : String) (score ep kp : Int) (wc0 wc1 bc0 bc1 : Bool) (rf : Nat)
    (ms : List Ref.RefMove)
    (hg : Env.lookup w.globals "directions" = some (.ref dad))
    (hobj : Heap.get? w.heap dad = some dirsObj)
    (href : Ref.refMoves b.toList wc0 wc1 ep kp rf = .ok ms) :
    ∃ st', GenYields sunfish ⟨w, [("self", posOf b score wc0 wc1 bc0 bc1 ep kp)]⟩
      [.block gmB] (ms.map moveVal) st' := by
  -- the reference, re-indexed off the character list
  rw [refMoves_eq_refScan] at href
  obtain ⟨rss, hscan, rfl⟩ := exceptMap_ok.mp href
  -- the enumerate object, allocated
  have hloc : RayLocals [("self", posOf b score wc0 wc1 bc0 bc1 ep kp)] := by
    intro x hx
    have hne : x ≠ "self" := by rintro rfl; exact hx (by decide)
    simp [Env.lookup, Ne.symm hne]
  have hself : Env.lookup [("self", posOf b score wc0 wc1 bc0 bc1 ep kp)] "self"
      = some (posOf b score wc0 wc1 bc0 bc1 ep kp) := rfl
  have hdlt : dad < w.heap.size := Heap.lt_size_of_get? hobj
  have hwf : WorldFacts dad w.heap.size 0 (strCharVals b)
      { w with heap := w.heap.push (enumObj 0 (strCharVals b)) } :=
    ⟨hg, by
      rw [show ({ w with heap := w.heap.push (enumObj 0 (strCharVals b)) } : World).heap
        = w.heap.push (enumObj 0 (strCharVals b)) from rfl, Heap.get?_push_lt hdlt]
      exact hobj,
      Heap.get?_push_size _ _⟩
  obtain ⟨st', hemits⟩ := board_scan dad w.heap.size b score ep kp wc0 wc1 bc0 bc1 rf
    b.toList 0 rss ⟨{ w with heap := w.heap.push (enumObj 0 (strCharVals b)) },
      [("self", posOf b score wc0 wc1 bc0 bc1 ep kp)]⟩
    hscan ⟨hloc, hself, by
      simpa [strCharVals_eq_map] using hwf⟩
  refine ⟨st', GenEmits.toYields ?_⟩
  refine GenEmits.silent
    (pre₁ := [GenFrame.forGen bTarget w.heap.size sBody, GenFrame.block ([] : List Stmt)])
    (fun k => by
      simpa [gmB_split] using genSilent_forHereGen (m := sunfish) (s := bScan)
        (ss := ([] : List Stmt)) (k := k) bScan_plan
        (enum_evals w _ b score ep kp wc0 wc1 bc0 bc1 hloc hself)
        (Heap.get?_push_size w.heap (enumObj 0 (strCharVals b)))) ?_
  simpa using GenEmits.trans hemits (block_done st')

/-! ## Non-vacuity

The flagship's two world hypotheses are `#guard`ed against
`initWorld sunfish` above. These are the two configurations this landing
added, on boards the pins already check against CPython: a pawn on the
seventh rank capturing onto the last row (`Ref.at? … 22` is an enemy rook
and 22 is a promotion square), and a pawn on the sixth rank whose double
push would land on the last row (41 + 2N = 21, and 41 is nearer than the
guard allows, so the ray reports nothing). -/

/-! A board a pawn PROMOTES BY CAPTURE on, checked against CPython's own
`sunfish.gen_moves` (`[(32,22,'N'),…,(32,21,'Q'),(91,81,''),(91,92,''),
(91,82,'')]`, run on the shipped file) as well as against the reference:
the pawn on 32 pushes onto 22 and takes the rook on 21, four promotions
each. It is a NEW board, and it is here because the existing pin labelled
"promotion captures" (pins_genmoves.lean) does not reach that leaf — its
enemy rooks stand on 22 and 24, which blocks the push and leaves both
diagonals empty, so the three moves it pins are the king's. The reference
was right; the pin's board was not the board its comment describes. -/

def capPromBoard : String :=
  "         \n         \n r.......\n .P......\n ........\n ........\n ........\n ........\n ........\n K.......\n         \n         \n"

#guard (match Ref.at? capPromBoard.toList 32 with | .ok c => c == 'P' | _ => false)
#guard (match Ref.at? capPromBoard.toList 21 with | .ok c => c == 'r' | _ => false)
#guard (32 + (Ref.N + Ref.W) == (21 : Int)) &&
  (decide (Ref.A8 ≤ (21 : Int)) && decide ((21 : Int) ≤ Ref.H8))
#guard (match Ref.refMoves capPromBoard.toList false false 0 0 64 with
        | .ok ms => ms.map (fun m => (m.i, m.j, m.prom)) ==
            [(32, 22, "N"), (32, 22, "B"), (32, 22, "R"), (32, 22, "Q"),
             (32, 21, "N"), (32, 21, "B"), (32, 21, "R"), (32, 21, "Q"),
             (91, 81, ""), (91, 92, ""), (91, 82, "")]
        | .error _ => false)

/-! The double push that CANNOT happen: from the sixth rank the landing
square is on the last row, and the guard refuses before the promotion test
is ever reached — which is why the configuration needs a theorem of its
own and why that theorem emits nothing. -/

#guard (decide (Ref.A8 ≤ 41 + (Ref.N + Ref.N)) &&
  decide (41 + (Ref.N + Ref.N) ≤ Ref.H8)) && decide ((41 : Int) < Ref.A1 + Ref.N)

/-! ## What is left, measured — and a DEFECT in the object-level statement

`gen_moves_yields_ref` is the generator's whole agreement: from the frame
stack the interpreter builds for `Position.gen_moves`, the machine yields
exactly `Ref.refMoves`. `GenMovesEqRef` (genmoves_theorem.lean) says the
same thing one level out — about the heap OBJECT the call returns, drained
by `stepIter`. Two things stood between them when this file landed. The
first is now BUILT one file over (L6, 2026-08-17) and this note is updated
in place; the second is a defect in the frozen statement and is still only
recorded.

**1. The object-level drain bridge LANDED at L6, and what it rests on is one
named property.** `genmoves_drain.lean` next door is `gen_moves_drains_ref`:
the shipped method CALLED and its object DRAINED (`drainIter`) yields exactly
`Ref.refMoves`' moves in `Ref.refMoves`' order. The bridge itself
(`IterDrains.of_genYields`, VCGen.lean §L6) is an induction on the emitted
list, exactly as this note predicted — and the lockstep it needs is real:
`stepIter` writes the resumption into slot `a` before every step and
`drainGen` never writes that slot, so after the first yield the two chains
sit at heaps differing exactly at `a`, and stepping them together needs
"`execGen` does not depend on the payload of the RUNNING generator at `a`".
That is `PayloadBlind`, and §L7 PROVED it
(LeanModels/Python/PayloadBlind.lean, `payloadBlind`): the eighteen
interpreter arms, the block's induction on fuel, and the reduction to the
`execGen` conjunct. `gen_moves_drains_ref` next door therefore carries no
hypothesis at all.

Peeling the frame-level `GenYields` is what the bridge does
(`GenYields.uncons`), and it does not avoid the property: the per-yield facts
come out at FRAME-level worlds, which is precisely the mismatch.

**2. `GenMovesEqRef` as written is FALSE, and the counterexample is
one line.** `drain` runs every step at a CONSTANT fuel — `stepIter sunfish
16384 w a` — while the statement quantifies over an arbitrary board. Take
`b` to be twenty thousand `'.'` characters: the reference answers `.ok []`
(no square holds one of ours), so the hypothesis is satisfied, but one
`stepIter` has to cross every square before the scan can report
exhaustion, and `execGen` charges a fuel unit per frame step — so the
single step times out, `drain` answers `none`, and the equality fails at
EVERY `F`. Nothing about the proof effort hides this: the statement is
unprovable because it is untrue.

The repair is one line and it is the statement's own stated intent —
`genmoves_theorem.lean`'s note 4 says "`genMovesOf` runs at a single fuel
`F` for both the call and the drain", which the code does not do: `drain`
would take `F` and pass it to `stepIter`. It is NOT made here, because the
statement is owner-decided (docs/backlog.md §H4) and a landing that cannot
also prove the repaired form should not be the one to edit it. -/

end Examples.python.sunfish.genmoves_scan
