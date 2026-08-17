/-
The RAY, round by round and leaf by leaf — the remainder of **L4**
(docs/generator-tier-architecture.md §4; docs/backlog.md §"L4 PARTIAL"
prices what is here and says why it is a separate module).

`genmoves_theorem.lean` landed the ray's FIRST agreement leaf,
`ray_stop_agrees`: the shipped `Position.gen_moves`, suspended in a ray at
the `count` object holding `j`, on a board whose square `j` the reference
reads as a blocker, emits exactly what `Ref.ray` reports (nothing). This
file carries that from one leaf to the whole ray, and its two halves are
not the same kind of work:

* the remaining **leaves** are settled in shape — project the statement,
  run it at a symbolic board, splice the frame rule — and each costs one
  ~20 s captured `py_simp` over the `sunfish` module literal, which is why
  they live here rather than growing `genmoves_theorem.lean`;
* the **round induction** is the piece with no precedent in the tier, and
  it is the reason the file exists. From the unconditional `yield` on, the
  ray CONTINUES, so agreement stops being a leaf fact and becomes an
  invariant carried across rounds.

**What the round induction turned out to be.** It is NOT an induction over
the generator. `count(i + d, d)` never exhausts, so the model side has no
remainder list to recurse on and `GenEmits.forGenDone` is unreachable — the
only thing that ends a ray is a `break`. The induction is therefore over
the REFERENCE's fuel, and the model side rides along as a
continuation-passing round transformer (`RayRound`): each round proves "I
emit `out`, and whatever the loop frame emits AFTER me, I prepend `out` to
it". Composition is then function composition, `GenEmits.forGenRound` is
its introduction rule, and the ray's end is any round that never calls its
continuation.

That split is what makes `ray_rounds` provable without a single `py_simp`:
it is pure `Except`/`List` reasoning over `rayBody_append_or_const`, and it
takes the model side entirely as hypotheses. The two hypotheses are exactly
the two arms of that characterization — a round that ENDS the ray and a
round that CONTINUES it — so discharging them is precisely the leaf work,
and nothing about the induction moves when a leaf lands.
-/
import Examples.python.sunfish.genmoves_theorem

namespace Examples.python.sunfish.genmoves_ray

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.pins_genmoves
open Examples.python.sunfish.genmoves_theorem

/-! ## The rest of the ray, projected

`genmoves_theorem.lean` projected `rQ` and `rStop` off the shipped AST and
pinned each with an `rfl`; `rRest` is the five statements after them. Same
discipline here: nothing is retyped, so a changed PROGRAM stops the `rfl`s
loudly instead of quietly proving a theorem about a stale ray. -/

/-- `if p == "P": …` — the pawn block (sunfish.py 188-195). -/
def rPawn : Stmt := nth 0 rRest
/-- `yield Move(i, j, "")` — the unconditional yield (sunfish.py 197). -/
def rYield : Stmt := nth 1 rRest
/-- `if p in "PNK" or q in "pnbrqk": break` — the crawler guard. -/
def rCrawl : Stmt := nth 2 rRest
/-- The `i == A1` castling slide (sunfish.py 202). -/
def rCastA : Stmt := nth 3 rRest
/-- The `i == H1` castling slide (sunfish.py 203). -/
def rCastH : Stmt := nth 4 rRest

theorem rRest_split : rRest = [rPawn, rYield, rCrawl, rCastA, rCastH] := rfl

/-! The `.branch` statements' own parts, projected out of `genPlan` rather
than retyped — so `rPawn_plan` below is simultaneously the plan pin and the
definition of what the taken arm contains. -/

/-- The test of a `.branch` statement. -/
def planTest (s : Stmt) : Expr :=
  match genPlan s with | .branch t _ _ => t | _ => .constant .none nowhere
/-- The taken arm of a `.branch` statement. -/
def planBody (s : Stmt) : List Stmt :=
  match genPlan s with | .branch _ b _ => b | _ => []
/-- The `else` arm of a `.branch` statement. -/
def planOrelse (s : Stmt) : List Stmt :=
  match genPlan s with | .branch _ _ o => o | _ => []

theorem rPawn_plan :
    genPlan rPawn = .branch (planTest rPawn) (planBody rPawn) (planOrelse rPawn) := rfl
theorem rYield_plan : ∃ e, genPlan rYield = .yieldHere e := ⟨_, rfl⟩
theorem rCrawl_plan : genPlan rCrawl = .delegate := rfl
theorem rCastA_plan :
    genPlan rCastA = .branch (planTest rCastA) (planBody rCastA) (planOrelse rCastA) := rfl
theorem rCastH_plan :
    genPlan rCastH = .branch (planTest rCastH) (planBody rCastH) (planOrelse rCastH) := rfl

/-- No `else` arm anywhere in the ray: every branch either runs its body or
falls straight through. -/
theorem rPawn_orelse : planOrelse rPawn = [] := rfl
theorem rCastA_orelse : planOrelse rCastA = [] := rfl
theorem rCastH_orelse : planOrelse rCastH = [] := rfl

/-- The pawn block's four statements: the three `break` guards (all
`.delegate` — a bare `break` carries no yield) and the promotion branch,
which does. -/
def pB0 : Stmt := nth 0 (planBody rPawn)
def pB1 : Stmt := nth 1 (planBody rPawn)
def pB2 : Stmt := nth 2 (planBody rPawn)
def pB3 : Stmt := nth 3 (planBody rPawn)

theorem pawnBody_split : planBody rPawn = [pB0, pB1, pB2, pB3] := rfl
theorem pB0_plan : genPlan pB0 = .delegate := rfl
theorem pB1_plan : genPlan pB1 = .delegate := rfl
theorem pB2_plan : genPlan pB2 = .delegate := rfl
theorem pB3_plan :
    genPlan pB3 = .branch (planTest pB3) (planBody pB3) (planOrelse pB3) := rfl
theorem pB3_orelse : planOrelse pB3 = [] := rfl

/-- The promotion arm is two statements: the inlined `yield from` —
`for prom in "NBRQ": yield Move(i, j, prom)`, a `forSeq` over a string
literal, so `GenEmits.forSeq` already covers it — and the `break` that ends
the ray behind it. -/
def pProm : Stmt := nth 0 (planBody pB3)
def pPromBrk : Stmt := nth 1 (planBody pB3)

theorem promBody_split : planBody pB3 = [pProm, pPromBrk] := rfl
theorem pPromBrk_plan : genPlan pPromBrk = .delegate := rfl
theorem pPromBrk_lit : ∃ s, pPromBrk = .brk s := ⟨_, rfl⟩

/-! ## The reference's leaf dichotomy, strengthened

`rayBody_map_or_const` (genmoves_theorem.lean) says every leaf of the ray
body is either constant in the tail or `g <$> tail`. The induction needs
one notch more: the tail-consuming leaf PREPENDS a fixed list, and it is
that `pre ++ ·` shape — not an arbitrary `g` — that lets
`ms.map moveVal` split into the round's output and the rest of the ray's.
Same proof: unfold, split every guard, and each leaf closes by `rfl` on one
side or the other, with `pre` read off by unification. -/

open Ref in
set_option maxHeartbeats 2000000 in
theorem rayBody_append_or_const (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int)
    (p : Char) (d : Int) (j : Int) :
    (∃ r, ∀ t, rayBody b wc0 wc1 ep kp i p d j t = r) ∨
    (∃ pre : List RefMove,
        ∀ t, rayBody b wc0 wc1 ep kp i p d j t = (pre ++ ·) <$> t) := by
  unfold rayBody
  simp only [bind, Except.bind]
  repeat' split
  all_goals
    first
      | exact Or.inl ⟨_, fun t => rfl⟩
      | exact Or.inr ⟨_, fun t => by cases t <;> rfl⟩

/-! ### Which leaf, for a NON-PAWN

`rayBody_append_or_const` says a leaf is one of the two shapes; these three
say WHICH, from the two guards a non-pawn ray actually consults. Together
they are the trichotomy the whole file's reference side runs on — a blocked
square, a square that ends the slide, and a square the ray slides through —
and the last of them is the one no crawler ever reaches. -/

open Ref in
/-- The square is a BLOCKER: the ray stops before it, whatever the tail. -/
theorem rayBody_stop_const (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int)
    (p : Char) (d j : Int) (c : Char) (href : at? b j = .ok c)
    (hstop : inStr c " \nPNBRQK" = true) :
    ∀ t, rayBody b wc0 wc1 ep kp i p d j t = .ok [] := by
  intro t
  unfold rayBody
  simp only [bind, Except.bind, href, hstop, if_pos, pure, Except.pure]

open Ref in
/-- The square is reachable but ENDS the slide — a crawler, or a capture:
the one move, and no tail. -/
theorem rayBody_break_const (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int)
    (p : Char) (d j : Int) (c : Char) (href : at? b j = .ok c)
    (hopen : inStr c " \nPNBRQK" = false) (hnp : p ≠ 'P')
    (hbrk : (inStr p "PNK" || inStr c "pnbrqk") = true) :
    ∀ t, rayBody b wc0 wc1 ep kp i p d j t = .ok [⟨i, j, ""⟩] := by
  intro t
  unfold rayBody pawnBreak
  simp only [bind, Except.bind, href, hopen, Bool.false_eq_true, if_false,
    bne_iff_ne, ne_eq, hnp, not_false_eq_true, if_pos, hbrk, pure, Except.pure]

open Ref in
/-- The ray SLIDES ON: the one move is prepended and the tail is consumed.
Off the two corner squares both castling slides are empty, so `pre` is the
single move — which is what makes `ray_rounds`' `hgo` inhabitable. -/
theorem rayBody_slide_map (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int)
    (p : Char) (d j : Int) (c : Char) (href : at? b j = .ok c)
    (hopen : inStr c " \nPNBRQK" = false) (hnp : p ≠ 'P')
    (hgo : (inStr p "PNK" || inStr c "pnbrqk") = false)
    (hA : i ≠ A1) (hH : i ≠ H1) :
    ∀ t, rayBody b wc0 wc1 ep kp i p d j t
      = ([(⟨i, j, ""⟩ : RefMove)] ++ ·) <$> t := by
  have hA' : (i == A1) = false := beq_eq_false_iff_ne.mpr hA
  have hH' : (i == H1) = false := beq_eq_false_iff_ne.mpr hH
  intro t
  unfold rayBody pawnBreak
  simp only [bind, Except.bind, href, hopen, Bool.false_eq_true, if_false,
    bne_iff_ne, ne_eq, hnp, not_false_eq_true, if_pos, hgo, hA', hH', pure,
    Except.pure]
  cases t <;> rfl

open Ref in
/-- The two arms of `rayBody_append_or_const` are EXCLUSIVE: a body that
ignores its tail cannot also prepend to it. Read off the lengths at two
tails — the whole content of "the ray either ends here or it does not". -/
theorem rayBody_const_not_append (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int)
    (p : Char) (d j : Int) (r pre : List RefMove)
    (hconst : ∀ t, rayBody b wc0 wc1 ep kp i p d j t = .ok r)
    (hmap : ∀ t, rayBody b wc0 wc1 ep kp i p d j t = (pre ++ ·) <$> t) : False := by
  have h₀ := (hconst (.ok [])).symm.trans (hmap (.ok []))
  have h₁ := (hconst (.ok [⟨i, j, ""⟩])).symm.trans (hmap (.ok [⟨i, j, ""⟩]))
  simp only [Functor.map, Except.map] at h₀ h₁
  have e₀ : r = pre ++ [] := Except.ok.inj h₀
  have e₁ : r = pre ++ [⟨i, j, ""⟩] := Except.ok.inj h₁
  have hl := congrArg List.length (e₀.symm.trans e₁)
  simp at hl

/-! ## One ROUND, in continuation-passing form

The model side of a round cannot be stated as "it emits `out` and lands in
state `st₂`", because a `break` in the middle of the body leaves the loop
frame too and there is no `st₂` at the loop altitude to land in. What holds
uniformly is the CPS form below: a round is a transformer on the rest of
the ray's emission. `RayRound` is that transformer for a round that goes
again; a round that ends the ray is just a `GenEmits` outright, which is
what `ray_stop_agrees` already is. -/

/-- **A ray round that CONTINUES**: from `st`, the loop frame emits `out`
and then behaves exactly as the loop frame does from `st₂`. -/
def RayRound (a : Addr) (out : List RVal) (st st₂ : FrameState) : Prop :=
  ∀ (ws : List RVal) (st₃ : FrameState),
    GenEmits sunfish st₂ [.forGen gmRayTarget a gmRay] ws st₃ →
    GenEmits sunfish st [.forGen gmRayTarget a gmRay] (out ++ ws) st₃

/-- The introduction rule: step the `count` object, bind `j`, run the body
to a fall-through. This is `GenEmits.forGenRound` with its continuation
left free — which is the whole trick that turns the ray into a fold. -/
theorem RayRound.intro {a : Addr} {st st₂ : FrameState} {w' : World}
    {env₁ : REnv} {v : RVal} {out : List RVal}
    (hiter : IterSteps sunfish st.world a (some v) w')
    (hasg : assignToH w'.heap st.locals gmRayTarget v = .ok env₁)
    (hbody : GenEmits sunfish ⟨w', env₁⟩ [.block gmRay] out st₂) :
    RayRound a out st st₂ :=
  fun _ _ hrest => GenEmits.forGenRound hiter hasg hbody hrest

/-! ## The ROUND INDUCTION -/

set_option maxHeartbeats 800000 in
/-- **The round induction** — L4's remainder, and the fact L5 consumes.

Given an invariant `Inv j st` that holds when the ray is about to run its
round at square `j`, and an exit condition `Out`:

* whenever the reference's body at `j` is CONSTANT in its tail (the ray
  ENDS there), the generator emits that constant and stops — `hstop`;
* whenever it prepends a fixed `pre` and recurses (the ray CONTINUES), the
  generator emits `pre` and re-establishes the invariant one square along
  — `hgo`;

then the generator agrees with `Ref.ray` at EVERY square, at every fuel,
for the whole ray.

The induction is on the reference's fuel, not on the generator: `count`
never exhausts, so the model side has no decreasing measure and
`GenEmits.forGenDone` is unreachable on a ray. Nothing here runs a
statement — the model side enters entirely through `hstop`/`hgo` and
`RayRound`'s composition — so this theorem does not move when a leaf lands,
and the leaves can land one at a time. -/
theorem ray_rounds {b : String} {wc0 wc1 : Bool} {ep kp i d : Int} {p : Char}
    {a : Addr} (Inv : Int → FrameState → Prop) (Out : FrameState → Prop)
    (hstop : ∀ (jv : Int) (st : FrameState) (r : List Ref.RefMove),
      Inv jv st →
      (∀ t, rayBody b.toList wc0 wc1 ep kp i p d jv t = .ok r) →
      ∃ st', Out st' ∧
        GenEmits sunfish st [.forGen gmRayTarget a gmRay] (r.map moveVal) st')
    (hgo : ∀ (jv : Int) (st : FrameState) (pre : List Ref.RefMove),
      Inv jv st →
      (∀ t, rayBody b.toList wc0 wc1 ep kp i p d jv t = (pre ++ ·) <$> t) →
      ∃ st₂, Inv (jv + d) st₂ ∧ RayRound a (pre.map moveVal) st st₂) :
    ∀ (f : Nat) (jv : Int) (ms : List Ref.RefMove) (st : FrameState),
      Inv jv st → Ref.ray b.toList wc0 wc1 ep kp i p d f jv = .ok ms →
      ∃ st', Out st' ∧
        GenEmits sunfish st [.forGen gmRayTarget a gmRay] (ms.map moveVal) st' := by
  intro f
  induction f with
  | zero => intro jv ms st _ h; simp [Ref.ray] at h
  | succ f ih =>
    intro jv ms st hI h
    rw [ray_step] at h
    rcases rayBody_append_or_const b.toList wc0 wc1 ep kp i p d jv with
      ⟨r, hconst⟩ | ⟨pre, hmap⟩
    · rw [hconst] at h
      exact hstop jv st ms hI (fun t => by rw [hconst]; exact h)
    · rw [hmap] at h
      obtain ⟨rest, hrest, rfl⟩ := exceptMap_ok.mp h
      obtain ⟨st₂, hI₂, hround⟩ := hgo jv st pre hI hmap
      obtain ⟨st', hOut, htail⟩ := ih (jv + d) rest st₂ hI₂ hrest
      exact ⟨st', hOut, by simpa [List.map_append] using hround _ _ htail⟩

/-! ## The frame's locals

Every name the ray reads that is not one of `gen_moves`' own locals is a
module GLOBAL — `Move`, `A1`, `H1`, `N`, `E`, `W` — and name resolution
consults the LOCAL env first. Over an abstract `env` that is a real side
condition, so it is stated once here rather than one hypothesis per name,
and it is stable under the ray's own writes because `j`, `q` and `prom` are
themselves locals. -/

/-- `Position.gen_moves`' own locals: the parameter, the two loop targets of
the enclosing scans, the ray's target, and the two names the ray body
binds. -/
def rayNames : List String := ["self", "i", "p", "d", "j", "q", "prom"]

/-- The frame binds nothing but `rayNames`, so no module global is
shadowed. -/
def RayLocals (env : REnv) : Prop := ∀ x, x ∉ rayNames → Env.lookup env x = none

theorem RayLocals.miss {env : REnv} (h : RayLocals env) (x : String)
    (hx : x ∉ rayNames := by decide) : Env.lookup env x = none := h x hx

theorem RayLocals.set {env : REnv} (h : RayLocals env) {x : String}
    (hx : x ∈ rayNames := by decide) (v : RVal) : RayLocals (Env.set env x v) := by
  intro y hy
  rw [Env.lookup_set_ne _ (by
    simp only [beq_eq_false_iff_ne, ne_eq]
    rintro rfl
    exact hy hx)]
  exact h y hy

/-- **What the ray's frame knows between rounds.** `self`, `i` and `p` are
set by the two enclosing scans and never touched by the ray, so they ride
across every round unchanged; `RayLocals` is what makes the module globals
visible. This is the state half of the round invariant, and it is what the
board scan (L5) will hand in and get back. -/
def RayFrame (b : String) (score ep kp iv : Int) (wc0 wc1 bc0 bc1 : Bool)
    (p : Char) (env : REnv) : Prop :=
  RayLocals env ∧
  Env.lookup env "self" = some (posOf b score wc0 wc1 bc0 bc1 ep kp) ∧
  Env.lookup env "i" = some (.int iv) ∧
  Env.lookup env "p" = some (.str (String.singleton p))

theorem RayFrame.set {b : String} {score ep kp iv : Int} {wc0 wc1 bc0 bc1 : Bool}
    {p : Char} {env : REnv} (h : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p env)
    {x : String} (hx : x = "d" ∨ x = "j" ∨ x = "q" ∨ x = "prom" := by decide)
    (v : RVal) : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p (Env.set env x v) := by
  obtain ⟨hloc, hself, hi, hp⟩ := h
  have hmem : x ∈ rayNames := by rcases hx with rfl | rfl | rfl | rfl <;> decide
  have hne : ∀ y : String, y = "self" ∨ y = "i" ∨ y = "p" → (y == x) = false := by
    rintro y (rfl | rfl | rfl) <;> rcases hx with rfl | rfl | rfl | rfl <;> decide
  exact ⟨hloc.set hmem v,
    by rw [Env.lookup_set_ne _ (hne "self" (Or.inl rfl))]; exact hself,
    by rw [Env.lookup_set_ne _ (hne "i" (Or.inr (Or.inl rfl)))]; exact hi,
    by rw [Env.lookup_set_ne _ (hne "p" (Or.inr (Or.inr rfl)))]; exact hp⟩

/-! ## The one-character string bridge

`p` and `q` reach the frame from `enumerate(self.board)` and
`self.board[j]` as ONE-CHARACTER strings, while the reference speaks
`Char`. `strContains` already had `strContains_singleton`; equality needed
its own, and it is not `rfl` in this Lean — a `String` is no longer a
`List Char` — so it goes through `String.toList_singleton`. -/

theorem sing_eq (p c : Char) : (String.singleton p == String.singleton c) = (p == c) := by
  by_cases h : p = c
  · subst h; simp
  · have hne : String.singleton p ≠ String.singleton c := by
      intro he
      apply h
      have hl := congrArg String.toList he
      rw [String.toList_singleton, String.toList_singleton] at hl
      simpa using hl
    rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h]

theorem sing_P (p : Char) : (String.singleton p == "P") = (p == 'P') := by
  rw [show ("P" : String) = String.singleton 'P' from by decide]; exact sing_eq p 'P'

theorem truthy_boolH (w : World) (b : Bool) : truthyH w.heap (.bool b) = .ok b := by
  simp [truthyH, truthy]

/-- The same bridge at `"."`, which is the character the pawn block tests
against three times. -/
theorem sing_dot (c : Char) : (String.singleton c == ".") = (c == '.') := by
  rw [show ("." : String) = String.singleton '.' from by decide]; exact sing_eq c '.'

/-- **`==` between two INTEGERS through the heap-aware equality.** `heapEq`
is a frozen recursion point, deliberately out of `interpUnfolds`, and
`evalCompareOpH`'s `.eq` arm has a `refFree` fast path that keeps ordinary
comparisons off it. A TUPLE MEMBERSHIP has no such path: `valContains`
reaches `heapEq` directly through `heapContainsScan`, which is how the
pawn's `d in (N, N + N)` guards meet it. One step of the recursion, and its
scalar arm is `valEq`. -/
theorem heapEq_int (h : Heap) (f : Nat) (act : List (Addr × Addr)) (m n : Int) :
    heapEq h (f + 1) act (.int m) (.int n) = .ok (m == n) := by
  rw [heapEq] <;> simp [valEq]

/-! ## The statements, pinned to literals

The recorded trap: `py_simp` over a still-PROJECTED statement blows
heartbeats, because it re-opens `findFunction sunfish …` at every rewrite.
Every captured run below therefore rewrites through a `_lit` existential
first, exactly as `rQ_lit`/`rStop_lit` do. The literals are not
transcribed — they are printed off the shipped AST with the spans blanked,
so a changed PROGRAM still stops the `rfl`s loudly. -/

/-- The yielded expression of a `.yieldHere` statement. -/
def planValue (s : Stmt) : Expr :=
  match genPlan s with | .yieldHere e => e | _ => .constant .none nowhere

theorem rYield_plan' : genPlan rYield = .yieldHere (planValue rYield) := rfl

theorem rCrawl_lit : ∃ s1 s2 s3 s4 s5 s6 s7 s8 s9, rCrawl =
    (.ifStmt (.boolOp .or
      #[(.compare (.name "p" s1) #[.inOp] #[(.constant (.str "PNK") s2)] s3),
        (.compare (.name "q" s4) #[.inOp] #[(.constant (.str "pnbrqk") s5)] s6)] s7)
      #[(.brk s8)] #[] s9) :=
  ⟨_, _, _, _, _, _, _, _, _, rfl⟩

theorem rYieldVal_lit : ∃ s1 s2 s3 s4 s5, planValue rYield =
    (.call (.name "Move" s1)
      #[(.name "i" s2), (.name "j" s3), (.constant (.str "") s4)] #[] none s5) :=
  ⟨_, _, _, _, _, rfl⟩

theorem rPawnTest_lit : ∃ s1 s2 s3, planTest rPawn =
    (.compare (.name "p" s1) #[.eq] #[(.constant (.str "P") s2)] s3) :=
  ⟨_, _, _, rfl⟩

/-- The castling tests are three-operand `and` chains whose FIRST operand
is the corner-square comparison, so off a corner Python never reads the
board or the rights — which is the whole reason a slider round is cheap. -/
theorem rCastATest_lit : ∃ s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16,
    planTest rCastA =
    (.boolOp .and #[(.compare (.name "i" s1) #[.eq] #[(.name "A1" s2)] s3),
      (.compare (.subscript (.attribute (.name "self" s4) "board" s5)
        (.binOp (.name "j" s6) .add (.name "E" s7) s8) s9) #[.eq]
        #[(.constant (.str "K") s10)] s11),
      (.subscript (.attribute (.name "self" s12) "wc" s13)
        (.constant (.int 0) s14) s15)] s16) :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

@[inherit_doc rCastATest_lit]
theorem rCastHTest_lit : ∃ s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16,
    planTest rCastH =
    (.boolOp .and #[(.compare (.name "i" s1) #[.eq] #[(.name "H1" s2)] s3),
      (.compare (.subscript (.attribute (.name "self" s4) "board" s5)
        (.binOp (.name "j" s6) .add (.name "W" s7) s8) s9) #[.eq]
        #[(.constant (.str "K") s10)] s11),
      (.subscript (.attribute (.name "self" s12) "wc" s13)
        (.constant (.int 1) s14) s15)] s16) :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-! The pawn block's four statements. Every guard is an `and` chain whose
FIRST operand tests the direction, so at a fixed `d` the later operands —
the second board read in `pB1`, `self.ep`/`self.kp` in `pB2` — are reached
only for the directions that need them. -/

theorem pB0_lit : ∃ s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13, pB0 =
    (.ifStmt (.boolOp .and #[(.compare (.name "d" s1) #[.inOp]
      #[(.tuple #[(.name "N" s2), (.binOp (.name "N" s3) .add (.name "N" s4) s5)] s6)] s7),
      (.compare (.name "q" s8) #[.notEq] #[(.constant (.str ".") s9)] s10)] s11)
      #[(.brk s12)] #[] s13) :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem pB1_lit : ∃ s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22,
    pB1 =
    (.ifStmt (.boolOp .and #[(.compare (.name "d" s1) #[.eq]
      #[(.binOp (.name "N" s2) .add (.name "N" s3) s4)] s5),
      (.boolOp .or #[(.compare (.name "i" s6) #[.lt]
        #[(.binOp (.name "A1" s7) .add (.name "N" s8) s9)] s10),
        (.compare (.subscript (.attribute (.name "self" s11) "board" s12)
          (.binOp (.name "i" s13) .add (.name "N" s14) s15) s16) #[.notEq]
          #[(.constant (.str ".") s17)] s18)] s19)] s20) #[(.brk s21)] #[] s22) :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem pB2_lit : ∃ s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22
    s23 s24 s25 s26 s27, pB2 =
    (.ifStmt (.boolOp .and #[(.compare (.name "d" s1) #[.inOp]
      #[(.tuple #[(.binOp (.name "N" s2) .add (.name "W" s3) s4),
        (.binOp (.name "N" s5) .add (.name "E" s6) s7)] s8)] s9),
      (.compare (.name "q" s10) #[.eq] #[(.constant (.str ".") s11)] s12),
      (.compare (.name "j" s13) #[.notEq] #[(.attribute (.name "self" s14) "ep" s15)] s16),
      (.compare (.call (.name "abs" s17)
        #[(.binOp (.name "j" s18) .sub (.attribute (.name "self" s19) "kp" s20) s21)] #[] none s22)
        #[.gt] #[(.constant (.int 1) s23)] s24)] s25) #[(.brk s26)] #[] s27) :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- The promotion test is a CHAINED comparison, `A8 <= j <= H8`, so the
middle operand is evaluated once and compared twice. -/
theorem pB3Test_lit : ∃ s1 s2 s3 s4, planTest pB3 =
    (.compare (.name "A8" s1) #[.ltE, .ltE] #[(.name "j" s2), (.name "H8" s3)] s4) :=
  ⟨_, _, _, _, rfl⟩

/-! ## The captured runs -/

set_option maxHeartbeats 1600000 in
/-- **`if q in " \nPNBRQK": break` when the square is OPEN.** The mirror of
`rStop_run`: same collapse to `strContains` on a one-character needle, the
other way round, so the ray falls through to the pawn block. -/
theorem rStop_run_next (w : World) (env : REnv) (c : Char)
    (hq : Env.lookup env "q" = some (.str (String.singleton c)))
    (hopen : Ref.inStr c " \nPNBRQK" = false) :
    execStmt sunfish 16 ⟨w, env⟩ rStop = .ok ⟨w, env⟩ .next := by
  obtain ⟨s₁, s₂, s₃, s₄, s₅, hlit⟩ := rStop_lit
  rw [hlit]
  have hc : strContains " \nPNBRQK" (String.singleton c) = false := by
    rw [strContains_singleton]; exact hopen
  py_simp [hq, hc]

set_option maxHeartbeats 1600000 in
/-- **`if p in "PNK" or q in "pnbrqk": break`, BOTH arms at once.** Each
`in` is rewritten to its constant BEFORE `py_simp` runs — left symbolic, the
two guards expand into a nine-character disjunction and the run times out.
Python's `or` short-circuits, so the four `bp`/`bq` cases are taken
separately and each is a concrete, cheap reduction. -/
theorem rCrawl_run (w : World) (env : REnv) (p q : Char) (bp bq : Bool)
    (hp : Env.lookup env "p" = some (.str (String.singleton p)))
    (hq : Env.lookup env "q" = some (.str (String.singleton q)))
    (hbp : Ref.inStr p "PNK" = bp) (hbq : Ref.inStr q "pnbrqk" = bq) :
    execStmt sunfish 16 ⟨w, env⟩ rCrawl
      = .ok ⟨w, env⟩ (if bp || bq then .brk else .next) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, hlit⟩ := rCrawl_lit
  rw [hlit]
  have h1 : strContains "PNK" (String.singleton p) = bp := by
    rw [strContains_singleton]; exact hbp
  have h2 : strContains "pnbrqk" (String.singleton q) = bq := by
    rw [strContains_singleton]; exact hbq
  cases bp <;> cases bq <;> py_simp [hp, hq, h1, h2]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
/-- **`Move(i, j, "")`** — the namedtuple the ray yields, at a symbolic
square. `Move` is a module-level namedtuple, so the call resolves off the
module; `RayLocals` is what says the frame does not shadow the name. -/
theorem rYield_evals (w : World) (env : REnv) (iv jv : Int)
    (hloc : RayLocals env)
    (hi : Env.lookup env "i" = some (.int iv))
    (hj : Env.lookup env "j" = some (.int jv)) :
    EvalsTo sunfish ⟨w, env⟩ (planValue rYield) (moveVal ⟨iv, jv, ""⟩) := by
  obtain ⟨s1, s2, s3, s4, s5, hlit⟩ := rYieldVal_lit
  rw [hlit]
  refine EvalsTo.of_eval (fuel := 16) ?_
  py_simp [sunfish, moveVal, hloc.miss "Move", hi, hj]

set_option maxHeartbeats 1600000 in
/-- **`p == "P"`** — the pawn block's test, at a symbolic piece. -/
theorem rPawn_test_run (w : World) (env : REnv) (p : Char)
    (hp : Env.lookup env "p" = some (.str (String.singleton p))) :
    EvalsTo sunfish ⟨w, env⟩ (planTest rPawn) (.bool (p == 'P')) := by
  obtain ⟨s1, s2, s3, hlit⟩ := rPawnTest_lit
  rw [hlit]
  refine EvalsTo.of_eval (fuel := 8) ?_
  py_simp [hp, sing_P]
  by_cases h : p = 'P'
  · subst h; simp
  · rw [if_neg h, beq_eq_false_iff_ne.mpr h]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
/-- **`i == A1 and …` off the a1 square** — and with it the tool defect
that held the slider rounds up, which is why the `valEq.eq_def` in the
`py_simp` list is load-bearing rather than decorative.

`valEq` is in `interpUnfolds`, so `py_simp` DELTA-unfolds it, and a delta
unfold is recorded as a rewrite proved by `Eq.refl`. That is fine wherever
the match can fire, but `evalCompareChain` puts the right operand behind a
`fun st rhs => …`, and simp opens `valEq (.int iv) rhs` under that binder
before the operand's own evaluation has resolved. `valEq` lives in a MUTUAL
block, so at a stuck match the elaborator accepts the `Eq.refl` (its `whnf`
does smart unfolding) and the KERNEL rejects it — `(kernel) application
type mismatch`, on a reduction that was otherwise perfect. `valEq.eq_def`
is that same rewrite carrying a REAL proof, and a lemma at the head fires
before the unfold does, so the term the kernel sees is the same one with a
proof it can check. -/
theorem castA_test_false (w : World) (env : REnv) (iv : Int)
    (hloc : RayLocals env) (hi : Env.lookup env "i" = some (.int iv))
    (hne : iv ≠ Ref.A1) :
    EvalsTo sunfish ⟨w, env⟩ (planTest rCastA) (.bool false) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, hlit⟩ :=
    rCastATest_lit
  rw [hlit]
  refine EvalsTo.of_eval (fuel := 16) ?_
  have hne' : ¬ (iv = 91) := hne
  py_simp [sunfish, hi, hloc.miss "A1", valEq.eq_def, hne']

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
@[inherit_doc castA_test_false]
theorem castH_test_false (w : World) (env : REnv) (iv : Int)
    (hloc : RayLocals env) (hi : Env.lookup env "i" = some (.int iv))
    (hne : iv ≠ Ref.H1) :
    EvalsTo sunfish ⟨w, env⟩ (planTest rCastH) (.bool false) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, hlit⟩ :=
    rCastHTest_lit
  rw [hlit]
  refine EvalsTo.of_eval (fuel := 16) ?_
  have hne' : ¬ (iv = 98) := hne
  py_simp [sunfish, hi, hloc.miss "H1", valEq.eq_def, hne']

/-! The pawn block's four statements, run at a SINGLE PUSH (`d = N`). At
that direction three of the four guards are decided by the direction alone,
which is what keeps them cheap: `pB1` never reads the board and `pB2` never
reads `self.ep`/`self.kp`. -/

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
/-- **`if d in (N, N + N) and q != ".": break`** — the pawn's own stop
guard. At `d = N` the membership is true, so the statement breaks exactly
when the square ahead is occupied. -/
theorem pB0_run (w : World) (env : REnv) (c : Char) (bq : Bool)
    (hloc : RayLocals env)
    (hd : Env.lookup env "d" = some (.int Ref.N))
    (hq : Env.lookup env "q" = some (.str (String.singleton c)))
    (hbq : (c != '.') = bq) :
    execStmt sunfish 16 ⟨w, env⟩ pB0 = .ok ⟨w, env⟩ (if bq then .brk else .next) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, hlit⟩ := pB0_lit
  rw [hlit]
  have hd' : Env.lookup env "d" = some (.int (-10)) := hd
  subst hbq
  by_cases hc : c = '.' <;>
    py_simp [sunfish, hloc.miss "N", hd', hq, valEq.eq_def, heapEq_int, sing_dot, hc]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
/-- **The double-move guard falls through at a single push**: `d == N + N`
is false, so Python never evaluates the `or` behind it and the SECOND board
read never happens. -/
theorem pB1_run (w : World) (env : REnv) (hloc : RayLocals env)
    (hd : Env.lookup env "d" = some (.int Ref.N)) :
    execStmt sunfish 16 ⟨w, env⟩ pB1 = .ok ⟨w, env⟩ .next := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, hlit⟩ := pB1_lit
  rw [hlit]
  have hd' : Env.lookup env "d" = some (.int (-10)) := hd
  py_simp [sunfish, hloc.miss "N", hd', valEq.eq_def]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
/-- **The capture guard falls through at a single push**: `d in (N + W,
N + E)` is false, so `self.ep` and `self.kp` are never read. -/
theorem pB2_run (w : World) (env : REnv) (hloc : RayLocals env)
    (hd : Env.lookup env "d" = some (.int Ref.N)) :
    execStmt sunfish 16 ⟨w, env⟩ pB2 = .ok ⟨w, env⟩ .next := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, s27, hlit⟩ := pB2_lit
  rw [hlit]
  have hd' : Env.lookup env "d" = some (.int (-10)) := hd
  py_simp [sunfish, hloc.miss "N", hloc.miss "W", hloc.miss "E", hd', valEq.eq_def, heapEq_int]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
/-- **`A8 <= j <= H8`**, the promotion test, at a symbolic square. Both
bounds are module globals and the comparison is ORDERING, so it never
reaches `valEq` — the chained shape is the only new thing here. -/
theorem pB3_test_run (w : World) (env : REnv) (jv : Int) (b : Bool)
    (hloc : RayLocals env)
    (hj : Env.lookup env "j" = some (.int jv))
    (hb : (decide (Ref.A8 ≤ jv) && decide (jv ≤ Ref.H8)) = b) :
    EvalsTo sunfish ⟨w, env⟩ (planTest pB3) (.bool b) := by
  obtain ⟨s1, s2, s3, s4, hlit⟩ := pB3Test_lit
  rw [hlit]
  refine EvalsTo.of_eval (fuel := 12) ?_
  subst hb
  by_cases h1 : (21 : Int) ≤ jv <;> by_cases h2 : jv ≤ (28 : Int) <;>
    py_simp [sunfish, Ref.A8, Ref.H8, hloc.miss "A8", hloc.miss "H8", hj, h1, h2]

/-! ## The segments

One statement each, over a FREE trailing continuation `pre`, so the same
lemma serves a round that falls through (`pre = []`, the block frame pops)
and a round that breaks (`pre = [.forGen …]`, because `break` unwinds past
the loop frame and the two leave together). That is the whole reason the
kit is stated this way. -/

/-- `q = self.board[j]` falls through. -/
theorem q_falls (w : World) (env : REnv) (b : String) (score ep kp jv : Int)
    (wc0 wc1 bc0 bc1 : Bool) (c : Char)
    {pre : GenCont} {ws : List RVal} {st₂ : FrameState}
    (hself : Env.lookup env "self" = some (posOf b score wc0 wc1 bc0 bc1 ep kp))
    (hj : Env.lookup env "j" = some (.int jv))
    (href : Ref.at? b.toList jv = .ok c)
    (hrest : GenEmits sunfish ⟨w, Env.set env "q" (.str (String.singleton c))⟩
      ([.block (rStop :: rRest)] ++ pre) ws st₂) :
    GenEmits sunfish ⟨w, env⟩ ([.block gmRay] ++ pre) ws st₂ :=
  GenEmits.silent (pre₁ := [GenFrame.block (rStop :: rRest)] ++ pre) (fun k => by
    simpa [gmRay_split] using genSilent_delegate (m := sunfish) (s := rQ)
      (ss := rStop :: rRest) (k := pre ++ k) rQ_plan
      (run_at_least (rQ_run w env b score ep kp jv wc0 wc1 bc0 bc1 c hself hj href))) hrest

/-- The stop guard falls through: the square is open. -/
theorem stop_falls (w : World) (env : REnv) (c : Char)
    {pre : GenCont} {ws : List RVal} {st₂ : FrameState}
    (hq : Env.lookup env "q" = some (.str (String.singleton c)))
    (hopen : Ref.inStr c " \nPNBRQK" = false)
    (hrest : GenEmits sunfish ⟨w, env⟩ ([.block rRest] ++ pre) ws st₂) :
    GenEmits sunfish ⟨w, env⟩ ([.block (rStop :: rRest)] ++ pre) ws st₂ :=
  GenEmits.silent (pre₁ := [GenFrame.block rRest] ++ pre) (fun k => by
    simpa using genSilent_delegate (m := sunfish) (s := rStop) (ss := rRest)
      (k := pre ++ k) rStop_plan (run_at_least (rStop_run_next w env c hq hopen))) hrest

/-- The stop guard BREAKS: the square is a blocker, and the loop frame goes
with the body. This is `ray_stop_agrees`' leaf, restated as a segment. -/
theorem stop_breaks (w : World) (env : REnv) (c : Char) (a : Addr)
    (hq : Env.lookup env "q" = some (.str (String.singleton c)))
    (hstop : Ref.inStr c " \nPNBRQK" = true) :
    GenEmits sunfish ⟨w, env⟩
      [.block (rStop :: rRest), .forGen gmRayTarget a gmRay] [] ⟨w, env⟩ :=
  GenEmits.blockBreak (pre := [GenFrame.forGen gmRayTarget a gmRay]) rStop_plan
    (fun _ => rfl) (run_at_least (rStop_run w env c hq hstop))

/-- The pawn block is SKIPPED — the piece is not a pawn, so the branch takes
its empty `else` arm and the frame pops straight through. -/
theorem pawn_skips (w : World) (env : REnv) (p : Char)
    {pre : GenCont} {ws : List RVal} {st₂ : FrameState}
    (hp : Env.lookup env "p" = some (.str (String.singleton p))) (hnp : p ≠ 'P')
    (hrest : GenEmits sunfish ⟨w, env⟩
      ([.block [rYield, rCrawl, rCastA, rCastH]] ++ pre) ws st₂) :
    GenEmits sunfish ⟨w, env⟩ ([.block rRest] ++ pre) ws st₂ := by
  have hb : (p == 'P') = false := by simp [hnp]
  refine GenEmits.silent
    (pre₁ := [GenFrame.block (planOrelse rPawn),
              GenFrame.block [rYield, rCrawl, rCastA, rCastH]] ++ pre)
    (fun k => by
      simpa [rRest_split] using genSilent_branch (m := sunfish) (s := rPawn) (b := false)
        (k := pre ++ k) rPawn_plan (hb ▸ rPawn_test_run w env p hp)
        (truthy_boolH w false)) ?_
  refine GenEmits.silent (pre₁ := [GenFrame.block [rYield, rCrawl, rCastA, rCastH]] ++ pre)
    (fun k => by
      simpa [rPawn_orelse] using genSilent_blockNil (m := sunfish) (st := ⟨w, env⟩)
        (k := GenFrame.block [rYield, rCrawl, rCastA, rCastH] :: (pre ++ k))) hrest

/-- The unconditional `yield Move(i, j, "")` — the ray's one certain move. -/
theorem yield_emits (w : World) (env : REnv) (iv jv : Int)
    {pre : GenCont} {ws : List RVal} {st₂ : FrameState}
    (hloc : RayLocals env)
    (hi : Env.lookup env "i" = some (.int iv))
    (hj : Env.lookup env "j" = some (.int jv))
    (hrest : GenEmits sunfish ⟨w, env⟩ ([.block [rCrawl, rCastA, rCastH]] ++ pre) ws st₂) :
    GenEmits sunfish ⟨w, env⟩ ([.block [rYield, rCrawl, rCastA, rCastH]] ++ pre)
      (moveVal ⟨iv, jv, ""⟩ :: ws) st₂ :=
  GenEmits.cons (pre₁ := [GenFrame.block [rCrawl, rCastA, rCastH]] ++ pre) (fun k => by
    simpa using genSteps_yieldHere (m := sunfish) (s := rYield)
      (ss := [rCrawl, rCastA, rCastH]) (k := pre ++ k) rYield_plan'
      (rYield_evals w env iv jv hloc hi hj)) hrest

/-- The crawler guard BREAKS — a crawler does not slide, and a capture ends
the slide. This is where a knight's or a king's ray ends. -/
theorem crawl_breaks (w : World) (env : REnv) (p q : Char) (a : Addr)
    (hp : Env.lookup env "p" = some (.str (String.singleton p)))
    (hq : Env.lookup env "q" = some (.str (String.singleton q)))
    (hbrk : (Ref.inStr p "PNK" || Ref.inStr q "pnbrqk") = true) :
    GenEmits sunfish ⟨w, env⟩
      [.block [rCrawl, rCastA, rCastH], .forGen gmRayTarget a gmRay] [] ⟨w, env⟩ :=
  GenEmits.blockBreak (pre := [GenFrame.forGen gmRayTarget a gmRay]) rCrawl_plan
    (fun _ => rfl)
    (run_at_least (by simpa [hbrk] using rCrawl_run w env p q _ _ hp hq rfl rfl))

/-- The crawler guard falls through: a slider keeps going. -/
theorem crawl_falls (w : World) (env : REnv) (p q : Char)
    {pre : GenCont} {ws : List RVal} {st₂ : FrameState}
    (hp : Env.lookup env "p" = some (.str (String.singleton p)))
    (hq : Env.lookup env "q" = some (.str (String.singleton q)))
    (hgo : (Ref.inStr p "PNK" || Ref.inStr q "pnbrqk") = false)
    (hrest : GenEmits sunfish ⟨w, env⟩ ([.block [rCastA, rCastH]] ++ pre) ws st₂) :
    GenEmits sunfish ⟨w, env⟩ ([.block [rCrawl, rCastA, rCastH]] ++ pre) ws st₂ :=
  GenEmits.silent (pre₁ := [GenFrame.block [rCastA, rCastH]] ++ pre) (fun k => by
    simpa using genSilent_delegate (m := sunfish) (s := rCrawl) (ss := [rCastA, rCastH])
      (k := pre ++ k) rCrawl_plan
      (run_at_least (by simpa [hgo] using rCrawl_run w env p q _ _ hp hq rfl rfl))) hrest

/-- The a1 castling `if` is SKIPPED: the piece is not on a1, so the `and`
chain short-circuits at its first comparison and the board is never read.
The statement is a `.branch` with an empty `else`, so this is `pawn_skips`'
shape — the branch pushes the empty arm, and the empty arm pops. -/
theorem castA_skips (w : World) (env : REnv) (iv : Int)
    {pre : GenCont} {ws : List RVal} {st₂ : FrameState}
    (hloc : RayLocals env) (hi : Env.lookup env "i" = some (.int iv))
    (hne : iv ≠ Ref.A1)
    (hrest : GenEmits sunfish ⟨w, env⟩ ([.block [rCastH]] ++ pre) ws st₂) :
    GenEmits sunfish ⟨w, env⟩ ([.block [rCastA, rCastH]] ++ pre) ws st₂ := by
  refine GenEmits.silent
    (pre₁ := [GenFrame.block (planOrelse rCastA), GenFrame.block [rCastH]] ++ pre)
    (fun k => by
      simpa using genSilent_branch (m := sunfish) (s := rCastA) (b := false)
        (k := pre ++ k) rCastA_plan (castA_test_false w env iv hloc hi hne)
        (truthy_boolH w false)) ?_
  refine GenEmits.silent (pre₁ := [GenFrame.block [rCastH]] ++ pre)
    (fun k => by
      simpa [rCastA_orelse] using genSilent_blockNil (m := sunfish) (st := ⟨w, env⟩)
        (k := GenFrame.block [rCastH] :: (pre ++ k))) hrest

/-- The h1 castling `if` is SKIPPED, and with it the ray body ENDS: what is
left is the empty block frame that `block_done` pops. -/
theorem castH_skips (w : World) (env : REnv) (iv : Int)
    {pre : GenCont} {ws : List RVal} {st₂ : FrameState}
    (hloc : RayLocals env) (hi : Env.lookup env "i" = some (.int iv))
    (hne : iv ≠ Ref.H1)
    (hrest : GenEmits sunfish ⟨w, env⟩ ([.block []] ++ pre) ws st₂) :
    GenEmits sunfish ⟨w, env⟩ ([.block [rCastH]] ++ pre) ws st₂ := by
  refine GenEmits.silent
    (pre₁ := [GenFrame.block (planOrelse rCastH), GenFrame.block ([] : List Stmt)] ++ pre)
    (fun k => by
      simpa using genSilent_branch (m := sunfish) (s := rCastH) (b := false)
        (k := pre ++ k) rCastH_plan (castH_test_false w env iv hloc hi hne)
        (truthy_boolH w false)) ?_
  refine GenEmits.silent (pre₁ := [GenFrame.block ([] : List Stmt)] ++ pre)
    (fun k => by
      simpa [rCastH_orelse] using genSilent_blockNil (m := sunfish) (st := ⟨w, env⟩)
        (k := GenFrame.block ([] : List Stmt) :: (pre ++ k))) hrest

/-- A finished block frame pops, at `GenEmits` altitude. -/
theorem block_done (st : FrameState) : GenEmits sunfish st [.block []] [] st :=
  GenEmits.silent (pre₁ := ([] : GenCont))
    (fun k => by simpa using genSilent_blockNil (m := sunfish) (st := st) (k := k))
    GenEmits.nil

/-! ### Inside the pawn block

The pawn block is the one `.branch` the ray ever ENTERS, so its four
statements need the same kit one level down. The frame below it — the rest
of the ray body — is just part of `pre`, which is why nothing here mentions
it. -/

/-- The pawn block is ENTERED: the piece is a pawn, so the branch pushes its
body ON TOP of the rest of the ray body. `pawn_skips`' other arm. -/
theorem pawn_enters (w : World) (env : REnv)
    {pre : GenCont} {ws : List RVal} {st₂ : FrameState}
    (hp : Env.lookup env "p" = some (.str (String.singleton 'P')))
    (hrest : GenEmits sunfish ⟨w, env⟩
      ([.block [pB0, pB1, pB2, pB3], .block [rYield, rCrawl, rCastA, rCastH]] ++ pre)
      ws st₂) :
    GenEmits sunfish ⟨w, env⟩ ([.block rRest] ++ pre) ws st₂ :=
  GenEmits.silent
    (pre₁ := [GenFrame.block (planBody rPawn),
              GenFrame.block [rYield, rCrawl, rCastA, rCastH]] ++ pre)
    (fun k => by
      simpa [rRest_split] using genSilent_branch (m := sunfish) (s := rPawn) (b := true)
        (k := pre ++ k) rPawn_plan (by simpa using rPawn_test_run w env 'P' hp)
        (truthy_boolH w true))
    (by simpa [pawnBody_split] using hrest)

/-- **The pawn's push is BLOCKED** — the square ahead is occupied, so the
ray ends with no move at all. The `break` is two block frames deep, so
`pre` carries the rest of the ray body as well as the loop frame; both
leave, which is exactly what `genBreak` does and why one break rule covers
every one of these guards. -/
theorem pB0_breaks (w : World) (env : REnv) (c : Char) (a : Addr)
    (hloc : RayLocals env)
    (hd : Env.lookup env "d" = some (.int Ref.N))
    (hq : Env.lookup env "q" = some (.str (String.singleton c)))
    (hne : c ≠ '.') :
    GenEmits sunfish ⟨w, env⟩
      [.block [pB0, pB1, pB2, pB3], .block [rYield, rCrawl, rCastA, rCastH],
        .forGen gmRayTarget a gmRay] [] ⟨w, env⟩ :=
  GenEmits.blockBreak (pre := [GenFrame.block [rYield, rCrawl, rCastA, rCastH],
      GenFrame.forGen gmRayTarget a gmRay]) pB0_plan (fun _ => rfl)
    (run_at_least (by
      simpa using pB0_run w env c true hloc hd hq (by simpa using hne)))

/-- The push is clear: the square ahead is empty. -/
theorem pB0_falls (w : World) (env : REnv)
    {pre : GenCont} {ws : List RVal} {st₂ : FrameState}
    (hloc : RayLocals env)
    (hd : Env.lookup env "d" = some (.int Ref.N))
    (hq : Env.lookup env "q" = some (.str (String.singleton '.')))
    (hrest : GenEmits sunfish ⟨w, env⟩ ([.block [pB1, pB2, pB3]] ++ pre) ws st₂) :
    GenEmits sunfish ⟨w, env⟩ ([.block [pB0, pB1, pB2, pB3]] ++ pre) ws st₂ :=
  GenEmits.silent (pre₁ := [GenFrame.block [pB1, pB2, pB3]] ++ pre) (fun k => by
    simpa using genSilent_delegate (m := sunfish) (s := pB0) (ss := [pB1, pB2, pB3])
      (k := pre ++ k) pB0_plan
      (run_at_least (by simpa using pB0_run w env '.' false hloc hd hq (by simp)))) hrest

/-- The double-move guard falls through: this is not a double move. -/
theorem pB1_falls (w : World) (env : REnv)
    {pre : GenCont} {ws : List RVal} {st₂ : FrameState}
    (hloc : RayLocals env) (hd : Env.lookup env "d" = some (.int Ref.N))
    (hrest : GenEmits sunfish ⟨w, env⟩ ([.block [pB2, pB3]] ++ pre) ws st₂) :
    GenEmits sunfish ⟨w, env⟩ ([.block [pB1, pB2, pB3]] ++ pre) ws st₂ :=
  GenEmits.silent (pre₁ := [GenFrame.block [pB2, pB3]] ++ pre) (fun k => by
    simpa using genSilent_delegate (m := sunfish) (s := pB1) (ss := [pB2, pB3])
      (k := pre ++ k) pB1_plan (run_at_least (pB1_run w env hloc hd))) hrest

/-- The capture guard falls through: this is not a diagonal move. -/
theorem pB2_falls (w : World) (env : REnv)
    {pre : GenCont} {ws : List RVal} {st₂ : FrameState}
    (hloc : RayLocals env) (hd : Env.lookup env "d" = some (.int Ref.N))
    (hrest : GenEmits sunfish ⟨w, env⟩ ([.block [pB3]] ++ pre) ws st₂) :
    GenEmits sunfish ⟨w, env⟩ ([.block [pB2, pB3]] ++ pre) ws st₂ :=
  GenEmits.silent (pre₁ := [GenFrame.block [pB3]] ++ pre) (fun k => by
    simpa using genSilent_delegate (m := sunfish) (s := pB2) (ss := [pB3])
      (k := pre ++ k) pB2_plan (run_at_least (pB2_run w env hloc hd))) hrest

/-- The promotion branch is SKIPPED, and with it the pawn block ends: two
empty block frames pop — the branch's `else` arm, and the pawn block
itself — so what is left is the rest of the ray body. -/
theorem pB3_skips (w : World) (env : REnv) (jv : Int)
    {pre : GenCont} {ws : List RVal} {st₂ : FrameState}
    (hloc : RayLocals env) (hj : Env.lookup env "j" = some (.int jv))
    (hnoprom : (decide (Ref.A8 ≤ jv) && decide (jv ≤ Ref.H8)) = false)
    (hrest : GenEmits sunfish ⟨w, env⟩ pre ws st₂) :
    GenEmits sunfish ⟨w, env⟩ ([.block [pB3]] ++ pre) ws st₂ := by
  refine GenEmits.silent
    (pre₁ := [GenFrame.block (planOrelse pB3), GenFrame.block ([] : List Stmt)] ++ pre)
    (fun k => by
      simpa using genSilent_branch (m := sunfish) (s := pB3) (b := false)
        (k := pre ++ k) pB3_plan (pB3_test_run w env jv false hloc hj hnoprom)
        (truthy_boolH w false)) ?_
  refine GenEmits.silent (pre₁ := [GenFrame.block ([] : List Stmt)] ++ pre)
    (fun k => by
      simpa [pB3_orelse] using genSilent_blockNil (m := sunfish) (st := ⟨w, env⟩)
        (k := GenFrame.block ([] : List Stmt) :: (pre ++ k))) ?_
  exact GenEmits.silent (pre₁ := pre)
    (fun k => by
      simpa using genSilent_blockNil (m := sunfish) (st := ⟨w, env⟩) (k := pre ++ k)) hrest

/-! ## A WHOLE RAY: the crawlers

`ray_stop_agrees` is one leaf of one round. This is the first COMPLETE ray
in the repo — every round, at every fuel, over an arbitrary board — and it
is what shows `ray_rounds` is usable rather than merely true.

The pieces it covers are the ones sunfish's own comment calls crawlers:
`p ∈ {'N', 'K'}`. They are exactly the pieces whose ray provably never
takes a second round, because `p in "PNK"` breaks it in the round it
starts — so the reference body is INDEPENDENT of its tail at every square,
`ray_rounds`' continuing case is vacuous, and the induction closes without
ever needing the statements past the crawler guard. (A slider needs those;
see the record at the end of this file.) -/

/-- **The reference's body ignores its tail, for a crawler.** Whatever is
at square `j` — off-board, blocker, capture, empty — the ray ends there, so
the body is the same whatever tail it is handed. This is what makes
`ray_rounds`' `hgo` unreachable below. -/
theorem rayBody_crawler_indep (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int)
    (p : Char) (d j : Int) (hnp : p ≠ 'P') (hcrawl : Ref.inStr p "PNK" = true)
    (t₁ t₂ : Except String (List Ref.RefMove)) :
    rayBody b wc0 wc1 ep kp i p d j t₁ = rayBody b wc0 wc1 ep kp i p d j t₂ := by
  unfold rayBody Ref.pawnBreak
  simp only [bind, Except.bind, bne_iff_ne, ne_eq, hnp, not_false_eq_true, if_pos,
    hcrawl, Bool.true_or]
  repeat' split <;> rfl

/-- A crawler's ray is ONE round: `Ref.ray` reports either nothing (the
square is a blocker) or exactly the one move to it. -/
theorem ray_crawler_leaf (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int)
    (p : Char) (d j : Int) (c : Char) (r : List Ref.RefMove)
    (href : Ref.at? b j = .ok c) (hnp : p ≠ 'P') (hcrawl : Ref.inStr p "PNK" = true)
    (hbody : ∀ t, rayBody b wc0 wc1 ep kp i p d j t = .ok r) :
    (Ref.inStr c " \nPNBRQK" = true ∧ r = []) ∨
    (Ref.inStr c " \nPNBRQK" = false ∧ r = [⟨i, j, ""⟩]) := by
  by_cases hstop : Ref.inStr c " \nPNBRQK" = true
  · exact Or.inl ⟨hstop, Except.ok.inj ((hbody (.ok [])).symm.trans
      (rayBody_stop_const b wc0 wc1 ep kp i p d j c href hstop (.ok [])))⟩
  · simp only [Bool.not_eq_true] at hstop
    exact Or.inr ⟨hstop, Except.ok.inj ((hbody (.ok [])).symm.trans
      (rayBody_break_const b wc0 wc1 ep kp i p d j c href hstop hnp
        (by rw [hcrawl]; rfl) (.ok [])))⟩

/-- **The model side of the round that ENDS a ray having moved**: the whole
ray body, from the loop frame's block down to the `break` at the crawler
guard, emitting the one move. Stated at the guard's own condition rather
than at `p in "PNK"`, so it serves a crawler and a CAPTURING slider alike —
they break at the same statement for the two different reasons. -/
theorem breaking_round (w : World) (env : REnv) (b : String)
    (score ep kp iv jv : Int) (wc0 wc1 bc0 bc1 : Bool) (p c : Char) (a : Addr)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p env)
    (hj : Env.lookup env "j" = some (.int jv))
    (href : Ref.at? b.toList jv = .ok c)
    (hopen : Ref.inStr c " \nPNBRQK" = false) (hnp : p ≠ 'P')
    (hbrk : (Ref.inStr p "PNK" || Ref.inStr c "pnbrqk") = true) :
    GenEmits sunfish ⟨w, env⟩
      [.block gmRay, .forGen gmRayTarget a gmRay] [moveVal ⟨iv, jv, ""⟩]
      ⟨w, Env.set env "q" (.str (String.singleton c))⟩ := by
  obtain ⟨hloc, hself, hi, hp⟩ := hframe
  have hq₁ : Env.lookup (Env.set env "q" (.str (String.singleton c))) "q"
      = some (.str (String.singleton c)) := Env.lookup_set_self _ _ _
  have hp₁ : Env.lookup (Env.set env "q" (.str (String.singleton c))) "p"
      = some (.str (String.singleton p)) := by
    rw [Env.lookup_set_ne _ (by decide)]; exact hp
  have hi₁ : Env.lookup (Env.set env "q" (.str (String.singleton c))) "i"
      = some (.int iv) := by rw [Env.lookup_set_ne _ (by decide)]; exact hi
  have hj₁ : Env.lookup (Env.set env "q" (.str (String.singleton c))) "j"
      = some (.int jv) := by rw [Env.lookup_set_ne _ (by decide)]; exact hj
  have hloc₁ : RayLocals (Env.set env "q" (.str (String.singleton c))) :=
    hloc.set (x := "q") (by decide) _
  refine q_falls (pre := [GenFrame.forGen gmRayTarget a gmRay])
    w env b score ep kp jv wc0 wc1 bc0 bc1 c hself hj href ?_
  refine stop_falls (pre := [GenFrame.forGen gmRayTarget a gmRay]) w _ c hq₁ hopen ?_
  refine pawn_skips (pre := [GenFrame.forGen gmRayTarget a gmRay]) w _ p hp₁ hnp ?_
  refine yield_emits (pre := [GenFrame.forGen gmRayTarget a gmRay])
    w _ iv jv hloc₁ hi₁ hj₁ ?_
  exact crawl_breaks w _ p c a hp₁ hq₁ hbrk

set_option maxHeartbeats 800000 in
/-- **RAY AGREEMENT FOR A CRAWLER, WHOLE, OVER AN ARBITRARY BOARD.**

A knight or a king, suspended in a ray at the `count` object holding `j`:
the shipped generator emits exactly the moves `Ref.ray` reports, for the
WHOLE ray at every fuel, and leaves the frame in a state the enclosing
scans can carry on from — `RayFrame` again, so `self`, `i` and `p` are
still bound and no module global is shadowed.

Board free, square free (negative-index fold included), character free,
world and frame free apart from the count object and the lookups the
statements perform. The first complete ray in the repo, and the first use
of `ray_rounds`. -/
theorem ray_crawl_agrees (w : World) (env : REnv) (a : Addr)
    (b : String) (score ep kp iv d : Int) (wc0 wc1 bc0 bc1 : Bool) (p : Char)
    (f : Nat) (jv : Int) (ms : List Ref.RefMove)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p env)
    (hcount : Heap.get? w.heap a = some (countObj jv d))
    (hnp : p ≠ 'P') (hcrawl : Ref.inStr p "PNK" = true)
    (hray : Ref.ray b.toList wc0 wc1 ep kp iv p d f jv = .ok ms) :
    ∃ st', RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p st'.locals ∧
      GenEmits sunfish ⟨w, env⟩ [.forGen gmRayTarget a gmRay]
        (ms.map moveVal) st' := by
  refine ray_rounds
    (Inv := fun j st => RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p st.locals ∧
      Heap.get? st.world.heap a = some (countObj j d))
    (Out := fun st => RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p st.locals)
    ?_ ?_ f jv ms ⟨w, env⟩ ⟨hframe, hcount⟩ hray
  -- the ray ENDS here: either the square is a blocker, or the crawler breaks
  · rintro j ⟨w₁, env₁⟩ r ⟨hfr, hcnt⟩ hbody
    obtain ⟨h₂, hback⟩ := Heap.update_of_get? (countObj (j + d) d) hcnt
    obtain ⟨sj, htgt⟩ := gmRayTarget_lit
    have hfr₁ : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p (Env.set env₁ "j" (.int j)) :=
      hfr.set (x := "j") (by decide) _
    have hj₁ : Env.lookup (Env.set env₁ "j" (.int j)) "j" = some (.int j) :=
      Env.lookup_set_self _ _ _
    -- the reference must have READ the square, or its body could not be `.ok`
    have hat : ∃ c, Ref.at? b.toList j = .ok c := by
      cases hr : Ref.at? b.toList j with
      | ok c => exact ⟨c, rfl⟩
      | error e =>
        exfalso
        have h := hbody (Except.error "unused")
        rw [rayBody] at h
        simp [bind, Except.bind, hr] at h
    obtain ⟨c, href⟩ := hat
    obtain ⟨hstop, rfl⟩ | ⟨hopen, rfl⟩ :=
      ray_crawler_leaf b.toList wc0 wc1 ep kp iv p d j c r href hnp hcrawl hbody
    · -- BLOCKER: nothing is emitted, but `q = self.board[j]` ran before the
      -- guard broke, so the frame the ray leaves has `q` bound
      refine ⟨⟨{ w₁ with heap := h₂ },
          Env.set (Env.set env₁ "j" (.int j)) "q" (.str (String.singleton c))⟩,
        hfr₁.set (x := "q") (by decide) _, ?_⟩
      refine GenEmits.forGenBreak (v := .int j) (w' := { w₁ with heap := h₂ })
        (env₁ := Env.set env₁ "j" (.int j)) (iterSteps_countFrom hcnt hback)
        (by rw [htgt]; rfl) ?_
      obtain ⟨hloc, hself, hi, hp⟩ := hfr₁
      simpa using q_falls (pre := [GenFrame.forGen gmRayTarget a gmRay])
        { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j)) b score ep kp j
        wc0 wc1 bc0 bc1 c hself hj₁ href
        (stop_breaks _ _ c a (Env.lookup_set_self _ _ _) hstop)
    · -- OPEN: the one move, then the crawler guard ends the ray
      refine ⟨⟨{ w₁ with heap := h₂ },
          Env.set (Env.set env₁ "j" (.int j)) "q" (.str (String.singleton c))⟩,
        hfr₁.set (x := "q") (by decide) _, ?_⟩
      refine GenEmits.forGenBreak (v := .int j) (w' := { w₁ with heap := h₂ })
        (env₁ := Env.set env₁ "j" (.int j)) (iterSteps_countFrom hcnt hback)
        (by rw [htgt]; rfl) ?_
      simpa using breaking_round { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j))
        b score ep kp iv j wc0 wc1 bc0 bc1 p c a hfr₁ hj₁ href hopen hnp
        (by rw [hcrawl]; rfl)
  -- the ray CONTINUES: unreachable, because a crawler's body ignores its tail
  · rintro j st pre _ hmap
    exfalso
    have h := rayBody_crawler_indep b.toList wc0 wc1 ep kp iv p d j hnp hcrawl
      (Except.ok []) (Except.ok [⟨iv, j, ""⟩])
    rw [hmap (Except.ok []), hmap (Except.ok [⟨iv, j, ""⟩])] at h
    simp only [Functor.map, Except.map] at h
    have h' : pre ++ ([] : List Ref.RefMove) = pre ++ [⟨iv, j, ""⟩] := Except.ok.inj h
    have hl := congrArg List.length h'
    simp at hl

/-! Non-vacuity, on the shipped opening board: the knight on 92 IS a
crawler and is not a pawn, so `ray_crawl_agrees` applies to it; and both
arms of its round are reachable — square 73 is empty (the ray yields and
then breaks) while square 84 holds our own pawn (the ray breaks at the stop
guard, yielding nothing). Neither branch of the theorem is vacuous. -/

#guard (match Ref.at? board0.toList 92 with | .ok c => c == 'N' | _ => false) == true
#guard Ref.inStr 'N' "PNK" == true
#guard ('N' != 'P') == true

#guard (match Ref.at? board0.toList 73 with
        | .ok c => Ref.inStr c " \nPNBRQK"
        | _ => true) == false

#guard (match Ref.at? board0.toList 84 with
        | .ok c => Ref.inStr c " \nPNBRQK"
        | _ => false) == true

/-! ## A WHOLE RAY: the sliders

The crawler's ray closes without ever running the statements past the
crawler guard, because it never takes a second round. A SLIDER does, and
those statements are the two castling `if`s — which is where the ray's last
tool-level obstacle sat (see `castA_test_false` for the mechanism and the
fix). With them stepping, the continuing round is the segment kit read
straight through, `ray_rounds`' `hgo` gets a real inhabitant instead of the
crawler's vacuous one, and the induction itself does not move: it was
stated against `rayBody_append_or_const`, not against the statements. -/

/-- **A slot reads back what was written to it** — the companion to
`Heap.update_of_get?` (VCGen.lean §L4), and the first thing a CONTINUING
loop needs that an ending one does not: a crawler's ray never re-reads the
count object, so the round invariant is re-established here for the first
time. -/
theorem heap_readback {h h' : Heap} {a : Addr} {o : Obj}
    (hu : Heap.update h a o = some h') : Heap.get? h' a = some o := by
  unfold Heap.update at hu
  split at hu
  · next hlt =>
      injection hu with hu
      subst hu
      rw [Heap.get?, dif_pos (by simpa using hlt)]
      simp
  · next => exact absurd hu (by simp)

/-- **The model side of a slider's CONTINUING round**: the whole ray body,
from the loop frame's block down to the empty block that pops, emitting the
one move and falling through so the loop goes round again. Eight segments
end to end, and the last three (`crawl_falls`, `castA_skips`/`castH_skips`,
`block_done`) are exactly the ones a crawler never reaches. -/
theorem slider_round (w : World) (env : REnv) (b : String)
    (score ep kp iv jv : Int) (wc0 wc1 bc0 bc1 : Bool) (p c : Char)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p env)
    (hj : Env.lookup env "j" = some (.int jv))
    (href : Ref.at? b.toList jv = .ok c)
    (hopen : Ref.inStr c " \nPNBRQK" = false) (hnp : p ≠ 'P')
    (hgo : (Ref.inStr p "PNK" || Ref.inStr c "pnbrqk") = false)
    (hA : iv ≠ Ref.A1) (hH : iv ≠ Ref.H1) :
    GenEmits sunfish ⟨w, env⟩ [.block gmRay] [moveVal ⟨iv, jv, ""⟩]
      ⟨w, Env.set env "q" (.str (String.singleton c))⟩ := by
  obtain ⟨hloc, hself, hi, hp⟩ := hframe
  have hq₁ : Env.lookup (Env.set env "q" (.str (String.singleton c))) "q"
      = some (.str (String.singleton c)) := Env.lookup_set_self _ _ _
  have hp₁ : Env.lookup (Env.set env "q" (.str (String.singleton c))) "p"
      = some (.str (String.singleton p)) := by
    rw [Env.lookup_set_ne _ (by decide)]; exact hp
  have hi₁ : Env.lookup (Env.set env "q" (.str (String.singleton c))) "i"
      = some (.int iv) := by rw [Env.lookup_set_ne _ (by decide)]; exact hi
  have hj₁ : Env.lookup (Env.set env "q" (.str (String.singleton c))) "j"
      = some (.int jv) := by rw [Env.lookup_set_ne _ (by decide)]; exact hj
  have hloc₁ : RayLocals (Env.set env "q" (.str (String.singleton c))) :=
    hloc.set (x := "q") (by decide) _
  have hdone : GenEmits sunfish ⟨w, Env.set env "q" (.str (String.singleton c))⟩
      ([.block []] ++ ([] : GenCont)) []
      ⟨w, Env.set env "q" (.str (String.singleton c))⟩ := by
    simpa using block_done ⟨w, Env.set env "q" (.str (String.singleton c))⟩
  simpa using
    q_falls w env b score ep kp jv wc0 wc1 bc0 bc1 c hself hj href
      (stop_falls w _ c hq₁ hopen
        (pawn_skips w _ p hp₁ hnp
          (yield_emits w _ iv jv hloc₁ hi₁ hj₁
            (crawl_falls w _ p c hp₁ hq₁ hgo
              (castA_skips w _ iv hloc₁ hi₁ hA
                (castH_skips w _ iv hloc₁ hi₁ hH hdone))))))

/-- **A non-corner slider's ray ENDS at `j` only two ways**: the square is a
blocker (nothing), or it holds an enemy piece (the one move). Anything else
and the body would have consumed its tail, which the constant hypothesis
forbids. -/
theorem ray_slider_leaf (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int)
    (p : Char) (d j : Int) (c : Char) (r : List Ref.RefMove)
    (href : Ref.at? b j = .ok c) (hnp : p ≠ 'P')
    (hslide : Ref.inStr p "PNK" = false) (hA : i ≠ Ref.A1) (hH : i ≠ Ref.H1)
    (hbody : ∀ t, rayBody b wc0 wc1 ep kp i p d j t = .ok r) :
    (Ref.inStr c " \nPNBRQK" = true ∧ r = []) ∨
    (Ref.inStr c " \nPNBRQK" = false ∧ Ref.inStr c "pnbrqk" = true ∧
      r = [⟨i, j, ""⟩]) := by
  by_cases hstop : Ref.inStr c " \nPNBRQK" = true
  · exact Or.inl ⟨hstop, Except.ok.inj ((hbody (.ok [])).symm.trans
      (rayBody_stop_const b wc0 wc1 ep kp i p d j c href hstop (.ok [])))⟩
  · simp only [Bool.not_eq_true] at hstop
    by_cases hcap : Ref.inStr c "pnbrqk" = true
    · exact Or.inr ⟨hstop, hcap, Except.ok.inj ((hbody (.ok [])).symm.trans
        (rayBody_break_const b wc0 wc1 ep kp i p d j c href hstop hnp
          (by rw [hcap]; exact Bool.or_true _) (.ok [])))⟩
    · simp only [Bool.not_eq_true] at hcap
      exact (rayBody_const_not_append b wc0 wc1 ep kp i p d j r [⟨i, j, ""⟩] hbody
        (rayBody_slide_map b wc0 wc1 ep kp i p d j c href hstop hnp
          (by rw [hslide, hcap]; rfl) hA hH)).elim

/-- **…and it CONTINUES only one way**: the square is empty of anything the
ray cares about, and what it prepends is the single move. The other
direction of `ray_slider_leaf`, and what discharges `ray_rounds`' `hgo`. -/
theorem ray_slider_go (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int)
    (p : Char) (d j : Int) (c : Char) (pre : List Ref.RefMove)
    (href : Ref.at? b j = .ok c) (hnp : p ≠ 'P')
    (hslide : Ref.inStr p "PNK" = false) (hA : i ≠ Ref.A1) (hH : i ≠ Ref.H1)
    (hmap : ∀ t, rayBody b wc0 wc1 ep kp i p d j t = (pre ++ ·) <$> t) :
    Ref.inStr c " \nPNBRQK" = false ∧ Ref.inStr c "pnbrqk" = false ∧
      pre = [⟨i, j, ""⟩] := by
  by_cases hstop : Ref.inStr c " \nPNBRQK" = true
  · exact (rayBody_const_not_append b wc0 wc1 ep kp i p d j [] pre
      (rayBody_stop_const b wc0 wc1 ep kp i p d j c href hstop) hmap).elim
  · simp only [Bool.not_eq_true] at hstop
    by_cases hcap : Ref.inStr c "pnbrqk" = true
    · exact (rayBody_const_not_append b wc0 wc1 ep kp i p d j [⟨i, j, ""⟩] pre
        (rayBody_break_const b wc0 wc1 ep kp i p d j c href hstop hnp
          (by rw [hcap]; exact Bool.or_true _)) hmap).elim
    · simp only [Bool.not_eq_true] at hcap
      refine ⟨hstop, hcap, ?_⟩
      have h := (hmap (.ok [])).symm.trans
        (rayBody_slide_map b wc0 wc1 ep kp i p d j c href hstop hnp
          (by rw [hslide, hcap]; rfl) hA hH (.ok []))
      simp only [Functor.map, Except.map] at h
      simpa using Except.ok.inj h

set_option maxHeartbeats 800000 in
/-- **RAY AGREEMENT FOR A SLIDER, WHOLE, OVER AN ARBITRARY BOARD.**

A bishop, rook or queen off the two castling squares, suspended in a ray at
the `count` object holding `j`: the shipped generator emits exactly the
moves `Ref.ray` reports, for the WHOLE ray at every fuel — sliding square
by square, stopping at the first blocker or capture — and leaves the frame
in a state the enclosing scans can carry on from.

This is the first ray in the repo that takes MORE THAN ONE round, so it is
the first use of `ray_rounds`' `hgo` and of `RayRound`'s composition; the
crawler theorem could close with that case vacuous. Board free, square
free, character free, direction free, fuel free.

`iv ≠ A1`/`iv ≠ H1` is a real restriction and not a technicality: on a
corner square the castling `and` chain reads the board a second time and
consults `self.wc`, which is the one `Ref.ray` leaf still open (the record
at the end of this file). Every OTHER slider on the board is covered. -/
theorem ray_slide_agrees (w : World) (env : REnv) (a : Addr)
    (b : String) (score ep kp iv d : Int) (wc0 wc1 bc0 bc1 : Bool) (p : Char)
    (f : Nat) (jv : Int) (ms : List Ref.RefMove)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p env)
    (hcount : Heap.get? w.heap a = some (countObj jv d))
    (hnp : p ≠ 'P') (hslide : Ref.inStr p "PNK" = false)
    (hA : iv ≠ Ref.A1) (hH : iv ≠ Ref.H1)
    (hray : Ref.ray b.toList wc0 wc1 ep kp iv p d f jv = .ok ms) :
    ∃ st', RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p st'.locals ∧
      GenEmits sunfish ⟨w, env⟩ [.forGen gmRayTarget a gmRay]
        (ms.map moveVal) st' := by
  refine ray_rounds
    (Inv := fun j st => RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p st.locals ∧
      Heap.get? st.world.heap a = some (countObj j d))
    (Out := fun st => RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p st.locals)
    ?_ ?_ f jv ms ⟨w, env⟩ ⟨hframe, hcount⟩ hray
  -- the ray ENDS here: a blocker, or a capture
  · rintro j ⟨w₁, env₁⟩ r ⟨hfr, hcnt⟩ hbody
    obtain ⟨h₂, hback⟩ := Heap.update_of_get? (countObj (j + d) d) hcnt
    obtain ⟨sj, htgt⟩ := gmRayTarget_lit
    have hfr₁ : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p (Env.set env₁ "j" (.int j)) :=
      hfr.set (x := "j") (by decide) _
    have hj₁ : Env.lookup (Env.set env₁ "j" (.int j)) "j" = some (.int j) :=
      Env.lookup_set_self _ _ _
    have hat : ∃ c, Ref.at? b.toList j = .ok c := by
      cases hr : Ref.at? b.toList j with
      | ok c => exact ⟨c, rfl⟩
      | error e =>
        exfalso
        have h := hbody (Except.error "unused")
        rw [rayBody] at h
        simp [bind, Except.bind, hr] at h
    obtain ⟨c, href⟩ := hat
    obtain ⟨hstop, rfl⟩ | ⟨hopen, hcap, rfl⟩ :=
      ray_slider_leaf b.toList wc0 wc1 ep kp iv p d j c r href hnp hslide hA hH hbody
    · -- BLOCKER: nothing is emitted, and the frame carries the `q` that was read
      refine ⟨⟨{ w₁ with heap := h₂ },
          Env.set (Env.set env₁ "j" (.int j)) "q" (.str (String.singleton c))⟩,
        hfr₁.set (x := "q") (by decide) _, ?_⟩
      refine GenEmits.forGenBreak (v := .int j) (w' := { w₁ with heap := h₂ })
        (env₁ := Env.set env₁ "j" (.int j)) (iterSteps_countFrom hcnt hback)
        (by rw [htgt]; rfl) ?_
      obtain ⟨hloc, hself, hi, hp⟩ := hfr₁
      simpa using q_falls (pre := [GenFrame.forGen gmRayTarget a gmRay])
        { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j)) b score ep kp j
        wc0 wc1 bc0 bc1 c hself hj₁ href
        (stop_breaks _ _ c a (Env.lookup_set_self _ _ _) hstop)
    · -- CAPTURE: the one move, and the crawler guard ends the slide behind it
      refine ⟨⟨{ w₁ with heap := h₂ },
          Env.set (Env.set env₁ "j" (.int j)) "q" (.str (String.singleton c))⟩,
        hfr₁.set (x := "q") (by decide) _, ?_⟩
      refine GenEmits.forGenBreak (v := .int j) (w' := { w₁ with heap := h₂ })
        (env₁ := Env.set env₁ "j" (.int j)) (iterSteps_countFrom hcnt hback)
        (by rw [htgt]; rfl) ?_
      simpa using breaking_round { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j))
        b score ep kp iv j wc0 wc1 bc0 bc1 p c a hfr₁ hj₁ href hopen hnp
        (by rw [hcap]; exact Bool.or_true _)
  -- the ray CONTINUES: the one move, the count advances, the invariant holds
  · rintro j ⟨w₁, env₁⟩ pre ⟨hfr, hcnt⟩ hmap
    obtain ⟨h₂, hback⟩ := Heap.update_of_get? (countObj (j + d) d) hcnt
    obtain ⟨sj, htgt⟩ := gmRayTarget_lit
    have hfr₁ : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 p (Env.set env₁ "j" (.int j)) :=
      hfr.set (x := "j") (by decide) _
    have hj₁ : Env.lookup (Env.set env₁ "j" (.int j)) "j" = some (.int j) :=
      Env.lookup_set_self _ _ _
    have hat : ∃ c, Ref.at? b.toList j = .ok c := by
      cases hr : Ref.at? b.toList j with
      | ok c => exact ⟨c, rfl⟩
      | error e =>
        exfalso
        have h := hmap (Except.ok [])
        rw [rayBody] at h
        simp [bind, Except.bind, hr, Functor.map, Except.map] at h
    obtain ⟨c, href⟩ := hat
    obtain ⟨hopen, hcap, rfl⟩ :=
      ray_slider_go b.toList wc0 wc1 ep kp iv p d j c pre href hnp hslide hA hH hmap
    refine ⟨⟨{ w₁ with heap := h₂ },
        Env.set (Env.set env₁ "j" (.int j)) "q" (.str (String.singleton c))⟩,
      ⟨hfr₁.set (x := "q") (by decide) _, heap_readback hback⟩, ?_⟩
    refine RayRound.intro (v := .int j) (w' := { w₁ with heap := h₂ })
      (env₁ := Env.set env₁ "j" (.int j)) (iterSteps_countFrom hcnt hback)
      (by rw [htgt]; rfl) ?_
    simpa using slider_round { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j))
      b score ep kp iv j wc0 wc1 bc0 bc1 p c hfr₁ hj₁ href hopen hnp
      (by rw [hslide, hcap]; rfl) hA hH

/-! Non-vacuity for the slider, on the shipped opening board: the queen on
94 is a slider, is not a pawn, and is on neither castling square, so
`ray_slide_agrees` applies to it — and all THREE arms of its round are
reachable as squares of that board: 84 is our own pawn (blocker), 74 is
empty (the ray slides on), 24 is the enemy queen (capture). -/

#guard (match Ref.at? board0.toList 94 with | .ok c => c == 'Q' | _ => false) == true
#guard (Ref.inStr 'Q' "PNK" == false) && ('Q' != 'P') && (94 != Ref.A1) && (94 != Ref.H1)

#guard (match Ref.at? board0.toList 84 with
        | .ok c => Ref.inStr c " \nPNBRQK"
        | _ => false) == true

#guard (match Ref.at? board0.toList 74 with
        | .ok c => !Ref.inStr c " \nPNBRQK" && !Ref.inStr c "pnbrqk"
        | _ => false) == true

#guard (match Ref.at? board0.toList 24 with
        | .ok c => !Ref.inStr c " \nPNBRQK" && Ref.inStr c "pnbrqk"
        | _ => false) == true

/-! ## A WHOLE RAY: the pawn's push

The third and last shape of ray. A pawn is a crawler in `sunfish`'s own
sense (`p in "PNK"` breaks its ray where it starts) but it is the only
piece whose ray runs the pawn BLOCK first, so the crawler theorem does not
cover it: `rayBody_crawler_indep` and `ray_crawler_leaf` both assume
`p ≠ 'P'` precisely because `pawnBreak` is where a pawn differs.

What lands here is the SINGLE PUSH, `d = N`. That direction decides three
of the block's four guards by itself, so the two expensive reads the pawn
block can perform — `self.board[i + N]` for the double move, `self.ep` and
`self.kp` for the captures — are provably never reached, and the round is
the segment kit again. -/

open Ref in
/-- **A pawn's body ignores its tail** — the crawler fact for the piece the
crawler fact excludes. Whatever the pawn block decides, and whatever is at
the square, `p in "PNK"` holds for `'P'`, so the ray ends in the round it
starts and the body is the same at every tail. -/
theorem rayBody_pawn_indep (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int) (d j : Int)
    (t₁ t₂ : Except String (List RefMove)) :
    rayBody b wc0 wc1 ep kp i 'P' d j t₁ = rayBody b wc0 wc1 ep kp i 'P' d j t₂ := by
  unfold rayBody
  simp only [bind, Except.bind, show inStr 'P' "PNK" = true from rfl, Bool.true_or, if_true]
  repeat' split <;> rfl

open Ref in
/-- The push is BLOCKED: the square ahead is on the board and not empty, so
the pawn block breaks with nothing. -/
theorem rayBody_pawn_block_const (b : List Char) (wc0 wc1 : Bool) (ep kp i j : Int) (c : Char)
    (href : at? b j = .ok c) (hopen : inStr c " \nPNBRQK" = false) (hne : c ≠ '.') :
    ∀ t, rayBody b wc0 wc1 ep kp i 'P' N j t = .ok [] := by
  intro t
  have hc : (c != '.') = true := by simpa using hne
  unfold rayBody pawnBreak
  simp [bind, Except.bind, href, hopen, hc, pure, Except.pure]

open Ref in
/-- The push is CLEAR and not a promotion: exactly the one quiet move. -/
theorem rayBody_pawn_move_const (b : List Char) (wc0 wc1 : Bool) (ep kp i j : Int)
    (href : at? b j = .ok '.')
    (hnoprom : (decide (A8 ≤ j) && decide (j ≤ H8)) = false) :
    ∀ t, rayBody b wc0 wc1 ep kp i 'P' N j t = .ok [⟨i, j, ""⟩] := by
  intro t
  have h1 : ¬ (A8 ≤ j ∧ j ≤ H8) := fun h => by simp [h.1, h.2] at hnoprom
  have hop : inStr '.' " \nPNBRQK" = false := rfl
  have hcr : inStr 'P' "PNK" = true := rfl
  unfold rayBody pawnBreak
  simp [bind, Except.bind, href, hop, hcr, h1, pure, Except.pure, N, W, E]

open Ref in
/-- **A non-promoting single push ends the ray in exactly three ways**: the
square is off the board or ours (nothing), it holds an enemy piece
(nothing — a pawn does not capture forwards), or it is empty (the one quiet
move). -/
theorem ray_pawn_leaf (b : List Char) (wc0 wc1 : Bool) (ep kp i j : Int) (c : Char)
    (r : List RefMove) (href : at? b j = .ok c)
    (hnoprom : (decide (A8 ≤ j) && decide (j ≤ H8)) = false)
    (hbody : ∀ t, rayBody b wc0 wc1 ep kp i 'P' N j t = .ok r) :
    (inStr c " \nPNBRQK" = true ∧ r = []) ∨
    (inStr c " \nPNBRQK" = false ∧ c ≠ '.' ∧ r = []) ∨
    (c = '.' ∧ r = [⟨i, j, ""⟩]) := by
  by_cases hstop : inStr c " \nPNBRQK" = true
  · exact Or.inl ⟨hstop, Except.ok.inj ((hbody (.ok [])).symm.trans
      (rayBody_stop_const b wc0 wc1 ep kp i 'P' N j c href hstop (.ok [])))⟩
  · simp only [Bool.not_eq_true] at hstop
    by_cases hdot : c = '.'
    · subst hdot
      exact Or.inr (Or.inr ⟨rfl, Except.ok.inj ((hbody (.ok [])).symm.trans
        (rayBody_pawn_move_const b wc0 wc1 ep kp i j href hnoprom (.ok [])))⟩)
    · exact Or.inr (Or.inl ⟨hstop, hdot, Except.ok.inj ((hbody (.ok [])).symm.trans
        (rayBody_pawn_block_const b wc0 wc1 ep kp i j c href hstop hdot (.ok [])))⟩)

/-- **The model side of a BLOCKED push**: into the pawn block and out again
through its first guard, emitting nothing. -/
theorem pawn_blocked_round (w : World) (env : REnv) (b : String)
    (score ep kp iv jv : Int) (wc0 wc1 bc0 bc1 : Bool) (c : Char) (a : Addr)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' env)
    (hd : Env.lookup env "d" = some (.int Ref.N))
    (hj : Env.lookup env "j" = some (.int jv))
    (href : Ref.at? b.toList jv = .ok c)
    (hopen : Ref.inStr c " \nPNBRQK" = false) (hne : c ≠ '.') :
    GenEmits sunfish ⟨w, env⟩
      [.block gmRay, .forGen gmRayTarget a gmRay] []
      ⟨w, Env.set env "q" (.str (String.singleton c))⟩ := by
  obtain ⟨hloc, hself, hi, hp⟩ := hframe
  have hq₁ : Env.lookup (Env.set env "q" (.str (String.singleton c))) "q"
      = some (.str (String.singleton c)) := Env.lookup_set_self _ _ _
  have hp₁ : Env.lookup (Env.set env "q" (.str (String.singleton c))) "p"
      = some (.str (String.singleton 'P')) := by
    rw [Env.lookup_set_ne _ (by decide)]; exact hp
  have hd₁ : Env.lookup (Env.set env "q" (.str (String.singleton c))) "d"
      = some (.int Ref.N) := by rw [Env.lookup_set_ne _ (by decide)]; exact hd
  have hloc₁ : RayLocals (Env.set env "q" (.str (String.singleton c))) :=
    hloc.set (x := "q") (by decide) _
  refine q_falls (pre := [GenFrame.forGen gmRayTarget a gmRay])
    w env b score ep kp jv wc0 wc1 bc0 bc1 c hself hj href ?_
  refine stop_falls (pre := [GenFrame.forGen gmRayTarget a gmRay]) w _ c hq₁ hopen ?_
  refine pawn_enters (pre := [GenFrame.forGen gmRayTarget a gmRay]) w _ hp₁ ?_
  exact pB0_breaks w _ c a hloc₁ hd₁ hq₁ hne

/-- **The model side of a QUIET PUSH**: through all four statements of the
pawn block, out the bottom of it, and on to the unconditional `yield` — nine
segments, and the ray ends at the crawler guard because a pawn is one. -/
theorem pawn_push_round (w : World) (env : REnv) (b : String)
    (score ep kp iv jv : Int) (wc0 wc1 bc0 bc1 : Bool) (a : Addr)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' env)
    (hd : Env.lookup env "d" = some (.int Ref.N))
    (hj : Env.lookup env "j" = some (.int jv))
    (href : Ref.at? b.toList jv = .ok '.')
    (hnoprom : (decide (Ref.A8 ≤ jv) && decide (jv ≤ Ref.H8)) = false) :
    GenEmits sunfish ⟨w, env⟩
      [.block gmRay, .forGen gmRayTarget a gmRay] [moveVal ⟨iv, jv, ""⟩]
      ⟨w, Env.set env "q" (.str (String.singleton '.'))⟩ := by
  obtain ⟨hloc, hself, hi, hp⟩ := hframe
  have hq₁ : Env.lookup (Env.set env "q" (.str (String.singleton '.'))) "q"
      = some (.str (String.singleton '.')) := Env.lookup_set_self _ _ _
  have hp₁ : Env.lookup (Env.set env "q" (.str (String.singleton '.'))) "p"
      = some (.str (String.singleton 'P')) := by
    rw [Env.lookup_set_ne _ (by decide)]; exact hp
  have hi₁ : Env.lookup (Env.set env "q" (.str (String.singleton '.'))) "i"
      = some (.int iv) := by rw [Env.lookup_set_ne _ (by decide)]; exact hi
  have hj₁ : Env.lookup (Env.set env "q" (.str (String.singleton '.'))) "j"
      = some (.int jv) := by rw [Env.lookup_set_ne _ (by decide)]; exact hj
  have hd₁ : Env.lookup (Env.set env "q" (.str (String.singleton '.'))) "d"
      = some (.int Ref.N) := by rw [Env.lookup_set_ne _ (by decide)]; exact hd
  have hloc₁ : RayLocals (Env.set env "q" (.str (String.singleton '.'))) :=
    hloc.set (x := "q") (by decide) _
  refine q_falls (pre := [GenFrame.forGen gmRayTarget a gmRay])
    w env b score ep kp jv wc0 wc1 bc0 bc1 '.' hself hj href ?_
  refine stop_falls (pre := [GenFrame.forGen gmRayTarget a gmRay]) w _ '.' hq₁ rfl ?_
  refine pawn_enters (pre := [GenFrame.forGen gmRayTarget a gmRay]) w _ hp₁ ?_
  refine pB0_falls (pre := [GenFrame.block [rYield, rCrawl, rCastA, rCastH],
    GenFrame.forGen gmRayTarget a gmRay]) w _ hloc₁ hd₁ hq₁ ?_
  refine pB1_falls (pre := [GenFrame.block [rYield, rCrawl, rCastA, rCastH],
    GenFrame.forGen gmRayTarget a gmRay]) w _ hloc₁ hd₁ ?_
  refine pB2_falls (pre := [GenFrame.block [rYield, rCrawl, rCastA, rCastH],
    GenFrame.forGen gmRayTarget a gmRay]) w _ hloc₁ hd₁ ?_
  refine pB3_skips (pre := [GenFrame.block [rYield, rCrawl, rCastA, rCastH],
    GenFrame.forGen gmRayTarget a gmRay]) w _ jv hloc₁ hj₁ hnoprom ?_
  refine yield_emits (pre := [GenFrame.forGen gmRayTarget a gmRay])
    w _ iv jv hloc₁ hi₁ hj₁ ?_
  exact crawl_breaks w _ 'P' '.' a hp₁ hq₁ rfl

set_option maxHeartbeats 800000 in
/-- **RAY AGREEMENT FOR A PAWN'S PUSH, WHOLE, OVER AN ARBITRARY BOARD.**

A pawn suspended in its `d = N` ray at the `count` object holding `j`, on a
square that is not the last row: the shipped generator emits exactly the
moves `Ref.ray` reports — the one quiet move, or nothing if the square
ahead is occupied — and leaves the frame in a state the enclosing scans can
carry on from.

The third ray shape and the first that runs the pawn block. Board free,
square free, character free, fuel free; `self.ep`, `self.kp` and the second
board read are provably never consulted, because at `d = N` each of their
guards short-circuits on the direction. `d`'s binding joins the round
invariant — the ray's other two shapes never read it. -/
theorem ray_pawn_push_agrees (w : World) (env : REnv) (a : Addr)
    (b : String) (score ep kp iv : Int) (wc0 wc1 bc0 bc1 : Bool)
    (f : Nat) (jv : Int) (ms : List Ref.RefMove)
    (hframe : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' env)
    (hcount : Heap.get? w.heap a = some (countObj jv Ref.N))
    (hd : Env.lookup env "d" = some (.int Ref.N))
    (hnoprom : (decide (Ref.A8 ≤ jv) && decide (jv ≤ Ref.H8)) = false)
    (hray : Ref.ray b.toList wc0 wc1 ep kp iv 'P' Ref.N f jv = .ok ms) :
    ∃ st', RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' st'.locals ∧
      GenEmits sunfish ⟨w, env⟩ [.forGen gmRayTarget a gmRay]
        (ms.map moveVal) st' := by
  refine ray_rounds
    (Inv := fun j st => RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' st.locals ∧
      Heap.get? st.world.heap a = some (countObj j Ref.N) ∧
      Env.lookup st.locals "d" = some (.int Ref.N) ∧
      (decide (Ref.A8 ≤ j) && decide (j ≤ Ref.H8)) = false)
    (Out := fun st => RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' st.locals)
    ?_ ?_ f jv ms ⟨w, env⟩ ⟨hframe, hcount, hd, hnoprom⟩ hray
  · rintro j ⟨w₁, env₁⟩ r ⟨hfr, hcnt, hdd, hnpr⟩ hbody
    obtain ⟨h₂, hback⟩ := Heap.update_of_get? (countObj (j + Ref.N) Ref.N) hcnt
    obtain ⟨sj, htgt⟩ := gmRayTarget_lit
    have hfr₁ : RayFrame b score ep kp iv wc0 wc1 bc0 bc1 'P' (Env.set env₁ "j" (.int j)) :=
      hfr.set (x := "j") (by decide) _
    have hj₁ : Env.lookup (Env.set env₁ "j" (.int j)) "j" = some (.int j) :=
      Env.lookup_set_self _ _ _
    have hd₁ : Env.lookup (Env.set env₁ "j" (.int j)) "d" = some (.int Ref.N) := by
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
      hfr₁.set (x := "q") (by decide) _, ?_⟩
    refine GenEmits.forGenBreak (v := .int j) (w' := { w₁ with heap := h₂ })
      (env₁ := Env.set env₁ "j" (.int j)) (iterSteps_countFrom hcnt hback)
      (by rw [htgt]; rfl) ?_
    obtain ⟨hstop, rfl⟩ | ⟨hopen, hne, rfl⟩ | ⟨rfl, rfl⟩ :=
      ray_pawn_leaf b.toList wc0 wc1 ep kp iv j c r href hnpr hbody
    · -- OFF THE BOARD or one of ours: the stop guard ends it, as for any piece
      obtain ⟨hloc, hself, hi, hp⟩ := hfr₁
      simpa using q_falls (pre := [GenFrame.forGen gmRayTarget a gmRay])
        { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j)) b score ep kp j
        wc0 wc1 bc0 bc1 c hself hj₁ href
        (stop_breaks _ _ c a (Env.lookup_set_self _ _ _) hstop)
    · -- AN ENEMY PIECE straight ahead: the pawn block breaks, no move
      simpa using pawn_blocked_round { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j))
        b score ep kp iv j wc0 wc1 bc0 bc1 c a hfr₁ hd₁ hj₁ href hopen hne
    · -- EMPTY: the one quiet move
      simpa using pawn_push_round { w₁ with heap := h₂ } (Env.set env₁ "j" (.int j))
        b score ep kp iv j wc0 wc1 bc0 bc1 a hfr₁ hd₁ hj₁ href hnpr
  -- a pawn never slides, so the continuing case is vacuous
  · rintro j st pre _ hmap
    exfalso
    have h := rayBody_pawn_indep b.toList wc0 wc1 ep kp iv Ref.N j
      (Except.ok []) (Except.ok [⟨iv, j, ""⟩])
    rw [hmap (Except.ok []), hmap (Except.ok [⟨iv, j, ""⟩])] at h
    simp only [Functor.map, Except.map] at h
    have h' : pre ++ ([] : List Ref.RefMove) = pre ++ [⟨iv, j, ""⟩] := Except.ok.inj h
    have hl := congrArg List.length h'
    simp at hl

/-! Non-vacuity for the pawn, on the shipped opening board: 84 holds a pawn
of ours, its single push lands on 74, which is empty and is not the last
row — so the quiet-move arm is reachable. The other two arms are reachable
as characters of that same board: 94 is our own queen (the stop guard ends
the ray) and 34 is an enemy pawn (on the board, not empty, so the pawn
block breaks). -/

#guard (match Ref.at? board0.toList 84 with | .ok c => c == 'P' | _ => false) == true
#guard (match Ref.at? board0.toList 74 with | .ok c => c == '.' | _ => false) == true
#guard ((decide (Ref.A8 ≤ (74 : Int)) && decide ((74 : Int) ≤ Ref.H8)) == false) == true

#guard (match Ref.at? board0.toList 94 with
        | .ok c => Ref.inStr c " \nPNBRQK"
        | _ => false) == true

#guard (match Ref.at? board0.toList 34 with
        | .ok c => !Ref.inStr c " \nPNBRQK" && (c != '.')
        | _ => false) == true

/-! ## What is left

Recorded rather than attempted, so the next session starts from a measured
position instead of a blank page.

**Counted honestly, FOUR of `Ref.ray`'s nine leaves are discharged** — and
they are the four that carry three whole ray shapes end to end
(`ray_crawl_agrees`, `ray_slide_agrees`, `ray_pawn_push_agrees`):

* the stop guard, a blocked square — every shape reaches it;
* the crawler guard, at both of its reasons: a piece that does not slide
  (`ray_crawl_agrees`) and a capture that ends one (`ray_slide_agrees`);
* the CONTINUING leaf, which is the one the round induction exists for;
* the pawn block's first guard, a push into an occupied square.

The five that remain are all pawn-or-corner leaves, and none of them needs a
new judgment, a new frame rule, or a tactic change — the kit that carries
three ray shapes carries these too:

**The castling YIELD** (`Ref.ray`'s ninth leaf). On a corner square the
`and` chain does not short-circuit: it reads `self.board[j + E]` — an
`rQ_run`-shaped fact at a shifted index — and then `self.wc[0]`, a tuple
subscript of a namedtuple FIELD, and on success `yield Move(j + E, j - E,
"")`. That is the only ray statement in the file whose taken arm has never
been run. It is what `iv ≠ A1`/`iv ≠ H1` buys in `ray_slide_agrees`, and it
is the reason a rook that has not moved is out of scope while every other
slider is in.

**The pawn's other three directions and its promotion** — four leaves.
`d = N` is one of `directions['P']`'s four entries, and the three that
remain are exactly the three that reach the reads the single push
short-circuits away:
* `d = N + N` runs the double-move guard, so it needs a SECOND
  `rQ_run`-shaped board read at `i + N` under an `or` — the first statement
  in the ray that reads the board twice;
* `d = N + W` and `d = N + E` run the capture guard, which compares against
  `self.ep` and calls `abs(j - self.kp)` — namedtuple FIELDS, so they are
  not exposed to the module-global defect `castA_test_false` records, but
  `abs` is a builtin call inside a comparison chain and is new here;
* the promotion arm (`A8 <= j <= H8`) is `for prom in "NBRQ": yield
  Move(i, j, prom)` — a `forSeq` frame over a string literal, so
  `GenEmits.forSeq` already covers the loop and `GenEmits.blockBreak` the
  `break` behind it; `pB3_test_run` already supplies its guard at both truth
  values, so what is missing is the four-element `forSeq` invariant and
  `Move(i, j, prom)` at a symbolic `prom`.

The counting matters because it is the honest shape of what is left: the
CALCULUS half of L4 is finished (the round induction, the segment kit, the
reference trichotomy, three whole rays), and the remainder is five more
captured runs of statements whose shapes are all precedented. -/

end Examples.python.sunfish.genmoves_ray
