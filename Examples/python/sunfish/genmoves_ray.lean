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

/-- The crawler guard falls through: a slider keeps going. Landed for the
slider rounds, which `castA_test_false` still blocks (see the record at the
end of this file). -/
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

/-- A finished block frame pops, at `GenEmits` altitude. -/
theorem block_done (st : FrameState) : GenEmits sunfish st [.block []] [] st :=
  GenEmits.silent (pre₁ := ([] : GenCont))
    (fun k => by simpa using genSilent_blockNil (m := sunfish) (st := st) (k := k))
    GenEmits.nil

end Examples.python.sunfish.genmoves_ray
