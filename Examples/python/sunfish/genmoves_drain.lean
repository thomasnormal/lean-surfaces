/-
**The generator as an OBJECT** — the last step of the `gen_moves` arc.

`genmoves_scan.lean` finished the suspended MACHINE: from the frame stack the
interpreter builds for `Position.gen_moves`, over an arbitrary board, the
machine yields exactly `Ref.refMoves`' moves in `Ref.refMoves`' order
(`gen_moves_yields_ref`). A consumer never sees that machine. It CALLS the
method, gets a heap object back, and drains it — `sorted(…)` and
`max(…)`/`min(…)` through `drainIter`, a `for` through `stepIter`.

This file is that one level out, and it is one theorem:
**`gen_moves_drains_ref`** — call the shipped `Position.gen_moves` on any
Position value, drain the object it answered, and the values that come out
are the reference's moves in the reference's order, at every fuel above a
threshold shared by the call and the drain.

**What it rests on, and it is no longer a hypothesis.** The lockstep the
bridge needs is `PayloadBlind sunfish`: the interpreter cannot observe the
payload of a RUNNING generator object. `stepIter` writes the resumption into
the generator's own slot before every step and the frame-level chain never
writes it, so the two chains sit at heaps differing exactly there. §L7
PROVED it (LeanModels/Python/PayloadBlind.lean, `payloadBlind`), so this
theorem takes no hypothesis at all: its `#print axioms` is
`propext`/`Classical.choice`/`Quot.sound`, and there is nothing left in its
signature for a reader to discount.

**And `GenMovesEqRef`, since 2026-08-19.** This file used to end by saying it
was not the frozen statement (genmoves_theorem.lean) and deliberately did not
touch it: that statement drained through its own `drain`, which ran every step
at the CONSTANT fuel 16384 while quantifying over an arbitrary board, and was
therefore false as written (genmoves_scan.lean's closing section has the
counterexample — a board long enough that one step cannot cross it). The owner
ruled the one-line repair — `drain` takes `F`, which is what that statement's
own note 4 always said `genMovesOf` does — so the last section here transports
`gen_moves_drains_ref` into the repaired statement's shape
(`drain_of_drainIter`) and states the flagship itself
(`gen_moves_eq_ref_of_dirs`). Its two remaining hypotheses are GROUND facts
about `initWorld sunfish`, and the reason they are hypotheses is the module
INITIALIZER rather than the generator — measured, with numbers, in that
section.
-/
import Examples.python.sunfish.genmoves_scan

namespace Examples.python.sunfish.genmoves_drain

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.pins_genmoves
open Examples.python.sunfish.genmoves_theorem
open Examples.python.sunfish.genmoves_ray
open Examples.python.sunfish.genmoves_scan

/-! ## The method, projected

Never retyped: `gm_lit` reads the shipped function out of `sunfish` and every
component the call rule needs — the parameter checks, the generator flag, the
call environment, the body — is `rfl` on that projection, so a changed
PROGRAM stops it loudly. -/

/-- The shipped `Position.gen_moves` and the five facts `callIn`'s creation
arm tests, plus the two shapes the frame-level theorem is stated in: the call
environment is `self` alone, and the body is `gmB`. -/
theorem gm_lit : ∃ f, findFunction sunfish "Position.gen_moves" = some f ∧
    f.argsOk = true ∧ f.localsOk = true ∧ arityOk f.params 1 = true ∧
    f.isGenerator = true ∧ (∀ p : RVal, mkCallEnv f.params #[p] = [("self", p)]) ∧
    f.body.toList = gmB :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩

/-- The object the CALL allocates: `gen_moves` suspended at its own body,
with the receiver bound and nothing run yet. -/
def gmObj (p : RVal) : Obj :=
  .generator "Position.gen_moves" [("self", p)] [.block gmB] .created

/-- The world the call leaves: one object, at the heap's END (which is why
its address is the old `heap.size`). -/
def gmWorld (w : World) (p : RVal) : World :=
  { w with heap := w.heap.push (gmObj p) }

/-- **Calling the shipped `Position.gen_moves` runs no code and allocates its
generator** — `callIn_genCall` at the projected function, with the object
spelled out rather than left as `genObj`. -/
theorem gm_call (w : World) (p : RVal) (F : Nat) :
    callIn sunfish (F + 1) w "Position.gen_moves" #[p]
      = .ok (gmWorld w p) (.ref w.heap.size) := by
  obtain ⟨f, hf, hargs, hlocals, harity, hgen, henv, hbody⟩ := gm_lit
  rw [callIn_genCall hf hargs hlocals (by simpa using harity) hgen]
  simp only [gmWorld, gmObj, genObj, henv, hbody]

/-! ## The agreement, at the object level -/

/-- **THE OBJECT-LEVEL AGREEMENT.** For every position the reference
enumeration has an answer for, the shipped `Position.gen_moves` — CALLED on
the shipped file under the Lean semantics, and the generator it answers
DRAINED to exhaustion — hands over exactly the reference's moves, in the
reference's order, at every fuel above one threshold for both halves.

Board free (an arbitrary `String`), rights/ep/kp free, the reference's own
step budget free, and the starting world free: the two world hypotheses are
the module-global `directions` dict, exactly as `gen_moves_yields_ref` takes
them (`initWorld sunfish` satisfies both — `#guard`ed in genmoves_scan.lean).

The exit world is existential. A drain's last act is to mark its own object
`.closed`, and no consumer of the VALUES has to name that bookkeeping. -/
theorem gen_moves_drains_ref (w : World) (dad : Addr)
    (b : String) (score ep kp : Int) (wc0 wc1 bc0 bc1 : Bool) (rf : Nat)
    (ms : List Ref.RefMove)
    (hg : Env.lookup w.globals "directions" = some (.ref dad))
    (hdirs : Heap.get? w.heap dad = some dirsObj)
    (href : Ref.refMoves b.toList wc0 wc1 ep kp rf = .ok ms) :
    ∃ w', ∃ t, ∀ F ≥ t,
      callIn sunfish F w "Position.gen_moves"
          #[posOf b score wc0 wc1 bc0 bc1 ep kp]
        = .ok (gmWorld w (posOf b score wc0 wc1 bc0 bc1 ep kp)) (.ref w.heap.size) ∧
      drainIter sunfish F (gmWorld w (posOf b score wc0 wc1 bc0 bc1 ep kp))
          w.heap.size = .ok w' (ms.map moveVal) := by
  obtain ⟨f, hf, hargs, hlocals, harity, hgen, henv, hbody⟩ := gm_lit
  have hdlt : dad < w.heap.size := Heap.lt_size_of_get? hdirs
  -- the frame-level agreement, at the world the stepper enters the body in:
  -- the object is on the heap and already flipped to `.running`
  obtain ⟨st', hy⟩ := gen_moves_yields_ref
    { w with heap := w.heap.push (.generator "Position.gen_moves"
      [("self", posOf b score wc0 wc1 bc0 bc1 ep kp)] [.block gmB] .running) }
    dad b score ep kp wc0 wc1 bc0 bc1 rf ms hg
    (by rw [show ({ w with heap := w.heap.push (.generator "Position.gen_moves"
        [("self", posOf b score wc0 wc1 bc0 bc1 ep kp)] [.block gmB] .running) } : World).heap
          = w.heap.push _ from rfl, Heap.get?_push_lt hdlt]; exact hdirs) href
  obtain ⟨w', t, hcd⟩ := callIn_drains (m := sunfish) (w := w)
    (fname := "Position.gen_moves") (args := #[posOf b score wc0 wc1 bc0 bc1 ep kp])
    (vs := ms.map moveVal) (st' := st') hf hargs hlocals
    (by simpa using harity) hgen (by simpa only [henv, hbody] using hy)
  exact ⟨w', t, fun F hF => by
    simpa only [gmWorld, gmObj, genObj, henv, hbody] using hcd F hF⟩

/-! ## `GenMovesEqRef`, repaired — and proved from two ground facts

`GenMovesEqRef` (genmoves_theorem.lean) is the theorem above read one notch
closer to a reader: an `Option` of `Move` triples instead of `drainIter`'s
`Run`, and `initWorld sunfish` instead of an arbitrary starting world. It was
frozen with a defect — every drain step ran at the constant fuel `16384`
while the statement quantified over an arbitrary board, so a board no single
step can cross made it FALSE. THE REPAIR IS MADE (owner-decided, 2026-08-19,
and it is the statement's own note 4): `drain` takes `F`. With it, the
statement is this file's content in another shape, and what remains is
transport. -/

/-- `drain`'s equation at a successor, written out and proved by `rfl`.

Lean cannot GENERATE `drain`'s equational theorems: the frozen definition
matches an ARRAY LITERAL (`#[.int i, .int j, .str p]`), whose splitter goes
through `Array.getLit` under a sparse-cases motive, and both `rw [drain]` and
`simp [drain]` fail there ("failed to generate equational theorem"). Stating
the unfolding by hand costs one `rfl`, and the two steps below are its only
consumers — the same shape `Ref.ray`'s `rayBody`/`ray_step` uses next door. -/
theorem drain_succ (F : Nat) (w : World) (a : Addr) (n : Nat) :
    drain F w a (n + 1) =
      (match stepIter sunfish F w a with
       | .ok w' (some (.ntuple _ _ #[.int i, .int j, .str p])) =>
         (drain F w' a n).map ((i, j, p) :: ·)
       | .ok _ Option.none => some []
       | _ => Option.none) := rfl

/-- A step that yielded a `Move`: its triple joins the drain's list. -/
theorem drain_move {F : Nat} {w w' : World} {a : Addr} {n : Nat}
    {m : Ref.RefMove} (h : stepIter sunfish F w a = .ok w' (some (moveVal m))) :
    drain F w a (n + 1) = (drain F w' a n).map ((m.i, m.j, m.prom) :: ·) := by
  rw [drain_succ, h]; rfl

/-- A step that reported exhaustion: the drain is over, with nothing more. -/
theorem drain_done {F : Nat} {w w' : World} {a : Addr} {n : Nat}
    (h : stepIter sunfish F w a = .ok w' Option.none) :
    drain F w a (n + 1) = some [] := by rw [drain_succ, h]

/-- **The statement's `Option`-valued drain IS `drainIter`, projected through
`Move`.** Induction on the drain's fuel; `stepIter_mono` is the whole content
of the step, because the repaired statement runs every round at one fuel `Fs`
while `drainIter` spends its own down. `Fs` need only be at least the drain's
own fuel — and at the call site they are the same `F`. -/
theorem drain_of_drainIter (Fs : Nat) (a : Addr) :
    ∀ (F : Nat) (w w' : World) (ms : List Ref.RefMove), F ≤ Fs →
      drainIter sunfish F w a = .ok w' (ms.map moveVal) →
      drain Fs w a F = some (refTriples ms) := by
  intro F
  induction F with
  | zero => intro w w' ms _ h; simp [drainIter] at h
  | succ F ih =>
    intro w w' ms hF h
    rw [drainIter] at h
    obtain ⟨w₁, r, hstep, hrest⟩ := Run.bind_eq_ok.mp h
    have hstep' : stepIter sunfish Fs w a = .ok w₁ r :=
      stepIter_mono hstep (by simp) Fs (by omega)
    cases r with
    | none =>
      simp only [Run.ok.injEq] at hrest
      obtain ⟨-, hnil⟩ := hrest
      cases ms with
      | cons m ms' => simp at hnil
      | nil => exact (drain_done hstep').trans rfl
    | some v =>
      simp only at hrest
      obtain ⟨w₂, vs, hdrain, hcons⟩ := Run.bind_eq_ok.mp hrest
      simp only [Run.ok.injEq] at hcons
      obtain ⟨rfl, hvs⟩ := hcons
      cases ms with
      | nil => simp at hvs
      | cons m ms' =>
        simp only [List.map_cons, List.cons.injEq] at hvs
        obtain ⟨rfl, rfl⟩ := hvs
        exact (drain_move hstep').trans
          (by rw [ih w₁ _ ms' (by omega) hdrain]; rfl)

/-- **THE `gen_moves` THEOREM, from the module's own `directions` dict.**

The statement the owner decided (docs/backlog.md §H4) with the fuel repair its
note 4 asked for, and nothing else: for every position the reference
enumeration answers for, calling the shipped `Position.gen_moves` under the
Lean semantics and draining the object it returns yields exactly the
reference's moves, in the reference's order, at every fuel above a threshold.
Board free, rights/ep/kp free, the reference's budget free.

The two hypotheses are `gen_moves_drains_ref`'s two, at the ONE world
`genMovesOf` starts from: the module-global `directions` dict, which is a
dict literal and therefore lives in the heap. They are ground facts about
`initWorld sunfish` — no quantifier, no board — and they are TRUE: the
compiled evaluator answers `some (.ref 63)` and `some dirsObj`, which is what
genmoves_scan.lean's two `#guard`s check. They are not DISCHARGED here, and
the next section says exactly what discharging them costs. -/
theorem gen_moves_eq_ref_of_dirs
    (hg : Env.lookup (initWorld sunfish).globals "directions" = some (.ref 63))
    (hd : Heap.get? (initWorld sunfish).heap 63 = some dirsObj) :
    GenMovesEqRef := by
  intro b score wc0 wc1 bc0 bc1 ep kp rf ms href
  obtain ⟨w', t, hcd⟩ := gen_moves_drains_ref (initWorld sunfish) 63 b score ep kp
    wc0 wc1 bc0 bc1 rf ms hg hd href
  refine ⟨t, fun F hF => ?_⟩
  obtain ⟨hcall, hdrain⟩ := hcd F hF
  rw [genMovesOf, hcall]
  exact drain_of_drainIter F _ F _ w' ms (Nat.le_refl F) hdrain

/-! ### The last inch, MEASURED: `initWorld sunfish` is not kernel-reducible here

`theorem gen_moves_eq_ref : GenMovesEqRef` is `gen_moves_eq_ref_of_dirs`
applied to two `rfl`s. Both `rfl`s were attempted and both are out of budget
on this hardware, which is a fact about the module INITIALIZER, not about the
generator tier:

* `initWorld m` is `initFoldLive` over `m.topLevel` — it RUNS the module, and
  sunfish's top level runs the `pst` pipeline (six pieces x 120 squares
  through a dict-items loop, a rebound lambda and three lowered genexps)
  before the heap it produces can be read.
* Compiled, that is nothing: `#eval` answers `(initWorld sunfish).heap.size =
  66`, `Env.lookup … "directions" = some (.ref 63)` and the `dirsObj` test
  `true`, in well under a second (7.3 s wall including imports).
* By kernel reduction it did not finish: at the defaults, `rfl` on either
  fact reports `maximum recursion depth` and then a `whnf` heartbeat timeout;
  at `maxRecDepth 1000000` + `maxHeartbeats 0` the elaborator was OOM-killed
  after about seven minutes on a 16 GB machine. A `#guard` is a COMPILED
  check, so the two `#guard`s next door are not proofs of these two facts.

Two routes were named here for closing it. **Both have since been priced
against this exact goal, and the answer is not the one this note expected**
(docs/backlog.md §L12; the chain is `Examples/python/sunfish/init_chain.lean`,
the calculus `LeanModels/Python/ModuleInit.lean`):

1. **A module-init calculus** — step `initFoldLive` symbolically. Its
   TOP-LEVEL layer is cheap and landed (`initFoldLive_fold` / `_exec` /
   `_dirty` / `_append`, general over arbitrary statements). Its
   SUB-statement layer — a loop invariant for the `pst` pipeline — is the
   remaining work, and it is now the only remaining work.
2. **A pinned-literal chain**, one top-level statement at a time — this note
   called it "bounded per step". **It is not, and the bound is not the
   literal size.** Twenty-two of the twenty-four top-level statements are
   kernel-reducible from pinned states (0.11 s for the seven before the
   pipeline, 0.72 s for the fifteen after it). The other TWO are the `pst`
   pipeline, and a single Python statement inside the first of them —
   `pst[k] = sum((padrow(table[i*8:i*8+8]) for i in range(8)), ())` — ran
   154 s to a 4 000 000-heartbeat timeout and 420 s / 8.5 GB to an OOM kill
   from a fully pinned input state, without finishing. Chopping the top level
   finer cannot help: the wall is inside one statement.

So the chain went as far as the chop granularity allows, and what it bought
is real: `init_chain.lean` proves both of this theorem's hypotheses from ONE
hypothesis about the `pst` pipeline's run (`gen_moves_eq_ref_of_pst`), with
the address arithmetic that puts `directions` at slot 63, the live-view
resolution, `resolvedG`, the poisoning arms and the `__main__` guard all
kernel-proved rather than assumed.

The honest reading of this file is therefore: the generator tier proves
`gen_moves` against the reference on an arbitrary board through the real
interpreter with zero hypotheses about the GENERATOR, and the flagship's last
assumption is one line of module initialization — the `pst` padding loop and
the endgame table — which the compiled evaluator confirms and the kernel
cannot yet afford. -/

/-! ## What is still between here and `GenMovesEqRef`

Two things, and neither is a proof gap in this file.

1. **`PayloadBlind sunfish` — LANDED (§L7).** It was the tier's one
   remaining piece of real proof work and it is now
   `payloadBlind sunfish` (LeanModels/Python/PayloadBlind.lean): all
   eighteen interpreter arms, the block's induction on fuel, and the
   reduction to the `execGen` conjunct. What §L6 priced at ClockErase scale
   cost a third of that, because the perturbation is a FUNCTION and every
   helper obligation is an equation.

2. **The frozen statement's own fuel defect — REPAIRED (2026-08-19).**
   `GenMovesEqRef` drained through `drain`, which passed the constant 16384 to
   every `stepIter` while the statement quantifies over an arbitrary board, so
   the statement was false as written. The owner ruled the repair (`drain`
   takes `F`, which is what its note 4 says it does), and the section above
   closes it: `drain_of_drainIter` IS the value-shape step from
   `ms.map moveVal` to `refTriples ms`, and `gen_moves_eq_ref_of_dirs` is the
   flagship. What is not discharged is two ground facts about the world
   `genMovesOf` starts from, which is a module-init question, not this one.

`sf_order`'s `bound_probe` consumes the same bridge and needed three further
things this file does not touch: a `sorted`-over-a-generator EXPRESSION rule
(the builtin arm drains through `drainIter` and then allocates the sorted
list, so `IterDrains` is its engine but not its statement), generator-internal
`break` at the loop-frame level, and `callClosure`'s generator arm for the
lowered generator EXPRESSION. All three landed at §L8
(LeanModels/Python/GenBound.lean), with a fourth the list had missed — you
cannot ENTER a `forList` loop whose iterable allocates — and each is gated on
the shipped program in `Examples/python/sf_order/proof.lean`. -/


/-! ## The drain as a JUDGMENT, and its STEP-INDEXED reading (2026-08-22)

`gen_moves_drains_ref` above concludes a raw `∃ w' t, ∀ F ≥ t, … ∧ …`. Its
second conjunct IS `IterDrains`, but not in those words — and until it is, the
inverses next door (`IterDrains.uncons`/`.exhausts`, VCGen.lean §L6) cannot be
applied to it. This bridge is that rename, and it is what unblocks the two
consumers that were waiting: R2a's `hdrain` (order_genexp.lean §10) and R3c's
interpreter half, neither of which can name a concrete round list without a
per-round `IterSteps` on this generator.

**The census, before the statement** (the exit law, and the drain law's question
asked and answered): `drainIter` is a FULL drain, not a short-circuiting one, so
its out-world IS a function of its inputs and the world may be written into the
conclusion. What is NOT uniform is the per-STEP world, and the numbers below are
why `uncons` hands the intermediate world over existentially rather than
computing it. -/

/-- **`gen_moves_drains_ref`, as the judgment the loop rules consume.** -/
theorem gen_moves_iterDrains (w : World) (dad : Addr)
    (b : String) (score ep kp : Int) (wc0 wc1 bc0 bc1 : Bool) (rf : Nat)
    (ms : List Ref.RefMove)
    (hg : Env.lookup w.globals "directions" = some (.ref dad))
    (hdirs : Heap.get? w.heap dad = some dirsObj)
    (href : Ref.refMoves b.toList wc0 wc1 ep kp rf = .ok ms) :
    ∃ w', IterDrains sunfish (gmWorld w (posOf b score wc0 wc1 bc0 bc1 ep kp))
      w.heap.size (ms.map moveVal) w' := by
  obtain ⟨w', t, ht⟩ := gen_moves_drains_ref w dad b score ep kp wc0 wc1 bc0 bc1 rf ms
    hg hdirs href
  exact ⟨w', IterDrains.of_drain (ht t (Nat.le_refl t)).2⟩

/-! ### The per-step worlds, MEASURED on the opening board

Twenty yields and then exhaustion, with the heap after each step. -/

private def stepTrace (n : Nat) : Option (Nat × List (Nat × Bool)) :=
  match callIn sunfish 64 (initWorld sunfish) "Position.gen_moves" #[posH 0] with
  | .ok w0 (RVal.ref a) =>
    let rec go : Nat → World → List (Nat × Bool) → List (Nat × Bool)
      | 0, _, acc => acc.reverse
      | k + 1, w, acc =>
        match stepIter sunfish 4096 w a with
        | .ok w' r => go k w' ((w'.heap.size, r.isSome) :: acc)
        | _ => acc.reverse
    some (w0.heap.size, go n w0 [])
  | _ => Option.none

/-! **The steps are NOT uniform, and that is the whole reason `uncons`'
intermediate world is existential.** From 67 the twenty yields land at
69, 70, 73, 74, 77, 78, 81, 82, 85, 86, 89, 90, 93, 94, 97, 98, 105, 112, 137,
144 — deltas of **1 to 25 objects**, because a step runs however much of the
board scan the next move happens to need. Step 21 reports exhaustion at 148 and
step 22 repeats it: the drain is idempotent once done. -/
#guard stepTrace 22 == some (67,
  [(69, true), (70, true), (73, true), (74, true), (77, true), (78, true),
   (81, true), (82, true), (85, true), (86, true), (89, true), (90, true),
   (93, true), (94, true), (97, true), (98, true), (105, true), (112, true),
   (137, true), (144, true), (148, false), (148, false)])

/-! **And the whole drain is 81 objects** (67 → 148) — §L29's own number for the
ORDERING LINE's drain, which is the point: the outer genexp yields `(v, m)`
TUPLES, and a tuple is an immediate value. **The genexp's drain allocates
nothing of its own; every object it costs is this generator's.** -/
#guard 148 - 67 == 81

#print axioms gen_moves_iterDrains

end Examples.python.sunfish.genmoves_drain
