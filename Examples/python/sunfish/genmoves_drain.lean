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

**What this file is NOT.** It is not `GenMovesEqRef` (genmoves_theorem.lean),
and it deliberately does not touch it: that statement drains through its own
`drain`, which runs every step at the CONSTANT fuel 16384 while quantifying
over an arbitrary board, and is therefore false as written (genmoves_scan.lean's
closing section has the counterexample — a board long enough that one step
cannot cross it). The statement is owner-decided, so the repair is not made
here. `gen_moves_drains_ref` is the same claim with the fuel the way that
statement's own note 4 says it was meant to be: one threshold `F` for the call
and the drain both.
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

/-! ## What is still between here and `GenMovesEqRef`

Two things, and neither is a proof gap in this file.

1. **`PayloadBlind sunfish` — LANDED (§L7).** It was the tier's one
   remaining piece of real proof work and it is now
   `payloadBlind sunfish` (LeanModels/Python/PayloadBlind.lean): all
   eighteen interpreter arms, the block's induction on fuel, and the
   reduction to the `execGen` conjunct. What §L6 priced at ClockErase scale
   cost a third of that, because the perturbation is a FUNCTION and every
   helper obligation is an equation.

2. **The frozen statement's own fuel defect**, recorded at genmoves_scan.lean:
   `GenMovesEqRef` drains through `drain`, which passes the constant 16384 to
   every `stepIter` while the statement quantifies over an arbitrary board, so
   the statement is false as written. Repairing it (`drain` taking `F`, which
   is what its note 4 says it does) is an owner call, and with that repair the
   theorem above is what closes it — modulo the value-shape step from
   `ms.map moveVal` to `refTriples ms`, which is `drain`'s own `Move`
   projection over the same list.

`sf_order`'s `bound_probe` consumes the same bridge and needed three further
things this file does not touch: a `sorted`-over-a-generator EXPRESSION rule
(the builtin arm drains through `drainIter` and then allocates the sorted
list, so `IterDrains` is its engine but not its statement), generator-internal
`break` at the loop-frame level, and `callClosure`'s generator arm for the
lowered generator EXPRESSION. All three landed at §L8
(LeanModels/Python/GenBound.lean), with a fourth the list had missed — you
cannot ENTER a `forList` loop whose iterable allocates — and each is gated on
the shipped program in `Examples/python/sf_order/proof.lean`. -/

end Examples.python.sunfish.genmoves_drain
