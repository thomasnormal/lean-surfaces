import LeanModels

/-!
# gen_lab — the H4 generator acceptance set (checks-only example)

Concrete regressions for generator functions (docs/memory-model.md
§generator semantics), pinned two ways: differential rows in
`harness/cases.json` (every function runs against CPython 3.9) and the
`#py_check`/`#guard` non-vacuity checks here (kernel-evaluated).

The three claims worth naming, because each one falsifies a cheaper
design that would otherwise look adequate:

* **Laziness is real.** `first_over_inf` and `any_over` consume
  INFINITE generators and terminate. Any design that pre-expands a
  generator into a list diverges here — and that is exactly the
  property sunfish's beta cutoff depends on, which is why a
  generator-free rewrite of `moves()` is not an option: an unconsumed
  yield must not run its TT-writing search.
* **A generator is IDENTITY, not a value.** `aliased` binds one
  generator to two names and steps through each; CPython advances the
  single shared frame (`0` then `1`, hence `1`). An immediate-value
  representation would restart and answer `0` — this row is the reason
  `Obj.generator` lives on the heap.
* **`break` SUSPENDS.** `two_phase` abandons a generator mid-loop and
  hands it to a second loop, which resumes where the first stopped;
  `drain_then_more` pins the exhausted case. Without suspension the
  cutoff would re-search from the first move.

Generator EXPRESSIONS are lowered at ingestion to generator functions
(CPython's own compilation), and `enumerate`/`itertools.count` are
lazy iterator objects riding the same stepper — `count` genuinely
infinite. The loud frontier — a `yield` in expression position (the
`send` channel), and a generator crossing the call boundary — is pinned
by the raw `#guard`s below and by whitelisted differential rows. No
`proof.lean`: checks-only, like `iter_lab`/`str_lab`/`cls_lab`.
-/

open LeanModels LeanModels.Python

load_program gen_lab from "Examples/python/gen_lab/gen_lab.json"

/-! ### consumption by a `for` loop -/

#py_check gen_lab.total(5) = 10
#py_check gen_lab.total(0) = 0
#py_check gen_lab.total(1) = 0
#py_check gen_lab.total_ret(5) = 10
#py_check gen_lab.sum_nested(7) = 412
#py_check gen_lab.first_over(10, 3) = 4
#py_check gen_lab.first_over(3, 99) = -1

/-! ### laziness: an INFINITE generator, consumed and abandoned -/

#py_check gen_lab.first_over_inf(4) = 5
#py_check gen_lab.first_over_inf(0) = 1

/-! ### suspension across `break`, and exhaustion -/

#py_check gen_lab.two_phase(5) = 1
#py_check gen_lab.two_phase(1) = -1
#py_check gen_lab.drain_then_more(4) = 6

/-! ### `next`, with and without a default -/

#py_check gen_lab.next_of(3) = 0
#py_check gen_lab.next_twice(3) = 1
#py_check gen_lab.next_default(0) = -1
#py_check gen_lab.next_exhausted(3) = -7

/-! ### heap IDENTITY: two names, one frame -/

#py_check gen_lab.aliased(4) = 1

/-! ### the faithful exceptions -/

#py_check gen_lab.next_stops(0) raises .stopIteration
#py_check gen_lab.next_of_int(3) raises
  (.typeError "'int' object is not an iterator")

/-! ### generator EXPRESSIONS — lowered at ingestion to generator
functions, exactly as CPython compiles them (`<genexpr@n>` with the
already-evaluated outer iterator as its first parameter and the captured
names after it). `any_over` runs a genexp over an INFINITE generator. -/

#py_check gen_lab.squares_upto(5) = 0
#py_check gen_lab.first_big(10, 4) = 5
#py_check gen_lab.any_over(7) = 8
#py_check gen_lab.genexp_sum(4) = 10

#guard (findFunction gen_lab (genExpName 0)).isSome
#guard (findFunction gen_lab (genExpName 0)).any (·.isGenerator)

/-! ### the builtin ITERATORS: `enumerate` over a str / a heap list, and
the infinite `itertools.count` (sunfish's ray shape) -/

#py_check gen_lab.enum_str("abc") = 296
#py_check gen_lab.enum_start("abc", 5) = 5
#py_check gen_lab.enum_lazy("abcdef", "c") = 3
#py_check gen_lab.count_ray(2, 3, 10) = 8
#py_check gen_lab.count_default() = 4
#py_check gen_lab.enum_of_int(3) raises
  (.typeError "'int' object is not iterable")

#guard callFunction gen_lab "enum_list" #[.list #[.int 3, .int 1, .int 2]] 4096
  == .ok (.int 5)

/-! ### the loud frontier (raw `#guard`: `unsupported` has no surface
form — deliberate). A generator cannot cross the boundary (a snapshot of
its yields would run the body eagerly); a `yield` in EXPRESSION position
is the `send` channel and refuses when the frame is stepped (creating
the generator is fine — calling one runs no code). -/

#guard callFunction gen_lab "upto" #[.int 3] 4096 matches .unsupported _
#guard callFunction gen_lab "gen_at_boundary" #[.int 2] 4096 matches .unsupported _
#guard callFunction gen_lab "send_is_loud" #[.int 3] 4096 matches .unsupported _

/-! ### the §exceptions obligation, DISCHARGED (docs/memory-model.md
§exceptions): what happens to a generator when a BUILTIN exception fires
inside a step. The raise itself propagates faithfully (`bad_first`/
`bad_second` are differential rows — the whole call raises CPython's
`ZeroDivisionError`), but the STATUS the object is left with diverges
from CPython today, and the raw `#guard` below pins the divergence
honestly: the stepper set `running` on entry and the exn path never
cleared it, so a THIRD step answers the fake "generator already
executing" `ValueError`, where CPython marks the frame finished and
`next()` raises `StopIteration`. Unreachable through the differential
harness until `try`/`except` exists (nothing in tier can survive the
second step to observe the third), which is exactly why the exceptions
design records "fix WITH the tier": the build flips this pin to the
CLOSED status and adds the `try`-driven differential row (`exc_lab`). -/

#py_check gen_lab.bad_second(2) = 0
#py_check gen_lab.bad_second(0) raises .zeroDivisionError

#guard (match callIn gen_lab 4096 ⟨#[], [], []⟩ "bad" #[.int 0] with
        | .ok w (.ref a) =>
          (match stepIter gen_lab 4096 w a with
           | .ok w₁ (some (.int 1)) =>
             (match stepIter gen_lab 4096 w₁ a with
              | .exn w₂ .zeroDivisionError =>
                -- the divergence, pinned: stuck `running`, fake ValueError
                -- (CPython: closed, StopIteration). Flipped by the build.
                (match stepIter gen_lab 4096 w₂ a with
                 | .exn _ (.valueError msg) => msg == "generator already executing"
                 | _ => false)
              | _ => false)
           | _ => false)
        | _ => false)

/-! ### the ingestion census: `is_generator` is CPython's syntactic,
scope-local rule — a def whose OWN scope contains a `yield`, reachable
or not. A generator def evicts the whole module from the heap-free
fragment (calling one ALLOCATES, and syntax cannot tell). -/

#guard (findFunction gen_lab "upto").any (·.isGenerator)
#guard (findFunction gen_lab "naturals").any (·.isGenerator)
#guard (findFunction gen_lab "evens").any (·.isGenerator)
#guard (findFunction gen_lab "total").any (fun f => !f.isGenerator)
#guard (findFunction gen_lab "next_of").any (fun f => !f.isGenerator)
#guard !moduleGenFree gen_lab
#guard !gen_lab.heapFree
