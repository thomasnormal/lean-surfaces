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

/-! ### the §exceptions obligation, discharged AND FIXED
(docs/memory-model.md §exceptions): what happens to a generator when a
BUILTIN exception fires inside a step. The raise itself propagates
faithfully (`bad_first`/`bad_second` are differential rows — the whole
call raises CPython's `ZeroDivisionError`). The STATUS was pinned
divergent BEFORE the exceptions build (commit "The stepper's exn
obligation, discharged": stuck `running`, a third step the fake
"generator already executing" ValueError) and the build's
close-on-exn-through-resume arm FLIPPED this `#guard` exactly as the
design required: the object is CLOSED, a third step is exhaustion —
CPython's `next()` → `StopIteration`, pinned differentially by the
try-driven `exc_lab.gen_closes_hard` row now that a handler can survive
the raise. -/

#py_check gen_lab.bad_second(2) = 0
#py_check gen_lab.bad_second(0) raises .zeroDivisionError

#guard (match callIn gen_lab 4096 ⟨#[], [], [], []⟩ "bad" #[.int 0] with
        | .ok w (.ref a) =>
          (match stepIter gen_lab 4096 w a with
           | .ok w₁ (some (.int 1)) =>
             (match stepIter gen_lab 4096 w₁ a with
              | .exn w₂ .zeroDivisionError =>
                -- CLOSED: the third step is exhaustion, never a fake
                -- ValueError and never a resumable frame
                (match stepIter gen_lab 4096 w₂ a with
                 | .ok _ Option.none => true
                 | _ => false)
              | _ => false)
           | _ => false)
        | _ => false)

/-! ### pass 4 (docs/memory-model.md §bound() end-to-end): genexp
admission for BODY-ASSIGNED free names under an IMMEDIATE drain — the
correction's `all(depth > 1 … >= val_lower …)` shape. Admitted only
when boundness at creation is provable (a parameter, or a direct-child
bind at a smaller line); a genexp bound to a NAME first (`g = (…)`)
or a conditionally-bound capture stays refused. -/

#py_check gen_lab.drain_assigned(5) = 2
#py_check gen_lab.drain_assigned(2) = 2
#py_check gen_lab.drain_assigned(0) = 1
#py_check gen_lab.drain_assigned_param(4) = 15
#py_check gen_lab.drain_assigned_param(0) = 3

#guard callFunction gen_lab "gen_assigned_lazy" #[.int 3] 4096 matches .unsupported _
#guard callFunction gen_lab "drain_unbound" #[.int 1] 4096 matches .unsupported _

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

/-! ### pass 5: `yield from <genexp>` — INLINED at ingestion
(docs/memory-model.md §yield from). The inlined loop reads the
enclosing frame by reference — exactly what a delegated genexp does,
since the enclosing frame cannot run mid-delegation (`yf_live`: the
rebound loop variable `i` is read live). The admission requires the
genexp's target to occur nowhere else in the body; `yf_leak` (target
read after the loop) and `yf_list` (not a genexp) survive un-lowered
and refuse loudly. -/

#py_check gen_lab.yf_promote_drive(1, 2) = "NBRQ"
#py_check gen_lab.yf_live_drive(3) = 11223
#py_check gen_lab.yf_live_drive(0) = 0
#py_check gen_lab.yf_filter_drive(5) = 19
#py_check gen_lab.yf_filter_drive(0) = -1

#guard callFunction gen_lab "yf_list_drive" #[.int 3] 4096 matches .unsupported _
#guard callFunction gen_lab "yf_leak_drive" #[.int 3] 4096 matches .unsupported _

-- the census: yield-from defs are generators (CPython's scope-local
-- syntactic rule sees YieldFrom), lowered or not
#guard (findFunction gen_lab "yf_promote").any (·.isGenerator)
#guard (findFunction gen_lab "yf_list").any (·.isGenerator)
