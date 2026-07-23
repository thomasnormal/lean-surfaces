# Why lean_models is built this way

This is the understanding-oriented piece: the design arguments behind the
framework, with pointers into the tree where each one is load-bearing. The
normative contracts live in [DESIGN.md](DESIGN.md) and
[spec-surface.md](spec-surface.md); the workflow lives in the
[README](../README.md) and the [tutorial series](tutorial/index.md); the
lookup tables are in [reference.md](reference.md); the prover's manual is
[AGENTS.md](../AGENTS.md).

## Deep embedding, because the prover has to read the program

You could connect Python to Lean by *translation*: compile each function to a
Lean function and prove things about that. lean_models instead does a **deep
embedding**: the program's real AST becomes a Lean value
(`load_program` in [LeanModels/Python/Logic.lean](../LeanModels/Python/Logic.lean)
defines it as a literal term), and a definitional interpreter
([LeanModels/Python/Semantics.lean](../LeanModels/Python/Semantics.lean)) gives
it meaning. Two reasons.

First, **legibility for the AI prover**, which is this project's primary user
and its primary design constraint. Programs stay source-shaped: the Lean term
mirrors the file you wrote, specs read against code you recognize, and the
goal state prints in the same surface notation the theorems are written in
([Delab.lean](../LeanModels/Python/Delab.lean): "for an AI prover the goal
state IS the interface"). A translator would put a second program — the
translation — between the prover and the code, and every one of its choices
would be invisible in the theorem.

Second, translations *bury semantic divergences*; a deep embedding surfaces
them. The house example is floor division
([spec-surface.md §2](spec-surface.md), [Examples/python/midpoint/midpoint.py](../Examples/python/midpoint/midpoint.py)):
Python's `//` floors, so `7 // -2 == -4`, while Lean's `Int` divisions
truncate or round differently (`(7 : Int) / -2 = -3`). A translator has to
pick some Lean division for `//`, and whichever it picks is silently wrong
somewhere. Here the interpreter implements `//` as `Int.fdiv`
([DESIGN.md](DESIGN.md), "Semantic decisions"), so the general theorem *must
say* `Int.fdiv (a + b) 2` — the prettier `(a + b) / 2` form is honestly
available only under a sign hypothesis, as a separate theorem. The divergence
is visible in the statement, never hidden in a translation.

## Four decoupled coverage axes

"Can it handle real code?" is four different questions, and the architecture
keeps them independent ([README](../README.md), [DESIGN.md](DESIGN.md)):

1. **Parse coverage** — borrow each language's own frontend (CPython `ast`
   here, pyslang for SystemVerilog) and dump a standardized JSON envelope
   ([envelope-schema.md](envelope-schema.md)). Parsing real code is a solved
   problem; don't re-solve it.
2. **Representation coverage** — full ASTs in Lean; unknown constructs become
   `Unsupported` *nodes*, so ingestion never fails on real files.
3. **Semantic coverage** — tiered, executable interpreters that fail loudly
   (`Res.unsupported`) outside the supported tier.
4. **Proof coverage** — the spec/tactic layer
   ([Surface.lean](../LeanModels/Python/Surface.lean),
   [LoopTactic.lean](../LeanModels/Python/LoopTactic.lean)) lags semantics by
   design.

Nothing on a lower axis blocks a higher one: you can ingest a file whose
constructs you cannot yet run, and run a program whose spec you cannot yet
prove. Coverage grows per axis, measured on real corpora — never faked.

## Fuel: honest partiality

Python programs may not terminate, but every Lean function must. The
interpreter takes `fuel : Nat`, decrements it on every recursive call, and
returns `.timeout` at zero. This is not a hack; it is the honest way to say
"we make no termination promises we haven't proved":

- Termination questions become *stateable* rather than presupposed — the tree
  can state the Collatz conjecture about an actual Python program
  ([spec-surface.md §8](spec-surface.md)).
- A theorem `tri(n) ==> n * (n + 1) / 2` means: *some* fuel suffices and
  returns that value. Its `@[spec]` corollary quantifies over *all* fuels.

Yet no theorem statement ever mentions fuel. That takes a theorem: **fuel
monotonicity** ([Obs.lean](../LeanModels/Python/Obs.lean), `fuelMono`) — a
run that decided (anything but `.timeout`) keeps its exact result at every
higher fuel. So the fuel-indexed runs form a chain whose decided value is
unique, and each call has a well-defined *outcome* — `returns v`, `raises e`,
`diverges`, or `stuck` — with fuel confined inside the `Obs` judgment
(`Obs.det`, `Obs.total`). The surface arrows (`==>`, `~~>`, `==>!`,
[spec-surface.md](spec-surface.md)) are sugar over that spine, which is why
`py_corollary` can move between the ∃-fuel, ∀-fuel, and partial forms for
free.

Two disciplines keep fuel-based partiality from degenerating into vacuity:

- **Non-vacuity checks**: a partial-correctness theorem is vacuously true if
  the interpreter never returns `.ok` (bug, wrong tier). So every example's
  first block runs the function on concrete inputs (`#py_check`) at
  elaboration time — the "if" side is demonstrably inhabited before any
  theorem is trusted.
- **The `~~>` form**: naive partial correctness ("if it returns `.ok`, the
  value is `v`") is vacuously provable *for every `v`* on a program that
  raises — a reward-hackable objective for an AI prover. The framework only
  offers the strengthened reading (`PartialTo`,
  [Surface.lean](../LeanModels/Python/Surface.lean)): every run either times
  out or returns exactly `v`, which is falsifiable — it is provably
  inconsistent with raising.

## The oracle principle

All nondeterminism is an explicit **oracle parameter** of the semantics. For
v0 Python this is invisible — the interpreter is deterministic. It exists for
SystemVerilog, where the IEEE scheduler may legally interleave processes in
many orders: the SV run function takes a schedule oracle `σ`
(`run d σ fuel stim`, [sv-design-m0.md](sv-design-m0.md)), and theorems
quantify over it. In the in-tree M0 slice
([LeanModels/Sv/Proofs.lean](../LeanModels/Sv/Proofs.lean)): `race_blk` is
proved *racy* by exhibiting two schedules with different traces, while
`swap_nba` and `counter` are proved correct **for every legal schedule** — a
claim no finite set of simulator runs can make. That is the payoff: simulator
nondeterminism becomes a quantified argument instead of a threat to validity.
(The SV lane is mid-integration: not yet imported by `lake build`, with its
own contract in [sv-design-m0.md](sv-design-m0.md) and gallery in
[sv-spec-surface.md](sv-spec-surface.md).)

## Differential testing: validating the semantics itself

A verification framework's weakest link is the semantics: prove everything
you like, and it means nothing if the model diverges from the real language.
So the interpreter is differentially tested against the real implementation —
CPython via [harness/diff_test.py](../harness/diff_test.py) on
[harness/cases.json](../harness/cases.json), Xcelium for the SV lane via
`harness/sv/diff_test.py` — and the rule is: the reference implementation is
ground truth, *not our reading of the spec*. Two catches made this mandatory
methodology rather than hygiene:

- **The gcd sign catch** ([Examples/python/gcd/spec.lean](../Examples/python/gcd/spec.lean),
  [spec-surface.md §3](spec-surface.md)). The obvious spec
  `gcd(a, b) ==> Int.gcd a b` is *false*: Python's `%` is `Int.fmod`, so
  `gcd(4, -6)` computes `4 % -6 = -2` and returns `-2` — CPython agrees, the
  harness pins it — while `Int.gcd 4 (-6) = 2`. Differential testing before
  proving is what showed the sign hypotheses on `gcd_total` are semantic
  content, not decoration.
- **The counter X-startup catch** (SV lane,
  [sv-spec-surface.md §2](sv-spec-surface.md),
  [LeanModels/Sv/Proofs.lean](../LeanModels/Sv/Proofs.lean)). The obvious
  refinement — "`counter` implements `if rst then 0 else s + 1` from a zero
  initial state" — is what a 2-state, zero-initializing simulator would
  coincidentally confirm. The LRM (and Xcelium, verified) says otherwise: an
  uninitialized 4-state signal starts all-X, and `X + 1 = X`, so before the
  first reset *no* `BitVec 8` state corresponds to the trace. The honest
  theorem (`counter_from_reset`) carries a load-bearing "from the first
  sampled reset" qualifier that only exists because the model was checked
  against a real simulator's startup behavior.

Same lesson both times: the bug isn't in the proof, it's in what you thought
the language does. Test the model against reality *before* proving.

## `unsupported`, and why loud beats wrong

`Res.unsupported` is not an error the program raised — it is the interpreter
declining: "this construct is outside my supported tier." The alternative to
declining is guessing, and a guess is a silently wrong semantics that proofs
then faithfully verify. Concrete case ([DESIGN.md](DESIGN.md)): CPython's
`list += x` mutates in place, observably through aliases; v0's value
semantics cannot reproduce that, so a list-valued `+=` is `unsupported` —
not "approximately supported" with rebind semantics that would be wrong in
exactly the aliasing cases someone eventually cares about.

Loudness is enforced end to end. In the logic, `stuck` is a distinct outcome
from `diverges` ([spec-surface.md §10](spec-surface.md)) — hitting an
unsupported construct can't hide as non-termination, and `~~>` specs are
falsifiable on unsupported programs. In the harness, `"expect":
"unsupported"` entries are a *whitelist of documented tier gaps*, printed in
the results table; any non-whitelisted mismatch fails the run. The two
whitelisted Python cases today (`powi(2, -1)` and `true_div(7, 2)` — floats
are out of the v0 tier) are listed next to a hundred and one matched ones,
which is the honest shape of a coverage claim: measured, with the gaps named.
