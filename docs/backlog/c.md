# The C lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by
the C lane.** Ids are `YYYY-MM-DD-c-<n>` and need no reservation, because the
lane name makes them unique — which is the point: this lane renumbered its own
section three times in one day around collisions (`L59→L63→L72`, then
`L59→L72→L79→L83`), each time under a push-time re-read that existed only to
survive the race §9.5 retires.

**Everything before 2026-08-22 is in `docs/backlog.md`** and stays there; this
lane's history is §L35, §L40, §L42, §L50, §L54, §L57, §L72 and §L83, and every
one of those references keeps resolving.

---

## 2026-08-22-c-1 — §L83's TRIAD CLOSES GREEN, the standing strategy is adopted by touch, and inch 4 opens with fuel

### §L83's owed triad — ALL FOUR LEGS GREEN

`§L83` (inch 3) landed with an honest gap: the tree triad had not run,
because the lock starved this lane for 50 minutes. It has now run, once,
under a ticket:

* `lake build` — **3711 jobs, exit 0**
* `docs_check` — **83/83**, 23 illustrative-exempt
* `diff_test` — **1394 cases, 0 failed**, 118 whitelisted, 1276 matched
* `script_corpus` — **65 scripts, 0 failed**, 50 matched, 15 loud

No `sorry`, no `native_decide`. The three drain-amendment theorems'
axioms are `[propext, Classical.choice, Quot.sound]`.

### The five dispatched items

**§9.1 — `c_construct_census --compare` exits 0 on drift. ALREADY FIXED, by
the audit lane, and NOT duplicated.** Verified on `origin/master` before
touching anything: `compare()` now carries a `drift` counter and returns 1.
The audit's fix also found a **second hole this lane had put there** — an
early return keyed on the SOURCE sha, so a census that differed for the same
input bytes (a moved frontend, a changed instrument, a hand-edited artifact)
reported `UNCHANGED` and exited 0. This lane hit that hole earlier the same
day, worked around it by diffing the JSON by hand, and **did not recognise it
as a defect**. That is the §5.4a shape exactly: the instrument read green
because it could not read anything else.

**§9.2 / `tools/triad.sh` — ADOPTED; the hand-rolled script is deleted.**
`scratchpad/ctier-triad.sh` was one of the six measured non-compliant and is
gone. Two defects it had, both real, both found the hard way:

1. **Its release was unconditional.** The trap ran `rm -rf` on the lock
   whenever it had *ever* acquired it, without re-reading the owner. The lock
   changed hands mid-tenure and the trap then **deleted another lane's
   tenure**. Release must re-read ownership, never infer it from history.
2. **It ran `diff_test` and `script_corpus` without re-asserting the lock.**
   Under Amendment 11 those RUN the interpreter, so losing the lock mid-tenure
   and continuing is a violation — which is what a peer flagged. Ownership
   must be asserted before *every* leg, and losing it must stop the work.

`tools/triad.sh` has both properties by construction, which is the whole
argument for the protocol being code rather than prose.

**§9.5 — per-lane backlog: this file.** New landings come here.

**§9.6 / A13 CoW seeding — NOT USED, and the reason is worth recording.**
`/tmp` was purged mid-session and took **every** lane tree with it, so there
was no sibling to `cp -Rpc` from; this lane re-cloned and ran
`lake exe cache get` (94 s, 8642 oleans already in `~/.cache`, no download).
A13 seeds from a sibling clone, so it is exactly unavailable in the case that
makes seeding most valuable. Worth a line in §7.1a: **after a purge the seed
source is gone too, and the fallback is the global cache, not a sibling.**

**§9.2 / `censuskit` — NOT YET; `harness/censuskit.py` does not exist on
master.** Adoption is by touch when it lands.

### Two measurements the machine emergency produced

**FIFO works.** The ticket queue (Amendment 9, this lane's design) delivered
the lock in **46 seconds** after 113 minutes of prior starvation across two
inches. Nothing else changed.

**`LEAN_NUM_THREADS=2` cut the worker count from 5+ to 2** — but **Amendment
11's 3 GB chain line cannot hold this tree.** Measured: a single Lean worker
on `Examples.python.sunfish.pins_clock` peaks at **2.67 GB**, and the chain hit
**3934 MB at 98% built** (3450/3514) and was killed by this lane's own
watchdog, twice. That module then took **2154 s** and `pins_search` **988 s**
under `nice 19`. **4 GB is the measured floor for a full-tree build here**;
this lane raised its own limit to 4 GB and says so rather than setting it
quietly. The 3 GB figure is right for a lane building only its own modules and
wrong for anyone building the tree.

### Inch 4 opens: `LeanModels/C/C23/Stmt.lean`

The statement census (1213 statements) and the design are
`docs/c-semantics-design.md` §4.6. What landed here is the layer the rest sits
on:

* **Fuel arrives at inch 4, not inch 5** — the correction §L83 recorded.
  **84 loops, and 20 of them contain no call at all**, so it is the loop and
  not the call that forces fuel. `execStmt` will recurse on fuel at exactly
  one place: the loop step.
* **`Halt` becomes the stack's base**, so `ExecM = ExceptT Refusal (StateT Mem
  Halt)`. `docs/c23-goal.md` §3 says TIMEOUT is "never conflated with REFUSE",
  and the Python tier's `Run` already agrees structurally: `.ok` and `.exn`
  carry state, **`.timeout` carries none**. A timeout discards the memory
  because it observed nothing.
* **One deliberate divergence from Python, recorded rather than drifted
  into**: Python's `Run.unsupported` carries no state; C's does, because it
  rides in `ExceptT` with the other refusals. The inch-6 scoreboard's REFUSE
  rows are worth more when they can say what had happened. **Only TIMEOUT
  loses its world.**
* **`Flow`** — the five completions, with `goto` carrying its label. Measured:
  the 7 `goto`s reach exactly **3 labels**, every one a forward jump inside
  one function, which is the shape an outward-propagating `Flow.goto` serves;
  a general `goto` needs a CFG and this corpus has none.

### CONVERGENCE, and a divergence inside it — for §9.3's attention

**Two lanes independently named the same type `Halt`, for the same job.**
`LeanModels/Es/Completion.lean` has one; this landing adds
`LeanModels/C/C23/Stmt.lean`'s. Neither lane saw the other's. Under §9.3
("ratified by convergence") that is the signal for a shared `Core` type
rather than two.

**But the two are NOT the same type, and the difference is a real family
question, not an accident:**

| | ES `Halt` | C `Halt` |
| --- | --- | --- |
| `ok` | yes | yes |
| `timeout` | yes | yes |
| **`unsupported`** | **yes — in the base** | **no — in `ExceptT`** |

Both lanes reasoned from the same covenant (Python's `Run`, where
`.timeout` and `.unsupported` both carry no state) and reached opposite
conclusions about `unsupported`. ES kept it state-free, matching Python.
This lane deliberately moved it into `ExceptT` so that a REFUSE row on the
inch-6 scoreboard can say **what had happened by the time the model
declined** — an out-of-tier construct is a refusal a reader wants located,
and "the program got this far, then hit a `switch`" is worth strictly more
than "unsupported".

**Neither is obviously right, and the family should decide once**: is
`unsupported` an observation (state-carrying, C's reading) or an
abandonment (state-free, ES's and Python's)? Whichever wins, both lanes
should share the type. Recorded here rather than resolved unilaterally,
because a third lane will otherwise invent a third `Halt`.

`execStmt` itself is the next landing.


---

## 2026-08-22-c-2 — INCH 4: the tier RUNS a function, and refusal moves to `Halt` on the §3.4 ruling

### The tier executes `pyfloordiv`, and agrees with Python

Inches 1-3 evaluated expressions. **This is the first time the C semantics
runs a whole function body taken out of the ingested term** — `pyfloordiv`
(sunfish.c L160-164), three statements: a two-declarator declaration, an `if`
over the corpus's own `&&`, and a `return`.

The point is not that it runs. It is that **it agrees with Python where C
alone would not**, at the site the ctwin README names as the #1 place C clones
silently diverge:

| | C's `/` alone | `pyfloordiv`, run by this model | Python |
| --- | ---: | ---: | ---: |
| `-7 / 2` | -3 | **-4** | -4 |
| `7 / -2` | -3 | **-4** | -4 |
| `-1 / 5` | 0 | **-1** | -1 |
| `-7 / -2` | 3 | **3** | 3 |

Gated against `Int.fdiv` over all eight pairs, so the agreement is a claim
about two definitions rather than a table of numbers someone typed. And
`pyfloordiv 1 0` **REFUSES** with `J.2(41)` rather than answering.

### The §3.4 ruling, adopted — and this lane's census is why it went the other way

This lane had argued `unsupported` should ride in `ExceptT` so a REFUSE row
could say what had happened. **The ruling put it in `Halt`, and the corpus
this lane censused is part of the reason**: putting a refusal in `ExceptT`
makes it catchable in principle, and the implicit defence was that nothing in
C intercepts control flow — but the corpus has **`setjmp` 2, `longjmp` 2 and 5
`jmp_buf` objects**, and the language has signal handlers besides. Inside `ρ`,
"no catch reaches a refusal" is a per-language, per-construct proof
obligation. **Uncatchability belongs to the definition.**

The diagnostic need is met the better way: `Halt.unsupported` carries a
structured payload — the cause plus an **optional** memory snapshot captured
AT the refusal site — and §3.4's existing law pays for it, because every
refusal already routes through a NAMED primitive and `refuseUnsupported`
performs the `get` itself, so no call site can forget.

**Both guards are STRUCTURAL, not advisory.** `Halt`'s `BEq` is hand-written
to ignore the snapshot, so two refusals of the same construct reached through
different memories compare EQUAL; and `Outcome` — the verdict a scoreboard
reads — has nowhere to put a `Mem` at all. Gates check both directions,
including that the CAUSE is still compared, so the guard has not quietly
disabled the gate.

Consequences: `Refusal` narrows to the two catchable causes (`ub`, `libc`),
the third reaching a scoreboard through `Outcome.cause?`; and **`ExecM` is now
literally `EvalM`** — one stack for both layers, which is what the ruling
bought — so `liftEval` is the identity, kept only to name the boundary.

### `execStmt`

The eleven statement kinds. Fuel decreases on every recursive call, not only
at loops — stricter than §4.6.1 needs, but it makes the recursion structural
on `Nat` with no measure to justify. `execBlock` threads the environment
declarations extend; `execLoop` runs `for`'s increment **after a `continue`**
(§6.8.6.4p2 — the detail a model gets wrong by treating `continue` as
`break`, and the gate is that the loop terminates with `a = 3`). `goto` is
served by a forward label search, which the census says is enough: 7 gotos, 3
labels, every one a forward jump inside one function.

**Held, and named rather than silently missing**: aggregate initializers (34
`InitListExpr` sites) refuse rather than initialize partially, and `fuelMono`
is STATED as an obligation, not proved. Both are the next landing.

### Triad

`lake build` **3721 jobs exit 0**; `docs_check` **83/83**, 24
illustrative-exempt; `diff_test` **1394 cases, 0 failed**, 118 whitelisted,
1276 matched; `script_corpus` green. Axioms unchanged for the nine C-lane
theorems (`[propext, Quot.sound]` or less, three also `Classical.choice`). No
`sorry`, no `native_decide`.

**The lock cost 5304 seconds — 88 minutes — of FIFO queueing**, and that is
the honest number: the ticket queue is fair but the machine is saturated, so
fairness converts starvation into a long, *bounded* wait. Work was pushed to a
branch while queued so a purge could not take it, and merged to master only
once green.


---

## 2026-08-23-c-3 — §6.7.11 AGGREGATE INITIALIZATION: the rule fires on NOTHING, so it is gated on a synthetic

### The census corrected my own number, and then found the fact that mattered

I had written "34 `InitListExpr` sites". There are **75** (35 top-level, 40
nested) — the 34 counted only those sitting directly on a `VarDecl`'s `init`.
But the number that shapes the work is one I had not measured at all:

> **ALL 75 ARE FULL.** No array initializer is shorter than its extent; no
> structure initializer omits a member.

So **§6.7.11p10 — the unmentioned members are initialized as objects with
static storage duration, i.e. to zero — fires on ZERO corpus sites.**

That is the effective-types situation from §2.5, exactly: cheap to install
correctly while nothing exercises it, expensive to retrofit afterwards, and
**no instrument in this project would otherwise notice it was missing.** So it
is implemented, and gated on a **SYNTHETIC** partial initializer, because the
corpus cannot exercise it and a rule nobody ran is a rule nobody checked.

### Two gates that make the zero mean something

`int a[4] = {7, 8};` appears nowhere in the corpus. The gate checks elements 2
and 3 read back as **0** — and the neighbouring gate checks that with **no**
initializer the same read **REFUSES** as indeterminate. Without that second
gate, the zero could have come from `alloc` handing back zeroed memory rather
than from §6.7.11p10, and the gate would have been decoration.

### Zero-initialization is TYPE-DIRECTED, not a memset

§6.7.11p10 initializes an unmentioned member *as if by `= 0`*, and for a
POINTER that is a **null pointer**, not all-bits-zero. Writing zero bytes would
leave a member that reads back as the integer 0 and makes `loadPtr` refuse — a
wrong answer wearing the shape of a right one. Gated: a partially-initialized
`struct box` reads its unmentioned `int *` member back as `Ptr.null`.

`Layout` gains `elem` and `members`, because **aggregate initialization WRITES
through the layout** where reading only ever asked it for one offset — the
obligation this lane named when it held the work.

### `fuelMono` — NOT proved, and the reason is structural

The technique is no longer open: **`LeanModels/Sv/Obs.lean` already solves this
exact problem** — a flat approximation order with `timeout` at the bottom,
`fuelMono` as ONE conjunction over the mutual block, induction on fuel with a
`le_bind` congruence — in **96 lines for four functions**. This lane should
**LIFT that machinery, not write a second copy**; a second hand-rolled
monotonicity order is precisely what §9.2 exists to stop.

Two things make it more than a transcription: this mutual block is **ten**
functions, not four, and its functions are MONADIC, so monotonicity is
pointwise in the memory.

**Why it was not attempted here, specifically.** Proof iteration needs many
short Lean runs, and under Amendment 11 every one needs a tenure — which cost
this lane **88 minutes** on the previous landing and **~80 minutes** on this
one. A 300-line proof developed at one compile per tenure is not a session's
work. **That is the lock's real cost on PROOF work as distinct from build
verification**, and it is a different shape of problem from the starvation the
ticket queue fixed. Reported rather than worked around.

### HOLD: `Core.SemM`'s `Halt` is not adopted yet, deliberately

`LeanModels/Core/SemM.lean` has this lane's `Halt` shape, but a **poorer
payload**: `unsupported (msg : String)` against this lane's
`(what, snapshot : Option Mem)` with the two structural guards that make the
§3.4 ruling real. **Importing it today would delete the ruling, not
consolidate it.** The rebuild lane is landing a Core payload that subsumes
this one; adoption then becomes a substitution. Recorded at the definition
site so the next lane to look does not "tidy" it away. Deliberate duplication
with a reason, not drift.

### A second RSS data point for Amendment 15

The first build attempt was killed by this lane's own watchdog at **6171 MB
against the 6144 MB (6 GB) chain line** — 27 MB over. So A15's chain SECONDARY
is marginally too tight for a full-tree build at `LEAN_NUM_THREADS=2` on this
machine; the per-process 3 GB line is the one doing the real work, and the
chain figure wants ~6.5 GB or advisory status. `triad.sh` handled it correctly
(exit 137 recognised as a resource kill, re-run once, second attempt green),
which is the amendment working as designed.

### Triad

`lake build` **3724 jobs exit 0**; `docs_check` 83/83; `diff_test` **1427
cases, 0 failed**, 118 whitelisted, 1309 matched; `script_corpus` **65
scripts, 0 failed**. **Coverage: full** — a green covers every default target
at this sha. 43 gates in `Examples/c/sunfish/stmt.lean`. No `sorry`, no
`native_decide`.

---

## 2026-08-22-softfloat-2 — INBOUND FROM THE SOFTFLOAT LANE: C lane's to triage

*Filed by the SoftFloat lane during its consumer census
(`docs/softfloat-charter.md` §2.3). The id is in the SoftFloat namespace on
purpose: this lane mints nothing in the C lane's sequence. Renumber it into
yours, or close it — it is yours from here.*

### THIS IS A BLOCKER-CLASS FINDING: THE MODEL AND THE DESIGN DOC DISAGREE ABOUT `v0`

`docs/c-semantics-design.md` §1.3 (line 103, *"Floats are a TIER, not a
hole"*) says:

> **v0 admits `double` values, assignment and comparison**, and REFUSES every
> operation whose rounding it would have to guess. On ctwin's fixed-depth path
> exactly one float operation is evaluated — `deadline != 0.0`, both operands
> exactly representable — so **the claim is exact rather than scoped away**.

**The model does not do this.** `LeanModels/C/C23/Expr.lean:719`:

```
| .floatLit .. => refuseUnsupported "floating literal (floats are a named decision)"
```

Every float literal is refused, and `IntegralToFloating` (line 600) with it.
So `deadline != 0.0` cannot be evaluated at all: the described v0 admits it,
the landed v0 refuses it. Pinned by `Examples/c/sunfish/expr.lean`.

**Why this is a blocker and not a footnote.** The family's standing rule is
that the model always matches the code, and a divergence is a blocker.
`docs/c-semantics-design.md` §1.3 is not a stale aspiration in a corner — it is
the section a reader consults to learn what the C tier claims about floats, and
it currently overstates the tier by exactly one evaluated operation. Either the
model gains the comparison fragment the doc describes, or the doc stops
describing it. **This lane has no opinion on which**; it has only measured that
they are two.

**Unrelated and unaffected:** the Annex F gate itself stands. Neither profiled
host defines `__STDC_IEC_60559_BFP__`, so the R4 rung's *oracle-side* gate is
real and is not what this entry is about. What SoftFloat unblocks is the
model-side half (`docs/softfloat-charter.md` §2.3).

**One number worth having when you price step 3.** Your own §6 headline is
*"21% of c-testsuite's format specs and 10% of Fujitsu's"*, which counts
SPECS; the table directly above it counts TESTS, and there the float slice is
**2 of 61** printf-family tests for c-testsuite and **19 of 261** for Fujitsu.
Both true, and they price correctly-rounded decimal printing very
differently — 21 tests, not a fifth of the corpus.
## 2026-08-23-c-4 — INCH 5 IS **RED**, and the diagnosis is the deliverable

`c-inch4-wip` @ `91ccd33` got its tenure at 04:30 after **11 366 s (3h9m)** of
FIFO queueing. **`lake build` exit 1.** It is on a branch and never touched
master, which is the whole reason the branch discipline exists.

### What broke, and it was my design, not the tooling

```
LeanModels/C/C23/Expr.lean:555: fail to show termination for
  evalLValue, evalExpr
  ... failed to eliminate recursive application
      evalLValue ctx (base.member field arrow ty sp)
```

Plus three collapsed proofs at `Expr.lean:844/854/866` — the drain-amendment
theorems, whose `simp` sets depend on `evalExpr`'s equation lemmas, which stop
being generated when termination fails. **Those three are consequences, not
separate failures.**

**The cause is inch 5's handler signature.** Passing `evalExpr ctx` as a
closure into `ctx.call` adds a recursive call site *through an opaque
function*, and Lean cannot verify an opaque callee will not re-enter with a
larger argument. That killed the whole inference — including a
`.member`/`.index` case that had been accepted since inch 3.

**The second defect the failure exposed, which inch 3 had been getting away
with.** `evalExpr`'s aggregate cases RECONSTRUCT the node:

    | .member base field arrow ty sp => do
        let p ← evalLValue ctx (.member base field arrow ty sp)

A reconstructed node is not a syntactic subterm, so it is not structurally
smaller. Inch 3 built green only because the inference had enough slack
elsewhere; inch 5 removed the slack and it fell over. **It was latent, and a
green build was hiding it** — which is why "it compiled" is not the same as
"the recursion is well-founded for a reason I could state."

### The repair, designed but NOT verified

1. **Take the parts, never rebuild the node.** Add `memberAddr ctx base field
   arrow` and `indexAddr ctx base idx ty` to the mutual block; both
   `evalLValue` and `evalExpr` call them with `base`/`idx`, which ARE
   subterms. The reconstruction disappears.
2. **Revert the handler to values, and put `evalArgs` back in the mutual
   block** with an explicit `termination_by` on an `Expr.size` measure, since
   structural inference cannot see through `List Expr`. `evalExpr` stays
   fuel-free — arguments are subterms — and the handler gets `List CVal`, so
   nothing opaque receives a recursive closure.

The design goal that drove inch 5's signature — *arguments are evaluated in
the caller's scope* — is preserved by (2): evaluation happens inside
`evalExpr`, which IS the caller's context.

**Not attempted here.** The repair needs a tenure to verify and the queue is
running 1-3 hours; a fix pushed unverified is what the branch exists to
prevent.

### Core adoption, priced by site count

The calibration law's grep — `.error (.unsupported` across `LeanModels/C/**`
and `Examples/c/**` — returns **0** for this tier, and the zero is
informative: this lane's §3.4 landing already moved `unsupported` OUT of the
error channel into `Halt`, so a pattern written for tiers where it still rides
in `ρ` cannot see it. **The named grep under-counts here by construction**; a
naive `.unsupported` grep then OVER-counts by 4, catching `Ast.lean`'s
`Expr`/`Stmt`/`Decl.unsupported` AST constructors, which are unrelated.

Measured surface for `Loud.unsupported (cause) (message) (snapshot)` at
`σ := Mem`:

| | sites |
| --- | ---: |
| CONSTRUCT the payload — production | **2** (`refuseUnsupported`, `exhausted`) |
| CONSTRUCT — gates | 6 (`memory.lean`'s snapshot-guard gates) |
| DESTRUCTURE — production | 5 (`Halt.bind`, `Refusal.j2`/`cause`, `Outcome.cause?`, `EvalM.verdict`) |
| DESTRUCTURE — gates | 3 (`stmt.lean`) |
| **INSULATED call sites — zero cost** | **53** |

**Price: ~11 real edit sites plus two type aliases** (`Halt` → `HaltWith`,
`EvalM`/`ExecM` → `SemMWith … Mem`). **53 of the 64 touch points cost
nothing**, because every refusal already routes through a NAMED primitive —
which is §3.4's own law paying for itself at adoption time, exactly as
predicted.

**Scheduled, not done**: adoption waits behind the inch-5 repair, so the tier
is not absorbing a substrate change and a termination fix in one unverified
step.

---

## 2026-08-23-c-5 — **A GREEN BUILD IS NOT A TERMINATION ARGUMENT**

A family-level finding, minted by inch 5's red build and worth more than the
inch was.

### What happened

`evalExpr`'s aggregate cases REBUILT the node they were dispatching on:

    | .member base field arrow ty sp => do
        let p ← evalLValue ctx (.member base field arrow ty sp)

A reconstructed node is not a syntactic subterm of anything, so it is not
structurally smaller. **This was in inch 3, which built green, and in every
landing since.** It survived three landings because Lean's structural
inference had enough slack elsewhere to find *some* measure. Inch 5 added one
more recursive call — a closure passed into an opaque handler — the slack ran
out, and the whole mutual block failed at once, taking three drain-amendment
theorems with it as collateral (their `simp` sets need equation lemmas that
are not generated when termination fails).

### The finding

**A build that goes green tells you a measure EXISTS. It does not tell you
which one, and it does not tell you that you could have named it.** Inference
succeeding is a fact about the elaborator's search, not about the program —
and it degrades non-locally: an unrelated edit elsewhere in the block can
withdraw it. The failure surfaces far from the defect and long after it was
introduced, which is exactly the shape of bug this project's laws exist to
convert into a loud one.

**The rule, adopted here:** *take the parts, never rebuild the node* — and
**state the measure**. `termination_by` on the whole mutual block, so the
argument is written down and reviewable, not re-derived by search on every
build.

### The repair

* `memberAddr ctx base field arrow` and `indexAddr ctx base idx ty` take
  `base`/`idx`, which ARE subterms. Both `evalLValue` and `evalExpr` call
  them; the reconstruction is gone from both.
* An explicit `termination_by` over the four functions: the main pair carries
  `2 * Expr.size e + 1`, the address helpers `2 * size + 2`. The doubling buys
  the middle rung — a helper is strictly smaller than the node that called it
  and strictly larger than the subterms it evaluates.
* `Expr.size` is defined through the EXISTING `Expr.subexprs`, so it adds no
  new recursion: the nested `List Expr` pattern that defeats inference is
  elaborated once, where it already was.

### What was NOT repaired, and is now named

Inch 5's handler is reverted to inch 3's signature. The attempt to pass
`evalExpr ctx` into the handler as a closure is **why a recursive function
handed to an opaque callee cannot be shown to terminate** — nothing
constrains what the callee does with it. Supplying the caller's scope without
a closure needs an `evalArgs` inside the mutual block feeding the handler
VALUES; that is inch 5's open problem, and `evalArgsLR` is kept as the shape
it will re-attach to.

Two changes on one tenure would have been a gamble at 1-3 hours per verdict,
so this landing repairs the latent defect and lands the finding; the handler
is a separate ticket.

---

## 2026-08-23-c-6 — STMT-59 answered: **(a), with a named (b) subset already scheduled**

`tools/editions.sh` reports the C tier at 3.02× (sibling 2213 / trunk 732),
theorems 7/0, and **no census naming the sibling's FILES**. §2.4(1) asks for
file-level conviction. Here it is — produced, not asserted, and it needed no
tenure.

### The file-level census

| file | lines | `J.2(` | `J.3.` | `C17` | §clauses |
| --- | ---: | ---: | ---: | ---: | ---: |
| **trunk** `Ast.lean` | 382 | 0 | 0 | 0 | 1 |
| **trunk** `Json.lean` | 318 | 0 | 0 | 0 | 1 |
| **trunk** `Load.lean` | 83 | 0 | 0 | 0 | 0 |
| `C23.lean` | 89 | 1 | 0 | 5 | 14 |
| `C23/Value.lean` | 448 | **16** | **11** | **12** | 71 |
| `C23/Memory.lean` | 829 | **47** | 1 | 3 | 95 |
| `C23/Expr.lean` | 910 | 2 | 3 | 0 | 82 |
| `C23/Stmt.lean` | 628 | **0** | **0** | **0** | 64 |

**The trunk is clean: 783 lines, zero Annex-J references, zero C17 contrasts.**
Its version-neutrality is not a claim, it is a measurement.

### The answer: (a) — and the ratio is what §1.4 PREDICTED

`docs/family-architecture.md` §1.4 said, before any of this was written:
*"M2's inches 2–5 — memory model, expression semantics, statements, calls —
are all rules an edition decides, so within the priced ~15–20 sessions `C23/`
holds most of the tier."* The sibling being 3× the trunk is that prediction
coming true, not drift away from it. **§2.4's thin-siblings expectation is
calibrated on tiers whose sibling holds a DELTA; this tier's sibling holds the
SEMANTICS, and the trunk holds an AST and an ingester.**

The sharper test, and the one that actually answers §2.4: **what would a C17
sibling differ in?** From this lane's own verified work — `IntTy.minVal` (C23
mandates two's complement at §6.2.6.2p6 NOTE 2; C17 permitted three
representations), the Annex J indices (C23 numbers J.1/J.2/J.3; C17 does not,
so `J.2(35)` is not a C17 citation form), `realloc(p,0)` (UB in C23, not in
C17), and every renumbered §6.5/§6.8 citation. **That is roughly ONE definition
plus a citation layer — a genuine delta.** The other ~2900 lines would be
character-identical, which is the honest reading of the 3.02×: the sibling is
big because the SEMANTICS is big, not because the editions differ by 2213
lines.

### The (b) subset, named and already scheduled

The census also convicts, and I am not going to round it away:

1. **`Halt` / `Outcome` / `Cause` / `Refusal` in `Memory.lean` are
   family-level, not C23-level.** `LeanModels/Core/Outcome.lean` now carries
   exactly this shape. This is the Core adoption already ticketed behind the
   inch-5 repair, priced at **~11 real edit sites, 53 insulated**. It is the
   single largest genuinely-misplaced block in the sibling.
2. **`Stmt.lean` carries ZERO Annex-J references and zero C17 contrasts** —
   the least edition-specific file in the sibling by a wide margin. Its 64
   clause citations are §6.8, which C23 renumbered, so it is edition-scoped by
   CITATION and not by content: statement semantics is the same language in
   both editions. It cannot simply move, because it depends transitively on
   `Value.lean`'s `minVal`, which is genuinely C23 — **but that dependency is
   the whole reason it sits in the sibling, and that is worth stating rather
   than leaving the reader to infer a richer justification than exists.**

### Theorems 7/0 — already fixed by the landing in flight

The gate saw `7/0` (all in the sibling, none on the trunk). The termination
repair adds **5 theorems to the trunk** (`Expr.size_member`, `size_index`,
`size_paren`, `size_call`, `sizes_cons` in `Ast.lean`) because the size
measure belongs where the AST is. Current counts in the working tree are
**18 sibling / 5 trunk**. The metric will move on its own when that lands.

### Ordering

Unchanged and not reordered: **inch-5 repair → Core adoption → any further
consolidation.** Item (1) above IS the Core adoption, so the (b) work is
already in the queue in the right place; item (2) is a note for whoever
revisits the trunk boundary, not work I am scheduling ahead of the repair.

---

## 2026-08-23-c-7 — THE TERMINATION REPAIR IS **GREEN**, and it took three tenures to state one measure

### Verdict

`lake build` **exit 0**; `docs_check` **87/87**; `diff_test` **1427 cases, 0
failed**, 116 whitelisted, 1311 matched; the dependent-fixture gate
(`Examples.c.sunfish.{expr,memory,guards}`) **green, 16 jobs**;
`script_corpus` **65 scripts, 0 failed**. Coverage: **scoped** — the touched
modules and everything they import, plus the three importers named as an extra
gate, because a scoped green does not otherwise cover modules that import the
touched ones.

The evaluator's recursion is now justified by a **written measure** rather
than by inference: `2 * Expr.size e + 1` for `evalLValue`/`evalExpr`,
`2 * size + 2` for the address helpers, with `memberAddr`/`indexAddr` taking
SUBTERMS instead of rebuilt nodes.

### Three tenures, three different failures — and none was the design

The repair was right from the first attempt. What cost three tenures (**~5.5
hours of queueing**) was everything around it:

1. **`size_pos` could not be proved by `cases e` alone** — `typeTrait` and
   `constExpr` carry an `Option Expr`, so `subexprs` has two clauses each and
   `cases` does not split them. Removed rather than repaired: the measure
   never needed positivity.
2. **`simp [...]; omega` where `simp` already closed the goal** — "No goals to
   be solved". `<;> omega` is a no-op when simp closes and a discharge when it
   does not.
3. **`termination_by` in the wrong PLACE.** I used the old Lean syntax — a
   block after `end` naming each function. This repo's convention
   (`Sv/Param2.lean`) puts it INSIDE the mutual block after each body.
4. **The measure was stated but not USABLE.** `omega` had no fact relating
   `sub.size` to `(unop …).size`, because the first attempt proved equations
   only for `member`/`index`/`paren`/`call`. **A stated measure is only as
   good as the lemmas that let the checker use it** — every constructor the
   evaluator recurses into needs its own equation. Seven were missing.

Point 4 is the one worth keeping. Stating a measure does not discharge the
obligation; it *relocates* it into a set of equations that must be complete,
and completeness there is checkable by eye against the recursion sites in a
way that "inference found something" never was.

### A process cost worth naming: enqueue LAST

One tenure was consumed entirely by a guard doing its job. `triad.sh` records
the tree hash at enqueue and refuses to build a tree that changed afterwards —
*"a queued tenure reads the source at BUILD time, so this run would verify a
tree nobody asked it to."* I committed the STMT-59 answer after ticketing, and
the run correctly declined, 85 minutes later. **Enqueue is the LAST action
before waiting**, and a second guard (A6: refusing to build mid-rebase) caught
the same class of mistake ten minutes afterwards. Both guards are right; both
cost a queue slot because I did not respect the ordering they encode.

---

## 2026-08-23-c-8 — CORE ADOPTED: the guard this lane wrote is now enforced for every tier

The HOLD at `2026-08-23-c-1` is released. `LeanModels/Core/Outcome.lean` carries
a payload that **subsumes** this lane's, so adoption is a substitution at
`σ := Mem` rather than a rewrite.

### What was deleted, and what replaced it

| deleted here | now from `Core` |
| --- | --- |
| `inductive Halt (α)` + its `BEq`, `bind`, `Monad`, 3 `@[simp]` lemmas | `Loud π σ` / `HaltWith π σ` |
| `inductive Cause` (3 constructors) | `RefusalCause π` (4) |
| `abbrev EvalM := ExceptT Refusal (StateT Mem Halt)` | `SemMWith Mem Refusal CDetail Mem` |

**Both structural guards are now Core's, not this lane's.** `Loud`'s `BEq`
ignores the snapshot and `Loud.observable` has nowhere to put a `σ` — the two
properties this lane argued for at §3.4, lifted so that no tier writes them
again and a tier that *forgets* to cannot silently promote a diagnostic into a
verdict.

### Core's taxonomy is richer, and the extra class is one this lane owes

`RefusalCause` has four constructors where this tier had three:

| this tier | `RefusalCause` |
| --- | --- |
| `ub` | `.undefined` |
| `unsupported` | `.unsupported` |
| `libc` | `.environment` |
| *(owed)* | **`.orderDependence`** |

The fourth is exactly the verdict Thomas's `∀ order` ruling needs for a program
whose observable depends on argument evaluation order — the `J.1(16)` domain
this lane measured at **7 sites** (`docs/c23-spec-mirror.md` §5.3). **Adoption
did not just remove duplication; it supplied a verdict this tier had named and
could not express.** `π := CDetail := Unit` for now, because the prose already
carries the detail; `π` is where those 7 sites go if the verdict later wants to
name them.

`Outcome` is KEPT as this tier's own type rather than folded into
`Loud.observable`, and the reason is not sentiment: a scoreboard needs the
REFUSAL VALUE to read its `J.2` index, which a `String × String` observable
deliberately discards.

### Price, against the estimate

Estimated **~11 real edit sites + 2 aliases, 53 insulated**. Actual: the two
named primitives (`refuseUnsupported`, `exhausted`), five destructure sites
(`EvalM.verdict`, `ExecM.run`, `EvalM.run`, `Refusal.cause`, `Outcome.cause?`),
three type aliases, and **14 gate updates** across the three fixtures — the
gates cost more than predicted because `Cause.ub`/`libc`/`unsupported` appear
in assertions, which the site census counted as destructures but not as
per-occurrence edits. **The 53 `refuseUnsupported` call sites cost exactly
nothing**, as predicted: routing every refusal through a named primitive is
what made a substrate change a one-definition edit.

### Stmt.lean's move toward the trunk: NOT free, so NOT noted as ready

The instruction was to fold this in only if the adoption made the dependency
explicit. **It did not.** `Stmt.lean` still imports `C23.Expr`, which imports
`C23.Value`, where `IntTy.minVal`'s two's-complement commitment lives; the
adoption changed the monad, not the import graph. So the observation from
`2026-08-23-c-6` stands unchanged and unhooked: `Stmt.lean` is edition-scoped
by CITATION alone (zero Annex-J refs), and moving it would need the `minVal`
dependency parameterised, which is a real piece of work and not a side effect
of anything landed here. Recorded so the next lane does not go looking for a
hook that exists.

### For the editions gate's CONVICTED-BY column

The file-level census the gate asked for is **`docs/backlog/c.md`
§ `2026-08-23-c-6`** — per-file line counts with `J.2(`, `J.3.` and `C17`
densities for all eight C-tier files, the (a)-with-named-(b) verdict, and the
delta a C17 sibling would actually carry. That is the citation the QoL lane's
tool should point at for this tier.

---

## 2026-08-23-c-9 — the audit's five rows, all FIXED; two were claims that had never been checked

`docs/quality-audit-2026-08-23.md` § `c` — five rows, none high. All five are
correct and all five are fixed. Two of them are the same failure this lane has
now hit three times: **a claim nobody had an instrument for.**

### MEDIUM · coverage · `Value.lean:38` — the widths did not "come from" the profile

The docstring said widths "come from the ABSTRACT profile". They are
**hand-transcribed literals** (`def int_ : IntTy := ⟨true, 32⟩`), and
`--check` gates a HOST against the JSON via clang — it never reads a Lean
file. Nothing in `tools/` or `harness/` compared the two.

Fixed BOTH ways. The docstring now says the profile is the widths'
**CITATION, not their SOURCE**; and **`harness/c_profile_probe.py
--check-lean`** now closes the gap for real — it parses the `IntTy`
definitions out of `Value.lean` and fails loudly if a width disagrees with the
profile fact it claims to follow. Deliberately a PARSE, not an import, so the
check runs anywhere the two committed files do, with no toolchain in the loop.

**Non-vacuous by measurement**: perturbing `int_` to 64 bits gives
`int_32 (sizeof(int) == 4) forces int_ to 32 bits, Lean says 64`, exit 1. It
also refuses to pass when it parses ZERO definitions, because a check that
matched nothing would read green forever.

### MEDIUM · provenance · `Examples/c/sunfish/memory.lean:20` — cited to a file with no layout in it

The struct-layout table was cited to `docs/c-profile.json`, which carries 13
facts and **not one layout offset**; `c_profile_probe.py` does not probe layout
at all. The offsets were real — measured by compiling `_Static_assert`s on both
targets — but the citation pointed somewhere they have never been. Corrected to
say exactly what was done, and to say that the profile supplies the TARGETS
while the offsets are their own measurement.

### LOW · docdrift · `Stmt.lean:343` — a headline refuted by its own parenthetical

*"all 50 carry all three clauses (48 `init`, 49 `cond`, 50 `inc`)"* — if 48
carry `init`, two do not. Now reads: **three of the 50 omit a clause (two omit
`init`, one omits `cond`)**, which is what the next sentence already said. The
identical wording had propagated to `docs/c-semantics-design.md`; fixed there
too.

### LOW · absence · `c_api_census.py:187` — provenance transcribed, not computed

`source` and `sha256` were hardcoded literals describing a tarball the script
never opens. Now **computed from the tree actually read** (`SRC`), as a
deterministic digest over every file's path and bytes in sorted order, and an
unreadable file is a loud exit rather than a silent gap.

### LOW · absence · `c_suite_census.py:138` — a swallowed read failure

`source_facts()` returned `{}` on `OSError`, and the caller does
`row.update(...)`, so an unreadable test produced a row that merely LACKED its
source facts — **indistinguishable from a test that has none**. That is the
never-hide-errors law, and it was mine. Now a loud `SystemExit`: *a census that
silently drops a file it could not read reports a wrong answer, not a smaller
one.*

### The pattern across three of these

`Value.lean`'s widths, `memory.lean`'s offsets, and — earlier today —
`c_construct_census`'s `--compare` were all **claims with no instrument
behind them**, and all three read green for exactly as long as nobody looked.
The audit found in one pass what this lane had walked past repeatedly. The
standing correction is the one already written at `2026-08-23-c-5` for
termination and it generalises: **a claim that cannot fail is not a check**,
and the fix is always to build the instrument, not to soften the sentence.

---

## 2026-08-23-c-10 — THE ADOPTION'S TENURE CAME BACK RED, and the one defect was sitting in its own diff's CONTEXT

### The verdict, recovered rather than re-run

The Core-adoption ticket (`1787486390521832000-49734-c`) **did** run. It
queued **8008 s** — 2 h 13 m — behind five lanes, acquired at 16:16:14, and
was **RED in 15 seconds**.

Recovering it was itself a lesson. `triad.sh` writes its build output to
`$TMPDIR/triad-build.XXXXXX`, and that file contains **only `lake build`
output** — no ticket, no lane, no branch. Sixty-eight such logs sat in
`$TMPDIR`, and grepping them for `cadopt`, `c-core-adoption` or the lane tag
matched **nothing**, because none of those strings is ever written into a
build log. The lane's own transcript (`say` lines: the ticket, the queue
waits, the classification, the verdict) goes to whatever file the detached
runner redirected to — here `scratchpad/triad-c.log`. **The ticket name lives
in the LANE's log; the errors live in the TRIAD's log, and only the lane's log
names the triad's.** Recovery is: find the lane log by CONTENT, read the `full
log:` line at its foot, and follow it.

### What was red

Build **exit 1** at **17 of 18** targets. Everything under `LeanModels/C`
built green — including the three drain-amendment theorems the hand-off named
as the sole expected unknown, which needed no repair at all and printed the
ordinary `[propext, Classical.choice, Quot.sound]`. `Examples.c.sunfish.stmt`
was never attempted; lake stops at the first failing module.

Two errors, both in `Examples/c/sunfish/expr.lean`, and **both one defect**:

```
:106:36  Function expected at
           Halt
         but this term has type ?m.1
:133:48  Invalid dotted identifier notation: the expected type of `.ok`
         could not be determined
```

`runIndetRaw`'s return type still names the **deleted local `Halt`**. The
second error is a cascade of the first: with the scrutinee at `?m.1` the
match's arms have no expected type.

### Why the site census missed it, and it is not a counting error

The adoption's own diff **touches this file** — one line, `Cause.ub` →
`(.undefined () : Cause)`, at `:118`. The stale `Halt` is at `:106`, which
puts it **inside that hunk's three lines of leading context**. The census
counted occurrences of the deleted *value* constructors and destructures; a
**type annotation** naming the deleted type is a fourth shape, and it appeared
on screen, greyed, directly above an edit that was made. The generalisable
form: **a census over a deleted definition must enumerate every syntactic
position the name can occupy — type annotations included — and diff context is
the worst place to review one, because the eye reads it as already-checked.**

### The repair

`LeanModels.HaltWith CDetail Mem (Except Refusal CVal × Mem)` — which is
exactly what `EvalM.run` returns (`Except (Loud CDetail Mem) (Except Refusal α
× Mem)`). Written with the `LeanModels.` prefix because this file opens
`LeanModels.C.C23` and not the root, the same reason `LeanModels.C.CSpan` is
spelled out ten lines above it.

Verified BEFORE the ticket, at **2.7 s** and no tenure, by `tools/check.sh` on
a scratch file outside the lake globs that restates both shapes — the
`EvalM.run` type and the `.ok (_, m)` destructure the memory-retention gate
does on it. Exit 0, 0 warnings. `check.sh` **refuses** the library file itself
(`CASE refuse-library`), which is right, and the scratch restatement is the
sanctioned way round it.

### The rest of the tree is clean, checked rather than assumed

`Cause.ub` / `Cause.libc` / `Cause.unsupported` / `Halt.ok` / `Halt.timeout`:
**zero** hits under `LeanModels/C` and `Examples/c`. The remaining `Halt`
mentions in the tier are docstring prose; every other `Halt` in the repository
belongs to the **ES lane's own local `Halt`** (`LeanModels/Es/Completion.lean`),
which is not this adoption's business.

### The re-gate is a SPINE build, not the `tier` one the classifier would pick

The first tenure classified `tier` and built 18 targets. It was right then.
It is wrong now: master moved **52 commits** under this branch, and `Core` is
in this tier's import closure, so a scoped green would say nothing about
whether the adoption still holds against the Core that exists. The re-ticket
therefore names **no build target at all** — `BUILD_TARGETS=""` is every
default target — and pays the full build deliberately.

### VERDICT — GREEN, and it is a SPINE green

`tools/triad.sh --lane cadopt` with no `--classify`: queued **4954 s**, held
the machine **42 minutes**, build **exit 0**, **3765 jobs**, *Build completed
successfully*. **Zero** `error`/`✖`/`sorry` lines in the whole log.

| gate | result |
| --- | --- |
| `lake build` (every default target) | **exit 0**, 3765 jobs |
| `tools/docs_check.py` | **91 / 91** marked blocks, 36 illustrative-exempt |
| `harness/diff_test.py` | **1427 cases, 0 failed** — 1311 matched, 116 whitelisted-unsupported |
| `harness/c_profile_probe.py --check-lean` | **9 / 9** width/signedness points, 8 `IntTy` defs parsed |
| `harness/script_corpus.py` | **65 scripts, 0 failed** — 50 matched, 15 loud-blocked |
| `tools/backlog-index.sh --check` | in sync, 189 entries |

The two targets that decided it: `Examples.c.sunfish.expr` ✔ (the module that
was red) and `Examples.c.sunfish.stmt` ✔ — **the one the first tenure never
reached**, because lake stops at the first failing module and `stmt` was
target 18 of 18.

**COVERAGE (§5.4a): SPINE — every default target, no scope caveat.** This is
the one claim a `tier` green could not have made, and it is the claim that was
needed: `Core` moved **52 commits** under this branch (`Core/Order.lean` new,
`Core/Outcome.lean` +67 lines of `PartialOrder` / `CCPO` / `MonoBind` instances
on `HaltWith`, all **purely additive** — 118 insertions, 0 deletions), and the
adoption's whole premise is that this tier's monad IS Core's. A green scoped to
the C modules would have re-verified the adoption against the Core it was
written for, not the Core that exists.

### Axiom ledger, from this build

| theorem | axioms |
| --- | --- |
| `Mem.get?_alloc`, `Mem.resolve_alloc`, `Mem.resolve_ok`, `Mem.loadBytes_storeBytes` | `propext, Quot.sound` |
| `Mem.get?_set_self` | `propext` |
| `Mem.resolve_kill` | `propext, Classical.choice, Quot.sound` |
| `and_shortCircuits`, `or_shortCircuits`, `cond_takesOneArm` | `propext, Classical.choice, Quot.sound` |

The three drain-amendment theorems — the hand-off's sole expected unknown,
because their simp sets gained `Except.bind`/`Except.pure` under the new monad
— **needed no repair and carry no new axioms.** The unknown resolved to
nothing; the defect was somewhere nobody had flagged.

### The queue, for Amendment 9's record

Enqueued 19:25:58 at depth 6, acquired 20:50:00 — **1 h 22 m**, behind `ada`
and `sv` (a 40-minute full build) with `leantier`, `softfloat` and `wasm`
ahead in the queue. One ticket ahead of this one was **reaped by the staleness
sweep** (`reaped stale ticket …-go (pid 73698 dead)`) — A9's sweep doing
exactly its job, visible in the lane log, and worth one line here because a
queue that only ever grows is the failure mode the sweep exists to prevent.

---

## 2026-08-23-c-11 — INCH 5's OPEN PROBLEM IS CLOSED, and the ∀-order discharge could not have been attempted before it

The dispatch was the 7-site `J.1(16)` ∀-order discharge. The first thing
that work found is that **the domain was unreachable**, so the discharge
would have been a theorem about seven refusals. This entry is the repair
that makes it reachable; the discharge itself is the next rung.

### The finding, and it is one line of the model

`docs/c23-spec-mirror.md` §5.3 describes the `J.1(16)` domain as *"7 call
sites where the effectful argument is a nested call"*. That sentence names
the domain **and** the reason it could not be evaluated:

```
LeanModels/C/C23/Stmt.lean:562   (before)
  | some _ => refuseUnsupported
      s!"nested call to '{nm}' — argument evaluation is inch 5's open problem"
```

**Every** call whose callee was a defined function refused. So an `∀ order`
theorem stated over the seven sites would have quantified over seven
`unsupported` refusals — true, unfalsifiable, and evidence of nothing.
That is `2026-08-23-c-5`'s law arriving in a new costume: **a claim that
cannot fail is not a check**, and a quantifier over an empty-in-practice
domain is exactly such a claim. The obligation was therefore inverted:
make the domain reachable first.

### Why it was unreachable: two rejected shapes, and the third

`CallHandler` had been through two designs before this one, and both
failure modes are recorded in the type's own docstring:

| shape | what it bought | what it cost |
| --- | --- | --- |
| `(Expr → EvalM CVal) → …` — hand the handler the evaluator | arguments evaluate in the caller's scope, per §6.5.3.3p4 | **termination died**: a recursive function passed into an opaque callee is constrained by nothing |
| `Expr → List Expr → EvalM CVal` — hand it the arguments unevaluated | terminated | the handler holds the CALLEE's scope and has no evaluator, so it could not do the job at all |
| **`Expr → List CVal → EvalM CVal`** — evaluate them first | both | one extra decrease goal, and `Expr.size_pos` |

The third shape is the one the second's own docstring predicted:
*"the shape that will solve it is an `evalArgs` inside the mutual block
below, feeding the handler VALUES."* The prediction was right and the
reason is worth stating generally: **the argument walk needs `evalExpr`'s
recursion, so it has to live where `evalExpr`'s MEASURE lives.** Handing
the evaluator out moves the recursion somewhere no measure covers; keeping
the walk in the mutual block costs one goal.

The expression layer is still FUEL-FREE, and for the reason it always was:
`evalArgs` is structural on `Expr`, not on a call graph. The fuel-bearing
recursion stays in `callFn`, one level down per call, which is what the
new fuel gate measures.

### `Expr.size_pos` comes back, and the earlier removal was a tactic verdict read as a fact

The list measure is `2 * Expr.sizes es + 2`. Three decrease goals:

| goal | needs |
| --- | --- |
| `evalExpr (.call c args)` → `evalArgs args` | `+2 < 2·c.size + 3` — free |
| `evalArgs (e :: es)` → `evalExpr e` | the `+2` beating `evalExpr`'s `+1` when the tail is empty |
| `evalArgs (e :: es)` → `evalArgs es` | **`0 < e.size`** |

`Expr.size_pos` had been tried at `LeanModels/C/Ast.lean` and removed, with
the reason recorded: `typeTrait` and `constExpr` carry an `Option Expr`, so
`subexprs` has two clauses each and `cases e` does not split them. **That
diagnosis was right about the tactic and wrong about the fact.** Every
`subexprs` clause emits the node itself — as `e :: …` or as the catch-all
`[e]` — so the list is never empty and the lemma is simply true:

```lean
@[simp] theorem Expr.size_pos (e : Expr) : 0 < e.size := by
  unfold Expr.size
  rw [Expr.subexprs.eq_def]
  split <;> simp
```

`eq_def` turns the definition back into its `match` and **`split` splits the
CLAUSES**, including the `some`/`none` pair that `cases e` leaves as one
unreduced variable. Three lines. The general lesson, and it is the second
time this lane has paid for it: **"my tactic failed" and "the fact is
false" are different findings, and only one of them is worth recording as
a reason not to try.** The removal note is now corrected in place rather
than deleted, because the wrong version is the instructive half.

### Non-vacuity, gated rather than asserted

Every call gate this tier had entered through `callByName`, which takes
**already-evaluated** arguments — so not one of them exercised a call in
ARGUMENT position. New gates in `Examples/c/sunfish/stmt.lean`:

* `c1` — `return pyfloordiv(7, 2);` — a call in expression position, its
  arguments evaluated by `evalArgs`. Answers **3**.
* `c2` — `return pyfloordiv(pyfloordiv(7, 2), 2);` — **the `J.1(16)` shape
  itself**: two arguments, one of them a call. Answers **1**.
* the outcome of `c2` is `"ran"`, stated as a match over all four
  `Outcome` constructors, so the gate fails loudly if it ever refuses again.
* `callByName 1` on the nested caller is a **`timeout`**, not a refusal —
  fuel still bounds nesting, and exhaustion stays unpooled with refusal.

`c2` is the gate that would have failed before this landing, and it would
have failed with `unsupported`, not with a wrong number.

### Two deletions and a message that had stopped being true

`evalArgsLR` is **deleted** rather than kept. It was the left-to-right walk,
sitting in `Stmt.lean` and unreachable, described as *"the shape the repair
will re-attach to"*. The repair did not re-attach to it — argument
evaluation had to move into `Expr.lean` to borrow the measure — so keeping
it would have left two answers to one question, which is what
`docs/family-architecture.md` §9.2 exists to stop.

`noCalls`'s message read *"call to 'x' — the call semantics is inch 5"*.
Inch 5 has landed; what remains true is that a bare `Ctx` has **no program
behind it**, so the text now says that. This is the `Stmt.lean:343` docdrift
class the audit named, caught before it aged.

### Model and code landed together

`docs/c-semantics-design.md` §4.1b said the handler *"takes the argument
expressions UNEVALUATED"*. That was the design, and it is now false, so it
is amended in the same commit rather than left for a reader to trip over.
`docs/c23-spec-mirror.md` §5.3 gains the reachability paragraph — the
J.1(16) row's status was never wrong about the count, only silent about
whether the seven could be run.

### What this does NOT claim

The ∀-order obligation is **not discharged**. Left-to-right is written down
as the canonical order and nothing more; `evalArgs` makes the property
STATABLE about a function instead of unstatable about an opaque handler.
The discharge — the effect-summary argument that at most one argument
writes what its siblings read, over the 7 sites, with `0` sites having two
effectful arguments to help — is the next rung and is named here so nobody
reads this landing as having done it.

### VERDICT — GREEN

`tools/triad.sh --lane corder --classify --build-target "LeanModels.C
Examples.c.sunfish.{expr,memory,stmt,guards}"`: queued **3714 s**, build
**exit 0**, **19 jobs**, zero `error`/`✖`/`sorry` lines. The build itself
took **17 s** — a scoped tier build on a warm clone, against 40 minutes for
the spine build this lane paid two rungs ago, which is the whole argument
for `--classify` when nothing shared has moved.

| gate | result |
| --- | --- |
| `lake build` (tier + the four C fixtures) | **exit 0**, 19 jobs |
| `tools/docs_check.py` | **91 / 91** marked blocks |
| `harness/diff_test.py` | **1427 cases, 0 failed** — 1311 matched, 116 whitelisted |
| `harness/c_profile_probe.py --check-lean` | **9 / 9** width/signedness points |
| `harness/script_corpus.py` | **65 scripts, 0 failed** |
| `tools/backlog-index.sh --check` | in sync, 197 entries |

**COVERAGE (§5.4a): SCOPED, and here the scope is the whole story.** A
scoped green does not cover modules that IMPORT the touched ones — so the
question is who imports the C tier, and the answer is measured, not
assumed: `grep '^import LeanModels\.C\(\.\|$\)'` over the tree returns
**16 lines, every one of them inside `LeanModels/C/` or `Examples/c/`**.
The C tier's importer set is exactly its own fixtures, all four of which
are named as build targets above. That makes this scoped green a complete
claim about the change, which a `tier` green is *not* entitled to be in
general — the entitlement comes from the import census, and it is recorded
here so the next lane checks rather than inherits it.

`Expr.size_pos` is a new `@[simp]` lemma, which is the one thing in this
landing with a blast radius beyond the tier. Measured too: nothing outside
`LeanModels/C/` mentions `Expr.size`, and the lemma is namespaced to
`LeanModels.C.Expr`.

### Axiom ledger

Unchanged, and that is the interesting part: adding a fifth function to
`evalExpr`'s mutual block did not disturb the three drain-amendment
theorems, which still prove and still carry `[propext, Classical.choice,
Quot.sound]`. Their proofs go through `simp [evalExpr, …]`, i.e. through
`evalExpr`'s equation lemmas, and those were the standing risk in
enlarging the block. Named here because it was a risk that could have
cost a tenure and did not.

---

## 2026-08-24-c-12 — RUNG A: the ∀-order domain was never 215 sites, and measuring it discharged 208 of them

The dispatch was Rung A — `Expr.isPure` plus memory-invariance — named in
`2026-08-23-c-11` as the enabling half of the `J.1(16)` discharge. It
landed, and the interesting part is not the theorem: it is that **stating
the predicate re-measured the obligation and most of it went away.**

### The finding, and it is a number the register did not have

`docs/c23-spec-mirror.md` §5.3 has said *"domain measured: 7 sites"* since
inch 3, against **320** call sites. What it never said is what the 7 are a
residue OF. `Expr.isPure`, run over the ingested unit by the model itself:

| | |
| --- | ---: |
| call sites | **320** |
| …taking two or more arguments — the sites §6.5.3.3p10 can order at all | **215** |
| …of those, EVERY argument pure | **208** |
| …of those, at least one argument impure — the `J.1(16)` domain | **7** |
| …with TWO impure arguments | **0** |
| impure node kinds occurring in ANY call argument, corpus-wide | **1** — `CallExpr`, ten times |

**208 of the 215 orderable sites need no effect summary at all**: with
every argument write-free, no order can differ, because no order can
write. The seven are the same seven the register names, at the same lines
(`map_find_h:L428`, `fmt_move:L978`, `printf:L1301`,
`set_knob:L1317/1331/1363/1369`), reached this time through the predicate
the theorem is stated about rather than through the census's separate
notion of *"an effect"*. Two definitions, one number, and the gate asserts
the line numbers, not just the count.

> **A quantifier's domain is a MEASUREMENT, and measuring it is often most
> of the discharge: a census that names a residue owes the population the
> residue is a residue OF.**

Read the two sentences side by side. *"The J.1(16) domain is 7 of 320
call sites"* invites the reading that 313 sites were somehow already fine;
*"7 of 215 ORDERABLE sites, and 208 of the other 215 fall to a syntax
check"* says which fact does the work. The first was true for two inches
and told nobody that Rung B's real price was 7 sites out of a population
that a `Bool`-valued function decides.

### What landed

**`Expr.nodeIsPure` / `Expr.isPure`, in the C23 sibling and not on the
trunk.** `isPure e` is `e.subexprs.all nodeIsPure` — **no new recursion**,
the same reason `Expr.size` is defined through `subexprs`
(`2026-08-23-c-11`). It is in `LeanModels/C/C23/Expr.lean` and not in
`LeanModels/C/Ast.lean` on purpose: the trunk's own docstring says *"this
file is a TYPE, not a semantics"*, and a predicate whose content is
*"which operator SPELLINGS reach `storeAt`"* is a claim about this
evaluator, not a query over the term. The cost of that placement is that
`Expr.isPure e` does not get dot notation, which is the honest price of
keeping the boundary where §2.4 put it.

**The memory-invariance theorem**, by strong induction on `Expr.size`
over `evalExpr` and `evalLValue` together:

```
theorem evalExpr_memInvariant (ctx) (e) (h : Expr.isPure e = true) :
    MemInvariant (evalExpr ctx e)
```

`MemInvariant x` quantifies over `r : Except Refusal α`, so it covers the
REFUSAL branch too — which is not decoration. `ExceptT` outside `StateT`
is the state-retaining order, so a refusal carries a memory, and a
predicate that spoke only about success would say nothing about the one
branch the layer order exists to keep world-aware.

`evalArgs` never appears in the induction, and that is the honest shape:
`nodeIsPure` makes a `call` node impure, so the arm that reaches an
argument walk is vacuous. A call is precisely what this theorem cannot
speak for, and the proof is structured so that it cannot pretend to.

### The over-approximation, and how a conservative predicate is DEFENDED

`isPure` convicts a write-capable node **anywhere** in the term —
including under a `&&` that would never run it and under a `sizeof` whose
operand §6.5.4.4p2 does not evaluate at all. That is slack, and slack is
usually where a predicate quietly stops being useful.

Measured instead of excused: **across all 320 call sites and every
argument of every one of them, the only impure node kind that occurs is a
`CallExpr`** — ten of them. Not one argument in the corpus contains an
assignment, a compound assignment or an increment, so the coarseness
misclassifies nothing here, and the gate that says so changes the day it
would.

> **An over-approximation owes a COUNT of what it over-convicts, not an
> apology; the defence of a conservative predicate is the measurement of
> its slack on the corpus it is used on.**

**And one classification that is deliberately not the convenient one.** An
`unsupported` node is IMPURE, though this evaluator refuses it and a
refusal can never return `.ok`. Calling it pure would have been sound
today and would have become unsound the day the construct is modelled,
silently.

> **"The model declines" is not "the construct does not write."** A
> predicate that pools the two is a predicate whose soundness expires
> without a diff.

### §9.3 CONVERGENCE — the run seam is family-level, and this is the second tier to need it

`LeanModels/Go/Obs.lean` §1 lands `run_bind` for `GoM`; this landing needs
the same lemma for `EvalM`. **`GoM` and `EvalM` are both
`LeanModels.SemMWith`**, and the C proof is Go's with four substitutions
— `GoWorld → Mem`, `Panic → Refusal`, `SpecRef → CDetail`, `Unit → Mem` —
and **not one line of either mentions a language**.

Go's own header says *"the ORDER lifts; the CONGRUENCES don't"*, and it is
right about Python's `Res`, which really is a different monad with an
`.exn` arm. It is not right about two tiers that share the substrate.

> **A congruence that is generic in the SUBSTRATE'S parameters is not a
> per-tier congruence; "the congruences don't lift" is a statement about
> a different monad, not about a second consumer of the same one.**

**Not taken unilaterally.** Lifting `run_bind` and its four step lemmas to
`LeanModels/Core/Outcome.lean` is a SPINE landing — a full build under
§7.1's classification, in a file two other lanes are live in — so it is
priced here and left for the coordinator: **5 theorems, ~40 lines, zero
proof change, and Go's rows become one-line instances.** Until it lands,
the C tier's copy carries this paragraph so that the duplication is
visible in the code rather than only in an audit.

### A MEASUREMENT THE PROCESS OWES: A17's swap gate is a HIGH-WATER MARK on macOS

This proof — 532 lines — was written and ticketed **without a single
iteration**, because `tools/check.sh --iterate` refused every one of ~30
attempts across the session, all with the same verdict:

```
CASE   refuse-swap
WHY    swap is 88.5% in use, over the line of 50%
STATE  load 2.42 (line 10), swap 88.5% (line 50%)
```

**The machine was not under memory pressure.** At the same moment,
`memory_pressure` reported **"System-wide memory free percentage: 59%"**,
`vm_stat` showed 78 250 free plus 253 176 inactive pages, and the load
average was 2.4 against a line of 10. The gate and the machine disagree by
construction, and `read_swap_pct` (`tools/check.sh:302`) is where:

* on Linux it reads `/proc/meminfo` `SwapTotal`/`SwapFree` — **current**
  usage, which falls when pressure falls;
* on macOS it reads `sysctl vm.swapusage` `used`, which is **swap the
  kernel has allocated and not reclaimed** — a high-water mark that
  survives the pressure that caused it, and in this session drained from
  8 274 MB to 8 154 MB in forty minutes.

So the same 50% line means *"is swapping now"* on one host and *"has ever
swapped this much since boot"* on the other. **A box that swapped once
has A17 closed for the rest of its uptime**, which turns the amendment
that exists to price proof iteration back into the starvation it was
written to fix.

> **A portable gate whose two implementations measure different
> QUANTITIES is not portable — it is two gates with one name, and the
> line only means what the instrument means.**

Not fixed here, and deliberately: it is the QoL lane's gate, A17 is a
DRAFT with five tightenings already flagged, and *"my lane is blocked"* is
the worst possible reason to move a shared safety line. Filed as an
inbound below. The suggested instrument is `memory_pressure`'s free
percentage or `kern.memorystatus_vm_pressure_level` — both report
pressure rather than allocation — with the swap reading kept as a
secondary on Linux where it means what the line says.

### A SMALLER ONE, and it cost twenty minutes: a mirror is validated by an ALREADY-GATED number

The corpus numbers above were measured in Python first (§9.0a,
census-first — no Lean, no tenure) by mirroring `TranslationUnit.exprs`.
The first mirror was **wrong**: it handled every statement kind the
envelope spells with a `kind` field and produced **156** call sites
instead of 320. The bug is that an expression in statement position has
**no wrapper kind at all** — `Json.lean:276` falls through to
`.expr (← parseExpr j)`, so a `CompoundStmt`'s body holds raw
`BinaryOperator` and `CallExpr` nodes — and a mirror that scanned for
statement kinds simply did not see them.

Nothing about the wrong mirror looked wrong. What convicted it was
running it against a number **this repository already gates**:
`indirectCalls == 19` (`Examples/c/sunfish/guards.lean`). The broken
mirror said 4.

> **A new instrument is validated against a number that is ALREADY GATED,
> before it is trusted for a number that is not — otherwise its first
> output is both the measurement and its own oracle.**

### What this does NOT claim

**The `J.1(16)` obligation is not discharged.** Rung A pays the sibling
half — *the siblings do not write* — for all seven sites and pays the
whole obligation for the 208 that have no impure argument at all. Rung B
is the other half: at each of the seven, one nested call, and whether it
writes what its siblings read.

**And Rung B's statement is not the obvious one**, which is worth writing
down before someone tries: even where every argument is pure, two orders
can still disagree about **which refusal is reported**, when more than one
argument would refuse. Order-independence holds for the value and for the
memory, never for the run. The observable Rung B quantifies over has to be
the ANSWER, not the trace — and `Outcome`, which already has nowhere to
put a `Mem`, is the type that says so.

### TENURES — and tenure 1's thirteen errors had ONE cause

**Tenure 1 — `crunga 44165`, LOCK ACQUIRED after 2 317 s, RELEASED 15 s
later. RED, and therefore an ABORTED triad: gates not run.** 13 `unsolved
goals` errors, every one of them inside the new block, nothing before line
1357 — so the predicate, the extraction lemmas, the whole run seam and the
entire `MemInvariant` algebra had elaborated clean.

The thirteen were one defect. `MemInvariant` was a `def` returning a `∀`,
and the closing tactic's `intro` **unfolds definitions** — so on a goal
`MemInvariant (…)` the `intro` alternative fired before `split` ever could,
stripped the predicate down to a bare `m' = m`, and every subsequent
`apply` then unified against *that*. The signature is unmistakable once
seen: thirteen goals of the form `⊢ pure m'✝ m✝ = Except.ok (?r, m'✝)`,
with a metavariable where a computation should be.

> **A tactic that dispatches on a goal's HEAD needs that head to be
> stable, and a `def` that unfolds to a binder has no stable head.**

The repair is one word: `MemInvariant` is a `structure` with a single
field. A structure is opaque to `intro` by construction, so the property
the tactic depends on is now a fact about the TYPE rather than a habit of
the tactic list. `map'` joined the algebra in the same pass, because `simp`
normalizes `x >>= fun a => pure (g a)` to `g <$> x` and a goal can arrive
wearing the other spelling.

**Tenure 2 — `crunga 41896`, LOCK ACQUIRED after 1 944 s, RELEASED 14 s
later. RED, aborted triad. Thirteen errors became TWO**, and both were
`(deterministic) timeout at whnf` — the `sizeof` arm and the `constExpr`
arm, the two whose goals carry the deepest terms (an `Option.bind` through
an opaque `Layout` field; a `String.toInt?`).

The defect was not in the proof, it was in what the tactic COST. `mem_inv`
is a `first | apply … | apply … ` list, and `apply` runs at DEFAULT
transparency — so a failing `apply MemInvariant.evalArith'`
delta-unfolds `evalArith` and matches its nineteen-way `String` match
against the goal before giving up, once per alternative, per goal, per
step.

> **A tactic assembled from `first | apply …` pays its ENTIRE alternative
> list at default transparency on every goal; if the alternatives name
> non-reducible constants, that list is a search over their bodies.**

Every `apply` in `mem_inv` now runs `with_reducible`, so each lemma
matches only when the goal's head IS the constant it names and every
failure is one comparison. `maxHeartbeats` on the one twenty-arm
declaration is raised alongside and is labelled in the source as a
BUDGET rather than the fix — twenty cheap searches still sum.

**Tenure 3 — `crunga 22930`, LOCK ACQUIRED after 1 673 s, RELEASED 14 s
later. RED, aborted triad. Two errors became ONE**, and it named a third
kind of defect: not the proof, not the cost, but **how much a fallback
OPENED.**

`open_eval` is `first | simp only [evalExpr] | rw [evalExpr.eq_def]` —
per-clause equations where they fire, the whole-function unfolding where
they do not. On the `sizeof` arm the per-clause equation did not fire, so
the fallback ran and `split` then produced one goal per arm of the WHOLE
twenty-arm match. Nineteen of those are impossible — each carries a
hypothesis equating two different constructors — and nothing in the
tactic's list could say so, because "this arm cannot happen" is not a
`MemInvariant` fact.

> **A fallback that opens MORE than the primary path owes the extra goals
> a closer; otherwise the fallback converts a missing rewrite into a wall
> of unreachable obligations, and the error you read is about the wrong
> thing.**

The closer is one word: `contradiction`, which discharges a
constructor-mismatch hypothesis by `noConfusion`. It is cheap, it is
precise, and on the primary path it never fires.

### AND THEN THE INBOUND CAME BACK AS AN INSTRUMENT, IN THE SAME SESSION

Between tenure 3 and this landing the QoL lane landed
**`2026-08-24-qol-53`, "the politeness line was reading a high-water
mark"** — `--iterate` now gates on `memory_pressure:free%(macos)` instead
of `vm.swapusage used`. On the first check after rebasing onto it, the
same box that had refused ~30 consecutive attempts read **memory pressure
31 %** against the same 50 % line, and permitted the run.

The next two defects were found in **ten seconds each**:

* `contradiction` (above) — confirmed, not guessed;
* and the last one, which no amount of reading would have produced:
  `evalExpr`'s `sizeof` clause binds `key` with a **`have`, not a `let`**
  — Lean elaborates a non-dependent `let` in term position to `letFun` —
  and **`split` cannot see through a `have`**. One alternative,
  `simp only [letFun]`, and the file went green.

> **`let` in a definition can elaborate to `have`, and a `have` is opaque
> to `split`: a tactic that opens `match`es needs an alternative that
> opens BINDINGS, or a clause disappears behind its own local name.**

**The measurement, and it is the whole argument for A17.** Three defects
cost **5 934 s of queueing for 43 s of building**. The next two cost
**20 seconds, total.** The instrument was the difference; nothing about
the proof changed.

> **A courtesy protocol is worth exactly what its gate's INSTRUMENT is
> worth: A17 was not too strict, it was reading the wrong quantity, and
> the two are indistinguishable from inside the lane that is refused.**

**And the process note, because it is the same finding as the inbound
above from the other end.** Thirteen errors with one cause is exactly what
a first elaboration is for. This lane paid **2 317 s of queue** to see the
first cause, **1 944 s** to see the second and **1 673 s** to see the
third — **5 934 s of queueing for 43 s of building**, three defects each
one line, each of which a fifteen-second `lake env lean` would have shown —
because `--iterate` was refused for the whole session on a swap reading
that is a high-water mark. **The cost of A17 being closed is not the
iteration; it is that the iteration happens inside the lock.**

### VERDICT — GREEN

`tools/triad.sh --lane crunga --classify`, ticket
`1787544192801624000-80997-crunga`:

```
[06:03:13] LOCK ACQUIRED after 0s as 'crunga 80997'
[06:04:16] TRIAD DONE (build exit 0, gates green)
[06:04:17] LOCK RELEASED (mine)
```

**63 seconds of tenure, after 5 934 s of queueing across three red ones.**

| gate | result |
| --- | --- |
| `lake build` (build phase) | **exit 0, 18 jobs** |
| `lake build` (gate phase) | **exit 0, 38 jobs** |
| `tools/docs_check.py` | **91 / 91** marked blocks, 39 illustrative-exempt |
| `harness/diff_test.py` | **1492 cases, 0 failed** — 1367 matched, 125 whitelisted |
| `harness/refusal_census.py --whitelist --no-build` | green |
| `harness/c_profile_probe.py --check-lean` | **9 / 9** width/signedness points |
| `tools/backlog-index.sh --check` | in sync |
| `error:` / `✖` / `sorry` lines in the full build log | **0** |

**THE ELABORATION WITNESS (Built vs Replayed).** `LeanModels.C.C23.Expr`
is **Built (7.6 s)**, not replayed, and so are every module below it:
`Built LeanModels.C.C23.Stmt (457 ms)`, `Built LeanModels.C.C23 (222 ms)`,
`Built LeanModels.C (755 ms)`, `Built Examples.c.sunfish.guards (5.7 s)`,
`Built Examples.c.sunfish.memory (1.2 s)`, **`Built
Examples.c.sunfish.expr (1.5 s)`** — which is the line that matters, because
that is the file whose fifteen `#guard`s carry 320 / 215 / 10 / 7 / 0 / 208,
the seven line numbers, and the ten `CallExpr` nodes. A replayed fixture
would have proved nothing about them.

### Axiom ledger

The three Rung A theorems carry exactly `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`, no `native_decide`:

```
'LeanModels.C.C23.evalExpr_memInvariant'   [propext, Classical.choice, Quot.sound]
'LeanModels.C.C23.evalLValue_memInvariant' [propext, Classical.choice, Quot.sound]
'LeanModels.C.C23.evalArgs_memInvariant'   [propext, Classical.choice, Quot.sound]
```

And the three drain-amendment theorems are **unchanged**, which was the
standing risk in adding a `structure`, a macro and eighteen lemmas to this
file: `and_shortCircuits`, `or_shortCircuits`, `cond_takesOneArm`, same
three axioms as before.

### COVERAGE (§5.4a) — SCOPED, with one gap NAMED and then CLOSED

The build was `lake build Examples.c.sunfish.expr LeanModels.C.C23.Expr
LeanModels.C`. A scoped green does not cover modules that IMPORT the touched
ones, so the question is who imports the C tier, and the answer is measured:
`grep '^import LeanModels\.C\(\.\|$\)'` returns **16 lines, every one
inside `LeanModels/C/` or `Examples/c/`** — unchanged from
`2026-08-23-c-11`'s census, re-run rather than inherited.

**And one of those importers was NOT in the build.** This lane passed
`--build-target "LeanModels.C Examples.c.sunfish.stmt"` on all four tenures
and the flag is a **silent no-op** — `tools/triad.sh` parses it at line 245
and resets `BUILD_TARGET_ARGS=""` at line 435, after the argument loop. Filed
as `2026-08-24-c-14`.

> **A green's coverage statement is written by the LANE and is only as true
> as the flags it believes it passed; a widening flag that silently does
> nothing produces an honest lane making a false claim.**

The gap is closed rather than carried: `Examples/c/sunfish/stmt.lean` was
elaborated **after** the green under A17 — `tools/check.sh --iterate`,
**exit 0, TRUSTWORTHY** — against the fresh oleans the tenure had just
written. That is a real check and it is a DIFFERENT one from a build, so it
is recorded as what it is: the tier's other three fixtures are covered by the
tenure; `stmt` is covered by a lock-free single-file elaboration at the same
tree.

`Expr.isPure` and `Expr.nodeIsPure` are new names in `LeanModels.C.C23`, and
`mem_inv` / `open_eval` / `open_lvalue` are new tactic macros. Blast radius,
measured: nothing outside `LeanModels/C/` and `Examples/c/` mentions any of
them, and no lemma in this landing is `@[simp]` — the one thing
`2026-08-23-c-11` flagged as having reach beyond the tier was `Expr.size_pos`,
and this landing adds no such thing.

### What Rung B now costs

**7 sites, not 215**, and the shape is fixed: at each, one nested call and
the question of whether it writes what its siblings read. `evalArgs` makes
the property statable; `evalArgs_memInvariant` retires the sibling half at
all seven. The remaining obligation is an effect summary for one callee per
site, plus the observable question this entry named — the ANSWER, not the
run, because two orders can disagree about which refusal is reported.

### §9.0 — the tier's standing number

**`gcc.c-torture` 0 scored (runner needed).** Unchanged, and it will stay
unchanged until inch 6 builds the batch runner that creates the
denominator: the corpus is GPL and is fetched AT PIN by content hash,
never vendored (`docs/c23-goal.md` §2), so the number is a property of a
`lean_exe` driver this tier does not yet have. Rung A moved a proof
obligation, not a score, and says so.

---

## 2026-08-24-c-15 — THE SEAM IS IN `Core`, and the paragraph that made the duplication visible is deleted with it

`2026-08-24-c-12` found that `LeanModels/Go/Obs.lean` §1 and the C tier's
Rung A landing had independently proved the same `run_bind` for the same
`SemMWith` stack, priced the lift at *"5 theorems, ~40 lines, zero proof
change"*, and **did not take it** — a spine landing is not a tier commit's
to make. It was dispatched back; this is it.

### What landed in `LeanModels/Core/Outcome.lean` §4

**183 insertions, 0 deletions** — the diff is the claim. Twelve theorems
and one `example`, no instance, no `simp`/`grind` attribute, and no change
to any existing declaration, so **every tier that has not adopted it
elaborates exactly as before**:

* `SemMWith.run_bind` — the opening, and the only hand-unfolding of the
  stack that now exists anywhere in the tree;
* `run_bind_ok` / `run_bind_loud` / `run_bind_raise` — stepping from a
  known head, stated on an `x w = …` hypothesis because **`simp` will not
  rewrite inside a match DISCRIMINANT** (`docs/backlog/go.md` §G11, a Lean
  fact both tiers hit independently);
* the primitive rows: `run_pure`, `run_get`, `run_set`, `run_modify`,
  `run_throw`, `run_raiseIn`, `run_exhausted`, `run_refuse`,
  `run_refuseWith`;
* the corollaries `run_map` and `run_seqRight`, which need no second
  opening — that being the point of having exactly one.

Attributes deliberately stay with the tiers: Go's rows are `@[go_run]`,
and a simp set is a lane's proof STRATEGY rather than a family fact.

### The estimate was wrong in the honest direction, and by how much

`2026-08-24-c-12` priced it at 5 theorems and ~40 lines. It is **12
theorems and 183 lines.** The gap is not the seam — that half was exact —
it is the PRIMITIVE ROWS, which the estimate counted as C's four
(`pure`/`get`/`throw`/`refuseUnsupported`) when the family's set is nine,
because `Core` §1 and §2 name primitives this tier has never used
(`exhausted`, `refuse`, `refuseWith`, `set`, `modify`).

> **A lift is priced from the LIFTING tier's use of the thing, and the
> thing belongs to the family: the estimate misses exactly the rows the
> estimating tier had no reason to write.**

Worth recording because the direction is predictable and the fix is
cheap — price a lift against the DEFINITION's surface, not against your
own call sites.

### Two Lean facts the lift produced, both by failing first

**A `match` over an instantiation is a DIFFERENT TERM from a `match` over
the general type.** The section's cross-spelling check was first written
as an `example` comparing `run_bind`'s match at `SemM W ρ` (i.e. `π = σ =
Unit`) with the general one. It does not typecheck: the two matchers are
distinct constants, elaborated at `Loud Unit Unit` and at `Loud π σ`.

> **State a cross-spelling claim on a MATCH-FREE lemma, or you are testing
> matcher elaboration rather than the fact you meant.** The check now goes
> through `run_bind_ok`, whose statement contains no match, and it passes.

**And `rw` closes more than it looks like it does.** `run_seqRight`'s
proof was written as `rw [run_bind]` followed by a `cases`; the `cases`
errored with *"no goals to be solved"*, because `rw`'s trailing `rfl` had
already discharged it. Harmless, and worth naming for the same reason the
first is: **a tactic that fails because the goal is GONE reads exactly
like a tactic that fails because the goal is hard.**

### The C tier adopted in this commit, and the note went with the code

`LeanModels/C/C23/Expr.lean`: **35 insertions, 63 deletions.** The five
seam theorems are deleted and the eight use sites now name Core's. One row
stays, and it is genuinely this tier's — `EvalM.run_refuseUnsupported`,
because `refuseUnsupported` CAPTURES the memory at the refusal site
(`fun m => … (some m)`) where Core's `refuseWith` takes the snapshot as an
argument. §3.4 put the capture in the primitive so no call site can forget
it; that makes the primitive C's, and so is its row.

The `§9.3 CONVERGENCE` paragraph that carried the duplication is **deleted
in the same commit**, and that is a rule rather than tidiness:

> **A paragraph whose job is to make a duplication VISIBLE is deleted by
> the commit that removes the duplication. Carrying it afterwards
> documents a state the tree is no longer in — which is the same defect as
> a stale comment, wearing the costume of diligence.**

### Go is NOT touched, and that is §9.2 rather than politeness

`LeanModels/Go/Obs.lean`'s eleven rows are now one-line instances of these
and the Go lane can retire them **by touch**, whenever it next has that
file open. Nothing asks it to today, and until it does the tree carries
two proofs of one fact **in the open** — Core's §4 says so in as many
words, and `2026-08-24-c-16` says it to the lane that owns the other
copy. That is the honest state; a silent one would be the defect.


---

## 2026-08-24-c-17 — RUNG B: the 208 are DISCHARGED, the 7 have a NAME, and the order parameter was never needed

Rung A proved a pure expression does not write. This spends it, and the
spending goes further than the plan expected — because purity does not
only retire the siblings' half of `J.1(16)`, it makes the whole ∀-order
question **disappear** wherever every argument is pure.

### The theorem, and why it is short

Once nothing writes, every argument is evaluated at ONE memory: the one
the call started in. So an argument's value is `valOf? ctx m e` — a
function of the memory, with no walk in it — and *"the value of argument
`i`"* is already order-free before any permutation is mentioned.

| theorem | what it says |
| --- | --- |
| `evalArgs_pure_pointwise` | a pure list's values ARE `valOf? ctx m` applied pointwise, and the memory comes back untouched |
| `evalArgs_pure_ofPointwise` | the converse at a given value list — the half that makes it EVERY order, not just the ones that succeed |
| **`evalArgs_orderIndependent`** | **any permutation of an all-pure list: both orders run, both agree, memory untouched** |
| `evalArgs_pair_swap` | the arity-2 instance, with the other order EXHIBITED rather than compared |

That last row matters because **four of the seven have arity two**, and
because comparing two runs is weaker than producing one.

### THE PLAN SAID `evalArgsAt`, AND THE PLAN WAS WRONG IN AN INSTRUCTIVE WAY

The dispatched shape was a position-tagged evaluator — `evalArgsAt` over
`List (Nat × Expr)` — so that two orders could be compared with each
argument's position carried along. It is not in the landing, and not
because it was hard: **it had nothing to carry.** Tagging exists to move
information across a reordering, and Rung A had already made the only
information in question order-free.

> **A parameter you were about to thread is a sign the property is not yet
> stated at the right level. When the order stops being observable, the
> machinery for observing it stops being needed — and building it anyway
> is how a model acquires a moving part that models nothing.**

The `List.Perm` statement that replaced it is shorter, quantifies over ALL
orders rather than over an encoding of them, and needed no new definition.

### THE RESIDUE — seven obligations, and it is seven rather than fourteen

`NonInterfering ctx x e` — running `x` leaves `e`'s value alone — is the
effect summary, written down as a predicate instead of a paragraph.
`evalArgs_pair_oneEffect` is what discharging it buys, and the theorem is
worth reading for which hypothesis carries which half: **`hp` is Rung A**
(the pure sibling does not write, so the call still starts from `m` when
it runs second) and **`hni` is the residue** (the call does not disturb
what the sibling reads, so the sibling still answers the same value when
it runs second). Neither implies the other.

**Stated OBSERVATIONALLY, over `valOf?`, and that is a decision.** A
footprint reading — *"the callee writes no location the sibling reads"* —
would be strictly stronger than the obligation needs: a callee that writes
a location and writes it back is non-interfering in the sense the standard
asks about and interfering in the footprint sense. The ruling quantifies
over the OBSERVABLE, so the obligation does too.

> **An obligation should be no stronger than the thing it discharges. A
> footprint is easier to compute and harder to satisfy, and choosing it
> silently turns "we could not prove it" into "the program is wrong."**

And `nonInterfering_of_isPure` is why the count is seven: a pure argument
is non-interfering with everything, so **only the nested call is ever in
question** at a site. Fourteen pairwise obligations collapse to one per
site, for free, out of Rung A.

### What is NOT claimed

Discharging `NonInterfering` at the seven needs a read-set or a frame
lemma, and this tier has neither. That is the next rung and it is priced
in constructs rather than effort: **one read-set over the expression
language, or one frame lemma over `Mem`, and the seven fall out of the
theorem that is already proved.**

**And the observable is the ANSWER, never the run.** Every theorem takes
the canonical run's success as a hypothesis — in the statement, not in
prose. Two orders can disagree about *which refusal is reported* when more
than one argument would refuse, and §3.1 never pools the causes, so a
∀-order theorem quantified over the run would be false for a reason that
has nothing to do with sequencing.

### The gate that makes the hypothesis load-bearing

A hypothesis nothing would violate is not a hypothesis, so
`Examples/c/sunfish/expr.lean` runs the excluded case on `pyfloordiv`'s own
frame. With `r = 7`:

| order | answer | memory |
| --- | --- | --- |
| `[r, r++]` | `[7, 7]` | `r = 8` |
| `[r++, r]` | `[7, 8]` | `r = 8` |

The final memories agree; the VALUES do not. That is exactly the
observable §6.5.3.3p10 leaves indeterminate, it is the corpus's own
construct (63 increment sites), and it is what Rung A's purity excludes.
Eleven `#guard`s in all, including `valOf?` on the corpus's `&&`.

### Four errors, and the interesting one is about `cases`

The proof went green in four fast-loop iterations (~10 s each — A17, open
since `qol-53`). Three were mechanical: two `simp made no progress` from a
redundant second `simp only` after the first had already applied
`Except.ok.injEq` twice, and two `rfl`s where the goal wanted `True`
because `simp only` without `and_true` leaves the tail of a `List.cons`
injection as `True`.

The fourth is worth keeping. `evalArgs_cons_inv` closes with an anonymous
constructor, and the first component would not typecheck: `he` had type
`evalExpr ctx e m = .ok (.ok v, m₀)` where the goal wanted
`.ok (.ok v, m₀) = .ok (.ok v, m₀)`. The cause is that **`cases he : x`
GENERALIZES `x` in the goal** — the goal's own `evalExpr ctx e m` had been
abstracted and instantiated to the constructor, so the slot wanted `rfl`
and not the hypothesis that says the same thing.

> **`cases h : e` rewrites the GOAL as well as introducing `h`, so inside
> the branch the hypothesis and the goal are no longer talking about the
> same syntax. A slot that wants `rfl` where you expected to pass `h` is
> that, and not a mis-stated lemma.**

### VERDICT — GREEN

`tools/triad.sh --lane crunga --classify`, ticket
`1787557614438165000-50586-crunga`:

```
[09:46:54] base: base 40c093c is AT the origin/master tip
[10:45:42] LOCK ACQUIRED after 3494s as 'crunga 50586'
[10:46:10] TRIAD DONE (build exit 0, gates green)
[10:46:11] LOCK RELEASED (mine)
```

Tree at enqueue `86ff6365ed9f`; classified **tier**; 29 seconds of tenure
behind 58 minutes of queue at depth 6.

| gate | result |
| --- | --- |
| `lake build` build phase / gate phase | **exit 0, 18 jobs / 38 jobs** |
| `tools/docs_check.py` | **91 / 91**, 39 illustrative-exempt |
| `harness/diff_test.py` | **1500 cases, 0 failed** — 1374 matched, 126 whitelisted |
| `harness/refusal_census.py --whitelist --no-build` | green |
| `harness/c_profile_probe.py --check-lean` | **9 / 9** |
| `tools/backlog-index.sh --check` | in sync |
| `error:` / `sorry` lines in the full log | **0** |

**ELABORATION WITNESS.** `Built LeanModels.C.C23.Expr (8.0 s)` and — the
line that carries the eleven new `#guard`s — **`Built
Examples.c.sunfish.expr (1.6 s)`**. `LeanModels.Core.Outcome` is
**Replayed**, which is the check that this landing is tier-local: the seam
lift is in and this rung did not touch it.

### Axiom ledger

All four Rung B theorems on `[propext, Classical.choice, Quot.sound]` —
no `sorryAx`, no `native_decide` — and Rung A's three and the three
drain-amendment theorems unchanged beside them:

```
evalArgs_pure_pointwise     [propext, Classical.choice, Quot.sound]
evalArgs_orderIndependent   [propext, Classical.choice, Quot.sound]
evalArgs_pair_swap          [propext, Classical.choice, Quot.sound]
evalArgs_pair_oneEffect     [propext, Classical.choice, Quot.sound]
```

### COVERAGE (§5.4a) — scoped, and the importer census re-run

`grep '^import LeanModels\.C\(\.\|$\)'` still returns 16 lines, all
inside `LeanModels/C/` or `Examples/c/`, and every one of them is in the
build. `--build-target` was NOT passed this time: it is a no-op
(`2026-08-24-c-14`, filed to QoL), and passing a flag that does nothing in
order to write a coverage sentence it does not support is the defect that
entry names. The classifier's floor covers the tier here because
`Examples.c.sunfish.expr` is in it and `stmt` imports it — and `stmt`
elaborated exit 0 under A17 against the fresh oleans after the green, the
same way `2026-08-24-c-12` closed the same gap.

### §9.0 — the tier's standing number

**`gcc.c-torture` 0 scored (runner needed).** Unchanged, and now the ONLY
thing between this tier and a number: rungs A and B moved proof
obligations, and inch 6's `lean_exe` batch runner is what creates the
denominator — corpus fetched AT PIN by content hash, never vendored
(`docs/c23-goal.md` §2, GPL).

---

## 2026-08-24-c-18 — INCH 6: the scoreboard is BUILT, and §9.0 stops being a promissory note

Every landing in this lane so far moved a proof obligation. This one
moves the standing number, because it builds the thing that creates the
denominator: **`docs/c23-goal.md` §4.2 said "specced, not built" since
M1, and it is now built.**

### Three programs, not one, and the split is the spec's own

§4.2 specced `harness/c_refusal_census.py` — one Python instrument. What
landed is three, because the spec had three jobs in it and they belong to
different machines:

| job | landed as |
| --- | --- |
| fetch at a pin, verify by content, never vendor | `tools/c_corpus_fetch.py` |
| run each test under fuel, ONE process for the batch | **`lake exe c-torture-run`** (`LeanModels/C/Torture.lean`) |
| score, and enforce the reporting rules | `harness/c_torture_score.py` |
| the three as one command | `tools/c_torture_gate.sh` |

The runner had to be the Lean one. A Python driver would have to shell
out per test, which is `docs/backlog.md`'s three-times-recorded lesson
inverted — 615 rows went from hours to ~11 s when a batch got one process.

### THE CORPUS IS NEVER IN THIS REPOSITORY, and the guard is EXECUTED

`gcc.c-torture` is GPL-3.0-or-later. `docs/c23-goal.md` §2's ruling is
*fetch at test time, pin by revision, vendor nothing*, and this is that
ruling as code: the cache root is **refused if it resolves inside the
tree**, checked on the RESOLVED path so a symlink or a `..` cannot walk
back in. `--selftest` runs the refusal three ways, including through
`docs/../harness`.

> **A licence rule that lives in a paragraph is a rule the next lane has
> to remember. Put it in the code that would break it, and check the
> RESOLVED path — a textual comparison is defeated by exactly the input
> that matters.**

**THE PIN IS TWO HASHES, and they answer different questions.**

| | what it answers |
| --- | --- |
| git blob sha1 | what GitHub says the file is AT THE REVISION — recomputed locally as `sha1("blob <len>\0" + bytes)`, so the check does not trust the transport |
| sha256 | what the bytes ARE, recorded by us — a refetch matching it needs no network to be believed |

> **A pin by revision is a claim about a server's history; a pin by
> content is a claim about the bytes. Only the second survives the
> server.**

`docs/c-torture-pin.json` is 300 rows of name + two hashes + frontend
status, 60 KB, and **contains no source** — a fingerprint is not the
corpus. It is also what makes `--offline` real: the whole verification
re-runs with no network and reproduces the same counts.

### The fetch, measured — and a sample rule that was not one

**300 files at pin `9e54d865`, 270 parsed, 30 rejected by the frontend.**

The census recorded **246** parsed of 300 (`docs/c23-suite-census.json`,
`gcc-torture-exec`). Both say "the first 300 by name" and they disagree
by 24, because *"first 300 by name"* is not a sample rule until it says
**first 300 of what**: this fetch takes the 995 `.c` files in the
`execute/` directory itself, and `execute/` has subdirectories
(`builtins/`, `ieee/`, `pr…`) that bring the corpus to the 1918 the goal
doc's table quotes. Two different populations, one phrase.

> **A sample rule has to name its POPULATION, not only its ordering.
> "First N by name" is reproducible and still ambiguous, which is the
> worst combination: it looks like a specification and two honest
> instruments disagree under it.**

The pin file settles it for this lane the only way that survives:
**by listing the 300, with hashes.** A prose rule can be re-read
differently; 300 sha256 lines cannot.

### The reporting rules, both EXECUTED rather than described

**The first failure is printed VERBATIM, in log order.** `--selftest`
runs the trap: two failures with identical text, the later one
alphabetically first. A sorted summary reports the wrong one; a
deduplicated summary collapses them to one and reports whichever
survived.

> **`sort -u` over failures answers "which distinct failures exist"; a
> reader after a red run asks "what went wrong first". The two coincide
> only by luck, and a summary that silently answers the other question is
> worse than no summary, because it looks like an answer.**

**The zeroes are not the same zero.** `not-fetched`, `not-parsed`,
`refused-unsupported`, `refused-libc`, `refused-ub` and `timeout` are six
numbers, never one, because they are facts about six different
subsystems — the fetch, the frontend, three different frontiers of the
model, and the fuel bound.

> **Pooling the absences makes a scoreboard unfalsifiable: it can no
> longer tell "the model declined" from "nobody ran it", which is the
> only distinction that says whether the next rung would move the
> number.**

The gate degrades along exactly that seam: on a machine with no corpus
cache the offline pass marks all 300 `absent`, the driver reports
`not-fetched 300`, and the number is `0/300` — a **different** zero from
"the model refused 300", and the summary says which.

### `scored = passed + failed`, and `failed` is a SCORE

`docs/c23-goal.md` §1.2: torture's verdict style is *exit status —
`abort()` on failure, fall off `main` on success*. So reaching `abort` is
a RESULT, not a refusal to produce one: the program ran and its own check
failed. The driver catches `abort` **by name** before the libc slice can
turn it into an environment refusal, because pooling it with `refused`
would hide the only failures this scoreboard can currently see.

### Two instruments, one answer — one level up

The Lean driver prints its own summary; `harness/c_torture_score.py`
recomputes it from the per-test lines, in a different language. Agreement
is evidence; a disagreement would be a defect in one of the two. Both
carry `--selftest`, and the scorer's refuses an unknown verdict token
rather than bucketing it.

### THE FIRST RUN CONVICTED THIS LANDING OF ITS OWN LAW

Tenure 1 came back green with `gcc.c-torture 24/300 scored`, and a line
under it that did not add up: **`not-parsed 233`**, against a manifest
that says **30**. The manifest was right. The 203 were envelopes clang
had ACCEPTED and the `c-0.1` ingester had refused — and this driver was
labelling both `not-parsed`.

That is the pooling defect **this very entry names**, committed in the
landing that names it. Two subsystems, one token:

* `not-parsed` — **clang** rejected the source under the pinned profile;
* `not-ingested` — clang accepted it, and the **extractor's output** was
  refused by the ingester.

> **The zero-state split is only as good as its finest real seam, and you
> do not know where that seam is until the instrument runs. A state
> partition written before the first run is a hypothesis; the first run
> is what tests it.**

Split in this landing, along with `runner-error` — which §4.2's own spec
had asked for (*"an unexecutable test emits a `runner-error` row rather
than no row, so the count stays honest"*) and which the first draft had
folded into `not-parsed` too.

### AND THE INSTRUMENT PAID FOR ITSELF ON ITS FIRST RUN

Of the 203, **195 are one defect**:

```
not a c-0.1 envelope: envelope: FunctionDecl: ParmVarDecl: span:
  field 'col': Natural number expected
```

`extractors/c/extract.py:146` writes `"col": b.get("col")`, and **clang
omits `col`** for locations it gives only as a line — an unnamed
parameter in a prototype is the common case. The extractor passes `null`
through; the schema says `Nat`; the ingester refuses, correctly. Three
more are `ParmVarDecl: field 'name': String expected` — C permits a
prototype parameter with no name and the schema does not — and one is
`EnumConstantDecl: field 'value'`.

**So 199 of the 300 are gated on one schema decision**: is a span's
`col` optional, and what does a model with no column do? That is the next
inch, and it is priced in a decision plus one extractor change rather
than in effort.

> **A scoreboard's first job is not to be high. It is to say WHICH ONE
> THING to fix next — and a number that could not do that would not be
> worth the tenure that produced it.**

### VERDICT — GREEN, and §9.0 MOVES

`tools/triad.sh --lane crunga --classify`, ticket
`1787563655997873000-64812-crunga`:

```
[11:27:36] base: base 7129f2b is AT the origin/master tip
[11:27:36] LOCK ACQUIRED after 0s as 'crunga 64812'
[12:03:34] TRIAD DONE (build exit 0, gates green)
[12:03:35] LOCK RELEASED (mine)
```

Classified **spine** (`lakefile.toml` gains a `lean_exe`), tree at enqueue
`db7ccb175d1f`, **36-minute full build, 3780 jobs, 0 `error:` lines**.
COVERAGE (§5.4a): **full — a green covers every default target at this
sha**, which is what a spine class buys and the only landing in this lane
entitled to say it without an importer census.

| gate | result |
| --- | --- |
| `lake build` (all default targets) | **exit 0, 3780 jobs** |
| `tools/docs_check.py` | **91 / 91** |
| `harness/diff_test.py` | **1504 cases, 0 failed** — 1378 matched, 126 whitelisted |
| `harness/refusal_census.py --whitelist --no-build` | green |
| `harness/c_profile_probe.py --check-lean` | **9 / 9** |
| `tools/c_corpus_fetch.py --selftest` | **ok** — the never-vendor guard refused three inside-repo paths |
| `harness/c_torture_score.py --selftest` | **ok** — the sort-`u` trap and all eight zero-states |
| `tools/c_corpus_fetch.py --offline` | **300 at pin `9e54d865`**, every sha256 re-verified, no network |

### THE NUMBER

```
gcc.c-torture 24/300 scored  (passed 24, failed 0)
  the zeroes, kept apart: refused-unsupported 39, refused-libc 1,
    refused-ub 3, timeout 0, not-ingested 203, not-parsed 30,
    runner-error 0, not-fetched 0
```

`24 + 39 + 1 + 3 + 0 + 203 + 30 + 0 + 0 = 300`. **Nothing is unaccounted
for, which is the property the state split exists to give.**

**§9.0 goes from `gcc.c-torture 0 scored (runner needed)` to
`gcc.c-torture 24/300 scored`.** It is the first number this tier has
ever had, and the first landing here that moved one rather than a proof
obligation.

**Read it honestly.** 24 is small, `failed` is 0, and the two facts
together say the tier does not yet get torture tests WRONG — it declines
them. The queue of reasons is now ordered and each has an owner:

| next | what it unblocks |
| ---: | --- |
| **199** | one schema decision — is a span's `col` optional? — plus one `extract.py` change |
| **39** | the `unsupported` frontier: rungs, one construct at a time |
| **30** | nothing this lane owns: clang rejects them under the pinned profile (K&R definitions, `asm`, VLAs in structs) |
| **3** | UB refusals, which never retire — they are the product |


---

## 2026-08-24-c-19 — SPAN `col` BECOMES OPTIONAL, and the prediction is recorded BEFORE the run

`2026-08-24-c-18`'s scoreboard reported **199 of 300** `gcc.c-torture`
tests refused at the ingester with `span: field 'col': Natural number
expected`. The ruling, with the absence family: **`col` becomes optional
with stated semantics, never a fabricated value.**

### The three clauses, and what each cost here

**(1) The extractor emits the field only when clang provides it.**
`extractors/c/extract.py:146` wrote `"col": b.get("col")` unconditionally,
so a location clang knew only to a line became `null`. It now emits the
key only when there is one — **the same shape the `macro` field already
used**, which is the "consistency over preference" half of the ruling: the
schema now has ONE spelling for absence rather than two.

**(2) The model's span carries the absence honestly.** `CSpan.col` and
`CSpan.endCol` are `Option Nat`. `LeanModels/C/Json.lean` reads them with
`getOptNat` — the same reader the macro fields use — so an explicit
`null` and a missing key are the same absence on the way in.

> **An absent column is `none`, never `0`. A fabricated column is
> silently wrong data that reads exactly like a measured one, and
> column 0 must stay distinguishable from column-unknown.**

**(3) Anything that READS `col` must decide the absence case.** Measured,
and it is the cheap half: **nothing in this tier reads `col` today.**
`grep '\.col\|\.endCol'` over `LeanModels/C/` and `Examples/c/` returns
only the field declaration and the parser that constructs it — the
refusal messages name `Expr.kindName`, never a column. So there is no
absence case to decide yet, no message to reformat, and this landing is
**pure schema-widening**: two `Option`s, one parser line, one extractor
clause, and two `noSpan` literals in the fixtures.

The `Option` is therefore not paying for a call site — it is there so the
FIRST reader has to decide the absence case in the open instead of
reaching for a default. Recorded because a reviewer who finds no consumer
should be able to tell a deliberate widening from an unfinished one.

### THE PREDICTION, written before the tenure

The calibration discipline: predict, then measure, and record both
whichever way it goes.

**Predicted: `gcc.c-torture` 74/300 scored** — up from 24 — with a band of
**55–100**, and `refused-unsupported` growing from 39 to roughly 180.

The reasoning, so the miss is informative:

* 199 tests become ingestible, taking the ingested population from **67**
  to **266**; `not-ingested` should fall from 203 to **4** (3 unnamed
  `ParmVarDecl` names, 1 `EnumConstantDecl` value — the same absence
  family, not covered by this ruling) and `not-parsed` stays **30**.
* Of the 67 already ingested, 24 score — **35.8 %**. Applying that rate
  flat gives ~96.
* But the currently-ingested 67 are **selected**: they are the files with
  no unnamed prototype parameter, which correlates with declaring fewer
  functions, which correlates with being smaller. The 199 should score
  LOWER than the 67 did, so the flat rate is an over-estimate. I take
  ~25 %, hence 74.

**An exact hit would be same-instrument transcription and worth little; a
miss is information about the frontier's shape** — high means the tier's
vocabulary reaches further into the corpus than its own gate suggests,
low means the `unsupported` frontier is the real wall and the 39 was a
sample of a much larger population.

### VERDICT — GREEN, and the PREDICTION MISSED for a reason worth more than a hit

`tools/triad.sh --lane crunga --classify`, ticket
`1787566273501235000-3965-crunga`:

```
[12:11:13] LOCK ACQUIRED after 0s as 'crunga 3965'
[12:13:06] TRIAD DONE (build exit 0, gates green)
```

Spine class, tree `2f41877e0469`, **3780 jobs, exit 0, 0 `error:` lines**,
COVERAGE **full**. docs_check 91/91; diff_test **1504 cases, 0 failed**;
c_profile_probe 9/9; both instrument `--selftest`s ok; `--offline`
re-verified all 300 sha256 with no network.

**PREDICTED 74/300 (band 55–100). ACTUAL:**

```
gcc.c-torture 24/300 scored  (passed 24, failed 0)
  the zeroes, kept apart: refused-unsupported 43, refused-libc 1,
    refused-ub 3, timeout 0, not-ingested 199, not-parsed 30,
    runner-error 0, not-fetched 0
```

**24. The prediction missed by 50, outside its own band, and the reason is
not the one the band was drawn for.**

`not-ingested` went 203 → **199**, not 203 → 4. The `col` widening worked
exactly as specified — **every `field 'col'` error is gone** — and what it
uncovered is that the 195 had a SECOND blocker underneath the first:

```
198  envelope: FunctionDecl: ParmVarDecl: field 'name': String expected
  1  envelope: EnumDecl: EnumConstantDecl: field 'value': String expected
```

An unnamed parameter in a prototype (`int f(int);`) has **both** `col:
null` and `name: null`. The parser reads `span` before `name`, so `col`
was the error every one of them reported — and a scoreboard can only ever
report the blocker it reaches first.

> **A scoreboard reports the FIRST blocker, never the only one. "199 are
> gated on X" means "199 reach X first" — how many were gated on X *and
> something else* is a fact only the run AFTER the fix can produce.**

That is what the calibration discipline bought here. The band 55–100 was
drawn around a guess at the tier's FRONTIER — how much of the corpus the
vocabulary reaches — and the miss says nothing about the frontier at all,
because the tests never got far enough to meet it. **An estimate can be
wrong about a quantity it was not measuring**, and only a recorded
prediction makes that visible instead of retrofitting the reasoning to
whatever came out.

**The four that did move** are real and are the whole of the honest
result: `InitListExpr: Unsupported: span: col` ×3 and `VarDecl:
InitListExpr` ×1 — the col cases that had no second blocker. And
`refused-unsupported` rose 39 → **43**, which is those four arriving at
the frontier. The chain is intact end to end; it is just four tests long.

### The next layer, and the revised prediction

`ParmVarDecl.name` is the same absence family and the same ruling shape —
C permits a prototype parameter with no name (§6.7.6.3), so `Decl.param`'s
`name` wants `Option String`. It is **not** pure schema-widening this
time, and that is the difference worth flagging before it is attempted:
`bindParams` READS the name, so §6.9.2p7's *"the parameters are declared
as if by declaration in the compound statement"* has to be decided for a
parameter that cannot be referred to — it still gets an object, and
nothing can name it.

**Predicted after that layer: 60/300 scored, band 40–110.** The band is
wider than last time, deliberately: this is the first prediction that will
actually be about the frontier, and the tier has never measured its
frontier against 266 tests. `refused-unsupported` predicted ~200.


---

## 2026-08-24-c-20 — AN UNNAMED PARAMETER: allocate, initialize, bind nothing

`2026-08-24-c-19` uncovered the second blocker under the first: **198 of
300** `gcc.c-torture` tests refused at the ingester with `ParmVarDecl:
field 'name': String expected`. C permits it — §6.7.6.3 lets a prototype
declare a parameter with no identifier (`int f(int);`) — so the schema was
wrong and the corpus was right.

**This one is not schema-widening**, and that is the whole of its
interest. `col` had no reader; `name` has one, and it is the semantics.

### The ruling, and where each clause lives in the code

> **§6.9.2p7 holds for an unnamed parameter too: the argument is
> evaluated, the parameter object exists and is initialized with the
> converted value, and no identifier denotes it — which in this model is
> exactly one thing: no environment entry.**

**(1) Argument evaluation is untouched, and structurally so.** Arguments
are evaluated by `C23.evalArgs`, in `Expr.lean`, *before* `bindParams` is
reached — the caller cannot see parameter names and nothing here is in a
position to make it. Same order, same effects, same memory growth. This
is not a promise about the diff; it is a fact about which function the
diff is in.

**(2) The allocation is NOT elided, and eliding it is not expressible.**
The `alloc` and the `storeAt` sit **outside** the match on the name; only
the environment update is inside it:

```lean
let (m', o) := m.alloc .automatic sz (some ty)
set m'
liftEval (storeAt (Ptr.toObject o) ty v)
let env' := match n with
            | some nm => (nm, o) :: ctx.env
            | none => ctx.env
```

Nothing can take the object's address, because nothing names it — so an
optimizer's instinct is to skip the allocation. **That instinct is a
LEMMA about `Mem`, not a shortcut**: this model's memory has a shape, and
whether an unreachable allocation is unobservable in it is a claim that
would have to be proved. It is not claimed here, so it is not taken, and
the code is arranged so that taking it would require moving lines rather
than deleting a branch.

> **"Nothing can observe it" is a theorem about your model, not a licence.
> Write the code so the shortcut costs an edit, and the next reader has to
> notice they are taking it.**

**(3) The absence is decided in exactly ONE place.** `bindParams` is the
only consumer of the `Option`. Nothing downstream ever sees a name for an
unnamed parameter, and in particular there is **no synthetic** — no
`_unnamed_3`, which would be a fabricated name one field over from the
fabricated column `2026-08-24-c-19` refused. A synthetic reads exactly
like a real name and something would eventually look it up.

`Examples/c/sunfish/guards.lean`'s structural gate compares against
`some "a"` rather than around it, so the gate sees the absence too.

### The prediction, restated beside its result

**Predicted (recorded in `2026-08-24-c-19`, before either run):
60/300 scored, band 40–110, `refused-unsupported` ~200.**

This is the first prediction that is actually about the FRONTIER —
`c-19`'s missed because the tests never reached it. 266 tests should now
ingest (`not-ingested` → 1, the lone `EnumConstantDecl: value`;
`not-parsed` stays 30), and what happens to them is a measurement of how
far this tier's vocabulary reaches into a corpus it was never designed
against.

### VERDICT — GREEN, and the INGESTION WALL IS GONE

Ticket `1787566806249940000-27008-crunga`:

```
[12:20:06] base: base aebf1fd is AT the origin/master tip
[12:46:11] LOCK ACQUIRED after 1555s as 'crunga 27008'
[13:18:02] TRIAD DONE (build exit 0, gates green)
```

Spine class, tree `fe634682147f`, **3781 jobs, exit 0, 0 `error:` lines**,
COVERAGE full. docs_check 91/91; diff_test **1504 cases, 0 failed**;
c_profile_probe 9/9; both `--selftest`s ok; `--offline` re-verified all
300 sha256 with no network.

```
gcc.c-torture 28/300 scored  (passed 28, failed 0)
  the zeroes, kept apart: refused-unsupported 197, refused-libc 38,
    refused-ub 4, timeout 0, not-ingested 3, not-parsed 30,
    runner-error 0, not-fetched 0
```

**§9.0: 24 → 28/300 scored.** `not-ingested` 199 → **3** (all three the
lone remaining absence-family case, `EnumConstantDecl: field 'value'`).
**267 of 300 now reach the interpreter**, against 67 two landings ago.

### PREDICTED 60/300, band 40–110. ACTUAL 28. MISSED AGAIN, and LOWER than the floor.

And this time the miss is about the frontier, exactly as `c-19` said it
would be — but not in the way the number suggests. **The interesting part
is which half of the prediction was right:**

| predicted | actual |
| --- | --- |
| `not-ingested` → ~1 | **3** — near enough |
| `refused-unsupported` → **~200** | **197** — near enough |
| **scored → 60** | **28** — off by 32 |

I predicted the largest bucket almost exactly and still missed the score
by more than the score. The gap is a bucket I did not predict at all:
**`refused-libc` went 1 → 38**, and 36 of those are `exit`.

> **Predicting a BUCKET is not predicting the RESIDUAL. A residual is a
> difference, so it inherits the error of every bucket you did NOT
> predict — and the one I did not predict was the one that had never had
> a chance to be observed.**

`refused-libc` stood at 1 because only 67 tests had ever reached the
interpreter; the libc wall was standing behind the ingestion wall, and a
frontier measured from behind another frontier is **a lower bound on
itself**. That is the third instance of one shape today — `col` hid
`name`, ingestion hid libc, and `2026-08-24-c-19` named the general form
before this run confirmed it.

> **Each wall you remove is the first honest measurement of the next one.
> A queue of blockers cannot be priced from behind the first of them, and
> a plan that prices it anyway is measuring its own ignorance.**

### The walls, all visible at once for the first time

| n | wall | owner |
| ---: | --- | --- |
| **197** | `unsupported` — 79 `no layout for declared type`, 64 `unbound name`, 8 arity, 7 `not an lvalue: StringLiteral`, 7 non-object block declarations, … | the tier's vocabulary: **rungs, one construct at a time** |
| **38** | `libc` — **36 `exit`**, 1 `memset`, 1 `__builtin_alloca` | widening the modelled slice |
| **30** | clang rejects under the pinned profile | nothing this lane owns |
| **4** | UB refusals | never retires — it is the product |
| **3** | `EnumConstantDecl: value` | the last absence-family case |

**36 `exit` is the single cheapest number on the board** and it is not a
rung: `exit(0)`/`exit(1)` in a torture test is the *oracle itself*
speaking — the same exit-status convention `abort` already has a verdict
for. Modelling `exit` is a scoreboard decision, not a semantics one, and
it is the obvious next move for anyone reading this table.

`no layout for declared type` at 79 is the largest and is one thing: the
runner hands `torLayout`, which knows the scalar spellings and nothing
about arrays or structs. That is a runner improvement, not a tier rung.


---

## 2026-08-24-c-21 — THE SCOREBOARD INCH: read the oracle, size what is exact, and refuse to invent a struct

Three items, none of them semantics, taken together because separately
each would leave the frontier lying. `2026-08-24-c-20`'s table said the
two largest reasons in a 197-item "unsupported frontier" belonged to the
INSTRUMENT rather than the tier — a frontier that counts instrument
limits as language limits is not a frontier.

### (1) `exit(n)` IS the verdict channel — and the guard is syntactic

Ruled: `exit` gets the by-name treatment `abort` already has, **reading
the oracle rather than modelling libc**. But `abort` needs no argument and
`exit` does: `exit(0)` is success, `exit(1)` is failure, and the refusal
carries only the NAME — so scoring `exit` by name alone would fabricate a
verdict exactly where §3.1 forbids pooling.

So the driver checks the ARGUMENT syntactically, in the envelope, before
it will read an `exit` refusal as a pass: **every `exit` call in the
translation unit must have exactly one argument that peels (through casts
and parens) to the literal `0`.** A program containing any other `exit`
is not scored — it stays a named refusal, because we could not tell which
`exit` was reached.

**Measured before it was built**: of the 36 tests refusing on `exit`, all
36 contain `exit(0)` and nothing else. The guard is therefore free today
and is still there, because it is what makes the reading honest rather
than lucky.

> **Reading an oracle is not modelling a library. The test is whether the
> code could answer differently for a program the oracle does not
> describe — and if it could, the guard belongs in the scoreboard, not in
> a comment.**

### (2) The runner's layout: size what is EXACT, name what is not

`torLayout` knew the scalar spellings and nothing else, so **79 tests
were refused for `no layout for declared type`** — an instrument limit
counted as a tier limit. Censused before building:

| n | kind | what it needs |
| ---: | --- | --- |
| **28** | arrays (`char[N]`, `int[N]`, …) | nothing — §6.2.5p20 makes an array's size EXACTLY `n × elem`, with no padding to guess |
| **32** | `struct`/`union` | an ALIGNMENT RULE, which the profile does not pin |
| **21** | other — `double`, typedef names (`trio`), `volatile a_struct` | qualifier stripping and typedef resolution are lookups; `double` is the floats decision |

Arrays, typedef resolution and qualifier stripping are **exact** and land.
Structs **do not**, and that is the point of the item rather than a
shortfall in it: laying out a structure needs an alignment rule, C leaves
padding implementation-defined (§6.7.2.1p18), and the natural-alignment
rule everyone would reach for is an ABI convention this project has not
pinned.

> **A layout the instrument computes from a rule nobody declared is a
> FABRICATED LAYOUT — the same defect as a fabricated column, one
> abstraction up. Structs stay a NAMED zero until the profile pins the
> rule.**

### (3) `EnumConstantDecl.value` — the last absence case

3 tests, same family, same rules: optional with stated semantics, no
fabrication. And measured like `col` was: **nothing in the tier reads it**
— `Ctx.enums` is only ever supplied from `Program.enums`, which nothing
builds from an envelope — so this is schema-widening again.

### THE PREDICTION, and its band is built out of the day's own two laws

`2026-08-24-c-20` established that a bucket can be predicted well and a
residual still missed, and that each wall is a lower bound on the next.
So this prediction is **per bucket**, and its band is split at the line
those laws draw:

| bucket | predicted |
| --- | ---: |
| `not-ingested` | **0** (from 3) |
| `refused-libc` | **2** (from 38 — `memset`, `__builtin_alloca`) |
| `refused-unsupported` | **~175** (from 197) |
| `refused-ub` | ~5 |
| `not-parsed` | 30 — unchanged, not this lane's |
| **scored** | **72 / 300** (from 28), band **64 – 105** |

**The floor and the width mean different things, and that is the whole
design of the band.**

*The floor, 64, is the part that CANNOT hide a wall.* A test refusing on
`exit` has already reached `exit(0)` — in these programs the last
statement of `main` — so it ran to completion and there is nothing behind
its refusal. 28 + 36 = 64 is arithmetic, not estimation.

*Everything above the floor is exposure to a wall that is unknown by
construction.* The layout fixes free a test at a DECLARATION, early in the
run, so every statement after it is unmeasured — and the tier has never
observed those statements. 41 of the band's 41-point width is that
ignorance, stated as width instead of hidden in a point estimate.

### TENURE 1 — RED, and the lesson is one I had already been taught today

`[13:28:15] LOCK ACQUIRED after 0s as 'crunga 87819'` →
`[13:30:10] TRIAD DONE (build exit 0, gates RED)`. **An aborted triad**,
and the diagnosis is not interesting: three errors in
`LeanModels/C/Torture.lean`, two of them one cause (`String.drop` returns
a `String.Slice` at this toolchain, not a `String`) and one a docstring
left stacked on another by a scripted edit.

**What is interesting is that A17 would have caught all three in ten
seconds and I did not run it.** I verified `LeanModels/C/Ast.lean` after
editing it and did not verify `Torture.lean` after REWRITING it — the
larger of the two changes went unchecked because the smaller one had just
passed.

> **The fast loop is only worth what you point it at. A cheap check that
> is run on the file you were LEAST worried about is a cheap check you did
> not run.**

The whole argument for `qol-53` was that a defect should cost ten seconds
instead of a tenure. This one cost a tenure because the instrument was
available and unused, which is a worse failure than not having it —
`2026-08-24-c-13`'s inbound bought a capability, and a capability is not a
practice.

Fixed and **verified in the fast loop before re-ticketing**: exit 0, zero
warnings, including the `String.dropRight` deprecation the first pass had
also introduced.

**If a fourth hidden wall appears, the register gets its confirmation and
the shape is a law. If it does not, this is the first prediction to
survive contact with a newly-exposed frontier, and the reason will be
that the exposure was priced into the band instead of into the guess.**

### VERDICT — GREEN, and the PREDICTION LANDED

Ticket `1787571147529854000-8803-crunga`:

```
[13:32:27] base: base 720ff3c is AT the origin/master tip
[13:32:27] LOCK ACQUIRED after 0s as 'crunga 8803'
[13:34:02] TRIAD DONE (build exit 0, gates green)
```

Spine, tree `0f1d03c02b78`, **3781 jobs, exit 0, 0 `error:` lines**,
COVERAGE full. docs_check 91/91; diff_test **1504 cases, 0 failed**;
c_profile_probe 9/9; both `--selftest`s ok; `--offline` re-verified all
300 sha256 with no network.

```
gcc.c-torture 67/300 scored  (passed 67, failed 0)
  the zeroes, kept apart: refused-unsupported 191, refused-libc 4,
    refused-ub 5, timeout 2, not-ingested 1, not-parsed 30,
    runner-error 0, not-fetched 0
```

**§9.0: 28 → 67/300 scored.** `67 + 191 + 4 + 5 + 2 + 1 + 30 = 300`.

### PREDICTED vs ACTUAL, per bucket

| bucket | predicted | actual | |
| --- | ---: | ---: | --- |
| `scored` | **72** (band 64–105) | **67** | **inside the band, 5 under the point** |
| `refused-ub` | ~5 | 5 | exact |
| `refused-libc` | 2 | 4 | close |
| `not-ingested` | 0 | 1 | close |
| `refused-unsupported` | ~175 | 191 | over-predicted the drop by 16 |
| `timeout` | *(not predicted)* | **2** | a bucket that had never been non-zero |

**This is the first prediction in this lane to survive contact with a
newly-exposed frontier**, and the reason is exactly the structure the band
was given rather than luck about the number:

* the **floor** was arithmetic — 28 already-scoring + 36 `exit`
  conversions that cannot hide a wall, because a test refusing on
  `exit(0)` had already run to completion. It held: 67 ≥ 64.
* the **width** was ignorance, and the ignorance was real. 67 sits **3
  above the floor**, which says that of the ~31 tests freed by the layout
  work, **almost all immediately hit another wall** — `refused-unsupported`
  fell only 197 → 191 while absorbing them. The fourth hidden wall
  appeared exactly as the shape predicted; it was priced into the band
  instead of into the guess, and so the prediction held anyway.

> **A band whose floor is arithmetic and whose width is a named ignorance
> can be RIGHT about a frontier it cannot see. A point estimate over the
> same evidence would have been wrong by 30 and called the shape wrong
> too.**

And `timeout` going 0 → 2 is the fifth wall arriving, small and on
schedule: two tests now run far enough to exhaust fuel 64. **A bucket
that has never been non-zero is not a measured zero** — it is a bucket
nothing has reached yet, which is the whole doctrine of this scoreboard
seen once more from the inside.

### The frontier now — and it is the tier's own for the first time

| n | wall | owner |
| ---: | --- | --- |
| **191** | `unsupported` — **69 unbound name**, 54 `no layout` (all struct/union now), 9 `not an lvalue: StringLiteral`, 8 non-object block declarations, 8 arity, 6 unary operator, 6 string literal | the tier |
| 30 | clang under the pinned profile | not this lane's |
| 5 | UB refusals | never retires — the product |
| 4 | libc — `memset`, `__builtin_memcpy`, `__builtin_memset`, `__builtin_alloca` | widening the slice |
| 2 | timeout at fuel 64 | the fuel bound |
| 1 | `EnumConstantDecl: value` | the last absence case, now single |

**`refused-libc` fell 38 → 4 and the remainder is four distinct names**,
which is the shape a genuine libc frontier has — no single dominant entry
left. The 54 remaining `no layout` are now **entirely struct/union**, so
the instrument's share of that number is gone and what is left is the
profile decision this landing declined to fake.

**`unbound name` at 69 is now the largest single reason and is the first
true semantics rung on this board.** Census before building, as always.


---

## 2026-08-24-c-22 — `unbound name` was not a missing feature. It was a WRONG LAW.

`2026-08-24-c-21` left `unbound name` as the largest single reason on the
board — **69 of 300** — and called it "the first true semantics rung".
The census says it is a rung, but not the one that was named.

### The census: 69 of 69

Every one of the 69 unbound names is a **file-scope object** of the test's
own translation unit. Not one is a local, a parameter, a function name or
a typo. Measured against each test's own envelope:

| | |
| --- | ---: |
| tests refusing on `unbound name` | **69** |
| …where the name is a **file-scope object** | **69 (100 %)** |
| …a local, parameter, function or enum constant | **0** |

And of those objects: **35 have no initializer** (so §6.7.10p10
zero-initializes them, exactly, with nothing to evaluate) and **34 have
one**; by type, 39 scalar, 22 array, 8 struct/union.

### The defect, and it is one line of the tier

`callFn` started every frame at `env := []`. That is the rule *"no object
declared outside a function is visible inside one"*, and C's rule is the
opposite: §6.2.1p4, an identifier declared at file scope has file scope,
which runs to the end of the translation unit.

> **This was not a missing capability. It was a wrong law, and it read as
> a missing capability because the corpus the tier grew up on passes
> everything through parameters.** `ctx0 := { env := [] }` is a complete,
> confident, wrong model of C's scoping, and nothing in `sunfish.c` could
> tell — every one of its 58 functions takes what it needs as an argument.

That is the sharpest form of the day's recurring shape. The instrument
did not reveal a gap in the tier's vocabulary; it revealed a rule the tier
had asserted and never been contradicted on.

> **A corpus can only contradict the rules it exercises. A model validated
> on one program has, for every rule that program does not use, an
> untested assertion where it thinks it has a verified one — and those are
> indistinguishable from inside.**

### What landed

**Tier**: `Program.globals : Env`, and `callFn` seeds `ctx0.env` from it —
parameters bind ON TOP, so a parameter shadowing a global wins by being
consed later, which is §6.2.1's block scope doing its own work.

**Runner**: `setupGlobals` builds the objects — `allocZeroed` when there
is no initializer (§6.7.10p10, exact), `alloc` (indeterminate) plus the
tier's own `initObject` when there is one, so a half-built object refuses
on `J.2(11)` instead of reading a fabricated 0. An object whose type the
layout cannot size is **skipped**, staying unbound and loud, because
binding it would need a size and inventing one is the fabricated-layout
defect this lane refused two landings ago.

### WHAT THE FAST LOOP COULD AND COULD NOT CHECK HERE

Both changed files went through A17 before ticketing — the practice
`2026-08-24-c-21` had to learn the hard way — and one of them **could not
be checked whole**, for a reason worth recording:

* `LeanModels/C/C23/Stmt.lean` — **exit 0, zero warnings.**
* `LeanModels/C/Torture.lean` — **refused**: `` `globals` is not a field of
  structure `Program` ``.

That error is the INSTRUMENT, not the code. `lake env lean` writes no
oleans — which is what makes A17 lock-free — so `Torture.lean` was checked
against the `Stmt.olean` from before the field existed.

> **A17 cannot check a file whose DEPENDENCY you just changed. It checks a
> file against the tree's last BUILD, so the edit it is blindest to is the
> one that moves an INTERFACE — which is the edit most worth checking.**

Closed rather than carried: `setupGlobals` never mentions `Program`, so it
was extracted verbatim into a scratch file and checked against the same
stale oleans — **exit 0, zero warnings**. What stays unverified until the
tenure is the single line `{ prog with globals := genv }`, named here
rather than rounded away.

### THE PREDICTION

| bucket | now | predicted |
| --- | ---: | ---: |
| **scored** | 67 | **78**, band **62 – 115** |
| `refused-unsupported` | 191 | ~175 |
| `refused-ub` | 5 | ~8 |
| `timeout` | 2 | ~4 |

**The floor is BELOW the current score, and that is deliberate.** Every
band so far has had a floor that was arithmetic. This one does not,
because this change can REGRESS: a test that scores today while never
touching a global may now fail during `setupGlobals` if one of its
globals has an initializer the tier cannot run. That risk is real, it is
not estimable from here, and a floor of 67 would have hidden it.

Of the 69, 8 have struct globals that stay unsizeable, so ~61 can pass
this wall. At the last two landings' conversion rate — about one in ten
freed tests actually reaching a verdict — 78 is the point estimate, and
the band's upper half is the fifth-wall exposure that has now appeared
four times running.

### VERDICT — GREEN, and the scoreboard CONVICTED THE MODEL for the first time

Ticket `1787601875914569000-93535-crunga`:

```
[22:04:36] base: base 8cfca11 is AT the origin/master tip
[23:25:56] LOCK ACQUIRED after 4819s as 'crunga 93535'
[23:29:17] TRIAD DONE (build exit 0, gates green)
```

Classified **tier** this time (no `lakefile.toml` in the diff), 14 build
jobs + 38 gate jobs, **exit 0, 0 `error:` lines**. docs_check 91/91;
diff_test **1508 cases, 0 failed**; c_profile_probe 9/9; both
`--selftest`s ok; `--offline` re-verified all 300 sha256.

```
gcc.c-torture 98/300 scored  (passed 96, failed 2)
  the zeroes, kept apart: refused-unsupported 154, refused-libc 5,
    refused-ub 10, timeout 2, not-ingested 1, not-parsed 30,
    runner-error 0, not-fetched 0
```

**§9.0: 67 → 98/300 scored.** And `failed` is **2**, where it has been
`0` every run since the scoreboard existed.

### PREDICTED 78, band 62–115. ACTUAL 98 — inside, and this time HIGH.

| bucket | predicted | actual |
| --- | ---: | ---: |
| **scored** | **78** (band 62–115) | **98** — inside, 20 over the point |
| `refused-unsupported` | ~175 | **154** — 21 better than predicted |
| `refused-ub` | ~8 | 10 |
| `timeout` | ~4 | 2 |
| `refused-libc` | — | 5 |

Two bands running now, and the second one held for the opposite reason
from the first: `2026-08-24-c-21` came in **3 above its floor** because
almost every freed test hit another wall; this one came in **20 above its
point** because they did not. **The conversion rate is not a constant** —
it was ~10 % when the freed tests were unblocked at a DECLARATION, and it
is ~50 % here, because a test unblocked by having its globals exist was
otherwise ready to run. I had reused the earlier rate; the mechanism was
different and the rate came with it.

> **A conversion rate measured behind one wall does not transfer to the
> next. What a fix frees is not "a test" — it is a test AT A PARTICULAR
> POINT in its own execution, and how much is left after that point is
> the whole quantity.**

The floor being deliberately below the current score also paid: **no
regression occurred**, `setupGlobals` broke nothing that was scoring, and
the floor is what made that a checkable claim rather than a hope.

### THE TWO FAILURES — and the register is opened for them

A `failed` row is the only class of scoreboard row that can convict the
model, so **`docs/c-declared-divergences.json` opens here** (§5.0a,
schema `declared-divergences-1`, matching the ES/Python/Sv registers) with
one row per failure. Neither is folded into a count and left there.

**`c-div-1` — `20021127-1.c`: the MODEL IS RIGHT and the test still
fails.** It declares `llabs`, calls `llabs(-1)`, and then DEFINES
`long long llabs (long long b) { abort (); }`. It passes only if the
implementation recognises `llabs` as a BUILTIN and never calls the
definition. The model does the ordinary, correct thing — finds the
definition and calls it — and reaches `abort`.

> **The oracle is testing the COMPILER, not the language. A conformance
> corpus contains tests a conforming semantics must fail, and a
> scoreboard that cannot say so will eventually be "fixed" into agreeing
> with them.**

Retirement is named and NOT taken unilaterally: model the `<stdlib.h>`
builtins by name, or class builtin-recognition tests out of the
denominator with a named state — **the second is a scoreboard decision,
and silently excluding tests a model cannot pass is how a conformance
number stops meaning anything.**

**`c-div-2` — `20010224-1.c`: OPEN, and recorded UNDIAGNOSED.** The test
requires `bndpsd[1] == 140` (50+40+30+20); the model reached `abort`, so
it computed something else, and **which step is wrong has not been
determined**. The `model` field says exactly that instead of a guess, and
lists the candidates it does not distinguish between — the
`int16_t`/`short` spelling, §6.7.11p21's zero-fill of `masktab[5]` which
`setupGlobals` performs here for the first time, the address-of-element
arguments, and the loop's use of `j` mutated in its own body.

The row carries a retirement condition that is really a deadline: **it
must not survive a second landing unchanged.** An open-undiagnosed row
that ages is a carried divergence that was never declared, which is the
thing §5.0a exists to prevent.

> **Write the row before you understand the defect. A divergence recorded
> only once it is explained is a divergence that had a window in which it
> was invisible — and that window is exactly when it is most likely to be
> normalised.**


---

## 2026-08-24-c-23 — `c-div-2` DIAGNOSED: the model was right, the ENVELOPE was a different program

The row `2026-08-24-c-22` opened undiagnosed, with a deadline it set
itself — *"must not survive a second landing unchanged"*. It did not.

### The defect

`20010224-1.c` declares `int16_t masktab[6] = { 1, 2, 3, 4, 5 };` — five
initializers for six elements. **clang's JSON dumper puts a PARTIALLY
initialised array's elements under `array_filler`, with the implicit
filler prepended, and leaves `inner` EMPTY.** `e_InitListExpr` read only
`inner`, so the envelope said:

```json
"init": { "kind": "InitListExpr", "inits": [], "type": "int16_t[6]" }
```

The tier then did exactly the right thing with exactly the wrong data:
§6.7.11p21 zero-fills every unmentioned element, all six were unmentioned,
and `bndpsd[1]` came out 0 where the test requires 140.

> **The envelope was not malformed. It was a well-formed description of a
> DIFFERENT PROGRAM — and that is the one failure mode a schema cannot
> catch, because every check it offers was passed.**

Every guard in the chain was green: clang accepted the source, the
extractor exited 0, the schema validated, the ingester parsed, the
interpreter ran, and the answer was confidently wrong. **The only
instrument that could see it was the one that compares an answer to an
oracle** — which is what the scoreboard is, and it found this on its
fourth run.

### Why the row was opened before it was understood — and what that bought

`2026-08-24-c-22` wrote the register row with `model: NOT YET DIAGNOSED`
and listed four candidates it could not distinguish between. **None of the
four was right.** The defect was not in the tier at all.

> **Had it been left as a number, `failed 2` would have read as two model
> defects.** Writing the row before the diagnosis is what kept the
> question open long enough to be answered — and the answer moved the
> defect out of the semantics entirely.

### The fix, and what it deliberately does NOT carry

`e_InitListExpr` reads `array_filler` when `inner` is empty, and **drops
the `ImplicitValueInitExpr`**: §6.7.11p21's zero-fill is the MODEL's job,
which `initElems` already performs from the extent, so carrying clang's
filler would be a second answer to one question (§9.2).

Verified end to end before ticketing: `masktab[0] = 1`, **`masktab[5] =
0`** (the zero-fill was always right — that half of the model needed no
change), `psd[3] = 20`, and **`bndpsd[1] = 140`**, the exact value the
test demands.

### THE BLAST RADIUS, measured — and the number was NOT inflated

**4 of 270 envelopes** carried an empty `InitListExpr`. Their verdicts on
the last run: **1 `failed`** (this one), 1 `refused-unsupported`, 1
`refused-libc`, 1 `timeout`.

**None of them PASSED.** The silent corruption never produced a false
pass in this corpus, so the standing 98 was not built on it. That is a
measurement and not a reassurance: it is exactly the question a reader
should ask when an ingester is found to have been emitting wrong data
under a green score, and it is answerable only because the per-test log
keeps every verdict rather than a total.

### THE PREDICTION, and it is deliberately narrow

| bucket | now | predicted |
| --- | ---: | ---: |
| `passed` | 96 | **97** |
| `failed` | 2 | **1** |
| **scored** | 98 | **98**, band **97 – 101** |

**A tight band is as much a claim as a wide one.** `2026-08-24-c-21`'s was
41 points because the change freed tests at a declaration and everything
after was unmeasured. This one is 4, because only four envelopes changed
and three of them were blocked before they ever reached the data. Scored
should barely move at all: `c-div-2` was already counted — it was a
`failed`, and `failed` is a score. **What changes is not the size of the
number but its truth.**

### Landed ALONE, and the reason is attribution

The coordinator ruled two further items in the same message — the
`oracle-tests-compiler` state and the struct-alignment profile extension.
Neither is here.

> **A landing that moves the number for three reasons at once has
> measured none of them.** Every prediction in this lane has been per
> bucket precisely so that a miss localises; folding an extractor fix, a
> new zero-state and a profile decision into one tenure would produce one
> number and three candidate explanations for it.

### VERDICT — GREEN, and all three point predictions EXACT

Ticket `1787607980059859000-38534-crunga`:

```
[23:46:20] base: base bc6ef3f is AT the origin/master tip
[23:46:20] LOCK ACQUIRED after 0s as 'crunga 38534'
[00:56:24] TRIAD DONE (build exit 0, gates green)
```

Spine (an `extractors/` path is UNRECOGNIZED by `--classify` and escalates,
which is right: the extractor produces the envelopes fixtures load at
elaboration time, so it genuinely can change elaboration). **3785 jobs,
exit 0, 0 `error:` lines**, COVERAGE full. docs_check 91/91; diff_test
**1508 cases, 0 failed**; c_profile_probe 9/9; both `--selftest`s ok;
`--offline` re-verified all 300 sha256.

```
gcc.c-torture 98/300 scored  (passed 97, failed 1)
  the zeroes, kept apart: refused-unsupported 154, refused-libc 5,
    refused-ub 10, timeout 2, not-ingested 1, not-parsed 30,
    runner-error 0, not-fetched 0
  FIRST FAILURE (log order, verbatim): 20021127-1.c  failed
```

| bucket | predicted | actual |
| --- | ---: | ---: |
| `passed` | **97** | **97** |
| `failed` | **1** | **1** |
| `scored` | **98** (band 97–101) | **98** |

**Three point estimates, three exact hits** — and by the discipline's own
terms that is the LEAST informative outcome available, which is exactly
what it should have been. The prediction was narrow because the change was
narrow: four envelopes moved and three of them were blocked before the
data mattered. **An exact hit here is same-instrument transcription, and
the row is worth having because the alternative — a surprise — would have
meant the blast-radius measurement was wrong.**

Compare the day's four bands. `c-19` missed low because a second blocker
was hidden behind the first; `c-21` landed 3 above an arithmetic floor
because everything freed hit another wall; `c-22` landed 20 above its
point because a conversion rate did not transfer; this one hit dead on
because nothing was hidden. **The band width has tracked the real
uncertainty every time, and the four together are the argument for
predicting per bucket rather than in total.**

### AND THE ONLY REMAINING FAILURE IS THE ONE A CONFORMING SEMANTICS MUST FAIL

`FIRST FAILURE: 20021127-1.c` — `c-div-1`, the `llabs`
declare-call-define shape. The scoreboard's `failed` column is now
**exactly one test, and it is the test where the model is right.**

That is the cleanest possible state to hand the `oracle-tests-compiler`
ruling: the state has exactly one member, its membership is already
argued in the register, and nothing else is hiding in the column.


---

## 2026-08-25-c-24 — THE REGISTER RESHAPED, and a gate that could not contradict its own tier

`harness/divergence_register.py` exits 1 on master, on **this lane's two
rows**, and every tenure whose floor runs it is red. ES, pyc, Ada, SV and
wasm are holding enqueues. Four problems, all mine:

```
row c-div-1 kind is 'oracle-shape', expected one of semantic | provenance
row c-div-1 guards must be TWO distinct named guards, got [one pin sentence]
row c-div-2 kind is 'retired-diagnosed', expected one of semantic | provenance
row c-div-2 guards must be TWO distinct named guards, got [three sentences]
```

### The root cause is not the rows. It is which gate the C floor runs.

`2026-08-24-c-22` invented `oracle-shape` and `retired-diagnosed` in good
faith and wrote guard *sentences* where the canon wants guard *names* —
and **no C tenure could contradict it**, because this lane's floor runs
`docs_check`, `diff_test`, `refusal_census`, `c_profile_probe` and
`c_torture_gate`, and never `divergence_register.py`. Other tiers had it;
this one did not; the rows sailed through four green tenures and detonated
on somebody else's floor.

That is `2026-08-24-c-22`'s own law arriving one layer up, and it is worse
here because a gate is supposed to be the thing that cannot be fooled:

> **A CORPUS can only contradict the rules it exercises; a GATE can only
> contradict the files it runs on. A lane that writes into a shared schema
> without running the shared checker has not been passing that check — it
> has been ABSENT from it, and absence and success are the same colour on
> a green board.**

The fix has to be both halves, and the second is the one that lasts:
**`harness/divergence_register.py` and `harness/c_divergence_probe.py` now
run in `tools/c_torture_gate.sh`, before the expensive half**, so a
malformed row costs seconds rather than a build — and so this class can
never again go unexercised in this lane.

### The rows, reshaped

**`c-div-1` stays LIVE, `kind: semantic`.** The oracle and the model
disagree about what the program MEANS — nothing about ingestion is
involved, which is exactly what separates it from `c-div-2`. Its
retirement condition is now an EVENT rather than a fork: the coordinator's
ruling authorises the `oracle-tests-compiler` zero-state, so the row
retires on the landing that adds the state, moves `20021127-1.c` into it
by name and pins the membership list. Modelling the `<stdlib.h>` builtins
is explicitly recorded as NOT the path — it would adopt GCC's optimiser
behaviour as if it were C semantics.

**`c-div-2` moves to `retired_rows`, `kind: provenance`** — the canonical
shape, all live fields plus `retired` and `retired_by`, with the
end-to-end evidence travelling with it. `provenance` rather than
`semantic` is the whole diagnosis in one field: the model was right and
the ENVELOPE described a different program.

### Two guards that run with no corpus, no toolchain and no lock

The canon wants `..._still_divergent` and `..._has_not_widened` as NAMES a
probe defines. The C tier's difficulty is that its divergence lives in a
scoreboard produced under the build lock from a GPL corpus — none of which
a checker may assume. So the number became a committed artifact:

* `harness/c_torture_score.py --emit` writes
  **`docs/c-torture-scoreboard.json`** — the counts, and **every `failed`
  test BY NAME**, because a count cannot say which;
* `harness/c_divergence_probe.py` reads it offline. `c_div_1_still_divergent`
  asks whether `20021127-1.c` is still in `failed_tests`;
  `c_div_1_has_not_widened` asks whether the `failed` count is still ≤ the
  number of live rows — **a failing test with no row is a divergence
  nobody declared**;
* and `c_torture_gate.sh` compares the committed scoreboard against the
  fresh run, so the published number cannot rot (qol-21's law), skipping
  the comparison only when the machine has no corpus at all — failing
  there would punish a lane for not holding a cache it is forbidden to
  vendor.

> **A guard that can only run where the evidence was produced is not a
> guard, it is a memory of one. Publish the evidence and the guard becomes
> portable — which is the same move that turned §9.0 from a log line into
> a file.**

**And the still_divergent guard is a trap this row walks into on purpose.**
`c-div-1`'s retirement path is reclassification, so the day
`oracle-tests-compiler` lands, `20021127-1.c` leaves `failed` and **this
guard goes red.** That is correct and is written into both the probe and
the row: the row must then be retired DELIBERATELY, not drained by a
change that happened to empty it.

### The number, and a correction to the expected one

**`gcc.c-torture` 98/300 scored (passed 97, failed 1)** — unchanged by
this landing, which touches no Lean.

The dispatch expected **99**, from `20010224-1.c` flipping failed→passed.
The flip happened; the total did not move, because **`failed` is already
a score**. `scored = passed + failed`, so a test moving from `failed` to
`passed` changes the composition and not the sum — 96+2 and 97+1 are both
98. The landing's own entry said so when it predicted 98 and hit it
exactly; repeating it here because an off-by-one in a headline number is
exactly the kind of thing that gets copied forward.

*(The checker's `SyntaxWarning` at line ~122 is pyc's and is dispatched
there. Not touched here — two lanes editing one file is how a fleet
unblock becomes a fleet conflict.)*


---

## 2026-08-25-c-25 — `oracle-tests-compiler`: a state that makes the number SMALLER and truer

Ruled after `2026-08-24-c-22` found the C tier's first failing test and
`2026-08-25-c-24` reshaped its register row: a conformance corpus contains
tests a **conforming semantics must fail**, and neither available option
was acceptable. Modelling the `<stdlib.h>` builtins by name would adopt
GCC's optimiser behaviour as if it were C semantics — a wrong law bought
to please an oracle. Silently excluding the test is the number-death this
lane already named. So: a third thing, the UB pattern's shape.

**`oracle-tests-compiler` is a NAMED ZERO-STATE**, printed in the
zero-states line beside `refused-ub`, and like the UB refusals **it never
empties, because it is part of what the number MEANS.**

### The number goes DOWN, and that is the point

| bucket | before | predicted |
| --- | ---: | ---: |
| `passed` | 97 | **97** |
| `failed` | 1 | **0** |
| `oracle-tests-compiler` | — | **1** |
| **scored** | **98** | **97** (band 97–98) |

`scored = passed + failed`, so moving a test out of `failed` and into a
zero-state **removes it from the score**: 98 → 97.

> **A named exclusion that makes the number BIGGER is a whitewash; one
> that makes it smaller is a measurement. `oracle-tests-compiler` costs
> this tier a point of its headline figure, and that is the strongest
> evidence available that it is not being used to flatter it.**

The band's upper end is 98 — the value if the SHAPE guard refuses the
classification and the test stays `failed`. There is no third outcome, and
no wall behind this one: nothing new runs.

**AND THE PREDICTION IS EXECUTABLE THIS TIME.**
`docs/c-torture-scoreboard.json` was edited to the predicted counts
**before** the tenure, and `tools/c_torture_gate.sh` compares the committed
board against the fresh run. So a miss is a RED GATE, not a paragraph in a
later entry.

> **A prediction that a gate can check is a claim; one only a human
> compares afterwards is a hope with a timestamp.**

### TWO LOCKS, because a named state is exactly what gets abused later

**Lock one — membership by NAME, with the citation, in the pin.**
`tools/c_corpus_fetch.py` carries `ORACLE_TESTS_COMPILER`, keyed by test
name, valued with the SYMBOL and the citation (`20021127-1.c` →
`llabs`, §7.24.6.1, the declare-call-define shape). `--write-pin` emits it
into `docs/c-torture-pin.json`, so membership travels with the fingerprint
and a reader of the pin can see it.

**Lock two — the SHAPE, re-derived from the ingested AST.**
`LeanModels/C/Torture.lean`'s `hasDeclareCallDefine` checks, per test, that
the unit CALLS the symbol, DEFINES it with a body, and that the body
reaches `abort`. If the shape is absent the classification is refused and
the verdict stays `failed`.

> **A name on a list cannot stop a state from being used, later and in
> good faith, to sweep an ordinary failure out of the `failed` column. The
> two locks fail in different directions: a human name so it cannot widen
> by accident, a machine shape so it cannot widen by intent.**

And the membership list itself is pinned by `c_torture_gate.sh`, which
asserts the scoreboard's `oracle_tests_compiler_tests` equals the pin's
keys — a test entering or leaving this state without the pin changing is
the state being used to move a number.

### c-div-1 RETIRES BY RECLASSIFICATION, and the trap sprang as designed

`2026-08-25-c-24` wrote `c_div_1_still_divergent` knowing it would go red
on exactly this landing, and said so in both the probe and the row. It
did. **The row could not be drained by a change that happened to empty
it — it had to be retired deliberately**, which is what a two-way gate is
for.

`docs/c-declared-divergences.json` now has **ZERO live rows** and two
retired ones. That is a real state, not an empty file: the C tier declares
no divergence today, the checker still runs on every C tenure
(`2026-08-25-c-24`), and the probe reports no guards because there is
nothing live to gate — it derives its guards FROM the live rows rather
than from a hard-coded list, so a retired row takes its guards with it and
cannot leave an ORPHANED name behind.

**The membership is deliberately NOT gated by the divergence register.**
It is not a debt — it is a permanent property of the corpus — and filing a
permanent property as a debt would put a row in a ledger that ages things
which are not supposed to age.

### THE REGISTER FILE IS DELETED, and the canon said so before I could argue

> **SUPERSEDED, 2026-08-26 — and the annotation stays rather than the section
> being rewritten.** Arch ruled (`52e9c4b`) that `rows: []` beside a non-empty
> `retired_rows` is LEGAL AND REQUIRED TO STAY, and filed the structural defect
> against itself: §5.0a mandated `retired_rows` while the deletion rule
> destroyed them. The file and the probe are RESTORED by `2026-08-26-c-27`.
> What follows was correct as taken — it is the compliance that surfaced the
> defect — and only its tense is wrong (§5.4b).


Retiring `c-div-1` left `docs/c-declared-divergences.json` with **zero live
rows**, and `harness/divergence_register.py` refuses that in as many words:

```
no rows: a register file with nothing in it is a claim that the tier has
no debts, and should be deleted rather than filed empty
```

This lane is the first tier to reach zero — es, python and sv all still
carry one — so the rule had never been exercised against a real file. It
is right, and it costs something real: **the two retired rows go with the
file.** `c-div-1` and `c-div-2` survive as prose here (`2026-08-24-c-22`,
`-c-23`, `2026-08-25-c-24` and this entry), which is §9.5's durable home,
but they stop being machine-readable.

> **A ledger that may not be empty cannot also be the archive. "Delete it
> rather than file it empty" is correct about the CLAIM a file makes and
> silent about the HISTORY it holds — and the tier that empties first is
> the one that discovers the two were the same file.**

Reported, not fixed: whether a retired-only register should be legal is
`harness/divergence_register.py`'s owner's call, not this lane's, and
inventing a `c-retired-divergences.json` to dodge the rule would be
exactly the shape the rule exists to stop. `harness/c_divergence_probe.py`
is deleted with it — a probe whose register is gone is the ORPHANED shape
the checker convicts.

**`divergence_register.py` STAYS in the C gate**, and that is deliberate
now that this tier files nothing: the lane broke the fleet once by not
running a shared checker, and *"we have no rows today"* is precisely the
reasoning that let it happen.

### RIDE-ALONG — the fleet's field-collision sweep, and the answer is NEGATIVE with a check

Arch's two-instance sweep: any field the INSTRUMENT writes that the SOURCE
it copies from could overwrite. ES's defect was the node type written to
`kind`, then ESTree properties merged over it, with
`VariableDeclaration`'s own `kind` winning.

**This extractor has the SHAPE.** `extract.py`'s `node()` read:

```python
out = {"kind": k, "span": span}
out.update(fn(n))          # the handler wins
```

**It does not have the DEFECT.** Checked by parsing the extractor's own
AST rather than by reading it: of its **36** `e_*` handlers, **none**
returns a dict literal keyed `kind` or `span`, and **none** builds a dict
with a non-constant key — so no source-chosen name can reach the merge.

> **A negative sweep result is only worth the check that produced it. "I
> read the handlers" is worth nothing at 36 of them; "I parsed them and
> looked at every dict key" is a number a reader can re-derive.**

The channel is closed anyway, because *"no handler does this today"* is a
fact about 36 functions and not about the 37th: a handler returning `kind`
or `span` now **dies loudly** instead of overwriting the instrument, and
`extract.py --selftest` lowers a colliding node through the real
`Extractor` to prove it — both directions, plus the ordinary path.

The guard is **inert on output, and that was measured, not assumed**:
regenerating all 270 envelopes leaves `docs/c-torture-pin.json`
byte-identical. A change to an instrument that produces a measured
artifact owes that differential.

`extract.py --selftest` joins the C gate beside the other three.

### VERDICT — GREEN, and the EXECUTABLE prediction held

Ticket `1787642655652345000-55338-crunga`:

```
[09:24:16] base: base c87de73 is AT the origin/master tip
[10:14:19] LOCK ACQUIRED after 2960s as 'crunga 55338'
[10:49:49] TRIAD DONE (build exit 0, gates green)
[10:49:51] LOCK RELEASED (mine)
```

Spine, tree `6c148259a841`, **3786 jobs, exit 0, 0 `error:` lines**,
COVERAGE full. docs_check 91/91; diff_test **1508 cases, 0 failed**;
c_profile_probe 9/9; **divergence_register OK — 3 tier files**; and all
four instrument self-tests: `c_corpus_fetch`, `c_torture_score`,
`extract`, plus the register.

```
gcc.c-torture 97/300 scored  (passed 97, failed 0)
  the zeroes, kept apart: refused-unsupported 154, refused-libc 5,
    refused-ub 10, oracle-tests-compiler 1, timeout 2, not-ingested 1,
    not-parsed 30, runner-error 0, not-fetched 0
```

`97 + 154 + 5 + 10 + 1 + 2 + 1 + 30 = 300`.

**And the two lines that make this landing different from every prior
one:**

```
c_torture_gate: committed scoreboard matches this run (97/300 scored)
c_torture_gate: oracle-tests-compiler membership matches the pin: ['20021127-1.c']
```

The first is **the prediction, checked by a gate**. `scored 97, passed 97,
failed 0, oracle-tests-compiler 1` was committed to
`docs/c-torture-scoreboard.json` before the tenure ran; the run produced
exactly that, and had it not, the gate would have gone red rather than a
later entry explaining the miss.

> **Six predictions in this lane, and this is the first one the machine
> could adjudicate. A prediction a gate can check is a claim; one only a
> human compares afterwards is a hope with a timestamp — and the
> difference is not rigour, it is whether being wrong costs anything.**

The second is the membership lock: the state has exactly the member the
pin names, so it cannot have been used to move a number.

### §9.0 — the standing number, and it went DOWN

**`gcc.c-torture` 98/300 → 97/300 scored.** The tier did not get worse and
nothing regressed: `passed` is 97 both before and after. What changed is
that a test which a conforming semantics MUST fail stopped being counted
as a thing the model could have got right.

> **The day a conformance number goes down because the tier learned what
> it is allowed to be judged on is the day the number starts being worth
> quoting.**


---

## 2026-08-26-c-27 — THE REGISTER COMES BACK, and the reversal is recorded rather than tidied

`2026-08-25-c-25` retired this tier's last live row, which left `rows: []`,
which the checker refused in as many words — so the register file and
`harness/c_divergence_probe.py` were **deleted**, because that is what the
canon then said. Arch ruled the other way (`52e9c4b`), adopted the
diagnosis as law, and **filed the structural defect against itself**: §5.0a
mandated `retired_rows` while the deletion rule destroyed them.

> **A rule about a CONTAINER is untested until the container is empty.**
> (Arch's wording, and it is the same law this lane keeps meeting from the
> other side: a corpus can only contradict the rules it exercises.)

The ruling: a file with `rows: []` and a non-empty `retired_rows` is
**legal and required to stay**, because *"no LIVE debts — and here is how
each one closed"* is a **stronger** claim than a file with rows.
Delete-rather-than-file-empty survives only for the never-had-a-row case.

### What came back, and in the fleet's shape

`docs/c-declared-divergences.json` returns with **zero live rows and two
retired ones**, each keeping **both** its guards — because retirement moves
a row, it does not end the watch, and *the guard is what would notice the
divergence coming back*.

`harness/c_divergence_probe.py` returns built to `dfc65dd`'s shape from the
start, not adapted afterwards:

* **`LIVE_GUARDS` / `RETIRED_GUARDS` partition**, `rc` from live only;
* retired guards **run, print, and appear in `--json`**, and their failure
  is reported and never fatal — otherwise every retirement would red its
  own probe forever, and §5.0a clause 3 asks the checker for a guard's
  EXISTENCE, not its passage;
* **and the regression alarm**: a retired `*_still_divergent` that HOLDS
  means the divergence came back, and that direction GATES.

**This tier has NO live rows at all, which makes the alarm the only thing
here that can ever set `rc`.** The probe's entire job is to notice a
return — which is the sharpest possible statement of what an archive that
is still watched is *for*, and it only became visible because this lane
was the first to empty.

Polarity, as the run reports it:

```
c_div_1_still_divergent  FAIL  20021127-1.c is not in `failed`; it sits in
                               oracle-tests-compiler as the retirement intended
c_div_2_still_divergent  FAIL  20010224-1.c is not in `failed`; the extractor fix holds
c_div_1_has_not_widened  ok    membership pinned=['20021127-1.c'] scored=['20021127-1.c']
c_div_2_has_not_widened  ok    scoreboard failed=0, live register rows=0
```

Two FAILs that are the CORRECT reading, and the event worth noticing is
either of them flipping to `ok`.

### The two guards are not decoration — they watch different fixes

`c-div-1` retired by **reclassification**, so its watch asks whether
`20021127-1.c` is back in `failed` (the `oracle-tests-compiler` state
stopped holding) and whether that state has acquired members the pin does
not name. `c-div-2` retired by a **fix**, so its watch asks whether the
`array_filler` regression returned, and — with zero live rows — whether
**any** test failed at all, since a failing test with no row is a
divergence nobody declared.

### And the deleted section is ANNOTATED, not rewritten

`2026-08-25-c-25`'s "THE REGISTER FILE IS DELETED" section keeps its text
and gains a SUPERSEDED note pointing here. It was correct as taken — it is
the compliance that surfaced the defect — and only its tense is wrong
(§5.4b's annotation norm; the same reason `qol-21`'s published table was
annotated rather than edited).

> **A reversal that erases the reasoning it reverses destroys the only
> evidence that the rule was tested. The compliance IS the finding.**


---

## 2026-08-26-c-28 — OPS-148: a NAMED NEGATIVE by grep, and the defect only RUNNING found

### The sweep, counted — **7 instruments**

`harness/c_divergence_probe.py`, `harness/c_torture_score.py`,
`harness/c_profile_probe.py`, `tools/c_corpus_fetch.py`,
`tools/c_torture_gate.sh`, `extractors/c/extract.py`,
`LeanModels/C/Torture.lean`.

| shape | grepped | found |
| --- | ---: | --- |
| first-element access over rows | **29 sites** | **none unguarded, and none over register rows** |
| `if rows:` as a proxy for "has a register" | **0 sites** | — |
| folds whose identity element is unstated | **8 sites** | **none — every identity is written at the call** |
| empty-collection messages that read as verdicts | **0 sites** | 3 text hits, all docstring prose or a selftest label |

**On (1)**, the 29 are all one of four safe shapes and it is worth naming
which, because "0 unguarded" is only meaningful if the reader can see what
guarded them: `c[0] if c else None` (17 sites in the extractor),
`next(…, None)` with an explicit default (3), an index preceded by a
length test (`len(parts) >= 2`, `"\t" in line`) (4), and — the nicest —
`e_ForStmt`'s `c = nonempty(n) + [None] * 5`, which **pads before it
indexes**, so the absent-slot identity is `None` by construction rather
than by a branch anybody has to keep.

**On (3)**, the two Lean folds are the ones the ride-along asked about and
both state their identity in the call: `foldl step (some (0, 1))` — offset
0, **alignment 1**, the only value that leaves `roundUp` a no-op for an
empty aggregate — and `foldl step (none, some 0)` — not-found, offset 0.
The Python folds are `sum(1 for …)` (identity 0) and `all(…)` over a fixed
non-empty tuple.

> **A named negative has to name what made it negative. "0 unguarded" is a
> claim; "29 sites, of four shapes, and here they are" is a claim a reader
> can falsify.**

### AND THE ONE GREP COULD NOT HAVE FOUND

pyc's addendum — *a named negative produced by grep is a claim about
TEXT, not about BEHAVIOUR* — and it landed on this lane directly. Running
`c_divergence_probe.py` against a **deleted** and then a **malformed**
scoreboard found exactly the fold pyc predicted, and it was **worse here
than anywhere else in the fleet**:

Every guard read `_load(SCOREBOARD)`; a missing file returned `None`; each
guard folded that into `(False, "no committed scoreboard")`. For a RETIRED
`still_divergent`, `False` means *"the divergence is gone"* — so a deleted
scoreboard printed the healthy picture. And because the regression alarm
fires on `held == True`, **an absent artifact silently disarmed the only
thing this probe does.**

> **In a tier with no live rows, "nothing was compared" and "all clear"
> are the same two words — and the alarm is the thing that goes quiet.
> The fail-closed rule protects the fleet through its LIVE guards; where
> there are none, it protects nothing unless you say so.**

Fixed in pyc's shape, one shape fleet-wide: three states, `held is None`
meaning nothing was compared, `no-run` / `watch` / `ok` / `FAIL` statuses,
and the verdict line `COULD NOT VERIFY (no comparison ran — not a model
verdict)`. `_load` now also treats a MALFORMED file as unverifiable rather
than raising, because a traceback is loud about the environment while
wearing the costume of a crash in the probe.

**Plus one corollary this tier needed and the fleet shape does not
express.** pyc's rule is *"live guards fail CLOSED"* — but with zero live
guards that clause has nothing to bite on, and an unverified probe would
still exit 0. So: **where there are no live guards, "could not verify"
gates directly.** The principle is fleet-wide; the mechanism was not, and
this is the pole where the difference is visible. Offered to arch as an
addendum rather than a fork.

### The three states, RUN

| scoreboard | verdict | `rc` |
| --- | --- | ---: |
| present | `PASS` | **0** |
| **deleted** | `COULD NOT VERIFY (no comparison ran — not a model verdict)`, 4 guards `no-run` | **1** |
| **malformed** | same | **1** |

Before the fix, rows 2 and 3 both printed the healthy picture and exited
**0**.


---

## 2026-08-26-c-29 — STRUCT LAYOUT, from a rule the profile now DECLARES

`2026-08-25-c-25` refused to lay out a `struct` and gave the reason: *"a
layout computed from an UNDECLARED rule is a FABRICATED layout — the same
defect as a fabricated column, one abstraction up."* That objection was to
the rule being undeclared, not to computing one.

### The profile declares it, and PROBES it

`docs/c-profile.md` §4a and the fact `natural_alignment`, alongside
`char_bit_8`, `int_32` and `long_64` — implementation-defined in exactly
the same sense, pinned in exactly the same way. The expression:

```
_Alignof(int) == 4 && sizeof(struct { char c; int i; }) == 8 &&
_Alignof(struct { char c; int i; }) == 4 && sizeof(struct { char a; char b; }) == 2
```

Four conjuncts for the four halves of the rule — a scalar's alignment, the
padding BEFORE a member, the aggregate's own alignment, and the absence of
padding where none is needed — and **both profiled hosts fold it true**
(`arm64-apple-darwin`, `x86_64-unknown-linux-gnu`).
`c_profile_probe --check` now satisfies **9** depended-on facts, up from 8.

> **A profile does not make an implementation-defined choice go away; it
> makes it ATTRIBUTABLE. The distance between "we may not compute this"
> and "we compute it from a stated rule" is one probed fact.**

### `torLayout` computes it

`sizeAlign` returns size and alignment **together**, because they are one
recursion: a structure's size needs its members' alignments and a member's
alignment may itself be a structure's. Splitting them would be two walks
that must agree. `fieldOffIn` walks the same rule for `offsetof`, peeling
the qualifiers and one pointer level because the base spelling arrives as
the EXPRESSION's type (`Pos` for `x.f`, `const Pos *` for `p->f`).

**Union-ness is read from the SPELLING**, and that is a named limit rather
than a hidden one: the `c-0.1` envelope does not carry clang's `tagUsed`,
so `Decl.record` has a name and fields and no struct/union bit. Exact for
the type being sized; a translation unit declaring BOTH `struct u` and
`union u` would collide on the tag. Nothing in the corpus does.

Still a named zero, and still deliberately: `_Alignas`, `#pragma pack` and
bit-fields are outside the pin AND outside the modelled vocabulary, so
they arrive as `unsupported` and never as a wrong offset.

### THE PREDICTION — and this one is adjudicated by a gate

| bucket | now | predicted |
| --- | ---: | ---: |
| `passed` | 97 | **110** |
| `refused-unsupported` | 154 | **141** |
| **scored** | **97** | **110**, band **97 – 135** |
| `failed` | 0 | **0** |

54 of the 154 `unsupported` are `no layout for declared type`, all
struct/union. Of those I expect **~25 %** to reach a verdict — between the
array-layout landing's 10 % (freed at a declaration, everything after
unmeasured) and the globals landing's 50 % (freed tests were otherwise
ready). The floor is **97** because nothing can regress: the change only
ADDS layout answers.

**`failed = 0` is the load-bearing half of this prediction.** A newly
runnable test that FAILS would be a divergence nobody declared, and
`c_div_2_has_not_widened` — *failed ≤ live rows*, and there are zero live
rows — would go red and take the gate with it. That is the archive doing
its job on its first real test: a new failure cannot land silently, it
must be written down as a row first.

**AND A COST THIS INTRODUCES, named before it is paid.** The committed
scoreboard is compared by the gate, so a landing that INTENDS to move the
number must predict it exactly or go red. For `2026-08-25-c-25` that was
free — the delta was deterministic. Here it is not, and an exact hit on a
nine-bucket vector is unlikely.

> **A drift gate and a prediction adjudicator are the same mechanism
> pointed at two different questions, and the mechanism cannot tell them
> apart. When a landing means to move the number, "drift" is the wrong
> reading of the same comparison.**

The protocol that falls out, and it is not a workaround: **a frontier
landing's first tenure may red on the comparison, and that red PRINTS BOTH
VECTORS — so the red IS the measurement.** The board is then committed
from the gate's own output and the second tenure is green. Deterministic
landings still cost one. Named here rather than discovered by whoever
lands next.


## 2026-08-26-c-30 — THE SCORER WAS NEVER IN THE BUILD, and `--classify` is not a dry run

Two findings, both caught by `triad.sh` BEFORE a tenure was spent, and both
paid for by the same pre-enqueue habit: classify, then read what it says.

**Finding 1 — `lean_exe c-torture-run` was never a default target.** Inch 6
(1ef4a02) added the executable to `lakefile.toml` and did not add it to
`defaultTargets`. Nothing imports `LeanModels/C/Torture.lean` either: the C
tier reaches the build graph only through `Examples/c/sunfish/guards.lean`
importing `LeanModels.C`, and `Torture` is on no path from there. So `lake
build` has never compiled the scorer, and **every green triad since inch 6
was green about nothing where the scoreboard's own program is concerned** —
including the three landings that edited that file. The §9.0 number was
produced by a binary CI does not build. Fixed in this landing by adding
`c-torture-run` to `defaultTargets`; the classification moves from `tier` to
`spine` as a result, and that cost is the honest price of the check.

  The law: **an executable is in the build only if it is in `defaultTargets`
  — being in `lakefile.toml` is registration, not coverage.** The ES lane's
  2026-08-22-es-1 states the general shape (a landing that takes a default
  can land green against FEWER checks than the one before it); this is the
  same shape arriving from the other direction, where the check was never
  added rather than quietly retired. `triad.sh`'s IMPORTED-BY-NOTHING warning
  names it in one line and it had been printing, unread, for three landings.

**Finding 2 — `--classify` RUNS; `--classify-only` prints.** Reading
`--classify` as a dry run enqueued two calign tickets in eight minutes,
neither of them detached. Both were killed by PID with parentage verified to
this session (`claude --resume`, PID 12455 — no process of Thomas's was
touched) and both tickets removed from `/tmp/ls-build-queue`; the queue was
left exactly as found, five lanes, lock held by `es`. The cost was the queue
position, not a tenure.

  The law: **the flag that scopes a tenure and the flag that describes one
  differ by a suffix; `tools/triad.sh --classify-only` is the one that runs
  nothing.** It is documented at line 166 of the script, one line below the
  spelling that does run. A lane reaching for a dry run should reach for the
  longer name.

**Standing number unchanged by this landing: `gcc.c-torture` 97/300 scored
(passed 97, failed 0).** The committed prediction for the alignment rung's
tenure is `passed 110, refused-unsupported 141, scored 110, failed 0`.

## 2026-08-26-c-31 — THE PREDICTION MISSED BY 7, and the red printed a two-year-old lie

The alignment rung's tenure went **build exit 0, gates RED**, and the red was
the scoreboard comparison. Both vectors, from the gate's own output:

| | passed | failed | refused-unsupported | refused-libc | refused-ub |
|---|---|---|---|---|---|
| committed (prediction) | 110 | 0 | 141 | 5 | 10 |
| fresh (truth) | 103 | **2** | 140 | 9 | 12 |

**THE PREDICTION FAILED BY 7 ON `passed`, and it was wrong in the worse
direction: it predicted `failed 0` and got `failed 2`.** Say it plainly —
the rung shipped a soundness regression. `failed 0` is this lane's whole
claim (the model refuses or it is right; it does not answer wrongly), and
the layout rung broke it by routing 14 tests past the "no layout" refusal
into code that could not carry them. The accounting is exact: 154 → 140
`refused-unsupported`, and the 14 went 6 → passed, 4 → libc, 2 → ub, 2 →
**failed**.

**FINDING 1 — `p + n` HAS BEEN ADVANCING EIGHT BYTES, ALWAYS.** Bisected on
the tenure's own binary against hand-written probes (no rebuild: the driver
takes any manifest, so the probes are envelopes in a scratch directory).
`p[1]` passes; `*(p+1)` fails — on `int *` as surely as on a struct
pointer. `evalArith` asks `ctx.layout.size ty` where `ty` is the
EXPRESSION's type, which for `p + n` is the POINTER, and `torScalarSize`
answers 8 for anything ending in `*`. Its neighbour `indexAddr` uses the
identical phrase correctly, because clang types `a[i]` as the ELEMENT.

  The law: **when one accessor is asked for two different types by two
  callers, the call sites must say which — `layout.size ty` meant "element"
  at a subscript and "pointer" at a `+`, and the idiom read the same at
  both.** Fixed with `pointeeOf`, which makes the peel explicit and named.

  This was never a regression of the layout rung. It was ALWAYS wrong, and
  the corpus hid it: of the 15 tests containing pointer `+`/`-`, the nine
  distinct pointee spellings are `char`, `const char`, `int`, `unsigned
  int`, `short`, `unsigned short`, and three structs — **not one of them is
  eight bytes wide**, so every site was wrong and no passing test happened
  to observe it. Five tests were refusing as `refused-ub` with
  `outOfBounds` faults that DECODE AS THIS BUG: `20030218-1` reports
  `off 8, elemSize 8, size 2` on a `short`, and `20020503-1` reports
  `off 1016` for `buf + 127` into a `char[128]`. **The model was accusing
  correct programs of undefined behaviour**, which is worse than refusing
  them: a refusal says "I cannot"; a UB report says "you did".

**FINDING 2 — THE EXTRACTOR DROPPED BIT-FIELD WIDTHS.** `20031211-1.c`
stores `0xbeef` into a `unsigned int b : 1` and expects to read 1. The
envelope said `{"name":"bitfield","type":"unsigned int"}`: clang's
`isBitfield` and its width were never read, so the model laid the member
out full-width, read `0xbeef` back, and reported a FAILURE. **Exactly the
shape of c-div-2** (2026-08-24-c-23), where the dropped key was
`array_filler` — an extractor that drops a key hands the model a different
program, and the model is then correct about the wrong one.

  The law: **a model that cannot represent a construct must DECLINE it, not
  approximate it** — the AST now carries `bits`, the extractor DIES on a
  bit-field whose width it cannot read rather than degrading to "not a
  bit-field", and a record with any bit-field is omitted from the layout,
  which makes every use of it refuse.

  **This costs a pass, and the pass deserved to go.** `20000113-1.c` has
  three bit-fields (`1`, `2`, `3` bits) holding 1, 2 and 5 — every value
  fits, so full-width layout gives the same answer and the test PASSED for
  a reason that was not true. 23 of the 300 tests contain a bit-field; 7
  never parse and 13 already refuse, so exactly two change bucket. This is
  2026-08-25-c-25's rule again: a state that makes the number SMALLER and
  truer.

**THE NEXT PREDICTION IS DERIVED, NOT GUESSED.** The 15 pointer-arithmetic
tests were enumerated from the envelopes, joined to the previous run's
per-test verdicts, and each read: `20030218-1` and `20030828-2` pass
(`offsetPtr` already permits one-past-the-end, so the corrected strides land
in bounds); `20000412-6`, `20000801-1` and `20020503-1` still refuse,
because past the stride they hit `tmp++`, `*bp++` and `*--p`, and pointer
increment is unsupported.

  `passed 105, failed 0, refused-unsupported 145, refused-libc 9,
  refused-ub 7, oracle-tests-compiler 1, timeout 2, not-ingested 1,
  not-parsed 30`. Scored stays 105 and every point of it becomes a pass.
  The band lives here rather than in the file: the two new passes are the
  soft part, since each must clear its whole body once the stride stops
  lying.

**A COST THIS LANDING CREATES, NAMED.** Adding `c-torture-run` to
`defaultTargets` (2026-08-26-c-30) put `LeanModels/C/Torture.lean` into the
build graph, and `tools/check.sh` refuses `--iterate` on library files. The
file that was the lane's fast loop now costs a tenure to check. That is the
right trade — coverage beats convenience — but it is a real loss and the
next hand should know it was bought, not lost.

**§9.0 standing number: `gcc.c-torture` 105/300 scored (passed 103, failed
2)** — the first C number ever produced by a `lake build` that compiled the
scorer, and the first with a non-zero `failed`. Both halves are fixed in
this landing; the number above is what is TRUE until its tenure runs.
