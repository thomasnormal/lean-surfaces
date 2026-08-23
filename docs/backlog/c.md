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

## INBOUND FROM THE SOFTFLOAT LANE — `2026-08-22-softfloat-2` (C lane's to triage)

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
