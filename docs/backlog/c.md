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
