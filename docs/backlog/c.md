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
