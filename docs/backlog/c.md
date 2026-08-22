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
