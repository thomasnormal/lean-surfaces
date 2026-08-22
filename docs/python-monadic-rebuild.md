# The Python monadic rebuild — the plan, and the first parity run

**Thomas's ruling** (2026-08-22): *"Rather than spending time debugging 5000
lines of python interpretation, I would rather rebuild the 'correct' version
from the start."*

This document is the rebuild's plan and its running gate report. The subject is
a **second Python semantics** written on the family substrate
(`docs/family-architecture.md` §3.4) in do-notation, whose acceptance test is
**parity with the trunk interpreter on the trunk's own differential battery**.

**Nothing here retires anything.** `LeanModels/Python/Semantics.lean` stays
authoritative and untouched, the campaign's files are untouched, no proof
migrates, and `LeanModels/Python.lean` does not import the rebuild. §0.1
principle I forbids swapping a validated definition for an unvalidated one; the
gate below is what would eventually earn that right, and `twinAgrees` (§8.5) is
what would earn it in a theorem.

---

## §0 THE VERDICT SO FAR, first

**The architecture is validated, the instrument is built, and the interpreter is
a slice that agrees with the trunk everywhere it reaches.** 846 of 1394 rows at
byte-identical parity, 548 rows refused with a "not yet" naming their arm, and
**zero divergences** — no row where the two interpreters disagree for any reason
other than the rebuild not having been written that far.

| | measured |
|---|---|
| substrate + iso + zooms | **landed, proved**, `#print axioms` clean |
| the fuel ruling | **taken, and it is a NEW design** — see §2 |
| kernel reducibility of the rebuilt interpreter | **holds** — 9 `#guard`s, incl. a `while` through the fueled knot |
| the shim | **landed** — one runner flag, three harnesses, **zero harness forks** |
| the `@[spec]` layer | **17 triples**, output-determined and state-framed, axioms clean |
| `mvcgen` on the REBUILT interpreter | **two gates close** (~11 s, ~10 s); the second closes the pilot's own fidelity gap. The full four-deep gate does **not** close at 8M heartbeats — §3.1 prices that |
| the trunk's baseline (re-measured, not quoted) | diff_test **1394 / 0 failed / 118 whitelisted / 1276 matched**; script_corpus **65 / 0 failed / 50 matched / 15 loud** |
| run 1 — the first parity run | 846 / 1394 (60.7 %), 548 frontier in 19 arms, zero divergences |
| run 2 — after eleven buckets | 1374 / 1394 (98.6 %), 10 frontier in 4 arms, 10 divergences — all ONE missing arm (§5.3.1) |
| **run 3 — closed-function surface** | **1394 / 1394 (100.0 %), zero frontier, zero divergences** |
| the SCRIPT surface | found three arms the closed-function corpus cannot reach (§5.3.3); frontier now empty on both |
| memory at fuel 10⁶ | **flat and equal to the trunk** after the lazy-knot fix (§5.3.2) |

**The frontier is now EMPTY on both surfaces**: all 22 names in
`isBuiltinName`'s implemented set are handled, and `CallPlan.notYetArm` is
declared but never constructed — the remaining `notYet` sites are unreachable
defensive arms. **Acceptance is still not claimed here**: it requires both
corpora green in the SAME run, and §5.3.3 is the reason that phrasing is not
pedantry.

The three things a later session inherits and does not have to invent: the fuel
architecture, the gate command, and a frontier that is **bucketed by arm** rather
than being one number.

---

## §1 THE LAYOUT, AND THE BOUNDARY

    LeanModels/Python/Monadic.lean             -- the umbrella; ONLY `Main.lean` imports it
    LeanModels/Python/Monadic/Substrate.lean   -- SemM, the Run iso, named refusals, the zooms
    LeanModels/Python/Monadic/Prim.lean        -- the @[spec]-shaped primitives, and `Kont`
    LeanModels/Python/Monadic/Eval.lean        -- the interpreter, the fueled knot, the boundary
    LeanModels/Python/Monadic/Spec.lean        -- 17 @[spec] triples + the demonstration gates
    harness/monadic_gate.py                    -- the gate: parity, frontier-by-arm, divergences

Namespace `LeanModels.Python.Monadic`.

**`Monadic/` is a PRESENTATION sibling, not a VERSION sibling, and the
distinction is load-bearing** because §1.1's convention reads
`LeanModels/<Lang>/<Ver>/` as an edition. This directory claims the **same**
edition as the trunk (CPython 3.9), the same oracle, the same corpus and the same
authority; what differs is how the semantics is *written*. When the Python lane
earns `LeanModels/Python/Py39/`, that is an orthogonal axis — a monadic Py311
would be `Monadic/`'s own sibling, not this one's parent. The name was chosen so
no reader can mistake it for an edition token.

**The trunk is shared to the maximum.** Every pure worker of `Semantics.lean` is
REUSED verbatim: `evalBinOp`, `evalUnaryOpH`, `indexValH`, `sliceVal`, `truthyH`,
`assignToH`, `unpackSeq`, `unpackStoreH`, `heapStore`, `heapAttrStore`,
`attrReadResult`, `ntupleAttr`, `strOfArgs`, `strOfValH`, `rangeMake`,
`rangeVals`, `strCharVals`, `sortedValH`, `extremumValH`, `absVal`,
`intCastVal`, `ordVal`, `chrVal`, `lenValH`, `dictBuild`, `evalCompareOpH`,
`mkCallEnv`, `arityOk`, `arityErrorMsg`, `paramArity`, `findFunction`,
`findClass`, `findNamedTuple`, `lookupG`, `moduleGlobals`, `isBuiltinName`,
`isPyBuiltinName`, `isModuleDunder`, `unmodelledBuiltinMsg`. **The rebuild owns
the CONTROL; the trunk owns the arithmetic.** A second `evalBinOp` would be a
second thing to keep true, and the thin-siblings instinct applies to code as much
as to editions.

Every **refusal string** is likewise the trunk's, copied verbatim, because the
refusal messages *are* the specification — `script_corpus.py` and
`refusal_census.py` compare them.

---

## §2 THE FUEL RULING — decided BEFORE the interpreter was written

§3.4 makes this a founding-checklist item. The measurement behind the decision is
the pilot's: fuel as a monad **layer** does not typecheck; fuel as an explicit
**argument** (the trunk's shape) is definable but `mvcgen` returns the goal
unchanged after 1 m 31 s at a symbolic fuel; only the **fuel-free** fragment is
one `mvcgen` walks.

**THE DECISION: split the interpreter at the fuel boundary.**

| half | recursion | measure |
|---|---|---|
| `evalOpen` / `execOpen` (+ list/chain companions) | **fuel-free**, open | `termination_by structural` on `Expr` / `Stmt` |
| `kont m : Nat → Kont` | the fueled knot | `termination_by structural` on **fuel** |

`Kont` (`Prim.lean`) is the **defunctionalized fuel boundary**: the record of the
operations whose recursion is bounded by fuel rather than by syntax — `call`,
`whileLoop`, `forSeq`, `forList`, and the generator steppers. The fuel-free half
takes it as a parameter, which is exactly what makes it structural.

**Two structural blocks instead of one, and BOTH stay kernel-reducible.** That
is the property everything rests on and it is **measured, not assumed**: nine
`#guard`s in `Eval.lean` §5 decide real runs — arithmetic, a retained-state
`NameError`, `and` answering its deciding operand, a short-circuiting comparison
chain, an allocating list display, an assignment, a `while` loop summing 1..4
through the fueled knot, a fuel-exhausted `while` timing out, and `print`
appending a chunk. `#guard` is `Decidable.decide` plus `rfl`, so a well-founded
fallback fails them outright. Well-founded recursion on a lexicographic
`(fuel, sizeOf e)` was the obvious alternative and is **rejected** for that
reason — it is the mergeSort trap, and it would silently delete every kernel
`rfl` in the tier.

**A recorded non-finding, because it wasted time once.** `#print axioms` on the
rebuilt `evalOpen` reports `[propext, Classical.choice, Quot.sound]` — and so
does the **trunk's** `evalExpr`. `Classical.choice` in the axiom print is **not**
a well-founded-recursion tell here; the operational test is `#guard`/`rfl`, and
that is the one to run.

### 2.1 THE ONE DELIBERATE DIVERGENCE, and its argument

The trunk decrements fuel at **every** expression and statement node. The rebuild
spends fuel only at the non-structural points. Stated exactly:

> At any fixed `F`, the rebuild is **at least as decisive** as the trunk: every
> run the trunk decides at `F`, the rebuild decides at `F`, with the same value.
> Only `.timeout` moves, and it moves in one direction.

Three consequences, and they are why this is a recorded decision rather than a
hidden optimization:

1. **The refusal surface is UNCHANGED.** `.unsupported` is fuel-independent by
   the loudness doctrine. `refusal_census.py` parity is a claim about exactly
   this, and the ruling leaves it untouched by construction — never wider, never
   narrower.
2. **Under the ∃-threshold form the two are EQUIVALENT.** Every landed theorem is
   `∃ t, ∀ F ≥ t, …`; a claim holding of the trunk at threshold `t` holds of the
   rebuild at `t`. The inequality points the safe way.
3. **It is observable, so it is measured.** A row where the trunk answers
   `.timeout` and the rebuild answers a value is a genuine difference. The corpus
   contains none — the trunk is 0-failed at its default fuel, so it never times
   out there — but the gate reports one if it ever appears.

### 2.2 THE ONE ARCHITECTURAL DEBT — found, priced, PAID

CPython's `BUILD_MAP` evaluates k₁, v₁, k₂, v₂, …, so a dict display must walk
**two parallel expression lists in lockstep**. The trunk does that freely because
its measure is fuel. A structural measure cannot: whichever list is chosen, the
other list's head is not a subterm of it, and Lean answers

    failed to eliminate recursive application
      evalOpen K m v

(bisected to a two-parallel-list member; every other member of the block is fine).
Interleaving first would preserve the order but the interleaving is a function
APPLICATION, not a projection of the node, so it is not a subterm either.

**Three exits were priced and the third is taken.**

| exit | price | verdict |
|---|---|---|
| a paired AST field, `Array (Expr × Expr)` on `.dict` | edits `Ast.lean`, `Json.lean`, the trunk's `evalExpr` and four walkers — **it changes the TRUNK**, which this rebuild may not do | REJECTED |
| one well-founded member inside the block | a mutual block shares ONE strategy, so it makes the WHOLE block well-founded and costs every kernel `rfl` — the mergeSort trap | REJECTED |
| **split the block: route the walk through `Kont`** | **one `Kont` field, one ordinary structural definition, one fuel level** | **TAKEN** |

`evalOpen`'s `.dict` arm calls `K.dictItems` — a record field, so from the block's
point of view it is not a recursive call at all. The walk (`dictItemsAt`) is
defined BELOW the block, where `evalOpen` is an ordinary constant, so its own
recursion is plainly structural on its own first list and nothing constrains the
second.

**The price, exactly: one fuel level per dict display**, because `kont m (fuel+1)`
must build the field from `kont m fuel`. That is **precisely what the trunk
charges** (`evalExpr m (fuel+1)` on a `.dict` calls `evalDictItems m fuel`), so
this arm is the one place the rebuild's fuel accounting is *identical* to the
trunk's rather than more generous. Nothing else is given up — the walk stays
kernel-reducible like the rest of the file.

**The generalisable lesson**, and it is why `Kont` was worth having before it was
needed: *the fuel record is not only a fuel boundary. It is a **recursion-knot
boundary**, and anything a structural measure cannot express can be cut out of
the block through it at the cost of one field.* A second instance of the same
obstacle was avoided by restructuring instead — `.boolOp` originally destructured
`values.toList` at the call site (the trunk's shape) and had to pass the list
WHOLE, since destructuring severs the subterm chain.

### 2.3 THE FREE-SCRUTINEE DISCIPLINE, earning its keep twice

The tier records three times that referent dispatch must fork on a **pure plan**
(`attrCallPlan`, `strCallPlan`, `genPlan`) because a `match` nested under the
receiver's binder is invisible to `cases`/`rw`. The rebuild's `callNamePlan`
follows it — and here it is also a **termination** requirement: a mutual member
taking the SAME `List Expr` as its caller is not a decrease, so folding the whole
call arm into the recursive block does not elaborate. The plan additionally makes
**when the arguments evaluate** explicit, which is observable: the trunk refuses
`input()`, module dunders, unmodelled builtins and the tail `NameError` *before*
touching the arguments, and evaluates them first everywhere else — including on
the paths that then raise `TypeError: … is not callable`. `preRefuse` /
`preNameError` are that split.

---

## §3 THE SUBSTRATE — now in `LeanModels/Core/`, and shared

**THE STACK WAS EXTRACTED TO THE FAMILY** (`LeanModels/Core/Outcome.lean`),
because a second lane arrived needing it. §3.8 lists three candidates for the
"move `Run` / land `SemM`" trigger and says whichever lands first fires it; the
SystemVerilog lane blocked on the canonical spelling rather than defining an
SV-local stack, which is §3.8's rule — *"a second interpreter landing with its own
copy is a defect, not a design"* — working as intended.

In `LeanModels/Core/Outcome.lean` (language-neutral) and then
`LeanModels/Python/Monadic/Substrate.lean` (Python's instantiation):

```lean
-- (illustrative — the two files' shapes, quoted together)
inductive Loud where | timeout | unsupported (msg : String)
abbrev Halt := Except Loud
abbrev SemM (W ρ : Type) := ExceptT ρ (StateT W Halt)
abbrev SemPS (W ρ : Type) : PostShape := .except ρ (.arg W (.except Loud .pure))

abbrev PyM (σ : Type) := SemM σ PyErr
abbrev SemF := PyM FrameState        -- statements and expressions
abbrev SemW := PyM World             -- a nested call
```

The naming is the family doc's own: `Loud` is the state-DISCARDING outcome,
`Halt` the base monad it lives in. The two failure channels are not
interchangeable — `ρ` is the LANGUAGE's raise and retains state; `Loud` is the
MODEL giving up and discards it, and is never a claim about the program.

**What did NOT move: `Run`.** §3.8's destination clause also wants Python's `Run`
in Core with `Runtime.lean` re-exporting. That half is deliberately excluded, and
the reason is measured: `Run` lives in `LeanModels/Python/Runtime.lean`, under the
umbrella that **65 files under `Examples/` import**, and moving it re-founds an
import graph the sunfish campaign is mid-flight in. **The substance of the rule is
satisfied anyway** — the family has ONE stack, in one file, and `Run` is *proved*
to be a view of it. A lane arriving by either route finds one artifact. Moving the
datatype is an erosion item, payable when those files are being touched anyway.

**The landing was measured before it was made:** all nine new `LeanModels.*`
names (`Loud`, `Halt`, `SemM`, `SemPS`, `refuse`, `exhausted`, `raiseIn`,
`zoomIn`, `zoomOut`) were checked against every declaration in `LeanModels/` and
`Examples/` — **zero collisions**, so the landing is additive and cannot break a
consumer.

The layer order is the pilot's **correction** to §3.4's first draft and it is
load-bearing: `StateT` outside `ExceptT` discards the state on a raise, and the
tier's `.exn` **retains** it. `Halt` is deliberately a named `inductive` rather
than the pilot's `Unit ⊕ String` — a refusal is a first-class notion here. **It
is a `LeanModels/Core/` candidate** once a second tier wants it; recorded, not
moved (§3.8's trigger discipline).

`Run σ α` **is** this stack, proved both ways (`toRun_ofRun`, `ofRun_toRun`), and
the two frame/world adapters are proved to agree with the trunk's own
(`inFrame_toRun` = `Run.withLocals`, `inWorld_toRun` = `Run.toWorld`). So the
rebuild's call boundary is the *same* boundary, not a similar one — which is what
lets `callInMono` have `callIn`'s type and the harnesses compare them directly.

### 3.1 THE PRICE OF FIDELITY, measured — and it is not free

The pilot's shallow twin closed GATE 3's **full four-deep** shape
(`score = pst[p][j] - pst[p][i]`) with an `mvcgen` step of **568 ms**. The same
statement against the **faithful** interpreter was attempted here and **does not
close at 8 000 000 heartbeats** (~14 minutes, `timeout at whnf`). Two smaller
gates against the faithful interpreter *do* close — `assign_binop_M` in ~11 s and
`subscript_global_M` (the one carrying the static-globals-fold premise the twin
dropped) in ~10 s.

**That gap IS the fidelity gap, priced.** What the twin's `resolve` left out —
the nine-step resolution chain with its `findFunction`/`findClass`/namedtuple/
builtin/dunder forks, and `execOpen`'s five-way assignment target fork — is
exactly what `mvcgen` must now split on, and the splits multiply through a
four-deep expression tree. So the pilot's headline number was measured on a
program the differential gate does not run, and the honest version of it is
larger by more than three orders of magnitude.

This is **not** a reason to keep a shallow twin — a twin is a second thing to
keep true, and §8.5's `twinAgrees` is the bill for it. The prescription was *more
`@[spec]` lemmas at the `evalOpen`-arm level, not fewer premises in the
statement*.

**THE PRESCRIPTION WAS THEN TESTED, AND IT DOES NOT SUFFICE — for a nameable
reason.** Two arm-level lemmas land (`evalOpen_name_local`, `evalOpen_const`).
The one that would actually bind — `evalOpen_name_global`, the static-globals-fold
arm, which GATE 3 exercises twice for `pst` — **cannot be stated at all**:
`mvcgen` splits the inner `match lookupG …` into one verification condition per
branch **without retaining the discriminant equation**, so the two unreachable
branches arrive as bare `⊢ False` with nothing available to refute them. Feeding
the hypothesis to `mvcgen`'s simp set does not help; the split has already
happened. Re-measured with both landed lemmas in the registry: the four-deep gate
**still does not close, at 4M heartbeats / ~10 minutes**.

So the blocker is not lemma COUNT — it is a specific tactic limitation, which is
a far more useful thing to know than "needs more altitude". **It is the third
`mvcgen` defect this lane has recorded**, after the `Spec.throw_Except`
metavariable bug and the no-op `mvcgen?`, and it sharpens the standing risk note:
a tactic whose authors call it experimental is being asked to carry a family-wide
substrate, and the family should expect to work around it by shape rather than by
volume.

**AND `grind` DOES NOT FIX IT EITHER — measured, and the failure separates two
things cleanly.** With `grind` wired into `mvcgen_trivial_extensible` (which
deletes the closing scripts of both landed gates outright), the four-deep gate
**still** dies at 4M heartbeats with `timeout at whnf`. That is not a discharge
failure: `grind`'s job is to close verification conditions once they exist, and
this run never gets that far. The blowup is inside `mvcgen`'s **own splitting**,
before any VC is handed to any discharge tactic.

So the two results do not compete, they partition the problem:

| stage | tool | status |
|---|---|---|
| GENERATING the VCs | `mvcgen`'s split | **the blocker** — cannot be helped from outside, and the one altitude lemma that would shrink it is unstateable |
| DISCHARGING them | `mvcgen_trivial` → `grind` | **solved** — closing scripts deleted on both landed gates |

The practical rule this yields, and it is the one to carry into other tiers:
**`grind` buys you the bottom of the pipeline for free; the top still has to be
bought with SHAPE** — smaller statements, or arm lemmas stated in a form
`mvcgen`'s splitter can actually consume.

### 3.2 A TRAP IN THE `#print axioms` LAW, worth recording

The failed `value_scores_M` printed

    'value_scores_M' does not depend on any axioms

which is **the cleanest possible axiom line and it means the opposite**: the
declaration errored, and the constant Lean left behind carries no axioms because
it carries no proof. `#print axioms` on a file with errors is not evidence of
anything. **Read the errors first; an axiom print is only meaningful in a file
that elaborated clean.** Every axiom line quoted in this document comes from a
run with zero errors, and the two landed gates were re-checked that way.

### 3.3 The pilot's four zero-cost laws, all adopted:

1. **Named refusals, never a bare polymorphic `throw`** — `refuse`, `exhausted`,
   `raisePy`, `liftRes`, `liftRunAt`, plus `notYet` (§4).
2. **Output-determined specs** — every `@[spec]` lemma binds its answer with the
   result binder.
3. **`Triple` does not frame the state** — read-only primitives pin the
   pre-state.
4. **`@[spec]` is the altitude registry** — primitives behind spec lemmas, never
   unfolded into the walker.

---

## §4 THE FRONTIER IS SPELLED DIFFERENTLY FROM THE TIER'S

An arm the rebuild has not yet transliterated refuses through `notYet`, whose
message carries the prefix

    monadic-rebuild: arm not yet transliterated: <arm>

**This is never a claim about Python.** A trunk refusal is a statement about the
language; a `notYet` is a statement about the rebuild's progress. They are
spelled differently so no report can conflate them, and so the gate is a
**burn-down list bucketed by arm** rather than a single number. The same
distinction was kept at the runner while the script executor did not exist:
`--monadic --script` exited **2** (a capability error), never 3 (the loud
semantic code), because answering 3 would have scored a missing module as a tier
boundary. **That exit is now gone — the script executor is rebuilt** (§6.2), so
both surfaces answer for real.

---

## §5 THE GATE

    # trunk baseline
    python3 harness/diff_test.py --no-build --runner ./.lake/build/bin/leanmodels-run
    python3 harness/script_corpus.py --no-build --runner ./.lake/build/bin/leanmodels-run

    # the rebuild, same corpus, same oracle, same canonical JSON
    python3 harness/diff_test.py --no-build --monadic \
        --runner ./.lake/build/bin/leanmodels-run

**No harness is forked.** All three already accept `--runner`; `--monadic` is a
one-line addition to each that appends the flag, and the runner's `splitMonadic`
strips it before mode dispatch. Each harness now also PRINTS which interpreter it
measured, for the same reason it prints the oracle version.

**Acceptance, unchanged:** diff_test 1394 / 0 failed with the same 118/1276
match/whitelist split, script_corpus 65 / 0 failed with the same 50/15 split, and
`refusal_census.py` the same MATCH/REFUSE per witness.

### 5.1 `diff_test --monadic` IS NOT THE GATE, and the reason is a real defect

`harness/diff_test.py` compares an `expect: "unsupported"` row **by status
alone** — `lean.get("status") == "unsupported"` — which is exactly right for its
own job (the whitelist records that the *tier* refuses, not which words it uses)
and **wrong for measuring the rebuild**: a `notYet` landing on a whitelisted row
scores WHITELISTED. That is a **false pass**, and it can flatter the rebuild by
up to the whole 118-row whitelist.

So the gate proper is **`harness/monadic_gate.py`**, which runs the corpus
through **both** interpreters and compares them to each other, message included:

    python3 harness/monadic_gate.py --no-build \
        --runner ./.lake/build/bin/leanmodels-run --json /tmp/gate.json

It reports three numbers that cannot be conflated — **PARITY** (rows where the
two answer identically), **FRONTIER** (rows the rebuild refuses with a
`monadic-rebuild:` message, bucketed by arm and ranked), and **DIVERGENCES**
(rows where they disagree and the rebuild is *not* saying "not yet"). Only the
third is alarming, and each is printed with CPython's answer beside both so it
can be adjudicated on the spot.

One bug was found in this tool by reading before it ever ran: it imports
`diff_test`, which **re-execs itself** into the pinned 3.9 oracle at import time,
so the import would have handed the process to `diff_test.py` and silently
abandoned the gate. `monadic_gate.py` therefore does the same re-exec *first*.
Invisible on a 3.9 box, fatal anywhere else.

### 5.2 PRE-REGISTERED, so it can be wrong

Written **before** the first run, because a prediction recorded afterwards is a
story:

* **PARITY: 30–45 %** of 1394 rows. The slice covers arithmetic, control flow,
  the full name-resolution chain, all five assignment target shapes, module-level
  calls, and twelve builtins; it does not cover the dict/class/namedtuple/
  generator/closure tiers, which is where most of the corpus's labs live.
* **TOP BUCKET: method calls** (`call: method call '.…'`), because `.get`,
  `.append`, `.pop` and the flattened `Class.method` dispatch run through
  `execAttrCall`, and that is one arm carrying many rows.
* **DIVERGENCES: 0.** This is the real prediction and the one worth being wrong
  about. Every rebuilt arm was transliterated from the trunk arm-for-arm and
  message-for-message, so a divergence means the transliteration slipped — or
  the trunk has a bug the rebuild does not. **Either way it is a finding**, and
  the gate prints CPython beside both so it can be adjudicated where it is
  found.

### 5.3 THE FIRST PARITY RUN — MEASURED

`lake build leanmodels-run` **green** (26 jobs). Oracle CPython 3.9.19.

```
MONADIC REBUILD GATE  (harness/monadic_gate.py)
------------------------------------------------------------------------------
rows                      1394
PARITY with the trunk      846  (60.7%)
frontier (`notYet`)        548  in 19 arms
DIVERGENCES                  0
------------------------------------------------------------------------------
THE BURN-DOWN LIST — rows blocked, by arm:
    111  call: class instantiation …
     88  call: generator function (H4)
     78  call: method call …
     53  expression: dict display (parallel key/value walk)
     36  call: keyword arguments (H6)
     34  statement: nested def / closure (H7)
     33  call: namedtuple construction …
     24  statement: try/except (exceptions tier)
     22  builtin: enumerate()
     21  statement: assert
     16  builtin: set()
     11  statement: del
      5  statement: raise (exceptions tier)
      5  builtin: count()
      4  builtin: all()
      2  builtin: next()
      2  builtin: any()
      2  call: statically-poisoned module binding …
      1  builtin: max() over a heap referent
```

Alongside: `script_corpus --monadic` **65 / 65 failed**, which is the expected
and correct reading — the script executor is not rebuilt, so the runner exits 2
(capability) on every row and the corpus scores every one a mismatch. It will
stay 65/65 until `runScript` exists; it is not a semantic result and the exit
code is what keeps it from being mistaken for one.

`refusal_census --whitelist` : **118 rows in 46 classes, 0 drifts — on BOTH
interpreters.** So refusal-surface parity holds *at the verdict level*: every
whitelisted row still refuses under the rebuild. See §5.5 for what that does and
does not claim.

### 5.3.1 RUN 2 — 98.6 %, and the ten divergences were ONE bug

After eleven buckets landed (dict displays, class instantiation, namedtuples,
method calls, generators, closures, keyword arguments, try/except, assert, del,
raise, set, any/all):

```
rows                      1394
PARITY with the trunk     1374  (98.6%)
frontier (`notYet`)         10  in 4 arms
DIVERGENCES                 10   <-- FINDINGS
```

**All ten divergences were the same missing arm: the TRACE CLOCK.** The rebuild
refused `time.time()` as an out-of-G1-tier module value where the trunk pops the
next reading of the world's trace. That is a refusal surface **wider** than the
trunk's — the one direction §2.1 forbids — and it is worth being precise about
why the gate caught it rather than the frontier report:

> the arm reused a **trunk-shaped** refusal message, so it did *not* carry the
> `monadic-rebuild:` prefix and could not be bucketed as "not yet". It could only
> appear as a DIVERGENCE. **A gate that compared statuses would have scored all
> ten as agreement** — both sides answer `unsupported` on three of the rows —
> and the remaining seven would have read as ordinary missing coverage.

That is §5.5's instrument argument, paid off on a real bug rather than in
principle. It also sharpens the `notYet` discipline: a genuinely-not-yet arm must
say so **in its message**, and an arm that borrows a trunk message is claiming
the trunk's semantics for itself.

Fixed in the same session, along with the four remaining frontier arms —
`max`/`min` over a heap referent (with the `moduleGenFree` guard that keeps them
inside the heap-free fragment), `sorted` over a generator, and statically-poisoned
module bindings consulting the live view.

### 5.3.2 THE LAZY-KNOT DEFECT — correct answers, catastrophic constant

Found by the gate STALLING, not by reading, and it is the sharpest cost lesson
this rebuild produced.

The obvious spelling of a defunctionalized knot binds the successor level once:

```lean
-- (illustrative — the WRONG spelling)
| fuel + 1 => let K := kont m fuel
              { call := fun … => … K …, … }
```

`let` is **strict**. So constructing `kont m F` forces the entire chain down to
`0` **before a single statement runs** — O(F) work and O(F) stack *per entry*.

**It survived three green gate runs**, because the closed-function surface runs
at fuel 10 000, where the cost is merely wasteful. Script mode runs at
**1 000 000**, and there it stalls outright: a runner pinned at ~0 % CPU having
executed nothing, and (on the machine's shared load) growing to gigabytes.

The fix is one property — every field takes its successor level *inside* its own
lambda, so construction is O(1) and the chain is forced exactly as deep as the
run goes.

**The generalisable warning, for any tier adopting this shape.** The trunk gets
this laziness FOR FREE by matching `fuel` inside each function; only the levels
actually reached are ever built. **A defunctionalized knot has to ask for it, and
asking is invisible**: the strict version compiles, type-checks, passes every
`#guard` (they all run at low fuel), and is wrong *only in cost*. Correct
answers, catastrophic constant — a failure mode no correctness gate detects.
`Kont`'s three earlier jobs all worked at low fuel and hid it.

**Measured after the fix**, same script, both interpreters:

| fuel | trunk | monadic |
|---|---|---|
| 1 000 | 37 MB | 37 MB |
| 10 000 | 37 MB | 36 MB |
| 1 000 000 | 36 MB | 36 MB |

Flat across three orders of magnitude and identical to the trunk. **A predicted
second defect — that the run itself retained the world/trace unboundedly — DOES
NOT EXIST**; the O(fuel) construction cost was the whole story. Recorded because
the prediction was made in writing first and the measurement refuted it.

### 5.3.3 WHY ACCEPTANCE IS BOTH CORPORA, demonstrated rather than argued

The closed-function gate read **1394/1394, 100.0 %, zero frontier, zero
divergences** — while **three arms were still `notYet`**.

They were invisible there because `harness/cases.json` cannot contain them: a
from-import and a positional `dict()` are script-shaped constructs, and a live
module binding only exists once a top level has run. Six script rows found them
immediately.

> **A gate is blind to whatever its corpus does not contain, and "zero frontier"
> means zero frontier ON THIS CORPUS.**

This is the same class of error as §5.5's instrument findings, one level up: there
the *comparison* was too weak, here the *corpus* was. Both were caught by adding
an independent instrument rather than by inspecting the first one harder — which
is the argument for keeping the acceptance gate at both corpora permanently, even
once both are green.

### 5.4 THE PRE-REGISTRATION SCORECARD — one of three

Scored against §5.2, written before the run.

| prediction | measured | verdict |
|---|---|---|
| PARITY 30–45 % | **60.7 %** | **MISS** — too pessimistic by ~16 points |
| top bucket = method calls | **class instantiation, 111**; method calls **third**, 78 | **MISS** |
| DIVERGENCES 0 | **0** | **HIT** |

**The two misses are cheap and the hit is the expensive one.** Parity and bucket
order only rank the next session's work — and the ranking is now measured rather
than guessed, which is the whole point of writing the buckets down. **Zero
divergences is the claim that the transliteration is faithful**: 846 rows on
which the rebuilt interpreter and the trunk return byte-identical canonical JSON,
including the exception classes and the verbatim refusal messages, and not one
row where they disagree for any reason other than the rebuild saying "not yet".

The parity miss has an identifiable cause worth keeping: `iterValues` was added
late (§6), and `sum`/`tuple`/`list` reach further into the corpus than expected
because so many rows are sequence arithmetic over already-supported values.

### 5.5 THREE INSTRUMENTS, TWO OF THEM BLIND — measured, not argued

**`diff_test --monadic` over-reports by exactly 56 rows.** It answers
902 "not failed" (784 matched + 118 whitelisted) where the gate finds 846 rows of
real parity. The 56-row gap is precisely the false pass predicted in §5.1: a
`notYet` landing on an `expect: "unsupported"` row, which diff_test scores
WHITELISTED because it compares those rows **by status alone**. Predicted from
reading the source, then measured.

**`refusal_census --whitelist` exits 0 on both interpreters while 66 lines of its
own output differ.** Its job is drift against a RECORDED class table, not parity
against the trunk, so a `monadic-rebuild:` refusal satisfies it silently. What
its 0-drift result legitimately claims is that every whitelisted row still
**refuses** — verdict-level parity, which matters and which held. What it cannot
see is *which* refusal, and the whole point of the rebuild's separate message
prefix is that those are different questions.

**A census diff is not a row diff, and one line in it looked alarming.** The
census prints one representative witness and one message per class; when other
rows in a class change message the representative moves, so `del_lab::read_after`
appeared to change from a `del` refusal to a static-locals refusal. Run directly
through both interpreters that row returns the **same message on both**. The gate
was right; the display was misleading. Row-level comparison is
`monadic_gate.py`'s job and nothing else's.

**Net: neither existing harness can score this rebuild on its own.** That is why
`harness/monadic_gate.py` exists, and it is the number to quote.

---

## §6 WHAT IS REBUILT, ARM BY ARM

**Expressions** — `.constant`, `.name` (the full nine-step resolution chain
verbatim, including both live-view consults), `.namedExpr`, `.binOp`,
`.unaryOp`, `.boolOp`, `.compare`, `.list`, `.tuple`, `.subscript`,
`.attribute`, `.ifExp`, `.slice`, `.genExp` (refusal), `.unsupported`
(refusal). `.call` on a NAME callee through `callNamePlan`, with **15 of the 22
builtins** `isBuiltinName` claims: `len`, `abs`, `int`, `ord`, `chr`, `str`,
`print`, `range`, `max`, `min`, `sorted`, `input`, `sum`, `tuple`, `list`.

The last three share `iterValues`, and that consolidation is worth naming. The
trunk spells the same eight-arm iterable dispatch out **three times**, because
its arms differ only in the builtin NAME its refusals interpolate and in one
generator policy. Here it is one function taking both as parameters, with the
trunk's messages verbatim — the maximal-trunk instinct applied to the rebuild's
own code. The generator policy is the `moduleGenFree` fork: `sum` and `tuple`
stay INSIDE the heap-free fragment and must refuse a generator when the module
owns no generator defs, while `list` ALLOCATES — CPython's `list(x)` is never an
alias — which is precisely what lets its generator arm drain unguarded.

**Statements** — `.ret`, `.assign` (all five target shapes: subscript,
attribute, all-name tuple, attribute-bearing tuple, generic — with the trunk's
evaluation ORDER), `.augAssign` (name and attribute, with the load-before-value
order), `.whileLoop`, `.forStmt` (all six iterable dispatches), `.ifStmt`,
`.exprStmt`, `.pass`, `.brk`, `.cont`, `.raiseStmt`, `.assertStmt`, `.delStmt`,
`.tryStmt`, `.yieldStmt`/`.yieldFromStmt` (refusals), `.unsupported` (refusal).
`execOpenList` stops at the first non-`next` flow.

**Method calls, all three receivers** — heap referents through
`attrCallPlan`/`applyAttrPlan` (instance methods, `dict.get`/`.clear`,
`list.append`/`.pop`/`.insert`), namedtuple subclasses through `ntupleCallPlan`,
and strings through `strCallPlan`/`applyStrMethod`. Each forks on the trunk's own
pure plan, and each preserves WHEN the arguments evaluate: a missing attribute,
an instance ATTRIBUTE in call position, a plan refusal and a dangling reference
all decide **before** any argument runs.

**Class instantiation and namedtuple construction** — `Obj.instance` allocation
plus `__init__` through the ordinary call path with `self` as an ordinary first
argument; the value-like SUBCLASS (`class Position(namedtuple(…))`) collapsing
into the same immediate-value arm as a plain namedtuple. All seven admission
guards fire before the arguments, as the trunk's do, and the no-`__init__` arity
error fires **before** the allocation so the failing run's world is the caller's
untouched.

**The knot** — `callInM` (guard order: parameter features, static-locals rule,
arity, generator fork), `whileLoop`, `forSeq`, `forList` (the LIVE index cursor,
referent re-read every step, with the trunk's six referent arms), `dictItems`
(§2.2), and the whole GENERATOR engine.

**Generators (H4), complete.** `Obj.generator` carries a DEFUNCTIONALIZED
continuation — a stack of `GenFrame`s, each a structural suffix of the body plus
that loop's residual state — so the frame stack replaces the Lean call stack and
`yield` is admitted in statement position. `stepIter`, `execGen`, `forGen`,
`drainIter` and `anyAllIter` are all ORDINARY non-recursive functions of `K`:
every continuation step goes through a `Kont` field, i.e. one fuel level down,
which is precisely the trunk's `execGen m fuel` recursion re-expressed. **That is
§2.2's block-split trick reused on a genuinely fuel-bounded knot** rather than a
structural one — the same mechanism paying twice.

Two details are worth naming because they are observable. An exception
propagating out of a resume **closes** the generator (CPython marks the frame
finished, so every later `next()` is exhaustion) — never `suspended`, never stuck
`running`; in the trunk that needs a bespoke `Run.bindE` combinator, and here it
is `tryCatch`. And `any`/`all` over a generator short-circuit and leave it
**suspended**, so they are routed away from the shared drain: a later `next()`
sees the partial consumption, and draining instead would be a wrong answer about
state rather than a missing feature.

**Closures (H7).** `defStmt` snapshots the captures, allocates `Obj.closure` and
binds the name; the call path resolves the cell directory through `cellsFor`
against the **caller's** locals — threaded explicitly through `Kont.callClo`,
because the world-typed field alone would have resolved captures against an empty
frame.

### 6.2 THE SCRIPT EXECUTOR — and 530 of its 893 lines were never rebuilt

`runScript` executes EVERY top-level statement from an EMPTY world and PUBLISHES
the frame's locals into `World.globals` after each one, because a module frame's
locals ARE its globals. That per-statement publish is the whole reason the script
layer is not just `execOpenList`: every compound statement needs a CONTROL SHELL
that runs its body through the publishing loop instead of delegating the
statement wholesale.

**The admission machinery is reused WHOLE, and that is most of the file.**
`classesCreationPure`, `defsBoundBefore`, `scriptFlushCoherent`, `scriptView`,
`publishScriptGlobals`, `scriptRebindMsg`, `benignImportBinds`,
`benignImportNames`, `dunderShaped` — roughly **530 of the trunk's 893 script
lines** — are pure, and are imported rather than rebuilt. The rebuild owns the
~320 lines of CONTROL, exactly as it owns `evalOpen`'s control and none of
`evalBinOp`'s arithmetic. That ratio is the maximal-trunk principle showing up as
a number.

**A SECOND knot record, `SKont`.** Every shell is fuel-recursive — a `while`
re-tests, a cursor re-reads — so none can be a member of a structural block. The
device is the one `Kont` already is: each shell is an ordinary non-recursive
function of `S`, and every loop step goes through a field, i.e. one fuel level
down. That is the trunk's `execScriptStmts m fuel` recursion re-expressed, and it
is the **fourth** distinct job the recursion-knot boundary has done.

### 6.1 THE EXCEPTIONS TIER IS WHERE THE SUBSTRATE PAYS FOR ITSELF

`try`/`except` is the arm that would have been fiddliest by hand and is close to
free here. `tryCatch` on `ExceptT PyErr …` catches **exactly** the language's
raise and lets `Loud` — the model giving up — propagate untouched, which is the
trunk's hand-written three-way fork over `.exn` / `.timeout` / `.unsupported`
obtained from the type. And the RETAINED-STATE covenant — the handler runs from
the state the raise happened in, with no rollback — **is** the layer order,
because `StateT` sits inside `ExceptT`.

Neither property is coded in the arm. Both are consequences of the stack the
pilot's `rfl` picked, which is the strongest available argument that the layer
order was worth getting right.

## §6.5 THE BUILD, AND WHY `lake build leanmodels-run` IS THE WHOLE GATE

Measured: **`Main.lean` is the only file in the tree that imports the rebuild.**
Nothing under `Examples/`, nothing under `LeanModels/` outside `Monadic/` — so
`lake build leanmodels-run` compiles 100 % of this change's blast radius, and a
full `lake build` would only re-verify other lanes' work.

That distinction mattered on this clone: rebasing onto master brought a
38-line change to `LeanModels/Python/DictCalc.lean`, which sits under the
`LeanModels` umbrella that **65 files under `Examples/` import** — including the
expensive sunfish proofs. A full build here is hours of re-proving that has
nothing to do with the rebuild, and under the machine-wide build lock those
hours are charged to eleven other lanes. Building the runner is both the honest
gate and the neighbourly one.

**And the lock is expensive, so the constructs that could waste it were checked
first**, in a dependency-free scratch file with no lock taken: the `if mono then
Monadic.callInMono else callIn` unification (they share a type by construction,
but "by construction" is a claim), and the early-`return` inside `main`'s guarded
match. `splitMonadic` carries three `#guard`s pinning that it strips the flag
from any position and leaves the positional order alone.

---

## §7 THE ORDER OF THE REMAINING WORK

**Ranked by §5.3's measurement, not by taste.** The pre-registered guess put
method calls first; the buckets put class instantiation first and method calls
third, which is exactly why the ranking is a measurement.

**Ten of the nineteen buckets are closed**, covering ~475 of the 548 frontier
rows: class instantiation (111), generators (88 + `enumerate` 22 + `count` 5 +
`next` 2), method calls (78), dict displays (53), closures (34), namedtuple
construction (33), try/except (24), assert (21), set (16), del (11), raise (5),
any/all (6). What is left, in measured order:

1. ~~Keyword arguments — 36 rows.~~ **DONE.** `mergeKwArgs` resolves keywords to
   a COMPLETE positional array at the call site, so the call boundary's signature
   never changes; module defs, instance methods and namedtuple-subclass methods
   all bind through it, plus `dict(k=v, …)` and `sorted(reverse=)`. The keyword
   VALUES needed the knot boundary a **third** time — `kwargs.toList.map (·.2)`
   is a function application, not a projection, so no block member can recurse on
   it (`Kont.kwArgs`).
2. **The small tail — ~5 rows.** Statically-poisoned module bindings (2), live
   module bindings, `max`/`min` over a heap referent (1).
3. ~~The script executor.~~ **DONE** — see §6.2.

Then, and only then, `twinAgrees` (§8.5) — which this rebuild does not attempt
and does not need in order to be measured.

Then, and only then, `twinAgrees` (§8.5) — which this rebuild does not attempt
and does not need in order to be measured.
