# The LEAN tier: Lean 4's kernel language as a versioned surface

**Status: founding charter. No semantics. No Lean.** Thomas chartered this
tier on 2026-08-22: *"Adding Lean as another language to lean-surfaces. This
would allow us to prove correctness of lean itself, similar to lean4lean."*

This document is the census and the positioning. Everything numeric in it was
**measured at our pin** by an instrument that ships with it
(`harness/lean_kernel_census.py` → `docs/lean-kernel-census.json`), or was read
from a primary source that is cited. Where a number is quoted from someone
else's artifact it is attributed to that artifact and marked as theirs.

**Two expected counts in the dispatching brief were wrong**, which is the
argument for landing the instrument before the prose: the brief expected ~11
`Expr` and ~7 `Level` constructors; the source says **12 and 6**. That is the
family's own §5.4 lesson arriving on day one of a new tier.

---

## 0 GÖDEL HONESTY, and it goes on the first page

A tier whose subject is its own logic has to say what it cannot do **before**
it says what it can, because every reader's first question is the one the
second incompleteness theorem already answered.

> **This tier will never prove Lean consistent. Not in Lean, not by any
> artifact it builds. If Lean is consistent, Lean cannot prove it.**

That is not a limitation of our approach or a gap to be closed later. It is a
theorem about the subject, and a charter that left it to a footnote would be
selling something. What remains is worth building, and it is exactly three
things:

| # | the achievable theorem | where it can be proved | status in the field |
| --- | --- | --- | --- |
| **(a)** | **the checker implements the spec** — an executable typechecker agrees with the thesis's inference rules | **in Lean.** No reflexivity problem: this is a statement about a program and a relation, both ordinary mathematical objects | lean4lean's stated goal |
| **(b)** | **soundness relative to a model** — the rules have a set-theoretic model, so a derivation of `False` would refute ZFC + inaccessibles | **NOT in Lean** — the metatheory is strictly stronger than Lean's own | the thesis's contribution |
| **(c)** | **cross-checker agreement** — independent implementations accept the same environments | empirically, by running both | **already built and public** — the Lean Kernel Arena, daily (§9.1) |

**(b) is where the honesty has to be sharpest.** A model-soundness proof does
not make Lean safe; it *reduces* Lean's consistency to a stronger theory's.
That is a real and standard gain — it is what "relative consistency" means
everywhere in logic — and it is not the same as safety. Anyone who reads a
soundness theorem as "Lean is proved correct" has read it wrong, and this
charter's job is to make that misreading hard.

**The reflexive capstone, stated honestly.** The family's endgame here is
attractive and should be described without inflation:

> Every environment this repository produces is checked today by a C++ kernel
> we did not write and cannot inspect from inside Lean. A verified checker
> would replace that with **a small proved artifact plus a formal spec**.
> Trust would be *reduced and made explicit* — never *eliminated*.

What would still be trusted afterwards, enumerated so nobody has to guess:
the **formal spec** is the right statement of Lean's type theory; the checker's
**own** compilation and execution; and — if the tier ever wants a number rather
than a proof about a corpus — the **exporter** that produced the environment.
That last one is the quiet one, and §2 below is where it stops being quiet.

**This is the same trust boundary the family already draws** (§0.1 principle
II), pointed at the repository's own floor. The definition is trusted and kept
minimal; the library is never trusted. A verified checker does not move the
boundary — it makes the trusted side *auditable*, which is the only kind of
progress available on this question.

---

## 1 THE DOCTRINE'S PUNCHLINE: Lean already IS §0.1 principle II

Worth stating plainly, because it is the reason this tier belongs in this
family rather than being a curiosity parked beside it.

The family's central architectural claim is a two-stratum trust boundary: a
**minimal trusted definition**, and an **unboundedly growable untrusted
library** whose output the definition re-checks. Every tier is built to that
shape and the shape is argued for at length in `docs/family-architecture.md`.

**Lean's own architecture is that claim, already implemented, at industrial
scale.** The split is not an analogy:

| family stratum | Lean's realization | measured at our pin |
| --- | --- | --- |
| **the DEFINITION** — trusted, minimal | the **C++ kernel** | **7 888 lines**, 38 files, 16 named reduction rules, 7 axioms |
| **the LIBRARY** — never trusted, grows forever | the **elaborator, tactics, `simp`, `grind`, `omega`, all of Mathlib** | the rest of the toolchain — orders of magnitude larger |

A tactic in Lean cannot make a false theorem true, for exactly the reason a
library lemma in this repository cannot: it only ever produces a term the
kernel rechecks. **`sorry` is tracked as an axiom** (`sorryAx`, measured at
`Init/Prelude.lean:747`) rather than as a warning, which is principle II's
"incompleteness is published, never hidden" implemented as a datatype.

So the tier's subject is not merely *another language*. It is **the family's
own doctrine, written in C++, that every other tier in this repository already
depends on.** The Python tier's 32 331 lines, the SV tier's 98 theorems and
every `#guard` in the tree are believed because that 7 888-line artifact
accepted them. Making it a modeled surface closes the family's floor.

**One consequence for the version registry**, and it is unusual: Lean's kernel
is the only "language" in the family whose implementation this repository
*already runs on every build*. Every other tier's oracle is a program we invoke;
this tier's oracle is the program that checks the tier.

---

## 2 THE KERNEL LANGUAGE, counted

The instrument takes **two** inputs, because the kernel is written in two
languages and neither half is optional:

* the **datatypes** come from the toolchain's shipped Lean sources
  (`src/lean/Lean/{Expr,Level,Declaration}.lean`);
* the **rules** come from the lean4 repository's `src/kernel` C++ tree.

**The C++ half is not shipped inside an elan toolchain.** Measured: the
toolchain's `src/kernel` directory *exists and is empty*, and all **2 485**
shipped source files are `.lean`. So the tier's authority document has to be
fetched at the tag matching the toolchain, and the instrument **REFUSES** when
the two disagree about the version rather than measuring a chimera. That
refusal fired for real during development, before it was ever tested
deliberately.

### 2.1 The vocabulary

| datatype | constructors | kernel-admissible | note |
| --- | ---: | ---: | --- |
| **`Expr`** | **12** | **10** | `mvar` and `fvar` are elaboration-only |
| **`Level`** | **6** | **5** | `mvar` again |
| **`Literal`** | 2 | 2 | `natVal`, `strVal` |
| **`Declaration`** | 7 | 7 | what may be *added* to an environment |
| **`ConstantInfo`** | 8 | 8 | what may be *found* in one |

`Expr`, in declaration order — and the order is the datum, so the census keeps
it rather than sorting: `bvar`, `fvar`, `mvar`, `sort`, `const`, `app`, `lam`,
`forallE`, `letE`, `lit`, `mdata`, `proj`.

**The two-constructor gap is the tier's first structural finding.** The kernel
refuses any declaration containing a metavariable or a free variable — stated
in `Environment`'s own docstring and enforced by two of the 15 kernel exception
classes (`declaration_has_metavars_exception`,
`declaration_has_free_vars_exception`). So **a Lean surface never has to model
`mvar`**, and the elaborator's hardest datatype is out of tier by the subject's
own rule rather than by our choice. That is the opposite of the usual founding
experience, where the vocabulary a tier must cover exceeds what it hoped.

**`Declaration` (7) and `ConstantInfo` (8) are different sets and the
difference is load-bearing.** `inductDecl` goes in; `inductInfo`, `ctorInfo`
and `recInfo` come out — because the kernel *elaborates* inductive
declarations rather than merely checking them (§2.3). `quotDecl` is a
declaration that carries no data at all: it asks the kernel to install the four
`Quot` constants at once.

### 2.2 The rules — 16, each a named function

The reason this census is a **set equality** and not a judgement call: every
reduction rule the kernel implements is a separately named C++ function, so
"did we cover the rules" is answerable by symbol lookup rather than by reading
prose. The instrument confirms each symbol exists and refuses if one moves.

| rule | kernel symbol | file |
| --- | --- | --- |
| beta | `whnf_core` (App case) | `type_checker.cpp` |
| zeta | `whnf_core` (Let case) | `type_checker.cpp` |
| zeta-fvar | `whnf_fvar` | `type_checker.cpp` |
| delta | `unfold_definition` | `type_checker.cpp` |
| delta-lazy | `lazy_delta_reduction` | `type_checker.cpp` |
| iota | `reduce_recursor` | `type_checker.cpp` |
| proj | `reduce_proj` | `type_checker.cpp` |
| eta | `try_eta_expansion_core` | `type_checker.cpp` |
| eta-struct | `try_eta_struct_core` | `type_checker.cpp` |
| proof-irrelevance | `is_def_eq_proof_irrel` | `type_checker.cpp` |
| unit-like | `is_def_eq_unit_like` | `type_checker.cpp` |
| nat-lit | `reduce_nat` | `type_checker.cpp` |
| nat-pow | `reduce_pow` | `type_checker.cpp` |
| string-lit | `try_string_lit_expansion` | `type_checker.cpp` |
| offset | `is_def_eq_offset` | `type_checker.cpp` |
| quot | `environment::add_quot` | `quot.cpp` |

**The literal acceleration set is 15 operations**, enumerated from
`reduce_nat`'s own dispatch rather than from documentation: `succ`, `add`,
`sub`, `mul`, `pow`, `gcd`, `mod`, `div`, `beq`, `ble`, `land`, `lor`, `xor`,
`shiftLeft`, `shiftRight`.

This set is **the single most likely source of a checker/kernel disagreement**,
and it is worth saying why. These are the rules where the kernel does *not*
follow the type theory's own definition: `Nat.add` unfolds to a unary recursor
in the theory and to a GMP call in the kernel. Every one of the 15 is a place
where an implementation must reproduce a *bignum library's* behavior exactly —
including `div` and `mod` at zero, and `sub`'s truncation at zero. A tier that
mirrors the thesis's rules and stops there would not check these at all, which
is precisely why §5's taxonomy puts them where it does.

`nat-pow` is broken out from the other fourteen in the kernel's own source —
it gets a separate guarded function rather than joining `reduce_bin_nat_op` —
because unguarded `pow` on literals is how you turn a typechecking request into
an out-of-memory. That is a resource-exhaustion boundary living inside the
trusted base, and it is a `TIMEOUT`-shaped concern rather than a soundness one.

### 2.3 The kernel elaborates inductives, and that is most of the work

`inductive.cpp` is **1 249 lines** — the second-largest file in the kernel
after `type_checker.cpp` (1 247). It does not merely check inductive
declarations; it **constructs** their consequences, and measured by the
functions it exports it does all of:

* the **positivity check** (`check_positivity`);
* the **elimination level** computation (`init_elim_level`) — the large-
  elimination side condition, i.e. whether a `Prop`-valued inductive may
  eliminate into `Type`;
* **recursor construction** (`mk_rec_name`, and the rule-building around it);
* **mutual** inductive families;
* **nested** inductives, which are compiled away to mutual ones by a separate
  pass in the same file.

**This is the tier's real scale statement.** "Model the kernel" sounds like
modelling `type_checker.cpp`; the census says a faithful surface owes
`inductive.cpp` too, and that half is where the specification is subtlest —
the eliminator's type is *computed* from the declaration, so a model must
compute the same type rather than check a given one.

### 2.4 The axioms — 7, and the split is the charter's hinge

| axiom | class | site | deprecated |
| --- | --- | --- | --- |
| `propext` | sound | `Init/Core.lean:1591` | — |
| `Quot.sound` | sound | `Init/Core.lean:1787` | — |
| `Classical.choice` | sound | `Init/Prelude.lean:818` | — |
| `sorryAx` | unsoundness marker | `Init/Prelude.lean:747` | — |
| `Lean.trustCompiler` | **trust extension** | `Init/Core.lean:2378` | **since 2026-02-01** |
| `Lean.ofReduceBool` | **trust extension** | `Init/Core.lean:2436` | **since 2026-02-01** |
| `Lean.ofReduceNat` | **trust extension** | `Init/Core.lean:2449` | **since 2026-02-01** |

Three parsing traps had to be cleared to get this table right, and each would
have produced a wrong charter:

1. A naive grep reports **five extra** `axiom` lines. All five sit inside
   ```-fenced blocks in docstrings. Counting them would more than double the
   stated size of Lean's trusted base.
2. `Quot.sound` is declared as bare `sound` inside `namespace Quot`. Without a
   namespace stack the most-cited axiom in Lean is named wrongly.
3. Once namespaces resolved, a classifier keyed on bare names silently
   re-filed all three trust extensions as **sound**. The instrument now keys on
   the local name and refuses if the family ever comes back empty.

**`sorryAx` is not a fourth sound axiom and not a bug.** It is principle II's
"the library's incompleteness is published, never hidden", implemented: an
incomplete proof does not fail quietly, it *changes the theorem's axiom
dependencies*, where `#print axioms` will find it. This repository's triad
already reads that field on every landing.

**The three trust extensions are the tier's most interesting single finding**,
and they connect directly to a ruling Thomas made the same day.
`Lean.ofReduceBool` is the axiom that says *if the compiler evaluated this
`Bool` expression to `b`, then it equals `b`* — it is what `native_decide`
appeals to, and it moves the compiler, its runtime and every
`@[implemented_by]` into the trusted base for any theorem that uses it.

`docs/family-architecture.md` §0.1 II(a) — the graded decide ladder — governs
exactly this axiom, ranking width-parametric symbolic proof above kernel
`decide` above `native_decide`, and requiring any rung-3 use to carry its
`#print axioms` receipt at the use site. **This tier would formalize the very
axiom the ladder rations.** A Lean surface that models `ofReduceBool` states,
as a definition rather than as policy, precisely what a rung-3 proof is
assuming — which is the strongest possible version of "the trust boundary is
per-theorem and visible, never ambient".

**AND THE AXIOM IS BEING RETIRED UPSTREAM — measured, and date-stamped by the
instrument.** All three trust extensions carry

> `@[deprecated "in-kernel native reduction is deprecated; assert native
> evaluations with axioms instead" (since := "2026-02-01")]`

and **none of the three sound axioms does.** The deprecation partitions exactly
onto the class this charter drew independently, which is the strongest
corroboration a classification can get: upstream and this census agree about
which of Lean's axioms are foundational and which are trust purchases.

The instrument records the `since` date as data rather than letting the prose
assert it, because **this is a moving target** and a charter that hard-coded
"Lean has 7 axioms, 3 of them trust extensions" would go stale silently. The
mechanism is not gone — `native_decide` still elaborates, and the C++ kernel
still calls compiled code — but the axioms underwriting it are on a published
retirement path.

**Lean's own docstring makes this tier's case better than this charter could.**
On `ofReduceBool`, upstream writes that using it puts the compiler and
interpreter into your trusted base — *"extra 30k lines of code"* — and then:

> *"you will probably not be able to check your development using external type
> checkers that do not implement this feature."*

That sentence presupposes external type checkers as the thing worth staying
compatible with. **Lean's own documentation treats independent checkability as a
property worth preserving**, and Thomas's ladder rations the axiom that costs
it. The tier sits precisely on that seam.

---

## 3 THE TAXONOMY MAPPING — §4.3's Lean row, filled

Lean's kernel is not a language specification with behavior classes; it is a
decision procedure. The mapping is therefore unusually clean, and two rows are
*empty by construction* — which the family asked founding lanes to gate rather
than celebrate.

| family cause | the Lean tier's content |
| --- | --- |
| **REFUSE `unsupported`** — out-of-tier construct | **The live one.** A rung not yet climbed: `mdata`, `proj`, nested inductives, the 15 accelerated `Nat` ops, `Quot`. Retires by widening. This is where essentially all early refusals live. |
| **REFUSE `undefined`** — the language says this run has no meaning | **EMPTY, and gated.** A typechecker is a total decision procedure over a well-defined relation; there is no undefined behavior in type theory. **A Lean tier emitting `undefined` has a bug.** This matches the family's expectation for Wasm and is a stronger statement: Wasm has a small named nondeterminism set, and this tier has none at all. |
| **REFUSE `environment`** — needs something outside the modeled slice | **Narrow but real, and it is the EXPORTER.** An environment reaching a declaration kind the export path cannot represent. Not "unmodeled libc" — the analogous hole here is a *serialization* hole. |
| **REFUSE `order-dependence`** — several admissible orders, invariant unshowable | **EMPTY.** See §3.1. |
| **DIVERGE** | **checker says yes, kernel says no — or the reverse. This is a soundness bug in one of them.** §3.2. |
| **TIMEOUT** | Real and unavoidable: `whnf` does not terminate on every input the *syntax* admits, and the kernel ships its own recursion-depth guard (`scope_rec_depth`). `nat-pow` is the memory-shaped instance. |

### 3.1 Nondeterminism: none — the family's simplest ∀-resolution

Stated plainly because the family asks every tier to state it, and this tier's
answer is the shortest one anybody will write:

> **Definitional equality is a deterministic relation, and the kernel's
> checking of it is a deterministic function of the environment and the term.
> There is no schedule, no evaluation order, no unspecified resolution, and no
> implementation-defined value. The ∀ that §0.1 principle I refuses to narrow
> is, here, a ∀ over nothing.**

Two caveats, both real and neither a nondeterminism:

* **Search order is a performance strategy, not a semantic choice.** The
  kernel's `lazy_delta_reduction` picks which side to unfold by comparing
  definition heights — a different order would be slower, or would fail to
  terminate within the depth guard, but it cannot accept a term the theory
  rejects. Order affects *whether an answer arrives*, never *which answer*.
* **Caches are observable in resources, not in verdicts.** The kernel memoises
  `whnf_core` and failed defeq pairs. A model may omit both.

So the tier has **no cause-4 bucket** and **no §5.1 membership sites**: every
site's permitted set is a singleton, and MATCH degenerates to equality. This
tier is the family's calibration point in the opposite direction from
WebAssembly — Wasm proves the instrument works where nondeterminism is small
and named; Lean proves it works where there is none.

### 3.2 DIVERGE is the highest-stakes row in the family

Everywhere else in this repository, a DIVERGE means *our model is wrong*. The
oracle is a mature implementation, and the finding is ours to fix.

**Here, a DIVERGE means one of the two is unsound, and it might not be ours.**
If an independent checker accepts an environment the C++ kernel rejects, or
rejects one it accepts, then either the checker has a bug or **the artifact
this entire repository's trust rests on has one**. There is no third
explanation, because both implement the same total relation and §3.1 says that
relation is deterministic.

Three consequences the tier has to build for from the first line:

1. **A DIVERGE row is never triaged as "our bug" by default.** The family's
   §4.2 precedence rule says the spec is the target and the implementation is
   the oracle; here the spec is the thesis's rules, and a disagreement is
   adjudicated *against the rules*, not against the kernel's behavior.
2. **The reproduction has to be minimal and shippable.** A disagreement on a
   Mathlib declaration is not a report anybody can act on. The tier owes a
   delta-debugger for exported environments before it owes coverage.
3. **The honest prior is that it will be OUR bug**, and the charter says so
   rather than letting a lane discover it under pressure. The kernel has been
   run over every Lean environment ever built.

### 3.3 How often does this actually happen? Measured.

A charter that called DIVERGE "the highest-stakes row" without saying how often
the row appears would be selling drama. The census counted, over the Lean 4 era,
from upstream issues and PRs:

| class | count |
| --- | ---: |
| **kernel soundness bugs admitting an axiom-free proof of `False`** | **9 confirmed**, 1 open/contested |
| runtime/toolchain soundness (e.g. a GMP version bug reaching the kernel) | 3 |
| kernel bugs with no demonstrated `False` | 4 |
| **elaborator / compiler / `native_decide`** (the kernel still catches these) | **11** |
| discussion and infrastructure RFCs | 6 |

**They cluster twice — by construct, and by DATE. The second clustering is the
one that should change a lane's plans.**

*By construct:* the densest cluster is **structure eta and projections** — §8's
construct again, four of the nine — with a second cluster in **accelerated
`Nat`** (a truncating `lean_nat_mod` gave an axiom-free `False` in 2022; GMP
versions below 6.3.0 could too). Precisely the two rule families §2.2 flagged as
where the kernel departs from the type theory's own definitions.

*By date, and this is the finding:*

> **Six of the ten landed between 2026-07-22 and 2026-08-21 — a five-week
> window. Before that wave the rate was roughly one every one to two years.**

The wave was driven by **AI-assisted adversarial search**, with the upstream
issues naming the models used. **So the base rate is not stable, and this
charter must not quote a per-year figure as though it were.** A lane planning
around "kernel bugs are rare" would be planning around a number that stopped
being true five weeks ago. The honest statement is that the search cost of
finding these just fell sharply, and nobody knows where the new rate settles.

**Independent checkers demonstrably catch these** — measured from the upstream
fix PRs' own text: `nanoda` is cited in **four separate** fix PRs as rejecting
the exploit; `lean-inductive-models` caught both exploits in another;
`leanchecker` detected an inconsistent environment a normal build accepted; and
lean4lean's own `bugs-found.md` records two kernel bugs it found, one described
upstream as *"the second kernel bug discovered by Lean4Lean verification"*.

**And the counter-evidence, which belongs in the same paragraph.** On one bug
the fix PR records that *"the bogus proof was also accepted by nanoda"*.
**Independence is not immunity.** lean4lean's `bugs-found.md` holds exactly
**three** entries after three years, and one of the three is not a kernel
soundness bug at all. A tier that sold independent checking as a reliable bug
detector would be overselling a technique whose measured yield is real but low.
---
## 4 THE ENVELOPE — the question the other tiers hand-built is ANSWERED

Every founding lane in this family has hand-built an envelope schema
(§8 step 4): `docs/envelope-schema.md`, `docs/c-envelope-schema.md`,
`docs/ada-envelope-schema.md`, `docs/es-envelope-schema.md`,
`docs/sv-envelope-schema.md`. Each is the lane's own answer to "how does a
frontend hand a program to Lean".

**This tier does not get to design one, and should not want to.** An
official, versioned, maintained serialization of a Lean environment already
exists: **`lean4export`** (`leanprover/lean4export`, **Apache-2.0**, verified
per-file — headers are Lean FRO, LLC).

Measured at its HEAD (`cacf989`, dated **one day before this census** — it is
actively maintained; 107 commits, contributors from the Lean FRO):

| datum | value |
| --- | --- |
| current format version | **3.1.0** |
| encoding | **NDJSON** — one JSON object per line |
| spec | `format_ndjson.md`, **353 lines, in-repo** |
| its toolchain pin | `v4.34.0-rc2` — **two minor releases ahead** of ours |
| dependencies | **none** (`lake-manifest.json` packages == `[]`) |
| source | 1 710 Lean lines, of which **509 are a PARSER back into `Lean.ConstantInfo`** |

**Four things this changes, and the fourth is the one to notice.**

**(1) The vocabulary question is answered by set equality, not by taste.** The
exporter emits exactly the **10 kernel-admissible `Expr` constructors** this
charter's §2.1 counted, and refuses exactly the **2 elaboration-only** ones —
`fvar` and `mvar` both hit a `panic!` reading *"cannot export free variables or
metavariables"* at `Export.lean:160`. Two independent artifacts, measured
separately, partition the same 12 constructors the same way. That is the
strongest form §5.5's coverage manifest can take, and this tier gets it before
writing a line of Lean.

**(2) `mdata` is stripped by default.** `removeMData` runs unless
`--export-mdata` is passed. `mdata` carries elaborator annotations that are
semantically transparent — the kernel's own `whnf_core` recurses straight
through it — so the default export is *the kernel's* view of the term rather
than the elaborator's. A tier that mirrors the kernel should keep that default,
and should say so rather than discovering it.

**(3) There is a round-trip, and it is theirs.** `Export/Parse.lean` parses the
format back into `Lean.ConstantInfo`. The family's usual step-5 extractor
obligation — write a frontend, run all three refusal paths — is largely
pre-discharged by a maintained upstream artifact with a golden-output test file
(`Test.lean`, 745 lines of `#guard_msgs`, i.e. an executable by-example spec).

**(4) The format has a VERSION, and it has already moved.** `3.1.0` today;
`2.0.0` was a whitespace-separated opcode format (`#NS`/`#EC`/`#EP`/`#IND`)
whose spec **never lived in this repo**. And the repo's own committed example
is **stale** — `examples/Nat.add_succ.ndjson` declares format `3.0.0` and wraps
a theorem in an array where current `3.1.0` code emits a bare object. So the
envelope's `schema_version` is not decoration here: it is a field that has
already been wrong inside the upstream repository, which is precisely
`family-architecture.md` §3.2's *"read the mode out of the artefact, never out
of an ambient setting"* arriving with a worked example.

### 4.1 The field mapping, and what a Lean tier still has to add

| family envelope field | supplied by lean4export 3.1.0? |
| --- | --- |
| `schema_version` | **yes** — `format.version`, emitted at `Export.lean:416-435` |
| `language_version` | **yes** — `exporter.version` plus the Lean version |
| node vocabulary | **yes**, and derived from the kernel rather than chosen |
| `source_file` / `source_sha256` | **no** — an environment has no single source file |
| `frontend` FAMILY | **partial** — the exporter is named; the *toolchain* that built the environment is the real input |
| `profile_id` | **not applicable** — §3.1: no implementation-defined behavior to pin |
| deterministic output | **not verified by us** — NOT MEASURED |
| `Unsupported` leaves | **no** — the exporter `panic!`s instead of emitting a refusal node |

The last row is the tier's one genuine envelope obligation, and it is a real
gap rather than a formality: the family's contract is that anything outside the
pinned vocabulary becomes a **loud `Unsupported` leaf** the scoreboard can
count, and `panic!` is the opposite of that — it destroys the run instead of
producing a countable row. A tier consuming this format must decide whether to
wrap the exporter or to carry a patch, and §7's options price that differently.

### 4.2 `leanchecker` — and the ecosystem already ships a differential

The neighbouring artifact matters more than expected, and the census caught it
by reading a deprecation notice rather than by asking the right question:

> **`lean4checker` is DEPRECATED and has been merged into Lean itself.** Its
> README says the repository *"is deprecated and will be archived"*. The
> program now ships as **`leanchecker` with every toolchain** — measured
> present in our own pin at `bin/leanchecker`, **78 128 bytes**.

What it does, answered precisely because the distinction is load-bearing: it
**re-checks compiled `.olean` environments in-process by replaying declarations
through the kernel. It never parses a text export.** Its own README calls it
*"not an external checker"*. Constructors and recursors are **not** sent to the
kernel — they are regenerated from the inductive declaration and compared for
equality.

**So the ecosystem already runs a replay check, and it runs the SAME kernel.**
That is the crucial qualifier and it is what leaves room for this tier:
`leanchecker` defends against a *corrupted or maliciously constructed `.olean`*,
because it re-derives everything from declarations. It cannot, even in
principle, find a bug in the kernel's own rules — there is only one
implementation in the loop. **An independent checker is a different instrument
answering a different question**, and §7's options turn on which question
Thomas wants answered.

---

## 5 THE CORPUS LADDER — measured at our pin

Every environment in the ladder below carries the C++ kernel's implicit verdict:
it exists as an `.olean` only because the kernel accepted every declaration in
it. **That is the differential oracle, and it is free.** Unlike every other tier
in this family, this one does not have to run its oracle to get expected values
— the corpus *is* the oracle's output, already computed, sitting on disk.

| rung | modules | declarations | `.olean` bytes | source lines |
| --- | ---: | ---: | ---: | ---: |
| **`Init`** | 631 | **65 994** | 99.3 MB | 212 717 |
| **`Std`** (closure) | 996 | **113 352** | 110.6 MB | 197 379 |
| **`Lean`** (closure — all of core) | **2 322** | **206 644** | 335.4 MB | 267 725 |
| **Mathlib** | 8 268 files | NOT MEASURED | **1.82 GB** | **2 280 560** |

Declaration counts are **import closures, not disjoint partitions** — `Std`'s
closure contains most of `Init`. They were measured by a single niced `lean`
process on a dependency-free scratch file (37.2 s for the `import Lean` run), no
`lake` and no build lock.

Of core's 206 644 declarations, **126 187 are non-internal and exportable** —
`lean4export` filters `!.isInternal` by default — and the mix is: 103 606
`def`, 89 382 `theorem`, 3 018 `opaque`, 2 893 `inductive`, 4 716 `ctor`,
3 010 `rec`, 4 `quot`, and **15 `axiom`**.

> **The 15 is worth a sentence.** §2.4 measured **7** axioms in the *sources*
> under `Init/`; the *environment* reports 15. The difference is not a
> contradiction — the environment count includes axioms declared outside the
> `Init/` tree this charter's instrument scanned. A tier that wants the
> authoritative number takes it from the environment, not from a grep, and this
> charter records both with their methods rather than picking the one it likes.

**Mathlib is present in this repository's own tree**, at
`.lake/packages/mathlib`, rev `79d0395a` (2026-07-16), pinned to
`leanprover/lean4:v4.33.0-rc1` — an **exact match to our pin**. So the largest
rung of the ladder is already on disk and already agrees with our toolchain,
which removes the usual corpus-acquisition step entirely.

**Mathlib's declaration count is NOT MEASURED, deliberately.** The probe
declined to load the environment: it measured a load average of 15.73 and ~34 MB
of free RAM with two other lanes building. A source-keyword approximation gives
126 976 `theorem` + 58 452 `lemma` + 32 423 `def` + 26 939 `instance` line
openers, and that is an **undercount of the environment** for the same reason
core's grep undercounted its axioms. It is recorded as an approximation and
labelled as one.

**A full Mathlib export was priced as an ESTIMATE — and then the estimate was
CHECKED against someone else's measurement, which is the only reason it is worth
printing.** This lane's estimate, from the exporter's own capacity hints
(`Export.lean:38` pre-sizes `visitedExprs` to 10 000 000 entries) and 56.7
bytes/line, was **order-of-magnitude 1–5 GB of NDJSON**.

> **The Lean Kernel Arena publishes the real number: its Mathlib test is a
> 5.2 GB export, 100.0 M lines.** (CLAIMED-BY-ARENA, from their published
> `results.json`; not measured by this lane.)

**So the estimate was the right order and slightly low**, which is the useful
outcome: the method is sound and a lane can trust it to within a factor of ~2.
The honest reading is that a full export is a **multi-gigabyte, hundred-million-
line artifact**, and the binding constraint is **peak RAM rather than time** —
`visitedExprs` holds every unique `Expr` in the library as a live key. Nobody
should schedule that run off this paragraph; they should run it under the build
lock and measure.

**And Mathlib's declaration count now has a citable number**, which §5's table
records as NOT MEASURED by us: **308 129 declarations** across 7 563 modules,
at commit `534cf0b` (2026-02-02) — attributed to a published network-structure
analysis of Mathlib, not to this lane. It is ~2.4× core's 126 187 exportable
declarations, which is the ratio a ladder should be planned around.

---

## 6 LEAN4LEAN — the census, and it is the heart of the positioning

`digama0/lean4lean`, **Apache-2.0** (verified: 201-line stock boilerplate;
of 102 `.lean` files, 4 carry copyright headers and all 4 are vendored from
upstream Lean/Mathlib — none are Carneiro's).

**It is alive.** HEAD `e0e3f6b`, **2026-08-14** — eight days before this census.
240 commits on master, **88 in the last six months**. Mario Carneiro is the
author of essentially all of it; Joachim Breitner and Kim Morrison contribute.
**It pins `leanprover/lean4:v4.33.0-rc2` — one release-candidate step ahead of
our `v4.33.0-rc1`**, the closest version alignment of any external artifact in
this family. It depends on `batteries` only; **no Mathlib**.

### 6.1 The shape — 39 468 lines, and the split is the finding

| partition | lines | % | theorems | defs |
| --- | ---: | ---: | ---: | ---: |
| **executable checker** | **3 964** | 10.0% | **0** | 309 |
| **proof / metatheory** (`Theory/`, `Verify/`, `Std/`) | **21 531** | 54.6% | 1 667 | — |
| **`Experimental/`** (not a default build target) | 13 309 | 33.7% | 987 | 469 |
| tests | 664 | 1.7% | 5 | — |

**The proof-to-executable ratio is 5.43** (8.79 counting `Experimental/`). A
tier that reads "a typechecker written in Lean" and budgets for 4 000 lines has
mis-priced the work by a factor of five, and the mis-pricing is in the half that
matters.

### 6.2 The executable checker: production-grade, and complete

This is the census's most favourable finding and it should be stated without
hedging.

* **Zero real `sorry`s in the executable partition.** Measured, after stripping
  comments.
* **All 12 `Expr` constructors handled**, refusing exactly `mvar` — the same
  partition the kernel draws and the same one `lean4export` draws. Three
  artifacts, one boundary.
* **Every reduction rule §2.2 counted**, plus K-like reduction and
  `lazy_delta_proj_reduction` (added 2026-08-14, at HEAD).
* **The 15 accelerated `Nat` operations, exactly** — independently enumerated by
  the probe from `TypeChecker.lean:493-517` and matching this charter's §2.2
  list element for element. `Nat.pow` carries its own guard (refuses exponents
  above 2^24), mirroring the kernel's separate `reduce_pow`.
* **All 7 declaration kinds**, and **full inductive elaboration** — positivity
  check included. It does not merely check pre-elaborated declarations.
* **A new, complete level-algebra decision procedure** (`Level.lean`, 363
  lines), enabled 2026-08-11. The stdlib path runs as a fast path with the
  complete procedure as fallback. HEAD's commit proves **coNP-hardness of level
  equivalence** by reduction from SAT.

**Two deliberate divergences, and the repo documents them itself** in a
`divergences.md` file — which is, in this family's vocabulary, a
self-maintained findings register:

1. **`reduceBool` / `reduceNat` are REFUSED.** lean4lean throws rather than
   implementing native reduction, and its stated reason is that doing so would
   require verified compilation — *"an additional chunk of work comparable to
   this entire repo"*. **This is the `ofReduceBool` trust extension of §2.4,
   refused by the one artifact best placed to model it.** Thomas's decide ladder
   rations that axiom; lean4lean declines to implement it at all. The two
   positions agree, and this tier sits exactly on the seam.
2. **Level normalization differs from the C++ kernel's**, per its own
   `divergences.md` item 11.

### 6.3 The proof status — the table this charter exists to produce

| result | file | status |
| --- | --- | --- |
| **`addDecl.WF`** — *the* top-level soundness statement | `Verify/Environment.lean:225` | **PROVED for 6 of 7 declaration kinds. `inductDecl` is `sorry`** (line 236) |
| `inferType.WF` | `Verify/TypeChecker.lean:188` | proved modulo 5 downstream sorries (`.proj`, struct-eta, unit-like) |
| `isDefEq.WF` | `Verify/TypeChecker.lean:196` | proved modulo 2 sorries. **One-directional**: `b = true` implies model defeq; completeness NOT claimed |
| `whnf.WF` | `Verify/TypeChecker.lean:184` | proved modulo 2 sorries (both `.proj`) |
| `checkType.WF` | `Verify/TypeChecker.lean:192` | proved modulo the same downstream sorries |
| **`IsDefEq.uniq`** — unique typing | `Theory/Typing/UniqueTyping.lean:13` | a real ~100-line induction, **consuming two sorry'd injectivity lemmas** |
| `IsDefEqU.sort_inv` — sort injectivity | `Theory/Typing/Injectivity.lean:11` | **`sorry`** |
| `IsDefEqU.forallE_inv_stratified` — Pi injectivity | `Injectivity.lean:14` | **`sorry`** |
| `IsDefEqU.sort_forallE_inv` — sort/Pi disjointness | `Injectivity.lean:33` | **`sorry`** |
| **`VInductDecl.WF` / `VEnv.addInduct`** | `Theory/Inductive.lean:5,7` | **NOT EVEN STATED — two `sorry` stubs in an 8-line file** |
| **model soundness** (§0 theorem (b)) | — | **ABSENT from the shipped build.** Model-theoretic work exists only in `Experimental/` |

Counts: **113 real `sorry`s** (132 raw grep occurrences, 19 in comments), of
which **24 are in the shipped build** and 89 in `Experimental/`. **34 axioms in
the shipped build** — 32 of them in `Verify/Axioms.lean`, each asserting that an
upstream `@[extern]`/`opaque` stdlib function equals a total Lean model of it,
plus a pointer-equality soundness axiom.

**Three honesty notes the census insisted on:**

* **CI is green WITH sorries, and admits it.** The workflow's own comment reads
  *"The proofs in `Verify` deliberately contain sorrys, so warnings must not fail
  the build."* A green badge here does not mean what a green badge means in this
  repository.
* **The README does not overclaim — it barely claims.** It states no `sorry`
  count, names no complete theorem, and is **stale** (it still calls
  `UniqueTyping.lean` conjectural, which HEAD has advanced past). Under-specified
  rather than wrong.
* **The author is candid in-source.** `Injectivity.lean`'s docstring reads *"A
  bunch of important structural theorems which we can't prove :("*. And
  `Verify/Environment/Boundaries.lean`'s docstring claims no sorry-backed
  assumptions are introduced, 25 lines above a `sorry` in the same file — found
  by the probe, and exactly the drift §5.5's generated-not-hand-maintained rule
  exists to prevent.

### 6.4 THE SEAM: the kernel's largest half is the metatheory's emptiest

Put §2.3 beside §6.3 and the tier's opening is not a matter of opinion.

> **`inductive.cpp` is 1 249 lines — the kernel's second-largest file, doing
> positivity, elimination levels, recursor construction, mutual and nested
> inductives. lean4lean's ABSTRACT SPECIFICATION of inductive types is an
> 8-line file containing two `sorry` stubs.**

The executable checker implements inductives fully and well. What does not exist
is **the statement of what a well-formed inductive type IS** in the abstract
model — and everything downstream inherits that hole: it is why `addDecl.WF`'s
seventh case is `sorry`, and it is why the thesis's own inductive-specification
rules have nothing to be checked against.

**This is one of the two grounds the tier would take.** It is not a gap anyone
is hiding; it is the hardest part of the subject, it is where the C++ kernel
spends its mass, and it is where a spec-mirror discipline — one Lean definition
per thesis rule, cited — has the most to offer, because the thesis *does* state
those rules (§7.1: the inductive families are 17 of the 71 kernel-relevant rules
families).

**THE SECOND SEAM IS `proj`, and it is worse — because there the thesis states
nothing at all.** §8 collects it, since four separate instruments found it
independently. The structural cause is visible in the model's own datatype:
**`VExpr` has 6 constructors against Lean's `Expr` 12.** `fvar`, `letE`, `lit`
and `mdata` are translated away, `mvar` is refused — all defensible. **`proj`
simply has no abstract counterpart**, which is why `TrProj` is a `sorry` and why
**11 of the 24 shipped sorries cluster there**.

The two seams differ in kind, and a lane should not conflate them. Inductives
are **specified but unformalized** — the thesis states 11 rules and the model
has not caught up. Projections are **unspecified entirely** — there is nothing
to catch up to, and the mirror would have to write the rule before it could
check anything against it.

### 6.5 The other checkers

Deferred to §9.2, where the field is surveyed properly — because the census
found it to be **an order of magnitude larger and healthier** than the brief
assumed, and that discovery changes the positioning rather than merely
decorating it.

### 6.6 Performance — theirs, not ours

**NOT MEASURED by this lane.** Attributed to the artifacts they came from:

* the **paper's abstract** claims *"between 20% and 50% slower"* than the C++
  kernel, on Lean core + Batteries + Mathlib. **No hardware is stated**, and the
  numbers are **byte-identical to the March 2024 v1** — treat them as of early
  2024, not as current.
* **the arena's own timings disagree, and by a lot.** On its Mathlib test:
  `official` **1 475 s**, `lean4lean` **2 979 s** — roughly **2.0×**, materially
  worse than the paper's 20–50%. Both figures are other people's; the charter
  records the disagreement rather than picking a side, and a lane that cares
  should measure. Meanwhile several Rust descendants of `nanoda` run **faster
  than the official kernel** — `sokonanoda` 54 s, `mathgraph` 41 s — which is
  worth knowing before anyone argues that a checker in Lean is the fast path.
* the **README makes no speed claim at all**.
* **there is no benchmark script in the repository.** The real harness is the
  arena's, and it lives in leanprover's repo (§9.1).

### 6.7 The paper, and its title is itself a finding

arXiv:2403.14064, Mario Carneiro, sole author. **The title has changed twice,
and the trajectory is evidence about the subject's difficulty:**

| version | date | title |
| --- | --- | --- |
| v1 | 2024-03-21 | *Lean4Lean: **Towards a formalized metatheory** for the Lean theorem prover* |
| v2 | 2024-12-03 | *Lean4Lean: **Towards a Verified Typechecker** for Lean, in Lean* |
| **v3** | **2025-09-14** | *Lean4Lean: **Verifying a Typechecker** for Lean, in Lean* — 14 pages, submitted to **CPP 2026** |

**Scope narrowed from metatheory to implementation verification** across three
revisions by the person best placed to judge the cost. A founding charter that
proposed to deliver the metatheory should read that table twice. (The brief
dispatching this lane carried the **v1** title, which is how the drift was
caught.)

Stated contributions, paraphrased and cited by the paper's own narrative §1:
the first complete Lean 4 typechecker other than the C++ reference, offered as
defense-in-depth of the *independent reimplementation* kind; partial progress
specifying the metatheory and verifying the checker against it; **and one real
kernel soundness bug found and fixed.** That third item is the field's existence
proof that this work catches things (§9.1 is the current, larger version of it).

**The repository is now ahead of the paper on two limitations** — `IsDefEq.uniq`
has a real proof where the paper calls it conjectural, and four `*.WF` theorems
exist where the paper says *"only a few functions"*. **Still current, and
unchanged:** sort/forall injectivity unproven, fuel-based rather than proven
termination, no verified compilation, and the inductive specification
*"pending future work"*. §9 lists no soundness theorem, no consistency proof and
**no C++-kernel correspondence theorem** as future work; the correspondence is
an informal claim that the Lean code mirrors the C++ *in the same order*.

*Citation caveat: the abstract is verified from the arXiv abs page; body content
came from the HTML rendering, so **section numbers are unverified**. Paraphrased
throughout — no passage reproduced.*

---

## 7 THE SPEC — and the answer to "is it formal" is NO

The authority document is **Mario Carneiro, "The Type Theory of Lean" (MS
thesis, CMU 2019)**, LaTeX source at `digama0/lean-type-theory`.

**Licence: there is NO LICENSE file in-tree and the GitHub API reports
`license: null`.** So the family's cite-and-paraphrase convention (the Ada
charter's §1.7) applies at its strictest: **cite by section and rule, never
vendor, never reproduce.** This charter names rules and counts them; it
reproduces none.

### 7.1 The rule inventory — 71 kernel-relevant rules, and the count has an instrument

**Measured by `harness/lean_spec_census.py` → `docs/lean-spec-census.json`**
(M1 inch 3), from the LaTeX source at the pinned commit, not from the PDF. The
instrument refuses to run against any other commit without an explicit override,
because of §7.2 finding 3.

The source uses **bare `\frac` display math** — no `\inferrule`, no `mathpar`,
no rule macro, and no rule names. So the unit of measure is *a `\frac`/`\dfrac`
occurrence, attributed to the most recent `\boxed{…}` judgment and the current
section*. That is reproducible, and it is a **proxy for "a rule" rather than the
thing itself** — which matters, below.

**Measured totals: 167 typeset rules in the document, 71 of them in the axioms
chapter across 12 judgment families**, 5 of which carry the source's only inline
names: *(beta)*, *(delta)*, *(eta)*, *(iota)*, *(zeta)*.

| judgment family | rules | declared at |
| --- | ---: | --- |
| Typing `Γ ⊢ e : α` | 7 | 2.1 |
| `Γ ⊢ α type` | 1 | 2.1 |
| `⊢ Γ ok` | 2 | 2.1 |
| Defeq `Γ ⊢ e ≡ e'` | 10 | 2.2 |
| Level equality `ℓ ≡ ℓ'` | 1 | 2.2 |
| Level order `ℓ ≤ ℓ' + n` | **14** | 2.2 |
| Algorithmic defeq `Γ ⊢ e ⇔ e'` | 9 | 2.3 |
| Head reduction `e ↝ e'` | 10 | 2.3 — **ELIDED** |
| Inductive spec `K spec` | 1 | 2.6.1 |
| Constructor `α ctor` | 5 | 2.6.1 — **ELIDED** |
| Large elimination `K LE` | 3 | 2.6.2 |
| Subsingleton ctor `α LEctor` | 8 | 2.6.2 |
| **KERNEL-RELEVANT TOTAL** | **71** | 12 families |

Per file, the rest: `Wtypes` 38, `unique` 25, `normalization` 11, `soundness`
10, `compilation` 9, `typesys` 3.

**THE INSTRUMENT CORRECTED THIS CHARTER'S OWN FIRST TABLE, and the correction is
worth more than the number.** An earlier hand-classification of the same chapter
reported **72** rules with a materially different per-family split (Typing 12,
Defeq 14, Head reduction 7, Constructor 3, Subsingleton 4). The disagreement is
**not** a counting error on either side — it is two different attribution rules:

* the **hand** classification attributed each rule to the judgment it
  **concludes**, so a typing rule stated in §2.6 counts under Typing;
* the **instrument** attributes by **position**, to the most recently boxed
  judgment.

**Both are defensible; only one is reproducible.** So the charter adopts the
instrument's numbers and records why they differ, rather than quietly keeping
the prettier table. The lesson generalizes and is exactly §5.5's: **the chapter
TOTAL is robust (71 either way, ±1 for the align* question below); the
per-family SPLIT is an artifact of the attribution rule and must never be quoted
without saying which rule produced it.**

**Two known undercounts, declared by the instrument itself** rather than
discovered later:

1. **`align*`-typeset computation rules are not counted.** The iota menagerie
   and the quotient-lift computation rule are typeset as equations, not
   `\frac`s. This is the ±1 to ~10 the two counts differ over.
2. **Two of the twelve kernel-relevant families are ELIDED** — `e ↝ e'` and
   `α ctor` end in an explicit `…` standing for unwritten congruence rules.

**~71 is the spec-mirror index**: one Lean definition per rule, each citing its
thesis section, coverage measured as a set equality against the committed JSON.
It is a tractable number — an order of magnitude below Wasm's 568 rules — and
the two elided families are where the mirror will have to *write* a rule before
it can check one.

### 7.2 Four findings that change how the mirror must be built

**(1) THE SPEC IS NOT MACHINE-READABLE, and this is the decisive contrast with
WebAssembly.** The Wasm charter's §1.4 could make spec-mirroring a
*machine-checked* correspondence because SpecTec emits the spec's rules as named
artifacts. Here there is **no such generator, and the rules have no names** —
the source tags only five inline: *(beta)*, *(eta)*, *(zeta)*, *(delta)*,
*(iota)*. A rule-name namespace would have to be **invented by this tier** and
maintained by hand against a PDF.

**(2) FOUR FAMILIES ARE TYPESET WITH AN ELISION.** `~>κ`, `≡p`, `>>κ` and `~>σ`
each end in an explicit `...` standing for an unwritten set of compatibility and
congruence rules, described in prose as *"compatibility rules for every syntax
operator"*. **A faithful mirror cannot be built from the LaTeX alone for those
families** — the missing rules must be reconstructed from prose. All four are in
the *metatheory* rather than the kernel-relevant 71 — though **two of the twelve
kernel-relevant families are elided too** (§7.1), which limits the damage less
than it first appeared,
but a lane that promised a complete mirror without reading this would have
promised something the document does not contain.

**(3) THE SPEC IS DORMANT AND FORKED, AND THE PUBLISHED VERSION CONTAINS A
KNOWN-WRONG RULE.** Last commit **2022-08-02** — four years stale, and by a
contributor other than the author. Worse for citation discipline: **the `v1.0`
tag (the published 44-page MS thesis) is NOT an ancestor of `master`.** They
fork at `cb22a27` (2019-02-04) and never rejoin. So "the thesis" is **two
documents**.

And the fork is not cosmetic. Commit `800ebf5` (2022-02-16, *"fix inductive
constructor level constraint"*) corrects the side condition on the
nonrecursive-constructor-argument rule (`axioms.tex:125`, thesis §2.6.1) from
`ℓ' ≤ ℓ` to `imax(ℓ', ℓ) ≤ ℓ`. **That fix exists only on `master`. The published
PDF carries the old condition.**

> **RULING: this tier pins `digama0/lean-type-theory` at `master` `0ba1787`,
> and cites section numbers against it — never against the released PDF.**

A lane that mirrored "the thesis" meaning the published document would encode a
rule its own author has already corrected. This is §1.1 law 4 and §5.5's
generated-not-hand-maintained rule arriving in a bibliography, and it is exactly
the trap `docs/family-architecture.md` §2.5 sprang on the C tier — *three of five
ISO citations an edition out of date*. The family has now met this failure mode
in two tiers founded a day apart.

**(4) THE SPEC IS ALREADY BEHIND THE KERNEL.** The thesis predates structure
eta, the current accelerated-`Nat` set, and `Expr.mdata` as the kernel now
handles it. §2.2's 16 rules are measured at *our pin*; the thesis's 71 are
measured at *2019*. **Reconciling those two lists is the tier's first real
intellectual task**, and it is exactly the family's §4.2 divergence discipline:
the model states the spec's rule, the harness records what the oracle does, and
the disagreement is published as a finding.

### 7.3 Is the thesis formalized inside lean4lean?

**Partly, and the partition is measurable.** `Lean4Lean/Theory/` (with
`Theory/Typing/`) is an abstract formalization — `VLevel`, `VExpr`, `VDecl`,
`VEnv` and the typing judgments — which is the thesis's type theory rendered in
Lean. `Verify/` proves the executable checker meets it.

But **the correspondence between `Theory/` and the thesis's 71 rules is not
itself machine-checked**, and cannot be while the spec is a PDF with unnamed
rules. And the formalization is **incomplete exactly where §6.4 says**: the
inductive families are stubs.

So the answer to the "spec-is-formal" question is: **the spec is prose; a
hand-written Lean mirror of it exists, is incomplete, and its fidelity to the
prose is a human judgement nobody has instrumented.** That gap — a
census-backed, cited correspondence between the thesis's rules and a Lean
surface — is a contribution this family's apparatus is unusually well suited to
make, and §8 option (b) is where it lives.

### 7.4 THE CORRESPONDENCE MANIFEST — built, and 24% of the spec maps onto a stub

**Landed as M1 inch 4:** `harness/lean_rule_correspondence.py` →
`docs/lean-rule-correspondence.json`. This is §5.5's coverage manifest with the
clause replaced by the rule, and **nobody in the field has one** — the
correspondence between Carneiro's thesis and Carneiro's formalization is, today,
a human judgement recorded nowhere.

**The honest split, because a manifest that blurred it would be the drift it
exists to catch.** MECHANICAL: `Theory/`'s inductive constructor lists, and the
rule counts joined from `docs/lean-spec-census.json` — both re-derived every run,
and a change in either is DRIFT. DECLARED: the map from a thesis judgment to a
`Theory/` inductive, one cited row per family, living in the instrument where a
reviewer can argue with it. **The instrument refuses if a declared target
vanishes, if the map and the spec census disagree about which families exist, or
if the map fails to cover exactly the kernel-relevant rules** — so it cannot rot
silently.

| thesis family | rules | relation | realized by |
| --- | ---: | --- | --- |
| Typing | 7 | **FUSED** | `IsDefEq` (13 ctors) |
| Definitional equality | 10 | **FUSED** | `IsDefEq` (same inductive) |
| Is-a-type | 1 | defined, not inductive | `IsType` is a `def` |
| Context well-formedness | 2 | reshaped | `Lookup`, `Ctx.LiftN` |
| Level equality | 1 | **SEMANTIC** | `VLevel` |
| Level order | 14 | **SEMANTIC** | `VLevel` |
| Algorithmic defeq | 9 | partial | `IsDefEqStrong` |
| Head reduction | 10 **(elided)** | reshaped | `WHRed` (4), `StRed` (6) |
| Inductive specification | 1 | **STUB** | `VInductDecl` — 0 |
| Constructor | 5 **(elided)** | **STUB** | `VInductDecl` — 0 |
| Large elimination | 3 | **STUB** | `VInductDecl` — 0 |
| Subsingleton constructor | 8 | **STUB** | `VInductDecl` — 0 |

**Rules by relation, and this is the headline:**

| relation | rules | share |
| --- | ---: | ---: |
| **STUB** — no abstract specification exists | **17** | **24%** |
| FUSED into one inductive | 17 | 24% |
| SEMANTIC — replaced by a semantic relation | 15 | 21% |
| RESHAPED | 12 | 17% |
| PARTIAL | 9 | 13% |
| defined, not inductive | 1 | 1% |

> **Seventeen of the thesis's 71 kernel-relevant rules — one in four — map onto
> a file that is 7 lines long and contains two `sorry`s.** Measured, not
> characterized: `Theory/Inductive.lean` has 4 non-blank lines, and both of them
> that matter are `def VInductDecl.WF … := sorry` and
> `def VEnv.addInduct … := sorry`.

**COVERAGE IS DELIBERATELY NOT A PERCENTAGE**, and the instrument says so in its
own output. The two artifacts are not in a 1:1 relation, for three structural
reasons the manifest records separately from any row:

1. **Typing/defeq fusion.** `HasType` is *defined* as the diagonal of `IsDefEq`.
   Two thesis judgments, one inductive — so per-family counts cannot be compared
   directly, and any "N of 71 rules covered" figure would be arithmetic on
   incomparable things.
2. **Environment-carried defeqs.** `IsDefEq.extra` admits whatever equations the
   *environment* declares. **Delta, iota and quotient computation enter the
   theory as environment data rather than as inference rules** — so those thesis
   rules have no constructor to match, and are discharged when a declaration is
   *admitted* rather than when a term is *checked*. This is a genuinely elegant
   design and it makes naive rule-counting meaningless.
3. **Levels are semantic, not algorithmic.** The thesis's 15 level rules describe
   an algorithm; `Theory/` defines the relation that algorithm is meant to
   decide. Mirroring them means *proving the algorithm decides it* — which is a
   theorem, not a transcription, and it is why HEAD's coNP-hardness result
   (§6.2) is in this area.

**What the manifest is FOR, stated so it is not mistaken for a scoreboard.** It
does not say lean4lean is 24% incomplete — it says *where the specification
work is*, in the spec's own units, with a citation per row and a drift guard.
That is the artifact option (b) needs on day one and the one this tier can build
before writing a line of semantics.
---

## 8 THE CONVERGENCE: four measurements, one construct

Before the positioning, the census's single most important result. Four
instruments, run separately and for different reasons, all landed on
`Expr.proj` — projection out of a structure that may or may not be a `Prop`.

| # | measurement | what it found at `proj` |
| --- | --- | --- |
| 1 | **the kernel census** (§2) | `proj` is kernel-primitive with **three** separate mechanisms — its own typing rule enforcing a `Prop`-squashing side condition twice, its own reduction rule, and its own defeq congruence with a dedicated lazy-delta loop |
| 2 | **the spec census** (§7) | `proj` **does not exist in the thesis grammar at all**. The thesis has 7 expression forms; Lean 4 has 12. `proj` is the largest single divergence, and nothing in the 71 kernel-relevant rules describes it |
| 3 | **the lean4lean census** (§6) | `VExpr` has **6 constructors** and `proj` has **no abstract counterpart**. `TrProj` is a `sorry`, and **11 of the 24 shipped sorries cluster on projections** |
| 4 | **the arena scoreboard** (§9) | the **four soundness tests the official C++ kernel fails** are all `proj`/`rec`-over-`Prop`. lean4lean's only two accept-side failures are the same family, from the other direction |

**Read together: `proj` is the construct where Lean's kernel is provably
unsound today, where its specification is silent, where its verification is
blocked, and where its independent checkers disagree in both directions.**

That is not a coincidence and it is not bad luck. It is what happens when an
implementation grows a primitive the theory never had, at exactly the boundary
— `Prop` versus `Type` — that proof irrelevance makes delicate. **This is the
tier's target.** Any endgame Thomas picks should be judged first on whether it
moves this.

---

## 9 THE PRIOR ART — and the scoreboard endgame is ALREADY OCCUPIED

The Wasm charter's §8 discipline applies: survey before positioning, and let the
survey change the plan. It did, decisively.

### 9.1 The Lean Kernel Arena exists, is official, and runs daily

> **`leanprover/lean-kernel-arena` — created 2026-01-06, last pushed the day of
> this census. 22 checker definitions, 19 scored, 197 tests, regenerated by CI
> daily.**

This charter did not take its numbers on faith. The probe fetched the arena's
`results.json` (3.0 MB) and **this lane recomputed the entire scoreboard from
the raw rows** — 3 743 results over 197 tests, 19 checkers. Run
`2026-08-22 10:33:41 UTC`, revision `46414771`. Test outcomes partition as **124
`accept`, 67 `reject`, 6 `either`**.

| checker | accept | **reject (the soundness suite)** |
| --- | ---: | ---: |
| `mathgraph` (Rust) | 124/124 | **67/67** |
| **`lean4lean`** | 121/124 | **67/67** |
| `sokonanoda`, `zignodamus`, `official-nightly` | 124/124 | 66/67 |
| `nanoclo`, `kiota` | — | 66/67 |
| `nanobruijn`, `rpylean`, `evmlean` | — | 65/67 |
| `vow-lean-kernel` | 113/124 | 64/67 |
| **`official` (Lean v4.33.0 — OUR PIN)** | 124/124 | **63/67** |
| `nanoda`, `nyaya`, `official-v4.28.0` | — | 60/67 |
| `parse-only` (control) | 124/124 | 6/67 |

**THE HEADLINE, verified by this lane's own recomputation:**

> **The official C++ kernel at our pin rejects 63 of 67 soundness tests.
> `lean4lean` rejects 67 of 67. The four the official kernel accepts are all
> proofs of `False`.**

Named, because a claim this size should be checkable: `proj-of-stuck-prop`,
`proj-of-subst-prop`, `rec-missing-ih`, `rec-of-subst-prop`. Every one is
§8's construct.

**Three of the four are fixed on nightly. One is not.** `rec-of-subst-prop` is
accepted by **all three** official builds the arena scores — `v4.28.0`, our
`v4.33.0`, and `official-nightly` — and **rejected by all fifteen** other
checkers (verified by this lane against the raw results; the only other accepter
is the `parse-only` control, which rejects almost nothing by construction).

> **That is a live, currently-unfixed divergence in which the independent field
> is ahead of the C++ kernel, and it is the single strongest empirical argument
> this charter has.**

It is also a caution about our own pin: **our toolchain is one of the builds
that accepts it.** Every `.olean` in this repository was checked by a kernel
with a known, reproducible, currently-open soundness gap. That is not a reason
for alarm — the gap requires an adversarially constructed declaration that no
honest elaboration produces — but it is the concrete answer to "why would this
repository care", and it should be stated as fact rather than as motivation.

**This is the value proposition of an independent checker, already demonstrated,
already public, and not by us.** It is also the strongest possible argument
against the naive version of this tier: the thing a conformance scoreboard would
prove has been proved, and it is regenerated every day by the language's own
organization.

**One qualification, and it is the crack worth knowing about.** The arena is a
*test suite* scoreboard — 197 curated adversarial cases. It is not a sweep of
real libraries, and the ecosystem's coverage there is thinner than it looks:
**Mathlib's regular PR CI no longer runs `lean4checker` at all**, its own
workflow recording that it is *"quite expensive"*; it runs periodically instead.
So *"is every declaration in Mathlib independently re-checkable today"* is
**not** a question the arena answers, and it is not one anybody is answering
continuously. That gap is smaller than it sounds — the arena's checkers do run
against a 5.2 GB Mathlib export — but it is the seam where an option-(a) revival
would have something real to add, and §10.1 keeps the drift guard for exactly
that reason.

### 9.2 The field is large, alive, and mostly not Lean

The brief's premise — lean4lean, trepplein, nanoda — was three artifacts, two of
them legacy. Measured, it is a dozen-plus, and the two legacy ones are dead
while their successor thrives.

| project | language | licence | last commit | era | maintained |
| --- | --- | --- | --- | --- | --- |
| **`nanoda_lib`** | **Rust** | Apache-2.0 | **2026-08-18** | **Lean 4** | **yes** — the base six arena checkers fork from |
| `lean4lean` | Lean | Apache-2.0 | 2026-08-14 | Lean 4 | yes |
| `lean4export` | Lean | Apache-2.0 | 2026-08-21 | Lean 4 | yes |
| `trepplein` | Scala | Apache-2.0 | 2022-03-13 | **Lean 3** | **no** |
| `nanoda` (original) | Rust | **NONE** | 2021-03-06 | **Lean 3** | **no** — author-deprecated |
| `lean4checker` | Lean | Apache-2.0 | 2026-03-25 | Lean 4 | **deprecated**, merged into Lean |

**`trepplein` cannot be incrementally updated** and the reason is exactly §8's:
its `Expr` grammar is `Var, Sort, Const, LocalConst, App, Lam, Pi, Let` — **no
`Proj`, no `Lit`**, precisely the two constructors Lean 4 added. It appears zero
times in the arena.

**`nanoda_lib` is the correction the brief needed.** Actively developed, Lean 4,
and it hard-gates the export version to `>=3.1.0, <3.2.0` — exactly
`lean4export`'s current format. Its Apache-2.0 licence is what makes the arena's
fork ecosystem legally possible.

**Licensing is the field's weakest dimension, and it is measured.** The original
`nanoda`, `zignodamus`, `nyaya`, and — **the arena repository itself** — ship
with **no LICENSE file**. Under this repository's step-0 rule (§8 of the family
charter: a corpus carries its licence and provenance *at the registry row, not
later*), **the arena's test corpus cannot be vendored here.** It can be cited,
reproduced by running their harness, and pointed at. That is a real constraint
on any option that wanted to import their 197 tests.

### 9.3 The independence caveat, in the project's own words

The census found the sentence that governs the whole positioning, and it is
lean4lean's README describing itself:

> *"It is derived directly from the C++ kernel implementation, and as such
> likely shares some implementation bugs with it (it's not really an independent
> implementation)."*

**So a lean4lean-vs-C++ scoreboard is a differential-testing instrument, not an
independence argument.** The arena's `nanoda`-lineage checkers — written in Rust
from the export format, by different people — are the ones that carry
independence. This is the distinction §4.2 drew between `leanchecker` (same
kernel, catches environment hacking) and a genuinely separate implementation,
applied one level up.

---

## 10 THE ENDGAME MENU — priced, none chosen

Thomas's decision. Each option below is priced against the census, and the
recommendation is argued rather than assumed. **No option is started this
dispatch.**

### 10.1 Option (a) — the conformance scoreboard. **NOT RECOMMENDED.**

Run our own checker, or lean4lean's, against the C++ kernel over core → Std →
Mathlib, with family-style verdicts and drift guards.

**Priced:** cheap. §9.1's routes work today; the corpus is on disk at our exact
pin; the oracle is free (§5).

**Why not:** §9.1. This is the Wasm charter's *"competing with a 99.4%
incumbent"* paragraph, and worse — the incumbent is **the language's own
organization**, runs **daily**, and covers **19 checkers** where we would have
one or two. We would rebuild a public scoreboard to learn what its front page
already says. And we could not even use its corpus (§9.2, no licence).

**What survives from it:** the *method*. A `--compare` drift guard over the
arena's published results, so that when the arena's verdicts move, this
repository notices. That is an hour of work, not an endgame.

### 10.2 Option (b) — consume and extend lean4lean. **RECOMMENDED.**

Engage Mario's project seriously: adopt the executable checker, and contribute
the family's apparatus where the census says the gap is.

**What we would ADD, and every item is a measured gap rather than a guess:**

1. **The abstract specification of inductive types** — `Theory/Inductive.lean`'s
   two `sorry` stubs (§6.4). This is the blocker for `addDecl.WF`'s seventh
   case, and it is the single highest-value unwritten artifact in the field.
2. **`TrProj`, and the projection metatheory** — §8's construct; 11 of 24
   shipped sorries; the site of four live kernel unsoundnesses.
3. **The spec-mirror correspondence itself** — a census-backed, cited mapping
   from the thesis's **71 kernel-relevant rules** (§7.1) to `Theory/`'s
   definitions, with a `--compare` gate. **Nobody has this**, the correspondence
   is hand-maintained prose today. The instrument makes the scale of the job
   concrete: **the LaTeX names only 5 rules** (§7.1), so the correspondence
   cannot be a name match — it has to be built as a citation per definition,
   which is precisely §5.5's manifest shape. This is precisely §5.5's manifest,
   and it is the family's most transferable instrument.
4. **A drift guard on the spec's two heads** (§7.2 finding 3) — mechanically
   detecting that a citation points at the corrected `master` rule rather than
   the published PDF's wrong one.
5. **THE DIVERGENCE LEDGER AS A FORMAL ARTIFACT** — and this one is squarely
   this repository's own law. lean4lean's `divergences.md` is **hand-maintained
   English prose carrying real soundness arguments** (why `imax 1 u ≤ u` is safe;
   why comparing projections by index alone is sound given what `inferProj`
   already checked). Those are load-bearing claims with no mechanized
   counterpart, in the most safety-critical repository in the ecosystem.
   **That is exactly the "model always matches code" failure mode this
   repository treats as a blocker rather than a footnote**, and turning that
   ledger into checked statements is a contribution the family's apparatus is
   built for.

**What we would UPSTREAM:** all of it. Items 1 and 2 are `sorry`s in an
Apache-2.0 repository whose author documents his own gaps candidly; item 3 is an
instrument that serves his paper as much as our charter.

**The honest risks, recorded as the Wasm charter recorded its own.** (i) Mario
closes these himself — he is the world expert, he is active (88 commits in six
months), and the two hardest items are exactly what he has said is next. That is
a *good* outcome and should be checked for before starting, not after. (ii) The
work is genuinely hard: the inductive specification has been open since 2023 and
its absence is structural, not a matter of effort. (iii) We would be a
contributor to someone else's research programme, which is a different posture
from owning a tier. **(iv) And the governance is thinner than the project's
standing suggests** — measured: `lean4lean` is a **personal repository**, not
under the `leanprover` organization (unlike `lean4export`, `lean4checker` and
the arena, which all are); it has a **sole committer** across its recent
history; and the **Lean FRO's published Year 3 roadmap mentions none of
lean4lean, external kernel checkers, kernel verification, or the arena**, and
has no section on soundness or the trusted base. The official project treats it
as a *de facto* reference implementation — upstream fix PRs now routinely report
whether lean4lean shares the bug — **with no published commitment to adopt it.**
Depending on it is depending on one person's research project, and the charter
says so rather than letting a lane infer institutional backing from 228 stars.

### 10.3 Option (c) — an independent kernel-language surface on the family substrate. **EXPENSIVE; PRICED HONESTLY.**

Instantiate the family's own substrate — `SemM`, `Run σ α`, the verdict system —
for the Lean kernel, and build the surface from the thesis's rules.

**Priced against the census, and the number is not encouraging.** lean4lean is
**39 468 lines** with a **5.43** proof-to-executable ratio, by the author of the
specification, over three years, and its top-level theorem still has a `sorry`
in the seventh case. A from-scratch surface would re-derive that and would not,
on any realistic schedule, catch up.

**And the substrate fits poorly, which is worth stating because it is a finding
about the family and not just about this tier.** `Run σ α` and `SemM` are built
for *interpreters with fuel over a mutable world*: `.timeout` is fuel
exhaustion, `W` carries the heap, effects are world data. A typechecker is a
different animal — a recursive decision procedure over an immutable environment,
returning `Except`. Some of it maps (`.unsupported` → REFUSE; the kernel's own
recursion-depth guard → `.timeout`, and lean4lean does use fuel counters). Much
of it does not: there is no world, no effects, no schedule, and §3.1 says no
nondeterminism. **A tier that forced this subject into the family's monad would
be measuring the substrate and calling it the kernel** — which is §0.1 principle
I's failure mode, pointed inward.

**What is genuinely ours in this option, and it is not nothing:** an independent
implementation is the only thing that buys the independence §9.3 says lean4lean
does not have. But the arena already has six independent Rust checkers, and
`mathgraph` already scores 124/124 + 67/67. The marginal independence of a
seventh is small.

**Recommendation: do not take (c) as an endgame.** Keep it as the answer to one
question — *what would it cost to own this outright* — now answered with a
number.

### 10.4 Option (d) — the TRUST-EXTENSION surface. **The genuinely unoccupied ground.**

This option did not exist when this lane was dispatched. The census produced it,
and it is the one place where the census found **no incumbent at all**.

**The finding, in one line:**

> **No external checker can check a `native_decide` proof — at all.** Not
> lean4lean (it hard-refuses `reduceBool`), not `nanoda`, not any of the arena's
> nineteen. The arena encodes this structurally with a *decline* mechanism
> rather than a verdict, and Lean's own reference manual says the same thing.

So the ecosystem's differential-checking story, which §9.1 showed is otherwise
strong and daily, has **exactly one hole**, and it is the hole Thomas's decide
ladder was written about.

**The evidence that this is live, not theoretical:**

* **Documented `False` proofs via the trust extension**, measured from upstream:
  a 2022 miscompilation of negative half-word ints on Intel macOS; a 2024
  constant-folding bug dropping modular reduction; a 2024 `UInt64` miscompile.
  Plus **attribute smuggling** — `@[csimp]` ignoring universe parameters gave a
  provable `False` through `trustCompiler` in 2025, and a related issue is
  **still open**.
* **Upstream is actively restructuring this**: RFC *"One axiom per native
  computation"* opened 2026-01-28 and closed **2026-02-03** — which is why §2.4's
  deprecation attributes are dated **2026-02-01**. The stated goal is that proofs
  using native computation carry *one axiom per computation*, so a reader can see
  exactly what was assumed.
* **That is this repository's decide-ladder ruling, arrived at independently by
  the Lean project, in the same week.**

**What the tier would contribute:** a Lean surface for the trust extension
itself — modelling `ofReduceBool`/`ofReduceNat` as what they are, an oracle
whose verdicts are assumptions — plus the scoreboard machinery to say, of any
environment, **exactly which of its theorems depend on a native computation and
which native computation**. That is a `#print axioms` refinement with teeth, and
it is what would let a rung-3 use carry a *checkable* receipt rather than a
prose one.

**Why it is attractive:** small, unoccupied, directly aligned with a ruling
Thomas already made, and it composes with option (b) rather than competing.
**Why it is not the headline recommendation:** it is narrow, and it does not
move §8's construct.

### 10.5 The reflexive capstone — a MILESTONE, reachable from any option

Stated separately because it is not an alternative to (a), (b) or (c) but a
destination any of them can reach, and because §0 has already priced its
honesty.

> **Every `.olean` this repository produces is checked today by a 7 888-line
> C++ artifact. The capstone is to check them with an artifact whose agreement
> with a written specification is proved in Lean.**

**What it would actually deliver, stated without inflation:** trust in this
repository's own proof estate reduced from "a C++ program we did not write" to
"a formal spec + a proved checker + a compiler". **Not eliminated** — §0's
enumeration of what remains trusted stands, and the compiler is on that list.

**Its cheapest honest form is reachable now**, and this is the useful part: run
an independent checker over this repository's own `.olean` output as a gate.
That is a real reduction in what the repository takes on faith, it costs a CI
job, and it does not require any theorem at all. **Option (b) then upgrades the
checker's warrant over time**, which is the right order — the gate first, the
proof after.

### 10.6 The recommendation, and its first milestone

**Take (b), with (d) as its natural companion, (a)'s drift guard as a free
rider, and §10.5's capstone as the milestone.**

The argument in one line: **(a) is occupied, (c) is priced out, (b) points at
the exact construct four independent measurements identified, and (d) is the
only ground in the field with no incumbent.**

The two recommended options divide cleanly and do not compete for the same
files: **(b) is the hard, high-value, long-horizon work** on someone else's
repository; **(d) is small, ours, and finishes.** A lane that wanted one
publishable result this quarter should take (d); a lane willing to work on the
field's hardest open problem should take (b).

**M1, planned as inches, endgame-neutral by construction** — every inch below is
useful under **all four** options, which is the property that makes it safe to
start before Thomas decides:

| inch | deliverable | why it is neutral |
| --- | --- | --- |
| **1** | **the kernel-vocabulary census + instrument. LANDED** (this dispatch) | the vocabulary is the vocabulary under every option |
| 2 | **the toolchain reconciliation, measured**: install `v4.33.0-rc2`, build `lean4lean` under the lock, run its own test suite. Report buildability — currently **NOT MEASURED** | every option needs a working checker on this box |
| 3 | **the spec-rule instrument** — `harness/lean_spec_census.py` over the thesis LaTeX at pinned `master 0ba1787`, emitting the **71 kernel-relevant rules** with `--compare`. **LANDED** (this dispatch) | item 3 of option (b) and §5.5's manifest; the only artifact that makes any spec-mirror claim checkable |
| 4 | **the correspondence gate** — map the 71 rules onto `Theory/`'s definitions and publish the coverage. **LANDED** (this dispatch, §7.4): 24% of the spec maps onto a 7-line stub | the deliverable nobody in the field has |
| 5 | **the axiom-dependency instrument** — for a given environment, report which theorems depend on a native computation and which one. Option (d)'s first artifact | a `#print axioms` refinement; useful under every option, and it is the receipt §0.1 II(a) asks a rung-3 use to carry |
| 6 | **the reflexive gate** — run an independent checker over this repository's own `.olean`s in CI, `maybe`-guarded | §10.5's cheapest honest form; pure gain, no theorem required |

**Inch 2 is the first real fork** and should be reported before inch 3 starts:
if `lean4lean` does not build on this box, options (a), (b) and the inch-6 gate
all need rescoping, and Thomas should hear that immediately rather than at the
end of M1.

**Inch 6 is the one with standing value regardless of the endgame.** Even if
Thomas founds no tier at all, running an independent checker over this
repository's own output is a real reduction in what the estate takes on faith,
and §9.1 measured the reason: **our own pinned toolchain accepts a proof of
`False` that fifteen other checkers reject.**

---

## 11 STILL OWED BY THOMAS

Named, so they are decisions rather than drift.

1. **The endgame.** §10's menu — **four** options, none chosen. The
   recommendation is **(b) with (d)**; the argument is §8, §9.1 and §10.4.
   Option (d) did not exist when this lane was dispatched; the census produced
   it, and it is the only ground with no incumbent.
2. **Whether this tier is founded at all, and in what order against the five
   other tiers founded this week.** §9 of the family charter reserves this.
3. **The registry row's edition token.** §12 proposes `Lean433` and explains why
   the choice is genuinely awkward here — Lean has no editions, only releases,
   and §1.1 law 3 says an edition token *"names an edition a reader can hold …
   never a point release"*. This tier may be the family's first legitimate
   exception, and that is Thomas's call, not this charter's.
4. **Whether we engage Mario Carneiro directly.** Option (b) is a contribution
   to someone else's project. The repository has no precedent for that posture
   and it should be an explicit decision, not a side effect of a merge.
5. **Whether the arena's corpus may be used** despite having no licence — by
   running their harness rather than vendoring their tests. §9.2.

---

## 12 THE REGISTRY ROW — PROPOSED

| field | value |
| --- | --- |
| language | Lean |
| `<Lang>` | `Lean` |
| authority | **SPEC-MIRROR** — Carneiro, *The Type Theory of Lean*, pinned at `digama0/lean-type-theory` **`master 0ba1787`** (§7.2), **cite-never-vendor: no licence** |
| edition tokens | **`Lean433` — PROPOSED, and see §11.3** |
| oracle | the **C++ kernel** at the pinned toolchain — and, uniquely in this family, **the program that checks the tier** |
| corpus | core `Init`/`Std`/`Lean` (**2 322 modules, 206 644 declarations**) and Mathlib (**8 268 files**, at our exact pin, already on disk) — **licence: Apache-2.0 both** |
| envelope | **adopt `lean4export` NDJSON format 3.1.0** (§4) — do not design one |
| state | **founding** |

**Two rows are unusual enough to flag.** The *oracle* is the program that checks
every artifact in this repository, so this tier's differential is free and its
DIVERGE is the family's highest-stakes (§3.2). And the *edition token* is
genuinely hard: §1.1 law 3 forbids point releases, but Lean has nothing else —
no ISO editions, no ECMA years. The honest options are a release-pinned token
(`Lean433`, accurate and law-3-violating) or a format-pinned one
(`Export31`, law-3-clean but naming the envelope rather than the language).
**Flagged, not decided.**

---

## 13 WHAT LANDED WITH THIS CHARTER

* **`harness/lean_rule_correspondence.py`** — the spec-mirror correspondence
  manifest (M1 inch 4): §5.5's coverage artifact with the clause replaced by the
  rule. Mechanical on both sides, with the editorial map declared in-instrument
  and guarded three ways. `--compare`, double-run byte-identical, **five refusal
  paths RUN**.
* **`docs/lean-rule-correspondence.json`** — its output. **17 of 71
  kernel-relevant rules (24%) map onto a stub**; coverage deliberately not
  reported as a percentage, with the three structural reasons recorded.
* **`harness/lean_spec_census.py`** — the spec-rule instrument (M1 inch 3).
  Pinned-commit enforcement with a deliberate `--allow-unpinned` override,
  `--compare`, double-run byte-identical, **six refusal paths RUN**. Declares its
  own two known undercounts rather than leaving them to be discovered.
* **`docs/lean-spec-census.json`** — its output. 167 typeset rules, **71
  kernel-relevant across 12 families**, 5 named rules, 2 elided families.
* **`docs/family-architecture.md` §3.4.1** — the substrate FIT BOUNDARY scope
  note, contributed upward: the substrate is for interpreters, and a tier whose
  subject is a judgment rather than a run should say so in its charter rather
  than discover it at founding-checklist step 7.
* **`harness/lean_kernel_census.py`** — the kernel-vocabulary instrument.
  Two-input (Lean datatypes + C++ rules), version-agreement enforced,
  `--compare`, double-run byte-identical (verified), **six refusal paths RUN**
  with their exit codes. Not wired into CI: the C++ half is an out-of-tree
  corpus, and §5.4 says a permanent SKIP is a check pretending.
* **`docs/lean-kernel-census.json`** — its output. 12 `Expr` / 6 `Level` / 7
  `Declaration` / 8 `ConstantInfo` / 16 reduction rules / 15 accelerated `Nat`
  ops / 15 kernel exceptions / 7 axioms with their deprecation dates.
* **`docs/lean-tier-charter.md`** — this document.
* **`docs/backlog.md`** — the record.

**No Lean, and no change to any existing file.** Nothing in this dispatch can
break a build, and no build was taken: the machine-wide lock was held by another
lane throughout and this charter needed none.

### 13.1 What this charter did NOT verify

Stated because the rest is measured and honesty about the edges is the point.

* **`lean4lean` was never built and never run by this lane.** Its coverage,
  sorry counts and theorem statuses are read from its source; its arena scores
  are recomputed from the arena's published `results.json`, not reproduced by
  running it. Buildability on this box is **NOT MEASURED** and is M1 inch 2.
* **`lean4export` was never built and no export was ever run.** The Mathlib
  export cost in §5 is an **order-of-magnitude estimate** with its basis stated.
* **Mathlib's declaration count is NOT MEASURED** — the probe declined it on
  measured memory pressure (load average 15.73, ~34 MB free) rather than risk
  another lane's build. The keyword approximation is labelled as one.
* **`leanchecker` ships at our pin and was not executed.**
* **The lean4lean paper's section numbers are UNVERIFIED** — body content came
  from the arXiv HTML, not the PDF. The abstract is verified.
* **No number in §9.1 came from running a checker.** They are this lane's
  recomputation of someone else's published measurements, and are attributed.
  The *recomputation* is ours and was done from the raw 3 743 rows — the
  aggregation is verified, the underlying runs are not.
* **§3.3's bug history is read from upstream issues and PRs; no exploit was
  reproduced.** The classification into "admits an axiom-free proof of `False`"
  versus "kernel bug without demonstrated `False`" follows what those issues
  themselves claim.
* **The Lean 3 era is NOT MEASURED**, and absence of found bugs there is not
  evidence of absence — those trackers are largely migrated or archived.
* **Mathlib's 308 129 declarations is a third party's published figure** at a
  February 2026 commit, not our count and not at our pin.
* **The arena's wall-clock timings are theirs**, and they disagree with the
  lean4lean paper's own speed claim by roughly 4× (§6.6). This charter records
  the disagreement and resolves nothing.
* **One Zulip thread cited in lean4lean's `bugs-found.md` could not be read**
  (the client does not render without JavaScript); only the link text was seen.
