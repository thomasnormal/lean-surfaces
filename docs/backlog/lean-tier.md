# Lean tier — lane backlog

Per-lane file per `docs/family-architecture.md` §9.5. Ids are
`YYYY-MM-DD-lean-tier-<n>` and need no reservation. Landings before this file
existed are in the archive as §L79 (founding charter) and §L85 (M1 complete).

---

## 2026-08-22-lean-tier-1 — §9.1 audited against this lane's six instruments; the one real defect was found twice, and the audit lane landed first

The standing strategy's **BUG BEFORE REFACTOR** clause, run against this lane's
six instruments. Two defects are named in §9.1. This lane had exactly one of
them, in exactly one instrument — and **found it independently of, and slightly
later than, the audit lane, which had already fixed it.**

### The `--compare` exit-0-on-drift bug: NOT PRESENT here

§9.1 names `c_construct_census`, `wasm_spec_census` and `wasm_suite_census`.
None of this lane's instruments is on that list, and the absence was **verified
rather than assumed**:

* all five `--compare` implementations return `1` on drift and `2` on a missing
  baseline — audited by reading every return path;
* `lean_rule_correspondence.py` was **run**: clean compare exit 0; perturbed
  baseline → `DRIFT: thesis_kernel_rules`, exit **1**.

The other four could not be re-run this dispatch — two need corpora a harness
restart destroyed (the C++ kernel checkout and the thesis clone), and two invoke
Lean, which amendment 11 puts behind a ticket. Their drift paths were exercised
when they landed; this is that record, not a fresh run, and it is stated as such.

**Independently corroborated:** the audit lane's own fix commit touched
`c_construct_census`, `es_census`, `wasm_spec_census`, `wasm_suite_census` and
one file of this lane's — and **left the other five of ours alone**. Two audits
from different directions agree on which instruments were clean.

### The `git_rev`-swallow bug: PRESENT in `lean_independent_check.py` — and FIXED UPSTREAM, not here

§9.1's second defect — *"copies of a 6-line `git_rev` that all swallow their
failure and stamp `null` provenance"* — had an instance in this lane's
`lean_independent_check.py`:

```python
rev = ""
try:  ... git rev-parse ...
except (OSError, subprocess.SubprocessError):
    pass
```

An `except: pass` stamping an empty `checker_commit`. A direct breach of the
never-hide-errors law, and **worse in this instrument than in most**, because the
artifact's entire claim is *"checker X accepted these modules"*. A verdict file
that cannot say **which X** is not weak evidence — it is no evidence.

**This lane wrote a fix and then discarded it.** The audit lane had already
landed one in `28b9f5e`, and on rebase the two collided. Theirs is semantically
identical and **strictly better written**: it folds the empty-output case into
the same condition and surfaces git's own stderr, so the refusal reads
`(exit 128): fatal: not a git repository` instead of a bare assertion that the
directory is not a checkout. Taking ours would have been churn on top of a
landed, tested fix.

**What this lane contributed instead is verification**, re-run against their
version: a non-git directory carrying a fake `lean4lean` binary exits **2**, and
the check sits above the module loop, so **no checker process is ever spawned** —
the refusal costs nothing and cannot half-run.

**Output is byte-identical for a valid checkout** (§9.2's test), shown without a
Lean run: the real checkout's `git rev-parse` and the committed
`docs/lean-independent-check.json` both read `e0e3f6bcccb8`. The fix changes
behaviour only where there was no provenance to record.

**One detail worth keeping.** This lane's other three git helpers already raised.
The defect was in the **newest** of the six, written last and fastest — the
ordinary shape of this failure, and a concrete argument for the shared helper
§9.1 asks for, since the defect reappears per-copy rather than persisting in one
place.

### Adoption status for the rest of §9

* **`harness/censuskit.py`** — not in the tree yet; nothing to adopt. Per §9.2
  this lane converts **on next touch** of each instrument, with the
  byte-identical test.
* **`tools/triad.sh`** — adopted for any future build. Noted: its header
  **recovered amendment 8**, which the prose register had lost — the audit's
  script-beats-prose thesis demonstrated on the register itself.
* **Amendment 13 CoW seeding** — adopted for the next workspace. This lane paid
  the cost A13 removes in full this dispatch, re-cloning from scratch after a
  harness restart destroyed its tree.
* **Per-lane backlog** — this file. `docs/backlog.md` untouched; converting it to
  a generated index belongs to the migration commit, not to a lane's landing.

### Deferred, unchanged

**Mathlib export: BLOCKED** — needs the coordinator's sign-off and Thomas's
training finished. §5's own pricing already said peak RAM is the binding
constraint, which is exactly what the 3 GB RSS line governs. **Inch-6 gate over
our own `.olean`s: awaits a quiet machine** — a ~3 700-job build that would hold
the machine's entire Lean allowance.

No Lean run, no build, no ticket taken for this landing.

---

## 2026-08-22-lean-tier-2 — M2 OBLIGATION CENSUS: 24 sorries are 3 missing DEFINITIONS, and two of the three are already being written by strangers

Thomas ruled the endgame **(b) CONSUME-AND-EXTEND** — *"no reason to copy
lean4lean; if we can reuse most of it that sounds good."* Option (d), the
trust-extension surface, stays registered as the companion after (b)'s first
milestone. The edition token **`Lean433`** is **RATIFIED** as the family's first
§1.1 law-3 exception: Lean has no editions, only releases, so the law's premise
is false here — recorded with its reasoning in charter §12.1.

M2's deliverable: `docs/lean4lean-obligation-census.md` +
`harness/lean4lean_obligation_census.py` + its JSON.

### The counting rule, and the delta is a finding

**138 raw / 113 real / 25 comment-only.** A raw grep overstates the load by
**22%**, concentrated in docstrings and commented-out attempts. The stripper
handles nested `/- /- -/ -/`, docstrings, line comments and escaped string
literals while preserving line numbers; 11-case `--selftest`, nesting included.

### All three M1 figures re-verified: two confirmed, one wrong

24 shipped sorries **CONFIRMED**; 89 experimental **CONFIRMED** (24+89=113); the
two-stub `Theory/Inductive.lean` **CONFIRMED verbatim**; partition line counts
identical. **"11 proj-related" was WRONG — it is 10.**

### The structural finding

**24 obligations are 3 definitional stubs + 21 theorems, and 14 of the 21 are
blocked by a stub.** `TrProj` is `def … := sorry` — the relation does not exist —
and it alone gates **11 of 21 (52%)**. The seven `TrProj.*` lemmas are not seven
hard proofs; they are statements about nothing. **Writing `TrProj` is a
definition task, not a proof task.**

### The dependency graph is SEMANTIC, not nominal

Two obligations that look independent by name are not, and only reading the
executables found it: `tryEtaStructCore.WF` builds `.proj` terms directly;
`reduceRecursor.WF` reaches `.proj` **transitively**, two call hops away via
`toCtorWhenK → expandEtaStruct`. A name-prefix analysis put a blocked theorem at
the top of the candidate list. Both edges are now declared in the instrument with
the reasoning attached.

The corner table also found a bug in itself: a path-based classifier filed all
seven `TrProj.*` lemmas as "other" because they live in a generically-named file,
making the census's largest cluster invisible in its own summary. Name rules now
run first.

### The active-work split changes the plan

**DO NOT ENTER:** inductive types (open PR #43 replaces both stubs), `addDecl`
surroundings (PR #32, updated the day of the census), injectivity, universe
levels (11 commits on one day this month), church-rosser.

**UNTOUCHED, ranked:** (1) **`TrProj`** — no branch, no PR, no issue; `sorry`
~15 months; dependent lemmas from 2023. (2) `isDefEqUnitLike.WF` /
`tryEtaStructCore.WF` — 11 months idle, *partly* gated on (1), and this census
says precisely which half: `isDefEqUnitLike` is free, `tryEtaStructCore` is not.

**THE CHARTER'S "SEAM" CLAIM IS NOW STALE.** M1 §6.4 called
`Theory/Inductive.lean` the highest-value unwritten artifact in the field; three
weeks later there is an open PR filling it. A lane that had started there on the
charter alone would have duplicated a stranger's work. That is the argument for
running the activity check *before* choosing a target.

### The injectivity trap — a stale docstring nearly set our direction

M1 quoted `Injectivity.lean`'s *"theorems which we can't prove :("* and concluded
these were hard-and-avoid. **Wrong: injectivity is already proved sorry-free on
master**, for the `SExpr` development — and `Theory/`/`Verify/` contain **zero**
`import Lean4Lean.Experimental`. The open work is the SExpr→VExpr port, which is
the author's obvious next move. The right conclusion (avoid) survives; the reason
was wrong and the header predates the proof.

Related measurement hazard: the `logrel` branch reports 42 commits "ahead" but
was **rebased onto master with new SHAs**. **A branch-ahead count is not evidence
of unmerged work here**, and every "untouched" verdict inherits that caveat.

### Two traps recorded for any future run

**`sorry` → `axiom` laundering:** the `types2025` branch converts eight sorries
into `axiom`s with `-- := sorry` kept as a comment — zero proof content. A
sorry-counter run there would report an improvement that did not happen. This
instrument counts axioms alongside sorries for exactly that reason.
**Recency that discharges nothing:** several sorry-bearing files show August
dates from toolchain bumps and a namespace move; the *site* blame is the honest
signal, and several are from 2023.

### Candidate first proof

**`isDefEqUnitLike.WF`** — the independent half of the second-ranked untouched
cluster: 9-line subject, no proj dependency (verified directly and
transitively), one waiting consumer in the same file, 26 proved analogues around
it at a median of 15 lines, and it realises `unit-like`, one of the 16 named
kernel rules in `docs/lean-kernel-census.json`. `checkPrimitiveDef.WF` was
**disqualified mid-census** when the activity data showed PR #32 touching it.

### Governance, for the engagement decision

Nine external proof PRs unanswered; one maintainer reply across eleven; no
published open-problems list; and **Thomas's own issue #16 — asking exactly which
sorries are unclaimed — open 23 days with zero replies.** No contact was made by
this census; engagement remains Thomas's call.

### Discipline

No Lean run, no build, no ticket. M1 inch 2 already built this commit green in
98 s and that is cited rather than repeated. Public reading only. Deferred items
unchanged: Mathlib export blocked; inch-6 gate over our own `.olean`s awaits a
quiet machine.

---

## 2026-08-22-lean-tier-3 — M3 inch 1 WITHDRAWN: the candidate first proof is blocked on a MISSING MODEL RULE, and my own M2 census recommended it

M3 was ranked: (1) prove `isDefEqUnitLike.WF`, (2) `TrProj` the definition. **Inch
1 is not available, and the census that recommended it was wrong.** No proof was
forced and no trusted definition was quietly extended to make one go through.

### The measurement

`isDefEqUnitLike.WF` must conclude that two arbitrary inhabitants of a unit-like
inductive are definitionally equal. **`VEnv.IsDefEq` has 13 constructors and none
of them can conclude that.** Walked individually: `eta` is *function* eta;
`proofIrrel` requires `.sort .zero` so it only reaches `Prop`; `extra` admits
only what `env.defeqs` carries, and that is populated from exactly two checked
places — δ-unfolding (`Theory/Typing/Env.lean:15-16,26,31`) and the quotient
package (`Theory/Quot.lean:21`). No lemma in `Theory/` concludes defeq of two
arbitrary inhabitants.

Cross-checked against this tier's own M1 instruments, which is what makes it firm:

| source | unit-like rule? |
| --- | --- |
| C++ kernel (`lean-kernel-census.json`) | **YES** — `is_def_eq_unit_like`, and separately `try_eta_struct_core` |
| the thesis (`lean-spec-census.json`) | **NO** — names only β, δ, η, ι, ζ |
| lean4lean's model | **NO** — 13 constructors |

**These are SPEC-GAP obligations, not proof obligations.** The rule exists in the
kernel, is absent from the 2019 spec, and is absent from the model that mirrors
that spec. Proving the theorem requires first *adding a rule to the model* — a
change to a trusted definition. That is why both `IsDefEq.lean` sorries have
stood eleven months with no claimant, and it is a better explanation than
"nobody got round to it".

### The method error, and it is mine

M2 introduced the semantic-dependency lesson and then committed a second instance
of it. My dependency check asked *"does the executable touch `proj`?"* — about
the **implementation**. It never asked *"does the model contain a rule that could
make this theorem true?"* — about the **specification**. Corrected triage rule,
now in the census: check **(a)** is the definition it needs present, **(b)** does
its executable reach a blocked construct directly or transitively, **(c)** can
the model discharge its conclusion at all. **(c) is the cheapest of the three and
it eliminated two candidates instantly.**

### Consequence: every independent obligation is unavailable

Injectivity ×3 and `NormalEq.parRed` ×2 and `checkPrimitiveDef.WF` are all DO NOT
ENTER (author's port; the `.extra` case circled by his own work and PR #43; PR
#32 updated the day of the census). `isDefEqUnitLike.WF` is blocked on the
missing rule; `tryEtaStructCore.WF` is blocked twice, on that **and** on `TrProj`.

There is no available first proof of the shape M2 proposed. Forcing one would
mean racing the author or quietly extending a trusted definition. Both refused.
**This promotes inch 2 from "highest-leverage" to "the only available item"** —
which is where the ruling already pointed.

### Inch 2 — the `TrProj` design census (census-first, not started)

What must be matched, from the kernel: `reduceProjCore` selects
`args[numParams + i]` from a constructor application; `inferProj` walks the
constructor telescope instantiating **earlier fields as `proj I j s`** (dependent
projections) and enforces the `Prop`-squashing side condition **twice**.

What the thesis offers: **nothing.** `proj` is absent from its 7-form grammar and
from all 71 kernel-relevant rules. So "match both sources" resolves
asymmetrically — design against the kernel, then write it *as the rule the thesis
would have had* so it can be cited into the §7.4 correspondence manifest.

`VExpr` has 6 constructors and no `proj`, so the projection must be **encoded**.
Three candidates, two rejected with reasons: **(a) recursor encoding — REJECTED**,
it needs `VInductDecl.WF`/`addInduct`, i.e. PR #43's territory, which the ruling
excludes; **(b) projection-constant encoding — REJECTED**, those are derived
declarations that need not exist, and `proj` is primitive precisely to avoid
them; **(c) reduction-relational — RECOMMENDED**, mirrors `reduceProjCore` and
`inferProj` and stays clear of both live PRs.

**The crux, and it is where the kernel is unsound.** The hard case is a STUCK
projection, and `proj-of-stuck-prop` / `proj-of-subst-prop` are two of the four
arena soundness tests **our own pinned kernel fails**. So `TrProj`'s hardest case
is the case the reference implementation gets wrong, and the design question —
model what the kernel *does*, or what it *should do*? — has to be settled before
any code. §4.2's precedence rule answers it (state the rule, record the oracle's
behaviour, publish the divergence), but this is the first time in this tier that
rule has teeth.

### Hygiene

No PRs, no comments, no contact upstream — engagement remains Thomas's call and
he has personal standing via issue #16. Work stays in our own clone. The
axiom-counting rule is now in the instrument's docstring **as the trap it
prevents**, with the measured `types2025` evidence: eight sorries converted to
`axiom`s with `-- := sorry` kept as a comment, zero proof content — a
sorry-counter run there reports an improvement that did not happen.

No Lean run, no build, no ticket taken this dispatch: the finding is a source
measurement, and the C++ kernel side was taken from our own committed
`lean-kernel-census.json` rather than re-fetching a wiped corpus.

---

## 2026-08-22-lean-tier-4 — the crux ruling CONFIRMED, and inch 2 blocked one level deeper: the model cannot say "constructor"

The crux was ruled: `TrProj` models the SOUND rule. Two verifications were run
before writing. The first confirmed the ruling. **The second stopped the work.**

### The sound rule is verified, and lean4lean already implements it

The arena's own mechanism note for `proj-of-stuck-prop` names **two** defects: a
hash-gated defeq cache, and — the part that matters — the `is_prop` test not
requiring the inferred type to **reduce to a sort**, so a *stuck* sort read as
"not a Prop" and a `Bool` field was projected out of a proposition. Upstream
fixed the projection half in lean4#14807 and the cache half in #14806;
`proj-of-subst-prop` is the same projection **reached without the cache**, so the
projection defect stands alone.

Cross-checked at source, which is what the ruling asked for: lean4lean's
`getSortLevel` goes through `ensureSortCore`, which whnfs and then **throws
`.typeExpected`** if the result is not a sort. `isProp` is
`(getSortLevel e).isAlwaysZero`, and `inferProj` calls it on the structure type
before permitting anything. **A stuck sort refuses rather than reading as
non-Prop — the artifact we are extending already implements the rule the ruling
selected**, which is why it scores 67/67 where our pinned kernel scores 63/67.

### The blocker: `VEnv` holds no constructor information

`TrProj` must relate a structure to its i-th field, which needs S's constructor,
parameter count and field types. Measured, `VEnv` has exactly two fields:
`constants : Name → Option VConstant` (and `VConstant` is `{uvars, type}` — a
type, nothing more) and `defeqs : VDefEq → Prop`. **No constructor table, no
inductive table, no fields.**

`VInductDecl` does carry the data (`VInductiveType extends VConstVal` with
`ctors`), but the ONLY route into a `VEnv` is `VEnv.addInduct`, which is `sorry`,
and `VDecl.WF.induct` (Theory/Typing/Env.lean:43-46) requires it. **A well-formed
environment containing an inductive is not currently constructible in the model.**

**So `TrProj` is not a peer of the inductive stubs — it is DOWNSTREAM of them.**
M2 recorded three independent definitional stubs; measured, there is ONE root,
the inductive specification, and TrProj sits below it. Corrected structure:
`addInduct`/`VInductDecl.WF` gates the 2 inductive obligations **plus TrProj plus
TrProj's 11** — **13 of 21 behind a single root**, and that root is PR #43's.

### The conflict this exposes

The ruling's two constraints — take the untouched complement, do not touch PR
#43/#32 territory — **cannot both hold for TrProj**, because the untouched item
is downstream of the in-flight one. Not a defect in the ruling; a fact the census
had not yet measured when it was made.

**No definition was written.** Doing so against a model that cannot express
"constructor" would mean either inventing an inductive interface (PR #43's job,
done worse and in parallel) or characterising constructors structurally from
their types — which is **unsound**, since any function into S would qualify.

### What is available — for Thomas, not started

Write `TrProj` **parametrically**, against an assumed constructor interface (the
`VConstVal` and `nparams`) rather than against `addInduct`'s implementation. It
touches none of PR #43's files, composes with whatever `addInduct` becomes, and
carries the §10.1 side condition — the genuinely novel part, independent of the
inductive representation. Needs confirmation first, because it converts an
"untouched item" into work adjacent to something in flight.

### The tier's central fact, now stated

Two withdrawals in one dispatch — no model rule (§8), no model constructors
(§10.2) — share one cause:

**lean4lean's MODEL is further from Lean's kernel than its EXECUTABLE CHECKER
is.** The checker handles projections, unit-like types and structure eta
correctly today. The model has none of them, and no inductives. Every obligation
needing one is a specification gap wearing a proof obligation's clothes.

### Discipline

Work stayed on a local branch `lean-surfaces/trproj` with no upstream tracking;
no PR, no comment, no contact. The arena's test corpus was sparse-fetched
(3.4 MB, `df` first per A11: 199Gi free) and read only. No Lean run, no build, no
ticket taken — both verifications were source measurements, so the queued rebuild
was never needed and the machine (queue depth 5) was left alone.

---

## 2026-08-22-lean-tier-5 — `TrProj` written PARAMETRICALLY, under explicit approval to take adjacent-to-in-flight work

### The rule that bends here, and why it is said rather than smoothed

The endgame ruling gave this lane two constraints: **take the untouched
complement**, and **do not touch PR #43/#32 territory**. Entry 4 measured that
they conflict for `TrProj` — the untouched item is *downstream* of the in-flight
one, because a projection needs constructor data and `VEnv.addInduct` is the
only route to it.

**This landing takes adjacent-to-in-flight work under explicit coordinator
approval.** The untouched-complement rule bends because the census found a
conflict the ruling did not know about when it was made. Recording that plainly
is the point: a lane that quietly widened its remit and called it the complement
would have been doing something else than what was authorised.

### What was written — `docs/lean4lean-trproj-parametric.lean`, 148 lines, 0 sorries

Verified sorry-free **by this lane's own obligation instrument**, which is the
right use of it: raw 3, **real 0**, all three hits prose in the docstring
explaining that `TrProj` is `sorry` upstream.

**The minimal assumed interface** is `ProjIface`, and it is exactly two fields —
`nparams` and `nfields` per structure name. Deliberately excluded, because a
projection does not consume them: the constructor's name, its type, the universe
parameters, the inductive's indices. Anything more would be a guess about how
`addInduct` will represent things. The file marks it in-line as **AN ASSUMPTION
TO RECONCILE**, and states that reconciliation is a **substitution** — swap in
the real environment lookup and re-instantiate — never a redesign. Every theorem
is proved for an *arbitrary* `ProjIface`, which is what makes that true.

**The sound side condition is the definition's centre**, as required, and it is
the genuinely novel, representation-independent part:

* `structSortReduces` — the structure's type must **reduce to a sort**. A stuck
  sort is a refusal, never a silent "not a `Prop`".
* `propSquash` — where the structure is a proposition, the projected field must
  be one too.

**Witnesses cited in-file**: the arena's `proj-of-stuck-prop` and
`proj-of-subst-prop`, proofs of `False` accepted by the official kernel at
v4.28.0, v4.29.1, **v4.33.0 (our pin)** and nightly; and the upstream fix split —
**#14807** (the projection half: `is_prop` must require the inferred type to
reduce to a sort) and **#14806** (the defeq-cache half). The file records that
`proj-of-subst-prop` reaches the same projection *without* the cache, which is
why the projection defect stands alone, and that lean4lean's executable already
enforces the rule via `ensureSortCore` — which is why it scores 67/67 where our
pinned kernel scores 63/67.

**The computational half** mirrors lean4lean's own `reduceProjCore` (which
selects `args[numParams + idx]`), indexed from the right of the `.app` spine.
That is not a convenience: `lift`, `inst` and `instL` all distribute over `.app`,
so the seven open `TrProj.*` obligations — all of which are structural
(commutation with substitution, plus functionality) — become near-mechanical
against this shape. **None of the seven needs the constructor table**, which is
precisely why they can be validated before the reconciliation lands.

### Validation

`ArgFromRight.det` and `ProjField.det` — the computational half is **functional**,
proved outright by a two-case induction rather than up to definitional equality.
Its consumer is `TrProj.uniq`, the cheapest of the seven.

**Typechecking: GREEN — see entry 6**, which supersedes this paragraph. (As
written, this entry said the typecheck was queued and not done; it completed
later the same night, twice, and the correction is recorded rather than edited
away.)

### Hygiene

Work is on the local branch `lean-surfaces/trproj` with no upstream tracking, and
the artifact is copied into **our** repo because the clone is scratch. No PR, no
comment, no contact — engagement remains Thomas's call. The file carries an
Apache-2.0 header matching the project it is written against.

### The central fact is now on the charter's front page

**lean4lean's model is further from Lean's kernel than its executable checker
is** — the checker is 67/67 on the arena's soundness suite while the model it is
proved against has no projections, no unit-like rule, no structure eta and no
inductives. A large share of the open work is **specification gaps wearing proof
obligations' clothes**, and the triage rule that catches them — *before asking
whether a proof is hard, ask whether the model can conclude it at all* — is now
stated at the top of the charter.


---

## 2026-08-23-lean-tier-6 — `ProjParam.lean` TYPECHECKS GREEN, verified twice; and the private script is retired for the owner-format defect

### The verdict

**`lake env lean Lean4Lean/Verify/Typing/ProjParam.lean` — exit 0, no diagnostics.**
Verified by **two independent runners**, which is more than was asked for and is
the only reason the first one counts at all (see below):

| runner | tenure | build | typecheck |
| --- | --- | --- | --- |
| the retired private script | lock after 3807 s | `lake build` exit 0, **115 s** | **exit 0, 1 s** |
| **`tools/triad.sh`** | lock after **6496 s** as `leantier 71863` | exit 0, 1 s (already built) | **green, 8 s** |

The triad's one-second build is not a no-op that skipped the work: the earlier
run had already produced `.lake` (405 MB), so `lake build` had nothing to do. The
gate is the load-bearing part, and it re-ran `lake env lean` **on the current
source** (mtime 21:19, gate 01:11) for 8 s with no output.

**The landed artifact is byte-identical to the file that was typechecked** —
`diff -q` between `docs/lean4lean-trproj-parametric.lean` and the clone's copy is
clean. Audited with this lane's own obligation instrument: **0 real sorries
(3 raw, all prose), 0 axioms**, 2 theorems, 3 defs, 2 structures, 1 inductive.

So the parametric `TrProj` — minimal assumed interface, sound side condition at
its centre, arena and #14807/#14806 cited as witnesses — **compiles against
lean4lean at its own pin**, and `ArgFromRight.det` / `ProjField.det` prove the
computational half functional.

### The private script is retired (A16.2), and the defect was mine three times

`scratchpad/leantier-m3.sh` and `scratchpad/leantier-inch2.sh` are **deleted**.
Both wrote the owner file as `<lane> lake pid <pid> (<note>)`, so the LAST field
was `TrProj)` / `lean4lean)` — **a paren, not a pid**, and a staleness check
reading `$NF` parses garbage. `tools/triad.sh`'s own header already cites the
`lean4lean)` instance as its exemplar. That is A5 read and then implemented
wrongly, by this lane, twice — which is the argument for the shared script
stated better than any advocacy could.

**One migration hazard worth passing on: SIGKILL bypasses the EXIT trap**, so the
killed script's queue ticket was orphaned and had to be removed by hand. Anyone
retiring a ticket-holding script owes that second step or leaves a phantom at the
queue head. (In this instance the process was already dead — it had completed at
20:26:27 and released cleanly — so the kill hit nothing live, but the ticket
cleanup was still required.)

Under `triad.sh` the owner line reads `leantier 71863`: lane, then pid, pid last.
The defect is gone because the format is no longer this lane's to get wrong.

### What `triad.sh` could not express, reported rather than worked around

`--classify` **cannot be used against a foreign checkout**, and there are two
independent reasons:

1. **The class floor hard-wires this repo's gates.** `gate_floor` yields
   `docs_check` / `diff_test`, which do not exist in the lean4lean clone, so
   every `--classify` run there fails on gates that are meaningless in it. There
   is no `--no-floor`.
2. **Classification diffs against the clone's `origin/master`** — which for a
   foreign checkout is *upstream's* master. Measured:
   `CLASSIFY: NOTHING STAGED OR COMMITTED against origin/master — this measured
   nothing`, with `origin -> git@github-work:digama0/lean4lean`. Correct
   behaviour, wrong frame.

**What was NOT missing**, checked rather than assumed: `--dir` genuinely
relocates the build (`cd "$CLONE"`, then `lake build`), and elan resolves the
toolchain per directory from `lean-toolchain`, so the clone's own
`v4.33.0-rc2` is picked up with no flag. The foreign-toolchain concern was a
non-issue.

**The workaround is legitimate, not a private copy:** without `--classify`,
`--gates` fully replaces the default (`if [ -z "$GATES" ]`), so
`--lane leantier --dir <clone> --gates 'lake env lean …'` runs exactly the two
phases the retired script ran — full `lake build`, then the typecheck — inside
one proper tenure, with no reduction in coverage. **Suggested addition for the
QoL lane** (not implemented here): a `--foreign` flag that keeps the tenure,
lock and RSS discipline, suppresses the class floor, runs only the lane's
`--gates`, and prints a coverage statement saying *foreign checkout, gates as
given, class floor not applicable*. `--against` already exists and would cover
reason 2 once the floor is suppressible.

---

## 2026-08-23-lean-tier-7 — `TrProjP.instL` GREEN, and the proof caught a soundness defect in my own definition

The validation lemma landed. **`lake build` exit 0 (152 modules), gate
`lake env lean …/ProjParam.lean` green**, under `tools/triad.sh --foreign`,
tenure `leantier 65793`, lock acquired in **0 s** (empty queue). Coverage
statement as printed: *foreign checkout `digama0/lean4lean`; gates as given;
class floor not applicable — evidence about THAT tree and those gates, and about
nothing in this repository.*

Local branch `lean-surfaces/trproj` @ **`71829bf6cd5c9b468f64c94cc65d58e0c0f967fe`**,
no upstream tracking, never pushed to `digama0`. `docs/lean4lean-trproj-parametric.lean`
is byte-identical to the file that went green: **243 lines, 0 real sorries
(3 raw, all prose), 0 axioms, 8 theorems.**

### THE FINDING: the proof caught a real soundness defect in the definition

The first draft required the structure's sort to be `IsAlwaysZero` — `Prop` under
every valuation. **That is unsound, and `TrProjP.instL` is unprovable with it.**

`instL` can turn `Type u` into `Prop` by taking `u := 0`. A structure that is not
a proposition at one instantiation becomes one at another, and a data field
projected out of it then yields `False`. The arena tests that family as
**`proj-of-imax-prop`**, which the official kernel failed at v4.28.0.

The kernel's own test is `maybePropType := !(← getSortLevel type).isNeverZero` —
***maybe* zero, not *always* zero.** So the structure side must be `MaybeZero`.

**The two polarities are exactly the two the proof needs, and for the same reason
they are the sound ones:** `MaybeZero` *reflects* along `instL` (the witness is
the instantiated valuation) so it can discharge a hypothesis; `IsAlwaysZero`
*transports forward* so it can supply a conclusion. With the polarities swapped
the first step is simply false.

`ProjSound` also moved from `∀ A u, … → …` to an existential — the `∀` shape
provably cannot transport, since nothing reflects an arbitrary instantiated type
back to an uninstantiated one. The `∃` shape is the model's own idiom (`IsType`
is `∃ u, HasType Γ A (.sort u)`).

**This is the argument for validation lemmas stated as cheaply as it can be: a
definition that merely compiled would have shipped the unsoundness. The proof is
what refused it.**

### The red round, and its one-line fix

The first tenure was **RED** — 4 errors, all
`Invalid field 'instL': the environment does not contain
'Lean4Lean.VEnv.IsDefEq.instL'`, and per the foreign-tenure contract the gates
never ran. **A missing import wearing a name-resolution error's clothes:**
`Theory.Typing.Basic` (reached via `Verify.Typing.Expr`) *defines* `IsDefEq` and
`HasType`; their `instL` lemmas are *proved* in `Theory.Typing.Lemmas`, which was
not in my closure. One import line. Upstream's own `Verify/Typing/Lemmas.lean` —
where the seven `TrProj.*` obligations live — reaches the same module via
`Theory.Typing.Strong`, and `Theory/` never imports `Verify/`, so no cycle.

Diagnosed from the FULL log, not the summary: the summary truncates, and on a
red the gate line is absent rather than failing, so "no gate error" would have
read as "gates passed".

### Tooling

`--foreign` **adopted** (master had landed it while I was arguing for it); the
plain `--gates` workaround is retired. `--gates-only` announced the skipped floor
explicitly, which is the Ada lane's 78-minute lesson working.

**`check.sh --iterate` refused twice, by number: swap 84.2 % then 83.2 %, against
a 50 % line** — load was fine both times (7.28, 8.40). I did not override it. The
machine is swapping persistently rather than being busy, so proof iteration is
unavailable and every check costs a tenure; both of this round's compiles were
ticketed.

---

## 2026-08-23-lean-tier-8 — `TrProj.uniq` is plausibly blocked on no-confusion: established by READING, at zero machine cost

I told the coordinator that `ProjField.det` gave `uniq`'s computational half.
**That was too optimistic and this entry withdraws it.**

### What `uniq` actually needs

```lean
theorem TrProj.uniq (H1 : TrProj Γ₁ s₁ i e₁ e₁') (H2 : TrProj Γ₂ s₂ i e₂ e₂')
    (H : env.IsDefEqU U Γ₁ e₁ e₂) : env.IsDefEqU U Γ₁ e₁' e₂'
```

`ProjField.det` proves *same spine, same index ⇒ same field*. `uniq`'s two
structures are **merely definitionally equal**, not identical. Concluding the
fields are defeq requires:

> **defeq of constructor-headed applications ⇒ defeq of the corresponding
> arguments** — constructor injectivity / no-confusion.

### Absent from the pin, established by PATTERN POSITION rather than by name

Grepping the identifier would prove nothing (the lemma could be named anything).
So the search was for the **shape**: any lemma in `Lean4Lean/Theory/` taking a
hypothesis of the form `IsDefEq(U) _ _ (.app …) (.app …)`.

**Zero hits across the whole of `Theory/`.**

Cross-checked against every inversion principle the model does have — 23 of them,
enumerated. They partition cleanly:

| what is inverted | lemmas | kind |
| --- | --- | --- |
| `app`, `lam`, `const`, `bvar` | `HasType.app_inv`, `.lam_inv`, `.const_inv`, `.bvar_inv` (`Strong.lean`) | **TYPING** inversion — extracts pieces from `HasType Γ (.app f a) V`. Says nothing about defeq of arguments |
| `sort`, `forallE` | `IsDefEqU.sort_inv`, `.forallE_inv`, `.forallE_inv_stratified` (`Injectivity.lean`) | **DEFEQ** inversion — and all three are `sorry` |
| lifting/weakening | `*.weakU_inv`, `*.weakN_inv` | structural, unrelated |

So the model has defeq-injectivity **only for the type formers** (`sort`,
`forallE`) — which is exactly what unique typing needs — and **none for
applications**.

### Why that is a structural fact, not an oversight

App-injectivity is **not valid in general**: `f a ≡ g b` does not give `a ≡ b`.
It holds when the head is a **constructor**, and the justification is
no-confusion, which comes from the inductive elimination principles — i.e. from
`VEnv.addInduct`, the same root entry 4 measured as gating everything else in
this cluster, and the same root **PR #43** is filling.

### The verdict, stated at the confidence the evidence supports

> **`TrProj.uniq` is PLAUSIBLY BLOCKED on no-confusion (`addInduct`, the PR #43
> root) — NOT MEASURED.**

Not measured because proving it blocked would cost a tenure, and the coordinator
ruled — correctly — that a reading-level finding at zero machine cost is worth
more than a confirmed negative at 90 minutes' queue. **If `instN` or `weak'`
later hand over the shape cheaply, revisit.**

**Next obligation is `TrProj.weak'`** — lifting, the same two-case induction as
`instL`/`instN`, since `liftN` also distributes over `.app` without changing
depth.

### The argument-order trap goes to the family doc

`docs/family-architecture.md` §3.4.2. `HasType` is a `def` over `IsDefEq`, so dot
notation resolves past it: `hA.instN …` picks `VEnv.IsDefEq.instN`, whose
argument order is `(henv)(h₀)(W)(H)` against `VEnv.HasType.instN`'s
`(henv)(W)(H)(h₀)`. Both exist, both typecheck at the call site's arity, and the
arguments silently mis-bind. This lane's first red was the same hazard's sibling
— the dot-notation target did not exist in the import closure, and reported as
`the environment does not contain …`, **a missing import wearing a
name-resolution error's clothes**. `instL` was green only because its two orders
happen to agree; that is luck. **Rule: name the lemma explicitly in a foreign
proof tree** — and in one's own, wherever a `def` sits over another relation
(this tier's `ProjField` over `ArgFromRight` got the same treatment).

---

## 2026-08-23-lean-tier-9 — `TrProjP.instN` GREEN; and the quality audit found four real defects in this lane's instruments, one of which had published wrong citations

### `instN`: GREEN, gate line PRESENT

`tools/triad.sh --foreign`, tenure `leantier 96709`, lock after 4454 s.
`lake build` exit 0 → BUILD GREEN; `=== gate: lake env lean …/ProjParam.lean ===`
**present**; `TRIAD DONE (build exit 0, gates green)`. Branch
`lean-surfaces/trproj` @ **`0f85caec154ad4edd9663082ab7b3d7a42d29a85`**.
`docs/lean4lean-trproj-parametric.lean` is byte-identical: **292 lines, 0 real
sorries, 0 axioms, 12 theorems.**

**The pre-registered mitigation worked.** `VEnv.HasType.instN` takes
`(henv)(W)(H)(h₀)`; `VEnv.IsDefEq.instN` takes `(henv)(h₀)(W)(H)`. Naming the
lemma explicitly avoided the mis-slotting; dot notation would have bound `W`
where `h₀` was expected.

### The audit's four defects — all real, all fixed, one had shipped wrong numbers

**HIGH — `lean_independent_check.py`: bare `"unsupported"` as an unanchored
substring over the whole stdout+stderr, tested BEFORE the DIVERGE fall-through.**
Any rejection whose text merely contained the word was reclassified DIVERGE →
REFUSE. That is the dangerous direction: DIVERGE is the zero-tolerance invariant
and REFUSE is never agreement, so the bug could silently downgrade a soundness
disagreement into a coverage note. Now three anchored, per-line patterns
(`lean4lean does not support`, `type checker does not support`,
`unsupported (declaration|construct|feature)`), so a marker cannot be satisfied
by words drawn from two unrelated lines. Seven classification fixtures run,
including *the word inside a filename* → **DIVERGE** and *word and rejection on
different lines* → **DIVERGE**.

> **BLAST RADIUS, measured rather than assumed.** The audit stated the arena
> soundness numbers flow through this instrument. **They do not.**
> `lean_independent_check.py` contains **zero** references to arena data — the
> 63/67 vs 67/67 figures came from this lane recomputing the arena's published
> `results.json` directly, a path that never touches this file. And every row in
> `docs/lean-independent-check.json` has `exit_code 0`, while `MATCH` is returned
> *before* the marker loops — so no published verdict could have been affected.
> The defect was real and worth fixing; its reach was not what the audit
> supposed. (The arena corpus has since been purged, so this is settled by code
> inspection, not by re-running their harness.)

**MEDIUM — `lean_kernel_census.py`: rule presence by unanchored `symbol in line`
over C++, first hit published as `definition_line`. THIS ONE SHIPPED WRONG
FACTS.** Re-run after the fix, **5 of 16 rules had been citing a line that is not
a definition**:

| rule | published | actually was | correct |
| --- | ---: | --- | ---: |
| `delta` | 488 | a doc comment: *"…`unfold_definition` will also succeed. */"* | **523** |
| `nat-lit` | 539 | a global: `static expr * g_lean_reduce_nat = nullptr;` | **611** |
| `proj` | 359 | a comment: `/* Auxiliary method for reduce_proj */` | **378** |
| `delta-lazy` | 886 | — | **975** |
| `string-lit` | 1032 | — | **1039** |

**Every COUNT was unchanged** — 12 `Expr`, 6 `Level`, 16 rules, 15 `Nat` ops,
7 axioms — so no headline moved; what was wrong were five *citations*, which is
precisely the "number from a substring census" shape. The matcher now requires a
definition form, skips comment lines and forward declarations, records
`definition_sites`, and refuses with the bare-mention count when no definition
exists.

**LOW ×2 — constructor detection required EXACTLY two leading spaces**
(`^\s{2}\|`), in both this file and `lean_rule_correspondence.py`, so a
constructor indented four spaces, with a tab, or inside a nested block matched
nothing and vanished silently. Now `^\s+\|`, plus a **zero-constructor refusal**
scoped to blocks that clearly opened a constructor list.

**LOW — `_sorry_stubs` grepped UNSTRIPPED source**, the exact defect
`wasm_sorry_census.py` was written to fix. Now imports that module's
`strip_lean` — the family's shared stripper, per §9.2 consolidation-by-touch
rather than a fourth private copy — and reports the raw/live delta. **This lane
wrote its own comment stripper for `lean4lean_obligation_census.py`, championed
it as the Wasm lesson, and then failed to use one here.**

### What did NOT change

`docs/lean-rule-correspondence.json` re-run post-fix: `IsDefEq` 13, `VExpr` 6,
`Theory/` inductives 33, `rules_by_relation` **identical** — the 24 %-maps-to-a-stub
headline holds. Stub sorries 2, and the stripper now confirms
`raw 2 / live 2 / comment-only 0`. Both instruments double-run byte-identical and
`--compare` clean; refusal paths re-verified at exit 2.

### `weak'` pre-registered, deliberately NOT written yet

Census done: `lift'` takes a `Lift` (not a `Nat`), `.app` keeps depth
(`| .app fn arg, k => .app (fn.lift' k) (arg.lift' k)`), sorts inert
(`| .sort u, _ => .sort u`) so no level transport, context relation
`Ctx.Lift' : Lift → List VExpr → List VExpr → Prop`. **Trap does not fire here**:
`IsDefEq.weak'` and `HasType.weak'` both take `(henv)(W)(H)`. Named explicitly
regardless — the rule is not to depend on the orders agreeing.

**A hazard worth §7: a queued tenure reads the source at BUILD time, not at
ENQUEUE time.** Adding `weak'` while `instN`'s ticket was still queued would have
silently changed what that tenure tested, and a green would have been reported
for code that was never the subject. The file was left untouched until `instN`
reported.

---

## 2026-08-23-lean-tier-10 — DECISION BRIEF for Thomas: PR #43 does NOT unblock `TrProj.uniq`, and consuming it buys nothing this lane needs

Read-only census of `digama0/lean4lean` PR #43 (`addInduct`), fetched as a
**ref only** and inspected with git plumbing — never checked out, because the
`weak'` enqueue-tree gate was live and a checkout would have modified the tree
the queued tenure had already hashed. (Verified after the fetch:
`git write-tree` still `706583bb408f`, matching the gate.)

PR #43 head `eddf009`, **20 files, +1256/−35**.

### Q1 — Would PR #43 supply the no-confusion shape `uniq` needs? **NO.**

`uniq` needs *defeq of constructor-headed applications ⇒ defeq of the
corresponding arguments*. What PR #43 actually adds is **ι-reduction**:

* a new `VEnv` field `pats : (p : Pattern) → p.RHS × p.Check → Prop` — a
  registry of schematic reduction rules — plus `VEnv.addPat`;
* a **14th `IsDefEq` constructor**, `| pat`, letting a registered pattern fire:
  `env.pats p r → p.Matches e m1 m2 → … → Γ ⊢ e ≡ r.1.apply m1 m2 : A`.

**That is the opposite direction from what `uniq` requires.** A reduction rule
computes *forwards* (a constructor-headed redex steps to its reduct); `uniq`
must reason *backwards* from "these two applications are defeq" to "their
arguments are". Reduction gives no such inversion.

**The word "injectivity" does appear in the PR, and it is a false friend.** All
of it is *name* injectivity — `addConst_foldlM_inj` (the naming function is
injective on the list), `addInduct_recs_name_inj` (recursor names),
`iota_toPattern_inj`, `Pattern.varN_const_inj`. **Nothing about defeq of
constructor arguments.** Searched by shape as well as by name: PR #43 introduces
**zero** lemmas taking a hypothesis of the form
`IsDefEq(U) _ _ (.app …) (.app …)`.

**And it makes `uniq` strictly HARDER.** A 14th way for two terms to be
definitionally equal is a 14th case any inversion must dispatch. The `uniq`
obligation's cost goes up, not down.

### Q2 — What would consuming it cost?

| dimension | measured |
| --- | --- |
| size | 20 files, **+1256 / −35** |
| `VEnv` shape | **a new field** — so every `VEnv` literal, and the `LE`/`rfl`/`trans` triple, changes |
| `IsDefEq` shape | **a new constructor** — every inversion over defeq gains a case |
| blast radius | PR #43 itself had to patch **20 files** to absorb its own change; `Theory/`+`Verify/` contain **157** `induction … with` / `cases … with` blocks as a loose upper bound on exposure |
| toolchain | **`v4.33.0-rc2` — identical to ours.** No reconciliation needed |
| freshness | **15 behind / 14 ahead of master**, merge-base `1a16b72`. **Not rebased.** Consuming means rebasing it ourselves or pinning to a stale base |
| build at our pin | **NOT MEASURED** — would cost a tenure, and Q1 already decides the question |

### Q3 — Does it collide with our work? **NO.**

**`TrProj` is still `sorry` on PR #43** (`Verify/Typing/Expr.lean:67`, verified on
the branch). PR #43 does not touch it. Its only change to that file is to add
`VExpr.mkApps`, a left fold of applications — a spine helper, adjacent to our
`ArgFromRight` but not a substitute for it.

So the parametric `TrProj` neither duplicates PR #43 nor is duplicated by it, in
either direction, which is what the untouched-complement rule was protecting.

### RECOMMENDATION

> **Do not consume PR #43. Wait for upstream.**

It does not unblock `uniq`, it does not touch `TrProj`, it raises the cost of
every defeq inversion, and it is 15 commits behind a moving master. The only
reason to take it would be to obtain **inductives** — a different goal, on the
in-flight side of the line, and one the ruling put out of bounds.

**`uniq`'s status is unchanged and its wording should stay as entry 8 set it:**
plausibly blocked on no-confusion — **and this brief narrows *where* that
no-confusion would have to come from.** It is not in `addInduct`; it would need
the constructor *elimination* principles (recursors and their no-confusion
consequences), which PR #43 registers as reduction rules rather than deriving as
injectivity. **Still NOT MEASURED, and now with a named place it is absent
from.**

---

## 2026-08-23-lean-tier-11 — `TrProj.weak'` GREEN (3 of 7); and censusing `TrProj.wf` found a real gap in my own definition

### `weak'`: GREEN

```
LOCK  [16:31:30] LOCK ACQUIRED after 6062s as 'leantier 20942'
      [16:31:38] build exit=0  ->  BUILD GREEN
GATE  [16:31:38] === gate: lake env lean .../ProjParam.lean ===     PRESENT
      [16:31:39] TRIAD DONE (build exit 0, gates green)
```

The **enqueue-tree gate held**: `tree at enqueue: 706583bb408f`, identical to
what was staged, so the tenure built exactly the tree that was ticketed.

Branch `lean-surfaces/trproj` @ **`d461f21db807c5f5748890de1564753805fd2d29`**.
`docs/lean4lean-trproj-parametric.lean` byte-identical to the green file:
**334 lines, 0 real sorries, 0 axioms, 16 theorems.**

**Three of the seven obligations are now proved** against the parametric
definition: `TrProjP.instL`, `TrProjP.instN`, `TrProjP.weak'`. The trap did not
fire for `weak'` (`IsDefEq.weak'` and `HasType.weak'` agree on `(henv)(W)(H)`);
the lemma is named explicitly regardless.

### THE FINDING: `TrProj.wf` is NOT provable against my definition as written

Censusing the next obligation — **by reading, before spending a tenure on it** —
turned up a gap in `ProjSound` rather than in lean4lean.

```lean
theorem TrProj.wf (H1 : TrProj Δ s i e e') (H2 : VExpr.WF env U Γ e) :
    VExpr.WF env U Γ e'
```

and `VExpr.WF env U Γ e := env.IsDefEqU U Γ e e` — *"`e` has a type"*. So `wf`
requires **the projected field to be typed unconditionally**.

My `ProjSound` types the field only *inside the `Prop` case*:

```lean
sound : ∃ A u, HasType e A ∧ HasType A (.sort u) ∧
  (VLevel.MaybeZero u → ∃ B w, HasType v B ∧ HasType B (.sort w) ∧ IsAlwaysZero w)
```

When the structure's sort is **not** maybe-`Prop`, the definition says **nothing
whatever about `v`** — so `wf` cannot be derived. The definition is too weak, and
this is the second time the obligations have caught a defect in it rather than in
the tree it targets (the first was the `IsAlwaysZero`/`MaybeZero` polarity).

### The pre-registered restructure

Hoist the field's typing **out of** the implication, leaving the `Prop`-squash as
a condition on the **levels alone**:

```lean
sound : ∃ A u B w, HasType e A ∧ HasType A (.sort u)
                 ∧ HasType v B ∧ HasType B (.sort w)
                 ∧ (VLevel.MaybeZero u → VLevel.IsAlwaysZero w)
```

* **strictly stronger** — the field is now typed in every case, which is exactly
  what `wf` consumes;
* **says the same thing about soundness** — a maybe-`Prop` structure still forces
  an always-`Prop` field;
* **transports identically** — the implication `MaybeZero u → IsAlwaysZero w`
  becomes `MaybeZero (u.inst ls) → IsAlwaysZero (w.inst ls)`, discharged by
  `MaybeZero.of_inst` then `IsAlwaysZero.inst`, which is the proof already
  written. The three green lemmas need only their `refine` shapes widened.

**Cost: one tenure for all four** (`instL`, `instN`, `weak'` re-proved, plus
`wf`), batched per base rule 4 rather than paid twice.

### Status of the seven

| obligation | status |
| --- | --- |
| `instL`, `instN`, `weak'` | **PROVED** (green, `d461f21`) |
| `wf` | blocked on **my own** definition; restructure pre-registered above |
| `uniq` | **plausibly blocked on no-confusion** — entry 8, narrowed by entry 10: not in `addInduct`, would need the constructor *elimination* principles. NOT MEASURED |
| `weak'_inv`, `defeqDFC` | uncensused. Both are `∃`-conclusions over a *changed* context, so neither is a congruence like the three proved ones |

---

## 2026-08-23-lean-tier-12 — `wf` GREEN and the hoisted `ProjSound` re-proved: 4 of 7; the remaining three are censused and none is ordinary work

### The batched tenure: GREEN

```
LOCK  [20:48:23] LOCK ACQUIRED after 5065s as 'leantier 77443'
      [20:48:32] build exit=0  ->  BUILD GREEN
GATE  [20:48:32] === gate: lake env lean .../ProjParam.lean ===     PRESENT
      [20:48:33] TRIAD DONE (build exit 0, gates green)
```

`tree at enqueue: 967759fafd66`, matching the staged tree. Branch
`lean-surfaces/trproj` @ **`da9e7b11abefabd5b7f3d53cf1c23f7216f7eac2`**; repo copy
byte-identical: **357 lines, 0 real sorries, 0 axioms, 18 theorems.**

**Four of seven proved** — `TrProjP.instL`, `.instN`, `.weak'`, `.wf` — with the
first three re-proved on the hoisted structure in the same tenure, so one tenure
bought the restructure and the new lemma together (base rule 4).

### Census of the remaining three: none is ordinary work

**`weak'_inv` — provable in FORM, but its only route rests on an upstream
`sorry`, and on exactly the direction it needs.**

Upstream parks `HasType.skips` immediately above `TrProj.weak'_inv`, which is the
intended tool. Following it down:

```
HasType.skips  ->  IsDefEq.skips  ->  (IsDefEqU.weakN_iff henv hΓ W).1
```

and `IsDefEqU.weakN_iff` (`UniqueTyping.lean:172`) is

```lean
refine ⟨fun h => have := henv; have := hΓ; sorry, fun h => h.weakN henv W⟩
```

— the **reverse** direction is proved (`h.weakN`); the **forward** direction is
`sorry`. `skips` uses `.1`, the sorried one, and forward reflection is precisely
what `weak'_inv` needs. It is the single `sorry` in that file and one of the 24.

So proving `TrProj.weak'_inv` today yields a lemma that **compiles green while
resting on somebody else's hole** — a green that carries an upstream `sorry`
inside it. That is a decision, not a detail, and it is the coordinator's:
this lane has so far only shipped lemmas whose dependencies are complete.

*The computational half is unaffected and is ours:* `lift'` maps `.app` to `.app`
and every other constructor to a non-`.app`, so `e.lift' l` being an application
spine forces `e` to be one. That half needs nothing from upstream.

**`defeqDFC` — same blocker family as `uniq`.**

```lean
theorem TrProj.defeqDFC (henv) (hΓ : IsDefEqCtx U [] Γ₁ Γ₂)
    (he : env.IsDefEqU U Γ₁ e₁ e₂) (H : TrProj Γ₁ s i e₁ e') :
    ∃ e', TrProj Γ₂ s i e₂ e'
```

`e₂` is only **definitionally equal** to `e₁` — nothing forces it to be a
syntactic application spine at all. Recovering a field from it needs
app-structure through defeq, which is the same missing no-confusion entry 8
established is absent by shape and entry 10 located: not in `addInduct`, but in
the constructor *elimination* principles. **Plausibly blocked — NOT MEASURED.**

**`uniq` — unchanged**, plausibly blocked on no-confusion.

### The seven, settled

| # | obligation | status |
| --- | --- | --- |
| 1 | `instL` | **PROVED** |
| 2 | `instN` | **PROVED** |
| 3 | `weak'` | **PROVED** |
| 4 | `wf` | **PROVED** |
| 5 | `weak'_inv` | provable in form; typing half rests on the **sorried forward direction** of `IsDefEqU.weakN_iff`. Coordinator's call |
| 6 | `defeqDFC` | plausibly blocked on no-confusion — NOT MEASURED |
| 7 | `uniq` | plausibly blocked on no-confusion — NOT MEASURED |

**The four that are proved are exactly the congruences** — the lemmas saying the
relation commutes with substitution — and they went through because `lift`,
`inst` and `instL` all distribute over `.app` without touching binder depth. **The
three that remain are exactly the inversions**, and every one of them needs to
reason backwards out of a `.app` spine. That split was visible in the shapes from
the start and is now measured rather than guessed.

---

## 2026-08-23-lean-tier-13 — MILESTONE: 4 proved / 3 blocked, `weak'_inv` parked on an IMPORT CYCLE; and the arena re-measure moved a fact

### `weak'_inv`: proving `weakN_iff`'s forward direction ourselves is NOT a bounded induction

The ruling was: don't ship a lemma resting on upstream's `sorry`; instead census
what it would cost to prove `IsDefEqU.weakN_iff`'s forward direction in the fork.
Censused by reading. **It is not a bounded induction, and the obstacle is
architectural rather than mathematical.**

Strengthening's hard case is `trans`: the middle term may mention the very
variable being stripped, so discharging it needs **confluence** to normalise that
term. lean4lean HAS confluence — `IsDefEq.church_rosser`,
`ChurchRosser.lean:1344`. But:

```
Basic -> Lemmas -> Strong -> Injectivity -> UniqueTyping -> ChurchRosser
                                 Pattern  ^                 ^
```

> **`ChurchRosser.lean` imports `UniqueTyping.lean`.** The confluence result that
> would discharge the obligation lives DOWNSTREAM of the module the obligation
> sits in. Using it is a module-layering inversion, not a lemma.

Measured, no confluence or normalisation result exists anywhere upstream of
`UniqueTyping` (`Injectivity`, `Pattern`, `Strong`, `Lemmas` — none). So the
options are (a) invert upstream's `Theory/` layering, (b) re-derive confluence
above `UniqueTyping`, duplicating a 1 300-line development — **and (c) neither
would suffice cleanly anyway, because `ChurchRosser.lean` itself carries two
`sorry`s** (`:1190`, `:1209`, both the `.extra` case).

**Verdict: park `weak'_inv` beside `uniq` and `defeqDFC`, blocked with a named
place** — *"the confluence result that discharges it is downstream of the
obligation."* That is a sharper statement than the other two blockers get, and it
cost no machine time.

### THE MILESTONE LEDGER — the in-reach obligations are DONE

| # | obligation | status |
| --- | --- | --- |
| 1 | `TrProjP.instL` | **PROVED** |
| 2 | `TrProjP.instN` | **PROVED** |
| 3 | `TrProjP.weak'` | **PROVED** |
| 4 | `TrProjP.wf` | **PROVED** |
| 5 | `weak'_inv` | **BLOCKED** — confluence is downstream of the obligation (import cycle) |
| 6 | `defeqDFC` | **BLOCKED** — app-structure through defeq; no-confusion. NOT MEASURED |
| 7 | `uniq` | **BLOCKED** — same. NOT MEASURED |

**4 proved, 3 blocked, 0 sorries, 0 axioms** in 357 lines. The split is exactly
congruences-proved / inversions-blocked, and every blocker now has a named
location rather than a shrug.

### The arena re-measure: our number held, upstream's moved

Re-fetched `results.json` (3.0 MB; `df` first, 145Gi) and recomputed. Fresher run
than the original: **2026-08-22 15:57 UTC rev `f0fe3b37`**, against the
2026-08-22 10:33 rev `46414771` used before.

| checker | accept | reject (soundness) | vs. previous |
| --- | ---: | ---: | --- |
| **`official` (our pin v4.33.0)** | 124/124 | **63/67** | **unchanged** |
| `official-nightly` | 124/124 | **67/67** | **was 66/67 — CHANGED** |
| `lean4lean` | 121/124 | 67/67 | unchanged |
| `mathgraph` | 124/124 | 67/67 | unchanged |

`official` still misses exactly `proj-of-stuck-prop`, `proj-of-subst-prop`,
`rec-missing-ih`, `rec-of-subst-prop`.

> **A PUBLISHED CLAIM OF OURS IS NOW STALE.** Entry/charter §9.1 says
> `rec-of-subst-prop` is *"accepted by ALL THREE official builds"*. **Nightly has
> since fixed it and is now 67/67.** Our pinned `v4.33.0` still fails all four, so
> the tier's motivating fact — *our own kernel accepts proofs of `False` that
> independent checkers reject* — stands, but it is now a statement about **our
> pin**, not about upstream generally. Corrected in the charter.

**On the instrument question, stated precisely:** the substring defect could not
have touched these numbers, and the re-measure confirms it — `lean_independent_check.py`
contains **zero** arena references, and this figure is recomputed directly from
the arena's published rows. The number moved because **upstream moved**, which is
the argument for re-measuring rather than re-citing.

---

## 2026-08-23-lean-tier-14 — CONSUME-PATH CENSUS at the new state: everything in reach is blocked, and the tier's next move is WAITING

The question was: with `TrProjP` done in-reach, what is the next obligation
family on the consume path that is neither inversion-blocked nor
confluence-blocked? **The honest answer is: there isn't one.** Written down
rather than worked around, because a lane that keeps looking busy past this
point is the failure this census exists to prevent.

### The 24 shipped obligations, partitioned by ROOT CAUSE

Re-run against the current fork. Every obligation lands in exactly one bucket and
the arithmetic closes:

| root | count | share |
| --- | ---: | ---: |
| **`addInduct` — the model cannot express "constructor"** | **15** | **63 %** |
| missing MODEL RULE (spec gap: unit-like / structure eta) | 2 | 8 % |
| confluence IMPORT CYCLE | 1 | 4 % |
| IN FLIGHT upstream — do not enter | 6 | 25 % |
| **total** | **24** | |

**The `addInduct` bucket, itemised**, because 63 % resting on one hole is the
finding: `TrProj` itself; its seven lemmas (`instL`, `instN`, `weak'`, `wf`,
`weak'_inv`, `defeqDFC`, `uniq`); the three checker-side proj/recursor lemmas
(`inferProj.WF`, `reduceProjCore.WF`, `reduceRecursor.WF`); the three
inductive-types obligations (`VInductDecl.WF`, `VEnv.addInduct`, `addInduct_WF`);
and `addDecl.WF`.

### The two obligations I had never examined are blocked too — and by inspection

`inferProj.WF` and `reduceProjCore.WF` were the only candidates left unexamined.
Both take `c.TrExprS (.proj n i e) e'` as a **hypothesis**, and `TrExprS`'s only
constructor producing a `.proj` is

```lean
| proj : TrExprS Δ e e' → TrProj Δ.toCtx s i e' e'' → TrExprS Δ (.proj s i e) e''
```

So inverting either hypothesis yields a `TrProj` fact **about a relation that
does not exist**. Nothing can be extracted from it. They are blocked at the same
root as everything else in the cluster, and it cost no machine time to establish.

*(`reduceProjCore.WF` is the closest thing to reachable in the whole census — it
is the executable counterpart of our `ProjField`, and our `ArgFromRight` is
exactly its computational content. It is blocked only because it names upstream's
`TrProj`, not ours. That is the shape of what unblocks the moment a real `TrProj`
lands.)*

### PROPOSAL: the tier's next state is WAITING, and here is what that means

Not idleness, and not a pause with no exit condition. Concretely:

**1. The trigger is PR #43 landing** (or any upstream commit that gives `VEnv`
constructor data). At that moment 15 of 24 unblock at once, and this lane's
`TrProjP` is designed to be substituted in — the minimal interface is
`nparams`/`nfields`, and reconciliation was specified as a **substitution, not a
redesign**. The four proved congruences transfer with it.

**2. What we hold meanwhile is drift-guarded, not frozen.** Every census here has
`--compare`, and the arena re-measure already proved the point: `official-nightly`
moved 66/67 → 67/67 between two runs on the same day, and our published claim
went stale. **The number moved because upstream moved.** Re-running the guards is
the cheap, correct activity for a waiting lane.

**3. Nothing gets shipped over somebody else's hole.** The `weak'_inv` ruling
generalises: this lane ships lemmas whose dependencies are complete, so a
`#print axioms` never carries `sorryAx`. That standard is why the answer here is
"blocked" rather than "four more greens".

### THE UPSTREAM-ENGAGEMENT QUESTION, with the evidence attached

This is now Thomas's to decide, and the census hands him the argument rather than
a feeling:

* **63 % of the consume path sits behind one artifact** — `VEnv.addInduct` — and
  **an open PR (#43) fills exactly it.**
* **Consuming that PR was already priced and declined** (entry 10): it does not
  supply the no-confusion `uniq` needs, it adds a 14th `IsDefEq` constructor that
  makes every inversion costlier, and it is 15 commits behind a moving master.
  **That judgement is unchanged.** The case for engagement is not "take the
  branch"; it is "the branch's *landing* is our unblock trigger, and we have no
  visibility into its schedule."
* **The channel's measured response rate is 0-for-1**: Thomas's own issue #16
  asked which sorries are unclaimed and has gone unanswered; nine external proof
  PRs sit unreplied; there is no published open-problems list.
* **We have something to offer now, which we did not before.** Four green
  congruence lemmas, a sound-rule side condition validated against the arena's
  own tests, and a definition explicitly designed to substitute into `TrProj`
  when constructor data exists. **That is a contribution with a demonstrated
  green, not a proposal.**

**Recommended framing if Thomas engages:** not "how can we help", which the
0-for-1 record suggests goes nowhere, but a specific artifact plus a specific
question — *here is a `TrProj` that compiles with four of its seven lemmas
proved, parametric in `nparams`/`nfields`; will `addInduct` expose those, and in
what shape?* That is answerable in one line and is the only thing blocking 63 %
of the path.

**If Thomas declines to engage, WAITING is still correct** — the drift guards
catch the landing whenever it comes, and the four proved lemmas keep.

---

## 2026-08-23-lean-tier-15 — WAITING begins, and the first act was fixing the guards that WAITING depends on

WAITING is ratified, and the lane's standing duty is the drift guards. So the
first thing to do was **run them**, because a duty that has never been executed
is a plan, not a duty. Two of four fired. **Both were self-inflicted.**

### The defect: the guards were pinned to OUR BRANCH, not to upstream

| guard | result | cause |
| --- | --- | --- |
| kernel census | ok | — |
| correspondence | **DRIFT: `lean4lean_commit`** | baseline captured at `71829bf` — **our own first branch commit** |
| obligation census | **DRIFT: `totals`** | `raw` 138→141, **`real` 113→113** — our own docstring prose in `ProjParam.lean` |
| spec census | **REFUSE** | thesis LaTeX corpus purged; see below |

> **A guard that always fires is exactly as useless as one that never can.** The
> audit's defect class was "a `--compare` that cannot exit nonzero"; this is its
> mirror — a `--compare` that cannot exit zero. Either way the lane learns to
> ignore it, and the drift it was watching for arrives unnoticed.

The cause is precise: the baselines were taken while checked out on
`lean-surfaces/trproj`, so they encode **our** work as the reference. Every
future commit of ours would re-fire them, and upstream drift — the thing they
exist to catch — would be indistinguishable from our own noise.

### The fix: baseline against upstream, not against ourselves

`git worktree add` gives a pristine `master` checkout (2.1 MB) **without touching
the branch**, and the guards now run against it:

```
correspondence  : ok
obligation      : ok
kernel          : ok
```

**No published fact moved.** `rules_by_relation` is unchanged (`STUB` 17 — the
24 %-maps-to-a-stub headline holds), obligations are 113 real / 24 proof-layer,
and the correspondence now records `e0e3f6bcccb8` — **upstream master** — as its
base rather than one of our commits. The re-baseline corrected *what the guard
watches*, not *what we measured*.

### THE STANDING DUTY, written so it can be executed without rediscovery

Run from `docs/backlog/lean-tier.md`'s lane clone, against the **master
worktree**, never the branch:

```
W=<scratchpad>/leantier-probe/l4l-master        # git worktree, upstream master
K=<scratchpad>/leantier-probe/kernelsrc/src/kernel
L=~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean

python3 harness/lean_kernel_census.py        --lean-src $L --kernel-src $K --compare docs/lean-kernel-census.json
python3 harness/lean_rule_correspondence.py  --l4l $W --spec-census docs/lean-spec-census.json --compare docs/lean-rule-correspondence.json
python3 harness/lean4lean_obligation_census.py --l4l $W --compare docs/lean4lean-obligation-census.json
```

Refresh the worktree first (`git -C $W fetch origin && git -C $W reset --hard origin/master`).
**All three are pure Python over out-of-tree corpora — no Lean, no tenure, no
ticket.** That is what makes this duty affordable at any cadence.

**The trigger to watch for is a DRIFT in the obligation census's `real` count or
in `proof_layer.definitional_stubs`** — specifically `VEnv.addInduct` or
`VInductDecl.WF` leaving the stub list. That is PR #43 landing, and it unblocks
15 of 24.

### Two honest gaps in the duty, recorded rather than glossed

1. **The spec census cannot run** — the thesis LaTeX corpus (`digama0/lean-type-theory`)
   was purged and is not re-fetched here. Its baseline is committed and the
   instrument is pinned to `master 0ba1787`, so re-fetching restores it; but as
   of now that guard is **armed but not runnable**, and saying so is the point.
2. **The arena check is not an instrument.** The 63/67 figure is recomputed by
   hand from a downloaded `results.json`; there is no `--compare` and no
   committed baseline. It caught real movement (nightly 66/67 → 67/67), so it
   earns its place — but it is a **procedure, not a gate**, and a future dispatch
   should either make it one or stop calling it a guard.

---

## 2026-08-23-lean-tier-16 — NEW CORNER CHARTERED: the export envelope. Three candidates eliminated by measurement, one stands

Thomas recalibrated to months-scale: WAITING is legitimate only for the
genuinely blocked SLICE, and the lane censuses a new corner rather than parking.
Four candidates, censused against upstream `master` `e0e3f6b`. **Three are
eliminated by measurement, and two of them are eliminated for the best possible
reason — the work is already done.**

### The eliminations

**Level arithmetic — ELIMINATED: already complete, and occupied.**

| file | lines | theorems | REAL sorries |
| --- | ---: | ---: | ---: |
| `Verify/Level.lean` | 3 880 | 249 | **0** |
| `Verify/LevelStd.lean` | 540 | 35 | **0** |
| `Theory/VLevel.lean` | 188 | 36 | **0** |
| `Level.lean` | 363 | 0 | **0** |
| **total** | **4 971** | **320** | **0** |

There is nothing to prove: completeness of `normalize'`, `isEquiv'` and `geq'`
all landed (`4ff2346`, `8b51c9c`), the new algorithm was switched on (`3f6e8f9`),
and HEAD adds coNP-hardness. The corner is finished **and** it is where the
author has been working this month.

**WHNF/reduction — ELIMINATED: it is entirely inside the 24 already censused.**
Five sorries across the whole `Verify/TypeChecker/` tree, and every one is
already classified: `inferProj.WF`, `reduceProjCore.WF`, `reduceRecursor.WF`
(TrProj-blocked), `tryEtaStructCore.WF` (TrProj + missing model rule),
`isDefEqUnitLike.WF` (missing model rule). `Basic.lean` (84 theorems) and
`TypeChecker.lean` (20) are **sorry-free**. No new obligations exist here.

**Defeq's non-app fragments — ELIMINATED: they ARE the injectivity cluster.**
`sort_inv`, `forallE_inv_stratified`, `sort_forallE_inv` are the three sorries in
`Theory/Typing/Injectivity.lean` — proved for `SExpr` in `Experimental/` and
awaiting the author's port (entry 6.4). DO NOT ENTER.

### THE CORNER: `lean4export` envelope verification

`leanprover/lean4export`, HEAD `cacf989`. **1 710 lines, 0 theorems, 0 sorries,
22 golden-output `#guard_msgs` tests.** It ships a complete emit/parse dual —
`Export.lean` (438) writes NDJSON, `Export/Parse.lean` (509) reads it back into
`Lean.ConstantInfo`.

**MEASURED OBLIGATION COUNT — 26 emit/parse pairs plus one top-level property:**

| kind | pairs | constructors |
| --- | ---: | --- |
| `Expr` | **11** | bvar, sort, const, app, lam, forallE, letE, proj, natLit, strLit, mdata |
| `Level` | 4 | succ, max, imax, param (`zero` pre-seeded at index 0) |
| `Name` | 2 | str, num (`anonymous` pre-seeded) |
| declaration kinds | 8 | axiom, defn, thm, opaque, quot, induct, ctor, rec |
| `BinderInfo` | 1 | 4 values |
| **total** | **26** | + `parse ∘ dump = id` at the environment level |

### Why this one, by reach-per-cost

**It depends on none of the three holes that block everything else.** No
`addInduct` (serialization needs no constructor data — it *transports* the
declaration, it does not interpret it). No confluence. No no-confusion. It is
**greenfield**: 0 sorries means nothing is inherited, and 0 theorems means **no
verification effort is in flight to collide with**.

**And it is on the reflexive capstone's own trusted list.** Charter §10.5
enumerates what stays trusted after a verified checker: *"the formal spec, the
checker's own compilation and execution, and — if the tier ever wants a number
rather than a proof about a corpus — **the exporter that produced the
environment**. That last one is the quiet one."* **This corner is that quiet
one.** Verifying the round-trip removes a named entry from the capstone's
trusted set — which is exactly the kind of reduction the tier exists to make, and
the only one currently reachable.

It is also **the backlog's original envelope item** and charter §4's subject:
every other tier in the family hand-built an envelope schema and this tier
adopted upstream's unverified. Verifying it closes that asymmetry.

### The honest difficulty, named before starting

**The real content is hash-consing, not JSON.** `dumpExprAux` assigns integer
indices through `getIdx` over a `visitedExprs` table, and `parse` resolves them
back. So the round-trip theorem is not a syntactic induction — it is a statement
that **the index table is consistent**: every index the exporter emits resolves,
under the parser, to the term that produced it. That is ordinary structural work
with an invariant, and it is where the arc's difficulty actually lives.

**Toolchain note:** lean4export pins `v4.34.0-rc2`, two releases ahead of ours,
but commit `af5aa64` sits at exactly our `v4.33.0-rc1` and is byte-identical to
master except one test expectation. The arc starts there.

**Scope caveat, stated plainly:** this verifies a TOOL, not the type theory. Its
reach is the envelope. That is a smaller claim than the TrProj corner's, and it
is the one currently available.

### First arc

1. Re-pin the clone at `af5aa64` (our toolchain) and census the format spec
   (`format_ndjson.md`, 353 lines) against the 26 pairs — a coverage manifest in
   §5.5's shape, which is the instrument this corner owes before any Lean.
2. State the round-trip property and the index-table invariant.
3. Take the cheapest pair — `Level` (4 constructors, no recursion through the
   index table except `succ`) — as the first proof, the same reach-per-cost move
   that opened the TrProj corner with `instL`.

**The TrProj drift guards continue as the background duty** (entry 15); this
corner is the foreground.

---

## 2026-08-23-lean-tier-17 — EXPORT CORNER, arc 1: re-pinned, 27-obligation manifest landed, round-trip property and index invariant stated

### Re-pin: exact

`lean4export` @ **`af5aa64`**, `lean-toolchain` = **`leanprover/lean4:v4.33.0-rc1`**
— identical to ours. Diff against upstream master is exactly what the charter
predicted: **one test expectation and the toolchain line**, nothing else. Format
version **3.1.0**, spec `format_ndjson.md` 352 lines.

### The manifest: `harness/lean_export_manifest.py` -> `docs/lean-export-manifest.json`

A §5.5 manifest joining **three independent sources** — the spec
(`format_ndjson.md`), the emitter (`Export.lean`) and the reference parser
(`Export/Parse.lean`). A round-trip obligation exists exactly where all three
agree an item kind lives; where they disagree the manifest says so.

**27 obligations, and every one resolves in all three sources:**

| category | obligations |
| --- | ---: |
| `expr` | 11 |
| `declaration` | 9 |
| `level` | 4 |
| `name` | 2 |
| `binderInfo` | 1 |
| **total** | **27** |

**Undocumented in spec: none. Nested arrays: `types`, `ctors`, `recs`.**

Four constructors are **not emitted by design** and the manifest records why
rather than scoring them as gaps: `Name.anonymous` and `Level.zero` are
pre-seeded at index 0; `Expr.fvar` and `Expr.mvar` hit a `panic!` — the same
10-of-12 kernel-admissible split §4 of the charter measured.

### THE INSTRUMENT CORRECTED ME TWICE, and one was the audit's defect class again

The charter said **26**; the manifest says **27**. I had missed `parseInductive`,
the wrapper that reads the `types`/`ctors`/`recs` arrays — counting the three
`*Info` parsers but not the group they sit in. **The instrument's count stands.**

Worse, and worth recording plainly: my first declared table keyed the nested
kinds as singular `ctor`/`rec`, which produced **two wrong rows**:

* `rec` reported **UNDOCUMENTED** — but the spec documents `"recs"` at
  `format_ndjson.md:291`. A false gap.
* `ctor` reported an emit site at `Export.lean:407` — which is
  `("ctor", ← dumpName rule.ctor)` inside **`dumpRecRule`**, a recursor rule's
  NAME FIELD, not the constructor declaration at all.

**That is the unanchored / first-hit-wins defect class the 2026-08-23 audit named
in `lean_kernel_census.py`, recurring in a brand-new instrument written after the
audit.** It is the third appearance in this lane's tools. Both rows were caught
by verifying the finding before publishing it — I was one step from writing "the
export spec does not document recursors", which is false. The instrument now
declares emit and spec keys per row and **refuses** when a nested kind's key is
singular, since a singular match there is almost certainly a same-named field.

Contract: sorted JSON, `--compare`, double-run byte-identical, four refusal paths
RUN (missing dir, non-checkout, missing baseline, drift at exit 1).

### THE ROUND-TRIP PROPERTY, stated

Measured mechanism. The exporter hash-conses through `getIdx`:

```lean
if let some idx := m[x]? then return idx      -- already emitted: share it
let s ← rec                                   -- else emit CHILDREN first
let idx := m.size
IO.println (s.setObjVal! namespaced idx).compress
modify fun st => setM st ((getM st).insert x idx)
```

so the emit tables are **value → index** (`visitedNames`, `visitedLevels`,
`visitedExprs`) while the parser's are **index → value** (`nameMap`, `levelMap`,
`exprMap`, `recursorRuleMap`). The property to prove:

> **`parse (dump E) = E`** at the `constMap` level, for every well-formed
> environment `E`.

**And the invariant that carries it — the arc's real content:**

> **(1) TOPOLOGICAL ORDER.** `getIdx` emits children *before* assigning the
> parent `idx := m.size`, so every index is strictly greater than the indices of
> its subterms. Therefore **every index referenced on line *n* was defined on
> some line < *n***, and the parser can always resolve it.
>
> **(2) TABLE INVERSION.** At every point in the line sequence, the parser's
> index→value map is the inverse of the exporter's value→index map on the
> indices emitted so far.

Two conventions the invariant must carry rather than assume: index **0** is
**pre-seeded** on both sides (`.anonymous`, `.zero`) and never emitted; and
`getIdx`'s sharing means `dump` is **not** injective on syntax trees — the same
subterm is emitted once — so round-trip holds *through* the sharing, which is
exactly why the invariant is about tables and not about term structure.

**This is the hash-consing difficulty the charter named prospectively rather than
at inch 3, now stated precisely enough to prove.**

### Next: `Level`, 4 constructors

`succ`, `max`, `imax`, `param` — the cheapest category with real content:
`succ`/`max`/`imax` recurse through the index table (so they exercise invariant
(1)) while `param` bottoms out in a name, and `zero` is the pre-seeded
convention. Same reach-per-cost move that opened the TrProj corner with `instL`.

### Ledger

* **TrProj slice** — 4 proved / 3 blocked, WAITING with triggers (entries 13–15).
* **Export corner** — **0 of 27 pairs proved**; manifest landed, property stated.
