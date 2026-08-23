# The python-completeness lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by
the python-completeness lane.** Ids are `YYYY-MM-DD-pycomplete-<n>` and need
no reservation, because the lane name makes them unique — which this lane can
attest to the value of: its rung-3b landing was written as §L59, renumbered to
§L74, then to §L85, and never landed under any of them, because each number
was taken while the lane sat in the build queue.

**Everything before 2026-08-22 is in `docs/backlog.md`** and stays there; this
lane's history is §L39 (the founding census), §L49 (rung 1), §L51 (rung 2) and
§L53 (rung 3's census), and every one of those references keeps resolving.

The lane's charter is `docs/completeness.md`: close the extractor/interpreter
refusal surface toward ARBITRARY Python, censused before priced and priced
before built. `harness/refusal_census.py` is the scoreboard and the acceptance
battery in one — it exits nonzero on drift, so a landing that moves the tier
must move the census in the same commit.

## 2026-08-22-pycomplete-1 — RUNG 3b: the eight consumers that could never meet the hazard their refusal cited

`list(d)`, `tuple(d)`, `sorted(d)`, `sum(d)`, `max(d)`, `min(d)`, `set(d)`,
`any(d)`, `all(d)` and `[*d]` all run, over the keys, in CPython's insertion
order. **Eight of the ten refusal messages §L39 hung rung 3 on are gone**, and
the grammar census moves **68 → 74 MATCH of 105**.
docs/memory-model.md §the draining consumers, as built.

### The finding this inch exists to prove

§L53 measured that these consumers **drain the keys with no user code running
in between**, so not one of the three mutation regimes — value update, size
change, same-size key-set churn — can arise inside them. Their refusals all
cited "live dict iteration; docs/memory-model.md", a blanket doctrine
inherited from the H1 decision to keep the live cursor out. **A refusal
inherits its REASON as readily as its text**, and only running each consumer
separately separated them.

What they needed was one line — `dictKeys es = es.map Prod.fst`, the entries
array being the insertion sequence already — plus seven value arms, each the
`.list` arm sitting beside it in the same `match`.

### The price was 19 walker arms, and §L53 called it

The census recorded the risk before the inch was written: *"`PayloadBlind`'s
swap-blindness lemmas must be shown to hold for the new dict arms… §L49's
`evalUnaryOpH_swapAt` is the standing reminder that an exhaustive `cases` can
hide behind a grep."* It fired, and wider than for one operator:

| walker | arms | why it broke |
| --- | --- | --- |
| `ClockErase` | 12 | `cases obj <;> try exact .unsupported` — the `try` silently absorbed the dict arm while it refused, and leaves the goal open once it decides |
| `PayloadBlind` | 7 | `\| _ => exact PBF.unsupported` catch-alls, plus the two `sortedValH` helper lemmas (`_swapAt`, `_slot`) whose `\| _ =>` arms had the same shape |

Every one is the adjacent `.list` arm's tactic verbatim. **The rule §L49
started now sharpens:** a change that makes a previously-REFUSING arm DECIDE
costs exactly as many proof arms as there are walkers whose catch-all was
leaning on that refusal. A refusal is not free in the proof layer — it is a
case someone else is standing on.

Payload-blindness holds structurally: a `PayloadTwin` is `.generator …
.running` on BOTH sides, so the swapped slot can never hold a dict; the new
arms read entries at an address the twin cannot be.

### The regression guard that flipped IS the acceptance signal

`Examples/python/star_lab/spec.lean` asserted `star_dict` refuses. `[*d]` now
answers CPython's `['x', 'y']`, so the build failed on that `#guard` — the
`%`-formatting landing's signal, at the one pre-existing expectation this inch
moves. It became a `#py_check` of the real value and its `cases.json` row
moved `unsupported` → `match`.

### What did NOT move, deliberately

The live cursor (`for k in d`, inch 3a) is untouched, and
`dict_lab.keys_for_is_still_loud` is the row that says so. The view methods
and `enumerate(d)` are inch 3c. The same-size churn regime stays
**permanently loud**, with §L53's cross-rung note standing: it is unreachable
today only because `del d[k]` refuses first, and becomes REQUIRED the day dict
deletion lands.

### THE OPERATIONAL LESSONS, paid for in full

This inch was built, verified green, and LOST — `/private/tmp` purged with the
commit unpushed while the lane queued on the build lock. It was rebuilt from
the recipe §L53 had already pushed: **the census survived because the census
was pushed.** Then it was nearly lost a second way, and that one is worth more
than the first:

* **`origin` in the seeded clones is a STALE LOCAL BUNDLE**
  (`~/repos/lean-surfaces-backup/…-20260814-….bundle`); the live remote is
  `github`. A lane that seeds a clone with `cp -Rpc` (§7 A13) inherits BOTH
  remotes, and `git reset --hard origin/master` silently lands it on
  2026-08-14 — a tree where this lane's own four landings do not exist. It
  also makes `git rev-list --count HEAD..origin/master` report `0` while the
  clone is a week behind, and makes a feature branch look "238 commits ahead
  of master". **Check `git remote -v` after seeding, and reset to
  `github/master`.**
* **A seeded clone inherits the seed's BRANCH.** `lean-es` was on `master`,
  but the first seed attempt (`lean-pyc2` from an earlier `lean-es`) came up
  on `pyrebuild-monadic`. Verify `git rev-parse --abbrev-ref HEAD` before
  building — a triad run on the wrong branch verifies nothing about master,
  and this lane spent one whole tenure discovering that.
* **Push on the FIRST green triad, before any fetch-rebase.** The verified
  state at first green is a landing; holding it for a post-rebase
  re-verification converts a landing into an exposure. Rebase and re-verify
  after the push.
* **Killing an out-of-tenure build costs almost nothing** — lake caches
  completed modules, so a killed build resumes where it stopped. Nobody
  should hesitate to kill their own build to protect the machine.

### Battery

`Examples/python/dict_lab` gains 17 functions / 33 `cases.json` rows: the
ORDER-observing rows (insertion order out of sort order, an overwrite keeping
its ORIGINAL position, `list(d)[0]`), every consumer, the empty-dict `max`
`ValueError` through the shared arm, non-int keys through the generic ordering
path, the `True`/`1` key-collision rule, the empty dict, and the still-loud
live cursor. Census: six `dict.*` witnesses flip REFUSE → MATCH.

## 2026-08-22-pycomplete-2 — the §9.4 DIVERGE/DIVERGED violation, closed

`harness/library_survey.py` emitted the family's failure verdict under two
names. The Go lane pinned the mechanism exactly — a deliberate rename at the
EMISSION BOUNDARY (`row["verdict"] = "DIVERGED" if verdict == "DIVERGE" else
verdict`) sitting downstream of eleven sites that already produced the
canonical `DIVERGE` — so the fix was mechanical rather than a redesign.

Eight sites: the translation is deleted, the direct set and its detail string
say `DIVERGE`, and the six consumers keyed on the drifted name follow it —
scoreboard order, the title/verdict pairing (which was `("DIVERGED",
"DIVERGED")`, a display title and a selector that had drifted TOGETHER, so
neither half revealed the other), and both exit gates.

**§5.4 both-directions discipline verified, not assumed**: both gates read
`return 1 if (counts.get("DIVERGE") or counts.get("INCOMPLETE")) else 0` — they
fail on a divergence or an unfinished battery and pass otherwise, and they now
key on the same string the 18 emission sites produce. Before the fix the gates
keyed on `DIVERGED`, which only worked because the boundary translation fed
them; delete that translation alone and the gates would have gone silent. The
two halves had to move together, which is why the audit's "one emits both" row
was the right tell.

`harness/library_oracle.py`'s `DIVERGED` is prose in a comment, not an
emission; normalized anyway so the vocabulary is single-valued in `harness/`.
`docs/duplication-audit.md`'s row is updated to record the fix rather than
left asserting a defect that no longer exists.

---

## INBOUND FROM THE SOFTFLOAT LANE — `2026-08-22-softfloat-6` (Python lane's to triage)

*Filed by the SoftFloat lane during its core census
(`docs/softfloat-charter.md` §2.5). Id kept in the SoftFloat namespace.*

### `docs/completeness.md` §6's FLOAT RUNG IS DEFERRED ON A LEAN-SIDE PREMISE THAT IS FALSE AT THE PIN

Lines 368-373:

> * **`float`** — the largest gap by value and by price simultaneously. Four
>   grammar rows depend on it … but a DECISION: **Lean's `Float` is not
>   kernel-reducible**, so `#py_check` and every captured `rfl` run would break
>   on it — the same family as **the mergeSort trap**. It needs an owner-gated
>   design (an exact-rational …)

**Measured on `leanprover/lean4:v4.33.0-rc1`, and the premise no longer
holds.** `Float` is a plain structure over `Float.Model`, which is a structure
over a `BitVec` with a validity proof, and the arithmetic is ordinary Lean.
`((0.1 : Float) + 0.2 == 0.30000000000000004) = true` closes by **`rfl`**;
`+ − × ÷` all close by `rfl` and by `decide`, at binary16, binary32, binary64,
binary128 and binary256.

**The mergeSort intuition was right about the FAMILY and wrong about the
SCOPE.** There *is* a well-founded-recursion wall, and it costs exactly one
operation: **`sqrt`**, because `Nat.sqrt` is defined with
`termination_by guess` (`Init/Data/Nat/Sqrt/Basic.lean`). Isolated,
`Nat.sqrt 49 = 7` fails both `rfl` and `decide`. Everything else reduces.

**Two of your four grammar rows change price accordingly:** `const.float` and
`op.Div` are unblocked on the Lean side today. `op.Pow` with a negative
exponent is too. **`str`/`repr` of a float is NOT** — `Float.toString` is
`opaque` and core ships no decimal-printing model at all, so shortest-round-trip
printing is a real algorithm someone has to write. It is SoftFloat plan step 3
(`docs/softfloat-charter.md` §3), and this lane will build it; you do not need
to.

**And your own instinct was the right design.** §6 asks for *"an exact-rational
…"* design, and that is precisely what SoftFloat layer 2 is:
`LeanModels/SoftFloat/Basic.lean` defines `Q` — an unnormalized rational whose
comparison is cross-multiplication — because every finite float's value is
dyadic and every `+ − × ÷ √` result on finite inputs is rational. **ℝ never
appears.**

**One warning that applies directly to `#py_check`.** `#guard` runs Lean's
**untrusted evaluator** (`unsafe evalExpr`; core's own docstring: *"this uses
the untrusted evaluator, so `#guard` passing is not a proof"*). It honours
`@[extern]`, so on a float row it attests **the host C runtime, not Lean** —
and it passes identically whether the declaration reduces or is `opaque` with
no body. Measured three ways in `harness/softfloat/probe_walls.lean`. If
`#py_check` is `#guard`-shaped, its float rows will go green on facts the
kernel cannot check. A reduction gate is `rfl` or `decide`.

## 2026-08-23-pycomplete-3 — INCH 3a's CENSUS: the capability is one arm on the new definition and ~35 on a SHARED datatype

Inch 3a is the live dict cursor — `for k in d` at function scope, and the
bare-key form — on the MONADIC interpreter, per the no-backwards-compat
ruling. **The census was taken before a line was written, and it says the
ruling cannot be satisfied as stated at this inch.** Not because the monadic
control is hard: because the thing that has to gain a case is not the
interpreter, it is the CONTINUATION TYPE, and that type is shared.

Branch: `pyc-3a` off `github/pyrebuild-monadic-gate-green` (98f8d9dc), both
identity dimensions checked — remote is `github`, not the stale
`origin` bundle (§2026-08-22-pycomplete-1), and the tip matches gate-green.

### The static surface, measured

The monadic interpreter refuses live dict iteration at exactly **four** sites
— three for the cursor and one already covered by rung 3b on master:

| site | what refuses |
| --- | --- |
| `Monadic/Eval.lean:1369` | the `for` dispatch's `.dict` arm — the loop never starts |
| `Monadic/Eval.lean:1392` | the `.forList` cursor re-reading a dict address |
| `Monadic/Script.lean:150` | the script shell's own `for` arm |
| `Monadic/Eval.lean:237` | the draining consumers (rung 3b's territory; **not** on this branch — it landed on master after the branch was cut, and arrives by merge) |

So the cursor itself is **one new `execGen` arm** in `Monadic/Eval.lean`, plus
the script shell's. That half is small, and it is genuinely monadic-only.

### THE FINDING: `GenFrame` is shared, so "monadic-only" does not reach this capability

A faithful live cursor cannot reuse an existing frame. `GenFrame.forSeq`
carries `remaining : List RVal` — **a snapshot**, which §L53 measured to be
the wrong semantics (mutation during iteration must be observed);
`GenFrame.forList` carries `(addr, i)` and re-reads, which is the right
*shape* but the wrong object and carries no size/version to guard with. The
cursor needs its own constructor, carrying the dict address, the index, the
size at entry and the `shapeVersion` at entry.

`GenFrame` is declared in **`LeanModels/Python/Runtime.lean`** — the SHARED
runtime, not the monadic sibling. `Monadic/Substrate.lean` says so by design:
the rebuild "re-presents the interpreter's CONTROL", reusing the trunk's types
and pure workers verbatim, and the generator continuation is one of those
types (it is reachable from `Obj.generator`, which lives in the shared heap).

Seven files walk `GenFrame` exhaustively (measured by the `countFrom` arm,
which every exhaustive walk must mention):

| file | role | arms owed |
| --- | --- | --- |
| `Runtime.lean` | the declaration | 1 |
| `Semantics.lean` | the TRUNK interpreter (`execGen`, `stepIter`, the frame walkers) | ~6 |
| `VCGen.lean` | the VC layer's frame reasoning (26 `countFrom` mentions) | the bulk |
| `ClockErase.lean`, `Obs.lean`, `PayloadBlind.lean` | the proof walkers | ~1 each, expected vacuous |
| `Monadic/Eval.lean` | **the capability** | 1 |

**So the split is roughly 1 arm of new capability to ~35 arms of shared-type
maintenance, and all ~35 are in the legacy walker's files.** That is the
§L49/§L53 law one level up: a constructor is not free, and the bill is paid by
whoever exhaustively matches the type — here, the interpreter the ruling says
not to touch.

### The recommendation, and it is a scheduling one

**Sequence inch 3a AFTER the monadic branch merges to master**, not before.
The ~35 trunk arms are throwaway if the trunk is retired at the merge, and
load-bearing if it is not — and which of those is true is exactly what the
merge decides. Building them now spends the cost in the one window where it
is guaranteed to be either wasted or immediately rewritten.

Nothing else in the inch changes: the semantics are settled and already
measured (§L53), the guards are known (size change → CPython's faithful
`RuntimeError`, same-size key-set churn → permanently loud), and the
`shapeVersion` field the guard needs already exists in `Obj.dict` and is
already maintained by `dictStore`. **This is a census that moves a date, not
a design.**

### Owed

The dynamic baseline — `harness/refusal_census.py` run against BOTH
interpreters (`--runner "lake exe leanmodels-run --monadic"`) — is queued
behind eight tickets at the time of writing. It is telemetry, not a gate for
this entry's conclusion: the four refusal sites above are read off the
monadic source, and the `GenFrame` count is read off the seven walkers. The
run will additionally extend the acceptance gate's trunk/monadic parity claim
from the 1394 differential rows to the census's 105 grammar witnesses, which
is worth having on the record either way.

## 2026-08-23-pycomplete-4 — THE CENSUS CORRECTS ITSELF: the price is ~9 arms, not ~35, and the recommendation REVERSES

§2026-08-23-pycomplete-3 priced inch 3a's shared-datatype cost at "~35 arms"
and recommended deferring the inch until after the monadic merge on that
basis. **The number was wrong by roughly 4x, the error was mine, and it was
the exact mistake this lane has now made twice.**

### What went wrong

The count came from `grep -c countFrom` per file — **mentions, not match
arms.** `VCGen.lean`'s 26 mentions, which supplied "the bulk" of the estimate,
are LEMMA NAMES and per-frame statements (`genSteps_countFrom`,
`genYieldsPrefix_countFrom`), not exhaustive matches. VCGen proves facts about
*particular* frames; a new frame simply has no lemma until someone wants one.

Counting actual pattern positions
(`grep -cE '(\| *\.?countFrom|case +\.?countFrom)'`) gives:

| file | real arms | what they are |
| --- | --- | --- |
| `VCGen.lean` | **0** | per-frame lemmas, not a walk |
| `Runtime.lean` | 2 | the constructor, and one `GenFrame` predicate arm |
| `Semantics.lean` | 3 | two GROUPED catch arms (`\| .enumSeq .. :: _ \| .enumList .. :: _ \| .countFrom .. :: _`) and the trunk `execGen` arm |
| `ClockErase.lean` / `Obs.lean` / `PayloadBlind.lean` | 1 each | one line each, of the shape `simp only [execGen]; exact …` |
| `Monadic/Eval.lean` | 1 | **the capability** |

**≈9 arms total**, of which one is the capability, three are one-line proof
arms, and the rest is declaration and bookkeeping. Under the ruling the
trunk's `execGen` arm is a `refuse` — the capability does not open there — so
it is one line, not an implementation.

### This is §L49's law, recurring, and the third time is not a coincidence

* §L49: a `\.usub` grep found every `match` position and missed every
  `cases op with \| usub =>` arm — **one character**.
* §L53/§2026-08-22-pycomplete-1: the walker price was predicted from the
  `.list` arms and came in at 19, because catch-alls were load-bearing.
* Here: mention-count read as arm-count, **4x high**, and the inflated number
  was about to move a date.

The rule this lane now writes down for itself: **a count that prices a
decision must come from the pattern position, never from the identifier.**
`grep -c <ctor>` answers "who talks about it"; only `grep -cE '\| *\.?<ctor>'`
answers "who must gain a case". The upstream commit title from the same day —
*"a grep that agrees with you is the one to re-run"* — is the same finding
arriving from another lane, and it should be read as a family law.

### The recommendation, reversed

**Inch 3a is affordable now and does not need to wait for the merge.** ~9
arms, one of them the capability and three of them one-liners, is an inch, not
a campaign. §2026-08-23-pycomplete-3's scheduling conclusion is WITHDRAWN;
its static surface map (four refusal sites, the snapshot-vs-cursor argument
for why a new constructor is unavoidable, and `shapeVersion` already existing
in `Obj.dict`) stands unchanged, because those were read off pattern positions
and source text rather than off a counter.

The one substantive point that survives from the earlier entry: **`GenFrame`
is shared, so this capability cannot be opened on the monadic definition
alone** — the trunk gains a `refuse` arm and three walkers gain a line each.
That is a fact about the type's home, and it is worth a ruling, but it is a
9-line fact rather than a 35-line one.

## 2026-08-23-pycomplete-5 — INCH 3a BUILT: the live dict cursor, on the monadic definition only

`for k in d` runs on the monadic interpreter, at BOTH scopes, with the three
regimes §L53 measured against CPython 3.9.19. The trunk gains a refuse arm and
nothing else, per the ruling. **Queued for verification at the time of
writing** (queue depth 9); this entry records what was built and why, and the
triad's numbers land with the next push.

### What the ruling bought, and what it cost

| file | change | kind |
| --- | --- | --- |
| `Runtime.lean` | `GenFrame.forDict` + its `WF` arm | shared type grows (ruled) |
| `Semantics.lean` | `genBreak`/`genContinue` arms + the trunk's `execGen` REFUSE arm | legacy contract: compiles, refuses, gains no consumers |
| `ClockErase/Obs/PayloadBlind` | one line each | walker bookkeeping |
| `Monadic/Eval.lean` | the dispatch builds the frame; the cursor arm | **the capability** |
| `Monadic/Script.lean` | `SKont.forDict` + `scriptForDictAt` + wiring | **the capability**, module scope |
| `Monadic/Prim.lean` | `dictStepM` | the new primitive |
| `Monadic/Spec.lean` | `dictStepM_spec` | its `@[spec]` lemma |

Measured at ~9 shared arms in §2026-08-23-pycomplete-4; that held.

### `genBreak`/`genContinue` are the arms a mechanical patch gets WRONG

`forDict` is a LOOP frame: `break` must pop it and `continue` must keep it, so
it belongs with `forSeq`/`forList`/`forGen`/`whileLoop` and NOT with the
builtin-iterator group (`enumSeq`/`enumList`/`countFrom`), which returns
`Option.none` because those frames have no body and flow can never reach one.
A patch that added `forDict` to the refusing group would have compiled and
been silently wrong for every `break` in a dict loop.
`dict.for-in-function` exercises exactly that — it `continue`s past a key and
`break`s early — which is why the witness is written that way.

### The step is a PURE PLAN, because the walker law says it must be

AGENTS.md records that `execGen` MUST fork on a pure plan (`genPlan`'s
precedent): with the match inline, the equation compiler splits the arm per
constructor and `simp only [execGen]` never fires at a symbolic frame. So the
three regimes are `DictStep` — `resized` / `rekeyed` / `yieldKey` / `done` —
decided by the pure `dictStep`, and BOTH cursors fork on it. One decision, two
consumers, no drift; and `dictStepM` lifts it to one action with one `@[spec]`
lemma instead of a heap read plus a decision that `mvcgen` must re-split at
each call site. `dictStepM_spec` says the step leaves the state UNCHANGED —
a cursor must not disturb the dict it walks, and that is now a theorem.

### THE GATE COULD NOT EXPRESS A RULED DIVERGENCE, and that is an instrument finding

`harness/monadic_gate.py` asserts trunk/monadic PARITY and exits non-zero on
any divergence whose monadic answer is not a `monadic-rebuild:` frontier
refusal. **Inch 3a creates a legitimate divergence on purpose** —
`dict_lab.iter_dict` refuses on the trunk and returns `1` on the rebuild — so
the ruled inch could not have landed green, and the wrong fix would have been
to switch the gate off.

The gate now has an `OPENED` classification, and its design is what keeps it
honest: **a row counts as OPENED only when the rebuild's answer MATCHES
CPYTHON.** If the rebuild diverges from the oracle it is a FINDING no matter
what the table says, because the adjudicator is CPython and never the table.
This is the same shape as the two other instrument gaps this lane has hit —
a check whose vocabulary cannot express a legitimate new state
(§2026-08-22-pycomplete-2's `DIVERGE`/`DIVERGED`, and the census's own
trunk-vs-monadic expectations below).

### The census becomes a TWO-INTERPRETER scoreboard

A witness may now carry `mono=` — the expectation under `--target monadic`,
when it differs. Four do, all of them this inch: `dict.for`,
`dict.for-in-function`, `dict.update-value-during-iter` and
`dict.grow-during-iter` are REFUSE on the trunk and MATCH on the rebuild.
`dict.churn-during-iter` stays REFUSE on both — `del d[k]` refuses first, so
the same-size churn hazard remains unreachable, exactly as §L53 recorded.

Encoding the divergence beats switching the parity check off: the census keeps
gating BOTH interpreters, and the rows where they differ ON PURPOSE are
written down rather than tolerated. 106 witnesses now.

## 2026-08-23-pycomplete-6 — THE FIRST TICKET WAS RED, and both reds were findings the witnesses were written to catch

Inch 3a's first verification came back **build green, gates RED**, on two
independent counts. Neither was a proof failure and both were real.

### RED 1 — the inch was HALF WIRED, and `dict.for-in-function` is what caught it

`dict.for` (module scope) MATCHED. `dict.for-in-function` REFUSED against a
recorded MATCH. The monadic interpreter has **THREE** `for` entry paths, not
the two the static census named:

| path | who takes it | wired in the first attempt? |
| --- | --- | --- |
| `execGen`'s `.forList`/`.forDict` frames | a GENERATOR body | yes |
| `SKont.forList`/`.forDict` | module scope | yes |
| **`Kont.forList`/`.forDict`** | an ORDINARY `def` — **the commonest path of all** | **NO** |

The third is `Monadic/Prim.lean`'s `Kont`, a *different record* from the script
shell's `SKont`, and its dict arm sat one screen below the one I patched. A
census that had stopped at "grep the refusal messages" would have shipped a
cursor that worked in generators and at module scope and refused in every
ordinary function — and the diff_test battery would NOT have caught it,
because the trunk refuses those rows too, so trunk/monadic parity holds while
both are wrong.

**The witness was written to exercise `break` and `continue` through the new
frame, and it earned its place twice over: it caught a missing ENTRY PATH, not
the flow control it was aimed at.** §L14's law again — a statement-level count
is not an ingestion verdict; run the thing.

### RED 2 — rung 3b never reached the rebuild, and the merge is where it was lost

25 divergences, every one a `keys_*` or `star_dict` row: **the trunk
implements the draining consumers and the rebuild does not.** Rung 3b landed
on the trunk (2026-08-22-pycomplete-1) while the monadic branch was already
cut, and the merge carried the trunk's arms without carrying the capability
across the presentation boundary. That is a defect on master that predates
this inch; the gate run is what surfaced it.

**The fix is ONE line, and the reason is the rebuild's own factoring.** The
trunk pays rung 3b seven times — one arm per consumer, each beside its own
`.list` arm. The rebuild has `iterValues`, the single dispatch `sum`/`tuple`/
`list`/`set`/`any`/`all` all share, so the same capability is one arm there.
`sorted`/`max`/`min` needed nothing at all: they route through the SHARED
trunk workers (`sortedValH`/`extremumValH`), which is `Monadic/Substrate.lean`'s
"maximal trunk" claim paying off in a measurable way — those four rows were
already green in the red run.

### What did NOT need changing

The census expectations were already right: the four `mono=` divergences and
the trunk column both stated the intended end state, so the fixes made the
recorded expectations true rather than the expectations being edited to match
the code. **That is the direction a scoreboard has to move in**, and it is
only possible because the expectations were written from CPython's measured
behaviour (§L53) rather than from the model's.

## 2026-08-23-pycomplete-7 — the second ticket: 25 divergences → 1, and the last one was a NAME that stopped being true

Ticket 2: build green, `diff_test` 1427/0/118, both `script_corpus` runs
65/0/50/15, trunk census 0 drifts, **monadic gate 1425/1427 parity with 1
CAPABILITY OPENING** (`iter_dict` — the `OPENED` bucket firing exactly as
designed: trunk refuses, rebuild runs, CPython agrees). The two fixes worked.

Two remainders, and they were the same fact reaching two instruments:

* the gate's last divergence — `keys_for_is_still_loud(7)`
* the census's two whitelist drifts — `iter_dict` and
  `keys_for_is_still_loud` "whitelisted but the model answered ok"

**`keys_for_is_still_loud` is a row I wrote in rung 3b**, whose comment read
*"the LIVE cursor is a separate inch (3a) and stays refused"*. Inch 3a landed
it. The row did not break — **its NAME made a claim that stopped being true**,
and the instruments correctly convicted the name.

It is renamed `keys_for_live_cursor`: it names the CONSTRUCT rather than a
verdict, which is the durable choice, and its comment now records that the
trunk refuses it by the ruling while the rebuild runs it. A name that asserts
a verdict has a shelf life; a name that asserts a construct does not.

### The whitelist half of the census gains the column the grammar half had

`MONO_OPENED` — whitelisted rows (the TRUNK refuses them) EXPECTED to answer
under `--monadic`. The split that keeps it honest is explicit: **the census
records intent and never adjudicates**, because it runs one interpreter and
never sees CPython's answer for those rows; proving the rebuild RIGHT is
`monadic_gate`'s job, whose `OPENED` bucket counts a row only when the rebuild
matches the oracle. Census records, gate adjudicates.

That is the fourth instrument this lane has had to teach a new legitimate
state, after `DIVERGE`/`DIVERGED`, the census's grammar column and the gate's
`OPENED`. The pattern is now unmistakable: **during a re-founding, every
two-sided check needs a vocabulary for "these differ on purpose", and the
default vocabulary never has one.**

## 2026-08-23-pycomplete-8 — INCH 3c's CENSUS: a view is a LIVE OBJECT, and the three views are not one construct

Measured on CPython 3.9.19 before any design. The headline is that
`.keys()`/`.values()`/`.items()` are **not** three spellings of one thing, and
the differences are exactly where a reasonable-looking model would be silently
wrong.

### What a view IS

| probe | CPython |
| --- | --- |
| `type(d.keys())` | `dict_keys` — an OBJECT, not a list |
| `k = d.keys(); d[2] = 'b'; list(k)` | `[1, 2]` — **LIVE**, it still sees the dict |
| `len(d.keys())` after growth | tracks the dict |
| `d.keys()[0]` | `TypeError: 'dict_keys' object is not subscriptable` |
| `list(reversed(d.keys()))` | works (3.8+) |

### THE TRAP, and it is the finding of this census

| probe | CPython | why it matters |
| --- | --- | --- |
| `d.keys() == {1, 2}` | **True** | keys compare as a SET |
| `d.items() & {(1,'a')}` | `{(1, 'a')}` | items are set-like too |
| `d.values() & {1}` | **TypeError** | values are NOT set-like |
| `d.values() == d.values()` | **False** | a values view defines NO equality, so it falls back to IDENTITY |

**`d.values() == d.values()` being False is the row to keep.** Two views of the
same dict, compared, answer False — and a model that treated the three views
uniformly (or that made a view compare by contents) would answer True. That is
the silently-wrong direction, and it is also the intuitive one, which is what
makes it worth a witness rather than a sentence.

### Mutation during view iteration is 3a's regime, unchanged

Growth during `.keys()` iteration raises the same
`RuntimeError: dictionary changed size during iteration`; a value update
during `.values()` iteration is fine. So 3c inherits 3a's guards rather than
inventing any — `dictStep` already decides all three regimes.

### `enumerate(d)` needs nothing new either

`enumerate(d)` is `[(0, k₀), (1, k₁), …]` over the keys, `enumerate(d, 5)`
starts at 5, and growth mid-iteration raises the same `RuntimeError`. It is the
key cursor with an index — 3a's frame with `enumSeq`'s counter.

### The split, and it is the same shape as 3b/3a

* **3c-i — views in CONSUMING position.** `for k, v in d.items():`,
  `list(d.keys())`, `sorted(d.values())`, `sum(d.values())`,
  `enumerate(d)`/`enumerate(d.items())`, `dict(d.items())`, `tuple(d.items())`.
  **The view never escapes**, so it needs no object: the call is FUSED with its
  consumer, exactly as the script shell already fuses
  `for … in d.items():`. This is nearly all real usage.
* **3c-ii — views as FIRST-CLASS VALUES.** `k = d.keys()` held across
  statements, set algebra, `==` against a set, `reversed`. This needs an
  `Obj.dictView` carrying the dict's address and the view KIND, plus a
  set-algebra inventory for keys/items and the identity-equality rule for
  values. `dict.view-escapes` is its marker witness.

**3c-i is the inch; 3c-ii is a tier.** Splitting them is not deferral: the
consuming forms are what stdlib and application code actually write, and they
cost no new heap kind.

### Where the refusals live, and the instrument constraint

Two SHARED sites carry almost all of it — `Semantics.lean:2920` (the dict
attribute-call plan, which admits `.get`/`.clear` and refuses the rest) and
`Semantics.lean:3805` (`enumerate()` over a dict). Both are pure workers on
the "maximal trunk", so admitting them serves BOTH presentations, exactly as
rung 3b's `sortedValH`/`extremumValH` already did.

Per the arch lane's end-condition, **3c adds nothing to `harness/monadic_gate.py`**:
the two-model window is closing, so new expectations go in the census's
CPython-written column and in `diff_test`, both of which survive the collapse.
`MONO_OPENED` and the monadic census column are window vocabulary and retire
with the window; when the successor's delete/modify conflict arrives on
`monadic_gate.py`, **the resolution is DELETE** — those +38 lines are
scaffolding, and its two `OPENED` rows become ordinary `diff_test` rows once
there is one interpreter and the differential's other side is CPython.

### Battery

Five new witnesses, all REFUSE today: `dict.values`, `dict.items-consumed`
(3c-i's targets), `dict.view-escapes` (3c-ii's marker),
`dict.values-identity-eq` and `dict.keys-set-algebra` (the two traps). 111
witnesses.

## 2026-08-23-pycomplete-9 — 3c-i CANNOT live in the shared pure workers, and the reason is the doctrine's own trap

The sequencing note asked that 3c-i's footprint stay "inside the two shared
pure workers + witnesses", so the successor's re-merge would be trivially
textual. **That footprint is not achievable for a CORRECT 3c-i**, and the
census already contains the proof. Recording it before a ticket is spent on it.

### Why the shared-worker route is a silent wrong answer

The two shared sites are `Semantics.lean`'s dict attribute-call PLAN (admits
`.get`/`.clear`) and `enumerate()`-over-a-dict. Admitting `.keys()`/
`.values()`/`.items()` in the plan means the call must ANSWER something, and
the only thing a pure plan can answer is a value. A snapshot is the obvious
one — and a snapshot is measurably wrong:

    d = {1: 'a'};  k = d.keys();  d[2] = 'b';  print(list(k))
    CPython: [1, 2]        a snapshot would print: [1]

That is `dict.view-escapes`, already a witness (§pycomplete-8). So the
shared-worker route buys 3c-i by installing exactly the failure the loudness
doctrine exists to prevent, in the one shape the census had already measured.
**The constraint and correctness point in opposite directions, and correctness
wins.**

### What the code says the real footprint is

Fusion is CONTROL, and the repo already knows it: the only view form in tier
today is recognised SYNTACTICALLY at the statement level —
`Monadic/Script.lean`'s `.forStmt target (.call (.attribute d "items" …) …)`
arm. Every consumer (`sum`/`tuple`/`list`/`set`/`any`/`all` via `iterValues`,
`sorted`/`max`/`min` via `sortedValH`/`extremumValH`) receives an ALREADY
EVALUATED `RVal`, so no pure worker can tell `list(d.keys())` from
`k = d.keys()`. Only the call site can.

### The corrected split — and the first piece is genuinely small

* **3c-i-a — `for` over a view, at every scope.** `for k in d.keys():`,
  `for v in d.values():`, `for k, v in d.items():`. **This is one FIELD on
  3a's frame**: `GenFrame.forDict` already carries
  `(target, addr, i, n, sv, body)`, so adding a view KIND turns
  `for k in d` and all three view loops into the SAME cursor, with
  `dictStep`'s `yieldKey` generalised to yield the key, the value, or the
  `(k, v)` tuple. Three cursor paths to touch — the same three 3a taught us
  to check — plus the syntactic recognition. **`for k, v in d.items():` at
  FUNCTION scope is the single most common dict idiom in real Python, and
  today it refuses** (`dict.items-in-function`).
* **3c-i-b — consuming CALLS.** `list(d.keys())`, `sorted(d.values())`,
  `sum(d.values())`, `tuple(d.items())`, `dict(d.items())`. Needs one
  argument-evaluation helper that recognises the view call before evaluating
  it, wired at the consumer sites.
* **3c-i-c — `enumerate(d)`.** Live, so it needs its own frame like `forDict`
  — it cannot ride a snapshot either.

### The recommendation

Take **3c-i-a** as the next ticket. It is the dominant idiom, it is one field
plus arms on machinery inch 3a just landed and verified, and its footprint is
`Runtime.lean` + monadic control + witnesses — the same shape the ruling
already sanctioned for 3a, and about as textual for the successor to re-merge
as anything that touches control can be. 3c-i-b and 3c-i-c follow separately.

**Nothing here touches `harness/monadic_gate.py`**, per the end-condition; the
new witnesses' expectations go in the census's CPython-written column and
`diff_test`.

## 2026-08-23-pycomplete-10 — 3c-i-b hits a STRUCTURAL wall, and the fix is an ingestion rewrite, not a call-site fusion

3c-i-b was built as designed — fuse the consuming call at the ONE site where a
named call's args meet its plan, recognising the view BEFORE evaluating it —
and it does not compile. The verdict is **RED**, the cause is structural, and
it redesigns the inch. Implementation reverted; this entry is the finding.

### The wall

`Monadic/Eval.lean`'s expression half is **structural on `Expr`**. The fused
arm has to evaluate the view's RECEIVER, and the receiver arrives out of a
pure recognizer (`viewArgOf plan args.toList`) — so the equation compiler
cannot see it as a subterm and the block stops being structurally recursive:

    error: LeanModels/Python/Monadic/Eval.lean:631:0: failed to infer structural recursion

**The file says so itself**, three lines above where the fusion went, and the
comment predates this inch:

> the free-scrutinee discipline … is load-bearing twice over — it is also what
> keeps this block structurally recursive, since a mutual member taking the
> SAME `List Expr` is not a decrease.

Checked rather than assumed: every `evalOpen` in that block is applied to a
DIRECTLY MATCHED subterm (`recv`, `iter`, `test`), and the file's only
`match args.toList` — the trace clock's — inspects ARITY and never evaluates a
matched element. There is no precedent for evaluating an `Expr` pulled out of
`args`, because there cannot be one.

### The finding, and it is the mirror of the walker law

§3a recorded that `execGen` MUST fork on a pure plan or `simp only` never
fires. Here the pure plan is what BREAKS the definition: the fuel-free half is
structural on the syntax, so a plan that HIDES the subterm relation costs
exactly what a plan that EXPOSES the constructor bought.

**The rule, for both halves at once: a pure plan may decide WHAT to do, but
never supply a term the definition then RECURSES on.** In the fueled half the
plan is free because fuel is the measure; in the fuel-free half the measure IS
the syntax, and the plan erases it.

### The corrected design — fuse at INGESTION, which the repo already does

Rewrite the ARGUMENT, not the call. At ingestion, when a consuming builtin's
sole argument is syntactically `d.keys()`/`.values()`/`.items()`, rewrite that
argument to a synthetic builtin call over the receiver:

    list(d.keys())   ⇢   list(<dictkeys>(d))

Then the evaluator's existing path evaluates `d` as an ORDINARY argument —
structural, because `d` sits in `args` and rides `evalOpenList` — and
`applyBuiltin` gains one arm answering the element sequence for
`<dictkeys>`/`<dictvalues>`/`<dictitems>`.

This is the repo's own established mechanism, not a new one: `ListComp`
desugars to `list(genexp)` and `yield from <genexp>` inlines, both at
ingestion, both for the same reason — the evaluator should meet a shape it
already handles.

What it costs, and why it is cheaper than what failed:

* **no new `Expr` constructor** — the rewrite lands inside the existing call
  shape, so `Ast.lean` and every walker are untouched;
* **no structural risk** — nothing new is recursed on;
* **no `Mono.lean` cost** — one arm under an existing shape, which the merge's
  measured rule says is free;
* **soundness unchanged** — the rewrite fires only when the view is the
  argument of a consuming call, so `k = d.keys()` is never rewritten and
  `dict.view-escapes` still refuses. The snapshot stays licensed by the SHAPE.

### Cost of this red, recorded honestly

Three tickets. Two were my own defect and the same one twice — a declaration
inserted between a doc comment and its `def`, which Lean reports as a bare
parse error far from the cause. **I had written a scanner for exactly that
after the first, and did not run it on the file I had just edited.** The scan
is now over every changed `.lean` in the diff, not the files I remember
touching. The third ticket is this finding, which no amount of care at the
edit would have avoided — only building it.

One process note worth carrying: a triad's enqueue-tree gate correctly refused
a run after I amended the commit post-enqueue. **Do not touch the tree between
enqueue and acquire** — the amend cost a full queue slot (83 minutes) for a
one-line index regeneration that should have preceded the ticket.

**Provenance.** This entry was WRITTEN on 2026-08-23 and never landed: it lived only on the unlanded branch `pyc-3cib` (`4aa12f7`), while the redesign it produced landed as §pycomplete-11 — which cites it. A citation whose target is on a branch is a dangling citation, and the remedy for a provenance gap is provenance. Recovered here VERBATIM; the `Monadic/Eval.lean` comment it quotes still resolves BY CONTENT (*“a mutual member taking the SAME `List Expr` is not a decrease”*).

## 2026-08-23-pycomplete-11 — 3c-i-b, rebuilt as an INGESTION rewrite, and the third decision site named

`list(d.keys())`, `sorted(d.values())`, `sum(d.values())`, `len(d.keys())`,
`tuple`/`set`/`any`/`all`/`max`/`min` over a view all run — by rewriting the
ARGUMENT at ingestion rather than fusing at the call site:

    list(d.keys())   ⇢   list(<dictkeys>(d))

The evaluator then meets a shape it already handles: `d` rides the ordinary
argument path, so nothing new is recursed on and §pycomplete-10's structural
wall is not approached. `applyBuiltin` gains one arm answering the element
sequence; `callNamePlan` admits the synthetic names.

### THE THIRD PLACE A CONSTRUCT'S MEANING IS DECIDED

A capability audit that reads the extractor and the interpreter will not find
this rewrite, because it is in neither. **Ingestion is a third decision site**,
and it already holds two other constructs:

| construct | decided at ingestion | recorded in |
| --- | --- | --- |
| `ListComp` | desugars to `list(<genexp>)` | docs/memory-model.md §list comprehensions |
| `yield from <genexp>` | inlined into the enclosing body | docs/memory-model.md §yield from |
| **dict views in consuming position** | **rewritten to `<dictkeys>`/`<dictvalues>`/`<dictitems>`** | **here, and `Ast.lean` §the dict-view ingestion rewrite** |

The vocabulary lives in `Ast.lean` (which is what ingestion can see) with a
header naming the precedent, so the next audit finds it from either end.

### The synthetic names are deliberately NOT builtins

`<dictkeys>` and its siblings use the `<genexpr@n>` convention — angle
brackets make them unspellable in Python, so they cannot collide with a user
binding. They are checked in `callNamePlan` BEFORE `isBuiltinName` and kept
OUT of it: that list is the pinned CPython `dir(builtins)` and every arm that
may decide a `NameError` consults it, so adding a synthetic name there would
move a real decision (the §2026-08-15 silent-wrong-answer fix's own lesson).

### The battery is written in the SOURCE spelling, which is the point

Ten new `dict_lab` rows spell `d.keys()`, never `<dictkeys>(d)`. CPython sees
the source text, and **the rewrite is what is under test** — a row written in
the lowered form would exercise the evaluator and skip the pass that produced
it. Two of the ten are the boundary:

* `view_escape_still_loud` — `k = d.keys()` then use. Not a consuming
  position, so ingestion leaves it alone and the tier refuses. CPython
  answers 1; the refusal is what keeps the snapshot honest.
* `view_arg_not_alone_still_loud` — a view that is not the sole argument of a
  consuming builtin is not the recognised shape either.

**The shape is what licenses the snapshot**, and these two rows are how that
claim is falsifiable rather than asserted.

## 2026-08-23-pycomplete-12 — the audit's §python triage

`docs/quality-audit-2026-08-23.md` §python, 14 rows. Fixed in this pass, folded
into 3c-i-b rather than stopping it. Each fix cites the audit.

### The two HIGHs

**`bench_bisect/spec.lean` — the stated reason was FALSE, and it cost the two
functions their oracle.** The block claimed `cases.json` rows were
"inexpressible … `leanmodels-run` parses CLI args as ints only". The runner has
taken canonical typed values for as long as the batch protocol has existed, and
the whole corpus uses them. **Measured before writing anything**: nine value
rows across `bisect_left`/`bisect_right` — including every line of the vendored
docstring's authenticity block — are answered by the model today and agree with
CPython. They are now `cases.json` rows. The ONE row the oracle cannot reach is
`lo < 0`, whose `raise ValueError(…)` is outside the exception tier; it is
whitelisted with that reason. **A false blanket claim was hiding a real,
one-shape gap** — which is the more interesting half: the gap was smaller than
the claim, and the claim is why nobody looked.

**`pins_genmoves.lean` — re-labelled, and the real fix delegated.** The
thirteen boards' expected lists said "Every expected list below IS CPython's
own answer, in CPython's order", present tense, while `gen_moves` appears in
ZERO `cases.json` rows — nothing re-derives them. The wording now says what is
true: TRANSCRIBED from CPython when the reference was written, with a date, and
nothing regenerates them.

The real fix is a generator that survives — the fourteen boards moved to one
data file that both the pin and a Python script read. **Not taken here**: the
boards are defined in the sunfish campaign's own proof files, so it belongs
with whoever owns them. Noted, not claimed.

### The mediums fixed

* **`Monadic.lean`'s header was stated-vs-actual, inverted by the collapse.**
  It said the trunk stays authoritative and the rebuild is merely
  build-checked via a `--monadic` shim. Checked: `Main.lean` now calls
  `callInMono`/`runScriptClockMono` UNCONDITIONALLY, and `--monadic` and
  `monadic_gate` are gone — while `LeanModels/Python.lean` still imports
  `Semantics.lean`. The header now states the actual split: **executable
  behaviour is the rebuild's, proved behaviour is still the trunk's**, held
  together by the pure workers they share. That split is worth stating
  plainly — it is why a capability opening here reaches the harnesses at once
  and the proof layer not at all.
* **`refusal_census.py` printed the ROW count as a PRODUCTION count** — "113
  productions" for a grammar of 81, because edge rows and per-construct
  witnesses are extra witnesses for productions already counted. It says
  `witnesses` now, and the header says "a witness per production, plus
  measured edge rows".
* **`script_corpus.py`'s `default_oracle` degraded silently** `python3.9` →
  `python3` → `sys.executable`, which its own docstring calls the trap. The
  fallbacks stay — a box without the pin should still run it — but each
  degradation now WARNS in the same voice the re-exec warning uses.
* **`docs/completeness.md`'s counts are derivable and were stale.** They are
  marked AS TAKEN, with the instrument named authoritative and the command to
  get live numbers. The taken-tables are deliberately kept: they are what each
  rung was PRICED against, and rewriting them would erase the pricing they
  justify.

### Not fixed, with reasons

* **`PayloadBlind.lean`'s cited line ranges, stale by ~350 lines.** Real, and
  a line-number citation goes stale on every insertion above it — that is the
  defect, not the current offset. Worth one pass converting them to lemma
  NAMES, which do not drift; noted for whoever next edits that file, since
  fixing offsets without changing the form buys one landing of accuracy.

## 2026-08-23-pycomplete-13 — INCH 3c-i-c's CENSUS: `enumerate(d)` is a GENERATOR FRAME, so the Kont record is not touched at all

Measured on CPython 3.9.19 before any design, and read against the tree
before any price. Two findings, and both correct a standing expectation.

### What CPython does — the ORACLE's column, in the SOURCE spelling

| probe | CPython 3.9.19 |
| --- | --- |
| `for i, k in enumerate(d):` | `0 x` / `1 y` — the index rides the KEYS |
| `list(enumerate(d, 5))` | starts at 5 |
| `list(enumerate(d, -3))` | starts at −3 — the start is an `int`, never a `Nat` |
| `enumerate(d, 1.5)` | `TypeError: 'float' object cannot be interpreted as an integer` |
| `list(enumerate(d, start=5))` | works — the KEYWORD spelling is a second shape |
| `next(enumerate(d))` | `(0, 'x')` — it is an ITERATOR OBJECT, not a sequence |
| `list(enumerate(d))` | `[(0, 'x'), (1, 'y')]` |
| `dict(enumerate(d))` | `{0: 'x', 1: 'y'}` |
| `list(enumerate(d.items()))` | `[(0, ('x', 1)), (1, ('y', 2))]` |
| `list(enumerate(d.values()))` | `[(0, 1), (1, 2)]` |
| `len(enumerate(d))` | `TypeError: object of type 'enumerate' has no len()` |
| `list(reversed(enumerate(d)))` | `TypeError: 'enumerate' object is not reversible` |
| `enumerate(d) == enumerate(d)` | `False` — identity equality, exactly `d.values()`'s row |
| `e = enumerate(d)` alone | binds SILENTLY — no output, no error |
| `print(type(e).__name__)` | `enumerate` |
| `print(e)` | `<enumerate object at 0x…>` — an ADDRESS, so unusable as an expectation |
| `e = enumerate(d)`; `d[2]='b'`; nothing | still no error — the guard is on the STEP, not the bind |
| `e = enumerate(d)`; `list(e)`; `d[2]='b'`; `list(e)` | `[(0, 'a')]` then `[]` — an EXHAUSTED enumerate stops checking |

### THE TRAP, and it is §pycomplete-8's, pointing the other way

    d = {1: 'a'};  e = enumerate(d);  d[2] = 'b';  print(list(e))
    CPython: RuntimeError: dictionary changed size during iteration
    a snapshot would print: [(0, 1)]

An escaped `enumerate(d)` **is live**. §pycomplete-8 measured a view answering
`[1, 2]` where a snapshot answers `[1]` — a wrong VALUE. Here a snapshot
answers where CPython RAISES — a wrong OUTCOME. Same trap, opposite direction,
and the second direction is the one a model reaches for first, because
"enumerate materialises its argument" is the intuitive reading. Growth inside
the loop and `del d[k]` inside the loop raise the same `RuntimeError`; a value
update of an existing key is fine (`{1: 'z', 2: 'z'}`) — so all three regimes
are 3a's, unchanged, and `dictStep` already decides them.

### THE STRUCTURAL FINDING: this inch does not touch `Kont`

The sequencing note expected 3c-i-c to be the PAYING case — "its own `Kont`
frame", with the four `Kont`-record touch points in `Monadic/Mono.lean` that
the `fuelMono` maintenance rule charges for a new field. **The code refutes
it.** `enumerate` in this tier is not a loop cursor: `applyBuiltin`'s
`enumerate` arm (`Monadic/Eval.lean`) builds a `GenFrame` through `enumFrame`
and heap-pushes `.generator "<enumerate>" [] [fr] .suspended`, so the object is
first-class ALREADY and every consumer reaches it through `stepIter`,
`execGen` and `forGen` — **all three of which are existing `Kont` fields**.

So: no new field, no new `KontLe` conjunct, no growth in the sixteen
`obtain ⟨…⟩ := hK` destructurings, nothing in `KontLe.bottom` or `kontMono`.
`Mono.lean` is untouched. The maintenance rule does not fire, and the reason it
looked like it would is that `for k in d` (§3a) and `for i, k in enumerate(d)`
LOOK like the same construct and are not: the first is a loop the interpreter
drives, the second is an object the loop consumes.

### The site is a SHARED pure worker, and this time that is CORRECT

`enumFrame` (`Semantics.lean`) is called by BOTH presentations — the rebuild at
`Monadic/Eval.lean`'s `enumerate` arm and the trunk at its own — and its dict
arm is today's refusal (*"enumerate() over a dict iterates its keys — outside
the tier"*). §pycomplete-9 ruled the shared-worker route a silently wrong
answer for the VIEWS, and that ruling **does not extend here** — the reason is
the RETURN TYPE. A pure plan admitting `.keys()` can only answer a VALUE, and
the only value available is a snapshot. `enumFrame` answers a **`GenFrame`** —
an address plus a cursor — which *is* the live object. The constraint and
correctness pointed in opposite directions for 3c-i-b; here they point the
same way.

### The price, by the `enumList` precedent — the frame it is modelled on

`enumDict (i : Int) (a : Addr) (cur n sv : Nat)` sits beside `enumList`, which
is already the live-cursor-over-an-address frame, and `n`/`sv` are 3a's two
guards. `enumList` is not a hypothetical sibling: `gen_lab::enum_list` walks
`for i, v in enumerate(xs)` over a HEAP LIST today, through `forGen` over a
heap-pushed `.generator "<enumerate>"`. The dict case is that path with a
different step decision.

| site | file | what |
| --- | --- | --- |
| constructor | `Runtime.lean` §generator continuations | one arm beside `enumList` |
| well-formedness | `Runtime.lean` `GenFrame` addr guard | `a < h.size` |
| ingestion | `Semantics.lean` `enumFrame` | the dict arm, replacing the refusal |
| classifiers ×2 | `Semantics.lean` (the two `Option.none` GenCont rows) | one pattern each |
| step | `Monadic/Eval.lean` `execGen` | reuse `dictStep … .keys` — all three regimes already decided; the `(i, k)` tuple is the FRAME's, not the cursor's, so `DictViewKind` gains nothing |
| step (trunk) | `Semantics.lean` `stepIter` | one arm, REFUSING — the `.forDict` template sits directly above it |
| `PayloadBlind` / `ClockErase` / `Obs` | one arm each | mechanical; the obligations are checked below and all four are free |
| `VCGen` | `GenSteps` / `GenSilent` | two transition theorems, if `enumList`'s precedent is kept |

**Where the executable capability lands, and where it does not.** The
rebuild's `execGen` STEPS the frame; the trunk's `stepIter` REFUSES it — the
arrangement §pycomplete-5 sanctioned for 3a, and the one the current split
states outright (*executable behaviour is the rebuild's, proved behaviour is
still the trunk's*). The template is already at the very site the new arm lands
beside: *"this interpreter never CONSTRUCTS a `forDict` frame … the arm exists
to compile and to refuse, and gains no consumers"*. One definition of
`enumFrame`, one place that steps it, and no duplicated decision.

**The trunk-side proof obligations were CHECKED, not assumed**, because
ruling (c) below makes the trunk BUILD the frame and `enumFrame` is a heap
reader. Every consumer of `enumFrame` was read, and all four are free:

* `PayloadBlind.enumFrame_swapAt` proves the frame blind, and the new dict arm
  reads `es.size` and `shapeVersion` out of a heap object — payload, on the
  face of it. It still closes with the proof it already has: `PayloadTwin o₀ o`
  requires BOTH sides to be `.generator q _ _ .running`, so
  `Heap.get?_swapAt_twin`'s twin branch lands on `enumFrame`'s GENERATOR arm on
  both sides, and the dict arm is reachable only in the branch where the two
  lookups are literally equal. **The swapped slot can never hold a dict** —
  §pycomplete-1's rung-3b argument, unchanged, at a different worker.
* `ClockErase` and `PayloadBlind` reach the `enumerate` arm through
  `cases … : enumFrame …`, which splits on the `Res` RESULT, not on the
  receiver's constructor. A new arm returning `.ok` adds no goal; it lands in
  the `.ok` branch that already exists.
* `Monadic/Spec.lean` owes nothing either: `dictStepM_spec` is stated for an
  arbitrary `kind` and arbitrary `(a i n sv)`, so the new frame's step inherits
  the `@[spec]` lemma — *"a cursor step must not disturb the dict it is
  walking"* — the moment it is written in terms of `dictStepM`.
* `Obs` never reaches it at all: `enumerate` is carved out of the `heapFree`
  fragment SYNTACTICALLY (`(fname == "enumerate") = false`), beside `sorted`,
  `next`, `count`, `any` and `all`.

So the §pycomplete-1 law does not fire at the CONSTRUCTION site, and the
reason is worth keeping: the law charges for a refusal OTHER PROOFS WERE
STANDING ON. These four were standing on the frame's SHAPE (`Res`, and a twin
that cannot be a dict), not on its refusal — and shape is what the new arm
preserves. The law WOULD fire at the STEP site, which is exactly why the
trunk's `stepIter` keeps refusing: three walkers stand on that one.

### THE DECISION THE CENSUS SURFACED — RULED, and the ruling is (c)

`.forDict`'s template is not a perfect fit, and the difference had to be
settled before a ticket was spent on it. The trunk never BUILDS a `forDict`
frame; it WOULD build an `.enumDict` one, because `enumFrame` is shared. So a
trunk `e = enumerate(d)` that is never stepped answers an object where it
refuses today, and only the first step refuses. Three ways out were on the
table: (a) decide in the trunk too — the three real proof arms above;
(b) refuse in the `enumerate` builtin arm BEFORE `enumFrame`; (c) accept the
delta and WITNESS it.

**Ruled (c).** The reasons, in the order that decides them:

* **The delta is a capability OPENING, not a regression.** CPython answers an
  object at `e = enumerate(d)` too — measured: binding is silent, `type(e)` is
  `'enumerate'`, and growing the dict afterwards raises NOTHING until a step.
  A tier that starts answering there moves TOWARD the oracle. There is nothing
  to defend against; there is a row to write.
* **(b) is §pycomplete-9's warned shape.** A refusal placed before
  `enumFrame` is a SECOND decision site for one construct — the defect that
  entry exists to name, and the same defect §pycomplete-11 had to name a third
  decision site to avoid hiding.
* **(a) buys nothing the oracle does not already answer.** Three trunk proof
  arms is §pycomplete-1's real price, and it is worth paying for a case where
  the trunk's answer is the one under proof. Here the oracle answers, the
  rebuild is what executes, and the arms would certify a decision no runner
  reaches.

So the delta is DECLARED and CARRIED BY A WITNESS, not suppressed — which is
the same move `dict.view-escapes` made for 3c-ii and `star_dict` made for
rung 3b: the boundary is falsifiable rather than asserted.

**The witness cannot be `print(e)`** — CPython answers
`<enumerate object at 0x109333e00>`, an ADDRESS, and printing a value the tier
cannot render exactly is already `set.order`'s refusal class. The spellings
that carry the ruling and are address-free are `print(type(e).__name__)` →
`enumerate`, and the never-stepped mutation row, which prints its own marker
and must NOT raise.

### What 3c-i-c does NOT cover, named so it is not silently assumed

* `enumerate(d.items())` / `enumerate(d.values())` — 3c-i-b's
  `consumesViewArg` deliberately EXCLUDES `enumerate`, because an `enumerate`
  object outlives its call and the rewrite's snapshot is licensed by the shape.
  Composing the view kind with this cursor is its own inch.
* `dict(d.items())` — `dict` is likewise absent from `consumesViewArg`;
  §pycomplete-8 listed it as a 3c-i target and §pycomplete-11 did not land it.
* `enumerate(d, start=5)` — the keyword spelling. `enumStart` reads positional
  arguments only, so this stays `kwargs.callee-kind`.
* `enumerate(d) == enumerate(d)`, `len`, `reversed` — 3c-ii's first-class
  territory, and the identity-equality row is `d.values()`'s row again.

### Battery — FIVE rows, named by CONSTRUCT, expectations written by the ORACLE

Every source below is the SPELLING a program would contain, and every
expectation is CPython 3.9.19's own.

| witness | source | CPython | after the inch |
| --- | --- | --- | --- |
| `dict.enumerate` (exists, the marker) | `for i, k in enumerate(d): print(i, k)` | `0 x` / `1 y` | REFUSE → **MATCH** |
| `dict.enumerate-start` | `print(list(enumerate(d, 5)))`, and `-3` beside it | starts at 5 / at −3 | **MATCH** — the start is an `int` |
| `dict.enumerate-escapes` | `e = enumerate(d)` / `d[2] = 'b'` / `print(type(e).__name__)` | `enumerate`, and NO error | **MATCH** — this row IS the ruled delta |
| `dict.enumerate-resize` | `e = enumerate(d)` / `d[2] = 'b'` / `print(next(e))` | `RuntimeError: dictionary changed size during iteration` | **MATCH** — raises, never snapshots |
| `dict.enumerate-of-items` | `print(list(enumerate(d.items())))` | `[(0, ('x', 1)), (1, ('y', 2))]` | stays **REFUSE** — the excluded composition |

`dict.enumerate-escapes` and `dict.enumerate-resize` are the SAME two
statements with a different third line, and that is deliberate: the pair is
what makes the ruling falsifiable. Binding and mutating must be silent;
STEPPING after the mutation must raise. A model that guarded at bind time
would pass the second and fail the first, and a model that snapshotted would
pass the first and fail the second. Neither can pass both by accident.

One further measurement, recorded because it constrains the step arm and is
satisfied BY CONSTRUCTION rather than by a guard: after exhaustion the size
check stops applying — `e = enumerate(d); list(e); d[2] = 'b'; list(e)` answers
`[(0, 'a')]` then `[]`, not a `RuntimeError`. The frame is popped at
exhaustion, so an exhausted generator never re-reads the dict. A model that
kept `n` live past the end would raise where CPython answers `[]`.
