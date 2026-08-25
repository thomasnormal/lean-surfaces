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

## 2026-08-22-softfloat-6 — INBOUND FROM THE SOFTFLOAT LANE: Python lane's to triage

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

## 2026-08-23-pycomplete-14 — INCH 3c-i-c BUILT: `enumerate(d)` runs, and the census's price held exactly

`for i, k in enumerate(d)`, `enumerate(d, 5)`, `enumerate(d, -3)` and the
escaped-then-stepped forms all run, on a new `GenFrame.enumDict` frame beside
`enumList`. §pycomplete-13 priced this at nine sites and ZERO new `Kont`
machinery; the price held, and two further sites turned out to owe nothing.

### What landed, against the censused site list

| site | what |
| --- | --- |
| `Runtime.lean` | `enumDict (i : Int) (a : Addr) (cur n sv : Nat)`, and its `a < h.size` WF arm |
| `Semantics.lean` `enumFrame` | the dict arm DECIDES — `.ok (.enumDict i a 0 es.size sv)` |
| `Semantics.lean` ×2 | `genBreak`/`genContinue`: a builtin-iterator frame is never a LOOP frame |
| `Monadic/Eval.lean` `execGen` | the step: `dictStepM ad cur n sv .keys`, tuple wrapped at the frame |
| `Semantics.lean` `stepIter` | the trunk REFUSES the step (ruling (c)) |
| `PayloadBlind` / `ClockErase` / `Obs` | one refusal-is-blind arm each |

### The two sites that owed NOTHING, and why that is the interesting half

* **`Monadic/Script.lean` needs no `SKont` field.** A module-level
  `for i, k in enumerate(d)` routes `S.forGen → K.stepIter → execGen` and
  lands on the new arm. §pycomplete-13 said `enumerate` is an OBJECT the loop
  consumes rather than a loop the interpreter drives; the script shell is the
  second record that would have paid for the other reading, and it pays
  nothing. **The finding generalised further than it was stated.**
* **`VCGen.lean` owes no transition theorem.** `genSteps_enumListCons` and
  `genSilent_enumListDone` exist because the trunk STEPS an `enumList` frame.
  The trunk refuses to step `enumDict`, so there is no transition to state —
  a refusal has no `GenSteps` and no `GenSilent`. The censused "optional" is
  now decided: not optional, INAPPLICABLE.

### A witness that would have tested the wrong construct

§pycomplete-13's battery spelled the never-stepped row
`print(type(e).__name__)`. **`type` is in `isPyBuiltinName` and NOT in
`isBuiltinName`** — CPython binds it, the model does not implement it — so
that row would have refused at `type` and been recorded as evidence about
`enumerate`. Caught by reading the two tables before the ticket rather than
by a red build. Re-spelled as `print('bound')`: reaching the print IS the
observation, because CPython's guard is on the step and binding is silent.
**A witness must fail for the reason it names**, and the census's own rule —
witnesses named by CONSTRUCT — does not by itself guarantee that; the
spelling has to be in tier too.

For the same reason `enum_dict_grow_is_loud` was renamed
`enum_dict_grow_then_step` before landing: it named a VERDICT, and the
verdict it named was wrong — the tier REPRODUCES CPython's `RuntimeError`
here (as `dict.grow-during-iter` already did for the bare cursor) rather than
refusing it.

### THE ENVELOPE OUTGREW THE ELABORATOR, and the error did not look like itself

`load_program` builds the module as a LITERAL through the derived `ToExpr`
instances, so the elaborator's recursion depth scales with the ENVELOPE.
`dict_lab` is now the largest in the tree — **611 KB, 101 functions**, against
`gen_lab`'s 272 KB and 53 — and it crossed the default `maxRecDepth` of 512
somewhere between §pycomplete-18's 85 functions (green) and this inch's 101.
Fixed with `set_option maxRecDepth 65536 in` at the `load_program`, the
established precedent (`clock_lab`, `sf_order` use 100000).

**The diagnosis cost far more than the fix, and the reason generalises.** The
recursion limit is hit at the `load_program` line; `dict_lab` is then added
UNCOMPILED; and all ~44 downstream `#guard`/`#py_check` lines report
*"depends on 'dict_lab', which is 'noncomputable'"*. **The visible errors are a
different failure class than the cause**, and they are individually plausible —
they read as "something in the new Python is noncomputable", which sent this
lane hunting generator expressions and `ToExpr` instances. The only error naming
the cause is the FIRST one.

> **A cascade's first error is the causal one, and every later error is
> evidence about the cascade rather than about the defect.**

**AND THE TRIAD'S SUMMARY OMITTED IT** — a finding for the tool, measured
against the kept full log. The summary announced *"first 8 of 46"* and listed
six errors at `spec.lean:102-139`. The full log's FIRST error is
`spec.lean:24:0: maximum recursion depth has been reached`; its LAST are
`spec.lean:140-143`. **The summary showed neither the head nor the tail, and
dropped the only line of a different class.** Truncation would have been
harmless; a labelled-but-unfaithful sample is not, because the surviving lines
are a coherent wrong story. The recommendation is one line: whatever else it
samples, the summary must print the FIRST error verbatim.

### Census deltas

* grammar census **113 → 117 witnesses**; `dict.enumerate` flips
  **REFUSE → MATCH**, joined by `dict.enumerate-start`,
  `dict.enumerate-escapes` and `dict.enumerate-resize` (MATCH) and
  `dict.enumerate-of-items` (REFUSE — the excluded composition).
* `harness/cases.json` **655 → 660 rows**, all five `match`, so
  `diff_test` goes **1456 → 1464 cases** (`1337 → 1345 matched`) with
  `119 whitelisted-unsupported` UNCHANGED — this inch adds capability
  without adding a gap.

  **That number was predicted WRONG before the ticket, and the verdict
  corrected it: 1461 was the prediction, 1464 is the measurement.** A ROW is
  not a CASE — a row carries an `args` LIST, and `diff_test` runs one case per
  arg-tuple, so three of the five rows are two cases each. Same shape as the
  conflation `6b91a8d` recorded when the model's §5.2 `class` was compared
  against `WHITELIST_CLASS`: two counts sharing a noun are not the same count.
  Recorded rather than quietly edited, because §5.4a's rule is that a
  published number is a second artifact — and the corrected one is the
  measurement, not the arithmetic.
* the whitelist census stays **119 rows in 46 classes** and the script census
  **15 rows in 10 classes**, for the same reason.

### What did NOT move

`enumerate(d.items())` still refuses: 3c-i-b's `consumesViewArg` excludes
`enumerate` because the object outlives its call. `dict(d.items())` is still
unlanded. `enumerate(d, start=5)` is still `kwargs.callee-kind`. The
first-class rows — `enumerate(d) == enumerate(d)`, `len`, `reversed` — remain
3c-ii's. And sunfish is untouched: its `enumObj` is `.enumSeq` over a string
snapshot, a different frame entirely.

**§pycomplete-13's "its dict arm is today's refusal" is superseded by this
entry**, and the date on each is what separates them.

## 2026-08-23-pycomplete-15 — THE FLAGSHIP LADDER's CENSUS: `del d[k]` makes a refusal REQUIRED that was only inherited

The R-track measured `bound()`'s AST down to **two refused constructs, both
`TABLE_SIZE` eviction lines**, and both are this lane's live-dict-iteration
family:

    541:  del self.tp_score[next(iter(self.tp_score))]
    511:  del self.tp_move[next(k for k in self.tp_move if k != self.root)]

Both are `del d[<expr>]`, so **inch (1) is the shared dependency** and the
other two are the two ways of producing the key. Censused on CPython 3.9.19
before any design, in the source spelling.

### THE FINDING, and it fires a cross-rung note written two rungs ago

§pycomplete-1 recorded that the same-size KEY-SET CHURN regime *"is
unreachable today only because `del d[k]` refuses first, and becomes REQUIRED
the day dict deletion lands."* **That day is inch (1), and the census now
proves the refusal must stay.**

| churn shape (same size: one `del`, one insert, mid-iteration) | CPython 3.9.19 |
| --- | --- |
| churn at the middle key of 3 | `RuntimeError: dictionary keys changed during iteration` |
| churn at the **first** key of 3 | **no error — the loop completes** |
| churn at the last key of 3 | `RuntimeError: dictionary keys changed…` |
| `del d[2]; d[2] = 9` (same key back) | **no error** |
| 1-key dict, del + add | `RuntimeError: dictionary keys changed…` |
| 8-key dict, churn at key 3 | `RuntimeError: dictionary keys changed…` |
| churn then `break` immediately | **no error**, `[1, 3]` |

**The first probe raised, and a one-probe census would have concluded the
regime is a faithful second `RuntimeError` and told the inch to reproduce
it.** Four shapes later it does not raise at all, and what separates them is
the entries-array layout and the compaction schedule — exactly what
`Semantics.lean`'s `rekeyed` arm already says is not guessable. So the
existing refusal is CONFIRMED BY MEASUREMENT rather than merely inherited,
and inch (1) must keep it while making it reachable for the first time.
*A regime that only ever raised in the probe you happened to write is the
most dangerous kind of green.*

### `del d[k]` — the rest of the oracle's column

| probe | CPython |
| --- | --- |
| `d = {1:'a',2:'b'}; del d[1]` | `{2: 'b'}` |
| `del d[9]` (absent) | `KeyError: 9` — and twice-deleted, and on `{}`, likewise |
| `del d[2]; d[2] = 'z'` | `[1, 3, 2]` — **reinsertion APPENDS**; deletion does not hold the slot |
| `del d[k]` inside `for k in d` | `RuntimeError: dictionary changed size during iteration` |
| `e = d; del e[1]` | `{2: 'b'}` — mutation through the alias, the heap shape the tier already has |

So the value semantics are cheap: remove the entry, and reinsertion is
`dictStore`'s existing append. **`shapeVersion` is the load-bearing half** —
deletion must BUMP it, or the churn guard above cannot fire (a `del` + insert
pair leaves the size unchanged, and size is the only guard that fires today).

### The price: inch (1) touches all THREE decision sites

`delStmt (names : Array String)` cannot represent a subscript target, and the
refusal is upstream of the AST: `Json.lean`'s `"Delete"` arm reads a plain
string array because **the EXTRACTOR's clause 4 admits BARE NAMES only** and
ships everything else as `Unsupported`. So this inch is the extractor, the
ingestion, and the evaluator — the first inch to touch all three sites
§pycomplete-11 named. The additive shape keeps the existing tier untouched: a
new `delSubscript (recv key : Expr)` beside `delStmt names`, so no landed
`del` behaviour moves. `del_lab::del_sub` is the witness that flips.

### Inches (2) and (3) — cheaper, and the 3c-i-c precedent transfers whole

| probe | CPython |
| --- | --- |
| `next(iter(d))` on `{2:'b',1:'a'}` | `2` — insertion order |
| `it = iter(d); next(it), next(it)` | `2 1` |
| `next(iter({}))` | `StopIteration` |
| `next(iter(d), -1)` on `{}` | `-1` — the 2-arg form |
| `type(iter(d)).__name__` | `dict_keyiterator` |
| `it = iter(d); d[2]='b'; print('bound')` | `bound` — **silent** |
| `it = iter(d); d[2]='b'; next(it)` | `RuntimeError: dictionary changed size…` |
| `next(k for k in d if k != root)` | `2`; no match → `StopIteration`; with default → the default |
| `g = (k for k in d); d[3]='c'; next(g)` | `RuntimeError` — the genexp is LAZY and LIVE over the dict |

**That bind-silent / step-raises pair is `dict.enumerate-escapes` and
`dict.enumerate-resize` again, unchanged**, so 3c-i-c's frame is the
precedent for both: an `iterDict` frame is `enumDict` without the index, and
the genexp already has a cursor class. Two cheap notes: `next` ALREADY
implements both the 1-arg and 2-arg forms, so inch (2) gets `next(it, d)`
free; and **`iter` is in `isPyBuiltinName` but NOT in `isBuiltinName`** — the
same two-table gap §pycomplete-14 was caught by — so inch (2) must add it to
the implemented list, deliberately and with the `NameError` consequence in
view.

### The sequencing, and why the flagship's own lines are SAFE

In both flagship lines the `next(...)` is evaluated to a key and the iterator
is then ABANDONED before `del` runs, so the mutation never meets a live
cursor. `del d[next(iter(d))]` answers `{2: 'b'}` and `del d[next(k for k in
d if k != root)]` answers `{1: 'a'}` — measured. The hazard the guards exist
for is real but is not on the flagship's path, which is the honest reason
these are inches rather than walls.

## 2026-08-23-pycomplete-16 — `del d[k]` LANDS as an ingestion rewrite, and the churn guard becomes REQUIRED

`del d[k]` runs, on the flagship's two eviction lines' shared dependency. The
census (§pycomplete-15) priced a `delSubscript` statement constructor; the
re-census before building priced the **`Stmt`-constructor tax** and the design
changed.

### The re-census that changed the shape, and the number that forced it

A new `Stmt` constructor is not one site. **`delStmt` has 28 occurrences
across 9 files; `assertStmt`, the closest precedent, has 22 across 8** — arms
in `heapFree`, the size/termination measure, span extraction, kind naming,
lowering, parsing, plus `Obs`/`PayloadBlind`/`ClockErase`. All mechanical, and
**none of them decide anything.**

So `del d[k]` lowers to **`<dictdel>(d, k)` under an `exprStmt`** — the THIRD
DECISION SITE this lane named in §pycomplete-11, reused. Six sites instead of
twenty-five: the extractor's clause 4, the ingestion arm, the synthetic name,
`callNamePlan`, `applyBuiltin`, and the two pure workers. **Zero `Stmt`
constructors, zero walker arms.** `del` is a statement with NO VALUE and
`exprStmt` DISCARDS the value, so the lowering is exact rather than
approximate, and the name can never appear in expression position because
ingestion emits it only from a `Delete` node — the same argument that licenses
`<dictkeys>`.

*"Re-census when the plan becomes expensive" earned its keep here: the rule
fired on a 4× price difference and the answer was already in this lane's own
toolkit.*

### THE CHURN GUARD IS NOW REQUIRED, and a one-probe census would have inverted it

§pycomplete-1 predicted that same-size key-set churn *"becomes REQUIRED the
day dict deletion lands."* That day is this inch. **The first churn shape
measured raised** `RuntimeError: dictionary keys changed during iteration` — a
faithful second message the tier could plausibly reproduce. Three shapes later
it does not raise at all:

| shape | CPython | tier |
| --- | --- | --- |
| churn at MIDDLE key | `RuntimeError: keys changed` | REFUSE |
| churn at FIRST key | **silent**, answers 102 | REFUSE |
| `del d[2]; d[2]=9` | **silent**, answers 3 | REFUSE |
| churn then `break` | silent, answers 1 | **MATCH** |

What separates them is the entries-array layout and compaction schedule, so
the regime stays LOUD and `dict.keyset-churn` is its class. **The three silent
shapes are honest REFUSEs**: the model refusing where CPython answers is a
witnessed capability gap, and CPython's answer is recorded in each row's
comment so the expectation column stays oracle-written. A MATCH there would
require answering through an unguessable layout — the snapshot sin again.

**The one MATCH is `del_churn_then_break`, and not because CPython was
silent.** `dictStepM` runs at the TOP of each iteration, so the guard fires
only on RE-ENTRY; `break` exits before the cursor re-reads and the guard is
never reached. *Two rows can agree with CPython for entirely different
reasons, and the row that says which is the one worth keeping.*

### `shapeVersion` is the load-bearing half

Deletion bumps it UNCONDITIONALLY, where `heapStore` bumps only on growth, and
the why is in the code: `del d[x]` followed by `d[y] = v` in one loop body
leaves `es.size` exactly as it was, so SIZE — the only guard that fires today
— stays silent and the churn would be walked as if nothing happened. Value
semantics are cheap by comparison: deletion does not hold the slot, so
reinsertion APPENDS (`del d[2]; d[2]='z'` lists `[1, 3, 2]`) and the entries
array stays exactly the insertion sequence every cursor in the file reads.

### The boundary is falsifiable

The rewrite is SYNTACTIC — it lowers `del o[k]` for any receiver — so the type
check lands in the arm, as it does for the view builtins.
`dict_lab::del_nondict_still_loud` is the witness: CPython DELETES there (list
item deletion, answers 1), and the tier refuses rather than invent an answer
for a receiver whose behaviour it has not measured. `del xs[1:]` is excluded
at extraction: a slice deletes a RANGE, a different operation.

### An inherited wart, named rather than replicated silently

A synthetic name reaching the TRUNK's name resolution is in neither
`isBuiltinName` nor `isPyBuiltinName`, so at module scope with complete
globals the trunk would decide a `NameError` CPython never has. This is
**inherited from §pycomplete-11**, not introduced here — `<dictkeys>` has had
it since 3c-i-b — and it is unobserved because the trunk is not the runner and
no proof exercises it. Recorded so the next audit finds it from either end;
the fix is one arm in the trunk's resolution, and it belongs to whichever inch
next has reason to open that file.

### Census deltas

* grammar census **117 → 122 witnesses**: `del.dict-key`,
  `del.dict-missing`, `del.dict-reinsert-order` (MATCH), `del.dict-churn` and
  `del.non-dict-receiver` (REFUSE).
* `harness/cases.json` **660 → 670 rows**. `del_lab::del_sub` FLIPS
  `unsupported → match` and LEAVES `WHITELIST_CLASS`; four new gaps join it —
  one `del.non-dict-receiver` and three `dict.keyset-churn`.
* `docs/memory-model.md` updated in three places: the H1 dict inventory, the
  `del` construct paragraph, and the cross-rung churn note that predicted
  this inch.

## 2026-08-24-pycomplete-17 — INCH (2)'s CENSUS: `iter(d)` arrives at the EVALUATOR, and it is the THIRD generator allocator

Inch (2) of the flagship ladder is `iter(d)` + `next` over dict keys — the key
half of `del self.tp_score[next(iter(self.tp_score))]` (sunfish.py:541), whose
`del` half landed as §pycomplete-16. Censused on CPython 3.9.19 and against the
tree before any design.

### THE FIRST FINDING, and it inverts inch (1)'s shape

Inch (1)'s answer was an INGESTION REWRITE: `del d[k]` could not arrive any
other way, because `delStmt` admits bare names and the refusal was upstream of
the AST. **Inch (2) is the opposite, and the extracted envelope says so
outright.** `iter(d)` comes out of the extractor as an ordinary
`Call(Name "iter", [Name "d"])` — no `call_unsupported`, no new node kind —
and `Json.lean` ingests it unchanged. The construct arrives at the
**EVALUATOR**, and the whole inch is one builtin arm plus one frame.

The reason is worth keeping, because it is the rule and not the accident:
**an ingestion rewrite is available exactly when the construct's meaning is
decided by SYNTAX.** `del o[k]` names its receiver syntactically and `del` has
no value, so `<dictdel>(o, k)` is exact. `iter` is a SHADOWABLE name whose
meaning depends on its argument's runtime TYPE — `list_iterator`,
`str_iterator`, `dict_keyiterator`, or the generator itself — and ingestion
sees neither the binding nor the type. A rewrite there would be a guess.
*The third decision site is a tool, not a default.*

### THE SECOND FINDING, and it is the one that would have gone wrong

`Expr.genAllocFree`'s docstring reads *"Only two shapes can allocate an
`Obj.generator` … a call of `enumerate` or `count`"*. **`iter` is the third**,
and nothing in the §pycomplete-15 price sheet predicted it. The consequence is
not a missing feature but a WRONG LOUD ANSWER: `moduleGenFree` would classify a
module holding an `iter` cursor as generator-FREE, and

    d = {2: 'b', 1: 'a'}
    for k in iter(d):
        print(k)

would report ordinary Python as *"internal: a generator object in a module
with no generator defs (heap well-formedness violation — report this)"* — the
2026-08-13 `tools/leanpy` incident, verbatim, at a new builtin. The witness
`dict.iter-for` exists to convict exactly that, and it is a MATCH only because
the census read the docstring that names the closed list.

`Expr.heapFree` needed the same carve-out for a DIFFERENT reason, and the two
must not be conflated. The trunk refuses `iter` entirely, so world-preservation
is safe there; but `funsHeapFree` is also the guard `callNamePlan` reads to
conclude that *a local holding a `.ref` in a heap-free module must be a DICT*
(closures allocate, so there can be none). An `it = iter(d)` that left the
fragment intact would falsify that, and `it(0)` would name the wrong type in an
otherwise faithful `TypeError`. **Two allocator censuses, two arguments, one
line each.**

### The oracle's column, in the source spelling

| probe | CPython 3.9.19 |
| --- | --- |
| `next(iter({2:'b',1:'a'}))` | `2` — insertion order |
| `it = iter(d); next(it), next(it)` | `2 1` — ONE cursor |
| `next(iter({}))` / `next(iter({}), -1)` | `StopIteration` / `-1` |
| `type(iter(d)).__name__` | `dict_keyiterator` |
| `it = iter(d); d[2]='b'; print('bound')` | `bound` — **silent** |
| `it = iter(d); d[2]='b'; next(it)` | `RuntimeError: dictionary changed size…` |
| `it = iter(d); del d[1]; next(it)` | the same `RuntimeError` — shrink is size too |
| `it=iter(d); jt=it; next(it), next(jt)` | `1 2` — identity, one shared cursor |
| `for k in iter(d)` / `list(iter(d))` | `2 1` / `[2, 1]` |
| `del d[next(iter(d))]` | `{2: 'b'}` — **the flagship line** |
| `iter([7,8])`, `iter('xy')`, `iter((5,6))`, `iter(range(3,9))`, `iter({4})` | all answer, each a DIFFERENT iterator type |
| `iter(g) is g` | `True` — a generator is its own iterator |
| `iter(3)` | `TypeError: 'int' object is not iterable` |
| `iter()` | `TypeError: iter expected at least 1 argument, got 0` |
| `iter(d, 0)` | `TypeError: iter(v, w): v must be callable` |
| `iter(lambda: 1, 1)` | a `callable_iterator` — a second OBJECT KIND |

### THE THIRD FINDING: the churn regime is TWO CPython rules, and now both are named

§pycomplete-15 measured the same-size key-set churn regime through a `for`
loop and concluded *"the entries-array layout is what separates them"*. Driving
the SAME regime through an explicit `iter`/`next` cursor splits that sentence
into two facts, because the cursor can be positioned anywhere:

| shape (`d = {1,2,3}`, one `del`, one insert, size unchanged) | CPython 3.9.19 |
| --- | --- |
| churn after yielding key **1** | `1, 3, 9` — **silent** |
| churn after yielding key **2** | `1, 2, 3` then `RuntimeError: dictionary keys changed…` |
| churn **before** any `next` | `2, 3, 9` — **silent** |
| churn, then the iterator RUNS OFF the end | `RuntimeError: dictionary keys changed…` |
| 8-key dict, churn at key 3 | `0,1,2,4` — silent |

`dictiter_iternextkey` raises *"changed size"* on `di_used != ma_used` — a SIZE
check the model has — and raises *"keys changed"* at the point CPython's own
source comments *"We found an element (key), but did not expect it"*: `di_len`
has reached **zero** while a live entry still lies ahead of the cursor. So the
`for` table's four shapes were four samples of one two-part rule, and the
`iter` spelling is what made the parts separable.

**The refusal is therefore not a coarse approximation of one rule; it is the
honest answer to two.** A model carrying `di_len` alone would answer where
CPython is silent; one carrying the tombstoned array alone would be silent
where CPython raises. Both, together, or LOUD — and LOUD is what stays.
*A regime you have only ever probed from one cursor position is a regime you
have measured once.*

### A fourth measurement, recorded because it constrains the frame

Exhaustion is **discovered, not implied**:

    d = {1:'a'};  it = iter(d);  next(it)   # yields 'the last key'
    d[2] = 'b';   next(it, -1)              # RuntimeError — the iterator is STILL LIVE

    d = {1:'a'};  it = iter(d);  next(it);  next(it, -1)   # RUNS OFF: -1
    d[2] = 'b';   next(it, -2)                             # -2 — silent, it is DEAD

CPython clears `di_dict` at the step that finds the end, and only then stops
guarding. A frame popped at the LAST YIELD would answer `-1` where CPython
raises; one never popped would raise where CPython answers `-2`. The
`enumDict` precedent already pops on `.done`, so both fall out — but they fall
out of WHERE the pop happens, which is why the pair is a witness and not a
comment.

### THE PRICE — nine frame sites, and the two that were not on the sheet

| site | file | what |
| --- | --- | --- |
| constructor | `Runtime.lean` §generator continuations | `iterDict (a cur n sv)` beside `enumDict` |
| well-formedness | `Runtime.lean` `GenFrame.WF` | `a < h.size` |
| classifiers ×2 | `Semantics.lean` `genBreak`/`genContinue` | one pattern each |
| worker | `Semantics.lean` `iterFrame` | new, beside `enumFrame` |
| step (rebuild) | `Monadic/Eval.lean` `execGen` | `dictStepM … .keys`, yielding the BARE key |
| step (trunk) | `Semantics.lean` `execGen` | one arm, REFUSING |
| `PayloadBlind`/`ClockErase`/`Obs` | one arm each | mechanical, and all three are the `enumDict` arm verbatim |
| builtin arm | `Monadic/Eval.lean` `applyBuiltin` | `iter` |
| builtin table | `Ast.lean` `isBuiltinName` | `+ "iter"`, 22 → **23 names** |
| **allocator census 1** | `Semantics.lean` `Expr.genAllocFree` | **not on the sheet** — see above |
| **allocator census 2** | `Semantics.lean` `Expr.heapFree` (+ the one `Obs.lean` destructuring) | **not on the sheet** — see above |
| lowering table | `Json.lean` `lowerBuiltins` | `+ "iter"`, the two-table gap closed at the third table too |

**`VCGen` owes nothing** and `Mono.lean` owes nothing, for §pycomplete-13's
reason unchanged: the frame is consumed through `stepIter`/`execGen`/`forGen`,
all of which are existing `Kont` fields, and the trunk refuses to step it, so
there is no transition theorem to state. `Monadic/Spec.lean` owes nothing
either — `dictStepM_spec` is stated for an arbitrary `kind` and arbitrary
`(a i n sv)`, so the new frame inherits it the moment it is written in terms of
`dictStepM`.

### The ruling §pycomplete-13 had to make, and why this inch has nothing to rule

3c-i-c had to choose between three ways of handling a TRUNK that builds a frame
it will not step, because `enumFrame` is SHARED. Here the trunk has **no `iter`
arm at all** — `iter` falls through its positional chain to `isPyBuiltinName`
and refuses as an unmodelled builtin, exactly as it did before this inch. So
`iterFrame` has one caller, the trunk never constructs the frame, and its step
arm is `forDict`'s: *"exists to compile and to refuse, and gains no consumers"*.
No capability delta, no witness to carry one, no `Obs.lean` branch to rewrite
away. **The cheaper arrangement was available because the trunk was silent, and
the census is what noticed the difference rather than transliterating (c).**

### What inch (2) does NOT cover, named so it is not silently assumed

* `iter` over a **list / str / tuple / range / set** — CPython answers, with a
  distinct iterator TYPE and a distinct mutation regime for each.
  `dict.iter-of-list` is the falsifiable witness; each is its own inch.
* `iter(g)` over a generator — CPython answers `g` ITSELF (`iter(g) is g`).
  Cheap, exact, and still out: it is a different RETURN (a `.ref`, not a
  frame), so it would be a second shape in one arm.
* `iter(d.keys())` — `consumesViewArg` excludes `iter` for `enumerate`'s
  reason: the cursor OUTLIVES the call, so the rewrite's snapshot is not
  licensed. Composing the view kind with this cursor is its own inch.
* `iter(v, sentinel)` — a `callable_iterator`, a second object kind.
* An ERROR-STATE gap, inherited and named below.

### AN INHERITED WART, MEASURED: CPython's iterator error state is STICKY

    d = {1:'a'};  it = iter(d);  d[2] = 'b'
    try:    next(it)
    except RuntimeError: pass
    next(it, 'DEFAULT')      # CPython: RuntimeError AGAIN. The model: 'DEFAULT'.

`dictiter_iternextkey` sets `di_used = -1` and CPython's own comment calls it
*"sticky"*; the model's `stepIterAt` CLOSES the generator when an exception
propagates out, and a closed generator answers `next`'s default. **"Dead" and
"poisoned" are different states, and the model has only one of them.** This is
**inherited from §pycomplete-14** — `enumDict` has had it since 3c-i-c and it
was not measured then — not introduced here; the fix is a `GenStatus`
constructor, which is a `Kont`-adjacent price and belongs to whichever inch has
reason to open that file. Recorded rather than replicated silently, and
deliberately NOT given a witness row: the census records measured verdicts, and
a row here would be a `DIVERGE`.
Interestingly the OTHER message is not sticky — after *"keys changed"* CPython
clears `di_dict` and the iterator merely dies — so the two RuntimeErrors differ
in aftermath as well as in cause.

### Battery — sixteen typed-call rows and ten witnesses, expectations ORACLE-written

Every source is the SPELLING a program would contain and every expectation is
CPython 3.9.19's own. Three rows are REFUSES and each names what CPython
answers: `iter_churn_still_loud` (CPython answers 4, silently),
`iter_list_recv_still_loud` (CPython answers 7), `iter_sentinel_still_loud`
(CPython raises `TypeError`). The falsifiable PAIRS are
`iter_bind_then_grow`/`iter_grow_then_step` (the guard is on the step) and
`iter_last_key_then_grow`/`iter_ran_off_then_grow` (exhaustion is discovered).

## 2026-08-24-pycomplete-18 — INCH (2) BUILT: `iter(d)` + `next` runs, and the price held except where the census caught it

`next(iter(d))` runs, and with it `for k in iter(d)`, `list(iter(d))`, the
aliased cursor, and **the flagship's whole line** — `del d[next(iter(d))]`
answers `{2: 'b'}`, which is inch (1) and inch (2) meeting on sunfish.py:541.

### What landed, against the censused site list

Nine frame sites, the builtin arm, the builtin table — all as priced. The two
sites the price sheet did NOT have are the two allocator censuses
(`Expr.genAllocFree`, `Expr.heapFree`), and they are the whole reason this inch
was censused against the tree rather than transliterated from `enumDict`.
**The `enumerate` precedent transfers at the FRAME and not at the MODULE.** A
new frame is nine mechanical arms; a new ALLOCATOR is two closed lists that
name their members, and a docstring is the only thing that says so.

### Three consumers that owed nothing, and that is the interesting half

`next`, `for`, and the draining consumers all reach the frame through
`stepIter`, and none needed a line:

* `next(it)` and `next(it, d)` — `next` already implemented both forms, so the
  sentinel came free with the frame, which is what §pycomplete-15 predicted.
* `for k in iter(d)` — the `.ref`-to-generator arm of the `for` dispatch, which
  routes to `forGen`. Free at function scope; at MODULE scope it is free only
  because `genAllocFree` was fixed, which is what makes `dict.iter-for` the
  witness for that site rather than for the cursor.
* `list(iter(d))` — `iterValues`' generator arm, draining unguarded because
  `list` allocates.

*The generator-frame design keeps paying: one stepper, and every consumer that
already reached `enumerate` reaches this too.*

### The churn guard, kept and now UNDERSTOOD

`iter_churn_still_loud` is the same `.rekeyed` refusal §pycomplete-16 made
required, reached through a different spelling — and the census (above) is what
turned "the entries-array layout" into two named CPython rules. The guard did
not move; the ARGUMENT for it got stronger, and a stronger argument for an
existing refusal is the cheapest kind of progress this lane makes.

### Census deltas

* grammar census **122 → 132 witnesses**: `dict.iter-next`, `dict.iter-steps`,
  `dict.iter-empty`, `dict.iter-escapes`, `dict.iter-resize`,
  `dict.iter-exhausted`, `dict.iter-for` and `del.dict-next-iter` (MATCH);
  `dict.iter-churn` and `dict.iter-of-list` (REFUSE).
* `harness/cases.json` **670 → 686 rows**, sixteen `dict_lab::iter_*`; three
  are new gaps and join `WHITELIST_CLASS` — one `dict.keyset-churn` and two
  new classes, `iter.non-dict-receiver` and `iter.sentinel-form`.
* `isBuiltinName` **22 → 23 names**; `Monadic/Eval.lean`'s count comment moved
  with it, because a comment that states a number is a claim.
* `docs/memory-model.md` updated in three places: the H1 dict inventory, the
  cross-rung churn note (now carrying the `di_len` mechanism), and a new
  §`iter(d)` cursor paragraph.

### §9.0 after this inch

**2 of 3 flagship-serving pyc surfaces.** `del d[k]` (§pycomplete-16) and
`iter(d)` + `next` (here); the third is `next(<genexp over keys with a
filter>)`, the other eviction line's key expression, and §pycomplete-15's
census of it stands unchanged — *"the genexp already has a cursor class"*.

## 2026-08-24-pycomplete-19 — INCH (3): the flagship's LAST refused line was already retired, and the inch is the MEASUREMENT that proves it

`bound()`'s two `TABLE_SIZE` eviction lines were the R-track's whole refused
census. §pycomplete-16 landed the `del`, §pycomplete-18 landed
`next(iter(...))`, and this inch went to build the third surface —
`next(<genexp over dict keys with a filter>)`, the `tp_move` line's key. **The
census before building found the price is ZERO model sites.**

### THE RE-CENSUS, and it is §pycomplete-16's law firing in the other direction

§pycomplete-16 re-censused an expensive design and found it four times cheaper.
Here the re-census found the design already BUILT, and every piece of it was
landed for another reason:

| the line needs | where it came from |
| --- | --- |
| `del d[k]` | §pycomplete-16 (inch 1) |
| `next(...)`, both arities | pre-existing (H4) |
| a genexp with a FILTER lowered to a generator function | pre-existing — `gen_lab::first_over` witnesses `next((x for x in upto(n) if x > k), -1)` today |
| `for k in <dict>` **inside a generator body** | §3a's cursor — `execGen`'s `.ref`-to-dict arm builds a `forDict` frame |
| the three mutation regimes | §3a, unchanged |

**Measured, not assumed.** The genexp at `sunfish.py:511` captures exactly one
name — `self` — and `self` is a parameter of `bound` that the body never
assigns, so the lowering's STRICT admission
(`ctx.params.contains n && !ctx.assigned.contains n`) passes with no `drainOk`
and no change to `drainingBuiltins`. The other three genexps in `bound` were
computed the same way; the one at line 444 fails admission and is a different
construct's problem.

> **`bound`'s unsupported census is ZERO.** It was two at §L14 and three at
> §L13. The flagship chain's rung 9 closes, and it closes on a measurement.

### WHAT WAS ACTUALLY MISSING WAS EVIDENCE, NOT CAPABILITY

Every genexp witness in the tree iterates a `range`, a generator, or a tuple.
**Not one iterates a DICT.** The composition — a genexp whose `for` walks a live
dict cursor, under a filter, stepped once by `next` — had never been run. So
this inch is seven typed-call rows and five witnesses, and the honest headline
is that it BUYS NO CAPABILITY: it converts a believed capability into a
measured one. *A surface nobody has run is a surface nobody knows the tier has.*

### THE PAIR THAT PREVENTS THE WRONG CONCLUSION

The naive witness for this surface REFUSES:

    root = 1                      # a body-assigned LOCAL
    return next(k for k in d if k != root)      # REFUSED

and a lane that wrote only that row would have concluded the dict-genexp
surface is out of tier. It is not. `genexp_next_key(a, root)` is the SAME
construct with `root` a PARAMETER and it MATCHES. **What refuses is the capture
admission, and it has nothing to do with dicts**: a by-value snapshot of a
body-assigned local could go stale, so the lowering refuses it unless the
genexp is immediately drained. The two rows are filed together for exactly that
reason.

**And the refusal is CONSERVATIVE rather than principled**, which is worth
saying because it names a separable inch. `next` is not in `drainingBuiltins`,
but a genexp in directly-passed argument position to `next` has a lifetime
strictly SHORTER than a drained one — one step, with no user code between
creation and step — so the snapshot cannot go stale. Admitting it is one line
and its own census; this inch does not take it, because the flagship does not
need it and a shared admission gate has a blast radius across every genexp.

### THE CLAIM WAS FALSE, AND THE CLAIM IS EXACTLY WHY I DID NOT LOOK

This entry first said the tier *"cannot witness"* a dict genexp's liveness,
because binding a genexp to a name supposedly refuses. **The gate convicted
both halves**, and the correction is the inch's real product.

**Binding does not refuse.** The lowering's strict admission passes on a
PARAMETER capture regardless of `drainOk`, so `g = (k for k in d if k != root)`
lowers and `next(g)` answers 2 — agreeing with CPython.
`gen_lab::gen_assigned_lazy` refuses because it captures a body-assigned `lim`,
**not** because it binds. *That is this entry's own §5.2 finding — a refusal
names a SITE, not its cause — broken in the same commit that stated it.*

**And the liveness IS witnessable — which is how the tier's first fully
probeable DIVERGENCE was found.** `g = (k for k in d)` / `d[3] = 'c'` /
`next(g)` raises in CPython and answers `1` here: PEP 289 calls `iter()` on the
outermost iterable when the genexp OBJECT is created, while this tier does not
push the cursor frame until the first resume, so the guard compares the dict
against itself. Filed as **`pyc-div-2`**, and unlike `pyc-div-1` its probe RUNS
both sides every time.

> **A false blanket claim hides the real gap, and the claim is why nobody
> looked.** The gap here was not smaller than the claim — it was a DIVERGE, and
> the sentence asserting unwitnessability is the reason it sat one edit away
> from being shipped as a REFUSE row.

### THE CONSTRUCTION-SITE CENSUS, and it corrected the question that ordered it

§5.2's ruling (`bf3f33f`) made "the trunk never constructs this frame" a
MEASURABLE claim rather than a docstring. Run over the three frames this lane
had called unreachable:

| frame | construction sites | trunk-reachable? |
| --- | --- | --- |
| `.forDict` | `Monadic/Eval.lean` ×3, `Monadic/Script.lean` ×3 — **zero trunk sites** | no |
| `.enumDict` | `Semantics.lean` `enumFrame` — **which the trunk's `enumerate` arm calls** | **YES** |
| `.iterDict` | `Semantics.lean` `iterFrame` — sole caller is the rebuild's `applyBuiltin` | no |

**`enumDict`'s trunk step arm is a LIVE path**, not an unreachable one: §3c-i-c
ruling (c) had the trunk BUILD the frame and refuse at the step, so a trunk
`e = enumerate(d); next(e)` reaches it. The lane asked for a ruling about
"three unreachable refusals" and **only two of them were unreachable** — the
census caught it on its first run, which is what it was ordered for.

Type-level discharge (`nomatch`, or narrowing the frame type) is **not
available at a price anyone would pay**: the frames live inside `Obj.generator`
on a SHARED heap, so narrowing means indexing the heap by presentation, which
ripples through `Obj`, `Heap.WF`, `PayloadBlind`, `ClockErase` and `Obs`. So
refusal-form stands for the two, with the claim gated by this census.

### THE DECLARED-DIVERGENCE REGISTER, FOUNDED

§5.0a's canonical shape is DATA per-tier, CHECKER shared, PROBE per-tier. This
tier builds the **checker** — `harness/divergence_register.py` — and files the
**data** (`docs/python-declared-divergences.json`) and its **probe**
(`harness/pyc_divergence_probe.py`) alongside it.

* **It validates SV's file UNMODIFIED**, today: 2 tier files, 3 rows, 6 guards,
  all held. Cross-tier validation is the acceptance test and it did not have to
  wait for a second filer.
* **It asks only tier-independent questions** — fields present, kind in the
  ruled two, guards exactly two and distinct, `declared` dateable, retirement
  condition not WAITING-shaped, probe exists, probe ran, every guard held.
  Nothing semantic is decided there; MEAS-28.
* **The guard set is checked BOTH ways.** A row naming a guard the probe lacks
  is UNGATED; a probe guard no row names is ORPHANED — the shape a deleted row
  leaves behind, and the one hole a build cannot see.
* **`--self-test` exercises the checker's own defect detection** against ten
  mutated copies of a real file. A checker that only ever passes is a claim,
  and the rules that matter are the ones that have never fired on real data.
* **The empty-register check is kept although it is now unreachable** (sv and
  python have both filed). It is a fact about today, not about the design, and
  removing it would buy a silent green.

### `pyc-div-1`, and the honest thing about its guards

The row is the sticky dict-iterator error state: CPython poisons
(`di_used = -1`, its own comment says sticky) and re-raises on every later
`next`; the model CLOSES the generator, so `next(it, x)` answers `x`.
`KIND: semantic`, `INHERITED FROM: enumDict / §pycomplete-14` — not blank,
because blank is the heavier ORIGINATED claim and it would be false.

**THE DIVERGENCE IS NOT REACHABLE BY AN IN-TIER PROGRAM**, and the probe says so
instead of implying a run it cannot make. Observing it needs the first
`RuntimeError` survived, which needs `except RuntimeError:` — and
`exc_lab::except_builtin` is a whitelisted refusal. So the ORACLE half is a
genuine run every time, and the MODEL half is pinned where the divergence
actually lives: the ABSENCE of a poisoned `GenStatus` constructor. That is not a
weaker guard than a program would be — **it fires on exactly the event that must
retire the row**, which is a poisoned state landing.

The widening metric is the count of synthetic iterators whose frame carries a
dict guard: `<enumerate>` and `<iter>`, two. `<count>` is allocated the same way
and deliberately NOT counted — its frame carries no dict guard, so it can never
raise the sticky error, and a metric that counted it would fire on an unrelated
feature.

### THE STALE PROSE, REPAIRED — and why nothing caught it

`sbEvict_lit`'s docstring said `del d[k]` *"ingests as `Stmt.unsupported`"* and
that `bound`'s unsupported census is two. Both were false the moment inch (1)
landed. **Nothing broke, because `sbEvict_lit` quantifies the body
existentially (`∃ b : Array Stmt`) and `evict_dead` earns its result by showing
the guard is `.bool false` and never opening the body.** The proof was immune to
the change; the prose was not, and prose cannot fail.

`BoundWF.room`'s rationale is rewritten to the falsifiable form: dropping it no
longer produces a refusal, it produces a WRONG WORLD — `evict_dead` proves
`.ok ⟨w, e⟩ .next` with the SAME `w`, and with the guard TRUE the body now
removes a key and bumps `shapeVersion`, answering `.ok ⟨w', e⟩ .next`. **The
hypothesis is unchanged and still needed; what changed is that its violation is
now SILENT**, and observability is not a property any instrument here measures.
It is reclassified TIER → MODELLING (§5.0a's taxonomy): the honest retirement is
to model the eviction, not to widen the tier.

### Census deltas

* grammar census **132 → 136 witnesses**: `dict.genexp-next`,
  `dict.genexp-nomatch`, `dict.genexp-default`, `dict.genexp-drain`, all MATCH.
  `dict.genexp-bound-is-loud` was written as a fifth and measured **DIVERGE**;
  it does not belong in this census's vocabulary and moved to the register,
  whose probe runs it both ways — strictly more gating than a census row.
* `harness/cases.json` **686 → 693 rows**; **one** new gap joins
  `WHITELIST_CLASS` (`genexp.lowering-admission` — the CAPTURE rule, not the
  dict cursor). A second was predicted and the gate refused it:
  `genexp_bound_still_loud` MATCHES.
* **declared-divergences: 0 → 2** — the third standing quantity, beside the
  coverage number and never folded into it. `pyc-div-2` is the register's first
  row whose probe runs BOTH sides.
* Three prose sites repaired in `Examples/python/sunfish/`; zero theorems moved.

### §9.0 after this inch

**3 of 3 flagship-serving pyc surfaces. `declared-divergences: 2`.**
Rung 9's dependency on this lane is discharged: `bound()` has no refused
construct left — **and the discharge is SCOPED, measured rather than assumed.**
Of `bound()`'s four generator expressions exactly one iterates a dict
(`sunfish.py:511`), and it creates and steps its cursor inside a single
expression, so real play never enters `pyc-div-2`'s create-to-first-resume
window. The `tp_score` line uses `iter()`, which snapshots at creation and is
unaffected. Had real play entered the window, this discharge would not stand.

## 2026-08-24-pycomplete-20 — the cursor moves to CONSTRUCTION, pyc-div-2 retires by its own condition, and the census that gates the claim corrected itself twice

§pycomplete-19 declared `pyc-div-2`: a genexp's dict cursor was built at FIRST
RESUME where PEP 289 builds it when the genexp OBJECT is made, so
`g = (k for k in d)` / mutate `d` / `next(g)` answered where CPython raised.
The fix lands, the row retires, and the retirement was ANNOUNCED BY ITS OWN
GUARD rather than by anyone deciding it was time.

### THE PROBE THAT NARROWED THE FIX, and its negative half is the load-bearing one

| shape | CPython 3.9.19 |
| --- | --- |
| **genexp**, mutate after create, before first `next` | `RuntimeError` |
| **generator FUNCTION**, same mutation | **`1`** — no error |
| generator function, then drained | **`[3]`** — it walks the GROWN dict |
| `(x for x in boom())` | raises **at creation** — outermost iterable is eager |
| `(x for x in d for y in boom())` | constructs — **inner clauses stay lazy** |

**So "make generator cursors eager" would have been the wrong fix.** Calling a
generator FUNCTION runs no code, so CPython has called no `iter()`; the tier's
deferred behaviour there is CORRECT and a blanket fix would have broken it.
Eagerness is a **genexp** rule, for the **outermost** clause only. And of the
receivers only a dict carries a snapshot — `forList` re-reads live, value
sequences are immutable, `forGen` holds no counts — so no other receiver can
show the difference.

That narrowing is why the fix is one worker and one call site:
`genInitCont` (`Semantics.lean`, beside `iterFrame`) seeds a synthesized
`<genexpr@n>`'s continuation with its cursor already pushed; `callInM` uses it;
everything else — including every user `def` with a `yield` — still gets
`[.block body]`. `genExpPrefix`/`genExpArgName` move to `Ast.lean` beside
`dictDelBuiltinName`, because ingestion mints those names and the evaluator now
has to recognise them, and a name spelled twice is a name that will drift.

`dict_lab::genfun_mutate_after_create` and `genfun_drain_after_create` are the
NEIGHBOUR rows, filed beside the fix precisely so a later blanket change flips
them. This is the `gen_closes` pattern's third use: *the row that proves the
fix did not fix the wrong thing.*

### THE RETIREMENT WAS ANNOUNCED BY THE GUARD, which is the half nobody designs for

`pyc_div_2_still_divergent` began FAILING the moment the fix compiled. §5.0a's
paired-guard law is usually read in one direction — *has the divergence
widened?* — and this is the other one paying out: **the divergence is gone, and
the declaration is now a false claim about the tier that reads as diligence.**
The row left the register on that evidence, not on anyone's say-so, which is
exactly what its retirement condition demanded (*"the row retires by the
behaviour changing and cannot be closed by assertion"*).

> **A register that only ever grows is a list. This one shrank, on a failing
> guard.**

The witness moved with it: `dict.genexp-bound-is-loud` measured DIVERGE at
§pycomplete-19, moved OUT of the census into the register, and **comes back as
a MATCH**. A row that leaves for the register and returns to the census is the
whole mechanism working, and the witness is the receipt.

### THE CONSTRUCTION-SITE CENSUS, gated — and it corrected itself twice

§5.2's ruling made *"the trunk never constructs this frame"* measurable rather
than a docstring. `harness/frame_construction_census.py` pins it:

| frame | route | trunk callers |
| --- | --- | --- |
| `iterDict` | `iterFrame` | **0** — MEASURED unreachable |
| `enumDict` | `enumFrame` | **1** (`Semantics.lean`) — POSITIVE, the correction |
| `forDict` | `genInitCont` / `K.forDict` / `S.forDict` | **0** |

**Its first draft reported two FALSE drifts, and both said the same thing.** It
counted `ClockErase`/`PayloadBlind` as trunk callers of `enumFrame` when those
files only REASON about the trunk; and it flagged a `forDict` construction in
`Semantics.lean` that is **this inch's own `genInitCont`** — a worker living in
a trunk file with only rebuild callers. So the measure had to become
**caller-based, not file-based**, which is the very distinction the enumDict
correction turned on. *A census whose first run convicts the lane's newest line
is a census pointed at the right thing.* The `enumDict` row is pinned as a
POSITIVE expectation so the correction cannot be lost the way the belief was.

### THE SHARED CHECKER GREW A SECOND PROBE SHAPE, and a migration clause

ES's row merged, so the acceptance test finally binds — and it FAILED: ES files
`declared-divergences-0.1`, no `probe` key, guards as
`"<path>: <name>"` Lean theorems, and a blank `inherited_from`. None of that is
wrong; it is a second legitimate shape in which **the build is the run**, and a
Lean theorem that stops holding fails the tenure — a stronger gate than a
script, not a weaker one.

* `probe` is now OPTIONAL; absent, guards name declarations and the checker
  verifies they exist. Both shapes satisfy §5.0a's *"named in the row"*.
* `declared-divergences-0.1` and blank `inherited_from` are accepted with
  MIGRATION WARNINGS that do not change exit status — §9.5a's old-valid clause
  applied to schemas: *a shape a lane shipped in good faith cannot become a
  failure the day the canon lands.* The schema earned its migration clause on
  day two.
* **The schema is written down ONCE**, as a docstring block in the shared
  checker, so the next tier reads it instead of inferring it from a neighbour's
  file — which is how the divergence arose.
* The checker now validates all three tiers' files UNMODIFIED: **4 rows, 8
  guards, 2 migration warnings, exit 0.**

**And a self-referential trap, caught by the self-test's own expectation.** The
new declaration-shape case first pointed its fake guard names at
`divergence_register.py` itself — and the substring existence check duly FOUND
them, passing a file it should have rejected. *A grep-based existence check is
self-referential when aimed at its own source.* Self-test: 10 → **13** defect
classes.

### Census deltas

* grammar census **136 → 138 witnesses**: `dict.genexp-bound-is-loud` returns
  as MATCH, and `dict.genfun-mutate-after-create` joins it as the negative half.
* `harness/cases.json` **693 → 697 rows**, four new `match` rows; no new gaps.
* **declared-divergences: 2 → 1** for this tier (4 across all three).
* new gate `harness/frame_construction_census.py`; `harness/divergence_register.py`
  extended for both probe shapes.

### §9.0 after this inch

**3 of 3 flagship-serving pyc surfaces · `declared-divergences: 1`.**
The scope qualifier on rung 9's discharge WEAKENS as predicted: with the cursor
built at construction, `pyc-div-2`'s create-to-first-resume window no longer
exists, so the claim that real play never enters it is moot rather than
load-bearing. What remains is `pyc-div-1`, whose retirement is blocked upstream
on `exc_lab::except_builtin`.

## 2026-08-24-pycomplete-21 — a substring is not a declaration: the register's declaration shape gets an anchor, and the fixture needs no fixture

ES retired its lane-local checker into the shared one and flagged what the
shared one was missing on the way out. The declaration-shape branch asked
`gname not in text` — **a plain substring test** — so a guard whose `def` had
been DELETED but whose name survived in a comment still passed.

**This is the third time this instrument has been bitten by the same shape.**
The self-test's own first draft aimed its fake guard names at
`divergence_register.py` and the checker FOUND them (§pycomplete-20); QoL hit
the self-matching row; and now a name in prose reads as a declaration. *A
grep-based existence check answers "is this string here", and the question was
"is this thing declared".*

### What the tightening requires, and why BOTH halves

ES's retired checker required `def <name>` **and** a matching `#guard <name>`,
and that pair is now the shared instrument's:

* `def <name>` at a line start — the declaration exists, rather than the name
  appearing in prose;
* `#guard <name>` at a line start — and the build actually EVALUATES it.

A `def` nobody `#guard`s is **a guard in name only**: the build compiles it and
nothing ever checks it. A `#guard` with no `def` cannot elaborate. Comments are
stripped (`/- -/` and `--`) before matching, because anchoring alone is not
enough — `^\s*def foo` matches happily inside a block comment, which is exactly
the deleted-declaration case.

### THE FIXTURES NEEDED NO FIXTURE FILE, and that is the nice part

Both new self-test cases point at REAL repository files, so there is nothing to
create, stage or clean up:

| case | fixture | why it must refuse |
| --- | --- | --- |
| name only mentioned | `docs/es-declared-divergences.json: es_div_1_still_divergent` | the name is in ES's own register as DATA and is declared nowhere — **the old substring test returned `True` for exactly this** |
| `def` without `#guard` | `LeanModels/Python/Ast.lean: isBuiltinName` | a real `def`, genuinely never `#guard`ed |

The first is the sharpest fixture available anywhere in the tree: the string
that proves the bug is the guard's own name, sitting in the register file that
names it. Self-test **13 → 15** defect classes.

### The fleet after this

Two probe shapes, both live and both gated: SCRIPT (`python`, `sv`) and
DECLARATION (`es`, `def` + `#guard`). Schema stable at
`declared-divergences-1` fleet-wide, **zero migration warnings** — the
migration clause did its job and is now dormant rather than load-bearing, which
is the outcome §9.5a's old-valid law is for. Register: 3 files, 4 rows, 8
guards. `declared-divergences: 1` for this tier.

**Class note.** This landed `docs`-class — no Lean elaborates — but the changed
file is a GATE, and a gate that lands without being run is the §5.4b shape
again. So the instrument was added to `--gates` explicitly rather than relying
on the class floor, which runs only `docs_check`.

## 2026-08-24-pycomplete-22 — `except <builtin>:` lands as a SUBSUMPTION TABLE, and a docstring that argued a case away expires with it

`exc_lab::except_builtin` was the whitelisted refusal upstream-blocking
`pyc-div-1`'s witness: a program-level probe of the sticky dict-iterator needs
`except RuntimeError:`, and the tier's admitted handler shape named user
classes only.

### THE FLAGSHIP DOES NOT CARE, measured before anything else

`bound()` contains **zero** `try` statements. All of `sunfish.py` has exactly
one, and its handler is `Stop` — a user class already in tier. So rung 9 is
untouched either way, and this inch is paying down a DEBT rather than serving
the flagship.

### BLAST RADIUS — AND I SCOPED IT WRONG TWICE, at two different scales

The first census enumerated handlers in `exc_lab.py` and found two builtin
classes (`ZeroDivisionError`, `Exception`). **The gate found a third**:
`assert_lab::catch_assert` catches `AssertionError`, and I had never looked
outside the file the row I was fixing happened to live in.

Re-scoped to `Examples/python/*/*.py` and re-ticketed. **The gate found a
fourth**: the grammar witness `stmt.Try` catches `ValueError` — and the grammar
census's witnesses are not files at all, they are Python source embedded as
STRING LITERALS inside `harness/refusal_census.py`.

> **A blast-radius census must span every corpus that RUNS the language, and
> this repository has three in three different shapes** — typed-call witnesses
> in `Examples/python/*/*.py`, grammar witnesses as inline source inside
> `refusal_census.py`, and whole programs in `harness/scripts/*.py`. Scoping to
> the file where the defect lives finds one; scoping to the obvious corpus
> finds most; only enumerating all three finds them all.

Two red tenures for one error at two scales. The complete enumeration:

| corpus | site | handler | disposition |
| --- | --- | --- | --- |
| Examples | `exc_lab` | `ZeroDivisionError`, `Exception` | FLIP to match |
| Examples | `assert_lab` | `AssertionError` | FLIP — missed by census 1 |
| Examples | `import_lab` ×3 | `ImportError` | unaffected — `importErrorHandlerMatch` is checked first |
| Census | `stmt.Try` | `ValueError` | FLIP — missed by census 2 |
| Scripts | 3 files | `ImportError` | unaffected, same reason |

**And two of the flipping rows were vacuous.** `except_builtin` passed `n=1`,
which never divides by zero, and `stmt.Try`'s program never raises at all —
both would have flipped to `match` WITHOUT ENTERING A HANDLER. The flip adds
`n=0` to the first; the second keeps its verdict, but its note now says plainly
what it does and does not prove, because a grammar row is a lower bound on
coverage and never evidence about the catch.

### WHY IT IS A TABLE, AND WHY IT IS DATA

Three facts make a name-to-constructor equality wrong:

* **`RecursionError <- RuntimeError`** in CPython's MRO, so the WIDER handler
  name must catch the narrower error. This pair alone makes it a subsumption
  relation.
* **`except Exception:` is universal** — every builtin the tier raises, and
  every admitted user class too.
* **`ZeroDivisionError` is TWO constructors** — see below.

So the relation lives in `Ast.lean` as three explicit tables
(`admittedBuiltinExc`, `refusedAncestorExc`, `builtinExcCatches`) rather than
as logic inside the matcher — **because the matcher exists twice**, at function
scope and at module scope, and a rule spelled twice is a rule that drifts.
**Nothing is inferred**: every pair is one this tier can actually exhibit, and
an ancestor the tier could compute but has not measured is refused BY NAME.

### THE DOCSTRING THAT EXPIRED, and it is the third of its shape

`PyErr.zeroDivisionPow`'s own docstring justified splitting the constructor
partly on this:

> *"`except ZeroDivisionError:` needs no update: builtin exception names are
> not matchable at all … so the two cannot be told apart by any program in the
> tier."*

True when written — and a claim about a LIMITATION rather than about the split,
so the inch that lifted the limitation falsified it, and **no proof noticed
because no proof depended on it.** Had the table mapped only
`zeroDivisionError`, `0 ** -1` would silently escape a handler CPython
catches: *a wrong answer, not a missing feature.* Both constructors map, and
the docstring is repaired in the same commit as the code that invalidated it.

> **Third instance of one shape: a docstring that argues a case away on the
> strength of a limitation the next inch removes.** `sbEvict_lit`'s "ingests as
> `Stmt.unsupported`" (§pycomplete-20), this lane's own "cannot be witnessed"
> (§pycomplete-19), and now this. The common factor is not carelessness — each
> was true when written. It is that **an argument resting on what the tier
> CANNOT do has an expiry date that nothing in the tree tracks.**

### The frontier names itself

`ArithmeticError`, `LookupError`, `BaseException`, `OSError`,
`EnvironmentError` are refused BY NAME with a message saying why — admitting
them would claim a catch set the model has never enumerated.
`exc_lab::except_ancestor_still_loud` is the falsifiable witness (CPython
answers −1 through `ArithmeticError`); it joins `WHITELIST_CLASS` as
`exc.ancestor-class`, so the frontier is a row rather than a belief.

**And the subsumption witness had to move.** Its first draft used a nested
recursive `def` — which is `closure_lab::rec_nested_name`'s whitelisted
refusal, so it would have refused for a reason having nothing to do with
exceptions. Its second problem was worse: the tier reaches `.recursionError`
at exactly ONE site, `heapEq`'s active-pair check, so deep recursion exhausts
FUEL instead. The witness lives in `dict_lab` on the two-self-cyclic-dicts
shape, which is the only place the pair is reachable at all.

### Census deltas

* `harness/cases.json` **697 → 699 rows**; `except_builtin`,
  `except_exception` and `assert_lab::catch_assert` FLIP
  `unsupported → match` and leave `WHITELIST_CLASS`; one new gap joins it
  (`exc.ancestor-class`). Grammar census: `stmt.Try` flips `REFUSE → MATCH`.
* `docs/backlog/python-completeness.md`'s INBOUND heading re-spelled id-first.
  The index derives an entry's id from the heading's FIRST TOKEN, so the old
  spelling rendered the row as ``| `INBOUND` | INBOUND | … |`` — present but
  unaddressable. Six of six now conform.

### What this unblocks

`pyc-div-1`'s retirement condition named `exc_lab::except_builtin` leaving the
whitelist as its blocker. **It has left.** The debt's witness
(`dict_lab::iter_sticky_after_resize`) is now writable, so the row's probe can
gain its program-level form and the retirement becomes fully exercisable — the
next inch, not this one, because writing the witness is where that debt's
measurement belongs.

**§9.0: `3 of 3` flagship-serving pyc surfaces · `declared-divergences: 1`.**

## 2026-08-24-pycomplete-23 — pyc-div-1's probe gains its second side, and the instrument's own claim expires with it

`pyc-div-1` said CPython POISONS a dict iterator whose size guard fired
(`di_used = -1`, sticky) while this tier merely CLOSES the generator, so a later
`next(it, x)` answers `x`. Filed at §pycomplete-19 with **one side running**:
the oracle half executed, the model half was pinned at the absence of a
poisoned `GenStatus` constructor. Honest, and weaker than a run.

### THE BLOCKER WAS NAMED, AND IT WENT AWAY

The row's `blocked_on` said the witness needs `except RuntimeError:` to survive
the first raise, and that `exc_lab::except_builtin` was a whitelisted refusal.
§pycomplete-22 admitted builtin handler classes; the refusal left the
whitelist; the blocker resolved. **The row's retirement condition is now fully
exercisable**, which is the whole point of having written the blocker down
rather than leaving it as "when someone models it".

The field is kept as `was_blocked_on` rather than deleted, because a blocker
that silently disappears leaves the instrument describing a world that no
longer exists — which is exactly what happened next.

### THE PROBE'S OWN DOCSTRING EXPIRED — fifth of the shape, first inside an instrument

`pyc_divergence_probe.py` opened with:

> **THE DIVERGENCE IS NOT REACHABLE BY AN IN-TIER PROGRAM.**

True for a day and a half, and false the moment §pycomplete-22 landed. It is
the **fifth** claim in this lane to expire that way — after `sbEvict_lit`'s
"ingests as `Stmt.unsupported`", this lane's "cannot be witnessed",
`zeroDivisionPow`'s "builtin exception names are not matchable at all", and
`catch_assert`'s "the recorded gap" — and the first found **inside an
instrument** rather than a docstring, a witness or a proof.

> Every one was TRUE when written. The common factor is that each rested on
> what the tier **could not do**, and a premise of that shape has an expiry
> date that nothing in the tree tracks. An instrument carrying one is worse
> than a comment carrying one, because the instrument is what a reader trusts
> when the comments disagree.

### What the guards do now

* `pyc_div_1_still_divergent` RUNS the witness under CPython and under
  `tools/leanpy` and compares: the oracle must print `first-raised` and then
  DIE re-raising, the model must print `first-raised` and then answer
  `DEFAULT`. The `GenStatus` check stays alongside, because a poisoned state
  landing is the fact the retirement condition names.
* `pyc_div_1_has_not_widened` gains a real control: **a FRESH cursor over the
  same dict, made after the poisoning, must work on BOTH sides** (CPython
  answers 1). The row describes one poisoned OBJECT — not a poisoned dict, and
  not a poisoned interpreter. The source-level counts
  (`DICT_GUARDED_ITERATORS`, `STICKY_CAPABLE_RAISES`) stay pinned above,
  because "could a THIRD site inherit this row" is a question no program can
  ask.

The first control drafted for this was `raise ValueError` inside the `try` —
and **raising a builtin class is itself a whitelisted refusal**, so it would
have refused for a reason having nothing to do with iterators. Caught before
ticketing this time, by asking what the program needs rather than what it
looks like.

### Blast radius — three corpora, checked FIRST

Per §pycomplete-22's law, and applied before the ticket rather than after two
red tenures. The change touches `harness/pyc_divergence_probe.py` and
`docs/python-declared-divergences.json`; **zero references to either exist in
any of the three corpora** that run Python (`Examples/python/*/*.py`, the
inline grammar witnesses in `refusal_census.py`, `harness/scripts/*.py`). No
witness moves, and none may: this row is a DIVERGENCE, so a census row for it
would be a `DIVERGE` — it lives in the register precisely so the scoreboard
never sees it.

### And what a failing guard would mean here

If `pyc_div_1_still_divergent` fails on this landing, the honest readings are
two and both are useful: either the model no longer diverges — in which case
**the row must retire** and the guard has done its job in the direction §5.0a
cares most about — or the witness is wrong. The detail line prints both sides'
exit status and output, so the tenure distinguishes them without a rerun.

**§9.0: `3 of 3` flagship-serving pyc surfaces · `declared-divergences: 1`**
for this tier, now with both sides measured.

## 2026-08-25-pycomplete-24 — the pins pair is SHARDED, and one of the two barely benefits

`pins_bound` (18.9 min) and `pins_clock` (19.0 min) are together ~85% of every
full spine build's elaboration. A single module elaborates SERIALLY, so the
probes inside each — independent `#guard`s — cannot overlap. This is a TOPOLOGY
change and nothing else: **no probe dropped, no fuel changed, every expected
value byte-identical.**

### The census corrected the mental model before any edit

Both files are **~250 lines**. The cost is not size, not guard count, but what
each `#guard` KERNEL-EVALUATES — the interpreter running sunfish at depth. So
shards must be balanced by guard cost, and "split the big file" was never the
right description of the problem.

Three facts made the split safe, and all three were measured first:

* **`globs = ["Examples.+"]`** — a new file under `Examples/` is a default
  target automatically. No lakefile edit, and coverage is unchanged *by
  construction* rather than by inspection.
* **Both files are LEAVES.** Nothing imports either, so splitting them cannot
  disturb another module.
* **`pins_common` already exported** `board0`/`posH`/`sp0`/`searcherW`; only
  `boundProbe` (and, for the clock file, `searcherWT`/`boundProbeT`) needed
  lifting, each moved verbatim.

### `pins_bound` — five leaves, and the boundary names the board

| shard | board | guards |
| --- | --- | --- |
| `pins_bound_h` | opening `posH 0`, depths 1–3 | 8 |
| `pins_bound_mid` | midgame `posMid` | 6 |
| `pins_bound_tac` | tactical `posTac` + quiet-pawn `posPend` | 5 |
| `pins_bound_end` | rook endgame `posEnd` | 4 |
| `pins_bound_searcher` | the trace-clock frontier | 3 |

`pins_bound.lean` survives as the prose home and a facade importing the five —
the capstone's 23-pair narrative stays in one place, and the module name keeps
resolving.

### `pins_clock` — three leaves, AND THE SHARDING BUYS LITTLE, which is the finding

`transport` (the ∀-trace theorem, 0 guards), `probe` (5 guards), `walk`
(1 guard). **That one guard is the module**: a 13-step search generator at fuel
4 000 000 that crosses node 2048.

> **A certificate cannot be split without changing it.** Splitting the walk in
> two would re-run its first twelve steps in both halves — doubling the work to
> halve the wall, which is not a trade. So `_walk` stays whole and stays the
> critical path.

The win here is real but smaller and differently shaped: `_walk` now overlaps
`pins_bound`'s five leaves instead of queueing behind the rest of its own file.
**Amdahl was predicted before the edit and confirmed by the structure**, which
is why this entry states it rather than leaving a future reader to wonder why
the second file did not halve.

### `genmoves_ray` is NOT included, and the reason is measured

It is not a leaf: `genmoves_scan`, `genmoves_drain` and `sf_order/transport`
all `open` it and consume its 173 theorems. Sharding it needs a re-exporting
facade — a materially riskier change that should be priced on its own rather
than bundled with a pair that splits cleanly.

### The certificates did not move, and that is CHECKED

Every `#guard` BLOCK (several span a dozen lines) was extracted from the
pre-shard file and from the shards, sorted, and compared:

    pins_bound   guards 26 -> 26  identical=True
    pins_clock   guards  6 ->  6  identical=True | theorems 1 -> 1 identical=True

A topology change that cannot prove its certificates are untouched is a
refactor with a story attached, and this lane has enough of those.

### Ride-along: the checker's own SyntaxWarning

`harness/divergence_register.py`'s `_strip_lean_comments` docstring QUOTES a
regex — ``^\s*def foo`` — in a plain string, so `\s` is an invalid escape:
a `DeprecationWarning` on 3.9 and a **`SyntaxWarning` on 3.14, emitted on every
gate run**. Now an r-string. *Prose that quotes code is still code to the
lexer* — and an instrument that warns on every invocation trains its readers to
ignore its output.

### And a note for the checker's ledger, from the fleet red this week

Master's register gate is red on rows using kinds outside §5.0a's enum. The
root cause is not the rows: **that tier's tenure floor never ran the register
gate at all, so its data was never exercised** — the corpus-exercise law, one
layer up, at the GATE rather than at the witness. The checker was right and
stays exactly as strict as it is; a checker loosened to accommodate unexercised
data would have converted a loud red into a silent wrong claim.

## 2026-08-25-pycomplete-25 — the midgame board splits by DEPTH, and the field-collision sweep returns a clean negative

Two items, and the first is the previous inch's own profile turned back on itself.

### `pins_bound_mid` was 74% of its family, and the axis was DEPTH

The five-way shard measured `_mid` at **875 s — 74% of the whole bound
family**, capping its win at **1.3×** where 2× was hoped. Balancing by guard
COUNT was the wrong axis; so was balancing by FAMILY. The cost follows depth,
and **the certificates print the evidence themselves** — each guard's expected
pair carries its node count:

| depth | guards | nodes | share | predicted |
| --- | --- | ---: | ---: | ---: |
| `_mid_d1` | `0 1`, `60 1` | 71 | 4.6% | ~40 s |
| `_mid_d2` | `0 2`, `60 2` | 826 | 53.3% | ~466 s (7.8 min) |
| `_mid_d3` | `0 3`, `60 3` | 653 | 42.1% | ~369 s (6.1 min) |

> **PREDICTION, stated before the tenure:** the bound family's critical path
> falls **14.6 → ~7.8 min (1.88×)**, set by the `_mid_d2` pair. Not the even
> thirds a guard count would suggest — 53/42/5 is what the node counts say.

**An even split was available and NOT taken.** Mixing depths across shards
(`0 2` alone; `0 3`+`60 2`; the rest) would balance to ~42% and shave a further
~1.7 min. It muddies what a red names — the whole point of the boundary — and
**the fleet floor is `pins_clock_walk` at 19.1 min either way**, so the extra
balance buys nothing that matters. Optimising below the floor is motion, not
progress.

`posMid` lifted to `pins_common` verbatim, as `boundProbe` did. Certificates
re-checked across the whole bound family: **26 → 26, identical**.

### THE FLEET FLOOR, named so nobody re-derives it

`pins_clock_walk` at **19.1 min is irreducible** — one certificate, and a
certificate cannot be split without changing it. Nothing to do but know it.
`genmoves_ray` (5.9 min) stays priced separately: it is not a leaf, so it needs
a re-exporting facade.

### The field-collision sweep: a clean NEGATIVE, checked rather than assumed

The fleet sweep asks whether any field this tier's instrument writes into an
envelope could be overwritten by the source when properties merge (ES's defect:
the node type in `kind`, silently beaten by the source's own `kind`).

**Impossible by construction here, because the pyc extractor is hand-built
rather than merge-based.** Verified mechanism by mechanism:

* no `.update()` on any emitted node — the two in the file operate on
  name-census *sets*;
* no `vars(node)`, no `node.__dict__`, no `{**…}` dict-unpack anywhere;
* `ast.iter_fields` appears **once**, inside `_replace_node`, an AST→AST
  rewrite (`type(root)(**fields)`) for the hoisted filter — never envelope
  construction.

**And the specific hazard was real.** CPython's `ast.Constant` *does* own a
field named `kind` — the string prefix, `'u'` for `u"abc"`. Measured:
`u"abc"` gives `value='abc', kind='u'`; `"abc"` gives `value='abc', kind=None`.
The extractor **never reads `node.kind`**, emitting `{"kind": "Constant", …}`
hand-built, so the source's `kind` is dropped rather than merged — and dropping
it loses nothing, the `u` prefix being lexical only in Python 3.

**The transferable half:** in `unsupported()` this tier already does what ES's
fix requires —

    "kind":    "Unsupported",
    "py_kind": py_kind if py_kind is not None else type(node).__name__,

the source-derived node type gets a **different field name**. *When an
instrument records what the source IS, the field must not be one the source
also owns.* Disjoint by naming, not by luck.

### And a process correction, recorded because it is my own law

`pyc-del` was never pushed; the coordinator had to fetch from the worktree.
Inch 1's rule — *push when the thing you would have to redo becomes green* —
includes the push, and I had been treating "committed and reported" as done.
The claim sequence is now **verdict → verify tree → commit → PUSH → report**.
## 2026-08-25-pycomplete-26 — the register's three clauses, and a probe that was starting UNLOCKED BUILDS

§5.0a's empty-register ruling (`52e9c4b`) lands in the shared checker, which
this lane owns. **A file's legality is decided by its CLAIM, not its LENGTH.**

1. `rows: []` is LEGAL iff `retired_rows` is non-empty — the claim being *"no
   LIVE debts, and here is how each one closed."*
2. `rows: []` **and** `retired_rows: []` is an ERROR whose message says to
   DELETE the file: it makes no claim at all, and an empty ledger reads as
   diligence while asserting nothing.
3. Every retired row must name a guard whose **EXISTENCE** the checker
   verifies.

### Clause 3 inverts the retirement discipline, and that is the point

**EXISTENCE, NOT PASSAGE** — and the distinction carries the design. A retired
row's `still_divergent` should now FAIL; that failure is the signal the
divergence has come back. Asserting it *holds* would invert the meaning;
asserting nothing would let the guard be deleted along with the row and take
the watch with it. So the checker requires the guard to exist, does not
require it to pass, and excludes retired guards from the ORPHAN rule.

**This corrects my own retirement of `pyc-div-2`** (§pycomplete-20), where I
deleted the row *and* its guards precisely to avoid the orphan error. Under the
ruled contract that was the wrong move: retirement moves a row to the archive,
it does not end the watch. Restoring `pyc-div-2` as a retired row with its
guards live is owed and is not in this commit — it is a data change to this
tier's own file, and the checker lands first so the fleet has one instrument.

### Blast radius, measured before landing

| tier | result |
| --- | --- |
| `es` | 0 problems |
| `python` | 0 schema problems (its probe is post-build) |
| `sv` | **2 problems** — `sv-div-2`'s two retired guards do not exist |

C's file is absent from master pending its restore, so **clause 3 reds SV, not
C** — and SV has no dispatch. Reported rather than softened: the migration
clause was for shapes shipped before a canon, and these guards were *deleted*,
which is the thing clause 3 exists to catch.

### AND THE PROBE WAS STARTING UNLOCKED LEAN BUILDS — my defect, found by tripping it

Running the shared checker in a fresh worktree kicked off a **`lake build` with
no tenure**, competing with the lane that held the lock. Cause: §pycomplete-23
made `pyc_div_1`'s probe two-sided, so it calls `tools/leanpy` — and `leanpy`
BUILDS when `.lake` is cold. Every tier whose floor runs the shared checker
would have paid that, in whatever clone they happened to be in.

> **Making a probe two-sided turned a Lean-free check into a Lean-executing
> one, and the instrument is shared.** The blast radius of a probe change is
> every lane that runs the checker, not just the tier that owns the row.

The probe now checks for `.lake/build/bin/leanmodels-run` and, when it is
absent, FAILS with the post-build-gate message instead of building. That file's
docstring already *claimed* it "runs as a POST-BUILD gate"; this is the claim
made true rather than asserted — a guard that cannot run must fail, never skip,
and never build.

Self-test: **15 defect classes + 3 clause cases**, the clause fixtures built
explicitly rather than mutated from a neighbour's file so they stay
deterministic as tiers come and go.

## 2026-08-25-pycomplete-27 — pyc-div-2 goes back on the watch, and the watch gains the alarm it was missing

§5.0a clause 3 shipped, so this tier's own file gets corrected against the
instrument rather than against my memory of it.

### The correction

At §pycomplete-20 I retired `pyc-div-2` by deleting the row **and its two
guards** — deliberately, to avoid the checker's ORPHAN error. Clause 3 ruled
that wrong: **retirement moves a row to the archive; it does not end the
watch.** The row is now in `retired_rows` with `retired`/`retired_by`, and
`pyc_div_2_still_divergent` / `pyc_div_2_has_not_widened` are live again in the
probe, reporting FAIL and not gating.

The `LIVE_GUARDS` / `RETIRED_GUARDS` partition is copied from
`sv_divergence_probe.py` deliberately — **one shape for a third tier to copy,
not two.**

### AND THE WATCH COULD NOT RAISE AN ALARM

Unit-testing the partition surfaced the case nobody had covered. For a retired
row the polarity of `still_divergent` **inverts**: FAIL means the divergence is
gone (healthy), and `ok` means it **came back**. Measured on the shipped shape:

| live | retired | rc | meaning |
| --- | --- | ---: | --- |
| pass | FAIL | 0 | healthy archive — correct |
| FAIL | FAIL | 1 | live guard gates — correct |
| pass | **ok** | **0** | **the divergence RETURNED, and nothing went red** |

The third row is the one the archive exists for, and it was **silent** — the
guard prints a cheerful `ok`, does not appear in the "reporting not-held"
summary, and the probe exits 0. SV's file names the event in prose (*"it
flipping to `ok` is the event worth looking at"*) and does not gate on it
either, so this is a fleet-wide gap rather than a local slip.

> **A watch whose most important signal produces no alarm is not a watch.**
> Keeping the guard alive was the ruled half; making its regression *fire* is
> the half that makes the guard worth keeping.

So a retired `*_still_divergent` that HOLDS now sets `rc = 1` with an explicit
REGRESSION message saying the row must leave the archive and become a live debt
again. **This does not contradict "existence, not passage"** — that rule
governs what the shared CHECKER may assert about another tier's row. What a
tier's own probe does about its own regression is the tier's business, and a
silent regression is precisely the failure the archive was created to prevent.

All three states are unit-tested by stubbing the two guard sets, so the
polarity cannot drift unnoticed — the test asserts `rc` for each, including the
regression case that has never yet occurred.

## 2026-08-25-pycomplete-28 — `watch` is not `FAIL`, and the polarity table becomes a file

Two ruled adoptions, both small, both closing gaps the previous inch opened.

### One word, two severities

With the regression alarm live, `FAIL` meant **opposite things** in the same
column: on a LIVE guard it gates, on a RETIRED one it is the archive behaving.
A reader scanning a column of `FAIL`s could not tell which was which. Ruled
fleet-wide and adopted verbatim from `sv_divergence_probe.py`: the healthy
retired state prints **`watch`**.

    pyc_div_1_still_divergent  FAIL   …              ← gates
    pyc_div_2_still_divergent  watch  …  [retired row] ← the archive working

*A status word that means "stop" in one row and "carry on" in the next is not a
status word.*

### The three-state table is now a file, not a stub I ran once

`harness/test_divergence_probe.py`, runnable against **any** tier's probe and
defaulting to all of them. Stubs the guard callables, runs no Lean, touches no
register file, and asserts:

| live | retired | rc | meaning |
| --- | --- | ---: | --- |
| pass | not-held | 0 | healthy archive |
| FAIL | not-held | 1 | a live guard gates, as always |
| pass | **HELD** | **1** | **REGRESSION — the divergence returned** |

The third row is the one worth having in a file. It has **never occurred in any
tier**, and a case that has never occurred is exactly the one nobody notices is
missing — it was silent in two tiers simultaneously until it was stubbed and
asserted. **The empty-container law pointed forwards: do not wait for the event
to find out whether the alarm is wired.**

A probe that has not adopted the LIVE/RETIRED partition FAILS the test rather
than being skipped, so the shape spreads by measurement. Both restored tiers
pass today; C inherits the test with its restoration.

### AN INSTRUMENT LIVES IN THE SPACE IT SEARCHES — third instance

The new test is named `test_divergence_probe.py`, which **ends in
`_divergence_probe.py`**, so its own glob matched itself and reported it "NOT
PARTITIONED". That is the third time this family has bitten the register work:

* a grep-based existence check that found its fake guard names **in its own
  source** (§pycomplete-20);
* a substring test that found a name in **its own fixture file**
  (§pycomplete-21);
* now a glob that found **its own file**.

> **Every pattern an instrument writes must exclude the instrument on purpose.**
> The bug is never the pattern being wrong about the world; it is the pattern
> being right about a world that contains the pattern.

## 2026-08-25-pycomplete-29 — the zero-live pole: my own test was asymmetric about a legality my own ruling created

C's restoration is the polarity test's first real subject, and it found the
place the test was **wrong** rather than the place C was.

### The defect was mine, and it was an asymmetry

`c_divergence_probe.py` has `LIVE_GUARDS = {}` — four retired rows, no live
ones. That is the pole §5.0a clause 1 made legal (`rows: []` beside a non-empty
archive), and C names it sharply: *rc comes entirely from the regression alarm;
the probe cannot report anything except a return.* My test printed **"no live
guards to stub"** and counted C as not honouring the table. **Master's fleet
test went red on a correct probe.**

The shape of the mistake is worth more than the fix. One inch earlier I had
written an explicit, labeled `n/a` for the **zero-retired** case, with a
sentence about why a skip would be dishonest. I did not give the **mirror**
case the same treatment — and the mirror case is one *my own clause-1 reading
had just made legal*.

> **An instrument that handles one pole explicitly and the other by accident is
> not symmetric — it is untested at the second pole.** Having written the
> careful branch, I stopped looking for its twin.

### The zero-live expectation, as ruled

Stub only the retired set; assert `rc = 0` with all retired not-held, and
`rc = 1` + alarm with any retired HELD. Printed as its own labeled state:

    c_divergence_probe.py    ZERO-LIVE retired=not-held  rc=0  ok — no live rows; rc is the alarm alone
                             ZERO-LIVE live=FAIL         n/a  no live guards to fail — vacuous, not unmet
                             any retired=HELD            rc=1  ok (regression alarm rang)

**Vacuous, not unmet** — states 1–2 have no live guard to exercise, which is a
different fact from failing them, and the line says which.

Fleet result: **all three probes honour the table.**

### The two failure branches are exercised, not asserted

A test about unexercised cases must not ship unexercised branches. Both new
rejection paths were run against synthetic probes: `NO GUARDS AT ALL` (both
sets empty — a probe that asserts nothing is not a probe) and `NOT PARTITIONED`
(no `LIVE_GUARDS`/`RETIRED_GUARDS` at all). Both fail as intended.

### The same bug, twice in one inch — and I pushed on the second one

Committing the fix above, the register self-test died with `IndexError: list
index out of range`. **I pushed anyway**, because I read the gate output
instead of gating on its exit code — the exact failure being corrected one
level up in the same hour.

The cause is the zero-live pole *again*, one layer down. The self-test builds
its 15 fixtures by mutating `rows[0]` of `sorted(glob(PATTERN))[0]`, and C's
file — legally `rows: []` under clause 1 — sorts first. The moment it landed,
every fixture in the shared checker's self-test broke.

> **Pick by the PROPERTY the fixture needs, never by sort order.** `base[0]` was
> never asking for "a file with a live row to mutate"; it was asking for "any
> file", and got one that could not serve.

Now selected by `rows` being non-empty, with a loud failure if no file has one
— because "no fixture base available" must not read as "passed".

**Three occurrences of one root cause in a single inch**: the test's zero-live
blindness, the self-test's `rows[0]`, and my own review missing both until the
interpreter and the coordinator caught them. The legality clause 1 introduced
has a blast radius through every instrument that assumed a non-empty ledger,
and that radius was not swept when the clause landed.

## 2026-08-25-pycomplete-30 — OPS-148 named negative for the checker, the probe and the polarity test

Per OPS-148 (arch, 9b72995), the four spellings, greped across the three
instruments this lane owns: `harness/divergence_register.py` (the shared
checker), `harness/pyc_divergence_probe.py`, `harness/test_divergence_probe.py`.
**Named negative, not "looks fine": 48 sites, one real defect, one named
dependency.**

### (a) First-element access — 19 sites, **1 real defect, fixed here**

| shape | n | verdict |
|---|---|---|
| `d["rows"][0][...]` fixture mutators | 13 | safe *now* — base guaranteed non-empty, and every file exercised |
| `with_rows[0]` fixture base | 1 | **DEFECT — fixed** |
| `label[0]`/`label[1]`, `declared_as_guard(...)[0]` | 4 | fixed-arity tuples, not growable collections |
| `problems[0][:70] if problems else ""` | 1 | explicitly guarded |

The defect is the one **my own fix for the IndexError left behind**. Selecting
the first file that *has* rows cured the crash but left the subject floating:
when ES filed its register, the 15 defect classes silently stopped being
exercised against the tier that wrote them and began testing **ES's document**.
No crash, no message — a change of subject.

> Sort order was never the property being asked for. The cure is not a better
> pick but **no pick**: the fixtures now run against *every* register file with
> a row — 15 × 3 = 45, and coverage grows with the fleet.

This is arch's generalization at one remove: adding ES to the register set
changed which document an aggregate *selected*, exactly as adding a category
changes every fold.

### (b) `if rows` as a proxy for "this tier has a register" — 6 sites, **0 defects**

`rows = doc.get("rows") or []` normalizes; `for row in doc.get("rows", [])`
iterates; `hasattr(LIVE_GUARDS/RETIRED_GUARDS)` tests partition *presence*, not
population. `if not rows and not retired` is the clause-2 both-empty error and
is deliberately **and**-ed — the clause-1-correct spelling. No site treats a
non-empty `rows` as a proxy for participation.

### (c) Aggregates with unstated identity — 9 sites, 0 defects, **1 named dependency**

- **`ok = True; ok &= …`** (polarity test). Identity `True` means a probe
  entering *neither* branch passes **vacuously**. The only thing preventing
  that is the `NO GUARDS AT ALL` rejection above it — **that guard is now
  load-bearing for the fold's soundness**, recorded so a future edit that
  removes it knows what it is removing.
- `all(… for x in g)` over an empty guards list would be vacuously true, but
  `len(g) != 2` short-circuits first in the same `or` chain: `[]` is rejected
  as "not two".
- `any(needle in p for p in problems)` over empty → `False` → reports NOT
  REJECTED. Correct polarity: empty means fail, not pass.
- `sum(…)` report folds → 0; reporting only.

### (d) Empty-collection messages that read as verdicts — 14 sites, **1 defect, found by RUNNING the thing**

Every one already discriminates: *"no probes found — nothing asserted"* → FAIL;
*"A register checker with no data is vacuous. FAIL."*; *"no register file has a
live row … which is not the same as passing"*; and the two `n/a` lines say
**"vacuous, not unmet"** and *"asserted the day one is archived"*. Watch item:
`held = sum(…)` prints 0 as "none held", which would read as good news over an
empty guard set — unreachable in a valid file only because of the both-empty
rejection.

**And then I ran the probe, and spelling (d) was in it.** Ninety seconds after
filing "(d) 0 defects", `pyc_divergence_probe.py` printed **`FAIL`** in a cold
clone — because `.lake` was cold, the post-build guard correctly declined to
run, and *"nothing was compared"* was folded into the same `False` as *"the
divergence regressed"*. Identical word, identical exit code, opposite meanings:
**a statement about the ENVIRONMENT wearing the costume of a verdict about the
MODEL.**

> **A named negative produced by grep is a claim about text, not about
> behaviour.** The sweep read four spellings across three files and certified
> the one instrument whose defect only appears when it *runs*. Grep cannot see
> a value folded into the wrong state at runtime.

Fixed with a third state: guards return `held is None` for "could not compare",
which prints `no-run` per guard and closes with **`COULD NOT VERIFY (no
comparison ran — not a model verdict)`**. Live guards still fail **closed** —
rc stays 1, unverified never counts as passed — and `_still_divergent`
regression detection reads `held`, so an unverified guard cannot raise a false
alarm either.

### ES's OPS-148 item — named negative, 3 sites, **0 live**

The pre-ruling sentence *"a register file with nothing in it is a claim that the
tier has no debts, and should be deleted rather than filed empty"* survives at
exactly three places, **none of them a live assertion**: `docs/backlog/c.md`
(C's own record of the ruling that superseded it) and
`docs/family-architecture.md:4394` (the ruling quoting the old canon in order to
amend it — *"The canon said …"*). The shared checker's live text already carries
the ruled form verbatim: `rows: []` beside a non-empty `retired_rows` is *"a
real and useful claim … so it is LEGAL"*, and `DELETE IT` fires only on
`not rows and not retired`. **Code and text agree; no edit made.** Confirmed
before ES's row retires rather than on the day it does.

### Recorded from the landing

> **A category added to a set changes every aggregate over that set — every
> fold written before the ruling silently treats the new kind as the old one.**
> Relay norm: **the first tier through a new ruling publishes the traps, not
> just the code.**

The `with_rows[0]` defect is the sharpest evidence for the first half: the fold
did not fail, it quietly redirected.

## 2026-08-25-pycomplete-31 — exit 143: the RSS discipline is machine-scoped in its claim and lane-scoped in its mechanism

pyc9's depth-split tenure died at 13:30:31 after 41 minutes of build:

    ✖ [884/911] Building Examples.python.sunfish.genmoves_ray (547s)
    error: Lean exited with code 143
    [13:30:31] GATES NOT RUN (build red — aborted triad)

**It was not a red build, and `genmoves_ray` is a file this commit never
touches.**

### Ruling out the fleet's own guard, by mechanism not by guess

triad's A16 guard kills with **`kill -9`** (→ exit **137**) and prints
**`RSS KILL LINE (A16, per-process)`** before it does. The log contains
**zero** KILL LINEs, and 143 is **SIGTERM**, not SIGKILL. So the guard did not
fire — which also means `lean` stayed **under** the 5 GB/proc cap. Nothing the
fleet measures was exceeded.

### What was actually true of the box

| | at failure |
|---|---|
| physical free | **~56 MB** |
| swap | **12002 M / 13312 M used (90%)** |
| load (2 cores) | **15.40** |
| `genmoves_ray` | **547 s**, against **18 s** in `lm_build.log` — **30×** |

And the cause is **outside the fleet entirely**: `lake build
AlgebraicComplexity …` out of `~/repos/matrix-m…`, a different repository,
running throughout and still running after.

*Honest limit on this claim*: I could not find a jetsam record naming the
`lean` process, so an OS-level memory kill is **inference from convergent
evidence** (SIGTERM, no KILL LINE, 30× slowdown on an untouched file, 90% swap),
not a log citation.

### The finding, and it is in triad's own header two rules apart

> line 110 — *"the lock, the ticket, the RSS discipline are about **THE
> MACHINE**, not about the repository"*
> base rule 6 — *"never kill another lane's processes — kills by **PARENTAGE**
> only"*

Both are right, and together they leave a gap:

> **The RSS discipline protects the machine FROM a lane; it cannot protect a
> lane FROM the machine.** Its claim is machine-scoped, its measurement is
> subtree-scoped, and a resource is only as governed as it is *measured*.

Base rule 6 should not change — never killing another lane's processes is
correct, and doubly so when the competitor is another repository whose work is
none of the fleet's business.

### The word was wrong, and it is the defect I fixed in my own probe an hour ago

`GATES NOT RUN (build red — aborted triad)` — **the build was not red, it was
killed.** triad already distinguishes *"resource kill, not a red build"*
(header line 21), but **only for kills it performs itself**. A kill from
outside lands in the same channel as a genuine compile error.

That is precisely the shape I fixed in `pyc_divergence_probe.py` at
`8e4ebaf`: *a statement about the ENVIRONMENT wearing the costume of a verdict
about the code.* Same defect, one level up, in the instrument every lane trusts.

**Proposed (arch's call, not mine):** on a nonzero build exit whose code is
signal-shaped (**137/143**) with **no KILL LINE of our own**, sample machine
memory and report `BUILD KILLED FROM OUTSIDE — box at N MB free, swap X%` rather
than `build red`. The distinction is worth real time: this cost one tenure plus
a **4593 s** queue wait, and any lane can lose the same.

### Re-queued, not retried blind

Rebased onto master tip `9c5b3f8` first (safe to do: the lock was released, and
master now carries **both** C's `rows: []` register **and** the fixed checker,
so the self-test gate passes for the right reason). Verified before enqueue:
self-test green at **15 × 3**, and the six certificates **byte-identical** to
pre-split after the rebase. Ticket `…-21614-pyc9`, tree `4a4501494f46`.

## 2026-08-25-pycomplete-32 — genmoves_ray DOES shard; my earlier "no" came from a substring grep

`genmoves_ray` killed pyc9's first tenure (pycomplete-31). Re-censused it while
the re-run built, and **the verdict I gave the coordinator was wrong.**

### What I reported before, and what is actually true

I reported *"`genmoves_ray` is not a leaf — `genmoves_scan`, `genmoves_drain`
and `sf_order/transport` all `open` it, so it does not shard naturally without
a facade."* That came from `grep -rln 'genmoves_ray'` — **a substring match,
which counts a prose mention as a dependency.** Anchored on real syntax:

| file | relationship |
|---|---|
| `genmoves_scan.lean` | **the only true `import`** |
| `genmoves_drain.lean`, `sf_order/transport.lean` | `open` the namespace, reached transitively |
| `genmoves_theorem.lean`, `LeanModels/Python/PayloadBlind.lean` | **prose mentions only — not dependents** |

> **I made the exact error the register checker was hardened against.** ES
> flagged the substring test one day ago; I replaced it with anchored `def` +
> `#guard` and wrote a fixture where the name lives only in a comment. Then I
> ran a census whose evidence was a bare `grep -rln` — and two of its five hits
> were names living only in a comment.
>
> **Hardening an instrument does not harden the hand that reaches past it.**

### It shards, and the constraint is the NAMESPACE, not the import

One direct importer makes a facade trivial. The real constraint is the two
transitive `open`ers: `open Examples.python.sunfish.genmoves_ray` must keep
resolving, so **the shards must declare INTO the parent namespace** rather than
into their own. Lean permits many modules to contribute to one namespace, so
every current `open` and `import` site stays byte-identical.

Seams are already there — 173 theorems in clean families:

    pB 36 | rayBody 21 | ray 20 | cast 22 (rCast 8 + castH 7 + castA 7)
    pawn 18 (pawn 11 + pProm 7) | remainder ~56

with the 31 `def`s lifting into a `genmoves_ray_common.lean` exactly as
`boundProbe`/`posMid` lifted into `pins_common.lean`.

### And the reason to do it is MEMORY, not minutes

The sharding task was dispatched on **build time**. `genmoves_ray` is the case
where it is **build survivability**: a 3740-line module elaborating 173
theorems in ONE `lean` process is the fleet's memory cliff, and splitting it
lowers peak RSS per process whether or not it saves a second of CPU. **A shard
that saves no time and prevents an OOM is still worth landing** — which is not
what the original framing would have predicted, and is the reason to revisit a
target that was correctly de-prioritised on speed alone.

## 2026-08-25-pycomplete-33 — genmoves_ray shard: the prediction, registered before the tenure

### The family split, named

Full prefix census of the 173 theorems (the earlier "top 8" truncated prefixes
and undercounted `pB*` and `cast*`):

| shard | families | theorems |
|---|---|---|
| `genmoves_ray_pB` | `pB0` 10, `pB1` 11, `pB2` 9, `pB3` 5, `pB3Test` | ~36 |
| `genmoves_ray_ray` | `ray` 20, `rYield`/`rPawn`/`rCrawl`/`rStop`/`rRest`/`rYieldVal`/`rPawnTest` | ~32 |
| `genmoves_ray_cast` | `castH` 7, `castA` 7, `rCastH` 3, `rCastA` 3, `cH`/`cA`/`cHVal`/`cAVal`, tests | ~26 |
| `genmoves_ray_pawn` | `pawn` 11, `pawnQ`, `pawnBody`, `prom*` 7, `pProm*` 6 | ~25 |
| `genmoves_ray_rayBody` | `rayBody` | 21 |
| `genmoves_ray_common` | the 31 `def`s + shared `open Ref` blocks | — |
| `genmoves_ray` (facade) | imports the five; keeps the 37 `#guard`s | — |

~30 structural singletons (`Heap`, `heapEq`, `flatten`, `absInt`, `RayLocals`,
`RayFrame`, `SlotOnly`, …) land in `_common` or the facade **by a dependency
census at the inch, not by this table** — I have not verified which are
infrastructure for the families and will not guess.

**Namespace continuity is the load-bearing constraint**: every shard declares
into `Examples.python.sunfish.genmoves_ray`, so `genmoves_scan`'s `import` and
`genmoves_drain`/`transport`'s `open` stay byte-identical.

### The memory prediction, and it points TWO ways

> **Largest single-process peak: DOWN. Concurrent aggregate: UP or flat.**

Not a hedge — a consequence. Each new `lean` process **re-pays Lean's constant
import baseline**, so the per-process peak falls only by the *module-specific*
portion (never by 1/6), while N shards building concurrently can cost **more**
in aggregate than one large module. Under a per-process cap that is a win;
**on a starved box, which is what actually killed pyc9, it could be a loss.**
Registering both directions is what makes the inch falsifiable rather than
self-confirming.

### The evidence — and why neither named proxy can supply it

Both proxies the dispatch offered are **too weak for this claim**, and saying so
is the point:

- **Job count** (911 → ~917) is uninformative about memory *by construction*.
- **Largest module's elaboration time** is a *weak* proxy: Lean modules can be
  slow-and-small (deep unification, little allocation) or fast-and-large.

So I am supplying the missing instrument rather than reading a proxy that
cannot answer. `/private/tmp/rss_sampler.py` samples `ps` every 10 s, attributes
by **tree path** (excluding the external `AlgebraicComplexity` build competing
for the same RAM), and records **per-module peak** *and* **concurrent
aggregate** — the two numbers the prediction splits on. It is not Lean
execution, so it touches no lock, and it writes nothing to the frozen tree.

**The baseline is being captured NOW, during this unsharded run** — that window
closes when the build ends and cannot be reopened without another tenure.
First samples: `genmoves_ray.lean` **469.59 MB** and climbing.

Two caveats recorded beside every figure rather than discovered later:

1. A sampled maximum misses spikes shorter than the interval — **every number
   is a lower bound.**
2. **Under swap pressure RSS measures what the OS *let* the process keep, not
   what it wanted.** A before/after comparison across different pressure
   regimes is therefore *not fair*, so load and swap are recorded at every
   peak, and a cross-regime comparison will be reported as **inconclusive**
   rather than quietly averaged.

## 2026-08-25-pycomplete-34 — the depth-split verdict, and the memory premise falsified by my own instrument

### The verdict: the critical path prediction holds

`pins_bound_*` elaboration, from the killed run's log (it built these before it
died, and the green re-run reused their `.olean`s):

| shard | nodes | time | s/node |
|---|---|---|---|
| `pins_bound_mid_d1` | 71 | **65 s** | 0.92 |
| `pins_bound_mid_d2` | 826 | **515 s** | 0.62 |
| `pins_bound_mid_d3` | 653 | **454 s** | 0.69 |
| `pins_bound_h` | — | 277 s | |
| `pins_bound_tac` / `searcher` / `end` | — | 51 / 26 / 10 s | |

**Predicted critical path ~7.8 min (468 s) set by `_mid_d2`; actual 515 s —
within 10%.** The node-count model (71/826/653) predicted the split well;
s/node is near-constant, which is why counting nodes beat counting guards.

### And the cost the prediction ALSO named: the total went up

`65 + 515 + 454 = 1034 s` against the **875 s** previously measured for the
unsplit `posMid` — **~18% more total CPU**. Splitting lowers the critical path
and *raises* the total, because each shard re-pays the import cost. That is the
**same mechanism I registered for memory** hours earlier, showing up in time.
*Soft*: 875 s came from a different run under different load, so this is a
cross-regime comparison and I am reporting it as directional, not exact.

`_d3` at 454 s is nearly `_d2`'s equal, so the split is **not balanced** — a
further win needs the d2/d3 pair split again, not a fourth sibling.

### THE MEMORY PREMISE IS FALSIFIED — and my own instrument did it

Peak RSS, sampled during the green run (**scope: only the ~15 modules this run
actually rebuilt**, since `.lake` was warm — not the full 911):

     1989.88 MB  bound_depth.lean
     1590.55 MB  move_gate.lean
     1465.55 MB  move_residue.lean
     1383.64 MB  genmoves_drain.lean
     1318.58 MB  value_bound.lean
      ...
      589.94 MB  genmoves_ray.lean

> **`genmoves_ray` is not the memory cliff. `bound_depth` is 3.4× larger in the
> same run, same regime — a fair comparison.**

`genmoves_ray` died in the first tenure not because it is the largest, but
because it was **the module that happened to be running when the box ran out**.

> **Under machine-wide starvation the victim is chosen by TIMING, not by SIZE.**
> Every "this module is the fragile one" conclusion drawn from *which module
> died* is an artifact of scheduling.

### And the lane never had a memory problem at all

Concurrent aggregate peak **2301.78 MB** against a **10240 MB** chain cap and a
**5120 MB** per-process cap. The lane used **22%** of its chain budget at peak.
**No topology change to any fleet file would have prevented that kill** — it was
external oversubscription by another repository, and sharding cannot fix a
machine-wide shortage.

### So the approved justification is wrong, and I have to say so

I reframed the `genmoves_ray` shard as **"survivability, not minutes"** and it
was approved on that basis. **The measurement refutes the reframe.** But the
same run makes the *original* case strongly: `genmoves_ray` took **962 s** — the
single largest elaboration in the tree, ahead of `_mid_d2`'s 515 s.

**The inch survives; its justification reverts to the one I talked us out of.**
Minutes, not survivability. Worth stating plainly rather than quietly letting an
approved-but-wrong premise carry a tenure — the prediction discipline worked
exactly as intended, falsifying a claim *within the hour* and *before* the
tenure was spent on it.
