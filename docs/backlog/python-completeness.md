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
