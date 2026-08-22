# Backlog — MOVED

**This file is a redirect, and it is FROZEN. Do not append to it.**

`docs/family-architecture.md` §9.5 retired the single-file backlog:

* **your lane's entries go in `docs/backlog/<lane>.md`**, appended only by
  that lane, with ids `YYYY-MM-DD-<lane>-<n>` that need no reservation;
* the single view across every lane is
  [`docs/backlog/INDEX.md`](backlog/INDEX.md), **generated** by
  `tools/backlog-index.sh` and never hand-maintained (§5.5);
* everything written before the split is in
  [`docs/backlog-archive.md`](backlog-archive.md), frozen, where **every
  `§Lnn` reference still resolves at the heading it always had.**

This stub exists because **111 tracked files cite `docs/backlog.md`** —
including `.lean` files, whose edit would make a docs landing tier-class. A
big-bang sweep is exactly what §9.2 forbids; the old spelling is retired **by
touch**. Until then, a citation that lands here is one hop from its target.

`tools/backlog-index.sh --check` asserts the index is in sync, and
`tools/docs_check.py` reports it when it drifts.

### NEW LAW — count the PATTERN POSITION, never the IDENTIFIER (§5.4a's constructive half)

Minted by the completeness lane on its **third** hit, corroborated by the
rebuild's `DRAIN` collision the same day. Placed beside *"a grep that agrees with
your prior is the one to re-run"* as its **constructive half**: that rule says
**re-run**, this one says **what to count**.

> **A COUNT THAT PRICES A DECISION MUST COME FROM THE PATTERN POSITION, NEVER
> FROM THE IDENTIFIER.**

An identifier count answers *"how often is this name written?"* — mentions,
docstrings, other lemmas' statements, the doc you are reading. A decision is
priced by *"how many places must change?"*, and those are **pattern positions**:
match arms, clause slots, actual branch points.

| instance | what went wrong | direction |
| --- | --- | --- |
| §L49's `\.usub` grep | missed every `cases op with \| usub =>` arm **by one character** | UNDER |
| §L53's walker price | landed at **19** because **catch-all arms were load-bearing** | UNDER |
| today's VCGen price | **26 lemma NAMES** priced a **9-arm** change at **35**, nearly moving a date | OVER |
| the rebuild's `DRAIN` | generator drain vs the short-circuit trick — a collision that **agreed with the prior** | OVER |

**Both directions are live, which is why the rule names the POSITION rather than
saying "count carefully."** Identifiers over-count because names appear where no
work happens; pattern searches under-count when the syntax differs by a
character; and **catch-all arms defeat arm-counting entirely** — one `| _ =>` can
absorb a dozen cases, so even a correct arm count can be the wrong price.

Practical form: **price a change by enumerating the positions it must visit, and
check that enumeration against the thing that DISPATCHES** — the `match`, the
clause list, the table — never against the name index.

### THE `GenFrame` RULING — what a SHARED type may do while the legacy layer erodes

Erosion raises a question neither "freeze it" nor "maintain it" answers: a type
used by **both** layers, not itself retiring, which the **new** layer needs to
**grow** for a new capability.

> **A shared-not-retiring type MAY grow for new capability. The legacy
> interpreter's contract is exactly three things: it COMPILES, it REFUSES what it
> does not implement, and it GAINS NO CONSUMERS.**

The growth lands and the legacy layer absorbs it with **a one-line refuse arm —
the legacy layer's ONLY permitted growth.** Not a stub that half-works, not a
TODO, not an implementation. A refusal is loud, fuel-independent and correct
(cause 1), so the legacy layer stays **true** without being **maintained**.

**Both foreclosed failure modes are real.** Freezing the type blocks the new
layer's capability on a layer that is supposed to be dying — the dead hand of the
thing being retired. Implementing the arm gives the legacy layer a **new consumer
and a new reason to live**, which is the opposite of erosion. The one-line refuse
arm is the unique move that keeps it compiling without giving it a future.
