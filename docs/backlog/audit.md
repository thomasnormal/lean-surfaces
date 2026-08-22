# The audit lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by
the audit lane.** Ids are `YYYY-MM-DD-audit-<n>` and need no reservation,
because the lane name makes them unique.

This lane writes **no Lean and runs none** (A11). Its subject is what the
family has built twice: every number here is git, grep, `ps`, `du` or
`python3 -c`, and the reproducing command is printed beside it. Audit #1
predates this file and lives at `docs/backlog.md` §L89; the standing
deliverable is `docs/duplication-audit.md`, which gains a dated section per
audit rather than a new file.

---

## 2026-08-22-audit-1 — AUDIT #2: adoption is real (6 lanes), the fixes hold 14/14, and a defect came BACK in a file written 3 hours after the fix

The §9.7 FULL cadence, due at **43 landings** since audit #1
(`git rev-list --count f66b1ad..HEAD`). Re-measured at `64ab535` in this
lane's durable clone (two items re-measured at `ad90bd2`, marked as such), fetch-rebased, `origin` verified as the real remote on
`master`. Docs and shell only, no Lean. Full detail:
[docs/duplication-audit.md](../duplication-audit.md) § *AUDIT #2*.

**Five of six items moved the right way, one did not move at all, and one
defect class came back.**

### The scoreboard

| | #1 | #2 |
| --- | --- | --- |
| private runner scripts | 6 (382 lines) | **1** (74 lines) |
| violations in them | 24 / 63 cells (**38%**) | 6 / 12 cells (**50%** density, **−18** absolute) |
| lanes on a shared runner | 0 | **6**, live |
| `--compare` that cannot fail | 3 of 14 | **1 of 16** |
| provenance stamps that swallow | 4 | **1** |
| durable amendments / in practice | 8 / 12 | **13 / 16** |
| backlog files / ratified ids | 1, colliding | **12**, 28 of 29 |

### Adoption is real, and it was measured live rather than claimed

At 23:03 `/tmp/ls-build.lock/owner` read `go 54886` — `tools/triad.sh`'s
exact A5 format — and `ps` resolves it to `bash tools/triad.sh --lane go
--classify` with one `lake` and one `lean` descending from it. All five
queued tickets resolve to the same script (`ada`, `basecase`, `wasm`, `es`,
and `pyc3a`, which arrived mid-measurement). **Six lanes on the shared
script; one (`leantier`) still private.** The three live checks — owner,
queue, concurrent builds by parentage — **passed**, where audit #1 caught
two builds running concurrently for 48 minutes.

### THE NEW FAILURE MODE: the shared script is being FORKED

Two copies in `/tmp` (454 and 502 lines) match **no committed version** of
`tools/triad.sh`. Of the non-comment lines each adds over the 381-line base,
only **11/66** and **23/111** are in today's repo script — four fifths of
two lanes' improvements are sitting in a purgeable directory. One of them is
load-bearing: `/tmp/my_triad.sh` carries a **measurement** (an honest `lean`
worker at 3251 MB, a build at 2846/3238/3117/2864 MB) concluding that A15's
3 GB line kills honest builds, and `tools/triad.sh:89` still uses 3 GB
summed over the chain. **`A14`, `A15` and `A16.1` appear in no durable
doc**; §7.1a ends at 13. The register was one amendment behind at audit #1,
was completed to thirteen, and is now **three** behind. The protocol moved
from prose into the script; the amendments are now moving from the script
into `/tmp`.

### The seven fixes: 14/14, re-run and not re-read

Zero commits touched the five files, but a fixed guard can regress, so all
fourteen checks were re-executed against fresh fixtures. All correct: the
three `--compare` modes exit 1 on drift and 0 on agreement; all four
provenance paths refuse with exit 2 on an unresolvable revision **and write
no artifact**.

### The defect that came back, and what it proves

`harness/wasm_sorry_census.py` landed at **20:44** — 2h39m after the fix —
and its `git_rev` is **byte-identical** to the function that fix deleted
from `wasm_spec_census.py`, its own lane's sibling. It stamps the null at
line 208 and its `--compare` returns 0 on drift at line 250. Seventeen
minutes later `harness/lean4lean_obligation_census.py` got **both** right.

> **Copy-paste propagates a defect FORWARD faster than a fix propagates
> SIDEWAYS.** Fixing seven implementations did not stop the eighth from
> being born with two of them, because the fix changed files and the defect
> lives in a habit.

Contract defects: **7 → 2**, both in one new file. Per §9.1, fix those two
(two lines) before any further consolidation; `censuskit.py` is correctly
**absent** and stays by-touch.

### New duplication measured

* **Two backlogs are live.** §9.5's migration says the monolith is renamed
  to an archive and `docs/backlog.md` becomes a generated index. Since v2
  landed, the monolith took **10** commits and the per-lane files **29**;
  the monolith grew to 21,797 lines and no index generator exists. The Go
  lane is the single id drifter (`## G1`). This entry is the audit lane
  moving first.
* **`RefusalCause` — measured at 4 spellings / 9 names, and then it
  RESOLVED ITSELF mid-audit.** `a7acd87` (arrived during the write-up)
  replaced the ES type with `inductive RefusalCause (π : Type)` — *"the
  family's four REFUSE classes — §5.2 — parameterized by a tier payload"* —
  with a per-tier instantiation and a `className` projection emitting
  exactly §5.2's four strings. **That is audit #1 §5's recommendation, and a
  lane reached it independently.** Residual: C's
  `valueUB`/`memUB`/`libc` and Ada's prose have not moved, so 9 names
  stands; but the family type now exists in code, so #3 measures uptake, not
  divergence. `libc` — the one name §5.2 calls wrong — is the last
  code-level obstacle.
* **`SemM` by shape: 13 sites, 5 spellings** — and **2 use `Except Loud`
  rather than `Halt`**, which §3.4 proves are not interchangeable. That part
  of the reconciliation bill is a semantics decision, not a rename. The Go
  lane declined to define its own and wrote the adoption note instead.

### The classifier's first hours

Landed 21:21, so this is hours and not a week. Every landing's diff
classified with the **shipped** `classify_path`, sourced out of
`tools/triad.sh`: since audit #1, **35 of 43 landings are docs-only** (7
tier, 1 spine); since `--classify` landed, **11 of 14** (3 tier, 0 spine).
Conservative, because the bare path rule can only be demoted by the
reachability probe, never promoted. The landings agree: 20 of 43 declare no
ticket or no tenure. **Roughly four in five landings owed no tenure**,
against a queue five deep.

### What audit #3 re-measures

The two `wasm_sorry_census.py` defects; whether the `triad.sh` forks came
home and A14-A16 reached §7.1a (fork count and register lag now replace the
private-script count as leading indicators); the dual-write count; the
`SemM` bill at the moment `Core.SemM` lands; and the three live checks every
keeper tick.
