# The PROOF-WRITER QoL lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by
the QoL lane.** Ids are `YYYY-MM-DD-qol-<n>` and need no reservation, because
the lane name makes them unique.

This lane writes **no Lean and runs none** (A11). Its subject is the cost a
proof writer pays between having an idea and having a green: the log they
cannot read, the statement shape they get wrong for the fourth time, the law
they cannot find, and the full build they did not owe. Everything here is
mined from the repository's own record — **every tool entry cites the
incident that minted it**, because a decoder that guesses is one more thing
to distrust.

---

## 2026-08-22-qol-1 — `tools/triad.sh --classify`: the triad now sizes itself to the diff, and SAYS WHAT ITS GREEN COVERS

Base rule 4 says *one triad per landing*. It does not say every landing owes
the same triad. A docs-only landing that pays for a full build pays a tenure
the machine does not owe it — and A11 makes tenures scarce on purpose, since
the lock covers **all** Lean execution and Thomas's own processes outrank
every lane.

But the reason this is a `--classify` flag on the canonical wrapper rather
than a lane's private shortcut is the other half: **a scoped green that does
not say what it covers is §5.4a's exact failure mode** — a number quoted
without the state it was taken in. So the classification is not only a
scope-picker; it prints the coverage statement next to the verdict, and the
triad repeats it at the end.

### The three classes, and where each boundary comes from

| class | what it is | build | tenure |
| --- | --- | --- | --- |
| `docs` | nothing in the diff can reach the elaborator | none | **no** |
| `tier` | `LeanModels/<tier>/` and its `Examples/` | scoped `lake build <modules>` | yes |
| `spine` | `LeanModels.lean`, `LeanModels/Core/`, the shared harness, the lakefile — **and anything unrecognized** | full | yes |

`docs` owes no tenure because `tools/docs_check.py` **shells out to nothing**
— checked, not assumed — so there is no Lean process for A11's lock to
cover. `harness/diff_test.py` runs `lake build` and `lake exe`, so any class
that runs it takes a tenure. That is the whole rule: the tenure follows the
Lean, not the file count.

`harness/diff_test.py` and `harness/cases.json` classify as **spine**, not as
tooling: they are the differential every tier is judged by. The other
`harness/*.py` are lane instruments — changing one invalidates no `olean`,
so they are `docs`, and a lane that wants its instrument exercised passes
`--gates`, which brings the tenure back.

### The direction of every doubt is fixed, and lean-tier paid for the rule

An unrecognized path **escalates and is named**. `docs/backlog/lean-tier.md`
§`2026-08-22-lean-tier-2` minted this the expensive way: a path-based
classifier filed all seven `TrProj.*` lemmas as *"other"* because they lived
in a generically-named file, and **the census's largest cluster went
invisible in its own summary.** A classifier that absorbs what it does not
recognize produces a confident wrong answer; this one prints
`UNKNOWN <path> <- no path rule matched; escalated, not absorbed`.

The same asymmetry decides the `Examples` module names. `Examples/system-verilog/toggle/proof.lean`
is really `Examples.«system-verilog».toggle.proof`, and the guillemets are
in the source imports — but whether that spelling survives the `lake build`
command line is something this script would have to **run Lean** to find out,
which A11 forbids. So a hyphenated example directory widens to the
`Examples` library target: less scope, **zero invention**.

### Never downgrade, stated as code

* the classification is a **floor**: `--gates` from the lane is appended to
  the floor, never substituted for it, and it re-arms the tenure even in the
  `docs` class;
* `BUILD_TARGETS` is only ever added to (`add_build_target` is a union), so
  a future `--build-target` flag composes with the classifier instead of
  fighting it;
* a `LeanModels/` path whose module name cannot be derived **escalates the
  whole landing to a full build** rather than silently building less;
* an **empty** diff is not a docs-only landing. It is a classification that
  measured nothing, and it says so and falls back to the full build — the
  silent-0-line-census law pointed at the classifier itself.

### The merge target carries its own provenance

The default base is `github/master`, falling back to `origin/master`, and
the chosen ref, its sha **and its remote URL** are printed. If that URL is a
local path or a bundle, the run prints the **A13 caveat** loudly: a seeded
clone inherits the peer's remotes, `origin` can be a stale local bundle from
2026-08-14, and `git rev-list HEAD..origin/master` reports `0` because it is
comparing against the bundle. Four lanes, one root cause (§7.1a). The run
also counts **unstaged `.lean` files it did not classify** and says so —
they are not in this green.

### Triad

`bash -n` clean. `--self-test`: **42 ok, 0 failed** (12 pre-existing queue
and lock checks unchanged, **30 new**), covering all three classes, both
mixed diffs (docs+tier → `tier`; docs+tier+spine → `spine`), two tiers in
one diff, the unrecognized path, the underivable module, the `input_dir`
file that is a real build input, the rootless tier (`Sv` has no
`LeanModels/Sv.lean`), and the never-downgrade rule. The four live classes
were exercised with `--classify-only`, which takes **no tenure and runs no
Lean**. **No Lean was executed by this lane at any point.**
