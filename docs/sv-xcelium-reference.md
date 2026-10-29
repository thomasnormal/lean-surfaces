# Xcelium is the reference, pinned as data

Rule (Thomas, 2026-10-29): **Xcelium is the reference simulator when building
ls-sv.** When the model and Xcelium differ, the model is suspect; Icarus,
Verilator and mox are witnesses. Xcelium is nevertheless not available
everywhere, so:

* nothing in CI, in the harness defaults, or in the svGolf checker may *require*
  Xcelium;
* every Xcelium result that the project relies on is captured as **pinned data**
  in the repo, keyed by a content hash of what was simulated, so anyone can
  compare the model against it without access.

The pinned data is `harness/sv/xcelium_golden.json`. This page says what is in
it, how to compare against it (no Xcelium needed), and how to refresh it.

## 1. What is pinned

For every simulated row of `harness/sv/cases2.json` (a row without a `refusal`
field; refusal rows run no simulator) the file holds one entry. Since round 6
(2026-10-29) it also keeps the entry of every row the model has since REFUSED
(`ArraySel:partial-overhang`, `PortConn:net-width`, `Select:wide-index`, ...) as
EVIDENCE: that is the Xcelium trace which motivated the refusal. `--golden`
reports simulated rows only, so an evidence entry is never compared; its hash
cannot be re-derived any more (the model that produced the testbench's port list
now refuses the design), and the entry is neither refreshed nor deleted.

| field | meaning |
|---|---|
| `hash` | sha256 over the canonical JSON of `{row, dut, tb, params, xrun_flags}`: the row name, the DUT source text, the generated testbench text, the row's parameter overrides, and the semantic xrun flags (`-sv -q -timescale 1ns/1ns`). Defined once, in `xcelium_golden.row_hash`. |
| `status` | `ok`; `xrun-compile-error` (Xcelium rejects the source); `runtime-error`; `timeout`; `no-testbench` (the model could not produce the port list the testbench needs, so no run was possible; `hash` is null). |
| `cycles` | the Xcelium trace: the `CYCLE <k> <name>=<bits> ...` lines from xrun's stdout, in order, exactly as `diff_test2.cycle_lines` extracts them. This is the thing the model is compared with. |
| `message` | failures only: the tool diagnostics (`*E`/`*F` lines) or the reason. |
| `warnings` | the `*W` diagnostic codes xrun printed (informational), when any. |

The top-level `simulator` object records the exact Xcelium version string
(`version_raw` is the line `refsim -version` printed), the host, and the
invocation. The file is serialized deterministically (rows sorted by name, one
cycle per line, no timestamps or timings), so a refresh produces a reviewable
diff.

**What a trace is.** The testbench (`harness/sv/gen_tb2.py`) drives the inputs
at times 3k, pulses the clock at 3k+1 / 3k+2, and samples every listed signal
in `always @(negedge clk)`, printing one `CYCLE` line per stimulus cycle. The
model produces the same lines from `run2` through `harness/sv/runner2.lean`.
The two are therefore directly comparable as lists of strings, which is exactly
what `diff_test2.py` has always done against Icarus.

**Time-zero races are recorded, not hidden.** A row whose result depends on
how a simulator orders time-zero events (a combinational block against the
testbench's first assignment) is pinned as Xcelium printed it, `x` and all.
That is one run of one scheduler; the pin says what Xcelium 24.03 did, not that
the standard forces it.

## 2. Comparing against the pin (no Xcelium needed)

`diff_test2.py` has an additive, default-off option:

```
python3 harness/sv/diff_test2.py --golden [PATH]            # all rows
python3 harness/sv/diff_test2.py --golden --case t2_sel_w8  # one row
python3 harness/sv/diff_test2.py --golden --golden-strict   # XREF-DIFF fails the run
python3 harness/sv/diff_test2.py --golden --sim xrun        # on a machine with no xrun: model vs pin only
```

After a row's normal checks it prints one status line:

| status | meaning |
|---|---|
| `XREF-MATCH` | the pinned hash matches the sources and the model trace (for an accepted schedule) equals the Xcelium trace. |
| `XREF-DECLARED` | hash matches, Xcelium `ok`, traces differ, and the row carries an `oracle_disagreement` declaration that names Xcelium (`"sim": "xcelium"`, round 6, [sv-oracle-disagreements.md](sv-oracle-disagreements.md)) whose recorded Xcelium trace is the pinned one and whose recorded model trace is the model's. Counted apart from `XREF-MATCH` and `XREF-DIFF`, never a match. A declared departure that is RESOLVED (the pin now equals the model) or CHANGED (either trace differs from the recorded one, or an input binding changed) is a hard failure of the run, as an Icarus declaration is. |
| `XREF-DIFF` | hash matches, Xcelium `ok`, traces differ: **the model is suspect.** The first differing lines are printed (`sim` is Xcelium). |
| `XREF-STALE` | the DUT, testbench or parameters changed since the pin. Nothing is claimed; refresh the pin. A warning, never a failure. |
| `XREF-NONE` | no usable Xcelium trace: the row is not pinned, or Xcelium itself could not take it (the pinned status and first message are shown). |

and a totals line. `XREF-DIFF` does not change the exit code unless
`--golden-strict` is given (`XREF-DECLARED` never does). On a stale or absent pin a declared
Xcelium departure cannot be re-checked against the pin; its input bindings (source, envelope,
case, testbench digests) still are, and a changed one fails the run. Without `--golden` the harness behaves exactly as
before (output and exit code unchanged; checked on a mixed 6-row subset).
Without any simulator on PATH, `--golden` still runs the model and compares it
to the pin; it needs only `lake`, never Xcelium.

## 3. Refreshing the pin

Needs: `lake` (the model side, to get each row's port list and model trace),
and `ssh vip-ng` (the Xcelium side). Two phases, so the slow Lean phase and the
Xcelium phase can overlap.

```
# Lean phase: per simulated row, run_lean (ports + model trace), the testbench, the hash.
# ~2 s per row when the Lean slot is free (428 rows: about 16 minutes). Resumable.
python3 harness/sv/xcelium_batch.py prepare --workdir $W [--lean-wrapper "$LEAN_SLOT"] [--case NAME ...]

# Xcelium phase: the rows that are not pinned / whose hash changed, batches of 40 per ssh session.
# 428 rows: about 20 minutes. Resumable; the golden file is rewritten atomically after every batch.
python3 harness/sv/xcelium_batch.py run --workdir $W [--follow] [--batch-size 40] [--retry-failed]

# Prove the pin reproduces: re-run a sample (default 10) and compare to the pinned traces.
python3 harness/sv/xcelium_batch.py verify --workdir $W --sample 10

# Counts: prepared / pinned by status / unpinned / stale.
python3 harness/sv/xcelium_batch.py status --workdir $W
```

`$W` is a scratch directory (prep files, the raw xrun output of every case under
`$W/raw/`, a per-case timing log); it is not committed. `$LEAN_SLOT` is whatever
wrapper your machine uses to serialize Lean jobs (on a memory-poor Mac, a slot
script that holds one Lean process machine-wide); it is prefixed to every `lake`
call. `--follow` lets `run` consume rows while a concurrent `prepare` is still
producing them.

Selection rules of `run`: a row is run when it has no pinned entry, or its hash
changed, or its status is `timeout`; `--retry-failed` also re-runs pinned
failures. If vip-ng's Xcelium version differs from the pinned one, `run` refuses
to mix versions and asks for `--rebase`, which re-runs every row and replaces the
pin. A refreshed file is then reviewed as a diff and committed by a person.

When a row's DUT, `gen_tb2.py` output or parameters change, its entry goes
`XREF-STALE` until the pin is refreshed for that row
(`prepare --case NAME` then `run --case NAME`).

## 4. The vip-ng procedure (and its etiquette)

Xcelium is run only on **vip-ng**, only through the fleet gate
`/var/tmp/thomas-ahle/fleet2/bin/refsim <xrun args>`. The gate sets the one
reachable license server (plain `xrun` hangs in `xmsim` and ends with `NOLICN`),
runs at low priority, caps memory at 10 GB and each run at 15 minutes wall.
Its slot count has been raised over time (the script in use when this was
written allowed 10 concurrent runs fleet-wide; it allowed 2 before): **this tool
runs exactly one refsim at a time**, whatever the gate allows, and each `xrun`
here takes about 2.3 s.

* `xcelium_batch.py run` works only in its own directory
  `/tmp/ta-xref/<label>/<batch id>/` on vip-ng (default label `ls-sv-golden`;
  `LS_SV_XCELIUM_REMOTE_ROOT` names another private root, e.g. `/tmp/ta-r6`),
  never in fleet directories, and removes each batch directory once its results
  are fetched.
* One ssh session handles a whole batch: the tool stages a tarball, starts a
  driver script *detached* (`nohup setsid`, guarded by `flock` so two drivers can
  never overlap), and polls with short ssh calls. A dropped connection loses
  nothing: ssh calls are retried with backoff, the driver keeps running, and
  re-running the same command re-attaches to the batch or re-fetches its results.
* Each case is its own `xrun` with its own `-xmlibdirname <case>/xcelium.d`
  (deleted after the case). The invocation is the one `diff_test2.run_xcelium`
  uses (`xrun -sv -q -timescale 1ns/1ns <dut.sv> tb.sv`) plus the library name.
* vip-ng is a shared machine running Thomas's agent fleet. Never build or write
  in fleet directories; never kill, pkill or killall anything except an exact PID
  you started yourself; do not run `find /` or other expensive scans.
* If vip-ng is unreachable for a long time, stop and report. compute-0
  (`ssh thomas-ahle@compute-0.hardware.normalcomputing.net`, with
  `/opt/cadence/installs/XCELIUM2609/tools/bin/64bit` first on PATH; its default
  24.03 `xrun` segfaults) is a fallback only if vip-ng is down. The tool targets
  the refsim gate on vip-ng, so using compute-0 means adapting the driver by
  hand; the version is then 26.09, and the whole pin has to be rebased and
  re-reviewed (`run` refuses to mix versions).

## 5. Pinned state

Captured 2026-10-29 on vip-ng:

* Xcelium **24.03-s004** (`refsim -version` prints `TOOL: xrun(64) 24.03-s004`);
  recorded in the file as `simulator.version` / `simulator.version_raw`.
* 428 rows pinned (every simulated row of the 626 in `cases2.json`; the other 198
  are loud-refusal rows), 3427 cycle lines. Status: 428 `ok`, 0 compile errors,
  0 runtime errors, 0 timeouts.
* Cost: `prepare` 16 minutes (426 rows prepared in one pass, 2 earlier), `run`
  19.4 minutes for 428 rows in 11 batches of at most 40 (xrun itself: 2.2 to 3.8 s
  per case, 2.35 s mean, about 16.7 minutes in total), `verify` 44 s for 10 rows.
* Against the model: 392 `XREF-MATCH`, 36 `XREF-DIFF`, 0 `XREF-STALE`, 0
  `XREF-NONE`, measured end to end by `python3 harness/sv/diff_test2.py --golden`
  over the whole corpus (626 rows, 24.6 minutes on a loaded Mac with Icarus as the
  only local simulator; normal totals unchanged: 383 verified, 24 skipped, 21
  declared disagreements, 23 unavailable backends, 198 loud refusals, exit 0).
  The 36 are classified in [sv-xcelium-audit.md](sv-xcelium-audit.md).
* Tests that need no simulator: `python3 harness/sv/test_xcelium_golden.py`
  (hash sensitivity, the four XREF statuses, the xrun output classifier, and the
  integrity of the committed pin).
* Later in round 6 (2026-10-29, lane B): the six admitted rows of the
  `always_comb` alias battery (`acg_alias_wr`, `acg_alias_copy`,
  `acg_alias_far`, `acg_alias_bits_ok`, `acg_alias_port_wr`,
  `acg_alias_hier_ok`) were pinned with `xcelium_batch.py prepare/run --case …`
  into a scratch copy of the golden file (own directory `/tmp/ta-r6/` on vip-ng)
  and merged: 465 entries, every one of the 422 simulated rows of the 676 in
  `cases2.json` pinned, the other 43 entries kept as evidence for rows that became
  loud-refusal rows (`acg_alias_assign` and `acg_alias_port` among them). The six
  are `XREF-MATCH`.
* Lane A repair (2026-10-29, after verification): the four admitted rows of the repair fixtures
  (`net_width_outvar`, `net_width_outvar1`, `wide_index_dead_n4`, `wide_index_dead_n40`) were
  pinned with `xcelium_batch.py prepare/run --case …` into a scratch copy of the golden file
  (`LS_SV_XCELIUM_REMOTE_ROOT=/tmp/ta-r6`, label `repair-lanea`) and merged: 469 entries, every
  new row `ok` and `XREF-MATCH`. The four new REFUSAL rows (`net_width_outwire`,
  `net_width_outwire1`, `wide_index_dead_n40_live`, `wide_index_wr`) are not pinned: their Xcelium
  traces, run by hand on vip-ng through the gate with the same generated testbench, are quoted in
  each row's `measured` field.
* **Round 6 (2026-10-29), the pin after the Xcelium-driven refusals**: 465 entries, all `ok`,
  3693 cycle lines, same Xcelium 24.03-s004 and same default flags. 422 are the simulated rows of
  the 676 rows of `cases2.json` (the other 254 are loud-refusal rows); 43 are EVIDENCE entries of
  rows the round turned into refusal rows (41 by the part-select, net-width and wide-index
  refusals, 2 by the alias guard), kept because they are the Xcelium traces that motivated the
  refusals and are neither compared nor refreshed (`--golden` reports simulated rows only). The
  rows added by the round (the split fixtures, the controls and the admitted counterparts) were
  pinned in `/tmp/ta-r6/<label>/` on vip-ng (`LS_SV_XCELIUM_REMOTE_ROOT`), and the five rows on
  the DUTs whose header comments were corrected (`array_oob`, `array_oob_lsbwrite`,
  `array_oob_lsbwrite_l1`, `dyn32`, `dyn32_part`) were re-run: the traces are identical and
  only the hash keys moved. The six `partsel_dyn*`/`dyn32_part` rows that carry an Xcelium
  declaration report `XREF-DECLARED`; `dyn32` stays an undeclared `XREF-DIFF` (audit 6.4, item 1).

## 6. Flags and diagnostics that change or explain the answer

The pin uses Xcelium's DEFAULT flags: `-sv -q -timescale 1ns/1ns` (`xcelium_golden.XRUN_FLAGS`).
That is a decision, not an accident (lead, 2026-10-29, round 6), recorded here together with the
option it declines. Everything below was measured on Xcelium 24.03-s004 by the audit's verifiers
(docs/sv-xcelium-audit.md, clusters P1 to P3 and DX1); no 26.09 run was made.

**`-ii_val` is NOT used.** `xrun -helpall` labels it "Correct value for vector part-selects", so
Cadence itself treats the default part-select value as the non-correct one. At the default,
Xcelium treats a part-select that is only PARTLY in range as wholly invalid: a read returns all x
and a write is dropped (one rule for reads and writes, constant and run-time bases alike; see
the audit's section 6). What `-ii_val` does about it is partial and depends on the context:

| construct (partly out-of-range part-select) | default | with `-ii_val` |
|---|---|---|
| read, base is a locally declared variable (constant base, run-time base, local 2-state variable) | all x (all 0 for a 2-state source) | the LRM value: in-range bits kept, x for the out-of-range ones |
| read inside a testbench task, a function or an `initial` block | all x | the LRM value |
| read, base is a port, a net, a run-time port base; module-level `assign`, `always_comb`, `always @*`, `always_ff`, `?:`, an expression | all x | **still all x** |
| read of an inner dimension of a packed array | all x | **still all x** |
| write (procedural or non-blocking, any base) | dropped whole | **still dropped** (only the IIWOOB / IIRAOB warnings are added; every row and signal of a 14-vector probe was identical to the default run) |

So the flag does not give the LRM behaviour for the constructs the model cares about (module-level
reads and every write), and it changes what the SAME select returns depending on where it is written.
The pin therefore stays on the default flags, which is what any harness without special knowledge
runs. Changing the flags is a deliberate re-pin: `XRUN_FLAGS` is part of every row hash
(`row_hash`), so every one of the pinned entries goes `XREF-STALE` at once and the whole pin has to
be taken again (`xcelium_batch.py run` over all rows, about 20 minutes on vip-ng, then the audit and
every `XREF-*` number is re-derived); and no single pin would show the LRM behaviour, only an
inconsistent mixture of it. If a future decision needs the repaired reads, the right shape is a
SEPARATE pin file (the tool refuses to mix versions or flag sets inside one file), compared with
the model's refusals row by row, not a replacement of this one.

**Diagnostics the audit relied on** (codes as `xmelab` / `xmsim` print them; default severity unless noted):

| code | meaning | where it matters |
|---|---|---|
| `BNDWRN` (warning) | a bit-select or part-select index is out of the declared bounds at elaboration. `xmhelp xmelab BNDWRN`: "An assignment will have no effect and the value of a reference will be X" (LRM 11.5.1) | P1 / P3 / DX1: it accompanies every constant-base case; it is NOT a complete predictor (a run-time base raises nothing by default, `dyn32`) |
| `BNDPERR`, `BNDIPERR` (ERROR) | an overhanging part-select (`BNDPERR`) or indexed part-select (`BNDIPERR`) used as a continuous-assign net target or as a module port-connection actual: the design does not elaborate. Procedural writes only warn `BNDWRN` and drop the write | P3 / DX1: for these shapes the reference rejects the design, so a loud refusal is the only reference-consistent answer. The message prints the evaluated range, e.g. `[8:7]` for `u[8 -: 2]` over `[7:7]` (DX2) |
| `IIFAOB`, `IIRAOB` (warning, only under `-ii_warn -ii_rwarn`) | "Accessing out-of-bound index (N)" at run time, on exactly the partly-out and fully-out accesses and on none of the in-range ones | P2: off by default, which is why a run-time-base overhang is silent at default flags |
| `IIWOOB` (warning, only under `-ii_wwarn`) | the write twin | P3 |
| `CUVMPW` | "port sizes differ in port connection" | H1: it fires on every width-mismatched connection and does NOT discriminate the one that leaves the high bits z |
| `BIGWBS`, `BIGWPL`, `BIGWIX` | the index of a bit-select / the base of a part-select / the index of an unpacked-array element is wider than 32 bits and is truncated to its low 32 bits; fires on the self-determined WIDTH (not for exactly 32 bits, also for a constant) | T1 |

## 7. Files

| file | role |
|---|---|
| `harness/sv/xcelium_golden.json` | the pinned data |
| `harness/sv/xcelium_golden.py` | stdlib-only: the golden format, `row_hash`, the `--golden` comparison; imported by `diff_test2.py` |
| `harness/sv/xcelium_batch.py` | `prepare` / `run` / `verify` / `status`: the only code that talks to Xcelium |
| `harness/sv/diff_test2.py` | `--golden [PATH]`, `--golden-strict` (additive, default off) |
| `harness/sv/xcelium_compare.py` | the three-way audit (model, pinned Xcelium, local Icarus): classes, equivalence layers, declaration verdicts, clusters; needs `iverilog` only (docs/sv-xcelium-audit.md) |
| `harness/sv/test_xcelium_compare.py` | its offline unit tests |
| `harness/sv/oracle_disagreements.py` | the declaration checker; since round 6 a declaration may name Xcelium (`"sim": "xcelium"`), checked against a live `xrun` run or, through `golden_disagreement`, against the pin (`XREF-DECLARED`) |
| `harness/sv/declare_disagreement.py` | writes an `oracle_disagreement` block from a row's current inputs and the pinned (or a fresh Icarus) trace; the digest recipe is the checker's own |
| `harness/sv/test_oracle_disagreements.py` | the checker's, the Xcelium declarations' and the writer's offline tests |
