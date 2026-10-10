# C++ capture literals: resource pricing

Measured **2026-10-10**, against the unchanged capture loader at `752e733`.
This prices the literal-ingestion boundary in [capture provenance](cpp-provenance.md),
not C++ semantics. The original registered TinyXML2 and nlohmann/json
translation-unit/profile bundles are used whole; read-only Mox still has no
published successful receipt. This is not a repository-wide census.

## Inputs and measurement boundary

The archived probes contain **32,723,259 bytes** for XML and **1,835,697,710
bytes** for JSON. Capture and probe digests are checked before and after the
experiments, as are the loader, receipt validator, strict parser, evidence
embedding and raw AST sources. The production loader SHA-256 is
`23a707859b50031a483a32c9b1d1d5ee5cf8dae74e66969f57f791d8b50bfc85`.
Neither input is trimmed, deduplicated, regenerated under a cheaper profile,
or replaced by a small fixture.

Lean is pinned to `leanprover/lean4:v4.33.0-rc1`. Each full-artifact attempt
uses `-j1`, a **180-second wall cap**, and an inherited **8 GiB per-process
address-space limit** with `-M8192`, except the explicitly named 16 GiB JSON
sensitivity control. Limits are applied by `/usr/bin/prlimit`, not a threaded
Python `preexec_fn`. Address space is not resident memory or an aggregate
process-tree budget. Larger caller budgets are experiments, not new defaults
or admission rules.

An external copy of `CaptureLoad.lean` adds monotonic phase markers, splits
`parseDeclarationProbeString` into its exact existing parser/validator
composition, and names the `Lean.toExpr` result before the existing
`addAndCompile`. It keeps every payload check and raw observation. A second
external copy appends and flushes markers to a file: Lean redirects ordinary
elaboration output, and an OOM can lose buffered markers. No instrumentation,
cache, new fast path or altered budget is added to the production loader.

RSS from `wait4` is the completed controller child's measured high-water
mark, including descendants it reaped. Killing the whole process group can
prevent that accounting from incorporating Lean: timeout rows instead name
a separately sampled Lean high-water lower bound. The corrected sampler
unions **all** `/proc/PID/task/TID/children` files. The initial leader-only
sampler saw Lake but missed its worker-spawned Lean process; its sample files
are retained as defective instrumentation, not Lean memory measurements.

## Default and finite-budget outcomes

| Whole XML attempt | Seconds | Measured RSS, KiB | Outcome |
| --- | ---: | ---: | --- |
| Original public loader | 39.510 | 2,808,412 | LCNF 200,000-heartbeat refusal |
| Instrumented, original defaults | 39.112 | 2,808,344 | Same LCNF refusal |
| Instrumented, `Elab.async false` | 40.430 | 2,754,248 | Same LCNF refusal |
| Heartbeats 2,000,000 | 41.519 | 2,811,920 | Recursion-depth refusal |
| Heartbeats 2,000,000, depth 4,096, synchronous checking | 42.324 | 2,755,136 | Recursion-depth refusal |
| `compiler.extract_closed false`, synchronous checking | 39.917 | 2,758,920 | LCNF 200,000-heartbeat refusal |
| Experimental kernel-only registration, synchronous checking | 28.678 | 1,870,576 | Kernel literal and two `rfl` witnesses pass; executable compilation not requested |

The closed-extraction control still reaches the same first compiler error;
downstream fixture elaboration after that error is not validation. Heartbeats
are not seconds, and the command's limit must not be attributed exclusively
to the final compiler phase. The tenfold heartbeat control merely exposes
another limit; it does not establish that unbounded compilation would finish.

The public JSON loader refuses with internal OOM at **27.183 seconds /
3,376,008 KiB**; its buffered instrumented 8 GiB control does likewise at
**24.475 seconds / 3,376,928 KiB**. No full public-loader compilation completes
for either original artifact in these default or finite-budget controls.
Printed `#check` output or a later command's sentinel is explicitly
insufficient: Lean can continue elaborating after the loader reports an
error, and complete process failure remains failure.

## Phase localization and controls

XML completes payload binding, UTF-8 decoding, strict raw parsing, full typed
validation and conversion to a literal expression before its compiler
refusal. In the ordinary asynchronous configuration, an
`add-and-compile-end` marker can appear **before** the eventual error; it
records API return, not completed compilation. The synchronous control has
no such completion marker. Compilation success always requires the entire
Lean process to finish successfully.

The corrected thread-aware XML repeat measures **6.539 seconds** for strict
raw parsing, **0.767 seconds** for typed validation and **0.426 seconds** for
`ToExpr`. Its sampled peak `VmRSS` is **2,817,620 KiB**, whereas its completed
`wait4` receipt records **2,800,400 KiB**; the discrepancy is retained, not
silently reconciled. These unreplicated phase timings identify work to price,
not an allocation breakdown or an optimization speedup.

The flushed JSON trace under 8 GiB reaches `probe-utf8-start` without
`probe-utf8-end`; no raw-parse marker is reached. Under 16 GiB it completes
UTF-8 decoding and enters strict raw parsing, but does not finish that phase
within the wall cap. This localizes two different resource barriers; it does
not blame XML's LCNF compiler for JSON's default failure, infer a fixed
allocation multiplier, or establish that parsed JSON would fit in memory.

| Flushed JSON trace, corrected sampler | Seconds | Sampled Lean high-water, KiB | Outcome |
| --- | ---: | ---: | --- |
| 8 GiB, otherwise original defaults | 23.700 | 3,336,040 | OOM between UTF-8 markers; exit 1 |
| 16 GiB sensitivity | 180.537 | 6,797,424 | Raw-parse wall timeout; exit -9 |

The 16 GiB trace completes UTF-8 decoding in **3.841 seconds**. Its timeout
controller's own `wait4` value, **836,328 KiB**, omits the killed Lean child's
peak and must not replace the sampled figure. Sampling has a nominal
0.1-second interval; the controller's reported elapsed time includes polling
and final process-group termination, not an exactly 180-second completed
parse. Neither trace reaches typed validation or literal compilation.

Import-only controls pass at **17.652 seconds / 1,581,300 KiB** for the public
loader and **17.652 seconds / 1,577,448 KiB** for the durable instrument module.
The actual eight-row module bundle passes the same two guards under both
original and ordinary instrumented loading: **19.263 seconds / 1,635,620
KiB**, and **21.167 seconds / 1,638,860 KiB**, respectively. The durable-marker
control also passes at **17.550 seconds / 1,648,456 KiB**. These controls rule
out an unconditionally failing instrument; their wall-time differences are
not isolated marker overhead or throughput estimates. Runs share a host and
have import, filesystem and scheduling effects.

Kernel-only XML registration uses the identical safe literal expression with
`Lean.addDecl` and `Elab.async false`; receipt schema and AST-root witnesses
close by `rfl`. This demonstrates kernel feasibility for the unchanged XML
literal, **not** success of `load_cpp_capture`'s executable compilation.
It omits LCNF/IR/code generation, does not register postponed compilation,
and does not establish general `#eval` or downstream executable availability.
`enableRealizationsForConst` is not a substitute for generated code. The
experimental alternative therefore remains outside production.

## Representation cost and next decision

A separately bounded streaming lexical/structural pass measures JSON's
original value spans without loading it into Python memory:

| Span, including internal whitespace | Bytes | Share of entire probe |
| --- | ---: | ---: |
| Raw AST value | 1,722,577,981 | 93.83778% |
| Metadata value | 113,119,708 | 6.16222% |
| Of metadata: declaration-array value | 113,119,460 | Included above |
| Remaining metadata | 248 | Included above |
| Outer framing | 21 | Remainder |

The pass uses a 64 KiB buffer and a 128 MiB address-space bound, completing
in **2.503 seconds / 17,408 KiB**. These are byte spans, not semantic node or
declaration counts. Dropping the AST would remove most bytes but violate the
literal-observation contract; it is not an optimization of the same input.

The embedding retains raw metadata and typed declaration rows, including
each `row.raw`. Derived `ToExpr` also emits list/pair scaffolding and typed
fields; it is not a general serializer that preserves heap sharing.
Parser and validator temporaries add costs, but no fixed memory multiplier
or complete allocation breakdown is measured here. Strings use literal
strings rather than an inferred character-list expansion.

**Decision:** keep public loading unchanged. Price general literal
organization/compiler work for XML and bounded decoding/parsing for JSON
separately before implementation. Preserve strict validation, complete raw
observations, same-byte payload binding and future executable availability;
do not use corpus-specific budgets, pruning, kernel-only success or a cached
result to claim completed public ingestion. Input-world/source-form closure,
tooling query eligibility, entity/type/template/linkage, graph consensus,
cross-TU/ODR and ISO admission remain separate barriers. C++ semantic and
runtime admissions stay **zero**.

## Whole XML component pricing

A follow-up on 2026-10-10 prices the original XML capture's component
literals before choosing an organization change. An external command calls
the unchanged `readDeclarationCapture` first: **every** run reads and validates
the complete receipt, bound payloads and probe. It then gives just the selected
projection, or the complete capture, to the same safe `addAndCompile` path.
The component runs are not reduced-input ingestion. Production loading is
unchanged, and no complete reconstruction from component constants is tested.

Each run uses Lean 4.33.0-rc1, `-j1 -M8192`, an inherited **8 GiB per-process
address-space limit**, a **180-second** wall bound and the original elaboration
and compiler defaults. Durable flushed markers record read, `ToExpr` and
add/compile API boundaries. Successful rows require the entire Lean process
to exit zero and a `#eval` sentinel to equal an independently inventoried
root or count, not just an API-return marker. RSS below is the completed
controller child's `wait4` high-water measurement; no run hits the wall bound.

| Selected literal | Seconds | Measured RSS, KiB | Outcome |
| --- | ---: | ---: | --- |
| Raw AST | 53.486 | 2,595,848 | Recursion-depth refusal at add/compile command |
| Raw metadata | 37.628 | 1,875,552 | Recursion-depth refusal at add/compile command |
| Typed declaration rows, retaining each `row.raw` | 44.628 | 1,889,136 | Recursion-depth refusal at add/compile command |
| Complete probe | 56.386 | 2,803,168 | LCNF 200,000-heartbeat refusal |
| Complete receipt, without probe | 25.716 | 1,742,320 | PASS; compiled payload count is 14 |
| Complete capture | 52.263 | 2,846,076 | LCNF 200,000-heartbeat refusal |
| Complete capture, no evaluation sentinel | 45.496 | 2,759,072 | Same LCNF refusal |

The no-evaluation control confirms that full-capture refusal is not introduced
solely by the sentinel. The recursion-depth messages do not identify a specific
compiler subphase; they must not be reported as measured LCNF failures.
Failed literals also produce noncomputable-dependency diagnostics at their
evaluation commands. Later elaboration does not repair the failed process.
These are bounded single samples, including imports, complete reading and
validation, expression construction and compilation/evaluation. Controls and
other lanes share the host; neither time subtraction nor an isolated compiler
speedup is justified.

An import-only evaluation control passes in **17.243 seconds / 1,581,248
KiB**. The real eight-row module capture passes both its `rfl` length witness
and compiled length evaluation in **23.390 seconds / 1,641,692 KiB**. Together
with the receipt projection, these rule out an unconditionally failing
instrument. They establish executable availability only in those Lean
processes, not downstream compiled-artifact import or complete-capture equality.

The unchanged XML probe is **32,723,259 bytes**: original AST value span
**29,223,730**, metadata **3,499,508**, of which the declaration array is
**3,499,260**, remaining metadata **248**, and outer framing **21**. Independent
compact Python UTF-8 serialization measures AST **10,194,322 bytes**, metadata
**3,499,508** and receipt **186,374**; these are not Lean expression, heap or
compiler sizes and are not replacement artifacts. There are **4,527** metadata
rows. The AST's **160** immediate children are uneven: the largest two compact
subtrees are **4,245,430** and **2,764,067** bytes. Its maximum raw JSON depth
of **61** does not bound the depth of Lean's inductive list scaffolding.
Bundle bytes, all 104 recorded positive-input pins and all six production
loader/parser/representation pins remain unchanged. Present-byte agreement
still does not establish input-world closure.

**Decision:** mere separation into whole AST/metadata/row fields does not
complete this bounded experiment: each large component already refuses.
Price a general, size-bounded structural literal organization and **complete
assembly** next, without pruning observations, replacing original artifacts,
adding an unprofiled cache or granting source-specific budgets. Component
failure is not a universal compiler impossibility, and the receipt-only success
is not completed public capture ingestion. Original full-compilation successes
remain **zero**; JSON parsing and every previously named ISO, identity and
execution barrier remain separate. C++ semantic and runtime admissions remain
**zero**.

## Generic closed-literal factoring

A second follow-up on 2026-10-10 tests structural organization without changing
production loading. Its external command first reads and validates the **complete**
original capture with `readDeclarationCapture`, then traverses every occurrence
in `Lean.toExpr capture` using an iterative postorder worklist. This constructor-built
capture term uses application, constant and literal nodes; other expression nodes
refuse. No observation, duplicate `row.raw`, string, declaration or receipt field
is pruned, and no deduplication or result cache is introduced.

Each reconstructed application counts its residual expression nodes. At a uniform
threshold `b`, it becomes a fresh **safe, kernel-unfoldable definition** marked
compiler `noinline` **before** normal `addAndCompile`. The replacement reference
counts as one node. Partial constructor applications are allowed: their inferred
type can be a function type, and safe declaration insertion still performs the
kernel check. Thus helper bodies have at most **`2b - 1` nodes**, not `b`, and the
residual root has fewer than `b`. This bounds expression scaffolding, **not string
byte size**, unfolded helper depth, environment size or total compilation work.
Thresholds 16, 256 and 4096 are generic organization controls, not per-source
resource exemptions. Invalid thresholds below two refuse before reading.

All measurements retain Lean 4.33.0-rc1, `-j1 -M8192`, the **8 GiB per-process**
address-space cap, **180-second** wall bound and default recursion/heartbeat
limits. Compilation is synchronous; errors propagate rather than being suppressed.
Durable markers distinguish every helper attempt/API return, assembly, root
compilation and complete-value evaluation. A positive native control requires
exit zero, the expected counts and `Meta.evalExpr DeclarationCapture` followed by
derived `BEq` against the **entire original parsed capture**. This executable
equality is not a kernel theorem or a downstream compiled-import test.

| Original capture / threshold | Seconds | Measured RSS, KiB | Outcome |
| --- | ---: | ---: | --- |
| Eight-row module / 16, native control | 25.016 | 1,918,192 | PASS; complete-value equality, counts 8 / 14 |
| Eight-row module / 256, native control | 20.885 | 1,697,956 | PASS; complete-value equality, counts 8 / 14 and count/root `rfl` witnesses |
| Eight-row module / 4096, native control | 19.260 | 1,655,332 | PASS; complete-value equality, counts 8 / 14 |
| Whole XML / 256 | 40.052 | 2,665,276 | LCNF compiler 200,000-heartbeat refusal; no complete assembly |
| Whole XML / 4096 | 40.221 | 2,735,804 | LCNF check 200,000-heartbeat refusal; no complete assembly |

RSS is completed controller-child `wait4` accounting. The separate 0.1-second
thread-aware descendant samples record Lean high-water observations of **2,676,460**
and **2,745,476 KiB** for the XML rows; they are not substituted for the controller
figures. No measured row reaches the wall bound. Times include imports, complete
reading/validation, expression construction, helper organization/compilation and
the observations actually reached. They are single shared-host samples, not an
isolated compiler speedup comparison.

The small capture's original expression has **91,025 occurrence-nodes** at all
three thresholds. Threshold 16 produces **5,156 helpers**, maximum body **31**,
residual root **5**; threshold 256 produces **319**, maximum **461**, root **1**;
threshold 4096 produces **20**, maximum **6,299**, root **2,489**. The XML/256
run records **2,866** helper API returns before its next attempt, zero-based index
2,866 with **401 nodes**, refuses. XML/4096 records **298** returns before index
298 with **7,801 nodes** refuses. Neither reaches root compilation or full-value
equality. These are not counts of a completely organized XML expression.

This instrument adds all helpers in one command's `CoreM` context: its synchronous
compiler path does not give each helper a fresh heartbeat origin. No heartbeat
reset or limit increase is used. Consequently the refusal is **not evidence that
the final bounded helper alone independently consumes 200,000 heartbeats**. It
prices the whole single-command procedure under the unchanged default budget.

Kernel preservation is measured separately, without deleting a failed witness or
raising recursion limits. The original eight-row complete-capture `rfl` comparison
fails at the default recursion depth for thresholds 16 and 256, **after** native
equality passes: process exit one, **27.942 seconds / 1,960,680 KiB** and **21.695
seconds / 1,716,348 KiB** respectively. Those kernel-inclusive runs are not counted
as successful ingestion. At threshold 4096, the unchanged whole-capture equality
statement **does close by `rfl`**, along with counts/root witnesses and native
equality: exit zero, **22.488 seconds / 1,675,356 KiB**. A generic 201-node synthetic
constructor control also passes full `rfl` equality and executable equality at
16/256, covering duplicate strings, empty/singleton lists, mixed alternatives and
Unicode/control bytes. Separate zero-budget, free-variable and loose-bound-variable
controls fail with the intended diagnostics. Named synthetic preservation
witnesses also report **no axioms**.

**Decision:** bounded helper bodies preserve complete small captures but do not
complete original XML assembly in this experiment. Next price ordinary separate
helper elaboration/compilation contexts and complete reconstruction, rather than
raising a single command's budget, pruning observations or introducing a cache.
Keep whole-value native equality, kernel equality and downstream artifact use as
separate measurements. Production loader/parser/embedding pins, both original
21-file bundles, all 14 payload bindings per bundle, and all **9 / 112** recorded
source pins remain unchanged before/after, with no unavailable/drifted pins. This
does not establish input-world closure. Original XML full-compilation successes,
production public-loader organization changes and C++ semantic/runtime admissions
remain **zero**; every ISO, identity, cross-TU/ODR and execution barrier remains.

## Fresh helper compiler contexts

The next **2026-10-10** experiment keeps the complete original captures and the
same uniform **256 / 4096** factoring thresholds, but moves the occurrence-wise
postorder traversal into `CommandElabM`. Each helper obtains its own ordinary
`liftTermElabM` context. Lean's `Command.runCore` supplies a fresh initial
heartbeat count at that boundary; neither an explicit reset nor a changed
heartbeat option is used. Independent context controls and per-helper
origin/current markers verify this distinction from the previous single lift.
It is not `elabCommandTopLevel` itself that supplies the new Core baseline.

Helpers remain safe, kernel-unfoldable `.regular 0` definitions, with compiler
`noinline` registered before ordinary `addAndCompile`, error propagation enabled
and noncomputability checked. Root compilation and whole-original-capture native
equality are required after complete assembly. The production loader is unchanged;
there is no pruning, deduplication, source-specific allowance or cache.

Both original-full XML runs retain **8 GiB address space per process**, Lean
**`-j1 -M8192`**, **180 seconds** and default heartbeat/recursion limits:

| Threshold | Result | Seconds | Controller-child wait4 RSS KiB | Sampled Lean HWM KiB | Prior helper API returns |
| --- | --- | --- | --- | --- | --- |
| 256 | FAIL: internal allocation panic | 63.672 | 4,279,764 | 4,292,104 | 8,204 |
| 4096 | FAIL: internal allocation panic | 58.826 | 4,217,116 | 4,225,052 | 811 |

Both stderr logs report `INTERNAL PANIC: out of memory`. Threshold 256 fails
during zero-based helper attempt **8,204**, body **269 nodes**; threshold 4096
during attempt **811**, body **4,461 nodes**. Neither reaches complete assembly,
root compilation or whole-value equality. Neither times out or reports the prior
aggregate heartbeat refusal. A returned helper prefix is not complete ingestion,
and these shared-host end-to-end samples do not isolate the last helper's cost.

Peak sampled Lean virtual size is **8,369,860 KiB** in both runs, near the
**8,388,608 KiB** address-space cap. This is **not 8 GiB RSS**. The panic does not
identify a compiler subphase, retained object or allocator cause; it establishes
a bounded allocation failure, not a universal impossibility of compiling the
capture. Fresh contexts move this experiment past the previous heartbeat wall
without establishing a complete executable XML capture.

### Complete producer-only census

A separate bounded producer emits every helper, the root and the complete-value
verification command using a flat postfix JSON expression codec. Both producers
exit zero with `plan-complete` and `source-complete`. **Neither generated file is
compiled or evaluated.** They measure complete organization, not ingestion:

| Threshold | Original nodes | Helpers | Maximum body | Root nodes | Generated bytes | Producer seconds | Sampled Lean HWM KiB |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 256 | 14,400,775 | 47,702 | 507 | 143 | 420,870,076 | 76.440 | 1,919,568 |
| 4096 | 14,400,775 | 2,992 | 8,113 | 3,251 | 416,189,542 | 82.085 | 1,920,000 |

Independent streaming audits verify ordered prior-only references, exactly one
use of every helper, body/root bounds, codec shapes and expanded occurrence-node
conservation. Both plans retain **14,008,508 UTF-8 string-literal bytes**,
**6,085,747 nonhelper constant occurrences** and **30 distinct nonhelper names**,
with agreeing universe inventories. Appended **4,527-row / 14-payload** controls
remain uncompiled. Producer and compiler receipts are separate per-process
experiments; two 180-second subprocess allowances would not be one unchanged
180-second end-to-end pipeline bound.

### Preservation controls and decision

Independent fresh-context runs on the complete original eight-row capture pass
native whole-value equality and **8 / 14** count witnesses. Threshold 256 passes
in **21.781 seconds / 1,690,780 KiB** controller-child wait4 RSS; threshold 4096
in **22.794 seconds / 1,671,232 KiB**. The same **91,025** occurrence-nodes produce
**319 / 20** helpers and maximum bodies **461 / 6,299**. At 4096, the unchanged
whole-capture kernel `rfl` theorem also passes and reports **no axioms**. No
whole-capture kernel equality is claimed at 256; the previous default
recursion-depth refusal remains recorded.

Codec controls found an auxiliary representation bug: `mkNatLit` reconstructs
an `OfNat.ofNat` application rather than the original raw Nat literal. The
external decoder now uses `mkRawNatLit`; exact structural, native/kernel
preservation and negative-codec controls pass after this correction. The primary
scoped experiment bypasses decoding, and the complete census only encodes, so
neither measured outcome is changed. Their original instrument source/module
hashes are preserved as **v1**; corrected codec controls carry **v2** pins.
Independent Lean string-parser/codepoint observations also preserve all **11**
fixtures, including Unicode, controls, duplicates and source-looking text.
Setup/logging failures and the original failing Nat diagnostic remain receipts,
not passing controls.

An independent receipt/source/pin audit passes for both full and both small
scoped compiler runs and both complete plans, including the archived v1 binding,
fresh context markers, resource limits and conservation checks.

**Decision:** profile compiler/environment memory retention under the unchanged
caps before selecting an optimization. Do not infer a cache, larger allowance or
opaque fallback from the allocation panic. Both original bundles remain **21
files / 14 payload bindings** each; all **9 / 112** recorded source pins and
**six** production pins match before/after, with no unavailable/drifted input.
This is not input-world closure. Production organization changes, original XML
full-compilation successes and C++ semantic/runtime admissions remain **zero**;
all ISO, identity, cross-TU/ODR and execution barriers remain.

## Compiler and environment memory profile

The next **2026-10-10** item observes the same complete reconstruction, with
unchanged **8 GiB per-process address space / 180 seconds / `-j1 -M8192`** and
default heartbeat/recursion bounds. An external diagnostic dynlib samples the
installed allocator, `/proc/self/status`, `smaps_rollup` and mappings at input
construction boundaries and every **128 helpers**, uniformly at both thresholds.
Sampled helpers additionally bracket inference, ordinary `addAndCompile` and
realization registration. The operation order, safe `.regular 0` definitions,
`noinline` and final whole-original-capture equality requirement are unchanged.
No collection, stats reset, allocator-policy change, cache or optimization is
introduced. The observer consumes time, allocations and potentially heartbeats;
these instrumented processes are not replacements for the preceding prices.

| Threshold | Result | Seconds | Controller-child wait4 RSS KiB | Sampled Lean HWM KiB | Prior helper returns | Complete snapshots |
| --- | --- | --- | --- | --- | --- | --- |
| 256 | FAIL: internal allocation panic | 87.313 | 4,253,608 | 4,265,216 | 8,034 | 381 |
| 4096 | FAIL: internal allocation panic | 67.856 | 4,218,616 | 4,234,504 | 811 | 45 |

Neither run assembles the root, compiles it or reaches full equality; neither
times out or reports a heartbeat refusal. The failing attempts are zero-based
**8,034 / 811**, bodies **353 / 4,461 nodes**. Instrumentation moves the 256
prefix relative to the earlier 8,204-return observation; do not infer an isolated
performance change. Sampled/final-error virtual sizes **8,372,740 / 8,372,732 KiB**
approach the **8,388,608 KiB** cap, still distinct from approximately 4 GiB RSS.

### Occupancy, mappings and retained roots

The native visitor measures **calling-thread default-heap allocated size-class
slots**, summing `area.used * area.block_size`; it is not logical payload size,
unique reachable Lean bytes, all heaps or RSS. Independent known-buffer and
explicit `IO.Ref` lifetime controls validate growth and release in this inventory.
At 4096, occupied slot bytes progress **90,664,272 → 192,928,560 → 395,947,424**
through read-start, read-complete and `toExpr`-complete, then **2,585,941,552** after
sampled helper 768. At 256 the corresponding last sampled helper 7,936 records
**2,769,406,288** bytes. These are sustained occupancy trajectories, not a
proven allocation-provenance or retaining-object attribution.

The `.olean` VMA footprint remains exactly **1,668,612,096 bytes** at both
thresholds; mapping growth is anonymous. Before the 4096 input read, **1,482,412
KiB** of **1,592,480 KiB** RSS is already file-backed. This separates an imported
baseline from subsequent anonymous growth. Mapping spans match process `VmSize`
after excluding the kernel `[vsyscall]` mapping. Snapshot components are read
sequentially, not atomically. The old process monitor omitted its monotonic
origin, so its retrospective phase alignment remains conditional; these new
stage-local observations do not require that alignment.

Installed source shows concrete environment roots: kernel bodies, saved
base/mono/impure LCNF and IR, and a historical environment retained by each
`enableRealizationsForConst` context. Persistent sharing does not mean copied
whole heaps or establish quadratic growth. `IR.compile` registers IR; it is not
evidence that each helper produces a native LLVM/JIT module. At sampled helpers,
immediate occupied-slot changes are much larger across the combined compilation
interval than inference or realization insertion. **A small insertion delta
does not exclude retention of a large existing graph**; this profile assigns
neither exact bytes nor dominant causality to those source roots.

### Failing paths, controls and decision

The experimental allocator-error callback records **ENOMEM (12)** and a
48-frame native backtrace in both failures. At 4096 the stack includes
`LCNF.getBaseDecl?` and repeated `LCNF.Specialize.visitCode`; at 256 it includes
array growth in a **phase-extension persistent hash-map insertion while
closed-term extraction saves a mono declaration**. A `replayFn` symbol name
alone does not prove whole-extension replay. These identify failing call paths,
not the major memory
retainer, a common cause of all earlier failures or a successful remedy.

Independent allocator controls distinguish occupancy from backing reservation:
known 32/64 MiB buffers produce matching occupied slots, and freeing restores
**64 slot bytes** while reservation remains **2 GiB**, without collection.
This binary's detailed `touched`/`pages` counters become negative after known
frees; their `not all freed` text is **not a leak receipt**. A synthetic 9 GiB
request under the 8 GiB cap exercises the callback, but does not guarantee
diagnostic reliability near exhaustion. The complete original small/4096 capture
passes native equality, counts **8 / 14**, whole kernel `rfl` and an axiom-free
named theorem: **21.962 seconds / 1,670,204 KiB** controller-child wait4 RSS.

Independent source, receipt and bounded streaming analyses preserve the raw
observations and unchanged original/production pins. Main driver hashes are
post-run pins, not an independent pre/post artifact-immutability pair; the
accepted small control additionally pins its instrument before/after. Initial
native-symbol lookup failures, a failed rebuild followed by a stale-module smoke
run, and exploratory lifetime controls remain setup evidence, not profile
acceptance. No failed witness or diagnostic is silently promoted.

**Decision:** next price ordinary bounded helper/module publication and complete
root reassembly, to measure compiler/environment lifetimes rather than assuming
a cache, selectively deleting compiler roots or raising a cap. Keep complete
input/value equality and normal kernel checking; separately price producer,
compiler, serialization/import and verification processes. No optimization is
implemented here. Original XML full-compilation successes, production loader
changes and C++ semantic/runtime admissions remain **zero**; all existing
ISO, identity, cross-TU/ODR, input-world and execution barriers remain.

## Bounded helper-module publication

The next measured organization uses **ordinary separate Lean modules**, not a
custom environment exporter or an allocator change. It partitions each complete
producer plan into uniform **128-helper batches**, a final root, and separate
native and kernel verifiers. Every ordered `cpp_piece` command, global name,
literal, field and original verifier statement is preserved byte for byte.
Imports follow the actual prior direct-owner dependency DAG; there is no
gratuitous previous-module chain. Helpers remain safe, kernel-unfoldable
`.regular 0` definitions with `noinline`. The production capture loader remains
unchanged, and no cache, deduplication, pruning or opaque fallback is introduced.

The complete XML plans still contain **14,400,775 occurrence nodes** and
**14,008,508 string-literal UTF-8 bytes**. Threshold 4096 partitions 2,992 helpers
into 24 batches, including a final 48-helper remainder; threshold 256 partitions
47,702 helpers into 373 batches, ending with 86. With root and both verifiers,
the complete plans have **27 / 376 stages**. Root modules directly import four
and three owners respectively, not necessarily their whole transitive closure.

The independent exact-text/dependency/conservation audits pass under their own
**256 MiB address-space / 180-second** bounds. Organization takes **8.269 /
9.098 s**, peaking at **25,320 / 21,136 KiB**; separate audits take **16.582 /
17.394 s**, peaking at **25,556 / 63,960 KiB**. These are producer/audit prices,
not compiled-artifact or complete-value equality outcomes. Synthetic mutation
and missing-owner-import negatives refuse as intended.

Publication uses normal headerless legacy modules, normal imports and ordinary
`lean -o`; no external C compilation is performed. Every compiler child retains
the **8 GiB per-process address-space cap**, **180-second** maximum, `-j1`,
`-M8192`, and default heartbeat/recursion options. Each output library starts
empty. Sources, direct dependencies and published artifacts are hashed, and
native whole-value equality against the complete original capture is separate
from the unchanged kernel count witnesses. A helper API return alone is not a
published `.olean`, and a prefix is not root reconstruction.

The initial driver declares a **900-second nominal pipeline allowance**, but
review finds that pre-spawn pinning is outside its stale remaining-time monitor;
post-child receipts are also outside that monitor. Thus this version does **not**
establish a strict 900-second controller bound. Original driver bytes and raw
measurements are retained rather than silently replaced during a run. A separate
corrected driver carries an absolute deadline, checks again before spawn,
rejects nonfinite/nonpositive bounds, enforces manifest stability and re-pins
all successful artifacts. Its post-child receipt overhead is explicitly outside
the child-execution deadline. Mocked deadline controls are not capture reruns.

### Complete XML outcome and registered prefix

Threshold **4096** reaches ordinary publication of all **2,992 helpers** and
the complete root, then imports that root and passes **native whole-value
equality against the original XML capture**, printing counts **4,527 / 14**.
The subsequent unchanged kernel declaration-count `rfl` fails at the default
maximum recursion depth. All **27** planned stages are attempted, **26** succeed,
and the overall pipeline is **FAIL**, not an all-green proof result.

| XML/4096 fresh processes | Outcome | Seconds | Peak wait4 child RSS KiB | Published artifact bytes |
| --- | --- | ---: | ---: | ---: |
| 24 helper batches, summed | PASS | 729.425 | 2,750,680 | 770,776,352 |
| Root publication | PASS | 22.974 | 1,720,816 | 614,464 |
| Imported native whole-value verifier | PASS | 38.936 | 2,040,856 | 1,864 |
| Unchanged kernel count verifier | FAIL: recursion depth | 20.376 | 1,695,624 | none |

Actual wall time through native verification is **793.372 s**, and through the
failed kernel stage **813.753 s**, below the nominal 900-second value without
establishing its enforcement. No compiler child times out. These process prices
include ordinary imports, elaboration, compilation and serialization; they are
not isolated serializer costs. The two primary runs overlap on a shared host,
so no isolated speedup is inferred. No failed witness is deleted, weakened,
assigned a higher recursion limit or replaced by native equality. Whole XML
kernel equality is **not** claimed.

Threshold **256** is deliberately only the pre-registered **eight-stage
prefix**: all eight batches publish **1,024 helpers** in **165.126 s**, occupying
**21,951,800 artifact bytes**. Peak wait4 child RSS is **1,708,012 KiB**; sampled
Lean HWM is **1,719,104 KiB** and VmSize **6,569,360 KiB**. The other 368 stages
are not attempted. This is neither a complete-root result nor an estimate of
the full 376-stage pipeline.

For XML/4096 the final root transitively imports **all 24 helper modules / 2,992
helpers**, despite directly naming only four owners. Thus a 128-helper module
does **not** bound its imported closure. Peak sampled Lean HWM is
**2,756,320 KiB** and VmSize **8,090,652 KiB**; that near-cap virtual size is not
8 GiB RSS. Successful artifact bytes total **771,392,680**, distinct from live
heap or imported-region measurements. Ordinary publication/process isolation
allows this particular full compiler/native verification run to finish where
the single accumulating environment failed; it does not identify the dominant
retainer, prove a general memory bound, or make threshold 256 complete.

Independent controls complete the **entire original eight-row capture** through
four fresh processes: plan generation **19.865 s**, helper publication
**23.291 s**, root publication **19.461 s**, and imported verification
**22.683 s**; end to end **86.292 s**, under a separately declared 600-second
control-pipeline allowance. Native full-value equality, counts **8 / 14**,
root checking and **whole-capture kernel `rfl`** pass with no axioms. Peak sampled
Lean HWM is **1,732,752 KiB**. Published helper/root/verifier artifacts occupy
**7,017,264 / 505,048 / 8,894,048 bytes**. A separate synthetic three-process
publication/import control passes in **63.612 s** and inspects all 25 imported
definitions as `.safe`, `.regular 0`, `noinline`; raw naturals, Unicode/control
strings and partial constructors retain axiom-free preservation witnesses.
These complete controls are not a complete XML result or one 180-second run.

Independent final audits bind every transitive helper artifact to its successful
publication hash, retain exact raw logs and confirm stable manifest/source
bytes. Both original bundles still have **21 files / 14 payload bindings**;
all **9 small / 112 XML source pins** and **six production pins** match the
pre-control snapshot after both primary runs. There is zero input drift.
Six corrected-driver mocked controls pass, including pre-pin expiry, spawn-time
charging, finite bounds, manifest drift and final-artifact drift; watchdog
sampling/scheduling latency remains explicit. Instrument function complexity
stays below 30.

**Decision:** this is the first original complete XML compiler/root/imported
native-equality positive in these receipts, but the preserved kernel witness
still refuses. Price bounded kernel checking of the unchanged declaration-count
statement next, without changing the input, proof statement or default limits.
Do not integrate an unmeasured production organization or treat native equality
as a kernel theorem. Production loader changes, C++ semantic/runtime admissions
and input-world closure remain **zero**; the ISO, identity, cross-TU/ODR and
execution barriers are unchanged.

## Bounded kernel count checking

The next experiment changes **proof organization only**, retaining the complete
original XML capture, all 24 published helper modules and their root, and the
exact original propositions:

```lean
GeneratedCapture.capture.probe.declarations.length = 4527
GeneratedCapture.capture.receipt.payloads.length = 14
```

Traversing the declaration spine observes 4,527 cons cells and 551 constant-tail
boundaries. The root, boundaries and nil give **553 named count facts**, with a
maximum span of **13 cons**; the general producer/checker also caps chunks at 16.
It works backward from nil. A normally checked polymorphic lemma derives a cons
count from its tail count using `List.length_cons`, `Eq.trans` and
`congrArg Nat.succ`. Direct expression applications of that lemma avoid concrete
length arithmetic during proof assembly. Each composed fact is separately added
through ordinary checked `Lean.addDecl`, rejecting unresolved term/universe
metavariables and requiring an actual checked theorem-kind postcondition. Wrong
numerals are not trusted by the checker. The final declaration theorem references the root count fact;
the unchanged payload theorem still uses `rfl`.

The final four fresh compiler children **all pass**:

| Stage | Child seconds | wait4 peak RSS, KiB | Artifact bytes |
| --- | ---: | ---: | ---: |
| Traverse original spine and emit plan | 18.972 | 1,710,084 | 2,008 |
| Check and publish all 553 count facts | 23.831 | 1,757,124 | 8,155,800 |
| Import facts; check exact 4,527/14 statements | 23.594 | 1,730,284 | 7,752 |
| Fresh reimport; repeat statements and inventories | 24.186 | 1,735,724 | 1,912 |

Summed child execution is **90.583 seconds**, and the four receipt intervals sum
to **92.968 seconds**, including their post-child pinning/receipt work but not
pre-child pinning. New artifacts total **8,167,472 bytes**; the emitted plan is
87,957 bytes / 560 lines. This starts from the **previously published** original
25-module import closure: it is not a new 90-second whole-capture compilation.
The separate instrument build takes 20.283 child seconds and produces 814,952
bytes. All children retain **8 GiB per-process AS / 180 seconds / `-j1 -M8192`**,
default recursion **512** and heartbeats **200,000**, synchronous elaboration and
`debug.skipKernelTC=false`. The absolute watchdog bounds child execution only;
controller pinning/receipt overhead and sampling latency are separate.
Peak sampled Lean HWM is 1,757,312 KiB and VmSize is 7,345,612 KiB: the AS
allowance is not an RSS allowance, and these shared-host observations are not
isolated speedup or dominant-retainer claims.

**Trust boundary:** ordinary Lean CLI import trust is **1025**, not zero. Fresh
`addDecl` still kernel-checks new proofs with kernel checking enabled; normal
imports do not recheck every serialized imported proof. Both verification
processes inspect the existing exported transitive axiom inventories of **all
553 facts** and report them empty. The generic cons lemma and both final theorems
also have empty inventories in both processes. No native equality result,
`native_decide`, new axiom, custom cache or increased checker budget supplies
these count proofs.

The prior whole-list `rfl` **remains failed** at default recursion depth, and the
earlier publication pipeline remains **26/27 stages passing, overall FAIL**.
This experiment also retains an unsuccessful explicit-conversion organization:
17 facts publish through count 128, then the next count 134 reaches default
recursion depth (18.055 child seconds, no artifact). The abstract-lemma
organization passes; the failed log does not isolate the exact internal
conversion/checking call. Wrong-trust-header guards, command/API setup errors,
an off-by-one universe instantiation and early strengthened `-t0` controls remain
archived separately, never promoted to normal-CLI positive receipts.

Independent controls retain the original long-list `rfl` failure while proving
the same synthetic 1,536-cell count by ordinary induction with empty axioms.
The final shared commands also pass the original synthetic count through 97
facts at uniform span 16, and the original small-capture count 8 through two
facts, with payload count 14 unchanged. All these count inventories are empty;
a fresh reimport passes in 25.661 wall seconds. An altered final-step count 1,537,
empty count 1 and false `0 = 1` proof each fail actual kernel type checking,
exit 1 and publish no artifact; a non-list argument refuses at the API boundary.
Per-child source/dependency pins and independent receipt audits retain the
complete original module closure, exact predecessor chain, unchanged count
statements and earlier failed witness. Generated fact-command lines are
byte-identical across the depth-failing and final proof organizations.
Post-primary original-input pins retain both bundles' 21 files / 14 bindings,
9 small / 112 XML source pins and six production source pins with zero drift.
Shared and independent instrument functions remain below complexity 30.

**Decision:** bounded kernel checking now proves these two original **metadata
counts**, not whole-capture value equality, clang AST correctness, C++ execution
or ISO semantics. The previous full-original native equality is still a separate
observation, not a substitute for a kernel equality theorem. Price the unchanged
whole-original equality witness next under the same bounds; do not promote
production organization or a new semantic/runtime admission from count proofs.
Production loader changes, input-world closure and semantic admissions remain
zero, with the ISO, identity, cross-TU/ODR and execution barriers unchanged.

## Whole-original equality witness

The follow-up keeps the complete published XML root and the exact original
capture path. A fresh command imports the 25-module publication closure,
reconstructs the unchanged `DeclarationCapture` with `price_cpp_capture`, and
then asks the kernel for the direct witness:

```lean
example : GeneratedCapture.capture = originalCapture := rfl
```

The run uses the normal Lean limits: synchronous elaboration, default recursion
depth **512**, **200,000** heartbeats, `-j1 -M8192`, an **8 GiB** per-process
address-space cap and a **180-second** child watchdog. Reading and `toExpr`
construction complete, but the fresh full-value declaration reaches the LCNF
compiler's heartbeat limit before its API returns. The equality declaration is
therefore not elaborated; the subsequent count checks only report the expected
dependent errors and are not positive evidence.

| Stage | Seconds | wait4 peak RSS, KiB | Outcome |
| --- | ---: | ---: | --- |
| Fresh full-value equality command | 47.682 | 2,873,480 | LCNF compiler heartbeat refusal; no artifact |

The durable markers are `read-start`, `read-complete`, `toexpr-start`,
`toexpr-complete` and `add-and-compile-start`; there is no
`add-and-compile-api-return`. Sampled Lean peaks are **2,881,668 KiB RSS/HWM**
and **8,336,540 KiB VmSize**, below the 8 GiB address-space ceiling. The source
fixture, published root and command instrument are pinned by SHA-256 in the
receipt directory. This is a bounded negative result, not evidence that a
larger budget or a different organization could never close the equality.

The earlier complete-capture native equality remains a separate positive
observation, and the bounded count facts above remain the only fresh kernel
theorems for the original XML under default limits. No equality theorem,
production loader change, input-world closure or C++ semantic/runtime
admission is promoted; ISO, identity, cross-TU/ODR and execution barriers are
unchanged.

## Prefix equality does not bypass the RHS

As a bounded organization probe, a fresh command imports the same published
root, loads the exact original declaration-row list, and asks only for the
first eight rows:

```lean
example : GeneratedCapture.capture.probe.declarations.take 8 =
    originalRows.take 8 := rfl
```

This still reconstructs `originalRows` from the complete input before `take`
can reduce. Under the unchanged default recursion depth **512**, the
`price_cpp_capture rows` declaration reaches the recursion-depth limit before
its API returns. The prefix theorem therefore has no RHS constant and is not a
positive equality witness.

| Stage | Seconds | wait4 peak RSS, KiB | Outcome |
| --- | ---: | ---: | --- |
| Full row literal plus eight-row prefix theorem | 39.041 | 1,952,916 | recursion-depth refusal; no artifact |

Markers reach `add-and-compile-start` but not
`add-and-compile-api-return`; sampled process peaks are **832,424 KiB
RSS/HWM** and **5,426,068 KiB VmSize**. The result confirms that a useful
prefix proof would require a separately admitted, input-preserving segmented
RHS—not merely `List.take` over the complete literal. That segmentation is a
new organization decision, not silently introduced by this negative probe.

## Receipts

Full commands, limits, diagnostics, source/input pins, instrument sources,
raw markers, sample archives and review notes are under
`/var/tmp/thomas-ahle/fleet2/state/ls-cpp/capture-pricing-20261010/`, split into
`xml/`, `json/`, `shared/` and `review/`. The prior default census remains
under `capture-ingestion-20261010/census/`; these new resource experiments
do not rewrite its outcomes or promote the observational captures to
semantic evidence.

The follow-up's exact commands, fixture/instrument hashes, effective toolchain,
durable markers, process samples, passing controls, independent inventories and
reviews are under
`/var/tmp/thomas-ahle/fleet2/state/ls-cpp/capture-organization-20261010/`, split
into `shared/`, `inputs/` and `review/`. Initial wrapper/build and wrong-toolchain
import failures are setup diagnostics, excluded from the pricing outcomes.

The factoring experiment's exact commands, final toolchain/instrument hashes,
original before/after pins, default-bound process samples, helper markers, native
and kernel controls, negative fixtures and independent audit are under
`/var/tmp/thomas-ahle/fleet2/state/ls-cpp/capture-factoring-20261010/`, split into
`shared/`, `runs/`, `controls/` and `review/`. Early reserved-keyword/command-grammar
build failures, runtime aborts during those setup attempts and a missing-module
control are retained as setup diagnostics, not XML pricing or ingestion outcomes.

Fresh-context compiler runs, complete producer-only plans, independent streaming
audits, original before/after pins, native/kernel and codec controls, versioned
instrument hashes, source reviews and validation logs are under
`/var/tmp/thomas-ahle/fleet2/state/ls-cpp/capture-command-factoring-20261010/`,
split into `shared/`, `runs/`, `census/`, `controls/`, `review/`, `versions/v1/`
and `validation/`. The v1 archive pins the instrument used for primary/census
measurements; current shared sources include the later v2 decoder correction.

The memory-profile item's exact commands, native diagnostic source/binary,
instrument/module hashes, complete stage logs and process samples, failing-path
backtraces, source-root inventory, independent allocator/lifetime/capture controls,
before/after input pins and bounded reproducible analyses are under
`/var/tmp/thomas-ahle/fleet2/state/ls-cpp/capture-memory-profile-20261010/`, split
into `shared/`, `runs/`, `controls/`, `census/`, `review/` and `validation/`.
These observations do not change the previous uninstrumented pricing receipts.

Exact module-partition commands, complete-plan manifests and streaming audits,
ordinary publication/import controls, primary stage logs and samples, published
artifact hashes, version-separated deadline instruments, independent source and
receipt reviews, before/after original-input pins and focused validation are
under
`/var/tmp/thomas-ahle/fleet2/state/ls-cpp/capture-module-publication-20261010/`,
split into `shared/`, `runs/`, `census/`, `controls/`, `review/` and `validation/`.
The primary receipts retain the initial driver's nominal-deadline limitation;
the corrected instrument's mocked controls do not retroactively strengthen them.

The unchanged-count experiment's exact commands, versioned proof instruments,
complete spine plan, default-bound child receipts and samples, empty axiom
inventories, independent small/synthetic/negative controls, source/module pins,
retained failed witnesses and focused validation are under
`/var/tmp/thomas-ahle/fleet2/state/ls-cpp/capture-kernel-count-20261010/`, split
into `shared/`, `runs/`, `controls/`, `review/`, `versions/` and `validation/`.
The passing final organization is V7; earlier setup and depth failures are not
relabelled, and a fresh reimport does not imply zero-trust import checking.

The default-bound whole-original equality attempt is under
`/var/tmp/thomas-ahle/fleet2/state/ls-cpp/capture-whole-equality-20261010/`.
Its source, command/result receipt, process samples, diagnostic markers and
SHA-256 input pins are retained; the expected heartbeat refusal produced no
artifact.

The bounded prefix-equality probe is under
`/var/tmp/thomas-ahle/fleet2/state/ls-cpp/capture-prefix-equality-20261010/`.
Its source, result, process samples, diagnostic markers and complete input pins
are retained; the recursion-depth refusal produced no artifact.
