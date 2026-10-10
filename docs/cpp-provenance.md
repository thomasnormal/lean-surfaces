# C++ declaration evidence — capture provenance

2026-10-10. **Optional observational runner and literal receipt loader; no
semantic query or runtime admission.** This specifies the process/input boundary
between [literal probe observations](cpp-declaration-pricing.md) and the
[ordinary ISO/frontend bridge](cpp-ordinary-bridge.md). The current
`cpp-canonical-probe-0.3` wrapper and `load_cpp_probe` remain unchanged.

## What the current artifacts establish

The optional plugin visits an ASTContext and dumps that same context's TU in
one output wrapper. Its pointer-derived handles belong to that frontend
session. The wrapper does **not** record the launch command, input manifests
or compiler/plugin/library images. Literal ingestion checks data and version
tags; it does not authenticate who produced it or under which inputs.

The separate `cpp-0.1` extractor records its constructed AST command, cwd,
selected environment values and positive dependency hashes. Discovery,
AST production, predefined macros, version and target are separate processes.
It passes the inherited environment while storing only a projection, and its
before/after checks do not establish an immutable filesystem. Neither an
existing Artifact nor an existing DeclarationProbe can be relabeled as the
capture below. Their literal-data and execution-refusal behavior stays
as specified in [the translation contract](cpp-translation.md).

Three obligations must stay separate:

| Obligation | Meaning | What it does not establish |
| --- | --- | --- |
| Receipt binding | Strict data, exact output-byte digest and complete required launch records agree. | Producer authenticity, actual execution or unchanged inputs. |
| Observed capture | The trusted capture launcher observed a successful pinned frontend run and matching positive-input checks around it. | Exact bytes read at every instant, negative lookup closure or replay. |
| Input-world closure | A separately specified witness identifies the frontend's actual input bytes, resolution observations and other admitted inputs, or a trusted isolated immutable world supplies them. | Clang conformance, declaration graph closure, ISO entity results or execution correctness. |

The first two are a useful tooling deliverable without the third. A later
source-linked semantic claim must state its input-world assumptions; successful
hash checks must not silently discharge them. Cryptographic digests bind bytes
under the stated integrity assumption, not a compiler process or a signature.
No new Lean axiom or theorem about a synthetic program supplies these bridges.

## Versioned capture bundle

The capture schema is **`cpp-probe-capture-0.1`**, with profile
**`cpp23-clang-probe-capture-0.1`** and subject edition **C++23**. These names
are emitted by the optional runner and accepted by the separate capture loader,
not by `load_program` or `load_cpp_probe`.
The initial runner uses the existing Clang/LLVM **21.1.8** plugin schema **0.3**.
The plugin build language remains separate from the subject language.

Keep an exact-byte `probe.json` and a separate strict `capture.json` receipt in
a no-overwrite publication bundle. Retain stderr and dependency output as
separately bound byte artifacts too. Do not normalize/re-serialize stdout and
then call its digest the digest of the frontend's original bytes. This avoids
duplicating a large AST inside two envelopes. Bundle-relative artifact paths
must not escape the bundle or alias source/tool inputs; logical source paths
remain separately recorded, not replaced by bundle paths.

Every field group below is mandatory. Unknown schemas, incomplete groups and
missing/null/type/API ambiguities refuse; extensions remain raw observations
only when the versioned field policy explicitly permits them. No empty string,
zero, empty manifest or inferred host default fills a missing observation.

| Group | Required record |
| --- | --- |
| Identity | Capture schema/profile/edition, exact probe schema, capture-tool version and source/image hash. |
| Payloads | Bundle-relative path, byte count and SHA-256 for exact stdout, stderr and dependency output; strict parsed stdout must be one complete probe wrapper. |
| Launch | Absolute invoked executable path and resolved image identity, ordered argv tokens, exact cwd, explicit environment policy/version and effective key/value map. |
| Frontend | Compiler, plugin and declared runtime-library image paths/hashes, resource-directory identity, compiled/runtime/header version observations and their producing commands/statuses. Record whether the declared image closure is complete or unestablished. |
| Source | Logical command path, resolved identity and main-source bytes/hash; preserve path spellings that can affect source-location macros. |
| Positive inputs | Discovery command/status and parsed manifest, pre-run hashes, the actual probe run's dependency manifest and post-run hashes, with explicit equality-check outcomes. Include system headers and positive existence-probe dependencies, not just user includes. |
| Completion | Exit status, signal/timeout/resource-limit outcome, complete-output checks, wall/RSS measurements and enforced bounds. Measurements never substitute for completion. |
| Closure limits | Explicit input-world closure status and evidence kind, including unresolved filesystem/search/loader/environment assumptions. A caller Boolean asserting closure is not a witness. |

All byte artifacts are checked before literal conversion. The strict parser
must retain integer lexemes, array/object order and repeated ledger rows while
rejecting invalid UTF-8, malformed Unicode, duplicate decoded object keys and
noninteger JSON numeric tokens. An output digest is checked against the stored
byte artifact, not a parsed tree's chosen serialization. Required hashes and
counts have exact domains; every required status distinguishes observed success
from not run, unknown, failure and truncation.

The launcher must construct an explicit effective environment rather than
inherit an unrecorded host environment or export credentials into receipts.
Absent and present-empty allowed variables are distinct. Driver overrides,
uncontrolled dynamic-loader injection and unrecognized environment inputs
refuse. Ordered flags, target, include-search paths, forced includes, macros,
resource directory and explicit `SOURCE_DATE_EPOCH` are retained. No response
file, default driver configuration or second source is silently expanded.
If effective cc1 arguments are not directly witnessed, record that limitation;
a separate diagnostic driver's rendering is not the actual cc1 transcript.

The implemented capture profile validates the existing strict single-TU C++23
**launch flag policy**, with explicitly pinned plugin options. Explicit
module/header-unit, PCH/GCH, VFS-remapping and additional-action configuration
flags are not admitted. This is not a source-form exclusion check: a source
module declaration or other excluded form may still parse under these flags.
The receipt's `ordinary_source_profile` therefore remains **unestablished**.
Even uniformly null `owning_module` observations would not prove that the
translation unit is nonmodule or meets the ordinary bridge's source profile.
Declarations from templates or headers remain in the complete raw output;
capture must not filter them away to satisfy a later ordinary-declaration gate.
Template/source-form exclusions remain query-local semantic obligations.

## Implemented observational slice

The standard-library-only `extractors/cpp/capture_probe.py` runner is optional,
Linux-only and separate from extraction, pricing and Lean ingestion. It does
not compile or obtain the plugin, discover its ABI-safe runtime closure or
execute the subject program. Supply an explicitly pinned compiler/plugin and
any declared runtime-library paths:

```sh
python3 extractors/cpp/capture_probe.py subject.cpp \
  --clang /path/to/clang++ --plugin /path/to/canonical_probe.so \
  --runtime-library /path/to/libclang-cpp.so.21.1 \
  --runtime-library /path/to/libLLVM.so.21.1 \
  --out-dir /path/to/new-capture --timeout 300 --memory-mib 16384 \
  -- -I/path/to/subject/includes
python3 extractors/cpp/test_capture_probe.py
```

The output parent must exist; an existing destination, including a dangling
symlink, refuses. Publication uses a Linux atomic no-overwrite directory rename
after validation; it neither makes outputs read-only nor protects against
adversarial concurrent filesystem mutation. After staging has been created, a
failure retains it with a named `failure.json` and any available exact outputs
and process observations. There is no successful requested bundle on failure.
Earlier preflight failures have no staging artifact to retain.

Successful bundles include exact `probe.json`, `stderr.txt`, actual `inputs.d`,
discovery depfile, auxiliary observation outputs and per-command process
receipts, together with `capture.json`. The runner checks strict UTF-8/JSON and
probe wrapper/header pins before publication; the full typed declaration-row
validator remains the separate Lean loader. Version, target, resource-directory
and predefined-macro queries are separate launches with retained command and
status records, not a transcript of the actual probe cc1 invocation.

The effective environment policy is `controlled-clang-environment-0.1`:
fixed `PATH`, `LC_ALL=C` and `TZ=UTC`, plus the existing extractor's allowed
include/platform variables. An absent `SOURCE_DATE_EPOCH` defaults to `0`;
present-empty remains distinct. Driver overrides and loader-injection variables
refuse; the rest of the inherited host environment is not passed or serialized.
Source argument spelling, ordered allowed flags and cwd are retained. A source
argument beginning with `@` or `-` refuses as a response-file/option/stdin
ambiguity; a literal filename with that prefix can use `./`. Only the strict
existing single-TU C++23 subject-flag policy is accepted after `--`; validation
does not establish the separate ordinary/nonmodule source profile.

The compiler, plugin, declared runtime-library files, producer sources and
Python executable receive before/after image checks. **Declared images are not
observed loaded images.** The list can be empty only with image closure still
unestablished. Resource-directory paths and walked entries are checked too;
symlink directory targets are not traversed. Inputs absent from discovery,
actual loader/search state, source-form exclusion and producer authenticity
remain outside the check.
No caller claim promotes those limits into closure evidence.

Defaults are 300 seconds per frontend subprocess and 16,384 MiB per process
address space, with bounds inherited by its descendants. An inherited 4 GiB
per-file size limit is not an aggregate disk-space bound. Child wait4 resource
usage is labeled separately from the parent runner. The parent parser's memory
is not limited by `--memory-mib`; these are not whole-capture resource bounds.
The supported launcher is the standalone single-threaded CLI. Additional
detected Python threads refuse before launch because child resource setup uses
the post-fork callback; this guard neither proves absence of native threads nor
supports concurrent library calls.
Exit 0 reports observed positive-input stability, never input-world closure,
hermetic replay, receipt ingestion, declaration admission or C++ execution.

## Optional literal receipt binding

`LeanModels.Cpp.CaptureLoad` supplies a separate command for a published bundle:

```lean
import LeanModels.Cpp.CaptureLoad

load_cpp_capture captured from "path/to/capture-bundle"
```

The result is a literal `DeclarationCapture`, containing a `CaptureReceipt`
and the existing `DeclarationProbe`. The receipt retains its complete parsed
raw tree alongside typed payload-binding records and validated field groups;
the probe retains its full AST, metadata, ordered rows and typed observations.
It is not an `Artifact`, a process witness or an ISO declaration certificate.
Neither command changes the other loaders or supplies execution semantics.

The receipt's JSON parser shares string, array, object, duplicate-decoded-key
and Unicode checks with the strict probe parser. Capture receipts additionally
accept the full JSON number grammar as exact `Raw.number` token strings:
decimals, exponent spelling, huge integers and `-0` are not converted through
floating point. Typed natural-number fields remain integer-only. Probe parsing
and `validateStrictRaw` remain integer-only; a receipt's numeric profile does
not weaken the probe profile.

Loading reads `capture.json`, validates its versioned literal-data contract,
and checks every declared bundle payload's byte count and SHA-256. The four
required payloads and each recorded process's stdout/stderr must be bound.
Mandatory field groups and selected cross-field correspondences are checked;
unknown fields remain raw observations, not new typed or semantic guarantees.
Recorded positive manifests are checked for agreement, not reconstructed from
the dependency payloads or authenticated against filesystem reads.
The exact in-memory probe bytes checked by the digest are the bytes decoded as
strict UTF-8 and passed to the existing typed probe parser. Auxiliary payloads
are checked but their complete bytes are not duplicated in the literal.
Bundle payload names are ordinary basenames; traversal, absolute names,
symlinks and non-file payloads refuse. The bundle must be a quiescent directory
owned by the caller. Before/after metadata checks and real-path checks are not
an adversarial concurrent-filesystem-mutation guarantee.

The byte-binding boundary explicitly trusts Lean's filesystem and process IO,
the executable **`/usr/bin/sha256sum`**, and SHA-256 integrity. Hashing is not
implemented as a kernel theorem. The hashing subprocess receives the same
in-memory bytes, with a cleared inherited environment and `LC_ALL=C`; a named
host executable is still a trust assumption, not producer authentication.
The receipt itself is unsigned, and successful loading cannot distinguish a
real launch record from a fabricated but internally consistent one.

Original source, positive inputs, producer sources and toolchain images need
not remain installed when a copied bundle is loaded. Their recorded paths and
hashes are literal observations, not source/image rechecks or proof of actual
reads. Portability means retaining and binding the bundle, not replaying the
frontend or authenticating its process. `input_world`, runtime image closure,
effective cc1 and ordinary source-profile closure remain **unestablished**;
semantic and runtime admissions remain **false**. No row consensus, graph
closure, pointer/entity merge, ISO query, ODR claim or runtime result follows.

## Capture checks and stronger input-world evidence

The observational launcher performs these checks, without claiming
that they implement a filesystem snapshot:

1. Validate the profile and controlled launch environment. Pin the capture
   tool, compiler/plugin and declared toolchain images before loading code;
   matching version strings alone do not establish ABI safety or image identity.
2. Discover positive inputs under the same source/profile, preserving that
   command and its outcome. Hash the discovered inputs and declared images.
3. Invoke **one probe frontend action** which supplies both metadata and raw
   AST from the same ASTContext, and emits its dependency record. Retain exact
   stdout/stderr/status. A separate compiler dump cannot supply interchangeable
   handles, even when source/header hashes and command strings match.
4. Require successful completion and strict complete output. Parse the actual
   dependency record, compare path sets and pre/post bytes, and recheck declared
   tool images. Missing, unreadable, changed or unparseable inputs refuse.
   A zero exit with malformed output is failure; parseable partial stdout from
   a failed/timed-out process is also failure.
5. Bind the receipt to the exact outputs and publish atomically. Failed
   validation leaves no successful bundle. Output aliases, partial publication,
   mutated referenced artifacts and unsafe relative paths refuse.

Changing a file during the run and restoring its original bytes before the
post-check can evade before/after hashes. Discovery and the actual frontend are
also different processes. Therefore the resulting guarantee is **observed
positive-input stability**, not proof of bytes read or complete input closure.
Tool/runtime/version queries made in additional processes must retain their
own status and timing boundaries; they cannot retroactively pin the main run.

In the pinned compiler, dependency generation registers a successful
`__has_include` lookup but not a missing file. It is not a transcript of failed
include-search candidates. An absent candidate becoming present, an earlier
search-directory header shadowing the old selection, symlink changes or an
unrecorded VFS mapping can change translation without changing the old positive
manifest. Do not deduce replay safety from that manifest. Original logical
paths, search order and resolution results matter independently of content
hashes. A fresh capture under the changed world is a new observation.

For Clang 21.1.8, accepted explicit `SOURCE_DATE_EPOCH` controls `__DATE__`, `__TIME__`
and `__TIMESTAMP__`; claiming that the last necessarily escapes this setting
would be wrong. This pin still does not close filesystem/search state,
toolchain images or every other input. A future supported closure witness must
either retain the frontend's actual read bytes and resolution/input oracle,
including relevant misses, or specify a trusted isolated immutable world with
escape prevented and all remaining inputs explicit. Neither mechanism exists
in this item. Replay comparisons allow fresh session handles and require
witnessed occurrence alignment; byte-identical pointer dumps are not required.

## Admission boundary and acceptance plan

Receipt parsing is pure literal-data ingestion. Observed capture depends on
the named trusted launcher/frontend boundary, not on reading a JSON status
claim. Any future admitted supplement must validate the applicable receipt
binding and state the capture/input-world assumptions it consumes. The four
declaration queries still separately require their raw occurrence witnesses,
query-local row consensus, relevant graph closure, typed family evidence and
ordinary ISO/source-form bridge. None is inferred from provenance, and no
cross-process/cross-TU entity relation or ODR claim follows from payload hashes.
Execution remains behind `rung-0:no-executable-semantics`.

The observational runner's focused tests and any later receipt-binding loader
must distinguish the following cases; capture-only validation must not be
relabeled as completed literal ingestion or stronger closure:

| Case | Required outcome |
| --- | --- |
| Pinned successful compiler/plugin run | Bound receipt with exact bytes, commands, positive inputs and successful status; semantic/runtime admission remains zero. |
| Observed main/header/compiler/plugin hash change or changed dependency set | Named stability refusal, no successful publication. Retain the failing receipt. |
| Nonzero exit, signal, timeout, bad/partial JSON or depfile | Failure even if some stdout parses; never an optional success or whitelist. |
| Changed flag order, cwd or absent/empty environment | Different recorded input; hidden overrides/unaccounted inputs refuse. |
| Negative include probe or higher-priority shadow appears | Demonstrate the observational manifest's replay limitation; never label the old receipt closed. |
| Change then restore between hash checks | Demonstrate the read-byte limitation, not a claim that two hashes detect it. |
| Duplicate keys, invalid Unicode/UTF-8, numeric coercion or tampered payload digest | Refusal before typed conversion/publication; huge integer and `-0` controls retain their lexemes. |
| Repeated/conflicting rows and a foreign valid handle | Retain ordered observations; no deduplication, cross-run pointer joins or fabricated semantic consensus. |
| Bare schema-0.3 probe, missing receipt fields or unsafe output path | Bare data stays observation-only; provenance-required admission refuses explicitly. |

For each of TinyXML2, nlohmann/json and read-only Mox, a later capture census
must report attempted TUs, unavailable inputs, strict frontend rejection,
timeout, parse/binding/stability refusal, successful observed capture and
literal embedding **separately**, with time/RSS/bytes and complete pin receipts.
Input-world closure, tooling query eligibility, semantic queries and runtime
verdicts are separate counters, not relabeled captures. The initial bounded
capture census attempts one original registered TU/profile per corpus, not all
TUs: TinyXML2 and nlohmann/json publish observational bundles; strict Mox
retains its anonymous-struct/nested-anonymous-type frontend rejection. It does
not perform new literal embedding or establish input-world/source-profile
closure. Historical source/body/declaration-only counts remain
XML **205/202/3**, JSON **1,572/963/609**; strict Mox refusal and semantic/runtime
admissions of **zero** are unchanged.

The separate capture-loader census attempts literal compilation of those two
published original-profile bundles under `-j1`, an 8 GiB address-space bound
and a 180-second wall cap. TinyXML2 refuses at Lean's default 200,000-heartbeat
LCNF deterministic timeout (**41.540 s**); nlohmann/json refuses with internal
out-of-memory (**23.750 s**). Strict Mox has no successful capture receipt to
load. Thus **zero original-profile capture literals complete compilation** in
this bounded default profile; partial elaboration or printed `#check` output
is not success. Aggregate measured maximum RSS is **3,324,508 KiB**. A separate
small actual-module observation with eight declaration rows loads successfully,
without establishing ordinary/nonmodule source admission or executable
semantics. These are literal resource outcomes, not new compiler or semantic
verdicts, and no corpus-specific budget or special-case path is introduced.

## Primary references

The baseline remains the charter's C++23/WG21 N4950. The translation discussion
concerns `[lex.phases]` and `[cpp.include]`; this document adds no interpretation
of entity rules beyond the separate declaration bridge.
Frontend details above are read from the **pinned** LLVM source, not a moving
development branch:

- [DependencyFile.cpp](https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/clang/lib/Frontend/DependencyFile.cpp): dependency registration, successful existence probes and missing files.
- [PPMacroExpansion.cpp](https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/clang/lib/Lex/PPMacroExpansion.cpp): date/time/timestamp expansion and `SOURCE_DATE_EPOCH` handling.
- [PPCallbacks.h](https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/clang/include/clang/Lex/PPCallbacks.h): final include/existence observations are not a complete filesystem lookup trace.

These references support a tooling contract, not independent compiler
conformance. The optional runner remains observational and the capture loader
remains literal-data binding. Any input-world closure mechanism is a separately
reviewable future item.
