# The duplication audit: where seven lanes built the same thing

**Measured 2026-08-22** against master at `76cd043`, in a clean clone
(`~/repos/lean-audit`). No Lean was executed for any number in this
document — every count is git, grep, `ps`, `du`, or `python3 -c`, and the
command that reproduces it is printed beside it.

The brief was Thomas's: *"look for duplicated work, that might inspire
better overall design."* The order matters. This is not a de-duplication
sweep — a family of thin siblings over a thin trunk (§2.4) is **supposed**
to repeat itself in places, and §3.7 already ruled that two of the three
span types are honest divergence and not defects. What earns a proposal
here is duplication that has produced **the same defect more than once**,
because that is the form of duplication that is not a style question.

Every proposal below is priced in three parts: lines saved, migration cost,
and the sequencing. **Nothing here is a big-bang migration.** Where a
proposal was ready to be code it is code: `tools/triad.sh` lands with this
document, syntax-checked and self-tested, and **wired into no lane's flow**.

---

## 0 THE HEADLINE, and it is not the line counts

Three findings, and the third one was live on the machine while this was
being written.

1. **The census contract is implemented 14 times, and 3 of those
   implementations cannot fail.** `--compare` exits **0 on drift** in
   `c_construct_census.py`, `wasm_spec_census.py` and
   `wasm_suite_census.py` — so the mode §5.4 requires *"because staleness
   must be mechanically detectable rather than merely possible"* is, in
   those three, detectable only by a human reading the delta. The first of
   those three is the instrument §5.4 names as the one that **fixed the
   contract**.

2. **The double-run byte-identity clause of §5.4 is implemented in ZERO
   instruments.** It appears as a claim in at least four instrument
   docstrings and eight documentation sites; no instrument has a mode that
   runs itself twice and compares. It is the cheapest clause in the
   contract and it is the only one nobody wrote.

3. **The build lock was being violated live, by two lanes, for 48
   minutes.** At 17:38 on 2026-08-22 `/tmp/ls-build.lock/owner` read
   `es-lane 87905`, two tickets were queued, and **two `lake build`
   processes were running concurrently** in two different clones — pid
   87633 under `ctier-triad.sh` (pid 85836, elapsed 49:03) in
   `lean-ctier2`, and pid 90763 under `es-build.sh` (pid 87905, elapsed
   47:12) in `lean-es`. The C lane held no lock and was building anyway.
   §7.1 rule 1 says ONE, machine-wide.

   Reproduce the shape (not the moment):
   `cat /tmp/ls-build.lock/owner; ls /tmp/ls-build-queue; ps -eo pid,ppid,etime,args | grep '[l]ake build'`

> **FINDINGS 1 AND 2's exit codes are FIXED — see §10, landed the same day.**
> The seven implementations were corrected and verified in both directions;
> the *contract* duplication they came from is untouched, and stays
> migrate-on-touch for the owning lanes.

Findings 1 and 3 have the same cause, and it is the subject of this
document: **the contract lives in prose, and each lane hand-implements
it.** Prose cannot be run, so a lane's implementation is only as good as
its reading, and a defect in one reading is invisible to every other lane.

---

## 1 THE INSTRUMENT CONTRACT, implemented 14 times

### 1.1 What was measured

Twenty-one census/check instruments, **10,220 lines** — of which 14
implement `--compare`:

    git ls-files | grep -E 'census|citation_check|independent_check|rule_correspondence' \
      | grep -v '^harness/scripts/'
    wc -l harness/*census*.py harness/c_citation_check.py harness/lean_independent_check.py \
          harness/lean_rule_correspondence.py extractors/sv/census.py

Contract-bearing spans, by `ast` (script: sum of the `main`, `compare`,
`self_test`/`selftest` and provenance-helper function bodies):

| instrument | total | main | cmp | self | prov | Σ | Σ% |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `harness/es_census.py` | 994 | 147 | 0 | 62 | 7 | 216 | 22% |
| `harness/import_census.py` | 561 | 140 | 0 | 29 | 0 | 169 | 30% |
| `extractors/sv/census.py` | 815 | 116 | 35 | 0 | 0 | 151 | 19% |
| `harness/ada_suite_census.py` | 785 | 45 | 0 | 75 | 0 | 120 | 15% |
| `harness/c_construct_census.py` | 616 | 29 | 22 | 59 | 10 | 120 | 19% |
| `harness/class_census.py` | 801 | 97 | 0 | 0 | 0 | 97 | 12% |
| `harness/wasm_suite_census.py` | 455 | 70 | 0 | 0 | 22 | 92 | 20% |
| `harness/wasm_spec_census.py` | 357 | 70 | 0 | 0 | 18 | 88 | 25% |
| `harness/ada_construct_census.py` | 321 | 49 | 0 | 39 | 0 | 88 | 27% |
| `harness/ada_spec_census.py` | 416 | 48 | 0 | 38 | 0 | 86 | 21% |
| … 11 more | | | | | | | |
| **all 21 files** | **10,220** | **1,218** | **57** | **384** | **101** | **1,760** | **17%** |

**17% is the outer bound and it flatters the case**, because those spans
also carry real tier logic (`es_census.py`'s `--check-schema`,
`lean_kernel_census.py`'s toolchain derivation). The honest inner number is
the *strictly generic* plumbing, counted block by block:

| generic block | instruments | total lines | command |
| --- | ---: | ---: | --- |
| `argparse` construction (`ap = …` → `parse_args()`) | 14 | **138** | `awk '/= *argparse\.ArgumentParser/{f=1} f{c++} /parse_args\(/{if(f){print c;exit}}' <f>` |
| `--compare` handling | 14 | **226** | `if args.compare` block + `compare()`/`do_compare()` bodies |
| output plumbing (serialize → `-o` → stdout) | 13 | **83** | `if args.output/out` block |
| the refusal exception class | 8 | **16** | `grep -n -A2 'class .*Refusal' harness/*.py` |
| `git rev-parse` provenance helper | 4 | **56** | `git_rev`/`git_describe`/`rev`, one 6-line function |
| **total strictly-generic** | | **≈519** | |

So: **~520 lines of pure contract, 1,760 lines of contract-shaped code, and
one contract.**

### 1.2 The four defect classes that duplication produced

Line counts are the weak argument. These are the strong one.

**(a) `--compare` exits 0 on drift in 3 of 14.** Four dialects exist:

| dialect | instruments | missing baseline | agreement | DRIFT |
| --- | --- | --- | --- | --- |
| Lean lane | `lean_{axiom,kernel,spec}_census`, `lean_rule_correspondence`, `lean_independent_check` | **REFUSE, exit 2** | 0 | **1** |
| Ada lane | `ada_{construct,spec,suite}_census` | traceback | 0 | **1** |
| ES lane | `es_census`, `es_m2_census` | traceback | 0 | **1** |
| SV | `extractors/sv/census.py` | — | 0 | **1** |
| **C + Wasm** | `c_construct_census`, `wasm_spec_census`, `wasm_suite_census` | traceback | 0 | **0** ← |

Cite: `sed -n '494,515p' harness/c_construct_census.py` (both exits are
`return 0`); `sed -n '320,332p' harness/wasm_spec_census.py`;
`sed -n '404,430p' harness/wasm_suite_census.py`. Contrast
`sed -n '396,408p' harness/lean_kernel_census.py`.

A `--compare` that cannot exit nonzero cannot be a gate, cannot be used
under `set -e`, and cannot be the staleness detector §5.4 asks for. Eleven
lanes got it right; three did not; nobody could see the difference because
there is nothing to compare *against*.

**(b) Four copies of one 6-line function, all with the same silent
degrade.** `git_rev` appears in `wasm_spec_census.py:205`,
`wasm_suite_census.py:268`, `es_census.py:771` and inline at
`lean_independent_check.py:100` — and **every one of them swallows the
failure**:

```python
    except (OSError, subprocess.SubprocessError):
        pass
    return None
```

The census is then written with `"revision": null` or `"checker_commit":
""` and **no refusal**. That is §5.4a inverted: the number is quoted and
the state is silently dropped, and §5.4a's own warning is that the failure
mode reads *cleaner than the truth*. The family already contains the
correct pattern — `lean_kernel_census.py:250` raises `CensusRefusal` when it
cannot determine the toolchain — so this is not a knowledge gap, it is four
copies of one function that was written wrong once.

    python3 - <<'EOF'   # 28 except-and-pass sites in instruments/extractors
    import ast, glob
    for p in sorted(glob.glob('harness/*.py')+glob.glob('harness/*/*.py')+glob.glob('extractors/*/*.py')+glob.glob('tools/*.py')):
        if '/scripts/' in p: continue
        for n in ast.walk(ast.parse(open(p).read())):
            if isinstance(n, ast.ExceptHandler) and len(n.body)==1 and isinstance(n.body[0], ast.Pass):
                print(f"{p}:{n.lineno}")
    EOF

(20 of the 28 are in `extractors/sv/`, which is a separate matter for that
lane; the 4 provenance ones are this finding.)

**(c) No two censuses agree on how to spell provenance.** Twenty-six
committed census artifacts under `docs/`:

    python3 -c "import json,glob,os; [print(p, sorted(json.load(open(p)).keys())) for p in sorted(glob.glob('docs/*census*.json'))]"

* a `schema` key: **12 of 26** carry one.
* **five carry no provenance key at all**: `c17-c23-clause-delta.json`,
  `class-tier-census.json`, `es-m2-census.json`,
  `import-ceiling-census.json`, `py-version-delta.json`.
* "which revision was this measured at" is spelled, across the family:
  `revision`, `rev`, `commit`, `checkout_git_commit`, `checker_commit`,
  `spec_commit`, `lean4lean_commit`, `describe`, `sources`. "What produced
  it" is `frontend`, `toolchain`, `toolchain_family`, `tools`, `profile`.
  Nine and five spellings, for two concepts §5.4 states in one sentence.

`es-m2-census.json` carries **no source stamp of any kind**, while the same
lane's other instrument (`es_census.py`) stamps `sources` with git
revisions — and both landed on the same day
(`git log --diff-filter=A --format=%ad --date=short -- harness/es_census.py harness/es_m2_census.py`).
The contract did not travel between two files by one lane in one day.

**(d) The double-run clause is prose everywhere and code nowhere.**

    grep -rlnE '\-\-twice|double_run|run_twice' harness/ extractors/ tools/    # -> nothing

versus `harness/c_construct_census.py:44`, `harness/ada_suite_census.py:46`,
`harness/es_m2_census.py:40`, `extractors/sv/census.py:799`, and eight
doc sites, all *asserting* byte-identity. Determinism is a property of the
code, so the assertions are probably true — but §5.4 asks for **verified**,
and "verified" here means a lane ran it twice by hand once, in a state
nobody recorded, which is exactly what §5.4a exists to stop.

### 1.3 PROPOSAL — `harness/censuskit.py`, the contract once

~160 lines, stdlib only, exporting what all fourteen already hand-write:

```python
class Refusal(Exception): ...              # the one class, the one docstring
def provenance(path) -> dict               # git rev + describe + dirty; REFUSES, never None
def canonical(obj) -> str                  # json.dumps(indent=2, sort_keys=True) + "\n"
def run(argv, *, census, self_test=None,   # the whole §5.4 CLI in one call
        name, out_default=None)            #   -o/--output  (one spelling)
                                           #   --compare  -> 0 same / 1 drift / 2 missing
                                           #   --self-test
                                           #   --twice    -> runs census() twice, byte-compares
```

`run()` fixes the exit codes once (0 agree / 1 drift / 2 refusal), the
output flag once (`-o/--output`; the tree currently has **11 `--output`, 5 `--out`
and 16 `-o`**, `grep -hoE '"--?(o|out|output)"' <the 21 files>`), the refusal print once, and
makes `--twice` real for every instrument that adopts it.

**Price.**

| | lines |
| --- | ---: |
| new `harness/censuskit.py` | +160 |
| removed from 14 instruments (the ~520 generic block, less ~60 that stays as per-tier `--compare` key lists) | −460 |
| **net** | **≈ −300** |

**Migration: on touch, never in a sweep.** The next time a lane opens its
instrument for any reason, it converts *that* instrument, in the same
landing, and its `--compare` output must be byte-identical before and after
(that is the test — the committed JSON does not move). Cost ≈ 20 minutes
per instrument. Fourteen instruments, no deadline. The three broken
`--compare` exit codes are the exception: those are a **bug fix**, land
them ahead of any migration, three one-line changes.

**What does NOT move into the kit:** the corpus walk, the classifier, the
self-test *fixtures*, the tier's `--compare` key list. Those are the tier,
and §2.4 says thin siblings.

---

## 2 THE TRIAD SCRIPT, implemented 6 times — and the protocol is only prose

### 2.1 The measurement

**Zero tracked files implement the build lock.**

    grep -rln 'ls-build.lock\|ls-build-queue\|LEAN_NUM_THREADS' . | grep -v '^\./\.git/'
    # -> docs/backlog.md, docs/family-architecture.md, docs/lean-tier-charter.md

All three are prose. The repository's own CI entrypoint, `tools/ci.sh`,
runs `lake build` at line 21 **with no lock acquisition at all**.

The implementations live in the scratchpad — the location §7.1a says a
protocol must not live in. Six of them, **382 lines**:

    wc -l <scratchpad>/{ctier-triad,es-build,leantier-inch2,locked_triad,pyc_triad,runtriad}.sh
    #  77  107  75  35  70  18

### 2.2 The compliance matrix

`✓` implements, `✗` violates, `·` not applicable.

| amendment | ctier (77) | es (107) | leantier (75) | merged (35) | pyc (70) | basecase (18) | ✓ |
| --- | :-: | :-: | :-: | :-: | :-: | :-: | ---: |
| A9 FIFO ticket queue | ✓ | ✓ | ✓ | ✗ bare spinlock | ✓ | ✗ bare spinlock | 4/6 |
| A9 only the oldest mkdirs | ✓ | ✓ | ✓ | · | ✓ | · | 4/4 |
| A4 owner under `set -C` | ✗ plain `>` | ✓ | ✓ | ✗ plain `>` | ✓ | ✓ | 4/6 |
| A5 owner is `<lane> <pid>`, pid LAST | ✓ | ✓ | ✗ | ✓ | ✓ | ✓ | 5/6 |
| A7 release is owner-conditional | ✗ flag-guarded | ✓ | ✗ unconditional | ✓ | ✓ | ✗ unconditional | 3/6 |
| A10 owner pid spans the tenure | ✓ | ✓ | ✓ | ✓ | ✗ child pid | ✗ child pid | 4/6 |
| A11 `LEAN_NUM_THREADS=2` | ✓ | ✓ | ✗ `=4` | ✓ | ✓ | ✓ | 5/6 |
| A11 `nice -n 19` | ✓ | ✓ | ✗ `-n 10` | ✓ | ✓ | ✓ | 5/6 |
| A11 RSS kill line | ✓ | ✗ dead | ✗ absent | ✓ | ✗ absent | ✗ absent | 2/6 |
| base 6 kills by PARENTAGE | ✗ string match | ✗ direct children only | · | ✗ `lsof` cwd match | · | · | 0/4 |
| A8 atomic re-read before `rm` | ✓ | ✗ | ✗ | · | ✗ | · | 1/4 |
| base 2 exit 143 = resource kill | ✓ | ✗ unreachable | ✓ | ✗ | ✗ | ✗ | 2/6 |
| **violations** | **3** | **3** | **6** | **4** | **4** | **4** | **24 / 63** |

**38% of the applicable cells are violations, in six scripts written by
lanes that had all read §7.**

Three of them are worth naming because they are not sloppiness, they are
what hand-implementation does:

* **`leantier-inch2.sh:41`** writes
  `echo "$LANE lake pid $$ (inch2 lean4lean)" > "$LOCK/owner"`. Its last
  whitespace-separated field is `lean4lean)`. This is, character for
  character, the defect §7.1 rule 5 documents as the Go lane's — *"has
  `lean-go)` as its last field, so the pid parse yields a non-numeric
  string"* — reproduced by a different lane after the rule was written
  down.
* **`es-build.sh:98`** guards RSS with `pgrep -P $BUILD_PID lean`, where
  `BUILD_PID=$!` of `nice -n 19 lake build 2>&1 | tail -6 &` — i.e. the pid
  of **`tail`**. No `lean` will ever be its child. The same line means
  `wait $BUILD_PID` returns `tail`'s status, so `[ "$BE" -lt 128 ]` can
  never see the build's 143 either: **the guard cannot fire and the
  resource-kill retry cannot trigger**, and both read as present.
* **`pyc_triad.sh:57`** sets `OWNER_TAG="$LANE $LAKE_PID"` — the child
  stage's pid, which is amendment 10's exact wording (*"never a child
  stage's"*). Amendment 10 was recorded the same day.

And §0's finding 3 is the consequence: two builds ran concurrently for 48
minutes. The mechanism the script text supports — stated as **inference**,
not measurement — is that a lock the C lane held was removed by an exiting
script with an unconditional release, after which `es-build.sh`'s `mkdir`
succeeded and overwrote the owner identity. Two of the six scripts release
unconditionally. That is the failure amendment 7 was written to prevent.

### 2.3 The register is already one amendment behind its own birth

    git log --format='%h %ad %s' --date=format:'%m-%d %H:%M' -6
    # 76cd043 08-22 16:48 Section 7 becomes the build protocol's only durable home
    # 13eff7f 08-22 16:46 Lean tier: amendment 11 lands on the two places it actually bites

§7.1a's table lists base 1-6 and amendments 1-10. **Amendment 11 is not in
it** — it is recorded in a `docs/backlog.md` narrative paragraph (line
20775) and in `docs/lean-tier-charter.md:896`. The register commit landed
**two minutes after** the amendment-11 commit and did not carry it. Three
more amendments (1, 3, 8) are marked LOST.

So the durable home carries **8 of 12** rules. A prose register can be one
amendment behind and look complete; **a script cannot** — a missing
amendment in a script is a diff.

> **SINCE FIXED, and by the mechanism this section argues for.** The
> family-architecture lane completed the register at `cd0a722`: thirteen
> amendments, none LOST — and **amendment 8's text was RECOVERED FROM
> `tools/triad.sh`'s header**, the script landed with this audit. A rule
> that no prose source retained was read back out of the code that
> implements it. That is the whole case for "the doc describes, the script
> IS", made by the register itself within the hour.

### 2.4 PROPOSAL — `tools/triad.sh`, LANDED WITH THIS DOCUMENT

In the repository, versioned, so a protocol amendment becomes a commit that
every lane gets by rebase. 381 lines, `bash -n` clean, `--self-test`
green (12 checks), exercised end-to-end in a sandbox
(`LS_LOCK`/`LS_QUEUE` overrides) for acquire, FIFO wait behind a live
holder, stale-ticket reap, and clean release.

Shape: `enqueue-ticket → sweep-stale → wait-oldest → mkdir → owner under
set -C (script pid, pid LAST) → RSS watchdog over our own descendants →
throttled build → gates → owner-conditional release + ticket removal in a
recursive-kill trap`.

The parts that exist because the six scripts got them wrong:

* `descendants()` — one `ps -eo pid,ppid`, then a BFS. Kills are by
  **parentage** and **recursive**, so a lane can neither touch a sibling's
  chain (base rule 6) nor miss a grandchild (`pgrep -P`'s gap).
* `now_ns()` — normalises to **19 digits** from `date +%s%N`, else
  `python3 time_ns`, else `date +%s` padded, and refuses rather than
  enqueue an unsortable ticket. BSD `date` prints a literal `N`; the queue
  sorts lexicographically, so a mixed-width stamp orders the queue
  backwards.
* `lock_is_stale()` — the **two-part** test (owner pid alive AND a live
  `lean`/`lake`/`gprbuild` descends from it), and an **unparseable owner
  returns NOT stale**. §7.1's own warning is that a broken liveness check
  *"falls forward into reclaiming a lock somebody is holding"*.
* `sweep_stale_tickets()` — A8's atomic re-read: existence and liveness are
  both re-checked immediately before the `rm`, never from the listing.
* a torn-tree precondition — refuses to start when `.git/rebase-merge`,
  `.git/rebase-apply`, `MERGE_HEAD` or `CHERRY_PICK_HEAD` exists (§7.2:
  *"a red from a torn tree is not evidence of anything"*).
* a **positive** success assertion — `grep -q 'Build completed
  successfully'`, because an argument error and a resource kill both emit
  no line the failure greps look for.
* `--self-test`, which is §5.4's *every refusal path RUN, not admired*
  pointed at the script itself, and needs no Lean at all.

**Price.** +381 lines in the repo, −382 lines of scratchpad scripts as
lanes adopt, and the amendment register gains a second, executable home.
**Adoption is per-lane on dispatch** — a lane replaces its script with
`tools/triad.sh --lane <name> --dir <clone> --gates "…"` at its next
tenure, and reports whether the tenure behaved. No lane is switched over by
this landing.

**What it does not fix.** It cannot make a lane run it. §0's finding 3 was
a live violation; a script in the repo is a smaller invitation to
improvise than a paragraph in a 2,800-line document, but it is not a
mechanism. The mechanism, if one is wanted later, is a pre-push check that
refuses a landing whose triad was not taken through the script — priced
here at ~30 lines and **not proposed**, because it needs Thomas's ruling
before a lane's landing can be blocked by a tool.

---

## 3 ENVELOPE LOADERS — four tiers, one command

### 3.1 The measurement

    wc -l LeanModels/{C,Es,Ada}/Load.lean          # 83 87 118
    norm() { sed -E 's/load_(c|es|ada)_program/load_X_program/g; s/LeanModels\.(C|Es|Ada)/LeanModels.X/g' "$1" \
             | sed -n '/^open Lean Elab Command in/,/^end /p'; }
    diff <(norm LeanModels/C/Load.lean) <(norm LeanModels/Es/Load.lean) | grep -c '^[<>]'   # 14

The `elab` bodies are 46 (C), 44 (Es) and 61 (Ada) lines. **C and Es differ
by 14 lines out of 46** once the tier name is normalised away — and those
14 are entirely the *refusal list* (C checks `language` + `profile_id`; Es
checks `schema_version` + `language_version`). The other ~32 lines —
`IO.FS.readFile` with the cwd-explaining error, `parseEnvelopeString`,
already-declared check, `addAndCompile` of a `.defnDecl` with
`hints := .abbrev`, `enableRealizationsForConst`, `addDocStringCore`,
`Term.addTermInfo'` — are the same code three times.

The JSON layer repeats too. Primitive helpers per tier:

| tier | file | helpers | lines | names |
| --- | --- | ---: | ---: | --- |
| C | `LeanModels/C/Json.lean` | 11 | 70 | `withCtx getField getStr getNat getOptStr getOptNat getArr getOptNode getBool parseSpan nodeSpan` |
| Ada | `LeanModels/Ada/Json.lean` | 8 | 58 | `withCtx getField getStr getNat getStr? getArr mapIdx parseSpan` |
| Es | `LeanModels/Es/Json.lean` | 7 | 43 | `withCtx getField getStr getNat getArr parseSpan parseErrorPos` |
| Sv | `LeanModels/Sv/Json.lean` | 7 | 34 | `withCtx getField getOptField getStrField getNatField getBoolFieldD getKind` |
| Python | `LeanModels/Python/Json.lean` | 4 | 22 | `withCtx getField getOptStrField parseSpan` |
| | | **37** | **227** | |

`withCtx` and `getField` are written five times. The optional-string
accessor is `getOptStr` (C), `getStr?` (Ada), `getOptStrField` (Python) —
three names, one function. `getArr` returns `List Json` in C and
`Array Json` in Ada and Es. Sv suffixes everything `Field` and takes
`List String` alternatives.

### 3.2 The span finding, and it is the one that inspires a design

§3.7 measured **three** span types for seven lanes and ruled that `Span`
stays in `Core` as the family's span *"with the docstring corrected to
state the contract rather than its Python provenance."* Today:

    grep -rn "structure .*Span" LeanModels/

| type | fields | lanes |
| --- | --- | --- |
| `LeanModels.Span` | `lineno colOffset endLineno endColOffset` | **Python only** |
| `LeanModels.C.CSpan` | `line col endLine endCol` + `macroLine? macroCol?` | C |
| `LeanModels.Ada.AdaSpan` | `line col endLine endCol` | Ada |
| `LeanModels.Es.EsSpan` | `start stop line col endLine endCol` | Es |
| `LeanModels.VerilogA.Span` | `line column` | Verilog-A |
| `LeanModels.Circuit.Spice.SourceSpan` | `line` | Spice |

Six, not three. `LeanModels/Core/Basic.lean` is **13 lines** and imported by
four files, all Python or C (`grep -rl "import LeanModels.Core"`); its
docstring still opens *"Field names mirror CPython's `ast` attributes"*, so
the correction §3.7 ordered has not landed.

The Ada lane's rationale is explicit and correct on its own terms
(`LeanModels/Ada/Ast.lean:58`): *"that `Span` is the Python lane's, with
Python's own field names … and `LeanModels/Ada/` is a SIBLING of
`LeanModels/Python/`, never a client."* It is right, and the design that
follows is not "stop declaring spans" — it is:

> **Three lanes independently chose `line/col/endLine/endCol`. That
> agreement is a measurement of what the neutral names should be.**
> `Core.Span` should be renamed to them, C's `macro*` pair is §3.7's own
> named model for EXTENSION, and Ada's type then has nothing left in it.

### 3.3 PROPOSAL — a `Core` loader utility, and nothing more

Two pieces, both small, both leaving the tier types alone.

**(a) `LeanModels/Core/Json.lean`** (~60 lines): `withCtx`, `getField`,
`getStr`, `getStr?`, `getNat`, `getBool`, `getArr` (as `Array`, the
majority), `getList`. Tiers `open` it and keep their own `parseSpan`,
`parseNode`, `parseEnvelope`. Saves ~120 of the 227 primitive lines.

**(b) `LeanModels/Core/Load.lean`** (~45 lines): one
`loadEnvelopeCommand` helper taking the parser, the accepted-schema
predicate, and the doc-string renderer, so a tier's `Load.lean` shrinks to
its `deriving ToExpr` block, its refusal list, and one call. Saves ~90 of
the 288 loader lines.

**Not proposed: `deriving FromJson`.** `docs/lean-structures-census.md`
makes it available, and it is the wrong tool here — the tiers do not want
a *decoder*, they want **refusals in the tier's own vocabulary** (Ada reads
the 280-kind census at elaboration time and refuses an out-of-vocabulary
kind by name; C refuses a profile; Es refuses an edition). A derived
`FromJson` gives a generic parse error where the tier's whole value is the
specific one. Keep the hand-written parsers, share the primitives.

**Price.** +105 lines in `Core`, −210 across five tiers, net **≈ −105**;
migration is per-tier and mechanical (~30 min each), on touch. The span
rename is a separate, larger change: it touches every `⟨_,_,_,_⟩` literal
in the Python lane and is **not** proposed here — it is proposed as a
backlog item with §3.7's ruling as its warrant.

---

## 4 BACKLOG CONTENTION — the incident count is unmeasurable, and that is the finding

### 4.1 What the history can and cannot say

    git log --oneline --follow -- docs/backlog.md | wc -l     # 251
    git rev-list --count HEAD                                 # 432
    git log --pretty=format: --name-only | sort | uniq -c | sort -rn | head -3
    #  251 docs/backlog.md   |   81 docs/memory-model.md   |   62 harness/cases.json

**58% of all commits touch one file**, and it is touched three times more
often than the next.

    git log --format='%ad' --date=short -- docs/backlog.md | sort | uniq -c | tail -3
    #  25 2026-08-19   |   22 2026-08-21   |   66 2026-08-22

On 2026-08-22 alone, **66 commits** landed in `docs/backlog.md`, which grew
from 796 KB / 13,547 lines to **1,260 KB / 21,050 lines** — **+58% in one
day**.

**Renumber incidents cannot be counted from history, and the reason is
structural.** A scripted scan for *"a heading whose title is unchanged and
whose `L`-number changed"* finds **0** events across all 251 commits. That
is not evidence of no races: §7.2's rule is *"read your own backlog section
at push time rather than at draft time"*, so the renumber happens **before
the push**, in the working tree, and the commit that lands carries only the
final number. **The fix erases its own evidence.**

What is measurable:

* section ordering: of 88 `## Lnn` sections, **one** (L30) landed after a
  higher number was already in the file — `git log --reverse` over the
  file, first-appearance order is `2,3,10,12…29,31,32,30,33,…88`.
* integrity today: **no duplicate numbers, no gaps** (1…88 complete), and
  **0 of 77 distinct `§Lnn` cross-references dangle**. The lanes are paying
  the tax and paying it correctly.
* **but the id scheme collides with itself.** `## L2`, `## L3` and `## L4`
  each appear more than once, because two different numbering systems share
  the letter:

  ```
  5155:## L2 — THE MODULE SYSTEM: CENSUSED AND STOPPED …            (2026-08-16)
  6045:## L2 LANDED — `GenYields` and the first generator theorem   (2026-08-17)
  6372:## L4 PARTIAL — the ray rules, the FIRST agreement leaf …    (2026-08-17)
  6525:## L4 REMAINDER — the round induction, the segment kit …     (2026-08-17)
  ```

  A `§L3` reference in this file is ambiguous between the class-tier ledger
  section and a generator-milestone entry. That is a live ambiguity, not a
  hypothetical.

### 4.2 The options, and the pick

| option | conflict rate | id stability | cost | reader's view |
| --- | --- | --- | --- | --- |
| status quo (one file, sequential `Lnn`) | every landing touches the tail | broken by rebase | 0 | one file |
| coordinator-assigned ranges (`L100-L119` = Ada …) | tail contention unchanged | stable | coordinator round-trip per lane | one file |
| date-based ids (`2026-08-22-ada-1`) | tail contention unchanged | **stable, no reservation** | 0 | one file |
| **per-lane files + generated index** | **near zero** | stable | +1 tool, +1 gate | index must be built |

**Pick: per-lane files, with date-based ids inside them.**
`docs/backlog/<lane>.md`, one per lane, each lane appending only to its own
file; `docs/backlog.md` becomes a **generated** index — one line per entry,
newest first, with the id, title, date and a link. Ids become
`YYYY-MM-DD-<lane>-<n>`, assigned by the lane with no coordination at all,
because the lane name makes them unique by construction.

Reasons, in order:

1. It removes the conflict rather than sequencing it. Two lanes appending
   to two files never conflict; two lanes appending to one file conflict on
   every landing, and 66 landings a day is the rate.
2. It makes the id stable *by construction*, so §7.2's push-time re-read
   rule — the rule whose whole purpose is to survive a race — no longer has
   a race to survive.
3. It fixes the `L2`/`L3`/`L4` collision as a side effect: the lane name is
   in the id.
4. It generates the reader's view, which §5.5 already argues for in the
   clause manifest: *"generated and checked, never hand-maintained."*

**Price.** A ~60-line `tools/backlog_index.py` (a `censuskit` client, once
that exists) plus a `tools/ci.sh` step that regenerates and diffs the
index. Migration is **append-only and needs no history rewrite**: the
existing `docs/backlog.md` is renamed `docs/backlog/archive-L1-L88.md`
untouched, every `§Lnn` reference keeps resolving, and new entries go to
per-lane files from that commit on. One landing, ~1 hour. Every cross-file
reference in the tree that says `docs/backlog.md §Lnn` must be checked —
`grep -c 'backlog.md' docs/*.md` says where.

---

## 5 VERDICT ROWS — divergence is real, but the VOCABULARY drift is not

The honest answer is a split one.

### 5.1 What was measured

    for f in harness/diff_test.py harness/library_survey.py harness/refusal_census.py \
             harness/lean_independent_check.py harness/leanpy_survey.py harness/sv/diff_test.py \
             harness/spice/diff_test.py; do
      echo -n "$f: "; grep -hoE '"(MATCH|MISMATCH|DIVERGED?|REFUSED?|TIMEOUT|WHITELISTED|ERROR|PASS|FAIL)"' $f | sort -u | tr '\n' ' '; echo; done

| emitter | vocabulary |
| --- | --- |
| `harness/refusal_census.py` | `MATCH REFUSE DIVERGE TIMEOUT` + `ERROR` |
| `harness/leanpy_survey.py` | `MATCH REFUSE DIVERGE TIMEOUT` |
| `harness/lean_independent_check.py` | `MATCH REFUSE DIVERGE TIMEOUT` |
| `harness/library_survey.py` | `MATCH REFUSED DIVERGE` `TIMEOUT` *(was `DIVERGE`/`DIVERGED`; fixed 2026-08-22, python-completeness lane)* |
| `harness/diff_test.py` | `MATCH MISMATCH WHITELISTED ERROR` |
| `harness/spice/diff_test.py` | `MATCH MISMATCH` |
| `harness/sv/diff_test.py` | `PASS FAIL` |

§5.1 fixes four names. **Three of seven emitters use none of them for the
failure case**, and one emitted both `DIVERGE` and `DIVERGED`
(`harness/library_survey.py:637` mapped one to the other, which was the
tell). **That one is FIXED** — the translation at the emission boundary is
deleted, the direct set and its detail string say `DIVERGE`, and the six
consumers that keyed on the drifted name (scoreboard order, the title
pairing, both exit gates) follow it; the gates still fail on `DIVERGE` or
`INCOMPLETE` and pass otherwise, so §5.4's both-directions discipline is
preserved. The remaining two emitters are untouched here.

Row *shapes*, where they exist:

| emitter | row |
| --- | --- |
| `lean_independent_check.py:123` | `{module, verdict, exit_code, seconds, detail}` |
| `refusal_census.py:925` | `{id, verdict, detail, …}` |
| `library_survey.py:684` | `{verdict, detail, …}` |
| `c_suite_census.py:171` | `{test, status, kinds, outside_vocab, …}` |

### 5.2 The answer

**A shared full row is NOT warranted.** The extensions are genuinely
different in kind: Ada's grading is membership in a set of ACATS markings
(`docs/ada-charter.md:537`, six marking classes with different pass rules),
ES's pass condition is *not throwing* over 4,248 negative tests, C's suite
row carries `outside_vocab`, and §5.1's own membership ruling says the
permitted set is *"a per-site datum the tier carries"*. Flattening those
into one schema would be the thick-trunk mistake §2.4 already ruled
against.

**A shared verdict VOCABULARY is warranted, and is already law.** §5.1
fixes `MATCH | REFUSE | DIVERGE | TIMEOUT`; §5.2 fixes the four REFUSE
causes; §5.3 says a vacuous run is an instrument ERROR and not a verdict.
Three emitters have drifted from a law that already exists — this is not a
design question, it is a **conformance gap**.

**Proposal (small, and it is the one that pays):** `censuskit` exports

```python
VERDICTS = ("MATCH", "REFUSE", "DIVERGE", "TIMEOUT")
REFUSE_CAUSES = ("unsupported", "undefined", "environment", "order-dependence")
def row(id, verdict, *, detail="", live=True, cause=None, **extra) -> dict
```

`row()` rejects an unknown verdict, requires `cause` when the verdict is
`REFUSE` (§5.2), and carries §5.3's `live` flag so a vacuous run cannot be
serialized as agreement. Everything else goes in `**extra`, untouched and
per-tier. **+15 lines; three emitters to convert on touch.** The
`MISMATCH`/`PASS`/`FAIL` emitters are *older than the law* — `diff_test.py`
is the Python lane's original harness — so converting them is a rename plus
a whitelist-semantics decision (`WHITELISTED` is not a §5.1 verdict; it is a
known tier gap, which is `REFUSE`/`unsupported` with a note). That decision
is the Python lane's and is **not** taken here.

---

## 6 WORKSPACE AND RECOVERY — and the 42 GB is not what it looks like

This is the item where measurement changed the recommendation.

### 6.1 The disk, measured

    for d in <scratchpad>/lean-* ~/repos/lean-*; do printf "%s\t" "$d"; du -sk "$d" | cut -f1; done

| clone | total | `.lake` |
| --- | ---: | ---: |
| `lean-ctier2` | 7.90 GB | 7.86 |
| `lean-basecase` | 7.86 | 7.82 |
| `lean-merged` | 7.86 | 7.82 |
| `lean-es` | 6.25 | 6.17 |
| `lean-pyc2` | 6.21 | 6.14 |
| `~/repos/lean-ada` | 6.13 | 6.06 |
| `~/repos/lean-surfaces` | 6.17 | 6.10 |
| `lean-arch2`, `lean-leantier`, `lean-sv`, `lean-audit` | 0.04 each | — |
| **13 clones** | **≈ 48.8 GB apparent** | **47.97** |

**A source-only clone is 40 MB.** Every gigabyte above that is build cache.

Now the decomposition, and it is the finding:

    du -skx <clone>/.lake/*
    #   0.43 GB  .lake/build        <- this repository's own oleans
    #   7.39 GB  .lake/packages
    du -skx <clone>/.lake/packages/*
    #   7.02 GB  mathlib            <- 89% of the cache

And the six caches are the **same** mathlib:

    for d in …; do git -C $d/.lake/packages/mathlib rev-parse --short HEAD; cat $d/lean-toolchain; done
    # 79d0395a18  leanprover/lean4:v4.33.0-rc1   × 6

> **The duplicated 42 GB is one immutable, pinned, byte-identical
> dependency — `mathlib @ 79d0395a18`, the revision `lake-manifest.json`
> pins — copied six times. The lanes' own divergent build output is 0.43 GB
> each.**

### 6.2 CoW, measured first-hand

    SRC=<clone>/.lake/packages/mathlib/.lake ; DST=<scratch>/cowtest
    df -k /System/Volumes/Data ; time cp -Rpc $SRC $DST ; df -k /System/Volumes/Data ; du -skx $DST

* size copied: **6.42 GB** (`du` on the copy agrees: 6.42 GB)
* elapsed: **27 s**
* real disk consumed (`df` delta): **29 MB — 0.4%**

APFS block sharing works exactly as the SV lane reported. Two consequences,
and the second is a warning:

1. Seeding a new cache from a warm peer costs **27 seconds and ~0 bytes**.
2. **`du` cannot tell shared blocks from unique ones**, so the 48.8 GB
   above is an *apparent* figure. The evidence that these six were NOT
   shared is Thomas's own: trimming two clones returned **14 GB**, against
   an apparent 14.1 GB for those two — a clone that shared its blocks would
   have returned a fraction of that. They were built or downloaded
   independently, which is precisely what breaks sharing.

The re-warm tax, from the ledger rather than re-measured:
`cp -Rc` **without `-p`** loses mtimes and Lake re-elaborates from cold —
one lane measured *"~8 oleans per several minutes"* (`docs/backlog.md:11661`); `lake exe cache get` restored 5,969 files in
**13 s** against *"an estimated five hours"* of compilation
(`docs/backlog.md:12074-12075`); a cold full rebuild is quoted at **~37 minutes**
(`docs/backlog.md:20789`).

### 6.3 The branch trap is not folklore; it is the current state

    for d in <scratchpad>/lean-* ~/repos/lean-ada; do
      printf "%-14s %-22s %s\n" $(basename $d) \
        "$(git -C $d rev-parse --abbrev-ref HEAD)" \
        "$(git -C $d rev-list --left-right --count HEAD...origin/master | tr '\t' '/')"; done

| clone | branch | HEAD…origin/master |
| --- | --- | --- |
| `lean-es` | **`pyrebuild-monadic`** | 244/0 |
| `lean-pyc2` | **`pyrebuild-monadic`** | 238/0 |
| `~/repos/lean-ada` | `master` | 242/0 (stale remote ref) |
| `lean-sv` | `master` | 0/2 (behind) |
| others | `master` | 0/0 |

Two lane workspaces are sitting on the branch §L86 names as the trap, and a
third has a remote-tracking ref 242 commits behind reality. §L86's rule —
*"VERIFY `git remote -v` AND the branch's upstream before committing in a
clone you did not create"* — is being enforced by memory.

**One correction to the record, because an audit that only confirms is not
an audit:** §L86 states that `~/repos/lean-surfaces`'s `origin` is a stale
local bundle. It is not, today —
`git -C ~/repos/lean-surfaces remote -v` shows both `origin` and `github`
pointing at `git@github-work:thomasnormal/lean-surfaces.git`. That half of
the incident has been fixed; the branch half has not.

### 6.4 THE THREE OPTIONS, priced

**(A) Status quo + mandatory CoW seeding.** Every new clone is
`cp -Rpc`'d from a warm peer; a periodic re-seed after divergence.

* disk: 6 caches → **~7 GB real + ~30 MB per extra lane**, measured above.
* time: **27 s** per lane workspace.
* risk: **none new**. No protocol change, no shared writer, no
  branch-switch, no torn-tree exposure. Each lane keeps its own tree and
  its own timing.
* residual: a lane that runs `lake exe cache get` in a fresh clone instead
  of seeding re-breaks sharing (that is how the 42 GB happened), so this is
  a *discipline*, and discipline is what §2 just measured going wrong six
  times — which is why it must be a **script**, not a paragraph.

**(B) Shared `.lake/packages`.** All lanes point at one packages
directory (symlink, or `packagesDir`), because the manifest pins one
revision and no lane ever writes it.

* disk: **~7 GB total, once**, for any number of lanes.
* risk: two lanes writing the shared directory concurrently — *except that
  amendment 11 already makes Lean execution single-tenant*, so the ticket
  **is** the writer serialization. The real risk is a lane bumping the
  mathlib pin: then the shared directory is rebuilt under one tenure and
  every lane's next build sees the new revision, which is correct but
  surprising, and must be announced.
* cost: one line per clone, plus a paragraph. Needs a verification run
  (does this Lake accept a symlinked `packagesDir`? — **untested**, and it
  needs a Lean run, so it is out of this audit's scope by Amendment 11).

**(C) One shared build workspace granted with the ticket.** Thin per-lane
source clones (**40 MB**, measured); the tenant checks out its branch into
the single build clone, builds against one warm cache, gates, releases.

* disk: **~8 GB**, the theoretical floor.
* but the measurement removes most of its motivation: it buys **0.43 GB per
  lane** over option B, because 89% of what it deduplicates is already
  deduplicated by B, and it charges for that:
  * **a checkout per tenure**, inside the tenure, which puts a working-tree
    mutation and a build in the same critical section — the exact adjacency
    §7.2's torn-tree rule exists to forbid;
  * **olean invalidation when tenants alternate.** Divergence is genuinely
    low — over the last 40 landings the `.lean` edits are tier-scoped
    (`es,Es` / `Sv` / `ada,Ada` / `c,C` / `python`, one area per commit),
    and the spine moves rarely: `LeanModels.lean` 8 times in 60 commits,
    `lakefile.toml` 3, `lean-toolchain` 1, `Core/Basic.lean` 1. But
    `LeanModels.lean` imports every tier, so a spine touch invalidates
    everyone, and 8-in-60 is not rare enough to ignore;
  * **it serializes editing against building.** Today a lane edits while
    another builds. Under (C) the build workspace is the only place a lane's
    edits can be *tested*, so the queue depth becomes the edit-feedback
    latency for the whole family.

### 6.5 RECOMMENDATION — (A) now, (B) next, (C) not yet

Land **`tools/workspace.sh`** (proposed, not written — it should follow
`tools/triad.sh`'s adoption so the family does not absorb two new scripts
at once), ~80 lines:

```
tools/workspace.sh new <lane> [--from <warm-peer>]
    git clone --shared / or a fresh clone, then cp -Rpc <peer>/.lake
    verify: origin is the real remote AND the branch's upstream is master
    refuse if <peer> has a build running (ps by parentage) or a torn tree
tools/workspace.sh check [<dir>]
    print remote, upstream, ahead/behind, .lake provenance; nonzero if any
    of §L86's three traps is present
tools/workspace.sh reseed <dir> --from <warm-peer>
    re-establish block sharing after divergence, under the build lock
```

`check` is the piece worth having first: it is 20 lines, it needs no
network, and run today it flags `lean-es` and `lean-pyc2` immediately.

Then **(B)**, once someone can spend one Lean run confirming Lake's
behaviour with a shared `packagesDir`. **(C) is not recommended**: it costs
0.43 GB per lane over (B) and buys a torn-tree adjacency, a spine-touch
invalidation, and edit-latency coupling. Revisit it only if `.lake/build`
grows past ~2 GB per lane, which is the number at which its arithmetic
changes.

---

## 7 LAWS VERSUS PRACTICE — three lanes' latest landings

Sampled: `31583c8` (ES M2 inch 2), `417e585` (Ada M1 inch 6), `13eff7f`
(Lean tier, amendment 11), each against §5.4, §5.4a and §7.

**§5.4a (provenance) is being followed unusually well.** All three commit
messages state what was measured, in what state, and — the harder half —
what was *not* run. `b2e23f5` is the model: *"the confirming triad is
WITHDRAWN, not run"*, with the reason, the queue position, and the explicit
judgement offered *"so it can be disagreed with"*. `13eff7f` says *"Docs
only. No Lean run, no build, no ticket taken."* `417e585` reports
non-vacuity as deltas (*"SubpDecl 15->16, markings 12->13"*), which is the
law's stronger form.

**§5.4 (instrument pattern) is drifting at the edges, in one direction:
newer instruments carry less of it.**

| clause | ES lane's newest | Ada lane's newest | Lean lane's |
| --- | --- | --- | --- |
| `harness/<lang>_<subject>_census.py` → `docs/<lang>-<subject>-census.json` | ✓ | ✓ | ✓ |
| `--compare` | ✓ | ✓ | ✓ |
| every refusal path RUN | ✓ (`es_census --self-test`, 6 paths) | ✓ (`ada_construct_census --self-test`, 8 checks) | ✗ no `--self-test` in any of the four Lean instruments |
| double-run byte-identical, **verified** | ✗ claimed in the docstring | ✗ claimed in the docstring | ✗ |
| every number paired with its STATE | ✗ **`docs/es-m2-census.json` has no provenance key at all** | ✓ (`frontend`, `corpus`) | ✓ (`toolchain`, `commit`) |
| stamps frontend family + profile | ✗ | ✓ | ✓ (toolchain) |

`harness/es_lean_lint.py` (new in `31583c8`) is deliberately excluded: it is
a **gate**, not a census, so §5.4 does not bind it — and it carries a
`--self-test` anyway, and its docstring records that its first rule list was
wrong and was corrected *by running the toolchain*, which is §5.4's
"executed, not admired" applied without being asked.

**§7 is the drift that matters**, and §2 is the evidence: 24 violations
across six scripts, amendment 11 missing from its own durable home, and a
live two-build violation while this was written.

---

## 8 TOP THREE, ordered by leverage

**1. `tools/triad.sh` — adopt it, lane by lane.** Landed here. It is first
because §7 is the only law whose violation takes the machine down, because
the violation was live during the audit, and because it is the one
duplication where the *shared* implementation already exists and only
adoption remains. Cost per lane: one dispatch, one tenure. **Leverage:
24 measured violations → 0, and the amendment register gains a home that
cannot silently fall behind.**

**2. `tools/workspace.sh check`, then CoW seeding.** ~20 lines for the
check, ~60 more for `new`/`reseed`. It flags two lanes' branch trap today
and turns the 42 GB into ~30 MB per lane at 27 s a clone — a measured
99.6% reduction with **no protocol change and no new risk**. It is second
only because disk is not yet failing; at 91% full on the data volume, that
is a matter of days.

**3. `harness/censuskit.py`, migrate-on-touch — but fix the three
`--compare` exit codes FIRST, as a bug, today.** The three-line fix is
independent of the kit and should not wait for it. The kit's own leverage
is not the ~300 net lines; it is that `--twice` becomes real for every
instrument, provenance stops degrading silently in four places, and §5.1's
verdict vocabulary gets a place to be enforced instead of remembered.

Below the line, in order: the `Core` JSON/loader utilities (§3.3, net −105,
mechanical); per-lane backlog files (§4.2, one hour, removes a conflict
class); the `Core.Span` field rename (§3.2 — §3.7 already ruled it, three
lanes have already voted on the names, and it is the largest of these).

---

## 9 WHAT THIS AUDIT GOT WRONG, recorded because §5.4a cuts both ways

While exercising `tools/triad.sh`'s ownership-trap path, this lane ran the
script **without `--dry-run`**, which took its sandbox lock and then ran
`lake build` in `~/repos/lean-audit` for roughly two minutes before the
harness timed the command out. It took **no real ticket and no real lock**
— `LS_LOCK`/`LS_QUEUE` were pointed at a temp directory — so it ran Lean
outside the machine-wide lock, which is an **Amendment 11 violation by this
lane**. The clone had no cache, so the time went to fetching mathlib
sources rather than to elaboration. Cleanup was verified: the accidental
`.lake` (**634 MB**) was removed, `pgrep -fl triad.sh` shows no process of
this lane's, and the four `*triad*.sh` processes on the box are other
lanes' and were not touched (base rule 6).

Recorded here rather than omitted, for the same reason §5.4's third bullet
exists: **the refusal path that is only designed is not one, and the
incident that is only regretted is not measured.** The A7 ownership-trap
path is consequently the **one** path in `tools/triad.sh --self-test` that
is asserted structurally rather than executed end-to-end; closing it needs
a tenure that runs no Lean, and is the first thing to do when the script is
next opened.


---

## 10 THE BUG FIX — seven implementations, verified 2 x 7

Dispatched by the coordinator as *bug before refactor*, from §8's own
recommendation. **Pure Python, no Lean, no ticket.** The censuskit refactor
(§1.3) was NOT started: it stays migrate-on-touch for the owning lanes.

**(a) `--compare` must exit 1 on drift.** Three instruments printed the
delta and returned 0.

**(b) A failed revision lookup must refuse, never stamp null.** Four copies
of one `git rev-parse` swallowed every failure. They now raise the file's
own refusal class, which the existing `main` catches and reports as exit 2
— and, verified below, **no artifact reaches disk on that path**, so a
null-stamped census can no longer be committed.

One extra hole was found while verifying (a) and had to be closed for the
mandated test to mean anything: `c_construct_census.compare()` returned
early on a matching **source sha256**, so a census that differed for the
same input — a moved frontend, a changed instrument, a hand-edited artifact
— printed `UNCHANGED` and exited 0. The early return now fires only on a
byte-identical census, and a same-source/different-census pair is reported
as drift in its own right.

### The verification table

Fixtures (built fresh, `<V>` = the scratchpad's `verify/`): a 3-line C
translation unit; a git checkout with `specification/wasm-3.0/a.spectec`; a
git checkout with `test/core/a.wast`; a git checkout with `src/**/*.mts`; a
lake package with a **stub `lake` on `PATH`** so the Lean instrument's own
path runs with **zero Lean executed**. The `-nogit` variants are copies with
`.git` removed.

| # | fix | direction | command (abbreviated) | before | after |
| --- | --- | --- | --- | :-: | :-: |
| A1 | `c_construct_census.py` `--compare` | agree | `… fixture.c --compare c-base.json` | 0 | **0** ✓ |
| A1 | | **drift** | `… fixture.c --compare c-bad.json` | **0** ✗ | **1** ✓ |
| A2 | `wasm_spec_census.py` `--compare` | agree | `… <V>/wspec --compare ws-base.json` | 0 | **0** ✓ |
| A2 | | **drift** | `… <V>/wspec --compare ws-bad.json` | **0** ✗ | **1** ✓ |
| A3 | `wasm_suite_census.py` `--compare` | agree | `… <V>/wsuite --compare wt-base.json` | 0 | **0** ✓ |
| A3 | | **drift** | `… <V>/wsuite --compare wt-bad.json` | **0** ✗ | **1** ✓ |
| B1 | `wasm_spec_census.py` `git_rev` | resolvable | `… <V>/wspec -o b1.json` | 0 | **0**, `revision=7b854e86…` ✓ |
| B1 | | **unresolvable** | `… <V>/wspec-nogit -o b1x.json` | **0**, `revision=None` ✗ | **2**, REFUSED, no file ✓ |
| B2 | `wasm_suite_census.py` `git_rev` | resolvable | `… <V>/wsuite -o b2.json` | 0 | **0**, `revision=11614693…` ✓ |
| B2 | | **unresolvable** | `… <V>/wsuite-nogit -o b2x.json` | **0**, `revision=None` ✗ | **2**, REFUSED, no file ✓ |
| B3 | `es_census.py` `rev` | resolvable | `… --engine <V>/esfix -o b3.json` | 0 | **0**, `engine262=c1e558cc…` ✓ |
| B3 | | **unresolvable** | `… --engine <V>/esfix-nogit -o b3x.json` | **0**, `sources={'engine262': ''}` ✗ | **2**, REFUSED, no file ✓ |
| B4 | `lean_independent_check.py` `checker_commit` | resolvable | `… --checker-dir <V>/leanfix --modules Init.Core` | 0 | **0**, `checker_commit=702e8110…` ✓ |
| B4 | | **unresolvable** | `… --checker-dir <V>/leanfix-nogit --modules Init.Core` | **0**, `checker_commit=""` ✗ | **2**, REFUSED, no file ✓ |

The `before` column is not reconstructed from reading — the pre-fix files
were extracted with `git show HEAD:harness/<f>.py` and run against the same
fixtures and the same perturbed JSONs.

**The B3 row is the one that was never hypothetical.**
`docs/es262-census.json` on master carries

    "sources": {"ecma262": "", "engine262": "c7939eaf…", "test262": "3655e746…"}

Two thirds provenanced, one third silently blank, from exactly this code
path. That is §5.4a's failure reading *cleaner than the truth*, sitting in a
committed artifact. **The fix does not repair that file** — re-deriving it
needs the ES corpora, which are not on this machine; the next `es_census
--spec` run will now refuse until the spec is censused from a checkout, and
that refusal is the finding, not a regression.

### Not changed, deliberately

* The **missing-baseline** dialect split stays: the Lean lane refuses with
  exit 2, Ada/ES/C/Wasm let `open()` traceback. That is one contract with
  four spellings and it belongs to §1.3's kit, not to a bug fix.
* No committed census JSON was touched (`git status` after the fix lists
  five `.py` files and nothing else).
* No instrument's output schema changed, so `--compare` against every
  committed artifact still agrees — the three `--compare` fixes move only
  the **exit status**.

Regression checks after the fix:
`c_construct_census.py --selftest` ok (6 stubs, `&automatic=2 &static=1`);
`es_census.py --self-test` ok (7 paths); `tools/docs_check.py` 83/83.

---

# AUDIT #2 — re-measured 2026-08-22, at `64ab535`

The dated second audit §9.7 requires: **FULL, about every ten landings, and
it re-measures its own headline numbers.** There have been **43 landings**
since audit #1 (`git rev-list --count f66b1ad..HEAD`). Same clone
(`~/repos/lean-audit`), fetch-rebased to master, `origin` verified as the
real remote on branch `master` tracking `origin/master`. Docs and shell
only; **no Lean executed**.

An audit that only confirms is not an audit, so the summary first: **five of
audit #1's six items moved in the right direction, one did not move at all,
and one defect class came back — in a file written three hours after the fix
that removed it.**

> **PIN, and one re-measurement.** Every number below was taken at
> `64ab535`. Two landings arrived during the write-up (`a7acd87`,
> `ad90bd2`) and moved two of them; rather than land a number whose state
> had already changed — §5.4a's whole point — both were re-measured at
> `ad90bd2` and are marked **RE-MEASURED** where they appear. Nothing else
> was re-run, and nothing else is claimed for that commit.

## 2.1 SCOREBOARD — every #1 headline, re-measured

| # | audit #1 | audit #2 | Δ |
| --- | --- | --- | :-: |
| private runner scripts | **6**, 382 lines | **1**, 74 lines | −5 |
| amendment violations in them | **24 / 63 cells (38%)** | **6 / 12 cells (50%)** | −18 total, +12pp density |
| lanes on a shared runner | **0** | **6** (live, by owner + `ps`) | +6 |
| `--compare` that cannot fail | **3 of 14** | **1 of 16** | −2 |
| provenance stamps that swallow | **4** | **1** | −3 |
| census instruments | 21 | 23 | +2 |
| `censuskit.py` | proposed | **absent (correct)** | — |
| durable amendments / in practice | **8 / 12** | **13 / 16** | +5 registered, still 3 behind |
| backlog: files / id schemes | **1 file**, colliding ids | **12 files**, 28 of 29 ratified ids | +11 |
| `SemM` definition sites | not measured | **13 sites, 5 spellings** | new |
| refusal-cause shapes | not measured | **4 spellings, 8 constructor names** | new |

## 2.2 (1) THE 38% — the population collapsed, the density did not

**Private scripts: 6 → 1.** The sweep retired four; `pyc_triad.sh` and
`runtriad.sh` are gone. The survivor is
`<scratchpad>/leantier-m3.sh` (74 lines, mtime **21:20**, i.e. written
**after** audit #1), and it re-hand-rolls the whole lock. Scored on audit
#1's axes: A9 ✓, A4 ✓, `LEAN_NUM_THREADS=2` ✓, `nice 19` ✓, 143-retry ✓ —
and **A5 ✗, A7 ✗, RSS line ✗, recursive kill ✗, A8 ✗**: six violations in
twelve applicable cells.

Its A5 violation is the one worth naming, because it is now the **third**
occurrence of a defect the law book documents by name:

```
( set -C; echo "$LANE lake pid $$ (M3 TrProj)" > "$LOCK/owner" )
```

Last whitespace-separated field: `TrProj)`. §7.1 rule 5 records this exact
shape as the Go lane's (`lean-go)`); audit #1 found it again in
`leantier-inch2.sh` (`lean4lean)`); here it is a third time, from the same
lane, in a script written after both.

**Adoption, measured live rather than claimed.** At 23:03 the lock owner
file read `go 54886` — two fields, pid last, `tools/triad.sh`'s exact A5
format — and `ps` resolves 54886 to `bash tools/triad.sh --lane go
--classify`, with exactly one `lake` and one `lean` descending from it.
Every queued ticket resolves to the same script:

    cat /tmp/ls-build.lock/owner ; for t in $(ls /tmp/ls-build-queue); do
      ps -o args= -p $(echo $t | cut -d- -f2); done

| lane | ticket pid | process |
| --- | --- | --- |
| go | 54886 | `bash tools/triad.sh --lane go --classify` (**holding**) |
| ada | 69754 | `bash tools/triad.sh --lane ada --gates …` |
| basecase | 71861 | `bash tools/triad.sh --lane basecase --gates …` |
| wasm | 78540 | `bash tools/triad.sh --lane wasm --dir …` |
| es | 2934 | `bash tools/triad.sh --lane es --dir …` |
| pyc3a | 80356 | `bash tools/triad.sh --lane pyc3a --dir …` (arrived mid-measurement) |

**Six lanes on the shared script, one lane not.** Audit #1's top
recommendation was adoption; that is the delta.

Also measured, and it is *not* good news: **the three live checks found no
violation this time.** One owner, one build chain by parentage, all five
queued pids alive. Audit #1 caught two concurrent builds for 48 minutes; the
same check now passes.

### 2.2a THE NEW FAILURE MODE: the shared script is being FORKED

    for f in /tmp/triad_sh /tmp/triad_new.sh /tmp/my_triad.sh; do md5 -q $f; done
    # then compare against every committed version of tools/triad.sh

| copy | lines | matches a commit? |
| --- | ---: | --- |
| `/tmp/triad_sh` | 381 | ✓ `f66b1ad` (a stale snapshot) |
| `/tmp/triad_new.sh` | 454 | **NO MATCH — a fork** |
| `/tmp/my_triad.sh` | 502 | **NO MATCH — a fork** |

Of the non-comment lines each fork adds over the 381-line base, only
**11 / 66** and **23 / 111** are present in today's `tools/triad.sh`. So
roughly four fifths of two lanes' improvements are sitting in `/tmp`.

And one of them is not a style difference. `/tmp/my_triad.sh` carries:

```
#   A16.1   per-process 5 GB AND chain 10 GB.  Measured, not chosen: a single
#           HONEST `lean` worker on the sunfish tree reached 3251 MB at
#           LEAN_NUM_THREADS=2 (base-case lane, 21:04), and a pre-A11 build of
#           the same tree ran 2846/3238/3117/2864 MB (three of four over 3 GB).
#           A15's 3 GB therefore killed …
```

`tools/triad.sh:89` still reads `RSS_LIMIT_KB="${LS_RSS_LIMIT_KB:-3145728}"
# 3 GB, amendment 11`, **summed over the chain**. If that measurement is
right, the canonical script's kill line terminates honest builds — and the
correction lives only in a purgeable file. This is audit #1's finding one
level up: the protocol moved from prose into a script, and the *amendments*
are now moving from the script into `/tmp`.

**And the register is behind again.** `A14`, `A15` and `A16.1` are cited by
`leantier-m3.sh` and `/tmp/my_triad.sh`; `grep -rn 'A1[4-9]' docs/*.md`
returns **nothing**, and §7.1a's table ends at 13. Audit #1 found the
register one amendment behind; it was completed to thirteen; it is now
**three** behind. The LOST problem is solved and the BEHIND problem is not —
the register is a snapshot of a moving thing, and only the script is the
thing itself.

## 2.3 (2) THE SEVEN FIXES — all still correct, re-run not re-read

`git rev-list --count 28b9f5e..HEAD -- <each file>` is **0** for all five
files, but "a fixed guard can regress" is the reason to run it, so all
fourteen checks were re-executed against fresh fixtures at `64ab535`:

| | agree / resolvable | drift / unresolvable |
| --- | :-: | :-: |
| A1 `c_construct_census --compare` | 0 ✓ | 1 ✓ |
| A2 `wasm_spec_census --compare` | 0 ✓ | 1 ✓ |
| A3 `wasm_suite_census --compare` | 0 ✓ | 1 ✓ |
| B1 `wasm_spec_census` revision | 0, `4a46e190` ✓ | 2, no file ✓ |
| B2 `wasm_suite_census` revision | 0, `6a68dda2` ✓ | 2, no file ✓ |
| B3 `es_census` sources | 0, `1d82ead6` ✓ | 2, no file ✓ |
| B4 `lean_independent_check` checker_commit | 0, `274a4599` ✓ | 2, no file ✓ |

**14 / 14. No regression.** (The revisions differ from the fix report
because the fixtures are rebuilt each time; that they are non-empty and the
`-nogit` runs write nothing is the property under test.)

## 2.4 (3) THE CONTRACT — censuskit correctly absent, and a defect came BACK

`harness/censuskit.py` does not exist, and neither does any other shared
census module (`git ls-files harness/ tools/ | grep -iE 'kit|common|shared'`
→ nothing). **Correct**: §9.2 made it by-touch.

Eight instruments were touched since #1, **two of them new**:

| instrument | landed | `--compare` on drift | provenance |
| --- | --- | :-: | --- |
| `harness/lean4lean_obligation_census.py` | **21:01** | **1** ✓ (missing baseline → 2) | **REFUSES**: *"--l4l is not a git checkout, so the census has no provenance"* ✓ |
| `harness/wasm_sorry_census.py` | **20:44** | **0** ✗ | **returns `None`** ✗ |

The fix landed at ~18:05. `wasm_sorry_census.py` was written **2h39m
later**, and its `git_rev` is **byte-identical** to the function that fix
deleted from `wasm_spec_census.py` — same lane, copied from its own sibling:

    git show f66b1ad:harness/wasm_spec_census.py | sed -n '/^def git_rev/,/^    return None/p' > /tmp/old
    sed -n '/^def git_rev/,/^    return None/p' harness/wasm_sorry_census.py > /tmp/new
    diff /tmp/old /tmp/new        # identical

It stamps the result at line 208 (`"revision": git_rev(...)`) and its
`--compare` returns 0 on drift at line 250. Seventeen minutes later the Lean
lane's new instrument got **both** right, in that lane's own words.

> **This is the measurement the censuskit argument was missing.**
> Copy-paste propagates a defect FORWARD faster than a fix propagates
> SIDEWAYS. Fixing seven implementations did not stop the eighth from being
> born with two of them, because the fix changed files and the defect lives
> in a habit.

Net contract-defect count: **7 → 2**, both in one new file, both in the lane
whose sibling was fixed. Recommended, in §9.1's own shape: **fix those two
today** (two lines), and let the by-touch migration continue.

## 2.5 (4) NEW DUPLICATION SINCE #1

### Backlog v2 — landed, and now there are TWO backlogs

Eleven per-lane files, 2,934 lines, and **28 of 29 entries carry the
ratified `YYYY-MM-DD-<lane>-<n>` id**. The single drifter is the Go lane
(`docs/backlog/go.md:9` — `## G1`), i.e. the sequential scheme §9.5 exists
to replace; its header also cites "§9" rather than §9.5 and states an
ordering convention ("Entries newest-last") no other file states. Four
distinct header spellings across eleven files.

The larger finding is what did **not** happen. §9.5's migration says *"the
current file is renamed to an archive"* and *"`docs/backlog.md` becomes a
generated index"*. Neither has:

    V2=$(git log --diff-filter=A --format=%h -- docs/backlog/ | tail -1)   # 3ad1550
    git rev-list --count $V2..HEAD -- docs/backlog.md    # 10
    git rev-list --count $V2..HEAD -- docs/backlog/      # 29

**Ten landings appended to the monolith after the replacement shipped**, it
grew from 21,050 to 21,797 lines, and no `tools/backlog_index.py` exists. So
the family currently maintains two backlogs and no index — a duplication
created by a half-finished de-duplication. Cheapest close: rename the
monolith to `docs/backlog/archive-L1-L89.md` (every `§Lnn` reference keeps
resolving, no history rewrite) and generate the index. **This audit lane
moved first**: its entry is `docs/backlog/audit.md`, not the monolith.

### `RefusalCause` — four spellings, eight constructor names, four causes

| site | kind | constructors (at `64ab535`) |
| --- | --- | --- |
| family §5.2 | law | `unsupported`, `undefined`, `environment`, `order-dependence` |
| `LeanModels/Es/Completion.lean:66` | **code** | `unsupportedConstruct`, `unmodeledIntrinsic`, `environment` |
| `LeanModels/C/C23/Memory.lean:221` | **code** | `valueUB (UB)`, `memUB (MemFault)`, `libc (String)` + a separate `Cause` projection |
| `docs/ada-semantics-design.md:120` | prose | `unsupportedConstruct`, `undefined`, `environment`, `orderDependence` |

Nine distinct constructor names for four causes, two implementations that
shared none of them, and `libc` — which §5.2 says in as many words is *"too
C-specific a name for a family contract"* — still in the code.

> **RE-MEASURED at `ad90bd2`, and this one RESOLVED ITSELF while the audit
> was being written.** `a7acd87` replaced the ES type with
> `LeanModels/Es/Completion.lean:118` — **`inductive RefusalCause (π : Type)`**,
> documented as *"the family's four REFUSE classes — §5.2 — parameterized by
> a tier payload"*, with `unsupported`/`undefined`/`environment`/
> `orderDependence` each carrying a `π`, a per-tier instantiation
> (`abbrev EsRefusal := RefusalCause EsDetail`), and a `className`
> projection emitting **exactly** §5.2's four strings — `order-dependence`
> included. The two ES-specific causes became payload.
>
> That is, precisely, audit #1 §5's recommendation: *a shared core with a
> per-tier extension, because the vocabulary is already law and only the
> extension is genuinely per-tier.* It was proposed, not imposed; a lane
> reached it independently, and the shape it reached is the proposed one.
>
> Residual bill: **9 distinct names → still 9**, because C's
> `valueUB`/`memUB`/`libc` and Ada's prose `unsupportedConstruct` have not
> moved. What changed is the direction: the family type now EXISTS in code
> for the first time, so C and Ada have something to instantiate rather than
> something to negotiate. `libc` is the one name §5.2 names as wrong, and it
> is now the only code-level obstacle to a straight instantiation.

**But the drift is DECLARED, not silent**, and that is a genuine improvement
over what audit #1 found: the Ada design states *"the Ada tier's
`RefusalCause` is not ES's, and this is stated as a finding rather than
silently diverging"*, prices the difference against ARM 1.1.5 with a census
number (23 erroneous-execution paragraphs in clauses 1-13), and explicitly
leaves the Core-vs-per-tier choice to the architecture lane. That is the
right shape for a pre-Core divergence.

### `SemM` by shape — 13 sites, 5 spellings, and 2 are a DIFFERENT MONAD

    grep -rnE 'ExceptT [^ ]+ \(StateT' --include=*.lean --include=*.md .

| spelling | sites |
| --- | --- |
| `ExceptT ρ (StateT W Halt)` — canonical | family §3.4 (`:1126`), `Es/Completion.lean:154` (**the only code**), `es-semantics-design.md:129`, `ada-semantics-design.md:22`, `sv-r1-scheduler.md:795`, `docs/backlog/go.md:155` (by shape, with an adoption note) |
| `ExceptT ρ (StateT CWorld Halt) α` — world fixed, α explicit | `c-semantics-design.md:330` |
| `ExceptT Refusal (StateT Mem Halt) α` — both slots fixed | `C/C23/Expr.lean:103`, `C/C23/Stmt.lean:43`, `c-semantics-design.md:563` |
| `ExceptT PyErr (StateT σ (Except Loud))` — **different base** | `docs/mvcgen-pilot.lean:63`, `docs/lean-structures-census.lean:49` |
| `ExceptT ρ (StateT SvWorld (Except Loud))` — **different base** | `sv-r1-scheduler.md:1158` |

**The reconciliation bill, stated so it can be paid deliberately:** thirteen
sites, of which three are Lean that must compile against a `Core.SemM` the
day it lands, and **two use `Except Loud` rather than `Halt` — which §3.4
proves are NOT interchangeable**, so those two are a semantics decision and
not a rename. The Go lane is the model: it declined to define its own and
wrote the adoption note instead (*"`Core.SemM` has not landed … so it is
defined BY SHAPE with the adoption note"*).

One free finding while counting: `LeanModels/C/C23/Expr.lean`'s **module
docstring** says `EvalM α := ExceptT Refusal (StateT Mem Id) α` (line 59)
while the `abbrev` twelve lines later says `Halt` (line 103). Doc-vs-code
drift inside one file, and `tools/docs_check.py` cannot see it because it
checks `docs/**`, `README.md` and `AGENTS.md` — not Lean docstrings.

## 2.6 (5) THE CLASSIFIER'S FIRST HOURS

`tools/triad.sh --classify` landed at **21:21** (`a0fd332`), so its life is
**hours, not a week**; the numbers below say so rather than annualising
them. Every landing's diff was classified with the **shipped**
`classify_path`, sourced out of `tools/triad.sh` itself — not a
re-implementation:

    sed -n '/^classify_path() {/,/^}/p' tools/triad.sh > /tmp/cp.sh   # then source it

| window | landings | docs-only (**no tenure owed**) | tier | spine |
| --- | ---: | ---: | ---: | ---: |
| since audit #1 (`f66b1ad`) | 43 | **35 (81%)** | 7 | 1 |
| since `--classify` landed (`a0fd332`) | 14 | **11 (79%)** | 3 | 0 |

These are **conservative**: `classify_path` alone ranks every `Examples/*`
path as `tier`, and the shipped classifier's reachability probe can only
*demote* unreferenced fixtures to `docs`. So the docs-only count can only go
up, never down.

What the landings themselves claim, across the 43:

* **20** state *no ticket / no tenure / docs-only / no Lean*;
* **17** name `tools/triad.sh`;
* **8** report a build or a gate result.

So the classifier's rule and the lanes' behaviour agree to within a few
landings: **roughly four out of five landings in this period owed no
tenure**, against a queue that was five deep while this was measured. That
is the item's value, and it is why §2.2's contention numbers improved
without anyone building faster.

## 2.7 WHAT AUDIT #3 SHOULD RE-MEASURE

0. **Whether C and Ada instantiated `RefusalCause π`** — the family type now
   exists in code (`ad90bd2`), so #3 measures uptake rather than divergence,
   and `libc` is the named obstacle.
1. **Whether the two `wasm_sorry_census.py` defects were fixed**, and
   whether instrument #24 is born clean. That is the by-touch policy's real
   test, and #2 is the first evidence against it.
2. **Whether `tools/triad.sh`'s forks came home** — specifically whether the
   A16.1 RSS measurement landed in the repo script, and whether A14-A16
   reached §7.1a. Fork count and register lag are now the leading
   indicators, replacing #1's private-script count.
3. **Whether the monolith was archived and an index generated** — the
   dual-write count (`10` and rising) is the metric.
4. **The `SemM` bill at the moment `Core.SemM` lands**: 13 sites, and
   whether the two `Except Loud` sites were decided rather than renamed.
5. **The three live checks**, every keeper tick. They passed this time; #1's
   48-minute violation is why they exist.
