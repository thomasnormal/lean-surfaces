#!/usr/bin/env bash
# tools/diagnose.sh — THE FAILURE DECODER.  A build log, annotated.
#
# WHY THIS FILE EXISTS.  The expensive part of a red is almost never the red;
# it is the investigation cycle.  A stale `olean` cost one lane roughly two
# hours and survived four plausible diagnoses (docs/backlog.md §L62).  A
# torn-tree rebase cost the Go lane a hunt for four constants that were
# present on master all along (§7.2).  A `#print axioms` line that reads
# CLEANER than the truth is §5.4a's first instance.  Every one of those has
# a literal string in the log, and every one of them is written down
# somewhere in this repository — just not next to the log.
#
# So: this script puts the record next to the log.  Give it a build or
# elaboration log (file or stdin) and it annotates the lines it recognizes
# with the CAUSE, the FIX, and THE LAW'S HOME — the durable place the rule
# lives, so the annotation can be checked and does not become a fourth copy.
#
# EVERY SIGNATURE CITES ITS INCIDENT.  A decoder that guesses is one more
# thing to distrust, so nothing is listed here that this repository has not
# actually hit.  One signature the dispatch asked for is NOT here: `E999` on
# a generated artifact.  It was searched for — `grep` over the working tree,
# `git log -S` and `-G` over all branches, a `git grep` sweep over 400
# revisions — and it does not exist at any revision.  The repo has no
# numbered-code linter to emit it.  An empty row beats a plausible rule.
#
# USAGE
#   tools/diagnose.sh build.log             # annotate a log
#   lake build 2>&1 | tools/diagnose.sh     # or a pipe
#   tools/diagnose.sh --list                # the signature table
#   tools/diagnose.sh --explain <id>        # one signature in full
#   tools/diagnose.sh --self-test           # EVERY signature run on a fixture
#
# ZERO Lean execution: this reads text.  It is safe outside a tenure (A11).

set -u

MAX_SAMPLES="${DIAG_MAX_SAMPLES:-4}"

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }

# ---------------------------------------------------------------- the table
# Order matters only for reading; every signature is tested against every
# line.  Ids are stable — a lane may cite `diagnose.sh:whnf-timeout`.
SIG_IDS="
whnf-timeout
unknown-constant
mvcgen-bare-false
axioms-clean-lie
resource-kill
unknown-option
lock-release-failed
worker-sigtrap
omega-no-constraints
max-rec-depth
vacuous-match
kernel-type-mismatch
doc-comment-before-command
universe-metavariables
split-failed
spec-proof-twin
py-loop-context
sorry-warning
census-drift
null-provenance
queue-gave-up
seeded-clone-identity
"

sig_regex() {
  case "$1" in
    whnf-timeout)        echo 'timeout at .?(whnf|isDefEq|simp)|maximum number of heartbeats' ;;
    unknown-constant)    echo '[Uu]nknown constant' ;;
    mvcgen-bare-false)   echo '⊢ False|\|- False' ;;
    axioms-clean-lie)    echo 'does not depend on any axioms' ;;
    resource-kill)       echo 'exited with code (137|143)|exit (status )?(137|143)|BUILD_EXIT=(137|143)' ;;
    unknown-option)      echo 'unknown option|unknown long option|unrecognized option' ;;
    lock-release-failed) echo 'LOCK[ _]RELEASE[ _]FAILED|Directory not empty' ;;
    worker-sigtrap)      echo 'rc=133|RC=133|exited with code 133|SIGTRAP' ;;
    omega-no-constraints) echo 'No usable constraints found|omega could not prove the goal' ;;
    max-rec-depth)       echo 'maxRecDepth|maximum recursion depth' ;;
    vacuous-match)       echo 'MATCH[[:space:]]+0[[:space:]]|[^0-9]0 [a-z()]+ (agree|agreed|compared|checked|matched)' ;;
    kernel-type-mismatch) echo '\(kernel\) (application|declaration) type mismatch' ;;
    doc-comment-before-command) echo "unexpected token '(#guard|#check|#print|#eval|mutual|open|namespace|set_option)'|doc comment cannot attach" ;;
    universe-metavariables) echo 'contains universe level metavariables' ;;
    split-failed)        echo 'Tactic .?split.? failed|Could not split an' ;;
    spec-proof-twin)     echo 'no proof named|is not an .*\.spec. module' ;;
    py-loop-context)     echo 'no .?hentry.? hypothesis|is not in the loop environment' ;;
    sorry-warning)       echo "declaration uses 'sorry'|uses .sorry." ;;
    census-drift)        echo 'DRIFT: ' ;;
    null-provenance)     echo '"(revision|git_rev|checker_commit|toolchain)": *(null|"")' ;;
    queue-gave-up)       echo 'GAVE UP after' ;;
    seeded-clone-identity) echo "A13 WARNING|is ahead of 'origin/master' by [0-9][0-9]+" ;;
    *) echo '' ;;
  esac
}

# A fixture is a REAL line: quoted from the incident wherever the record
# quoted one.  --self-test runs each through the same matcher the live path
# uses, so a signature cannot be listed without being exercised.
sig_fixture() {
  case "$1" in
    whnf-timeout)        echo 'error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached' ;;
    unknown-constant)    echo "error: unknown constant 'Bracket.sw_push'" ;;
    mvcgen-bare-false)   echo 'case vc3 ⊢ False' ;;
    axioms-clean-lie)    echo "'value_scores_M' does not depend on any axioms" ;;
    resource-kill)       echo 'error: Lean exited with code 143' ;;
    unknown-option)      echo "error: unknown option '-j4'" ;;
    lock-release-failed) echo 'rmdir: /tmp/ls-build.lock: Directory not empty' ;;
    worker-sigtrap)      echo 'rc=133   chapter-22/22.9--unconnected_drive-invalid-2.sv' ;;
    omega-no-constraints) echo 'error: omega could not prove the goal: No usable constraints found.' ;;
    max-rec-depth)       echo 'error: maximum recursion depth has been reached (use `set_option maxRecDepth <num>`)' ;;
    vacuous-match)       echo 'MATCH  0 marking(s) agree' ;;
    kernel-type-mismatch) echo 'error: (kernel) declaration type mismatch' ;;
    doc-comment-before-command) echo "error: unexpected token '#guard'; expected 'lemma'" ;;
    universe-metavariables) echo "error: declaration 'get!_spec' contains universe level metavariables at the expression" ;;
    split-failed)        echo 'error: Tactic `split` failed: Could not split an `if` or `match` expression in the goal' ;;
    spec-proof-twin)     echo 'error: no proof named relu_of_nonneg in Examples.tut_03.proof — add it to proof.lean' ;;
    py-loop-context)     echo 'error: py_loop: no `hentry` hypothesis in context — run `py_begin [f]` first' ;;
    sorry-warning)       echo "warning: declaration uses 'sorry'" ;;
    census-drift)        echo 'DRIFT: thesis_kernel_rules' ;;
    null-provenance)     echo '  "revision": null,' ;;
    queue-gave-up)       echo 'GAVE UP after 14400s without reaching the front — NOT a build failure' ;;
    seeded-clone-identity) echo "Your branch is ahead of 'origin/master' by 238 commits." ;;
    *) echo '' ;;
  esac
}

# TITLE / CAUSE / FIX / HOME / INCIDENT, one heredoc per signature.
sig_meta() {
  case "$1" in

  whnf-timeout) cat <<'S'
TITLE|a fuel mismatch until proven otherwise — and FOUR causes wear this same face
CAUSE|A `whnf` (or `isDefEq`, or `simp`) heartbeat timeout is the most overloaded string in this tree. Four recorded causes present identically: (1) an off-by-one between a gate's fuel numeral and its `execStmts_singleton (F := k)`, which asks unification to solve an unsolvable numeral equation and never gives up; (2) a STALE `olean` still holding a pre-refactor fuel; (3) a missing altitude lemma over an expensive operand; (4) mvcgen's own exponential splitting.
FIX|Discriminate in this order, cheapest first. (a) `#check @thm` on every imported lemma and READ THE NUMBERS — `lake env lean` type-checks WITHOUT writing the olean, so importers keep seeing the old one; this is the two-hour case. (b) Re-state the single gate at a fresh abstract frame: if it still times out the composition is innocent and the gate's own application is wrong — 30 seconds. (c) Prefer SYMBOLIC fuel in compositions (`Fg + 3 + 2` vs `Fg + 6`), which turns the same off-by-one into an application type error naming both sides. (d) In a long chain the missing thing is an altitude lemma — THE BUDGET KNOB IS THE WRONG KNOB: at 10x heartbeats the same goal reported `timeout at simp` in 15 s and then `timeout at whnf` after two minutes; six altitude lemmas made it elaborate in under two seconds.
HOME|docs/backlog.md §L23 "Findings worth carrying" item 1; §L48 finding 2 (altitude); §L62 (stale olean); docs/statement-cookbook.md §5 (fuel placement)
INCIDENT|Three off-by-ones between a gate's fuel and its singleton fuel each appeared as a 2-3 minute whnf storm, and the table store was nearly reported as a HARD BLOCKER on that evidence (§L23).
S
  ;;

  unknown-constant) cat <<'S'
TITLE|a TORN TREE or a stale olean — this is not evidence that master is broken
CAUSE|Two causes, both spurious. (1) A fetch-rebase ran in the SAME CLONE while a build was live, so the build reads rebased files against a pre-rebase build graph and dies with `Unknown constant` errors that look exactly like a broken master. (2) `lake env lean` type-checked a file WITHOUT writing its olean, so every importer still sees the old declaration.
FIX|Verify before believing: `git diff github/master -- <file>` (the incident's diff was EMPTY, and all four "missing" constants were present) and `#check @<constant>`. Then order the tenure `stage -> build -> rebase`, or `rebase -> build`, never both at once — and note this is a SAME-CLONE hazard the build lock does not prevent, because the lock serializes builds against each other and a rebase is not a build. Before trusting any cross-file goal, `lake build` rather than `lake env lean`.
HOME|docs/family-architecture.md §7.1a register row 6, carried in §7.2; §5.4a provenance table, third instance; stale-olean at docs/backlog.md §L62 and §L41 finding 3
INCIDENT|Go lane, 2026-08-22: a fetch-rebase at 13:07:58 ran while that build was running; four constants were chased as a possible red master and master was never broken. "A RED FROM A TORN TREE IS NOT EVIDENCE OF ANYTHING" — it discharges nothing (an owed build stays owed) and convicts nothing (not grounds to call master broken), and it must not be laundered into a green either.
S
  ;;

  mvcgen-bare-false) cat <<'S'
TITLE|the splitter dropped the discriminant — an unreachable branch you cannot refute
CAUSE|mvcgen splits an inner `match` into one verification condition per branch WITHOUT retaining the discriminant equation, so the unreachable branches arrive as bare `⊢ False` with nothing available to refute them. On the join-point path the splitter is invoked with `useSplitter := false` (so the equalities are never requested), the join goal clears the stateful hypothesis, and the matcher is abstracted with an explicitly NON-DEPENDENT motive — that is the mechanism by which an alternative forgets which discriminant produced it.
FIX|Do not reach for the simp set: feeding the hypothesis to mvcgen's simp set does NOT help, because the split has already happened — and `grind` does not fix it either, since the blowup is inside mvcgen's own splitting, before any VC reaches a discharge tactic. The owed measurement is two runs on the same gate, default vs `mvcgen (config := { jp := true })`, WITH BOTH NUMBERS AND BOTH jp SETTINGS RECORDED TOGETHER, plus a ~20-line repro for an upstream report. Note honestly that `+jp` is core's more conservative but "slightly lossy" encoding: it may be the SOURCE of the loss rather than its cure.
HOME|docs/backlog/research.md 2026-08-22-research-1 ("The second finding, same neighbourhood"); docs/proof-framework-research.md §1.5
INCIDENT|The rebuild lane's arm-level lemma — the static-globals-fold arm its gate exercises twice — CANNOT BE STATED AT ALL. Re-measured with both landed lemmas in the registry, the four-deep gate still did not close at 4M heartbeats / ~10 minutes. Recorded as the third mvcgen defect that lane found.
S
  ;;

  axioms-clean-lie) cat <<'S'
TITLE|the STATEMENT failed — the cleanest possible axiom line, and it means the opposite
CAUSE|`#print axioms` on a declaration whose STATEMENT failed to elaborate prints "does not depend on any axioms" even when the proof is literally `sorry`, because the declaration was RECOVERED before the proof was ever checked against it.
FIX|Read the errors FIRST. An axiom print is meaningful ONLY from a zero-error elaboration, and every quoted axiom line is paired with that status. The mode table, measured on the pin: unsolved goals -> [sorryAx] (honest); body type error -> [sorryAx] (honest); explicit sorry -> [sorryAx] (honest); ERROR IN THE STATEMENT -> "does not depend on any axioms" (lies). Only the fourth mode lies, and it is the one that reads cleanest.
HOME|docs/family-architecture.md §0.1 II(a) (the mode table), cross-referenced from §5.4a; docs/backlog.md §L59
INCIDENT|The rebuild lane's failed `value_scores_M` printed `'value_scores_M' does not depend on any axioms` — the cleanest possible axiom line, meaning the opposite. This is the FIRST of §5.4a's three provenance instances, and the one that reads cleanest when it lies.
S
  ;;

  resource-kill) cat <<'S'
TITLE|a RESOURCE KILL, never a red build
CAUSE|The OS terminated an oversubscribed job — 143 is SIGTERM, 137 is SIGKILL/OOM. Neither is a proof or compilation failure.
FIX|Re-read as "the machine was oversubscribed": check the lock discipline and re-run UNDER THE LOCK. NEVER record it as a red build. tools/triad.sh treats both exits as a resource kill and re-runs once, by design rather than by a lane deciding a red was spurious.
HOME|docs/family-architecture.md §7.1 base rule 2, amendment register row 2; implemented in tools/triad.sh
INCIDENT|Three, all 2026-08-22. The Go lane died at 3,678 of 3,693 jobs with exit 143, load average peaking at 40.3 with five lanes building. The SV lane reached 3,690 of 3,693 jobs with ZERO compilation errors and two Python-tier targets killed — no SV target failed. A kernel `rfl` through a module initializer was OOM-killed (137) after 3m56s. And the amendment was OBSERVED WORKING: the 143/137 retry came back GREEN on attempt 2.
S
  ;;

  unknown-option) cat <<'S'
TITLE|an argument error — the build never ran, and the triad can still look green
CAUSE|This lake has no job flag at all: `-j4`, `--jobs=4` and `--jobs 4` are ALL rejected (measured on Lake 5.0.0-src / Lean 4.33.0-rc1). It exits 1 INSTANTLY, so no build runs — and because docs_check, the differential and the corpus scripts all still execute and can all still pass, A SCRIPTED TRIAD LOOKS GREEN WHILE `lake build` NEVER RAN.
FIX|Throttle with `LEAN_NUM_THREADS` (and `nice`), never with `-j`. And assert success POSITIVELY: grep for `Build completed successfully` rather than grepping for errors, because an argument error and a resource kill both emit no line the failure greps look for, and "no error found" must never read as "the build happened".
HOME|docs/family-architecture.md §7.1 base rule 2 and the positive-assertion clause in §7.1a; implemented in tools/triad.sh
INCIDENT|Reproduced INDEPENDENTLY by two lanes that had not read each other — the wasm lane's first triad (§L71 defect 1) and the Go lane (§L76). Two lanes meeting the same failure is what promoted it from a lane's notes to a shared document.
S
  ;;

  lock-release-failed) cat <<'S'
TITLE|a pre-A2 rmdir release — and a leaked lock blocks every other lane forever
CAUSE|A `rmdir` release composed with an owner file INSIDE the lock directory fails silently: rmdir refuses a non-empty directory, the trap swallows the status, and the lock leaks — after which every other lane blocks forever on a lock nobody holds.
FIX|`rm -rf "$LOCK" || echo "LOCK RELEASE FAILED" >&2` — rm -rf removes the directory whatever it contains, and the `|| echo` makes a failed release LOUD instead of invisible. If you are reading this line in a real log the release genuinely failed: check the owner before removing anything, because the dual defect is worse — an UNCONDITIONAL release (pre-A7) deletes an active holder's lock and every queued lane then runs concurrently. The trap must be OWNERSHIP-CHECKED.
HOME|docs/family-architecture.md §7.1 rule 1 AMENDMENT 2 (register row 2); A7 in §7.1a; implemented in tools/triad.sh
INCIDENT|The wasm lane leaked a lock PROVING IT — verified directly: after the trap ran, the lock directory was still present with `owner` in it. Independently reproduced by the Go lane, which leaked its own lock exactly once. The A7 dual was found live in a stale hand-rolled runner (docs/backlog/sunfish-rtrack.md, "The lock incident — a mechanism, and it is not a reclaim").
S
  ;;

  worker-sigtrap) cat <<'S'
TITLE|a worker died (133 = 128+5 = SIGTRAP) — and the Pool waits forever for its result
CAUSE|The frontend hard-crashes with SIGTRAP and ZERO bytes of output on some inputs, and `multiprocessing.Pool` then waits forever for a result from a worker that no longer exists. The hang itself has NO exit code, no message and no failing file name; the process-level tell is a worker sitting at 0.0% CPU in state S — stopped, not slow.
FIX|Per-file subprocess isolation (`ProcessPoolExecutor`), so a worker death becomes ONE recorded `error` row NAMING THE FILE. The obvious alternative does not work: a per-file `signal.alarm` cannot help, because the process carrying the alarm is the one that dies. Measured after isolation: the full 717-file corpus completes in 1.0 s where it previously never completed at any job count.
HOME|docs/sv-charter.md (the census section); docs/backlog.md §L60, closed at §L67; harness/sv_round_trip.py
INCIDENT|SV lane, 2026-08-22. Bisected on `--limit`: 100/200/400 complete in ~1.5 s each; 500, 600 and 717 NEVER complete. Running files 400-510 individually isolated exactly one. Classified as two "never hide errors" violations — the frontend dies on input a conformance suite is meant to reject gracefully, and the instrument converts that crash into a HANG, which is strictly worse. It also corrected the charter's own draft conclusion, and only running it showed so.
S
  ;;

  omega-no-constraints) cat <<'S'
TITLE|a reducible brand — omega's atom matching is SYNTACTIC and does not unfold it
CAUSE|The branded type is DEFINITIONALLY the base type, but omega skips a comparison headed at the brand wholesale — hypothesis or goal alike. The head type is decided by the LEFTMOST intrinsically-typed operand, and ascriptions on branded variables are looked through.
FIX|Unbrand FIRST, and mind which of the three cases you are in. In a HYPOTHESIS you wrote: go through `py_begin`, which restates every branded hypothesis at the unbranded type — or by hand, put a genuinely base-typed term on the LEFT (`have hx' : (0 : Int) ≤ x := hx`, flipped for the other direction). ASCRIPTION DOES NOT UNBRAND: all three ascribed spellings re-land at the brand, and the restated hypothesis PRINTS IDENTICALLY to the original — no visible difference is the tell. In a `by_cases` you are about to run: put the base-typed term on the left, or keep omega out of it. In the GOAL: a brand-headed goal comparison cannot be restated — switch the closer to `grind`, which matches up to reducible unfolding.
HOME|AGENTS.md "Failure modes" table row 1 (every string in it reproduced on the current tree); docs/tutorial/06-when-proofs-fail.md §5
INCIDENT|Reproduced at named examples in the tree. Blast radius: the same root cause makes `py_prove` fail on branching goals that need a precondition (its closer is omega), and makes an omega bullet after `py_loop` unable to use a theorem-level hypothesis even though the residual-goal facts work fine.
S
  ;;

  max-rec-depth) cat <<'S'
TITLE|THREE causes, and raising the option is the right fix for exactly one of them
CAUSE|(1) `cbv` on a HEAP-WALKING residue: it unfolds eagerly and the walk is too deep — it blew maxRecDepth at 40,000. (2) A kernel `rfl` through a module initializer, which RUNS the module. (3) A large LITERAL — a 2 MB envelope, a 5.5 MB guard file.
FIX|Tell the three apart BEFORE touching the option. For (1) the route is altitude lemmas: cbv's reach is the pure-arithmetic and small-match residues — a real and recurring class, honestly bounded, and NOT the heap-walking ones. For (2) raising it only moves the failure: at maxRecDepth 1000000 and maxHeartbeats 0 the elaborator was OOM-killed after about seven minutes. For (3) `set_option maxRecDepth 100000 in` IS the fix, and the in-tree note says exactly why: raised for the LITERAL, not for a proof.
HOME|docs/lean-structures-census.md §1.3/§10.2 (docs/backlog.md §L81); the kernel-rfl site in docs/backlog.md; Examples/c/sunfish/guards.lean for the literal case
INCIDENT|The structures census bounded `cbv` honestly IN THE SAME PARAGRAPH as its win: one token closes the pure residue with a clean axiom line and the false variant leaves unsolved goals, and the heap residue is stated as out of reach rather than quietly omitted.
S
  ;;

  vacuous-match) cat <<'S'
TITLE|a run that executed NOTHING must never score as agreement
CAUSE|The check compared nothing and scored it as a match — an empty comparison set reads as agreement. An empty census is an INSTRUMENT FAULT, never a finding.
FIX|Report VACUOUS. A scoreboard that reports an empty run as MATCH is broken, and one that reports it as REFUSE is lying about coverage. Check every source file rather than the first, and let the artifact say VACUOUS when both sides are genuinely empty — that is the instrument taking no credit rather than the instrument failing.
HOME|docs/family-architecture.md §5.3 "VACUOUS is not a verdict" and §5.4 (zero-row parse); docs/backlog/ada.md
INCIDENT|Ada lane, §L75: a markings check compared only the first of four files on a twelve-marking envelope and printed `MATCH 0 marking(s) agree`. Caught by the family's own law. Its neighbours were three quiet-failure traps in the suite's own tools — a CRLF parse error, a filename-length error at 13 characters, and an output path that leaves a STALE file and exits without complaint — and one had already produced a false green: A CHECK THAT PASSES FOR THE WRONG REASON IS WORSE THAN NO CHECK.
S
  ;;

  kernel-type-mismatch) cat <<'S'
TITLE|the elaborator accepted it and the kernel refused — a delta-unfold in a mutual block
CAUSE|The definition is in the interpreter's unfold set, so a captured run DELTA-unfolds it and simp records that unfold as a rewrite proved by `Eq.refl`. The definition lives in a mutual block, so at a stuck match the elaborator's `whnf` does smart unfolding and the kernel cannot. The tell is that the reduction was PERFECT — the residual can be literally the goal you wanted.
FIX|Hand `py_simp` the definition's `.eq_def`. It is the SAME rewrite carrying a real proof. General rule: to keep a definition in the unfold set from delta-unfolding badly, give the tactic its `eq_def`.
HOME|docs/backlog.md §L4 CLOSED ("THE BLOCKER, and the mechanism" + "THE FIX"), reproduced at §L56
INCIDENT|Four runs isolated it to a comparison whose operand arrives from module-global resolution. The fix cost NO tactic edit at all — refuting its own predecessor's conclusion that the fix belonged in the tactic. It then reproduced CHARACTER-FOR-CHARACTER a section later on a different file and a different comparison, and the recorded fix worked first try: a recorded failure mode that reproduces exactly is the cheapest kind of knowledge there is.
S
  ;;

  doc-comment-before-command) cat <<'S'
TITLE|a doc comment before a COMMAND — and the error never mentions the comment
CAUSE|In this toolchain a `/-- ... -/` doc comment attaches only to a DECLARATION. Put one before `#guard`, `mutual`, `#print`, `#check`, `#eval`, `open`, `namespace`, or `set_option ... in theorem`, and the file does not parse — with an error that names the FOLLOWING TOKEN and not the comment, so the cause is a line or twenty above the report.
FIX|Use `/-! ... -/` (a section comment) or a plain `/- ... -/` before command blocks. Run the gate first: `python3 harness/es_lean_lint.py [PATH ...]`.
HOME|AGENTS.md "Failure modes"; docs/backlog.md §L66, §L82, §L62 finding 4, §L86; the gate is harness/es_lean_lint.py (docs/backlog.md §L88)
INCIDENT|It cost a compile FOUR SEPARATE TIMES ACROSS FOUR LANES despite being known and written down — "a law that is known and still costs a compile every inch is a law that wants a GATE, not more discipline". And the gate's own first version was wrong: it also listed `example`, which is legal, and that false positive fired on a file that was on master and green. A LINT'S FIRST RUN ACCUSING A PASSING FILE IS THE LINT BEING WRONG, NOT THE FILE.
S
  ;;

  universe-metavariables) cat <<'S'
TITLE|a bare polymorphic `throw` — the declaration is rejected outright
CAUSE|At this pin the `Spec.throw_Except` lemma is declared under a `variable {m} {ps}` block it does not use, so the monad and its predicate shape are not determined by the conclusion. A bare polymorphic `throw` leaves them as universe metavariables and the declaration is REJECTED. Look just above for leftover goals of the form `case vc2.m ⊢ Type ?u`.
FIX|Never write a bare polymorphic `throw` in interpreter code: route EVERY refusal through a NAMED primitive with its own `@[spec]` lemma (`refuse` / `liftRes`). Doing so removed all four metavariable goals. Record it as a rule, not a hack — a refusal is a first-class notion in this family, and the tooling rewards making it one.
HOME|docs/mvcgen-pilot.md §1.4 "A bug in Std at this version, and its workaround"; docs/backlog.md §L61; docs/statement-cookbook.md §8
INCIDENT|One real upstream bug found at the pin in twenty lines of probing, during the mvcgen pilot.
S
  ;;

  split-failed) cat <<'S'
TITLE|two sequential ifs — the branch recipe ran out
CAUSE|On the fall-through arm the full simp set rewrites the second surviving `ite` into a DISJUNCTION, and `split` cannot attack a disjunction.
FIX|Decide the branches up front and hand them to symbolic execution: `by_cases h1 : x < 0 <;> by_cases h2 : 1 < x <;> py_simp [callFunction, f, h1, h2] <;> grind`.
HOME|AGENTS.md "Failure modes" table row 2; docs/tutorial/06-when-proofs-fail.md §7
INCIDENT|Reproduced on the current tree at a named example — the failure-modes table's own header asserts that every error string in it was reproduced rather than remembered.
S
  ;;

  spec-proof-twin) cat <<'S'
TITLE|the spec-side twin is missing — and the SILENT version of this is worse
CAUSE|The statement has no same-name twin in the sibling `proof.lean`, or `:= by proofs` was used outside a three-file spec module.
FIX|Write or rename the theorem under the EXACT spec-side name, inside the `namespace Examples.<name>.proof` wrapper; only spec modules use `:= by proofs`. And know the silent face: rename a shadowing binder so it DOES match the environment and the tactic proceeds — into unprovable goals whose invariant facts never mention the spec. Make the spec and proof statements identical again; DO NOT "fix" it by proving in the spec file.
HOME|AGENTS.md "Failure modes"; docs/tutorial/06-when-proofs-fail.md §3; docs/statement-cookbook.md §21 (never repair a statement to make a proof pass)
INCIDENT|Reproduced on the current tree; the silent variant is walked through step by step in the tutorial because the loud one is the easy half.
S
  ;;

  py-loop-context) cat <<'S'
TITLE|py_loop has no entry lemma, or the loop variables are shadowed
CAUSE|`py_loop` was run without the entry lemma in context, or the invariant's binder names are shadowed by ambient binders, so the loop variable is not the one in the loop environment.
FIX|Run `py_begin [<prog>]` first. When the Python variable names are shadowed by ambient binders, name the state explicitly: `py_loop (state := [s, n]) (inv := ...)`.
HOME|AGENTS.md "Failure modes"; docs/tutorial/06-when-proofs-fail.md
INCIDENT|Reproduced on the current tree. The related shadowing trap has the same silent face as the spec/proof twin: make the names match by accident and the tactic proceeds into goals that cannot close.
S
  ;;

  sorry-warning) cat <<'S'
TITLE|an obligation, not a proof — and the COUNT is not a grep
CAUSE|The tree is telling you a declaration is unproved. The interesting failure is downstream, in how the number gets reported.
FIX|Count them with an instrument that strips Lean comments (`--`, nestable `/- -/`, doc comments) and string literals BEFORE looking for the token — a commented-out `sorry` is not an obligation, it is a note about work someone was thinking about. And beware the other direction: "0 sorry" can distinguish the EMISSION MODE rather than the progress. A generated file with zero sorries may emit no well-formedness theorems at all, or emit them as an `inductive ... : Prop` that takes well-formedness as a PREMISE — which proves nothing and cannot fail.
HOME|docs/backlog/wasm.md 2026-08-22-wasm-1; harness/wasm_sorry_census.py
INCIDENT|A textual grep reported 13 obligations. Eight were inside comments — six a block of planning notes, two a commented-out proof attempt — and the real number was 5. THE DELTA WAS THE FINDING, and the instrument now reports both counts.
S
  ;;

  census-drift) cat <<'S'
TITLE|the census moved — now CHECK THE EXIT CODE
CAUSE|A `--compare` found that the committed JSON and a fresh run disagree. That line is the instrument working.
FIX|Read the drift, then verify the run actually FAILED. Three of fourteen instruments had a `--compare` path that could not exit nonzero, and a fourth short-circuited on the SOURCE sha, so a census that differed for the same input bytes reported UNCHANGED and exited 0. A drift guard that cannot fail cannot be a gate, cannot be used under `set -e`, and cannot be the staleness detector §5.4 asks for. Verify BOTH directions: clean compare exits 0, perturbed baseline prints DRIFT and exits 1.
HOME|docs/family-architecture.md §5.4 (the --compare clause) and §9.1 BUG BEFORE REFACTOR; docs/duplication-audit.md §0 finding 1
INCIDENT|Duplication audit, 2026-08-22: eleven lanes got it right, three did not, and NOBODY COULD SEE THE DIFFERENCE because there is nothing to compare against. Sharpest self-indictment: one lane hit the hole earlier the same day, worked around it by diffing the JSON by hand, and did not recognise it as a defect.
S
  ;;

  null-provenance) cat <<'S'
TITLE|a swallowed `git rev-parse` — the number is quoted and the STATE is silently dropped
CAUSE|An `except: pass` around the provenance helper. Four copies of one six-line `git_rev` function each swallowed their failure and stamped null provenance.
FIX|RAISE, and surface git's own stderr so the refusal names the cause (`(exit 128): fatal: not a git repository`). Put the check ABOVE the module loop so no worker process is ever spawned — the refusal then costs nothing and cannot half-run.
HOME|docs/family-architecture.md §9.1 and §5.4a (this is the provenance law INVERTED); docs/duplication-audit.md
INCIDENT|A verdict file whose entire claim is "checker X accepted these modules", and that cannot say WHICH X, is not weak evidence — IT IS NO EVIDENCE. The defect was in the NEWEST of the six copies, written last and fastest, which is the ordinary shape of this failure and the argument for one shared helper: the defect reappears per copy rather than persisting in one place.
S
  ;;

  queue-gave-up) cat <<'S'
TITLE|never reached the front of the queue — NOT a build failure
CAUSE|The FIFO ticket queue did not hand this lane the lock inside its wait budget, so the wrapper gave up loudly and exited 9.
FIX|Re-queue when the machine is quiet. Exit 9 is not a red build and must not be recorded as one. Thomas's own processes have absolute priority — a training run outranks every tenure, and a lane that would hold the machine's whole Lean allowance waits for a quiet machine and a ticket.
HOME|docs/family-architecture.md §7.1a A9 (the FIFO queue) and A11 (priority); implemented in tools/triad.sh
INCIDENT|A9 exists because the C lane lost FIVE CONSECUTIVE HANDOFFS while queued first, waiting 43 minutes under bare spinning — a plain mkdir spinlock has no queue discipline, and a lane that releases and immediately re-acquires beats a poller every time. Re-measured under the same contention after the ticket queue: the same lane acquired the lock in 58 SECONDS, roughly a 45x improvement, and the starvation mode is gone rather than merely shortened.
S
  ;;

  seeded-clone-identity) cat <<'S'
TITLE|a seeded clone's identity — BRANCH AND REMOTES BOTH — is INHERITED, not chosen
CAUSE|CoW seeding (`cp -Rpc`) inherits the peer's checked-out BRANCH and its REMOTES. In a seeded clone `origin` can point at a stale local BUNDLE, so `git reset --hard origin/master` silently lands a tree days back, `git rev-list HEAD..origin/master` reports 0 (it is comparing against the bundle), and a feature branch reads "238 commits ahead" — which looks like a branch-hygiene problem and is not.
FIX|After seeding, run `git remote -v` AND `git branch --show-current`. Compare or reset only against `github/master`, never against `origin`, which in a seeded clone is not what the name implies. Push `HEAD:master`, never bare `master`, which pushes the local ref rather than the work in hand.
HOME|docs/family-architecture.md §7.1a "THE A13 CAVEAT" and "AND SEEDING INHERITS THE REMOTES TOO"
INCIDENT|FOUR LANES, ONE ROOT CAUSE. What looked like several lanes drifting onto feature branches was one seeding defect wearing three different faces — and the obvious check does not catch it, because it compares HEAD rather than the ref you are about to push.
S
  ;;

  *) echo "TITLE|(no such signature)" ;;
  esac
}

# ------------------------------------------------------------------ output
w() {                                  # w LABEL text  — wrapped, aligned
  printf '%s' "$2" | fold -s -w 74 | awk -v l="$1" '
    NR == 1 { printf "  %-9s %s\n", l, $0; next }
            { printf "  %-9s %s\n", "", $0 }'
}

explain() {                            # explain <id>
  local id="$1" line label text
  sig_meta "$id" | while IFS= read -r line; do
    label="${line%%|*}"; text="${line#*|}"
    case "$label" in
      TITLE) printf '\n▌ %s — %s\n' "$id" "$text" ;;
      *)     w "$label" "$text" ;;
    esac
  done
}

list_signatures() {
  local id line
  printf '%-28s %s\n' "SIGNATURE" "WHAT IT MEANS"
  for id in $SIG_IDS; do
    line="$(sig_meta "$id" | head -1)"
    printf '%-28s %s\n' "$id" "${line#*|}"
  done
  printf '\n%s signatures.  `--explain <id>` for cause, fix, home and incident.\n' \
         "$(printf '%s\n' $SIG_IDS | grep -c .)"
}

# ------------------------------------------------------------------ engine
# Regexes are compiled into a parallel array ONCE, so matching a 10k-line log
# does not fork per line per signature.
IDX_ID=(); IDX_RE=()
build_index() {
  local id
  IDX_ID=(); IDX_RE=()
  for id in $SIG_IDS; do
    IDX_ID[${#IDX_ID[@]}]="$id"
    IDX_RE[${#IDX_RE[@]}]="$(sig_regex "$id")"
  done
}

HIT_N=(); HIT_SAMPLE=(); TOTAL_HITS=0; SAW_SUCCESS=0; SAW_ERROR=0; N_LINES=0
scan() {                               # scan < log   — fills the HIT_* arrays
  local line i n lineno=0
  n=${#IDX_ID[@]}
  HIT_N=(); HIT_SAMPLE=(); TOTAL_HITS=0; SAW_SUCCESS=0; SAW_ERROR=0; N_LINES=0
  for ((i = 0; i < n; i++)); do HIT_N[$i]=0; HIT_SAMPLE[$i]=""; done
  while IFS= read -r line || [ -n "$line" ]; do
    lineno=$((lineno + 1)); N_LINES=$lineno
    case "$line" in
      *"Build completed successfully"*) SAW_SUCCESS=1 ;;
    esac
    case "$line" in
      error:*|*" error:"*|*"✖"*) SAW_ERROR=1 ;;
    esac
    for ((i = 0; i < n; i++)); do
      if [[ "$line" =~ ${IDX_RE[$i]} ]]; then
        HIT_N[$i]=$(( ${HIT_N[$i]} + 1 ))
        TOTAL_HITS=$((TOTAL_HITS + 1))
        if [ "${HIT_N[$i]}" -le "$MAX_SAMPLES" ]; then
          HIT_SAMPLE[$i]="${HIT_SAMPLE[$i]}${lineno}	${line}
"
        fi
      fi
    done
  done
}

report() {                             # report <label>
  local i n id shown
  n=${#IDX_ID[@]}
  printf 'diagnose.sh — %s (%s lines)\n' "$1" "$N_LINES"
  for ((i = 0; i < n; i++)); do
    [ "${HIT_N[$i]}" -gt 0 ] || continue
    id="${IDX_ID[$i]}"
    shown="${HIT_N[$i]}"
    [ "$shown" -gt "$MAX_SAMPLES" ] && shown="$MAX_SAMPLES of ${HIT_N[$i]}"
    printf '\n▌ %s — %s\n' "$id" "$(sig_meta "$id" | head -1 | cut -d'|' -f2-)"
    printf '%s' "${HIT_SAMPLE[$i]}" | awk -F'\t' '{ printf "  %6s  %s\n", $1, substr($2, 1, 110) }'
    [ "${HIT_N[$i]}" -gt "$MAX_SAMPLES" ] && printf '  %6s  ... and %s more\n' "" "$(( ${HIT_N[$i]} - MAX_SAMPLES ))"
    sig_meta "$id" | tail -n +2 | while IFS= read -r l; do w "${l%%|*}" "${l#*|}"; done
  done

  # ---- whole-log verdicts.  Some failures have NO line to match, which is
  # exactly why they are dangerous: "no error found" must never read as "the
  # build happened" (§7.1a).
  if [ "$SAW_SUCCESS" = "1" ]; then
    printf '\n  BUILD     `Build completed successfully` IS present — the build happened.\n'
  elif [ "$SAW_ERROR" = "0" ]; then
    printf '\n▌ build-did-not-happen — no success line AND no error lines\n'
    w "CAUSE" "The log carries neither \`Build completed successfully\` nor a single error line. An argument error and a resource kill both emit no line the failure greps look for, and a scripted triad whose other gates still pass then LOOKS GREEN while lake build never ran."
    w "FIX" "Assert success POSITIVELY — grep for \`Build completed successfully\` — and check the build's exit status separately. Re-run and keep the full log."
    w "HOME" "docs/family-architecture.md §7.1a (the positive-assertion clause); implemented in tools/triad.sh"
  else
    printf '\n  BUILD     no `Build completed successfully` line — this log is not a green build.\n'
  fi

  if [ "$TOTAL_HITS" = "0" ] && [ "$SAW_SUCCESS" = "0" ]; then
    printf '\n'
    w "NO MATCH" "This decoder recognizes $(printf '%s\n' $SIG_IDS | grep -c .) failures and none of them is in this log. That is an HONEST MISS, not a clean bill: read the errors yourself, and when you find the cause, add it here with its incident (docs/backlog/qol.md). A decoder that says nothing must not be read as a decoder that found nothing wrong."
  fi
}

# --------------------------------------------------------------- self-test
# §5.4's law pointed at this script: every signature RUN, not listed. Each
# fixture goes through the SAME matcher the live path uses.
self_test() {
  local id i n ok=0 bad=0 fired want tmp
  build_index
  n=${#IDX_ID[@]}
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; \
            else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }

  for id in $SIG_IDS; do
    scan <<< "$(sig_fixture "$id")"
    fired=""
    for ((i = 0; i < n; i++)); do
      [ "${HIT_N[$i]}" -gt 0 ] && fired="${fired:+$fired,}${IDX_ID[$i]}"
    done
    want=0
    case ",$fired," in *",$id,"*) want=1 ;; esac
    check "$id fires on its own fixture" "$want" "1"
    # Every signature must also carry a complete annotation: a decoder that
    # matches and then says nothing is worse than one that does not match.
    check "$id has cause+fix+home+incident" \
          "$(sig_meta "$id" | cut -d'|' -f1 | tr '\n' ' ' | sed 's/ *$//')" \
          "TITLE CAUSE FIX HOME INCIDENT"
  done

  # A benign line must fire NOTHING — the false-positive direction.
  scan <<< "info: [3691/3693] Building LeanModels.Python.Semantics"
  check "a benign progress line fires nothing" "$TOTAL_HITS" "0"

  # A green log: the positive assertion must see it.
  scan <<< "Build completed successfully."
  check "a green log is recognized as green" "$SAW_SUCCESS" "1"

  # The whole-log verdict: no success line, no errors.
  tmp="$(printf 'info: starting\ninfo: nothing to do\n')"
  scan <<< "$tmp"
  check "silent log: no success line seen" "$SAW_SUCCESS" "0"
  check "silent log: no error lines seen"  "$SAW_ERROR" "0"
  check "silent log matches no signature"  "$TOTAL_HITS" "0"

  # And the multi-line path, so the sampler and counter are exercised too.
  scan <<< "$(printf 'a\nerror: unknown constant %s\nb\nerror: unknown constant %s\n' "'X'" "'Y'")"
  i=0; fired=""
  for ((i = 0; i < n; i++)); do
    [ "${IDX_ID[$i]}" = "unknown-constant" ] && fired="${HIT_N[$i]}"
  done
  check "two hits are counted, not deduped" "$fired" "2"
  check "and the error line was seen"       "$SAW_ERROR" "1"

  echo "self-test: $ok ok, $bad failed ($(printf '%s\n' $SIG_IDS | grep -c .) signatures)"
  [ "$bad" = "0" ] || return 1
  return 0
}

# -------------------------------------------------------------------- main
case "${1:---}" in
  --self-test) self_test; exit $? ;;
  --list)      list_signatures; exit 0 ;;
  --explain)
    [ $# -ge 2 ] || { echo "diagnose.sh: --explain needs a signature id" >&2; exit 2; }
    case " $(printf '%s ' $SIG_IDS)" in
      *" $2 "*) explain "$2"; exit 0 ;;
      *) echo "diagnose.sh: no signature '$2' — try --list" >&2; exit 2 ;;
    esac ;;
  -h|--help)   usage ;;
esac

build_index
if [ $# -eq 0 ]; then
  scan
  report "(stdin)"
else
  for f in "$@"; do
    case "$f" in -*) echo "diagnose.sh: unknown argument '$f'" >&2; usage ;; esac
    [ -r "$f" ] || { echo "diagnose.sh: cannot read '$f'" >&2; exit 2; }
    scan < "$f"
    report "$f"
  done
fi
