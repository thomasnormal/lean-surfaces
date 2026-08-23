import LeanModels.Python.Json
import LeanModels.Python.Semantics
import LeanModels.Python.Script
-- THE MONADIC REBUILD (docs/python-monadic-rebuild.md), pulled in through its
-- umbrella so `lake build` CHECKS the whole rebuild — interpreter, `@[spec]`
-- layer and demonstration gates — as a side effect of building the runner that
-- the acceptance gate drives.
--
-- WHY HERE AND NOT FROM `LeanModels.lean`: measured, 65 files under `Examples/`
-- import the `LeanModels` umbrella, including the expensive sunfish proofs. An
-- import there would invalidate every one of them for zero benefit, and would
-- charge that rebuild to the eleven other lanes sharing this master. The runner
-- is the one target that must know about the rebuild anyway.
import LeanModels.Python.Monadic

/-!
# `leanmodels-run` — CLI runner for the differential harness

`lake exe leanmodels-run <envelope.json> <function> [args…] [--fuel N]`

Loads the standardized envelope JSON at **runtime** (via the `Json.lean`
parser), calls `callFunction` on the named module-level function with the
given arguments (default fuel 10000), and prints exactly ONE line of
canonical JSON to stdout (DESIGN.md "Runner + differential harness").
Each argument is either an (arbitrary-precision) integer literal or a
canonical typed JSON value — the same `{"t":…,"v":…}` encoding the runner
prints — so list/tuple/str/bool/None arguments (sunfish's score lists and
game trees) get real differential rows:

* `{"status":"ok","value":V}`
* `{"status":"exn","exn":"ZeroDivisionError"}` (canonical `PyErr` names)
* `{"status":"timeout"}`
* `{"status":"unsupported","msg":"…"}`

where `V` is `{"t":"none"}` | `{"t":"bool","v":true}` | `{"t":"int","v":"55"}`
(decimal string) | `{"t":"str","v":"…"}` | `{"t":"list","v":[V…]}` |
`{"t":"tuple","v":[V…]}`.

Exit code: 0 whenever a canonical line was printed (semantic errors such as
`exn`/`timeout`/`unsupported` are *results*, not failures); nonzero on
usage errors (2) and envelope load/parse errors (1).

**Batch mode** (`--batch <jobs.jsonl> [--fuel N]`): one process, many
calls — the differential harness's shape, so 615 rows cost one `lake`
startup instead of 615. Each non-empty line of the jobs file is one job:

* `{"path":"….json","function":"f","args":[…],"fuel":N?,"clock":[…]?}`

with `args` elements either plain JSON integers or canonical typed
values (the same encoding as the CLI), `fuel` optional (default: the
command line's `--fuel`, else 10000), and `clock` an optional array of
integer readings seeding the world's CLOCK TRACE
(`callFunctionClock` — docs/memory-model.md §the trace clock; absent =
empty trace). Envelopes are parsed once per
distinct `path` and cached. Exactly ONE line is printed per job, in job
order, flushed as it is produced (a stalled consumer sees progress, not
silence). A job the runner itself cannot execute — unparsable line,
unreadable or invalid envelope — emits `{"status":"runner-error",
"msg":…}` on stdout (so the row count stays honest), mirrors the message
to stderr, and forces a nonzero exit: LOUD, never absorbed into the
stream as agreement.

**`--observations`** (2026-08-16, OPT-IN): with the flag, a `--batch`
line also carries what the run OBSERVED and not only what it returned
(`batchObs`). The public wrapper ERASES the world, so under the flag the
driver calls `callIn` directly and keeps it. Added fields, each "present
exactly when":

* `stdout` — the accumulated line list, present exactly when the run
  reached a world (`.ok`/`.exn`); the same field, the same shape and the
  same `World.stdout` as `--script-batch`, so a consumer's existing
  list-of-lines adapter reads it unchanged.
* `exnmsg` — present exactly when the model's `PyErr` carries a message,
  `--script-batch`'s rule verbatim.
* `args_after` — the arguments frozen against the POST-call heap — and
  `mutated`, the boolean off comparing them with the inputs. Present
  exactly when the run reached a world AND every argument freezes;
  otherwise `args_after_refused` says why.
* `class` — the model's own §5.2 REFUSAL CLASS (`unsupported`,
  `environment`, `order-dependence`, `undefined`), present exactly when
  `status` is `unsupported` and the refusal came from the INTERPRETER.
  `Run.unsupported` carries one `String`, so the public wrapper erases
  the class and a scoreboard is left parsing prose; under the flag the
  driver keeps it off the inner run, the same way it keeps the world.
  Absence means the run did not refuse — never "refused, unclassified"
  (`Monadic.refusalClass_isSome_iff`). A boundary-FREEZE refusal keeps a
  bare `status: unsupported` with no `class`, because it is a statement
  about the boundary and not about the tier.

WHY OPT-IN, since the fields are strictly additive: `harness/diff_test.py`
compares the model's line to a dict it builds itself by WHOLE-DICT
equality (`cpy == lean`), which is precisely the strictness a differential
wants and precisely what an extra key breaks. Emitting them by default
failed 1156 of 1271 cases on the first run — measured, not feared. Without
the flag the line is byte-identical to what `resJson` always printed.

**Script mode** (`--script <envelope.json> [--fuel N] [--clock i,j,k]`):
leanpy — execute the module's whole top level, print its stdout, exit
0 (ok) / 1 (exn) / 3 (unsupported) / 4 (timeout). `--clock` seeds the
CLOCK TRACE `time.time()` consumes (absent = the empty trace, so any
reading refuses with the loud underrun).

**Script batch mode** (`--script-batch <jobs.jsonl> [--fuel N]`): many
whole PROGRAMS, one process — the survey shape behind
`harness/leanpy_survey.py`, so a 200-file sweep costs one startup instead
of 200. Each non-empty line is `{"path":"….json","fuel":N?,"clock":[…]?}`
(a bare JSON string is shorthand for the path alone), and each produces
exactly one line

* `{"path":…,"status":"ok","exit":0,"live":N,"stdout":[…]}`
* `{"path":…,"status":"exn","exit":1,"exn":"NameError","exnmsg":…,"live":N,"stdout":[…]}`
  (`exnmsg` present exactly when the model's `PyErr` carries a message)
* `{"path":…,"status":"unsupported","exit":3,"live":N,"msg":…}`
* `{"path":…,"status":"timeout","exit":4,"live":N}`

carrying the SAME exit status the one-shot mode would have produced, plus
`live` — the number of top-level statements the executor was given, so a
definitions-only agreement (`live: 0`) is never counted as a real run.
Runner-level failures are `{"status":"runner-error",…}` rows plus a
nonzero exit, exactly as in `--batch`.
-/

open LeanModels.Python

/-- Canonical harness name of a `PyErr` (DESIGN.md "Exceptions" row). -/
def errName : PyErr → String
  | .typeError _ => "TypeError"
  | .nameError _ => "NameError"
  | .zeroDivisionError => "ZeroDivisionError"
  -- the same CLASS as the above; only the message differs
  | .zeroDivisionPow => "ZeroDivisionError"
  | .indexError => "IndexError"
  | .valueError _ => "ValueError"
  | .keyError => "KeyError"
  | .runtimeError _ => "RuntimeError"
  | .recursionError => "RecursionError"
  | .attributeError => "AttributeError"
  | .assertionError _ => "AssertionError"
  | .stopIteration => "StopIteration"
  -- Pass 0 (docs/memory-model.md §import forms): CPython 3.9 raises the
  -- SUBCLASS for a missing module, so the class line is exact
  | .importError _ => "ModuleNotFoundError"
  -- exceptions tier: CPython's `type(e).__name__` — the carried class name
  | .user _ name => name

/-- The MESSAGE a `PyErr` carries, when it carries one (2026-08-13).

CPython's uncaught-exception line is `ClassName: message`, and mapping
every exception to exit 1 means stdout + exit code cannot tell two apart —
the class comparison the harnesses gained closes that, and this is the
next resolution step down. `none` = the model's representation carries NO
message for this class, which is a real gap and is reported as its own
telemetry bucket rather than silently compared against CPython's text:
`IndexError` alone is "list index out of range" / "string index out of
range" / "tuple index out of range" in CPython, and the payload-free
constructor cannot say which. Never invent one here. -/
def errMessage : PyErr → Option String
  | .typeError msg => some msg
  | .nameError n => some s!"name '{n}' is not defined"
  | .valueError msg => some msg
  | .runtimeError msg => some msg
  -- `StopIteration` is raised BARE by CPython (`str(e)` is empty), so the
  -- class IS the whole line and this one is exact
  | .stopIteration => some ""
  -- the tail batch: `assert` renders its message through `printOne`, and
  -- a bare `assert` prints the class alone — both EXACT, so this
  -- constructor answers rather than reporting a gap
  | .assertionError msg => some (msg.getD "")
  -- Pass 0 (§import forms): CPython 3.9's exact text, module name in
  -- single quotes — EXACT, so this constructor answers rather than
  -- reporting a gap
  | .importError m => some s!"No module named '{m}'"
  -- ZeroDivisionError's two texts, split at the CONSTRUCTOR (2026-08-15,
  -- docs/backlog.md §the payload-free constructors): the class does not
  -- determine the message, but the RAISE CONDITION does, and both are
  -- statically distinguishable in `evalBinOp`. Measured verbatim against
  -- CPython 3.9.19 — 13 of the 14 raising cases in `harness/cases.json`
  -- take the first, `0 ** -1` the second.
  | .zeroDivisionError => some "integer division or modulo by zero"
  | .zeroDivisionPow => some "0.0 cannot be raised to a negative power"
  -- STILL payload-free, and deliberately so: these texts carry RUNTIME
  -- DATA the constructor does not hold, so no split can supply them —
  -- `IndexError` distinguishes list/tuple/assignment/pop (4 measured
  -- texts), `KeyError` prints the missing key's `repr`, `AttributeError`
  -- names the type AND the attribute. Reported as `ABSENT` by the
  -- survey's message telemetry, never invented; the priced plan for
  -- giving them payloads is in docs/backlog.md. `RecursionError` is the
  -- one that must STAY absent: CPython names the C site it hit
  -- ("maximum recursion depth exceeded in comparison"), which no model
  -- state determines.
  | .indexError | .keyError | .recursionError
  | .attributeError => Option.none
  -- a user exception raised bare (`raise Stop`) prints its class alone
  | .user _ _ => some ""

/-- JSON string literal with proper escaping (delegates to `Lean.Json`). -/
def jsonStr (s : String) : String :=
  (Lean.Json.str s).compress

/-- Canonical one-line JSON form of a value (exact field order per
DESIGN.md). `partial` only because of the nested `Array Val` recursion;
this is runtime-only code, nothing proves theorems about it. -/
partial def valJson : Val → String
  | .none => "{\"t\":\"none\"}"
  | .bool b => "{\"t\":\"bool\",\"v\":" ++ (if b then "true" else "false") ++ "}"
  | .int n => "{\"t\":\"int\",\"v\":" ++ jsonStr (toString n) ++ "}"
  | .str s => "{\"t\":\"str\",\"v\":" ++ jsonStr s ++ "}"
  | .list xs => "{\"t\":\"list\",\"v\":[" ++ ",".intercalate (xs.toList.map valJson) ++ "]}"
  | .tuple xs => "{\"t\":\"tuple\",\"v\":[" ++ ",".intercalate (xs.toList.map valJson) ++ "]}"

/-- Canonical one-line JSON form of an interpreter result. -/
def resJson : Res Val → String
  | .ok v => "{\"status\":\"ok\",\"value\":" ++ valJson v ++ "}"
  | .exn e => "{\"status\":\"exn\",\"exn\":" ++ jsonStr (errName e) ++ "}"
  | .timeout => "{\"status\":\"timeout\"}"
  | .unsupported msg => "{\"status\":\"unsupported\",\"msg\":" ++ jsonStr msg ++ "}"

/-- JSON array of strings (script stdout lines). -/
def jsonStrArray (xs : List String) : String :=
  "[" ++ ",".intercalate (xs.map jsonStr) ++ "]"

/-- The `exnmsg` clause, shared by every arm that can raise: present
exactly when the model's `PyErr` CARRIES a message. A constructor that
carries none makes no claim, and inventing one for it would be a claim
the semantics does not make. -/
def exnMsgField (e : PyErr) : String :=
  match errMessage e with
  | some msg => ",\"exnmsg\":" ++ jsonStr msg
  | Option.none => ""

/-- `--batch`'s OBSERVATION fields (2026-08-16 — the library lane's
request, and it arrived quantified: ALL 22 UNCOMPARABLE rows of the L1
library baseline are one gap, "the call printed; `--batch` reports no
stdout").

What `resJson` prints is a VALUE and an exception CLASS, because that is
everything `callFunction` returns — the public wrapper ERASES the world
(`Run.toPublic`). These come off the RUN instead, so the batch driver
calls `callIn` directly and keeps the world the wrapper throws away.
Every field carries a "present exactly when" rule — the convention
`--script-batch` already states — so a consumer can tell absence from
emptiness:

* `stdout` — the accumulated line list, present exactly when the run
  reached a WORLD (`.ok`/`.exn`). The same field off the same
  `World.stdout` as `--script-batch`, in the same shape, so the survey's
  existing list-of-lines adapter reads it with no change.
* `args_after` / `mutated` — the arguments AS THEY STAND AFTER THE CALL,
  each frozen through the boundary against the POST-call heap, plus the
  boolean the oracle already computes (`args != before`). DERIVED, never
  asserted, and that distinction is the whole design: today a `Val.list`
  thaws to an IMMEDIATE `RVal.listV`, so a callee cannot reach a caller's
  argument and `mutated` comes out false — which is a claim worth
  PRINTING rather than omitting, because CPython's `insort` mutates and
  the two answers then DISAGREE instead of being counted unverified. When
  lists move to the heap at H2 the same expression reads the real
  mutation with no edit here.

Both are present exactly when the run reached a world; `args_after` and
`mutated` additionally require every argument to FREEZE, and otherwise
`args_after_refused` carries the reason — a silently dropped field would
read as "nothing changed". -/
def batchObs (fuel : Nat) (inArgs : Array Val) (thawed : Array RVal)
    (w : World) : String :=
  ",\"stdout\":" ++ jsonStrArray w.stdout
    ++ (match RVal.freezeListB w.heap fuel thawed.toList with
        | .ok vs =>
            ",\"args_after\":[" ++ ",".intercalate (vs.map valJson) ++ "]"
              ++ ",\"mutated\":" ++ (if vs.toArray == inArgs then "false" else "true")
        | .unsupported msg => ",\"args_after_refused\":" ++ jsonStr msg
        | .exn e =>
            ",\"args_after_refused\":"
              ++ jsonStr ("freezing an argument raised " ++ errName e)
        | .timeout =>
            ",\"args_after_refused\":"
              ++ jsonStr "freezing an argument exhausted the boundary fuel")

/-- `resJson` PLUS `batchObs`, taken off the RUN rather than the public
result. The status/value/exn fields are `resJson`'s verbatim — including
the arm where the boundary FREEZE itself refuses, which stays a
`status: unsupported` line and now also says what was printed on the way
there. `.timeout`/`.unsupported` reached no world, so they carry nothing
extra and are byte-identical to before. -/
def batchResJson (fuel : Nat) (inArgs : Array Val) (thawed : Array RVal)
    (cls : Option String) :
    Run World RVal → String
  | .ok w v =>
      (match RVal.freezeB w.heap fuel v with
       | .ok pv => "{\"status\":\"ok\",\"value\":" ++ valJson pv
       | .exn e => "{\"status\":\"exn\",\"exn\":" ++ jsonStr (errName e) ++ exnMsgField e
       | .timeout => "{\"status\":\"timeout\""
       | .unsupported msg => "{\"status\":\"unsupported\",\"msg\":" ++ jsonStr msg)
        ++ batchObs fuel inArgs thawed w ++ "}"
  | .exn w e =>
      "{\"status\":\"exn\",\"exn\":" ++ jsonStr (errName e) ++ exnMsgField e
        ++ batchObs fuel inArgs thawed w ++ "}"
  | .timeout => "{\"status\":\"timeout\"}"
  | .unsupported msg =>
      -- THE §5.2 CLASS, and it rides on this arm ALONE. `refusalClass` is
      -- `some` exactly on the runs whose `Run` projection is `unsupported`
      -- (`Monadic.refusalClass_isSome_iff`), so a consumer reading `class`
      -- never has to ask whether its absence means "not classified" or "did
      -- not refuse" — it means the latter, and only the latter.
      "{\"status\":\"unsupported\",\"msg\":" ++ jsonStr msg
        ++ (match cls with
            | some c => ",\"class\":" ++ jsonStr c
            | Option.none => "")
        ++ "}"

/-- Decode a canonical typed JSON value — the inverse of `valJson`
(same encoding, DESIGN.md). `partial` like `valJson`: runtime-only. -/
partial def valOfJson (j : Lean.Json) : Except String Val := do
  let t ← (j.getObjVal? "t").mapError (fun _ => s!"missing \"t\": {j.compress}")
  let tstr ← t.getStr?.mapError (fun _ => s!"\"t\" must be a string: {j.compress}")
  match tstr with
  | "none" => return .none
  | "bool" => return .bool (← (← j.getObjVal? "v").getBool?)
  | "int" =>
    let v ← j.getObjVal? "v"
    match v.getStr? with
    | .ok s =>
      match s.toInt? with
      | some n => return .int n
      | Option.none => throw s!"\"int\" value is not a decimal string: {s}"
    | .error _ =>  -- accept a plain JSON number too (harness convenience)
      return .int (← v.getInt?)
  | "str" => return .str (← (← j.getObjVal? "v").getStr?)
  | "list" =>
    let elts ← (← j.getObjVal? "v").getArr?
    return .list (← elts.mapM valOfJson)
  | "tuple" =>
    let elts ← (← j.getObjVal? "v").getArr?
    return .tuple (← elts.mapM valOfJson)
  | other => throw s!"unknown value tag {other.quote}"

/-- Parsed command line. -/
structure Cli where
  path : String
  fname : String
  args : Array Val
  fuel : Nat

def usage : String :=
  "usage: leanmodels-run <envelope.json> <function> [args...] [--fuel N]\n" ++
  "  args: integer literals or canonical typed JSON values " ++
  "({\"t\":\"list\",\"v\":[…]} — the encoding the runner prints); default fuel 10000"

/-- Split `--clock i,j,k` off the argument list (anywhere; last wins) —
the CLOCK TRACE `time.time()` consumes in order, script mode's counterpart
of a batch job's `"clock"` field. `--clock ''` is the explicit empty trace
(the default; every reading then refuses with the loud underrun). -/
private def splitClock : List String → Except String (List String × Option (List Int))
  | [] => .ok ([], Option.none)
  | "--clock" :: rest =>
    match rest with
    | [] => .error "--clock expects a comma-separated list of integers"
    | spec :: rest' => do
      let readings ←
        if spec.trim.isEmpty then .ok ([] : List Int)
        else (spec.splitOn ",").mapM fun r =>
          match r.trim.toInt? with
          | some n => .ok n
          | Option.none => .error s!"--clock readings must be integers, got '{r}'"
      let (pos, later) ← splitClock rest'
      return (pos, some (later.getD readings))
  | a :: rest => do
      let (pos, clock) ← splitClock rest
      return (a :: pos, clock)

/-- Split `--fuel N` off the argument list (anywhere; last wins), keeping the
positional arguments in order. -/
private def splitFuel : List String → Except String (List String × Option Nat)
  | [] => .ok ([], Option.none)
  | "--fuel" :: rest =>
    match rest with
    | [] => .error "--fuel expects a value"
    | n :: rest' =>
      match n.toNat? with
      | some fuel => do
          let (pos, later) ← splitFuel rest'
          return (pos, some (later.getD fuel))
      | Option.none => .error s!"--fuel expects a natural number, got '{n}'"
  | a :: rest => do
      let (pos, fuel) ← splitFuel rest
      return (a :: pos, fuel)


def parseCli (argv : List String) : Except String Cli := do
  let (positional, fuel?) ← splitFuel argv
  match positional with
  | path :: fname :: argStrs => do
      let args ← argStrs.mapM fun a =>
        match a.toInt? with
        | some n => .ok (Val.int n)
        | Option.none =>
          match Lean.Json.parse a with
          | .ok j => valOfJson j
          | .error _ =>
            .error s!"arguments must be integers or canonical typed JSON values, got '{a}'"
      return { path, fname, args := args.toArray, fuel := fuel?.getD 10000 }
  | _ => .error "expected <envelope.json> <function>"

/-- `leanpy` v0 script mode (`--script`): execute the module's top level
(`runScript`, Script.lean), print the accumulated stdout chunks as lines,
and map the outcome to the process exit status (docs/memory-model.md
§effects — exit status is the RUNNER boundary):

* `ok` → 0 (stdout printed);
* `exn e` → 1, stdout-so-far printed, the exception CLASS LINE on stderr
  (CPython convention's comparable slice);
* `unsupported` → 3, the construct report on stderr — LOUD, the
  differential driver must never read it as agreement;
* `timeout` → 4 (loud likewise).
-/
def runScriptMode (m : Module) (clock : List Int) (fuel : Nat) : IO UInt32 := do
  match Monadic.runScriptClockMono m clock fuel with
  | .ok w () =>
      for line in w.stdout do IO.println line
      return 0
  | .exn w e =>
      for line in w.stdout do IO.println line
      IO.eprintln (match errMessage e with
        | some "" => errName e
        | some msg => s!"{errName e}: {msg}"
        | Option.none => errName e)
      return 1
  | .unsupported msg =>
      IO.eprintln s!"leanpy-unsupported: {msg}"
      return 3
  | .timeout =>
      IO.eprintln "leanpy-timeout"
      return 4

/-- Canonical one-line JSON form of a SCRIPT outcome, carrying the exit
status the one-shot `--script` mode would have produced — so the batch
stream and the process boundary can never disagree about what counts as
agreement (`exit` 0/1 are outcomes, 3/4 are LOUD). `stdout` is the
accumulated line list, present exactly when the run reached a world.

`live` is HOW MUCH TOP LEVEL THE LIVE RUN EXECUTED: since THE ONE
PIPELINE (docs/memory-model.md §the one pipeline) that is the whole top
level — every statement goes through the script executor, nothing is
folded into an `initWorld` the run then skips. A definitions-only module
has `live = 0` — its `def`s and `class`es are ingestion tables, so it
ingests and finishes silently, which agrees with CPython on stdout and
exit code but exercises no executor step; a survey that did not report
this could not tell a real run from a vacuous one. -/
def scriptJson (path : String) (live : Nat) : Run World Unit → String
  | .ok w () =>
      "{\"path\":" ++ jsonStr path ++ ",\"status\":\"ok\",\"exit\":0,\"live\":"
        ++ toString live ++ ",\"stdout\":" ++ jsonStrArray w.stdout ++ "}"
  | .exn w e =>
      "{\"path\":" ++ jsonStr path ++ ",\"status\":\"exn\",\"exit\":1,\"exn\":"
        ++ jsonStr (errName e)
        ++ (match errMessage e with
            | some msg => ",\"exnmsg\":" ++ jsonStr msg
            | Option.none => "")
        ++ ",\"live\":" ++ toString live
        ++ ",\"stdout\":" ++ jsonStrArray w.stdout ++ "}"
  | .unsupported msg =>
      "{\"path\":" ++ jsonStr path ++ ",\"status\":\"unsupported\",\"exit\":3,\"live\":"
        ++ toString live ++ ",\"msg\":" ++ jsonStr msg ++ "}"
  | .timeout =>
      "{\"path\":" ++ jsonStr path ++ ",\"status\":\"timeout\",\"exit\":4,\"live\":"
        ++ toString live ++ "}"

/-- One parsed job line of `--batch` mode. `clock` is the optional
CLOCK TRACE (pass 6, docs/memory-model.md §the trace clock): integer
readings `time.time()` consumes in order — the model side of the
harness's record-replay protocol. Absent = empty trace (any reachable
`time.time()` refuses with the loud underrun). -/
structure BatchJob where
  path : String
  fname : String
  args : Array Val
  fuel : Option Nat
  clock : Option (List Int)

/-- Parse one jobs-file line. Every failure message carries the line, so
a bad row in a 615-row file is findable without counting. -/
def parseJob (line : String) : Except String BatchJob := do
  let j ← (Lean.Json.parse line).mapError
    (fun e => s!"not JSON ({e}): {line}")
  let path ← ((j.getObjVal? "path").bind (·.getStr?)).mapError
    (fun _ => s!"job needs a string \"path\": {line}")
  let fname ← ((j.getObjVal? "function").bind (·.getStr?)).mapError
    (fun _ => s!"job needs a string \"function\": {line}")
  let argsJ ← ((j.getObjVal? "args").bind (·.getArr?)).mapError
    (fun _ => s!"job needs an \"args\" array: {line}")
  let args ← argsJ.mapM fun a =>
    match a.getInt? with
    | .ok n => .ok (Val.int n)
    | .error _ => valOfJson a
  let fuel? ← match j.getObjVal? "fuel" with
    | .error _ => pure Option.none
    | .ok f =>
      match f.getNat? with
      | .ok n => pure (some n)
      | .error _ => throw s!"\"fuel\" must be a natural number: {line}"
  let clock? ← match j.getObjVal? "clock" with
    | .error _ => pure Option.none
    | .ok c =>
      match c.getArr? with
      | .ok arr => do
        let readings ← arr.mapM fun r =>
          match r.getInt? with
          | .ok n => .ok n
          | .error _ => throw s!"\"clock\" entries must be integers: {line}"
        pure (some readings.toList)
      | .error _ => throw s!"\"clock\" must be an array of integers: {line}"
  return { path, fname, args, fuel := fuel?, clock := clock? }

/-- `--batch` driver: one canonical line per job, in order, flushed per
line; envelopes cached by path; runner-level failures are per-row
`runner-error` lines PLUS a nonzero exit. -/
def runBatchMode (jobsPath : String) (defaultFuel : Nat) (obs : Bool) : IO UInt32 := do
  match ← (IO.FS.readFile ⟨jobsPath⟩).toBaseIO with
  | .error e =>
      IO.eprintln s!"leanmodels-run --batch: cannot read '{jobsPath}': {toString e}"
      return 1
  | .ok contents =>
      let stdout ← IO.getStdout
      let mut cache : List (String × Module) := []
      let mut hadError := false
      for line in contents.splitOn "\n" do
        if line.trim.isEmpty then
          continue
        -- Resolve the job to either a module+call or a runner error.
        let outcome : Except String (Module × BatchJob) ← do
          match parseJob line with
          | .error e => pure (.error e)
          | .ok job =>
            match cache.find? (·.1 == job.path) with
            | some (_, m) => pure (.ok (m, job))
            | Option.none =>
              match ← (IO.FS.readFile ⟨job.path⟩).toBaseIO with
              | .error e => pure (.error s!"cannot read '{job.path}': {toString e}")
              | .ok raw =>
                match parseEnvelopeString raw with
                | .error e => pure (.error s!"'{job.path}' is not a valid envelope: {e}")
                | .ok envl =>
                  if envl.language == "python" then do
                    cache := (job.path, envl.module) :: cache
                    pure (.ok (envl.module, job))
                  else
                    pure (.error s!"'{job.path}' has language '{envl.language}', expected 'python'")
        match outcome with
        | .error e =>
            hadError := true
            IO.eprintln s!"leanmodels-run --batch: {e}"
            stdout.putStrLn ("{\"status\":\"runner-error\",\"msg\":" ++ jsonStr e ++ "}")
        | .ok (m, job) =>
            -- `callIn` rather than `callFunction`, and it is the SAME run:
            -- the public wrapper IS `Run.toPublic ∘ callIn ∘ thaw` over a
            -- fresh world, and `callFunction m f args fuel` is definitionally
            -- `callFunctionClock m f args [] fuel` (the `clock := []` default).
            -- Unrolling it one step is what keeps the post-call WORLD, which
            -- `Run.toPublic` erases and `batchObs` reports.
            let fuel := job.fuel.getD defaultFuel
            let thawed := RVal.thawArgs job.args
            -- THE INTERPRETER. `callInMono` had `callIn`'s type by construction
            -- (`Monadic/Eval.lean` §4), which is what let the two be compared
            -- row for row; the gate passed and the dual mode is gone.
            -- ONE EXECUTION, TWO PROJECTIONS. `callInRaw` is the inner
            -- value `toRun` projects, and `Monadic.callInMono_eq_ofHalt` is
            -- the theorem that `ofHalt raw` IS what this line used to compute
            -- -- so the class is bought without running the interpreter twice
            -- and without the two answers being able to drift.
            let raw := Monadic.callInRaw m fuel
              { initWorld m with clock := job.clock.getD [] } job.fname thawed
            let run := Monadic.ofHalt raw
            stdout.putStrLn (if obs then
                               batchResJson fuel job.args thawed
                                 (Monadic.refusalClass raw) run
                             else resJson (Run.toPublic fuel run))
        stdout.flush
      return (if hadError then 1 else 0)

/-- One parsed job line of `--script-batch` mode: a whole PROGRAM to run,
so there is no function name and no arguments — only the envelope, its
fuel, and its clock trace. -/
structure ScriptJob where
  path : String
  fuel : Option Nat
  clock : Option (List Int)

/-- Parse one `--script-batch` jobs-file line. A bare JSON string is
accepted as shorthand for `{"path": …}` — a survey over a directory is a
list of paths and nothing else. -/
def parseScriptJob (line : String) : Except String ScriptJob := do
  let j ← (Lean.Json.parse line).mapError
    (fun e => s!"not JSON ({e}): {line}")
  match j.getStr? with
  | .ok path => return { path, fuel := Option.none, clock := Option.none }
  | .error _ =>
    let path ← ((j.getObjVal? "path").bind (·.getStr?)).mapError
      (fun _ => s!"script job needs a string \"path\": {line}")
    let fuel? ← match j.getObjVal? "fuel" with
      | .error _ => pure Option.none
      | .ok f =>
        match f.getNat? with
        | .ok n => pure (some n)
        | .error _ => throw s!"\"fuel\" must be a natural number: {line}"
    let clock? ← match j.getObjVal? "clock" with
      | .error _ => pure Option.none
      | .ok c =>
        match c.getArr? with
        | .ok arr => do
          let readings ← arr.mapM fun r =>
            match r.getInt? with
            | .ok n => .ok n
            | .error _ => throw s!"\"clock\" entries must be integers: {line}"
          pure (some readings.toList)
        | .error _ => throw s!"\"clock\" must be an array of integers: {line}"
    return { path, fuel := fuel?, clock := clock? }

/-- `--script-batch` driver: leanpy's SURVEY shape — many whole programs,
one process, one canonical `scriptJson` line each in job order, flushed as
it is produced. Envelopes are deliberately NOT cached (each program runs
once; a corpus sweep must not accumulate every module it has seen).
Runner-level failures are per-row `runner-error` lines PLUS a nonzero exit
— LOUD, never absorbed into the stream as agreement. -/
def runScriptBatchMode (jobsPath : String) (defaultFuel : Nat) : IO UInt32 := do
  match ← (IO.FS.readFile ⟨jobsPath⟩).toBaseIO with
  | .error e =>
      IO.eprintln s!"leanmodels-run --script-batch: cannot read '{jobsPath}': {toString e}"
      return 1
  | .ok contents =>
      let stdout ← IO.getStdout
      let mut hadError := false
      for line in contents.splitOn "\n" do
        if line.trim.isEmpty then
          continue
        -- a runner error keeps the job's PATH whenever the line parsed, so a
        -- survey attributes the failure to the file instead of losing it
        let outcome : Except (Option String × String) (Module × ScriptJob) ← do
          match parseScriptJob line with
          | .error e => pure (.error (Option.none, e))
          | .ok job =>
            match ← (IO.FS.readFile ⟨job.path⟩).toBaseIO with
            | .error e => pure (.error (some job.path, s!"cannot read '{job.path}': {toString e}"))
            | .ok raw =>
              match parseEnvelopeString raw with
              | .error e =>
                  pure (.error (some job.path, s!"'{job.path}' is not a valid envelope: {e}"))
              | .ok envl =>
                if envl.language == "python" then
                  pure (.ok (envl.module, job))
                else
                  pure (.error (some job.path,
                    s!"'{job.path}' has language '{envl.language}', expected 'python'"))
        match outcome with
        | .error (path?, e) =>
            hadError := true
            IO.eprintln s!"leanmodels-run --script-batch: {e}"
            stdout.putStrLn ((match path? with
                | some p => "{\"path\":" ++ jsonStr p ++ ",\"status\":\"runner-error\""
                | Option.none => "{\"status\":\"runner-error\"")
              ++ ",\"exit\":1,\"msg\":" ++ jsonStr e ++ "}")
        | .ok (m, job) =>
            stdout.putStrLn (scriptJson job.path m.topLevel.size
              (Monadic.runScriptClockMono m (job.clock.getD []) (job.fuel.getD defaultFuel)))
        stdout.flush
      return (if hadError then 1 else 0)

def main (argv : List String) : IO UInt32 := do
  match argv with
  | "--batch" :: rest =>
    match splitFuel rest with
    | .error e =>
        IO.eprintln s!"leanmodels-run --batch: {e}"
        return 2
    | .ok (positional, fuel?) =>
      -- `--observations` is OPT-IN, and the reason is a measured one: the
      -- differential harness compares the model's line to a dict it builds
      -- itself, by WHOLE-DICT equality (`cpy == lean`, harness/diff_test.py),
      -- which is exactly the strictness that differential wants and exactly
      -- what an "additive" field breaks. Turning the fields on by default
      -- failed 1156 of 1271 cases on the first run. So the result line stays
      -- byte-identical for every consumer that did not ask.
      let obs := positional.contains "--observations"
      let positional := positional.filter (· != "--observations")
      let some jobsPath := (match positional with | [p] => some p | _ => Option.none)
        | do
            IO.eprintln
              "usage: leanmodels-run --batch <jobs.jsonl> [--fuel N] [--observations]"
            return 2
      runBatchMode jobsPath (fuel?.getD 10000) obs
  | "--script-batch" :: rest =>
    match splitFuel rest with
    | .error e =>
        IO.eprintln s!"leanmodels-run --script-batch: {e}"
        return 2
    | .ok (positional, fuel?) =>
      match positional with
      | [jobsPath] => runScriptBatchMode jobsPath (fuel?.getD 1000000)
      | _ =>
          IO.eprintln "usage: leanmodels-run --script-batch <jobs.jsonl> [--fuel N]"
          return 2
  | "--script" :: rest =>
    -- leanpy: `leanmodels-run --script <envelope.json> [--fuel N] [--clock i,j]`
    -- (default fuel 1000000: fuel is a depth/iteration bound and concrete
    -- runs cost time proportional to steps, so generosity is free)
    match splitClock rest >>= fun (rest', clock?) =>
          (splitFuel rest').map (fun (pos, fuel?) => (pos, fuel?, clock?)) with
    | .error e =>
        IO.eprintln s!"leanmodels-run --script: {e}"
        return 2
    | .ok (positional, fuel?, clock?) =>
      let some path := (match positional with | [p] => some p | _ => Option.none)
        | do
            IO.eprintln "usage: leanmodels-run --script <envelope.json> [--fuel N] [--clock i,j,k]"
            return 2
      match ← (IO.FS.readFile ⟨path⟩).toBaseIO with
      | .error e =>
          IO.eprintln s!"leanmodels-run --script: cannot read '{path}': {toString e}"
          return 1
      | .ok contents =>
        match parseEnvelopeString contents with
        | .error e =>
            IO.eprintln s!"leanmodels-run --script: '{path}' is not a valid envelope: {e}"
            return 1
        | .ok envl =>
            unless envl.language == "python" do
              IO.eprintln s!"leanmodels-run --script: '{path}' has language '{envl.language}', expected 'python'"
              return 1
            runScriptMode envl.module (clock?.getD []) (fuel?.getD 1000000)
  | _ =>
  match parseCli argv with
  | .error e =>
      IO.eprintln s!"leanmodels-run: {e}"
      IO.eprintln usage
      return 2
  | .ok cli =>
    match ← (IO.FS.readFile ⟨cli.path⟩).toBaseIO with
    | .error e =>
        IO.eprintln s!"leanmodels-run: cannot read '{cli.path}': {toString e}"
        return 1
    | .ok contents =>
      match parseEnvelopeString contents with
      | .error e =>
          IO.eprintln s!"leanmodels-run: '{cli.path}' is not a valid envelope: {e}"
          return 1
      | .ok envl => do
          unless envl.language == "python" do
            IO.eprintln
              s!"leanmodels-run: '{cli.path}' has language '{envl.language}', expected 'python'"
            return 1
          -- The single-call surface runs the same interpreter as the batteries:
          -- `callFunction` was `Run.toPublic ∘ callIn ∘ thaw` over a fresh world,
          -- and this is that with the rebuilt entry point.
          IO.println (resJson (Run.toPublic cli.fuel
            (Monadic.callInMono envl.module cli.fuel (initWorld envl.module)
              cli.fname (RVal.thawArgs cli.args))))
          return 0
