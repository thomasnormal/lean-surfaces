import LeanModels.Python.Json
import LeanModels.Python.Semantics
import LeanModels.Python.Script

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
-/

open LeanModels.Python

/-- Canonical harness name of a `PyErr` (DESIGN.md "Exceptions" row). -/
def errName : PyErr → String
  | .typeError _ => "TypeError"
  | .nameError _ => "NameError"
  | .zeroDivisionError => "ZeroDivisionError"
  | .indexError => "IndexError"
  | .valueError _ => "ValueError"
  | .keyError => "KeyError"
  | .runtimeError _ => "RuntimeError"
  | .recursionError => "RecursionError"
  | .attributeError => "AttributeError"
  | .stopIteration => "StopIteration"
  -- exceptions tier: CPython's `type(e).__name__` — the carried class name
  | .user _ name => name

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
def runScriptMode (m : Module) (fuel : Nat) : IO UInt32 := do
  match runScript m fuel with
  | .ok w () =>
      for line in w.stdout do IO.println line
      return 0
  | .exn w e =>
      for line in w.stdout do IO.println line
      IO.eprintln (errName e)
      return 1
  | .unsupported msg =>
      IO.eprintln s!"leanpy-unsupported: {msg}"
      return 3
  | .timeout =>
      IO.eprintln "leanpy-timeout"
      return 4

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
def runBatchMode (jobsPath : String) (defaultFuel : Nat) : IO UInt32 := do
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
            stdout.putStrLn (resJson (match job.clock with
              | some clock =>
                  callFunctionClock m job.fname job.args clock
                    (job.fuel.getD defaultFuel)
              | Option.none =>
                  callFunction m job.fname job.args (job.fuel.getD defaultFuel)))
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
      let some jobsPath := (match positional with | [p] => some p | _ => Option.none)
        | do
            IO.eprintln "usage: leanmodels-run --batch <jobs.jsonl> [--fuel N]"
            return 2
      runBatchMode jobsPath (fuel?.getD 10000)
  | "--script" :: rest =>
    -- leanpy v0: `leanmodels-run --script <envelope.json> [--fuel N]`
    -- (default fuel 1000000: fuel is a depth/iteration bound and concrete
    -- runs cost time proportional to steps, so generosity is free)
    match splitFuel rest with
    | .error e =>
        IO.eprintln s!"leanmodels-run --script: {e}"
        return 2
    | .ok (positional, fuel?) =>
      let some path := (match positional with | [p] => some p | _ => Option.none)
        | do
            IO.eprintln "usage: leanmodels-run --script <envelope.json> [--fuel N]"
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
            runScriptMode envl.module (fuel?.getD 1000000)
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
          IO.println (resJson (callFunction envl.module cli.fname cli.args cli.fuel))
          return 0
