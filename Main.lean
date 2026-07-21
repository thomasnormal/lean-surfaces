import LeanModels.Python.Json
import LeanModels.Python.Semantics

/-!
# `leanmodels-run` — CLI runner for the differential harness

`lake exe leanmodels-run <envelope.json> <function> [args…] [--fuel N]`

Loads the standardized envelope JSON at **runtime** (via the `Json.lean`
parser), calls `callFunction` on the named module-level function with the
given integer arguments (default fuel 10000), and prints exactly ONE line of
canonical JSON to stdout (DESIGN.md "Runner + differential harness"):

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
-/

open LeanModels.Python

/-- Canonical harness name of a `PyErr` (DESIGN.md "Exceptions" row). -/
def errName : PyErr → String
  | .typeError _ => "TypeError"
  | .nameError _ => "NameError"
  | .zeroDivisionError => "ZeroDivisionError"
  | .indexError => "IndexError"
  | .valueError _ => "ValueError"

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

/-- Parsed command line. -/
structure Cli where
  path : String
  fname : String
  args : Array Val
  fuel : Nat

def usage : String :=
  "usage: leanmodels-run <envelope.json> <function> [args...] [--fuel N]\n" ++
  "  args are parsed as (arbitrary-precision) integers; default fuel 10000"

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
        | Option.none => .error s!"arguments must be integers, got '{a}'"
      return { path, fname, args := args.toArray, fuel := fuel?.getD 10000 }
  | _ => .error "expected <envelope.json> <function>"

def main (argv : List String) : IO UInt32 := do
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
