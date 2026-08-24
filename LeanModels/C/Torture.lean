import LeanModels.C.Load
import LeanModels.C.C23

/-!
# `c-torture-run` — inch 6's batch driver, and the tier's first NUMBER

`docs/c23-goal.md` §4.2 specced a scoreboard and did not build one. This
is it: a `lean_exe` that reads a MANIFEST of ingested `gcc.c-torture`
tests, runs each one's `main`, and prints one verdict per test followed by
the summary the tier's §9.0 number is read off.

## THE CORPUS IS NEVER IN THIS REPOSITORY

`gcc.c-torture` is **GPL-3.0-or-later** (`docs/c23-goal.md` §2, measured:
0 of the sampled files carry a per-file header, so they inherit GCC's).
`tools/c_corpus_fetch.py` fetches it AT A PIN into a cache OUTSIDE the
tree and refuses to write inside it; what the repository holds is a
manifest of **hashes and verdicts**, which is not the corpus. This driver
never sees a `.c` file — only the `c-0.1` envelopes the extractor
produced from one.

## THE ZEROES ARE NOT THE SAME ZERO

The summary distinguishes them, because a scoreboard that prints one `0`
for all of these is unreadable and, worse, unfalsifiable — it cannot tell
*"the model declined"* from *"nobody ran it."*

| state | what happened | whose fact |
| --- | --- | --- |
| `not-fetched` | the file was never obtained at the pin | the fetch |
| `not-parsed` | clang rejected it under the pinned profile | the FRONTEND, not the model |
| `refused` | the model saw it and declined — cause kept apart | the tier's frontier |
| `timeout` | fuel ran out | the fuel bound |
| `failed` | the program reached `abort()` | **scored** |
| `passed` | `main` returned | **scored** |

**`scored = passed + failed`, and that is the oracle's own reading.**
`docs/c23-goal.md` §1.2: torture's verdict style is *exit status —
`abort()` on failure, fall off `main` on success*. Reaching `abort` is
therefore a RESULT, not a refusal to produce one: the program ran and its
own check failed. Pooling it with `refused` would hide the only failures
this scoreboard can currently see.
-/

namespace LeanModels.C.C23.Torture

open LeanModels.C

/-- What one test did. Constructors, not strings, so the summary buckets
on the TYPE and never by parsing prose (`Core`'s `RefusalCause` rule, one
level up). -/
inductive Verdict where
  | passed
  | failed                       -- reached `abort()`: the test's own check failed
  | refusedUB (what : String)
  | refusedLibc (name : String)
  | unsupported (what : String)
  | timeout
  | notParsed (why : String)
  | notFetched
deriving Repr, Inhabited, BEq

/-- Is this a SCORE — a verdict the oracle can read — as opposed to an
absence of one? -/
def Verdict.isScored : Verdict → Bool
  | .passed | .failed => true
  | _ => false

def Verdict.token : Verdict → String
  | .passed => "passed"
  | .failed => "failed"
  | .refusedUB _ => "refused-ub"
  | .refusedLibc _ => "refused-libc"
  | .unsupported _ => "refused-unsupported"
  | .timeout => "timeout"
  | .notParsed _ => "not-parsed"
  | .notFetched => "not-fetched"

def Verdict.detail : Verdict → String
  | .passed | .failed | .timeout | .notFetched => ""
  | .refusedUB w => w
  | .refusedLibc n => n
  | .unsupported w => w
  | .notParsed w => w

/-! ## The layout, from the PROFILE and not from a host

`docs/c-profile.md` pins `char_bit_8`, `int_32`, `long_64`. A spelling
outside the table gets `none`, which is a loud refusal at the use site
rather than a guessed size — the same discipline `Layout.unknown` exists
for. -/
def torSize : CType → Option Nat
  | "char" | "signed char" | "unsigned char" | "_Bool" => some 1
  | "short" | "short int" | "unsigned short" => some 2
  | "int" | "unsigned int" | "const int" | "unsigned" => some 4
  | "long" | "unsigned long" | "long long" | "unsigned long long"
  | "long int" | "unsigned long int" => some 8
  | t => if t.endsWith "*" then some 8 else none

def torLayout : Layout := { Layout.unknown with size := torSize }

/-- Run one ingested test: call its `main` with no arguments, from an
empty memory, and read the outcome.

`abort` is NOT modelled and never will be by widening the libc slice —
reaching it is the oracle's failure signal, so it is caught here by NAME
and turned into a verdict rather than left as an environment refusal. -/
def scoreEnvelope (fuel : Nat) (envl : Envelope) : Verdict :=
  let prog : Program := { fns := envl.unit.functionDefns, layout := torLayout }
  match ExecM.verdict Mem.empty (callByName fuel prog "main" []) with
  | .ok _ => .passed
  | .refused (.libc "abort") => .failed
  | .refused (.libc n) => .refusedLibc n
  | .refused (.valueUB u) => .refusedUB (toString (repr u))
  | .refused (.memUB f) => .refusedUB (toString (repr f))
  | .unsupported w => .unsupported w
  | .timeout => .timeout

/-! ## The manifest

`{ "pin": {...}, "tests": [ { "name":…, "status":"parsed"|"rejected"|"absent",
"envelope":…, "why":… } ] }` — produced by `tools/c_corpus_fetch.py`, in
NAME ORDER, and the order is load-bearing: the summary quotes the FIRST
failure, and "first" has to mean something stable. -/

structure Entry where
  name : String
  status : String
  envelope : Option String
  why : String
deriving Inhabited

private def str? (j : Lean.Json) (k : String) : String :=
  (j.getObjValAs? String k).toOption.getD ""

def parseEntry (j : Lean.Json) : Entry :=
  let env := str? j "envelope"
  { name := str? j "name", status := str? j "status"
    envelope := if env.isEmpty then none else some env
    why := str? j "why" }

def runEntry (fuel : Nat) (e : Entry) : IO Verdict := do
  match e.status, e.envelope with
  | "absent", _ => pure .notFetched
  | "rejected", _ => pure (.notParsed e.why)
  | _, none => pure (.notParsed "manifest says parsed but names no envelope")
  | _, some p =>
      match ← (IO.FS.readFile ⟨p⟩).toBaseIO with
      | .error err => pure (.notParsed s!"cannot read envelope: {toString err}")
      | .ok contents =>
          match parseEnvelopeString contents with
          | .error err => pure (.notParsed s!"not a c-0.1 envelope: {err}")
          | .ok envl => pure (scoreEnvelope fuel envl)

/-! ## The summary

**The first failure is printed VERBATIM, in log order.** Not the
lexicographically smallest, not one of a deduplicated set: the first one
the run met. A summary that sorts or uniques its failures answers a
different question from the one a reader asks after a red run, and the
reader cannot tell that it did. -/

def summarise (rows : List (String × Verdict)) : List String := Id.run do
  let mut passed := 0; let mut failed := 0; let mut refUB := 0
  let mut refLibc := 0; let mut unsup := 0; let mut tmo := 0
  let mut notParsed := 0; let mut notFetched := 0
  let mut firstFail : Option (String × Verdict) := none
  for (n, v) in rows do
    match v with
    | .passed => passed := passed + 1
    | .failed =>
        failed := failed + 1
        if firstFail.isNone then firstFail := some (n, v)
    | .refusedUB _ => refUB := refUB + 1
    | .refusedLibc _ => refLibc := refLibc + 1
    | .unsupported _ => unsup := unsup + 1
    | .timeout => tmo := tmo + 1
    | .notParsed _ => notParsed := notParsed + 1
    | .notFetched => notFetched := notFetched + 1
  let total := rows.length
  let scored := passed + failed
  let mut out : List String := []
  out := out ++ [s!"gcc.c-torture {scored}/{total} scored  (passed {passed}, failed {failed})"]
  out := out ++ [s!"  the zeroes, kept apart: refused-unsupported {unsup}, refused-libc {refLibc}, refused-ub {refUB}, timeout {tmo}, not-parsed {notParsed}, not-fetched {notFetched}"]
  match firstFail with
  | none => out := out ++ ["  first failure: none"]
  | some (n, v) =>
      out := out ++ [s!"  FIRST FAILURE (log order, verbatim): {n}  {v.token}  {v.detail}"]
  pure out

def main (args : List String) : IO UInt32 := do
  let (manifestPath, fuel) :=
    match args with
    | [p] => (p, 64)
    | [p, f] => (p, f.toNat?.getD 64)
    | _ => ("", 64)
  if manifestPath.isEmpty then
    IO.eprintln "usage: c-torture-run <manifest.json> [fuel]"
    return 2
  let contents ← IO.FS.readFile ⟨manifestPath⟩
  let j ← IO.ofExcept (Lean.Json.parse contents)
  let tests := (j.getObjValAs? (Array Lean.Json) "tests").toOption.getD #[]
  let mut rows : List (String × Verdict) := []
  for tj in tests do
    let e := parseEntry tj
    let v ← runEntry fuel e
    IO.println s!"{e.name}\t{v.token}\t{v.detail}"
    rows := rows ++ [(e.name, v)]
  IO.println "----"
  for l in summarise rows do IO.println l
  return 0

end LeanModels.C.C23.Torture

/-- The `lean_exe` root. -/
def main (args : List String) : IO UInt32 := LeanModels.C.C23.Torture.main args
