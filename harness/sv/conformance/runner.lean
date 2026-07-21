/-
# SV self-check conformance runner

Executed as

  lake env lean --run harness/sv/conformance/runner.lean <envelope.sv.json> [--fuel N]

Loads a self-check-tier envelope (`docs/sv-envelope-schema.md` + the §f
vocabulary of `docs/sv-corpus-coverage.md`), runs every `initial` process
once at time 0 via `LeanModels.Sv.SelfCheck.runSelfCheck`, and prints the
collected `$display` lines to stdout — nothing else. Failures (load error,
`.timeout`, `.unsupported`) print `ERROR: ...` on stderr and exit nonzero.
The conformance tests are self-checking: a passing run prints `PASS`.

Batch mode (corpus-scale measurement — one Lean process instead of
thousands):

  lake env lean --run harness/sv/conformance/runner.lean --batch <list.txt> [--fuel N]

where `list.txt` has one envelope path per line. Per envelope it prints

  === BEGIN <path>
  <the $display lines>
  === END <path> status=<ok|error|timeout|unsupported> [detail]

and always exits 0 (per-file status is in the END lines).

Default fuel: 1000000 (fuel is a shared depth/step bound — see
`Semantics.lean`'s fuel discipline; conformance bodies are hundreds of
statements deep at most).
-/

import LeanModels.Sv.SelfCheck

open LeanModels.Sv
open LeanModels.Sv.SelfCheck

def defaultFuel : Nat := 1000000

/-- Run one envelope file; returns (status word, detail, output lines). -/
def runOne (path : String) (fuel : Nat) : IO (String × String × List String) := do
  let text ← try IO.FS.readFile path
    catch e => return ("error", s!"cannot read: {e}", [])
  match loadEnvelopeDesign text with
  | .error e => return ("error", e, [])
  | .ok d =>
      match runSelfCheck d fuel with
      | .ok lines => return ("ok", "", lines)
      | .timeout => return ("timeout", "fuel exhausted", [])
      | .unsupported msg => return ("unsupported", msg, [])

def parseFuel : List String → Option Nat
  | [] => some defaultFuel
  | ["--fuel", n] => n.toNat?
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | "--batch" :: listPath :: rest =>
    let some fuel := parseFuel rest
      | IO.eprintln "usage: runner.lean --batch <list.txt> [--fuel N]"; return 2
    let listing ← IO.FS.readFile listPath
    for path in listing.splitOn "\n" do
      let path := path.trim
      if path.isEmpty then continue
      IO.println s!"=== BEGIN {path}"
      let (status, detail, lines) ← runOne path fuel
      for l in lines do
        IO.println l
      let tail := if detail.isEmpty then "" else s!" {detail.replace "\n" " "}"
      IO.println s!"=== END {path} status={status}{tail}"
    return 0
  | envPath :: rest =>
    let some fuel := parseFuel rest
      | IO.eprintln "usage: runner.lean <envelope.sv.json> [--fuel N]"; return 2
    let (status, detail, lines) ← runOne envPath fuel
    for l in lines do
      IO.println l
    if status == "ok" then
      return 0
    else
      IO.eprintln s!"ERROR: {status}: {detail}"
      return 1
  | _ =>
    IO.eprintln "usage: runner.lean <envelope.sv.json> [--fuel N] | --batch <list.txt> [--fuel N]"
    return 2
