/-
# Timed SystemVerilog conformance runner

This runner is the scheduler-facing companion to `runner.lean`. It loads the
same self-check envelope, elaborates it with `elabTimedDesign`, and drives a
bounded sequence of time slots through the Active/Inactive/NBA loop. A slot
at time zero is followed by one-unit advances; the bound is an observation
budget, not a semantic shortcut. `$finish` preserves the collected output in
the `SvM` world and stops the drive early.
-/

import LeanModels.Sv.Load

open LeanModels.Sv
open LeanModels.Sv.SelfCheck

def defaultFuel : Nat := 1000000
def defaultTicks : Nat := 16

partial def drive (fuel ticks : Nat) (first : Bool) (world : SvWorld) :
    Except String SvWorld :=
  if world.out.halted || ticks == 0 then
    .ok world
  else
    let action : SvM Unit :=
      if first then
        slotStep ρ_src fuel
      else
        do
          advanceTime 1
          wakeTimers
          slotStep ρ_src fuel
    match SvM.exec action world with
    | .error loud => .error s!"scheduler halted: {repr loud}"
    | .ok (_, next) => drive fuel (ticks - 1) false next

def runTimedOne (path : String) (fuel ticks : Nat) :
    IO (String × String × List String) := do
  let text ← try IO.FS.readFile path
    catch e => return ("error", s!"cannot read: {e}", [])
  match loadEnvelopeDesign text with
  | .error e => return ("error", e, [])
  | .ok design =>
      match elabTimedDesign fuel design with
      | .error e => return ("unsupported", e, [])
      | .ok world =>
          match drive fuel ticks true world with
          -- A scheduler refusal is a loud, classified boundary.  Preserve
          -- it as `unsupported` so differential rows can record the exact
          -- missing region/event rule; `error` remains reserved for load or
          -- runner failures before a world exists.
          | .error e => return ("unsupported", e, [])
          | .ok final => return ("ok", "", final.out.flush)

def parseNatArg : String → Option Nat := fun s => s.toNat?

def parseArgs : List String → Option (String × Nat × Nat)
  | [path] => some (path, defaultFuel, defaultTicks)
  | [path, "--fuel", fuel] => do
      let f ← parseNatArg fuel
      return (path, f, defaultTicks)
  | [path, "--fuel", fuel, "--ticks", ticks] => do
      let f ← parseNatArg fuel
      let t ← parseNatArg ticks
      return (path, f, t)
  | _ => none

def parseBatchArgs : List String → Option (String × Nat × Nat)
  | ["--batch", listing] => some (listing, defaultFuel, defaultTicks)
  | ["--batch", listing, "--fuel", fuel] => do
      let f ← parseNatArg fuel
      return (listing, f, defaultTicks)
  | ["--batch", listing, "--fuel", fuel, "--ticks", ticks] => do
      let f ← parseNatArg fuel
      let t ← parseNatArg ticks
      return (listing, f, t)
  | _ => none

def main (args : List String) : IO UInt32 := do
  match parseBatchArgs args with
  | some (listingPath, fuel, ticks) =>
      let listing ← IO.FS.readFile listingPath
      for path in listing.splitOn "\n" do
        let path := path.trimAscii.toString
        if path.isEmpty then continue
        IO.println s!"=== BEGIN {path}"
        let (status, detail, lines) ← runTimedOne path fuel ticks
        for line in lines do IO.println line
        let tail := if detail.isEmpty then "" else s!" {detail.replace "\n" " "}"
        IO.println s!"=== END {path} status={status}{tail}"
      return 0
  | none =>
      match parseArgs args with
      | none =>
          IO.eprintln "usage: timed_runner.lean <envelope> [--fuel N] [--ticks N] | --batch <list> [--fuel N] [--ticks N]"
          return 2
      | some (path, fuel, ticks) =>
          let (status, detail, lines) ← runTimedOne path fuel ticks
          for line in lines do IO.println line
          if status == "ok" then
            return 0
          else
            IO.eprintln s!"ERROR: {status}: {detail}"
            return 1
