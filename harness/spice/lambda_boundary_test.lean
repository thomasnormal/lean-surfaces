/-
The channel-length-modulation boundary, exercised rather than asserted.

WHAT THIS PINS.  The tier supports the `LAMBDA=0, IS=0` MOS1 profile and
refuses everything else.  That refusal is written in ELEVEN places: once in
`elaborate` (LeanModels/Circuit/Spice.lean, the SourceCircuit -> ElaboratedCircuit
step) and ten times in the per-device projections (`toLoadedInverterNominal`,
`toDiffPairNominal`, ...).

Only the first is REACHABLE.  Every per-device projection takes an
`ElaboratedCircuit`, whose models have already passed `elaborate`'s
`channelLengthModulation == 0` guard, so a lambda-bearing deck is rejected
before any of them runs.  This file proves that by construction: it mutates a
real deck's model and shows the ELABORATION error comes back, not the
projection's.

So the ten downstream checks are DEFENCE IN DEPTH, not outstanding work, and
counting them as a proof obligation -- as this lane's F4 row did, at "88
sites" -- prices a supported constant as a gap.  They stay: if the outer guard
were ever removed they would catch it, and this test would then report the
projection's message instead of elaboration's, loudly.
-/
import LeanModels.Spice.LoadedInverter
import LeanModels.Spice.DiffPair
import LeanModels.Spice.CommonSource
import LeanModels.Spice.Dram1T1C
import LeanModels.Circuit.Spice

open LeanModels.Circuit LeanModels.Circuit.Spice LeanModels.Spice

/-- Give the first MOS model a nonzero channel-length modulation. -/
def withLambda (source : SourceCircuit) : SourceCircuit :=
  let model := source.models[0]!
  let model := { model with channelLengthModulation := 1 / 100 }
  { source with models := source.models.set! 0 model }

/-- Give the first MOS model a nonzero junction saturation current. -/
def withSaturation (source : SourceCircuit) : SourceCircuit :=
  let model := source.models[0]!
  let model := { model with junctionSaturation := 1 / 1000000 }
  { source with models := source.models.set! 0 model }

structure Deck where
  name : String
  path : System.FilePath
  projects : ElaboratedCircuit → Bool

def decks : List Deck :=
  [ { name := "loaded_inverter"
      path := "Examples/spice/loaded_inverter/loaded_inverter.cir"
      projects := fun c => (c.toLoadedInverterNominal).isOk },
    { name := "diff_pair"
      path := "Examples/spice/diff_pair/diff_pair.cir"
      projects := fun c => (c.toDiffPairNominal).isOk },
    { name := "cs_amp"
      path := "Examples/spice/cs_amp/cs_amp.cir"
      projects := fun c => (c.toCommonSourceNominal).isOk },
    { name := "dram_1t1c"
      path := "Examples/spice/dram_1t1c/dram_1t1c.cir"
      projects := fun c => (c.toDram1T1CNominal).isOk } ]

def main : IO UInt32 := do
  let mut failed := false
  for deck in decks do
    let text ← IO.FS.readFile deck.path
    let source ← match parse text with
      | .ok s => pure s
      | .error e => IO.eprintln s!"{deck.name}: parse failed: {e.describe}"
                    return 1
    -- 1. the committed deck elaborates and projects
    let accepted :=
      match elaborate source with
      | .ok circuit => deck.projects circuit
      | .error _ => false
    -- 2. lambda /= 0 is refused, and refused AT ELABORATION
    let lambdaRefusedAtElaboration := !(elaborate (withLambda source)).isOk
    -- 3. the same for IS /= 0, the other half of the named profile
    let saturationRefusedAtElaboration :=
      !(elaborate (withSaturation source)).isOk
    for (label, passed) in
        [ (s!"{deck.name}: committed deck accepted", accepted),
          (s!"{deck.name}: lambda /= 0 refused at elaboration",
            lambdaRefusedAtElaboration),
          (s!"{deck.name}: IS /= 0 refused at elaboration",
            saturationRefusedAtElaboration) ] do
      IO.println s!"{label}: {if passed then "PASS" else "FAIL"}"
      if !passed then failed := true
  return if failed then 1 else 0
