import LeanModels.Spice.DramDifferentialSense
import LeanModels.Circuit.Spice

open LeanModels.Circuit LeanModels.Circuit.Spice LeanModels.Spice

def sourcePath : System.FilePath :=
  "Examples/spice/dram_sense_amp/dram_sense_amp.cir"

def withSelfCoupledTrueGate (source : SourceCircuit) : SourceCircuit :=
  let sense := source.subcircuits[0]!
  let device := sense.mosfets[0]!
  let device := { device with gate := "q" }
  let sense := { sense with mosfets := sense.mosfets.set! 0 device }
  { source with subcircuits := source.subcircuits.set! 0 sense }

def withMissingComplementCapacitor
    (source : SourceCircuit) : SourceCircuit :=
  let sense := source.subcircuits[0]!
  let sense := { sense with devices := sense.devices.pop }
  { source with subcircuits := source.subcircuits.set! 0 sense }

def withDifferentTrueCapacitance
    (source : SourceCircuit) : SourceCircuit :=
  let sense := source.subcircuits[0]!
  let capacitor := sense.devices[0]!
  let capacitor := { capacitor with value := 1 / 1000000000000 }
  let sense := { sense with devices := sense.devices.set! 0 capacitor }
  { source with subcircuits := source.subcircuits.set! 0 sense }

def withUnsupportedLambda (source : SourceCircuit) : SourceCircuit :=
  let model := source.models[0]!
  let model := { model with channelLengthModulation := 1 / 100 }
  { source with models := source.models.set! 0 model }

def project (source : SourceCircuit) :
    Except String DramDifferentialSenseLayout := do
  let circuit ← match elaborate source with
    | .ok circuit => pure circuit
    | .error error => throw error.describe
  circuit.toDramDifferentialSense

def main : IO UInt32 := do
  let text ← IO.FS.readFile sourcePath
  let source ←
    match parse text with
    | .ok source => pure source
    | .error error =>
        IO.eprintln error.describe
        return 1
  let projectedCapacitance :=
    match project (withDifferentTrueCapacitance source) with
    | .ok layout => layout.trueCapacitance
    | .error _ => 0
  let checks := #[
    ("original source accepted", (project source).isOk),
    ("self-coupled gate rejected",
      !(project (withSelfCoupledTrueGate source)).isOk),
    ("missing complement capacitor rejected",
      !(project (withMissingComplementCapacitor source)).isOk),
    ("changed capacitance remains accepted",
      (project (withDifferentTrueCapacitance source)).isOk),
    ("changed capacitance reaches typed layout",
      projectedCapacitance == 1 / 1000000000000),
    ("unsupported channel-length modulation rejected",
      !(project (withUnsupportedLambda source)).isOk)]
  let mut failed := false
  for (name, passed) in checks do
    IO.println s!"{name}: {if passed then "PASS" else "FAIL"}"
    if !passed then
      failed := true
  return if failed then 1 else 0
