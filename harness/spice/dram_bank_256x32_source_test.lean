import LeanModels.Spice.DramBank256x32

open LeanModels.Circuit.Spice LeanModels.Spice

def sourcePath : System.FilePath :=
  "Examples/spice/dram_bank_256x32/dram_bank_256x32.cir"

def withAliasedRowWordline (source : SourceCircuit) : SourceCircuit :=
  let bank := source.subcircuits[6]!
  let subarray := bank.instances[10]!
  let subarray :=
    { subarray with connections :=
        subarray.connections.set! 13 "word0" }
  let bank := { bank with instances := bank.instances.set! 10 subarray }
  { source with subcircuits := source.subcircuits.set! 6 bank }

def withWrongBitlineCapacitance (source : SourceCircuit) : SourceCircuit :=
  let column := source.subcircuits[5]!
  let capacitor := column.devices[0]!
  let capacitor := { capacitor with value := 0 }
  let column := { column with devices := column.devices.set! 0 capacitor }
  { source with subcircuits := source.subcircuits.set! 5 column }

def withAliasedColumnSelect (source : SourceCircuit) : SourceCircuit :=
  let bank := source.subcircuits[6]!
  let column := bank.instances[dramBankSubarrayCount 256 + 17]!
  let column :=
    { column with connections :=
        column.connections.set! 1 "select0" }
  let bank :=
    { bank with instances :=
        bank.instances.set! (dramBankSubarrayCount 256 + 17) column }
  { source with subcircuits := source.subcircuits.set! 6 bank }

def withAliasedSenseNodes (source : SourceCircuit) : SourceCircuit :=
  let sense := source.subcircuits[0]!
  let complementPmos := sense.mosfets[2]!
  let complementPmos := { complementPmos with drain := "q" }
  let sense :=
    { sense with mosfets := sense.mosfets.set! 2 complementPmos }
  { source with subcircuits := source.subcircuits.set! 0 sense }

def withMissingReferenceCoupling (source : SourceCircuit) : SourceCircuit :=
  let column := source.subcircuits[5]!
  let coupling := column.instances[4]!
  let coupling :=
    { coupling with connections := coupling.connections.set! 0 "bit" }
  let column :=
    { column with instances := column.instances.set! 4 coupling }
  { source with subcircuits := source.subcircuits.set! 5 column }

def withZeroSenseCapacitance (source : SourceCircuit) : SourceCircuit :=
  let sense := source.subcircuits[0]!
  let capacitor := sense.devices[0]!
  let capacitor := { capacitor with value := 0 }
  let sense := { sense with devices := sense.devices.set! 0 capacitor }
  { source with subcircuits := source.subcircuits.set! 0 sense }

def withWrongThreshold (source : SourceCircuit) : SourceCircuit :=
  let model := source.models[0]!
  let model := { model with threshold := 2 }
  { source with models := source.models.set! 0 model }

def withUnsupportedLambda (source : SourceCircuit) : SourceCircuit :=
  let model := source.models[0]!
  let model := { model with channelLengthModulation := 1 / 100 }
  { source with models := source.models.set! 0 model }

def main : IO UInt32 := do
  let text ← IO.FS.readFile sourcePath
  let source ←
    match parse text with
    | .ok source => pure source
    | .error error =>
        IO.eprintln error.describe
        return 1
  let projectedThreshold :=
    match (withWrongThreshold source).toDramBank 256 32 with
    | .ok bank => bank.parameters.accessThreshold
    | .error _ => 0
  let checks := #[
    ("original source accepted", dramBank256x32SourceMatches source),
    ("aliased row wordline rejected",
      !dramBank256x32SourceMatches (withAliasedRowWordline source)),
    ("wrong bitline capacitance rejected",
      !dramBank256x32SourceMatches (withWrongBitlineCapacitance source)),
    ("aliased column select rejected",
      !dramBank256x32SourceMatches (withAliasedColumnSelect source)),
    ("aliased differential latch nodes rejected",
      !dramBank256x32SourceMatches (withAliasedSenseNodes source)),
    ("missing complement coupling rejected",
      !dramBank256x32SourceMatches (withMissingReferenceCoupling source)),
    ("zero latch capacitance rejected",
      !dramBank256x32SourceMatches (withZeroSenseCapacitance source)),
    ("supported MOS threshold remains accepted",
      dramBank256x32SourceMatches (withWrongThreshold source)),
    ("changed MOS threshold reaches projected profile",
      projectedThreshold == 2),
    ("unsupported channel-length modulation rejected",
      !dramBank256x32SourceMatches (withUnsupportedLambda source))]
  let mut failed := false
  for (name, passed) in checks do
    IO.println s!"{name}: {if passed then "PASS" else "FAIL"}"
    if !passed then
      failed := true
  return if failed then 1 else 0
