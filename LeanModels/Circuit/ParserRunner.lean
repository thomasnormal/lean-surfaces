import LeanModels.Circuit.Spice

open LeanModels.Circuit

private def deviceLine (circuit : ElaboratedCircuit)
    (device : ElaboratedDevice) : String :=
  let name := circuit.deviceNames.getD device.id.index "?"
  match device with
  | .resistor _ positive negative resistance =>
      s!"device resistor {name} {positive.index} {negative.index} {resistance}"
  | .voltageSource _ positive negative voltage =>
      s!"device voltageSource {name} {positive.index} {negative.index} {voltage}"
  | .currentSource _ positive negative current =>
      s!"device currentSource {name} {positive.index} {negative.index} {current}"
  | .capacitor _ positive negative capacitance =>
      s!"device capacitor {name} {positive.index} {negative.index} {capacitance}"
  | .inductor _ positive negative inductance =>
      s!"device inductor {name} {positive.index} {negative.index} {inductance}"
  | .mosfet _ drain gate source bulk model =>
      s!"device mosfet {name} {drain.index} {gate.index} {source.index} \
        {bulk.index} {model.index}"

def main (arguments : List String) : IO UInt32 := do
  let path ← match arguments with
    | [path] => pure path
    | _ =>
        IO.eprintln "usage: ParserRunner <deck.cir>"
        return 2
  let contents ← IO.FS.readFile path
  match Spice.parseAndElaborate contents with
  | .error error =>
      IO.eprintln error
      return 1
  | .ok circuit =>
      IO.println s!"title {circuit.title}"
      for (name, index) in circuit.nodeNames.zipIdx do
        IO.println s!"node {index} {name}"
      for device in circuit.devices do
        IO.println (deviceLine circuit device)
      return 0
