// A concatenated continuous-assignment target that leaves bits of a
// variable undriven: nothing drives y[1:0]. An explicitly typed
// `output logic` is a variable (IEEE 1800-2023 23.2.2.3), its bits are
// independent (6.5) and a four-state variable starts at x (6.8, Table 6-7),
// so y[1:0] reads x. Icarus 12.0 lowers the partially continuously assigned
// variable to a net and reads z there: declared disagreement
// `iverilog-concat-target-undriven-init` (docs/sv-oracle-disagreements.md,
// "Partial variable initialization").
module concat_undriven (
  input  logic [2:0] x,
  output logic [3:0] y,
  output logic       z
);
  assign {y[3:2], z} = x;
endmodule
