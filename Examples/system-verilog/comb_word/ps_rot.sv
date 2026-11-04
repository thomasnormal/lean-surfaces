// WP-B2 gate 4a: literal-bound part selects (the legacy `PartSel`): read in the parts of a concatenation, written as targets, and as a plain field.
module ps_rot (
  input  logic [15:0] x,
  output logic [15:0] r,
  output logic [15:0] sw,
  output logic [4:0]  e
);
  assign r = {x[8:0], x[15:9]};   // rotate left by 7
  assign sw[7:0]  = x[15:8];      // byte swap: part-select targets
  assign sw[15:8] = x[7:0];
  assign e = x[14:10];            // a field
endmodule
