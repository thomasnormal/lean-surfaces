// Selects of a signed signal: a bit or part select is unsigned whatever the signedness of the signal (IEEE 1800-2023
// §11.8.1). The sign bit, the low bits, a bit inside an operation, and the sign bit above a part select (an arithmetic
// shift right by one, written out).
module ssel #(parameter integer W = 8) (
  input  logic signed [W-1:0] a, b,
  output logic                msb,
  output logic        [W-2:0] low,
  output logic                x,
  output logic signed [W-1:0] h
);
  assign msb = a[W-1];
  assign low = a[W-2:0];
  assign x   = a[0] ^ b[W-1];
  assign h   = {a[W-1], a[W-1:1]};
endmodule
