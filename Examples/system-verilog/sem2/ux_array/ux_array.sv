// Unsized x/z literals as UNPACKED-ARRAY assignment-pattern elements
// (round 5 Lane A, 2026-10-29; INIT2 verifier repro `ap`). Neither Icarus
// 12.0 ("sorry: Assignment to an entire array ... not yet supported") nor
// Yosys 0.53 (syntax error) runs the declaration, so no value can be
// checked. At 2e8c8b28 each element was a zero-extending `Resize` that
// `instDecl` refused ("non-literal initializer"); the round-4 expression
// rule padded them into admitted literals. Loud again
// (`Initializer:unsized-xz-element`).
module ux_array (
  input  logic        clk,
  input  logic        a,
  output logic [39:0] y0,
  output logic [39:0] y1
);
  logic [39:0] m [0:1] = '{'hx0, 'hz1};
  assign y0 = m[0];
  assign y1 = m[1];
endmodule
