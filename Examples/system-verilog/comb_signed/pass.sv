// A signed input copied to an unsigned output of the same width.
module pass #(parameter integer W = 8) (
  input  logic signed [W-1:0] x,
  output logic        [W-1:0] y
);
  assign y = x;
endmodule
