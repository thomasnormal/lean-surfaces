// The arithmetic shift right of a signed operand inside `always_comb` (the procedural route reads it as the
// continuous-assign one does).
module asr_proc #(parameter integer W = 8) (
  input  logic signed [W-1:0] a,
  input  logic        [2:0]   s,
  output logic signed [W-1:0] y
);
  always_comb y = a >>> s;
endmodule
