// A signed comparison inside `always_comb`: the procedural route does not read signed comparisons yet.
module sg_cmp_proc #(parameter integer W = 8) (
  input  logic signed [W-1:0] a, b,
  output logic lt
);
  always_comb lt = a < b;
endmodule
