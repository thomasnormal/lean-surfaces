// A bit select of a signed signal inside `always_comb`.
module sg_sel_proc #(parameter integer W = 8) (
  input  logic signed [W-1:0] a,
  output logic                y
);
  always_comb y = a[W-1];
endmodule
