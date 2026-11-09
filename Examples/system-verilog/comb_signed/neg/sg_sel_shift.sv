// A part select of a signed signal as the operand of a shift.
module sg_sel_shift #(parameter integer W = 8) (
  input  logic signed [W-1:0] a,
  input  logic        [2:0]   s,
  output logic        [W-2:0] y
);
  assign y = a[W-1:1] >> s;
endmodule
