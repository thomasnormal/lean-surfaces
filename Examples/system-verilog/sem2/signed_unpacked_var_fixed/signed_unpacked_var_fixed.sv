// Signed fixed-unpacked cells retain signed operator semantics.
module signed_unpacked_var_fixed (
  input logic signed [3:0] a,
  output logic signed [3:0] y0,
  output logic signed [3:0] y1
);
  logic signed [3:0] arr [0:1];
  assign arr[0] = a;
  assign arr[1] = -a;
  assign y0 = arr[0] + 4'sd1;
  assign y1 = arr[1] + 4'sd1;
endmodule
