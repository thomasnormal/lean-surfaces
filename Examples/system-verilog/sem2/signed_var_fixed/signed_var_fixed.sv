// Flat signed module variables reuse the signed PDecl storage path.
module signed_var_fixed (
  input logic signed [3:0] a,
  input logic signed [3:0] b,
  output logic signed [3:0] y,
  output logic signed lt
);
  logic signed [3:0] t;
  always_comb begin
    t = a;
    y = t;
    lt = t < b;
  end
endmodule
