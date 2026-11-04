// A signed wire with one whole-net driver has variable-equivalent storage.
module signed_net_fixed (
  input logic signed [3:0] a,
  input logic signed [3:0] b,
  output logic signed [3:0] y,
  output logic signed lt
);
  wire signed [3:0] w;
  assign w = a;
  always_comb begin
    y = w;
    lt = w < b;
  end
endmodule
