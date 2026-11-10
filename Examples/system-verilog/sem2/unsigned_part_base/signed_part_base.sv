// Signed dynamic bases remain outside the admitted select tier.
module signed_part_base (
  input logic [7:0] v,
  input logic signed [31:0] si,
  output logic [3:0] y
);
  assign y = v[si +: 4];
endmodule
