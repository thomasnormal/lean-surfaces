// An explicitly typed output NET and internal NET, both undriven: their bits
// read z (IEEE 1800-2023 §6.6), while the semantic tier initializes every
// declaration to x. Refused: `PortSymbol:net-z`, `NetSymbol:net-z`.
module net_z_flat (
  input  logic [1:0] a,
  output wire logic [1:0] yn,
  output logic [1:0] y,
  output logic [1:0] t
);
  wire logic [1:0] w;
  assign y = a;
  assign t = w;
endmodule
