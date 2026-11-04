// SCALAR implicitly typed nets (no packed dimensions to make them
// unrecoverable): an undriven `output wire` and an undriven internal `wire`
// read z. Refused: `PortSymbol:net-z`, `NetSymbol:net-z`. The input net `b`
// stays admitted (the instantiating scope drives it).
module net_z_scalar (
  input  logic a,
  input  wire  b,
  output wire  yo,
  output logic u,
  output logic v
);
  wire w;
  assign u = w;
  assign v = a & b;
endmodule
