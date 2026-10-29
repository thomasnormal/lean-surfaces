// A net declaration assignment plus a second continuous driver of one bit
// (2026-10-28, round 3 CX repair). A net's initializer is a continuous
// driver of its own (§10.3.1), so `w[0]` is a resolved two-driver net
// (constant 1 and `a`; Icarus 12: y = 01, 0x, 0x, 01 for a = 1, 0, x, z);
// the model does not resolve drivers and would let the `assign` win. Loud
// (`ContinuousAssignSymbol:initialized-net`). Before the guard this shape
// was already loud for an unrelated reason (the symbolic extractor does
// not recover a `wire [1:0]` net's packed dimensions); the guard names
// the real one and covers any net type that becomes representable.
module vg_initn (
  input  logic a,
  output logic [1:0] y
);
  wire [1:0] w = 2'b01;
  assign w[0] = a;
  assign y = w;
endmodule
