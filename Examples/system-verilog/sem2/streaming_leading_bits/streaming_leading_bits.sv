// Both symbolic assignment paths consume the leading eight source bits.
module streaming_leading_bits (
    input logic [11:0] source,
    output logic [3:0] hi, lo,
    output logic [3:0] procedural_hi, procedural_lo
);
  struct packed { logic [3:0] hi; logic [3:0] lo; } packet;
  assign {>> {packet}} = source;
  assign hi = packet.hi;
  assign lo = packet.lo;
  always_comb {>> {procedural_hi, procedural_lo}} = source;
endmodule
