// Noncanonical final member bits use recursive and local offsets.
module nested_noncanonical_bit (
    input  logic       source,
    output logic [3:0] out
);
  struct packed {
    struct packed {
      logic [10:7] hi;
      logic [3:0]  lo;
    } inner;
  } value;

  assign value.inner.hi[10] = source;
  assign out = value.inner.hi;
endmodule
