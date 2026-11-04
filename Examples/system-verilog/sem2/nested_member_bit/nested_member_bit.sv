// Bits in nested packed structs use accumulated member offsets.
module nested_member_bit (
    input  logic       source,
    output logic [3:0] out
);
  struct packed {
    struct packed {
      logic [3:0] hi;
      logic [3:0] lo;
    } inner;
  } value;

  assign value.inner.hi[0] = source;
  assign out = value.inner.hi;
endmodule
