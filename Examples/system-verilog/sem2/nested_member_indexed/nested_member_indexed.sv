// Indexed slices in nested packed structs use accumulated offsets.
module nested_member_indexed (
    input  logic [1:0] source,
    output logic [3:0] out
);
  struct packed {
    struct packed {
      logic [3:0] hi;
      logic [3:0] lo;
    } inner;
  } value;

  assign value.inner.hi[0 +: 2] = source;
  assign out = value.inner.hi;
endmodule
