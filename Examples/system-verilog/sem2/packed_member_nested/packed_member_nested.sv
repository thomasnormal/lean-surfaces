// Nested untagged packed members flatten to outer vector windows.
module packed_member_nested (
    input  logic [3:0] source,
    output logic [7:0] out
);
  struct packed {
    struct packed {
      logic [3:0] hi;
      logic [3:0] lo;
    } inner;
  } value;

  assign value.inner.lo = source;
  assign value.inner.hi = 4'ha;
  assign out = value;
endmodule
