// Nested member slices can receive one sampled concatenated RHS.
module nested_member_concat (
    input  logic [3:0] source,
    output logic [3:0] hi,
    output logic [3:0] lo
);
  struct packed {
    struct packed {
      logic [3:0] hi;
      logic [3:0] lo;
    } inner;
  } value;

  assign {value.inner.hi[1:0], value.inner.lo[1:0]} = source;
  assign hi = value.inner.hi;
  assign lo = value.inner.lo;
endmodule
