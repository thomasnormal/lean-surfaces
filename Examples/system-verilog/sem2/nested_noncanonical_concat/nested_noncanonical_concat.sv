// Nested noncanonical member slices split one sampled concatenated RHS.
module nested_noncanonical_concat (
    input  logic [3:0] source,
    output logic [3:0] hi,
    output logic [3:0] lo
);
  struct packed {
    struct packed {
      logic [10:7] hi;
      logic [10:7] lo;
    } inner;
  } value;

  assign {value.inner.hi[10:9], value.inner.lo[10:9]} = source;
  assign hi = value.inner.hi;
  assign lo = value.inner.lo;
endmodule
