// Nested member concatenations through typedefs keep fixed windows.
module typedef_nested_concat (
    input  logic [3:0] source,
    output logic [3:0] hi,
    output logic [3:0] lo
);
  typedef struct packed {
    struct packed {
      logic [3:0] hi;
      logic [3:0] lo;
    } inner;
  } T;
  T value;

  assign {value.inner.hi[1:0], value.inner.lo[1:0]} = source;
  assign hi = value.inner.hi;
  assign lo = value.inner.lo;
endmodule
