// Noncanonical member bits through typedefs keep declaration offsets.
module noncanonical_typedef_bit (
    input  logic       source,
    output logic [3:0] out
);
  typedef struct packed {
    logic [10:7] hi;
    logic [3:0]  lo;
  } T;
  T value;

  assign value.hi[10] = source;
  assign out = value.hi;
endmodule
