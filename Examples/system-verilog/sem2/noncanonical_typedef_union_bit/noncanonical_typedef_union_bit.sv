// Noncanonical union bits through typedefs keep shared vector aliases.
module noncanonical_typedef_union_bit (
    input  logic       source,
    output logic [3:0] out
);
  typedef union packed {
    logic [10:7] bytes;
    logic [3:0]  alt;
  } U;
  U value;

  assign value.bytes[10] = source;
  assign out = value.alt;
endmodule
