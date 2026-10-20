// Simple slices of noncanonical packed-union members use label offsets.
module noncanonical_union_subrange (
    input  logic [1:0] source,
    output logic [3:0] out
);
  union packed {
    logic [10:7] bytes;
    logic [3:0]  alt;
  } value;

  assign value.bytes[10:9] = source;
  assign out = value.alt;
endmodule
