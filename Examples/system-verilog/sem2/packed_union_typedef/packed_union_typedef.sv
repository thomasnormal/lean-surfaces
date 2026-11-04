// An untagged packed-union typedef is compile-time metadata for vector storage.
module packed_union_typedef (
    input  logic [7:0] source,
    output logic [7:0] out
);
  typedef union packed {
    logic [7:0] bytes;
    logic [7:0] alt;
  } union_t;
  union_t value;

  assign value.bytes = source;
  assign out = value;
endmodule
