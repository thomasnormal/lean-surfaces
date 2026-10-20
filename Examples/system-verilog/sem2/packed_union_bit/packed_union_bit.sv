// Constant bits of untagged packed-union members flatten to vector windows.
module packed_union_bit (
    input  logic       source,
    output logic [3:0] out
);
  union packed {
    logic [3:0] bytes;
    logic [3:0] alt;
  } value;

  assign value.bytes[0] = source;
  assign out = value.alt;
endmodule
