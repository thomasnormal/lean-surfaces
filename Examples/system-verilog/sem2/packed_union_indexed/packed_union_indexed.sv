// Literal indexed slices of packed-union members flatten to shared windows.
module packed_union_indexed (
    input  logic [1:0] low,
    input  logic [1:0] high,
    output logic [3:0] out
);
  union packed {
    logic [3:0] bytes;
    logic [3:0] alt;
  } value;

  assign value.bytes[0 +: 2] = low;
  assign value.bytes[3 -: 2] = high;
  assign out = value.alt;
endmodule
