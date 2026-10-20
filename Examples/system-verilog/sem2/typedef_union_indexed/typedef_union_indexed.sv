// Indexed slices through packed-union typedefs keep shared vector aliases.
module typedef_union_indexed (
    input  logic [1:0] source,
    output logic [3:0] out
);
  typedef union packed {
    logic [3:0] bytes;
    logic [3:0] alt;
  } U;
  U value;

  assign value.bytes[0 +: 2] = source;
  assign out = value.alt;
endmodule
