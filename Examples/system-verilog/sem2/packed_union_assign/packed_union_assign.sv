// An untagged packed union aliases fields in one existing vector store.
module packed_union_assign (
    input  logic [7:0] source,
    output logic [7:0] out,
    output logic [7:0] alt
);
  union packed {
    logic [7:0] bytes;
    logic [7:0] alt;
  } value;

  assign value.bytes = source;
  assign out = value;
  assign alt = value.alt;
endmodule
