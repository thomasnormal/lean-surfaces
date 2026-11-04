// Packed-struct member leaves flatten into one sampled concatenation.
module packed_member_concat (
    input  logic [7:0] source,
    output logic [3:0] hi,
    output logic [3:0] lo
);
  struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } value;

  assign {value.hi, value.lo} = source;
  assign hi = value.hi;
  assign lo = value.lo;
endmodule
