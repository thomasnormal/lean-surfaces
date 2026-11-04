// Constant bits of packed members flatten to outer vector windows.
module packed_member_bit (
    input  logic       source,
    output logic [3:0] out
);
  struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } value;

  assign value.hi[0] = source;
  assign out = value.hi;
endmodule
