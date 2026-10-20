// Constant subranges of packed members flatten to outer vector windows.
module packed_member_subrange (
    input  logic [1:0] source,
    output logic [3:0] out
);
  struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } value;

  assign value.hi[1:0] = source;
  assign out = value.hi;
endmodule
