// Untagged packed-struct fields reuse the existing vector windows.
module packed_member_assign (
    input  logic [3:0] source,
    output logic [7:0] out,
    output logic [3:0] low
);
  struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } value;

  assign value.lo = source;
  assign value.hi = 4'ha;
  assign out = value;
  assign low = value.lo;
endmodule
