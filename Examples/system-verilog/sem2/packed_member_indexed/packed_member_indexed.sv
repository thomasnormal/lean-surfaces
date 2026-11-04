// Literal indexed slices of packed members flatten to outer windows.
module packed_member_indexed (
    input  logic [1:0] low,
    input  logic [1:0] high,
    output logic [3:0] out
);
  struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } value;

  assign value.hi[0 +: 2] = low;
  assign value.hi[3 -: 2] = high;
  assign out = value.hi;
endmodule
