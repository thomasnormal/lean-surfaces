// Indexed slices through packed-struct typedefs keep fixed member windows.
module typedef_member_indexed (
    input  logic [1:0] source,
    output logic [3:0] out
);
  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } T;
  T value;

  assign value.hi[0 +: 2] = source;
  assign out = value.hi;
endmodule
