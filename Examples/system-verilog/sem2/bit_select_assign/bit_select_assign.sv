// Constant bit-select continuous drivers reuse Design2's existing windows.
module bit_select_assign (
    input  logic [3:0] source,
    input  logic       flag,
    output logic [7:0] value
);
  assign value[1] = source[0];
  assign value[6] = flag;
endmodule
