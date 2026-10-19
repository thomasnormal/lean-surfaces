// Constant part-select continuous drivers reuse Design2's existing windows.
module selected_assign (
    input  logic [3:0] nibble,
    output logic [7:0] value
);
  assign value[3:0] = nibble;
  assign value[7:4] = 4'ha;
endmodule
