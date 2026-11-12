module array_select_e(input logic [1:0] i, output logic [7:0] y);
  assign y = missing[i];
endmodule
