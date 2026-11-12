module invalid_continuous_assign_e(input logic [7:0] x, output logic [7:0] y);
  assign y = {x, missing} >> 1;
endmodule
