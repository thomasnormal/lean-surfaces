module shift_param #(parameter int W = 8)(input logic [W-1:0] xv, output logic [W-1:0] ws0);
  localparam int XS = 1;
  assign ws0 = xv >> XS;
endmodule
