module pow_wall #(parameter int W=8193) (output logic [7:0] y);
  localparam int K = 2**W;
  assign y = K[7:0];
endmodule
