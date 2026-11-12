module mem_twostate_start_e(input logic [7:0] d, output logic [7:0] q);
  bit [7:0] s [0:1];
  assign q = s[0];
endmodule
