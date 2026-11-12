module typed_array_e(input logic [7:0] x, output logic [7:0] y);
  wire [7:0] values [0:3];
  assign y = values[0] ^ x;
endmodule
