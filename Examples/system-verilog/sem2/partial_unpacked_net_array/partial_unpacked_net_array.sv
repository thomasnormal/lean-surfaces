// An undriven fixed wire-array cell remains high impedance.
module partial_unpacked_net_array (
  input logic [3:0] a,
  output logic [3:0] y
);
  wire [3:0] cells [0:1];
  assign cells[0] = a;
  assign y = cells[1];
endmodule
