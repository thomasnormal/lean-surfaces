// A parameter-dependent packed bit vector squashes X/Z at the port boundary.
module bit_param_fixed #(parameter N = 4) (
  input  bit [N-1:0] a,
  output logic [7:0] y
);
  always_comb y = a;
endmodule
