// Untyped package parameters are signed 32-bit elaboration constants.
package package_param_untyped_pkg;
  parameter W = 4;
  localparam L = W + 1;
endpackage

module package_param_untyped #(parameter N = 0) (
  input logic [3:0] a,
  output logic [3:0] y
);
  import package_param_untyped_pkg::*;
  always_comb y = a ^ W ^ L ^ N;
endmodule
