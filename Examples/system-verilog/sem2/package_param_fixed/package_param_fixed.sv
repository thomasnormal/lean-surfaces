// A scalar package parameter remains a qualified ParamRef in the symbolic
// envelope and supplies a packed range at every module parameter point.
package package_param_fixed_pkg;
  parameter int W = 4;
endpackage

module package_param_fixed #(parameter N = 2) (
  input logic [package_param_fixed_pkg::W+N-1:0] a,
  output logic [package_param_fixed_pkg::W-1:0] y
);
  always_comb y = a[package_param_fixed_pkg::W-1:0];
endmodule
