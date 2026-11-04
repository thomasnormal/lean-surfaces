// A fixed-width packed package parameter remains a qualified ParamRef.
package package_param_packed_pkg;
  parameter logic [3:0] P = 4'b1010;
endpackage

module package_param_packed (
  input logic [3:0] a,
  output logic [3:0] y
);
  always_comb y = a ^ package_param_packed_pkg::P;
endmodule
