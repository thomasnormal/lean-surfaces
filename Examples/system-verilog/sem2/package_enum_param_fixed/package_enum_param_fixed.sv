// A package enum remains qualified in a parameter type/default and in the body.
package package_enum_param_fixed_pkg;
  typedef enum logic [1:0] { IDLE = 2'd0, RUN = 2'd1 } state_t;
endpackage

module package_enum_param_fixed #(
  parameter package_enum_param_fixed_pkg::state_t S = package_enum_param_fixed_pkg::RUN
) (
  input logic [1:0] a,
  output logic [1:0] y
);
  always_comb begin
    if (a == S) y = package_enum_param_fixed_pkg::RUN;
    else y = package_enum_param_fixed_pkg::IDLE;
  end
endmodule
