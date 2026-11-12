// Source-shaped initial elaboration checks and a packed enum from a package.
package initial_enum_checks_pkg;
  typedef enum logic [1:0] { IDLE = 2'd0, RUN = 2'd1 } mode_t;
endpackage

module initial_enum_checks_e (
  input logic [1:0] a,
  output logic y
);
  initial begin
    if (initial_enum_checks_pkg::RUN != 2'd1)
      $fatal(1, "RUN enum value changed");
    if (initial_enum_checks_pkg::IDLE != 2'd0)
      $error("IDLE enum value changed");
  end
  assign y = (a == initial_enum_checks_pkg::RUN);
endmodule
