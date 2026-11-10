// Refused construct: a packed enum type declared in a package and used as a port.
// Tool: load_design_sv2 (gates ~15 blocks).
// Exact message: defaults: enum 'mode_t': unrecoverable packed dimensions
package modes_pkg;
    typedef enum logic [1:0] {MODE_A, MODE_B} mode_t;
endpackage
module packed_enum_package(input modes_pkg::mode_t mode, output wire y);
    assign y = mode == modes_pkg::MODE_B;
endmodule
