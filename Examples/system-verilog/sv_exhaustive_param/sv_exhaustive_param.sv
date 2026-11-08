// A parametric combinational design (one `integer` parameter, the width W): every output bit is the input bit
// inverted, through an XOR with an all-ones mask of width W. `premise.lean` builds over it, at a parameter point
// and at every point, the no-qualified-`case` premise that `sv_exhaustive` passes to its lowering theorem.
module sv_exhaustive_param #(parameter integer W = 2) (
    input logic [W-1:0] a,
    output logic [W-1:0] y
);
    assign y = a ^ {W{1'b1}};
endmodule
