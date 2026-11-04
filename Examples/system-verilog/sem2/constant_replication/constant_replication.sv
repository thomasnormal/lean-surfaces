// Refused construct: a replication expression used in a parameterized constant expression.
// Tool: load_design_sv2 (gates 1 blocks).
// Exact message: localparam 'SIGN': replication in a constant context
module constant_replication #(parameter integer E = 8) (
    input wire [E-1:0] x,
    output wire [E-1:0] y
);
    localparam integer SIGN = {{E{1'b0}}};
    assign y = x ^ SIGN;
endmodule
