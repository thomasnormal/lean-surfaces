// Refused construct: a signed packed localparam whose width conversion is used in arithmetic.
// Tool: load_design_sv2.
// Exact message: localparam 'DOUBLE_BIAS': unsupported node 'ConversionExpression:width' in a constant context
module signed_localparam_cast #(parameter integer E = 8) (
    input wire [E-1:0] e,
    output wire [11:0] q
);
    localparam integer BIAS = (1 << (E-1))-1;
    localparam signed [11:0] DOUBLE_BIAS = 2*BIAS;
    assign q = $signed({{(12-E){1'b0}},e}) - DOUBLE_BIAS;
endmodule
