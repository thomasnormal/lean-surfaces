// Refused construct: an unbased unsized literal used as a packed parameter default.
// Tool: load_design_sv2.
// Exact message: defaults: parameter 'TAPS' default: unbased-unsized literal in a constant context (no context width)
module unsized_param_literal #(parameter integer W = 8,
    parameter logic [W-1:0] MASK = '0) (
    input wire [W-1:0] x,
    output wire [W-1:0] y
);
    assign y = x ^ MASK;
endmodule
