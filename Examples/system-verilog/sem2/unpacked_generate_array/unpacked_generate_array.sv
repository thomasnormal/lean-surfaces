// Refused construct: a parameter-dependent unpacked array declaration.
// Tool: load_design_sv2.
// Exact message: VariableSymbol:default-point-array
module unpacked_generate_array #(parameter integer W = 8, S = 2) (
    input logic [W-1:0] x,
    output logic [W-1:0] y
);
    logic [W-1:0] stage [0:S-1];
    assign stage[0] = x;
    assign stage[1] = stage[0];
    assign y = stage[1];
endmodule
