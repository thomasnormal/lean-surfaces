// A signed comparison of a signed signal with an unsized constant (the downstream clean-room repro `signed_decl.sv`):
// the unsized `0` is a 32-bit signed integer, so `x` is sign-extended to 32 bits (IEEE 1800-2023 §11.8.1, §11.4.4).
// The extractor marks that sign extension `ConversionExpression:width`, so the semantics lowers the site to a loud node.
module signed_decl (
    input logic signed [7:0] x,
    output logic y
);
    assign y = x >= 0;
endmodule
