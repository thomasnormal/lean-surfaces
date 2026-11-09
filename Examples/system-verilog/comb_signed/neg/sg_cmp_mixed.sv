// A signed comparison of two signed signals of different widths: the narrower is sign-extended (IEEE 1800-2023
// §11.8.2), which the extractor marks `ConversionExpression:width`.
module sg_cmp_mixed (
    input logic signed [7:0] x,
    input logic signed [15:0] w,
    output logic y
);
    assign y = x < w;
endmodule
