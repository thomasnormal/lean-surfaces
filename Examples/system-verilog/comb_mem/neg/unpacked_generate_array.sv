// A parameter-dependent unpacked array, written and read at constant indices (the clean-room repro, verbatim below).
module unpacked_generate_array #(parameter integer W = 8, S = 2) (
    input logic [W-1:0] x,
    output logic [W-1:0] y
);
    logic [W-1:0] stage [0:S-1];
    assign stage[0] = x;
    assign stage[1] = stage[0];
    assign y = stage[1];
endmodule
