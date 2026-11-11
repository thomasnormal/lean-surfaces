// A FIXED-size unpacked array written and read at constant indices: the clean-room repro `unpacked_generate_array.sv` with
// its cell count a literal (`[0:1]`, not `[0:S-1]`). The extractor declares one signal per cell (`stage[0]`, `stage[1]`).
module fixed_cells #(parameter integer W = 8) (
    input logic [W-1:0] x,
    output logic [W-1:0] y
);
    logic [W-1:0] stage [0:1];
    assign stage[0] = x;
    assign stage[1] = stage[0];
    assign y = stage[1];
endmodule
