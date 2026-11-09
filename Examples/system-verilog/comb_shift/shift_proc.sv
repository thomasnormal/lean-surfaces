// The same shift of an operation inside `always_comb`, which the procedural route reads too.
module shift_proc #(parameter int W = 8) (
    input  logic [W-1:0] a,
    input  logic [W-1:0] b,
    output logic [W-1:0] y
);
    always_comb begin
        y = (a - b) << 1;
    end
endmodule
