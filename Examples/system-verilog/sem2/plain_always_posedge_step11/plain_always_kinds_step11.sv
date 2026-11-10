// Clean-room source: retain both edge process styles and sample old state.
module plain_always_kinds_step11 (
    input logic clk,
    input logic [1:0] sel,
    input logic [3:0] d,
    output logic [3:0] q,
    output logic [3:0] q_old,
    output logic [3:0] q_case
);
    always @(posedge clk) begin
        q <= d;
        q <= ~d;
        case (sel)
            2'b00: q_case <= d;
            2'b1x: q_case <= 4'hA;
            default: q_case <= 4'h5;
        endcase
    end

    always_ff @(posedge clk) begin
        q_old <= q;
    end
endmodule
