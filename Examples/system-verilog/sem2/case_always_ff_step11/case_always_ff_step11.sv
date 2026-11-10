// Clean-room Step 11 fixture: plain case inside one always_ff process.
// The x/z labels are deliberate: plain case uses case equality, so they match
// only the same four-state selector bits (IEEE 1800-2023 §12.5).
module case_always_ff_step11 (
    input  logic       clk,
    input  logic [1:0] sel,
    input  logic [3:0] d,
    output logic [3:0] q,
    output logic [3:0] q_default
);
    always_ff @(posedge clk) begin
        case (sel)
            2'b00: q <= d;
            2'b01: q <= 4'hA;
            2'b1x: q <= 4'hB;
            2'bz1: q <= 4'hC;
            default: q <= 4'hF;
        endcase

        case (sel)
            2'b00: q_default <= d;
            default: q_default <= 4'hD;
        endcase
    end
endmodule
