// Clean-room Step 11 fixture: casez and casex in one always_ff process.
// The wildcard bits are source-shaped CaseStmt nodes; no case expansion is
// performed before the E edge review.
module casez_casex_always_ff_step11 (
    input  logic       clk,
    input  logic [3:0] sel,
    input  logic [3:0] d,
    output logic [3:0] qz,
    output logic [3:0] qx
);
    always_ff @(posedge clk) begin
        casez (sel)
            4'b1???: qz <= d;
            4'b01??: qz <= 4'h1;
            4'b00z1: qz <= 4'h2;
            default: qz <= 4'h3;
        endcase

        casex (sel)
            4'b1x??: qx <= d;
            4'b01??: qx <= 4'h4;
            4'b00z1: qx <= 4'h5;
            default: qx <= 4'h6;
        endcase
    end
endmodule
