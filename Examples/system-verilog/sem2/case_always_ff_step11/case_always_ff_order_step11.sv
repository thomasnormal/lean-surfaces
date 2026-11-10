// Clean-room IEEE 1800-2023 12.5: ordered labels, empty/no-default arms,
// default before explicit labels, and nested cases with ordered NBA issues.
module case_always_ff_order_step11 (
    input  logic       clk,
    input  logic [1:0] sel,
    input  logic [3:0] d,
    output logic [3:0] q,
    output logic [3:0] q_hold,
    output logic [3:0] q_empty,
    output logic [3:0] q_nested
);
    always_ff @(posedge clk) begin
        case (sel)
            default: q <= 4'hF;
            2'b00, 2'b01: q <= d;
            2'b01: q <= 4'h9;
            2'b1x: q <= 4'hB;
            2'bz1: q <= 4'hC;
        endcase
        case (sel)
            2'b00: q_hold <= d;
        endcase
        case (sel)
            2'b00: begin end
            default: q_empty <= d;
        endcase
        case (sel)
            2'b00: begin
                q_nested <= 4'h1;
                case (d[1:0])
                    2'b01: q_nested <= d;
                    default: q_nested <= 4'h2;
                endcase
            end
            default: q_nested <= 4'h3;
        endcase
    end
endmodule
