// IEEE 1800-2023 §§9.2.2.2.2, 9.4.2.2: @* is its own event control.
module always_star_step11 #(parameter int W = 4) (
    input logic [W-1:0] a, b,
    input logic [1:0] sel,
    output logic [W-1:0] y_star, y_comb
);
    always @* begin
        case (sel)
            2'b00: y_star = a;
            2'b01: y_star = b;
            2'b1x: y_star = a ^ b;
            2'b1z: y_star = ~a;
            default: y_star = '1;
        endcase
    end
    always_comb begin
        case (sel)
            2'b00: y_comb = a;
            2'b01: y_comb = b;
            2'b1x: y_comb = a ^ b;
            2'b1z: y_comb = ~a;
            default: y_comb = '1;
        endcase
    end
endmodule
