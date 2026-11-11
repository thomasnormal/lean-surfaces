// IEEE 1800-2023 §§9.4.2.2, 12.5: a plain @* case without a default
// retains its target when no item matches.  The source case remains intact.
module always_star_case_latch_e #(parameter int W = 4) (
    input logic [1:0] sel,
    input logic [W-1:0] d,
    output logic [W-1:0] q
);
    always @* begin
        case (sel)
            2'b00: q = d;
            2'b01: q = ~d;
        endcase
    end
endmodule
