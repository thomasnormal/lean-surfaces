// Same-module initialization isolates @* startup from input-port propagation.
module always_star_startup_step11 #(parameter int W = 4) (
    output logic [W-1:0] y_star, y_comb, y_constant_star, y_constant_comb
);
    logic [W-1:0] a = 4'b0011, b = 4'b0101;
    always @* y_star = a ^ b;
    always_comb y_comb = a ^ b;
    // The inferred sensitivity set is empty. @* never wakes; always_comb
    // still runs at startup (IEEE 1800-2023 §9.2.2.2.2).
    always @* y_constant_star = 4'b0110;
    always_comb y_constant_comb = 4'b0110;
endmodule
