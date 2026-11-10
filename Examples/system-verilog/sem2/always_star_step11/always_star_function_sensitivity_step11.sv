// IEEE 1800-2023 §9.2.2.2.2: @* observes actual arguments, not function globals.
module always_star_function_sensitivity_step11 #(parameter int W = 4) (
    input logic [W-1:0] a, hidden,
    output logic [W-1:0] y_star, y_comb
);
    function automatic logic [W-1:0] probe(input logic [W-1:0] value);
        probe = value ^ hidden;
    endfunction
    always @* y_star = probe(a);
    always_comb y_comb = probe(a);
endmodule
