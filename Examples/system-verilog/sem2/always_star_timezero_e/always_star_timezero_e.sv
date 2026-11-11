// IEEE 1800-2023 §§9.2.2.2.2, 9.4.2.2: a plain @* waits for a
// sensitivity event.  The continuous driver is deliberately retained in the
// source shape so E, rather than always_comb lowering, owns the time-zero
// ordering.
module always_star_timezero_e #(parameter int W = 4) (
    input logic [W-1:0] a,
    output logic [W-1:0] y_star,
    output logic [W-1:0] y_comb
);
    wire [W-1:0] k;
    assign k = a;

    always @* y_star = k;
    always_comb y_comb = k;
endmodule
