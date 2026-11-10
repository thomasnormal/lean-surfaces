// IEEE 1800-2023 §§9.4.2, 27.5: retain an explicit event in a generate arm.
// This is source evidence for a refusal, not an E execution fixture.
module always_event_generate_refusal_step11 #(
    parameter integer ENABLE = 1
) (
    input logic a,
    output logic y
);
    generate
        if (ENABLE) begin : selected
            always @(a) y = a;
        end
    endgenerate
endmodule
