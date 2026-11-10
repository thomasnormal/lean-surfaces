// IEEE 1800-2023 §§6.21, 9.2.2.4: private static cells survive re-entry.
module static_local_lifetime_step11 #(parameter int W = 4) (
    input logic clk, reset, load,
    input logic [W-1:0] d,
    output logic [W-1:0] q_old, q_new, q_shadow, q_known,
    output logic [W+3:0] q_signed
);
    always_ff @(posedge clk) begin : capture
        logic [W-1:0] t;
        bit [W-1:0] known;
        static logic signed [W-1:0] signed_t;
        if (reset) begin
            t = '0;
            known = '0;
            signed_t = '0;
        end
        q_old <= t;
        q_known <= known;
        if (load) begin
            t = d;
            known = d;
            signed_t = $signed(d);
        end
        q_new <= t;
        q_signed <= signed_t;
        begin : shadow
            logic [W-1:0] t;
            if (load) t = ~d;
            q_shadow <= t;
        end
    end
endmodule
