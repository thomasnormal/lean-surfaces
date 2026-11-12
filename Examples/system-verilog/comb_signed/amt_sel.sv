// Selects of a signed input as the amount of a shift: a select is an unsigned value (IEEE 1800-2023 §11.8.1), and the
// amount of a shift is unsigned in any case (§11.4.10).
module amt_sel (
    input  logic [7:0]        a,
    input  logic signed [7:0] x,
    output logic [7:0]        y,
    output logic [7:0]        z
);
    assign y = a << x[2:0];
    assign z = a >> x[7:5];
endmodule
