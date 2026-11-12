// A shift in a localparam used as a value (the clean-room repro `localparam_shift.sv`, verbatim below this header):
// `BIAS = (1 << (E - 1)) - 1` (IEEE 1800-2023 §11.4.10), an `integer` read in the unsigned context of `x + BIAS` (§11.8.2:
// its 32-bit value is converted to the context, which the envelope marks `Resize`).
module localparam_shift #(parameter integer E = 8) (
    input logic [E-1:0] x,
    output logic [E-1:0] y
);
    localparam integer BIAS = (1 << (E - 1)) - 1;
    assign y = x + BIAS;
endmodule
