// WP-B2 gate 3 pin P15: a shift into a WIDER target. The left operand is zero-extended to the context width BEFORE the shift (so the bits shifted out of the 4-bit operand survive in a 5-bit and an 8-bit target), a `>>` is a logical shift of the extended operand, and an amount at least the CONTEXT width gives 0 (`s = 5` into 5 bits).
module wl_shl_wide (
  input  logic [3:0] a,
  input  logic [2:0] s,
  output logic [4:0] y5,
  output logic [7:0] y8,
  output logic [4:0] r5,
  output logic [7:0] r8
);
  assign y5 = a << s;
  assign y8 = a << s;
  assign r5 = a >> s;
  assign r8 = a >> s;
endmodule
