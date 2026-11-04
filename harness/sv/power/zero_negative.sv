module top;
// DIVERGENCE: IEEE 1800-2023 §11.4.3 Table 11-4 requires all x for an
// integral zero base raised to a negative exponent. Icarus agrees. The
// separate reference run returns zero, so these rows are not confirmations.
// REFERENCE: c6e89990f6b74c057dad284b xrun(64)-24.03-s004 2026-10-12T07:58:29Z | tests=zero_negative | source=harness/sv/power/zero_negative.sv@sha256:2c801f5e1c024f0b35b3da64079f4425b2adfc37010872064fe7c6a6d2714a42 | top=top | args=[] | map=zero-negative-rows
  logic [7:0] unsigned_base;
  logic signed [7:0] signed_base;
  logic signed [3:0] exponent;
  initial begin
    unsigned_base = 0;
    signed_base = 0;
    exponent = -1;
    if ((unsigned_base ** exponent) !== 8'bxxxxxxxx) $display("FAIL unsigned zero negative");
    if ((signed_base ** exponent) !== 8'bxxxxxxxx) $display("FAIL signed zero negative");
    if ((0 ** -1) !== 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx) $display("FAIL literal zero negative");
    $display("PASS");
    $finish;
  end
endmodule
