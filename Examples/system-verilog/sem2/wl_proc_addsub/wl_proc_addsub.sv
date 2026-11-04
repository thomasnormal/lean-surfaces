// WP-B2 gate 2a pin P9: `+` and `-` in the leaves of an `always_comb` `if`: the operands are zero-extended to the 5-bit target in both arms; an x/z bit of an operand makes the whole sum x; an x condition takes the `else` arm (IEEE 1800-2023 12.4).
module wl_proc_addsub (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic c,
  output logic [4:0] y
);
  always_comb begin
    if (c) y = a + b; else y = a - b;
  end
endmodule
