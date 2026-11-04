// WP-B2 pin P3: `+` and `-` are context-determined: operands are ZERO-extended to the target width (the carry survives in a wider target, a subtraction wraps modulo 2^5), truncated into a narrower one; any x/z bit of an operand makes the whole result x; chains associate to the left at the context width.
module wl_addsub_ctx (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic [7:0] c,
  output logic [4:0] s5,
  output logic [3:0] s4,
  output logic [2:0] s3,
  output logic [4:0] d5,
  output logic [8:0] m9,
  output logic [4:0] chain5
);
  assign s5 = a + b;
  assign s4 = a + b;
  assign s3 = a + b;
  assign d5 = a - b;
  assign m9 = c + b;
  assign chain5 = a + b + 1'b1 - a;
endmodule
