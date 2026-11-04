// WP-B2 pin P7: reductions with x/z bits (`|` is 1 given a known 1, `&` is 0 given a known 0, `^` is x given any x).
module wl_red (
  input  logic [3:0] a,
  output logic r_or,
  output logic r_and,
  output logic r_xor,
  output logic r_nor
);
  assign r_or = |a;
  assign r_and = &a;
  assign r_xor = ^a;
  assign r_nor = ~|a;
endmodule
