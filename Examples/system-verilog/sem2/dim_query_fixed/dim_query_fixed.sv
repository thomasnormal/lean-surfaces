// Fixed packed dimensions are elaboration metadata, not a run-time read.
// These queries stay exact because the [7:4] range is independent of any
// parameter point.
module dim_query_fixed (
  input  logic [7:4] a,
  output logic [31:0] l,
  output logic [31:0] r,
  output logic [31:0] lo,
  output logic [31:0] hi,
  output logic [31:0] inc,
  output logic [31:0] sz
);
  always_comb begin
    l  = $left(a);
    r  = $right(a);
    lo = $low(a);
    hi = $high(a);
    inc = $increment(a);
    sz = $size(a);
  end
endmodule
