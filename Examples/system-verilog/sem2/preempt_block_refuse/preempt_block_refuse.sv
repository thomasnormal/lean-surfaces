// A multi-write blocking process has a §4.7 suspension point that another
// process can observe. The default admission guard must refuse it.
module preempt_block_refuse (
  input logic a,
  input logic b,
  output logic q,
  output logic r,
  output logic z
);
  always_comb begin
    q = a;
    r = q;
  end
  always_comb z = q;
endmodule
