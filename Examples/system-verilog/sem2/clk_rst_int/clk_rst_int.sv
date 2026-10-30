// REFUSED by the clock discipline (`Clock:reset`, WP-Q0): the asynchronous
// reset of the block is generated inside the design (a register), not an
// input port. A real simulator resets asynchronously the moment `rst_q`
// falls; the model's reset-event phase compares the settled inputs between
// snapshots and does not see it.
module clk_rst_int (
  input  logic clk, d, rst,
  output logic q
);
  logic rst_q;
  always_ff @(posedge clk) rst_q <= ~rst;
  always_ff @(posedge clk or negedge rst_q)
    if (!rst_q) q <= 1'b0;
    else q <= d;
endmodule
