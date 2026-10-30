// ACCEPTED by the clock discipline (WP-Q0): an enum FSM (IDLE -> RUN -> DONE
// -> IDLE) with a combinational `busy` output, one input-port clock.
module clk_fsm (
  input  logic clk, rst, go,
  output logic busy, done
);
  typedef enum logic [1:0] {IDLE = 2'd0, RUN = 2'd1, DONE = 2'd2} st_t;
  st_t st;
  always_ff @(posedge clk)
    if (rst) st <= IDLE;
    else
      case (st)
        IDLE:    if (go) st <= RUN;
        RUN:     st <= DONE;
        DONE:    st <= IDLE;
        default: st <= IDLE;
      endcase
  assign busy = (st == RUN);
  assign done = (st == DONE);
endmodule
