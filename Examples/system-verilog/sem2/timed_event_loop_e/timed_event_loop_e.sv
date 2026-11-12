module timed_event_loop_e(input logic [7:0] x, output logic [3:0] y);
  integer i;
  always @* begin
    y = 0;
    for (i = 0; i < 8; i = i + 1) if (x[i]) y = i;
  end
endmodule
