/*
:name: streaming_aggregate_member
:description: §11.4.14 — right streaming into a packed member window
:tags: 11.4.14
:type: simulation
*/
module top;
  logic [3:0] source;
  logic [1:0] out;
  struct packed { logic [1:0] hi; logic [1:0] lo; } value [0:0];

  initial begin
    source = 4'b1011;
    {>> {value[0].lo, out}} = source;
    if (value[0].lo === 2'b10 && out === 2'b11)
      $display("PASS");
    else
      $display("FAIL %b %b", value[0].lo, out);
    $finish;
  end
endmodule
