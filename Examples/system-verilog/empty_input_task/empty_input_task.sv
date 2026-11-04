/* Empty input-only tasks have no body or copy-out effect. */
module top;
  logic value;
  task automatic noop(input logic x);
  endtask
  initial begin
    value = 1'b0;
    noop(1'b0);
    noop(value);
    $display("PASS");
    $finish;
  end
endmodule
