/*
:name: pure_empty_subroutine_statements_adapter
:description: Discarded calls to empty tasks carry no adapter state.
:tags: 13.4
:type: simulation
*/
module top;
  task automatic noop();
  endtask
  task automatic input_noop(input logic value);
  endtask
  initial begin
    noop();
    input_noop(1'b0);
    $display("PASS");
    $finish;
  end
endmodule
