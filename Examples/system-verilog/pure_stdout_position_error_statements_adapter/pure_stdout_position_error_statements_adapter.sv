/*
:name: pure_stdout_position_error_statements_adapter
:description: Discarded fseek and ftell calls on the predefined stdout descriptor carry no adapter state.
:tags: 21.7 21.8
:type: simulation
*/
module top;
  initial begin
    $fseek(32'h8000_0001, 0, 0);
    $ftell(32'h8000_0001);
    $display("PASS");
    $finish;
  end
endmodule
