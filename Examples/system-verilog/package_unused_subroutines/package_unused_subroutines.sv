// Uncalled package routines are declarations only and have no runtime effect.
package Functions;
  task automatic never_called();
    $display("SHOULD NOT RUN");
  endtask
  function automatic int also_unused(input int value);
    return value + 1;
  endfunction
endpackage
module top;
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
