/* Empty zero-argument tasks/functions have no observable call effect. */
module top;
  task automatic noop();
  endtask
  function void done();
  endfunction
  initial begin
    noop();
    done();
    $display("PASS");
    $finish;
  end
endmodule
