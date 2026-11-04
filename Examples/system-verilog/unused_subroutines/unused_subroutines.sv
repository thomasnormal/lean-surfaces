module top;
  task automatic never_called();
    $display("SHOULD NOT RUN");
  endtask
  function automatic int also_unused(input int value);
    return value + 1;
  endfunction
  // expected self-check line: PASS
  initial $display("PASS");
endmodule
