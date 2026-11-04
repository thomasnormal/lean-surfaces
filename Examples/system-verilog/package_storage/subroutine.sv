package Functions;
  function int value(); return 9; endfunction
endpackage
module top;
  initial begin $display("function %0d", Functions::value()); $finish; end
endmodule
