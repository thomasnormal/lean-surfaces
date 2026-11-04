module top;
  if (1) begin : live
    function int helper(); return 9; endfunction
  end
  initial begin $display("active member"); $finish; end
endmodule
