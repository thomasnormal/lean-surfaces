module top;
  int calls;
  logic [3:0] value;
  function logic next_bit(); calls++; return 1'b1; endfunction
  initial begin
    calls = 0;
    value = '{default:next_bit()};
    $display("effects %b %0d", value, calls);
    $finish;
  end
endmodule
