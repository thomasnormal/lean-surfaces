module top;
  int calls;
  logic [3:0] value;
  function logic tick(); calls++; return 1'b1; endfunction
  initial begin
    calls = 0;
    value = {{0{tick()}}, 4'ha};
    $display("effects %0d %h", calls, value);
    $finish;
  end
endmodule
