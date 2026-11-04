module top;
  logic [23:0] word = {{2{"A"}}, "B"};
  logic [31:0] controls = {2{"A\n"}};
  initial begin
    $display("strings %h %h", word, controls);
    $finish;
  end
endmodule
