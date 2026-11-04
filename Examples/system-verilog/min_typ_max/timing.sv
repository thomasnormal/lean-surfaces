module top;
  initial begin
    #3;$display("marker3");
    #4;$display("marker7");
  end
  initial begin
    #(2:5:8);
    $display("selected");
    $finish;
  end
endmodule
