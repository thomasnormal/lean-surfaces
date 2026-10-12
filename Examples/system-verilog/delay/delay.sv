module delay;
  logic [3:0] value;
  initial begin
    value = 4'd1;
    #3;
    value = 4'd2;
    $display("PASS");
    $finish;
  end
endmodule
