module multi_initial;
  logic [3:0] value;
  initial begin
    value = 4'd1;
    #1;
    value = 4'd2;
  end
  initial begin
    #1;
    if (value !== 4'd2) $display("FAIL");
    else $display("PASS");
    $finish;
  end
endmodule
