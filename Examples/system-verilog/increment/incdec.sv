module top;
  logic [3:0] value;
  initial begin
    value = 4'd0;
    value++;
    ++value;
    value--;
    --value;
    value = 4'hf;
    value++;
    if (value !== 4'h0) $display("FAIL increment wrap");
    else $display("PASS");
    $finish;
  end
endmodule
