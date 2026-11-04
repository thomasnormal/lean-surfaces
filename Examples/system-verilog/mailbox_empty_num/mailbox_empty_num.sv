module top;
  mailbox box;
  int result;

  initial begin
    box = new();
    result = box.num();
    if (result === 0)
      $display("PASS");
    else
      $display("FAIL: result=%0d", result);
    $finish;
  end
endmodule
