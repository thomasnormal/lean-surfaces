`define TEST """
many
more
lines"""

module top;
  initial begin
    string text;
    string path;
    text = `TEST;
    path = `__FILE__;
    if (text.len() > 0 && path.len() > 0)
      $display("PASS");
    else
      $display("FAIL: predefined string macro was empty");
    $finish;
  end
endmodule
