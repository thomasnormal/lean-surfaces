/* Scalar observations of source-pure concatenation and replication history. */
module top;
  initial begin
    string left = "Hi";
    string right = "!";
    string joined;
    string repeated;
    joined = {left, right};
    repeated = {2{left}};
    if (joined.len() == 3 && joined.substr(0, 1) == "Hi" &&
        repeated.len() == 4 && repeated.compare("HiHi") == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
