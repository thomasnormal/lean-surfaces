module signed_two_state_output(output bit signed [3:0] a);
  initial begin
    if (a !== 4'b0000) $display("FAIL initialization");
    a = 4'sb1000;
    if (a >= 4'sb0001) $display("FAIL signed comparison");
    a = 4'bx1z0;
    if (a !== 4'b0100) $display("FAIL two-state conversion");
    $display("PASS");
    $finish;
  end
endmodule
