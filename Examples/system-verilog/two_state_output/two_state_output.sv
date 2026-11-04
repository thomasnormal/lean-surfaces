module two_state_output(output bit a);
  initial begin
    if (a == 1'b0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
