module top(output logic y);
  logic ready;

  initial begin
    wait (ready);
    y = 1'b1;
    $display("WAIT PASS");
    $finish;
  end

  initial begin
    #1 ready = 1'b1;
  end
endmodule
