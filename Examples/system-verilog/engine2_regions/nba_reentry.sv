module nba_reentry;
  reg value;

  initial begin
    value = 0;
    #1;
    $display("active %0d", value);
    value <= 1;
    #0;
    $display("inactive %0d", value);
    #1;
    $display("later %0d", value);
  end

  always @(posedge value) begin
    $display("reentered %0d", value);
  end
endmodule
