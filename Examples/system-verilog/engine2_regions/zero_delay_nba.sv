module zero_delay_nba;
  reg value;

  initial begin
    value = 0;
    $display("active %0d", value);
    value <= 1;
    #0;
    $display("inactive %0d", value);
    #1;
    $display("later %0d", value);
  end
endmodule
