module blocked_sensitivity;
  reg flag;

  initial begin
    flag = 0;
    $display("waiting");
    @(posedge flag);
    $display("unreachable");
  end
endmodule
