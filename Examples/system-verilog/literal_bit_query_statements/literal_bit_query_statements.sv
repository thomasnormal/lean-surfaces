/* Discarded literal bit queries have no represented state effect. */
module top;
  initial begin
    $countbits(4'b1010, 1'b1, 1'bx);
    $countones(4'b1010);
    $onehot(4'b0001);
    $onehot0(4'b0000);
    $isunknown(4'b10x0);
    $display("PASS");
    $finish;
  end
endmodule
