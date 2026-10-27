/* Discarded bit queries may read a source-pure named integral history. */
module top;
  logic [3:0] value;
  logic [0:0] mask;
  initial begin
    value = 4'b1010;
    mask = 1'b1;
    $countbits(value, mask, 1'bx);
    $countones(value);
    $onehot(value);
    $onehot0(value);
    $isunknown(value);
    $display("PASS");
    $finish;
  end
endmodule
