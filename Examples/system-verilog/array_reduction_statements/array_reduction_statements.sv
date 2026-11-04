/* Discarded pure fixed-array reductions have no observable result. */
module top;
  logic [3:0] values [2];
  initial begin
    values[0] = 4'd1;
    values[1] = 4'd2;
    values.sum();
    values.product();
    values.and();
    values.or();
    values.xor();
    $display("PASS");
    $finish;
  end
endmodule
