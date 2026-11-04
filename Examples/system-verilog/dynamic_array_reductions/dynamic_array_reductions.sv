/* A finite literal dynamic array is flattened into reduction cells. */
module top;
  byte values[] = '{1, 2, 3, 4};
  byte total;
  byte product;
  byte all_bits;
  byte any_bits;
  byte parity;
  initial begin
    total = values.sum();
    product = values.product();
    all_bits = values.and();
    any_bits = values.or();
    parity = values.xor();
    if (total === 8'd10 && product === 8'd24 &&
        all_bits === 8'd0 && any_bits === 8'd7 && parity === 8'd4)
      $display("PASS");
    else
      $display("FAIL %0d %0d %0d %0d %0d", total, product,
               all_bits, any_bits, parity);
    $finish;
  end
endmodule
