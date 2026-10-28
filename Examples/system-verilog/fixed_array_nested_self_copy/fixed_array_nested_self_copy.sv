/* IEEE 1800-2023 §7.6: an exact blocking self-copy of a
   multidimensional fixed unpacked integral array is an observable no-op. */
module top;
  logic [3:0] value [0:1][0:2];

  initial begin
    value = '{'{4'h1, 4'h2, 4'h3}, '{4'h4, 4'h5, 4'h6}};
    value = value;
    if (value[0][0] === 4'h1 && value[0][2] === 4'h3 &&
        value[1][0] === 4'h4 && value[1][2] === 4'h6)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
