module top;
  logic [7:0] source_value;
  int index_value;
  logic low_bit;
  logic clear_bit;
  logic z_bit;
  logic x_bit;
  logic high_bit;
  logic below_bit;
  logic above_bit;

  initial begin
    source_value = 8'b10xz0101;
    index_value = 0;
    low_bit = source_value[index_value];
    index_value = 1;
    clear_bit = source_value[index_value];
    index_value = 4;
    z_bit = source_value[index_value];
    index_value = 5;
    x_bit = source_value[index_value];
    index_value = 7;
    high_bit = source_value[index_value];
    index_value = -1;
    below_bit = source_value[index_value];
    index_value = 8;
    above_bit = source_value[index_value];
    $display("bit-indices=[%b][%b][%b][%b][%b][%b][%b]", low_bit, clear_bit,
             z_bit, x_bit, high_bit, below_bit, above_bit);
    if ((low_bit === 1'b1) && (clear_bit === 1'b0) &&
        (z_bit === 1'bz) && (x_bit === 1'bx) && (high_bit === 1'b1) &&
        (below_bit === 1'bx) && (above_bit === 1'bx))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
