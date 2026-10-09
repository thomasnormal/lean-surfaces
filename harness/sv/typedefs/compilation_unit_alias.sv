typedef logic [11:0] compilation_word_t;
typedef compilation_word_t compilation_alias_t;

module top;
  compilation_alias_t source_value;
  compilation_word_t sum_value;
  logic [15:0] widened_value;

  initial begin
    source_value = 12'h8a5;
    sum_value = source_value + 12'h123;
    widened_value = source_value;
    $display("unit-alias=[%h][%h][%h]", source_value,
             sum_value, widened_value);
    if ((source_value === 12'h8a5) &&
        (sum_value === 12'h9c8) &&
        (widened_value === 16'h08a5) && !(source_value < 0))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
