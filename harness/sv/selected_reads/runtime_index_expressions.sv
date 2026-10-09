module top;
  logic [3:0] upper_value;
  logic [3:0] lower_value;
  logic [7:0] source_value;
  int index_value;
  logic selected_bit;
  logic [3:0] below_part;
  logic [3:0] above_part;
  logic [3:0] high_part;

  initial begin
    upper_value = 4'hc;
    lower_value = 4'h3;
    source_value = {upper_value, lower_value};
    index_value = 2;
    selected_bit = source_value[index_value + 1];
    below_part = source_value[(index_value - 4) +: 4];
    above_part = source_value[(index_value + 7) -: 4];
    high_part = source_value[(index_value + index_value) +: 4];
    $display("index-expressions=[%b][%b][%b][%b]", selected_bit, below_part,
             above_part, high_part);
    if ((selected_bit === 1'b0) && (below_part === 4'b11xx) &&
        (above_part === 4'bxx11) && (high_part === 4'b1100))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
