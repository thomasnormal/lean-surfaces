module top;
  logic [7:0] source_value;
  logic [3:0] high_part;
  logic [3:0] middle_part;
  logic [3:0] above_part;
  logic [3:0] below_part;
  logic [3:0] outside_high;
  logic [3:0] outside_low;

  initial begin
    source_value = 8'b10xz0101;
    high_part = source_value[7:4];
    middle_part = source_value[5:2];
    above_part = source_value[9:6];
    below_part = source_value[1:-2];
    outside_high = source_value[12:9];
    outside_low = source_value[-1:-4];
    $display("simple-parts=[%b][%b][%b][%b][%b][%b]", high_part, middle_part,
             above_part, below_part, outside_high, outside_low);
    if ((high_part === 4'b10xz) && (middle_part === 4'bxz01) &&
        (above_part === 4'bxx10) && (below_part === 4'b01xx) &&
        (outside_high === 4'bxxxx) && (outside_low === 4'bxxxx))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
