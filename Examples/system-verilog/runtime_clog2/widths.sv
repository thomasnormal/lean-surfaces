module top;
  logic signed [7:0] narrow;
  int signed integer_value;
  logic [127:0] wide;
  logic [2:0] truncated;
  logic signed [63:0] extended;
  initial begin
    narrow = -1; integer_value = -1;
    wide = 128'h80000000000000000000000000000000;
    $display("unsigned %0d %0d %0d", $clog2(narrow), $clog2(integer_value), $clog2(wide));
    wide = wide + 1;
    truncated = $clog2(wide);
    extended = $clog2(wide);
    $display("contexts %0d %0d %0d %0d", $clog2(wide), truncated, extended, $bits($clog2(wide)));
    $finish;
  end
endmodule
