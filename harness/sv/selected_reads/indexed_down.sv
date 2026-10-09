module top;
  logic [7:0] source_value;
  integer base_value;
  logic [3:0] middle_part;
  logic [3:0] above_part;
  logic [3:0] below_part;
  logic [3:0] outside_part;

  initial begin
    source_value = 8'b10xz0101;
    base_value = 5;
    middle_part = source_value[base_value -: 4];
    base_value = 9;
    above_part = source_value[base_value -: 4];
    base_value = 1;
    below_part = source_value[base_value -: 4];
    base_value = -1;
    outside_part = source_value[base_value -: 4];
    $display("indexed-down=[%b][%b][%b][%b]", middle_part, above_part,
             below_part, outside_part);
    if ((middle_part === 4'bxz01) && (above_part === 4'bxx10) &&
        (below_part === 4'b01xx) && (outside_part === 4'bxxxx))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
