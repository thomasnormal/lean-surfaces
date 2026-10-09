module top;
  logic signed [7:0] source_value;
  int base_value;
  logic signed [15:0] whole_value;
  logic signed [15:0] selected_value;
  logic signed [15:0] simple_value;
  logic signed [15:0] indexed_value;
  logic signed [15:0] bit_value;

  initial begin
    source_value = 8'he1;
    base_value = 4;
    whole_value = source_value;
    selected_value = source_value[7:0];
    simple_value = source_value[7:4];
    indexed_value = source_value[base_value +: 4];
    bit_value = source_value[7];
    $display("unsigned-context=[%h][%h][%h][%h][%h]", whole_value,
             selected_value, simple_value, indexed_value, bit_value);
    if ((whole_value === 16'hffe1) && (selected_value === 16'h00e1) &&
        (simple_value === 16'h000e) && (indexed_value === 16'h000e) &&
        (bit_value === 16'h0001) && (source_value < 0) &&
        !(source_value[7:0] < 0) && !(source_value[7:4] < 0))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
