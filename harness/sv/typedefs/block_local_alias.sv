module top;
  typedef logic [3:0] module_nibble_t;

  initial begin
    typedef module_nibble_t local_nibble_t;
    typedef logic signed [7:0] local_signed_byte_t;
    local_nibble_t source_value;
    local_signed_byte_t cast_value;
    local_nibble_t narrowed_value;
    source_value = 4'h9;
    cast_value = local_signed_byte_t'(source_value);
    narrowed_value = local_nibble_t'(cast_value + 8'h10);
    $display("block-alias=[%h][%h][%h]", source_value,
             cast_value, narrowed_value);
    if ((source_value === 4'h9) &&
        (cast_value === 8'h09) &&
        (narrowed_value === 4'h9) && !(cast_value < 0))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
