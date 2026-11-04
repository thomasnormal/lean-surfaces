module top;
  typedef logic signed [7:0] signed_byte_t;
  typedef signed_byte_t middle_alias_t;
  typedef middle_alias_t final_alias_t;
  final_alias_t source_value;
  logic signed [15:0] widened_value;
  middle_alias_t incremented_value;

  initial begin
    source_value = 8'hf9;
    widened_value = source_value;
    incremented_value = source_value + 1;
    $display("alias-chain=[%h][%h][%h]", source_value,
             widened_value, incremented_value);
    if ((source_value === 8'hf9) &&
        (widened_value === 16'hfff9) &&
        (incremented_value === 8'hfa) && (source_value < 0))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: caf15329e8a86ba4e717f65a TOOL:	xrun(64)	24.03-s004 2026-10-09T21:34:48Z
