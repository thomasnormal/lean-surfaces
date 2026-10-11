module top;
  logic [3:0] value;
  logic signed [3:0] same_signed;
  logic [3:0] same_unsigned;
  logic [7:0] wide_signed, wide_unsigned;

  initial begin
    value = 4'b1001;
    same_signed = $signed(value);
    same_unsigned = $unsigned(value);
    wide_signed = $signed(value);
    wide_unsigned = $unsigned(value);
    if ((same_signed === value) && (same_unsigned === value) &&
        (wide_signed === 8'hf9) && (wide_unsigned === 8'h09) &&
        ($signed(value) < 4'sd0) && !($unsigned(value) < 4'sd0) &&
        ($signed(value) === signed'(value)) &&
        ($unsigned(same_signed) === unsigned'(same_signed)) &&
        ($bits($signed(value)) === 32'd4) &&
        ($bits($unsigned(value)) === 32'd4))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 67ac3eea85bdf0c1f4239ebd independent-simulator 2026-10-11T16:22:48Z
