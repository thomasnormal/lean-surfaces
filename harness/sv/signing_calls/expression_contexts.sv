module top;
  logic [3:0] value;
  logic [7:0] signed_sum, unsigned_sum, concatenated;
  logic [3:0] selected;
  logic matched;

  initial begin
    value = 4'b1010;
    signed_sum = $signed(value) + 8'sd0;
    unsigned_sum = $signed(value) + 8'd0;
    concatenated = {$signed(value)};
    selected = 4'b0000;
    selected[1:0] = $unsigned(value[3:2]);
    matched = 1'b0;
    case ($signed(value))
      -4'sd6: matched = 1'b1;
      default: matched = 1'b0;
    endcase
    if ((signed_sum === 8'hfa) && (unsigned_sum === 8'h0a) &&
        (concatenated === 8'h0a) && (selected === 4'b0010) && matched &&
        ($signed(value) < 4'sd0) && ($unsigned(value) > 4'd0) &&
        (($signed(value) < 4'sd0 ? $unsigned(value) : 4'd0) === value))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 28840f51894bfd61727fb24d independent-simulator 2026-10-11T16:22:51Z
