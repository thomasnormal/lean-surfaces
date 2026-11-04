module top;
  initial begin
    logic [7:0] value;
    logic [63:0] widened;
    logic [2:0] narrowed;
    integer index;
    value = 8'b10xz0011;
    index = 1;
    widened = $countones(value);
    narrowed = $countones(8'hff);
    if (widened != 3 || narrowed != 0 || $countones(value) < -1 ||
        $onehot(8'd1) !== 32'd1 || $countones(value[index +: 3]) != 1 ||
        $countones({value, 4'b1111}) != 7 ||
        $countbits($countones(value), 1'b1) != 2 ||
        $isunknown(value ^ 8'b00000000) !== 1'b1) begin
      $display("FAIL: query operand and result contexts");
      $finish;
    end
    case ($countones(value))
      $countones(8'b11100000): $display("PASS");
      default: $display("FAIL: pure query in ordinary case");
    endcase
    $finish;
  end
endmodule
// REFERENCE: 14537610ce5c2ea9290e3eb3 xrun(64) 24.03-s004 2026-10-10T09:45:09Z; PASS.
