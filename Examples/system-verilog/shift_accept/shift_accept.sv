// Small self-check witness for four-state integral shifts.
module top;
  logic [3:0] value;
  logic signed [3:0] signed_value;
  logic [1:0] amount;

  initial begin
    value = 4'b1001;
    signed_value = 4'b1001;
    amount = 2'd1;

    if ((value << amount) !== 4'b0010) begin
      $display("FAIL logical left");
      $finish;
    end
    if ((value <<< amount) !== 4'b0010) begin
      $display("FAIL arithmetic left");
      $finish;
    end
    if ((value >> amount) !== 4'b0100) begin
      $display("FAIL logical right");
      $finish;
    end
    if ((value >>> amount) !== 4'b0100) begin
      $display("FAIL unsigned arithmetic right");
      $finish;
    end
    if ((signed_value >>> amount) !== 4'sb1100) begin
      $display("FAIL signed arithmetic right");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
