// Small self-check witness for four-state case equality and inequality.
module top;
  logic [1:0] value;

  initial begin
    value = 2'b1x;
    if (!(value === 2'b1x)) begin
      $display("FAIL case equality hit");
      $finish;
    end
    if (value === 2'b10) begin
      $display("FAIL case equality miss");
      $finish;
    end
    if (!(value !== 2'b10)) begin
      $display("FAIL case inequality");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
