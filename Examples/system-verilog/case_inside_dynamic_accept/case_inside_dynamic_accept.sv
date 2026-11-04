// Small self-check witness for dynamic case-inside range endpoints.
module top;
  logic [3:0] value;
  logic [3:0] low;
  logic [3:0] high;
  logic [3:0] result;

  initial begin
    value = 4'd3;
    low = 4'd2;
    high = 4'd4;
    case (value) inside
      [low:high]: result = 4'd1;
      default: result = 4'd0;
    endcase
    if (result !== 4'd1) begin
      $display("FAIL dynamic hit");
      $finish;
    end

    value = 4'd7;
    low = 4'd8;
    high = 4'd9;
    case (value) inside
      [low:high]: result = 4'd1;
      default: result = 4'd0;
    endcase
    if (result !== 4'd0) begin
      $display("FAIL dynamic miss");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
