// Small self-check witness for dynamic inside-expression range endpoints.
module top;
  logic [3:0] value;
  logic [3:0] low;
  logic [3:0] high;

  initial begin
    value = 4'd3;
    low = 4'd2;
    high = 4'd4;
    if (!(value inside {[low:high]})) begin
      $display("FAIL dynamic inside hit");
      $finish;
    end

    low = 4'd5;
    high = 4'd6;
    if (value inside {[low:high]}) begin
      $display("FAIL dynamic inside miss");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
