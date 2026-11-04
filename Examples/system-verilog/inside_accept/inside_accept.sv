// Small self-check witness for ordinary inside-expression membership.
module top;
  logic [3:0] value;

  initial begin
    value = 4'd3;
    if (!(value inside {[4'd1:4'd5]})) begin
      $display("FAIL inside range hit");
      $finish;
    end
    if (value inside {[4'd4:4'd6]}) begin
      $display("FAIL inside range miss");
      $finish;
    end
    if (!(value inside {4'd1, 4'd3})) begin
      $display("FAIL inside scalar set");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
