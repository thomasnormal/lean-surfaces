// Small self-check witness for ordinary case-inside range membership.
module top;
  logic [3:0] value;
  logic [3:0] result;

  initial begin
    value = 4'd3;
    case (value) inside
      [4'd0:4'd2]: result = 4'd0;
      [4'd3:4'd5]: result = 4'd1;
      default: result = 4'd2;
    endcase
    if (result !== 4'd1) begin
      $display("FAIL case-inside");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
