// Small self-check witness for the admitted casez/casex predicates.
module top;
  logic [1:0] value;
  logic [1:0] result;

  initial begin
    value = 2'b1x;
    casez (value)
      2'b1?: result = 2'b01;
      default: result = 2'b00;
    endcase
    if (result !== 2'b01) begin
      $display("FAIL casez");
      $finish;
    end

    casex (2'bx0)
      2'b00: result = 2'b10;
      default: result = 2'b00;
    endcase
    if (result !== 2'b10) begin
      $display("FAIL casex");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
