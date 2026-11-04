/*
:name: priority_case_fallback
:description: IEEE 1800-2023 §12.5.3 — priority cases with explicit default fallbacks
:tags: 12.5.3
:type: simulation
*/
module top;
  initial begin
    int value;
    int result;

    value = 2;
    result = 0;
    priority case (value)
      1: result = 1;
      2: result = 2;
      default: result = 99;
    endcase
    if (result !== 2) begin
      $display("FAIL normal %0d", result);
      $finish;
    end

    value = 13;
    result = 0;
    priority casez (value)
      4'b1???: result = 1;
      default: result = 99;
    endcase
    if (result !== 1) begin
      $display("FAIL casez %0d", result);
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
