/*
:name: qualified_if_fallback
:description: IEEE 1800-2023 §12.4.2 — unique and priority if chains with an explicit fallback have no qualifier diagnostic
:tags: 12.4.2
:type: simulation
*/
module top;
  initial begin
    int value;
    int result;

    value = 5;
    result = 0;
    unique if (value == 1) result = 1;
    else if (value == 2) result = 2;
    else result = 99;
    if (result !== 99) begin
      $display("FAIL unique %0d", result);
      $finish;
    end

    value = 3;
    result = 0;
    priority if (value > 4) result = 4;
    else if (value > 2) result = 3;
    else result = 99;
    if (result !== 3) begin
      $display("FAIL priority %0d", result);
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
