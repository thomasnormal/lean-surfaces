/*
:name: unique0_case
:description: IEEE 1800-2023 §12.5.3 — unique0 cases with an allowed no-match path
:tags: 12.5.3
:type: simulation
*/
module top;
  initial begin
    int value;
    int result;

    value = 2;
    result = 0;
    unique0 case (value)
      1: result = 1;
      2: result = 2;
    endcase
    if (result !== 2) begin
      $display("FAIL match %0d", result);
      $finish;
    end

    value = 13;
    result = 99;
    unique0 case (value)
      1: result = 1;
      2: result = 2;
    endcase
    if (result !== 99) begin
      $display("FAIL no-match %0d", result);
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
