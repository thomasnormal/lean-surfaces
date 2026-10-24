/*
:name: sformat_literal_integral
:description: IEEE 1800-2023 §§5.9 and 21.3.3 — a plain literal $sformat writes right-aligned bytes into packed integral storage.
:tags: 5.9 21.3.3 sformat string assignment
:type: simulation
*/
module top;
  logic [7:0] narrow;
  logic [47:0] wide;

  initial begin
    $sformat(narrow, "A");
    $sformat(wide, "Hello");
    if (narrow === 8'h41)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
