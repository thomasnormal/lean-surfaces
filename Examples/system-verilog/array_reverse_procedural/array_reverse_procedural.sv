/*
:name: array_reverse_procedural
:description: IEEE 1800-2023 7.12.2 — reverse arrays initialized and copied procedurally
:tags: 7.12.2 10.4.1
:type: simulation
*/
module top;
  logic [7:0] source[3];
  logic [7:0] values[3];
  logic [7:0] copy[3];

  initial begin
    source = '{8'h10, 8'h20, 8'h30};
    values = source;
    copy = source;
    values.reverse();
    values.reverse();
    if (values[0] == 8'h10 && values[2] == 8'h30 &&
        copy[0] == 8'h10 && copy[2] == 8'h30)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
