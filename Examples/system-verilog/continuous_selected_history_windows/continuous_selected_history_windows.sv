/*
:name: continuous_selected_history_windows
:description: §10.3/§28.12 — selected net drivers may snapshot one literal source write
:tags: 10.3 28.12
:type: simulation
*/
module top;
  logic [7:0] source = 8'b1010_1010;
  wire [7:0] bus;

  assign bus[0] = source[0];
  assign bus[3:0] = source[3:0];

  initial begin
    if (bus[0] !== source[0])
      $display("FAIL bit");
    else if (bus[3:0] !== source[3:0])
      $display("FAIL window");
    else
      $display("PASS");
    $finish;
  end
endmodule
