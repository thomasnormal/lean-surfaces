/*
:name: unpacked_conditional
:description: §11.4.11 — conditional fixed-unpacked array assignment selects or merges cells
:tags: 11.4.11
:type: simulation
*/
module top;
  logic [7:0] a [0:1];
  logic [7:0] b [0:1];
  logic [7:0] value [0:1];
  logic choose;
  initial begin
    a[0] = 8'hf0;
    a[1] = 8'h0f;
    b[0] = 8'h0f;
    b[1] = 8'hf0;
    choose = 1'b1;
    value = choose ? a : b;
    if (value[0] === 8'hf0 && value[1] === 8'h0f) $display("PASS1");
    else $display("FAIL1 %h %h", value[0], value[1]);
    choose = 1'bx;
    value = choose ? a : b;
    if (value[0] === 8'hxx && value[1] === 8'hxx) $display("PASS2");
    else $display("FAIL2 %h %h", value[0], value[1]);
    $finish;
  end
endmodule
