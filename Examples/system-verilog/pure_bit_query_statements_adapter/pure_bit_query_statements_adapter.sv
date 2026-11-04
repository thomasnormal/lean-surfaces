/*
:name: pure_bit_query_statements_adapter
:description: Discarded pure bit queries carry no adapter state.
:tags: 20.5
:type: simulation
*/
module top;
  logic [3:0] value;
  logic [0:0] mask;
  initial begin
    value = 4'b1010;
    mask = 1'b1;
    $countbits(4'b1010, 1'b1, 1'bx);
    $countones(value);
    $onehot(4'b0001);
    $onehot0(value);
    $isunknown(4'b10x0);
    $countbits(value, mask, 1'bx);
    $display("PASS");
    $finish;
  end
endmodule
