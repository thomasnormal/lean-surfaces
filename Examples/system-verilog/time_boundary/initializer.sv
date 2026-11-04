// Conservatively retain the restriction even when the query initializes a value.
module top;
  logic [63:0] saved = $time;
  initial begin
    #2;
    $display("saved %0d", saved);
    $finish;
  end
endmodule
