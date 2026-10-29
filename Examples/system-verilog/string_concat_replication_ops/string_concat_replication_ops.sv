/* Source-pure §11.4.12.2 string concatenation and replication. */
// Hello_World!
// testtesttesttest
module top;
  string joined;
  string repeated;

  initial begin
    joined = {"Hello", "_", "World", "!"};
    repeated = {4{"test"}};
    $display("%s", joined);
    $display("%s", repeated);
    $finish;
  end
endmodule
