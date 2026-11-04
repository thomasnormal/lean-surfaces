/*
:name: assoc_unsigned_endpoint_history
:description: IEEE 1800-2023 §7.8.4 - unsigned packed integral associative keys use unsigned endpoint ordering.
:tags: 7.8 7.8.4 associative array unsigned packed integral endpoint
:type: simulation
*/
module top;
  typedef bit [3:0] U4;
  int values[U4];
  U4 key;
  initial begin
    values[4'hF] = 10;
    values[4'h0] = 20;
    values[4'h8] = 30;
    void'(values.first(key));
    if (key !== 4'h0) begin
      $display("FAIL: first should be 0, got %0h", key); $finish;
    end
    void'(values.last(key));
    if (key !== 4'hF) begin
      $display("FAIL: last should be F, got %0h", key); $finish;
    end
    $display("PASS");
    $finish;
  end
endmodule
