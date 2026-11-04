// Small self-check witness for packed concatenation and replication.
module top;
  logic [3:0] high;
  logic [3:0] low;
  logic [7:0] joined;
  logic [7:0] repeated;

  initial begin
    high = 4'ha;
    low = 4'h5;
    joined = {high, low};
    if (joined !== 8'ha5) begin
      $display("FAIL concatenation");
      $finish;
    end

    repeated = {2{4'b0011}};
    if (repeated !== 8'h33) begin
      $display("FAIL replication");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
