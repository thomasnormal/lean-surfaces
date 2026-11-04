module top;
  initial begin
    repeat (3) begin
      static int saved [0:1] = '{4, 8};
      automatic int fresh [0:1] = '{4, 8};
      $display("entry %0d %0d", saved[0], fresh[0]);
      saved[0] = saved[0] + 1;
      fresh[0] = fresh[0] + 1;
    end
    $finish;
  end
endmodule
