// WP-G S3b: a priority encoder as default-then-override: the highest requesting line wins (later `if`
// statements override earlier ones); no request gives 0.
module prio_enc (input logic [3:0] r, output logic [1:0] y);
  always_comb begin
    y = 2'd0;
    if (r[1]) y = 2'd1;
    if (r[2]) y = 2'd2;
    if (r[3]) y = 2'd3;
  end
endmodule
