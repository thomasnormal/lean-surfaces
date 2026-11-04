module top;
  typedef struct packed {logic[7:0] a;logic[7:0] b;} pair_t;
  pair_t pair_value;
  logic[15:0] value;
  logic[15:0] repeated;
  int table_values[0:2];
  initial begin
    value = 256;
    pair_value = '{a:8'($clog2(value)),b:8'($clog2($clog2(value)))};
    repeated = {2{8'($clog2(value))}};
    table_values = '{10,20,30};
    $display("composed %h %h %0d", pair_value, repeated, table_values[$clog2(4)]);
    case ($clog2(value))
      8: $display("selected");
      default: $display("unexpected");
    endcase
    $finish;
  end
endmodule
