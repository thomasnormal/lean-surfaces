/*
:name: pure_string_query_statements_adapter
:description: Discarded source-pure string queries carry no adapter state.
:tags: 6.16
:type: simulation
*/
module top;
  string len_text;
  string getc_text;
  string atoi_text;
  string radix_text;
  string left;
  string rhs;
  initial begin
    len_text = "hello";
    getc_text = "101";
    atoi_text = "101";
    radix_text = "101";
    left = "101";
    rhs = "101";
    len_text.len();
    getc_text.getc(0);
    atoi_text.atoi();
    radix_text.atobin();
    left.compare(rhs);
    left.icompare(rhs);
    $display("PASS");
    $finish;
  end
endmodule
