/* Discarded queries on unchanged ASCII strings have exact scalar results. */
module top;
  initial begin
    string len_text;
    string getc_text;
    string atoi_text;
    string radix_text;
    string left;
    string rhs;
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
