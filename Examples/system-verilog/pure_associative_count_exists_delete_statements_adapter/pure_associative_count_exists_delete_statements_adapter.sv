/*
:name: pure_associative_count_exists_delete_statements_adapter
:description: Finite associative count and exists observations and empty deletes are inert in the adapter.
:tags: 7.9.2 7.9.3
:type: simulation
*/
module top;
  int score[int];
  int empty[int];
  initial begin
    score[1] = 10;
    score[2] = 20;
    score.num();
    score.size();
    score.exists(1);
    empty.delete(7);
    empty.delete();
    if (score.num() == 2 && score.exists(1) && empty.num() == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
