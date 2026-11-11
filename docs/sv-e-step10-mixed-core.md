# E Step 10 mixed comb/edge source evidence

`Examples/system-verilog/sem2/mixed_core_step10/` is a clean-room source
fixture for the mixed-core boundary in E migration Step 10. It keeps two
source-shaped `always_comb` processes beside one NBA-only
`always_ff @(posedge clk)` process. The second comb process reads the first's
output, so the observable `post` value tests both ordinary comb settling and a
second settle after the edge commits `q`.

The source follows IEEE 1800-2023 §§9.2.2.2.1, 9.2.2.4 and 10.4.2. The
fixture's parser/profile proof confirms three retained processes and the
existing mixed profile. `agree.lean` deliberately makes no E execution claim:
the mixed executor is the Step 10 semantic work. `check.py` compares the
source rows from Icarus 13.0 with Xcelium through the simulator readiness gate;
rows that change `q` at an edge must also show the post-edge `n` and `post`
values after comb re-settling.

Measured with Icarus 13.0 (s20250103) and Xcelium 24.03-s004: all nine
source rows match. The startup row is `q=xxxx n=xxxx post=xxxx`; the
pre-edge rows are `en1_d3: q=1111 n=1100 post=1101`,
`en0_da: q=0011 n=1001 post=1010`, `en1_x5: q=0101 n=x000 post=xxxx`,
and `en0_z0: q=x101 n=x101 post=xxxx`. The corresponding post-edge rows
are `en1_d3: q=0011 n=0000 post=0001`, `en0_da: q=0101 n=1111 post=0000`,
`en1_x5: q=x101 n=x000 post=xxxx`, and `en0_z0: q=x111 n=x111 post=xxxx`.
The clean-room source SHA-256 is
`95f5977842c56ab28f7fd36af045b0086fcf68696a5266280d2c67cf473f9dec` and
the regenerated envelope SHA-256 is
`5847b2643400cbda0a4f839ce267db6c40df55c14ba3336a7c573dda161bfc0b`.
