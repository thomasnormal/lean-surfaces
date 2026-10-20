# Let expressions

IEEE 1800-2023 §11.12 fixtures for declaration-scope binding, context sizing,
nesting, named actuals, live package/unit/generate/hierarchy reads, unused
actuals and NBA capture. [Contract](../../../docs/sv-let-expressions.md).

Seven programs match complete independent transcripts under both tested region
oracles. `call`, `effects` and `program` retain runtime refusals. `typed` and
`defaults` have structural checks only: the independent simulator rejects these
forms with `LTUXDF` and `LTUNDEF`, respectively. No expected transcript is
asserted for them and they are not counted as execution agreements.

| Source | SHA-256 | Invocation key | Qualification |
|---|---|---|---|
| [binding](binding.sv) | `75ce296763a0c23b0ef9aa989e3703fe5d00bf7d43fab02f455ca52eb435f57e` | `b03b0a3b73727ba781dd4d7a` | MATCH |
| [call](call.sv) | `e9b97df59c248d2b2e253878951977cf9a5bf25073957843fb4010c3b62a50f3` | `dd359c6ae6a63f1283f53c17` | REFUSE |
| [certificate](certificate.sv) | `17f5597e37b25f42a237a95ab6d29ab7cde82ccc2015fbe4acbb5d538e9be59a` | `d131ac0601814c4465fbf855` | MATCH |
| [defaults](defaults.sv) | `960fcd5089fce30105543cbba59906fb5656930204eff69cc31035652d1334e6` | `67a561adccd4d999fc45c48f` | oracle unavailable |
| [effects](effects.sv) | `5ee81e71294b540e08ce72971f9e8f2482b6b531752765aa650292c6fbdcca1c` | `528421725d2b3a50177f573c` | REFUSE |
| [local](local.sv) | `bc065ab862053db508afdd460895367de43089665db2f06e3b06d1dce0987b98` | `9e29b5de4163af92fb63e6a5` | MATCH |
| [program](program.sv) | `af52324ce6c3eac8b76f2e61a0cdec2f568c56490ee8e0c1cd7c0be8ced82911` | `f15f532a1ceb1ee3a1fdb244` | REFUSE |
| [sizing](sizing.sv) | `2cc1da1a70aa06e76b0dc57276c9bb08b85f50c0376af42f5e4bf5974c00c6a2` | `49383f3eb729b467587c94dd` | MATCH |
| [structure](structure.sv) | `19ead2ca28de495bf38017cab0cceff22a670236fb44513d68ce7d439694b140` | `9c5fd762733e0f5f2bbc4b92` | MATCH |
| [timing](timing.sv) | `ee50869ba77f49dfd5ba65ec75840593d9e740d5f9c2def33caddaaa86f7fed2` | `60a678378f8e897c3abebf09` | MATCH |
| [typed](typed.sv) | `a479066705456997b5ad17e01df288600829c380eae36aa1526a56178f9d2c5d` | `3c5ee8f06efeb86fb8d95e28` | oracle unavailable |
| [unused](unused.sv) | `ab0dffd96ad1882b35fa5ac036f95d2cd6b2d3219a24ed8a754e4a568e0ae017` | `f177e74e6c20640c68fc43ff` | MATCH |

Independent invocations use top `top` and arguments
`["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"]`,
version `24.03-s004`, 2026-10-20. Successful rows carry full source/status/stdout/
provenance authentication; unavailable rows retain failure receipts separately.

`proof.lean` loads the actual certificate envelope, checks both the expanded
assignment and its distinct shadow declaration, and proves four kernel facts:
live template reads, shadow independence, modular addition and retained-work
copyback. It also executes the seven successful programs under both orders and
checks all three runtime refusals. Structural typed/default tests assert no
unverified numeric expectation.
