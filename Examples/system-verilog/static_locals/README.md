# Procedural variable lifetimes

The sources exercise IEEE 1800-2023 §6.21/§9.3 through the existing interpreter
and scheduler. Static storage initializes before entry and survives re-entry;
automatic entry creates a fresh value and saved continuations retain it.
See [the contract](../../../docs/sv-procedural-lifetimes.md).

`proof.lean` proves four kernel properties of the actual parsed certificate:
pre-process initialization, entry retention, retained-value increment and modular
four-bit addition for every operand. Its IO receipt checks the extracted source
shapes, executes all eight positive fixtures under both tested orders and checks
all four refusals. The theorems do not certify the frontend in general.

All references below completed with status 0 on 2026-10-20, version 24.03-s004,
top `top`, arguments `-ii_val -abvcoveron -abvrecordcoverall -abvdisableasrtst`.
Keys bind exact source bytes and invocation; source hashes bind the evidence to
the fixtures. Comparisons use complete stdout and require model completion.

| Authored source | Reference key | Source SHA-256 | Model result |
|---|---|---|---|
| [automatic.sv](automatic.sv) | `7deb2ae9ce23b3daa158a048` | `74119694a29fe12d0f61f9f2e4c0e09d218efceba416b4e8bb9dca7940416a78` | MATCH, both orders |
| [capture.sv](capture.sv) | `aab68993bb563b089657e1e8` | `38d0fe5fbef2ae6bfdb267543ddb8978b60f9d31036d8125d04839ee9dfbcda1` | MATCH, both orders |
| [certificate.sv](certificate.sv) | `a474b88404d946bd9c175b3c` | `a30bce69093252b7575e14be45e9f905c8ad55c6d79bf9fdd9f41d0ff3689e04` | MATCH, both orders |
| [default_lifetime.sv](default_lifetime.sv) | `92ad75893d727250b88b982a` | `6e767758354f37fd5dcaf0870316446f4672462fccebd13204749e0019f6ceff` | REFUSE |
| [initializer_effect.sv](initializer_effect.sv) | `d5b996840a9241012d0c6493` | `b86e3915122d0f39b3da881afd30d97dc0e8eae0137934dbf02d0c819411aca2` | REFUSE |
| [initializer_order.sv](initializer_order.sv) | `776555f02dea92c46ced95b5` | `03e197775515f1206d8ca6c2aa92735d698ee6a3c07a7c659cf6bb6e3077132a` | REFUSE |
| [initializer_read.sv](initializer_read.sv) | `255f3bee71bd2fb0fa23be5b` | `b38e50c1ad1551e64dbd459e00b4e9581135bd03d063be3ecbd8ad4c043259d5` | REFUSE |
| [nba.sv](nba.sv) | `c33d70fdad4993c446d887a3` | `ba6b1c518c4b7c5ef49bb492e0c6478805d6cb235468690cafc002eec1f8305e` | MATCH, both orders |
| [preentry.sv](preentry.sv) | `f2acc5a16b42767004a1df2d` | `6e134cef86fa23267206140df38e8b25227a17e73cf4f7200b5b27fb9e162a0b` | MATCH, both orders |
| [reentry.sv](reentry.sv) | `e99e93c829e313a6bd95e3c1` | `fd5c1b3d38f16a2a3ca9ef257b7d1c43d80e0edbd787d9d40d357130e97f1d9b` | MATCH, both orders |
| [shadow.sv](shadow.sv) | `63d03789ee75d95c9c60c270` | `643d3494bd9e12cdadcb5af3a20c07be3753d8cf68c7789ce0e89409dda750d2` | MATCH, both orders |
| [structure.sv](structure.sv) | `2c18aac11282bafbc7d8e496` | `dfca10b91fb1b039b3ca1082fb9122343a1299a3677d753e9b193a749eb0649c` | MATCH, both orders |

`default_lifetime.sv` preserves the unresolved frontend/reference disagreement:
the reference prints `automatic 1 1`, `automatic 2 2`, `automatic 3 3` for the
implicit local in an automatic module. The model refuses this provenance.
The separately qualified explicit `automatic` source prints 3, 6, 9. The other
negative sources require runtime initializer reads, effects or an initialization
order contract; successful reference execution is not model agreement.

The twenty gained corpus rows were separately qualified. Nineteen simulation
rows match full independent transcripts under both orders; the compile-warning
row without `$finish` is HORIZON, with no execution agreement claimed.

| Corpus-relative source | Reference key | Source SHA-256 | Model result |
|---|---|---|---|
| `chapter-12/12.7.1--for-inside-while-inside-for.sv` | `90f24e600be3fc3836da598f` | `eb2dae87aed5fb9ed5f29bb9717af56ba07ca926812119a3a79ba38843596cec` | MATCH, both orders |
| `chapter-12/12.8--break-exits-innermost-loop-only-v4.sv` | `fc004413e707142ffcab20b9` | `fa827abd18a1c9263cf3a0fb159897038b27f07a247eb940527bbd25fee7170d` | MATCH, both orders |
| `chapter-12/12.8.2--break-exits-innermost-nested-loop-only-v3.sv` | `32e1c35a63e0e6a52d7c034f` | `df83a17e42a6f8b87d2bf956b3b2d9cc9d16c79deecba9a18d1aef5227060037` | MATCH, both orders |
| `chapter-12/12.8.2--break-innermost-nested.sv` | `7a94b33ab10d49d2a062cd2a` | `18ff4c8b9d88c93fafe5a3e36748a5eb4e77c1bc38b2957e211a76a23fcdc703` | MATCH, both orders |
| `chapter-23/23.6--hierarchical-named-begin-block-access.sv` | `6aa87225fe15799da4123d79` | `b1a1822215aa4a8346f8fdfcff1c698d728dde0335477a6349651158e23445bc` | MATCH, both orders |
| `chapter-23/23.6--hierarchical-nested-block-scope-v3.sv` | `2aa1c7b186d0525cca11609c` | `100987be8719dc8c68397400e6d3302288fc43eb943419ab80e55d46c8356027` | MATCH, both orders |
| `chapter-23/23.6--named-begin-end-block-hierarchical-scope.sv` | `8a92f3237b828fe602c7ef32` | `0489fdc24ad9dc55a923e68ee91d12a140ccda090d02ffc584ed9cbee569aced` | MATCH, both orders |
| `chapter-3/3.13--named-block-hierarchical-reference.sv` | `9a20e9eb7d294472773a0641` | `6663db8697a2e92256f461dbb6cbfccad4c7b3d6ec97fc30e90dbbab2d255937` | MATCH, both orders |
| `chapter-3/3.13--nested-block-shadow-explicit-outer-reference.sv` | `4a8737d14810c7c5977ffc67` | `8a491d021f8fb8610770de4ded9cf40f1af360a40a4ce6c075dae403765efbb5` | MATCH, both orders |
| `chapter-3/3.13--nested-named-block-hierarchical-reference.sv` | `5d80a5291116449277e17365` | `627f397d2148d370fd9c57d69bb401b7e41786ed30e97aebf08d636d18342d2f` | MATCH, both orders |
| `chapter-3/3.8--escaped-identifier-named-block-label.sv` | `4e7cfcf7c0a8933d2bc63d0c` | `87027d8a8be7b348d47eea1dd1f3571f9cae4dc5a1162a70aaeed067f0686057` | MATCH, both orders |
| `chapter-3/3.8--nested-escaped-identifier-block-hierarchy.sv` | `6efc3655aea48148008662a9` | `43b9d810024ff4f6297980066ce8a7db8844638c548ccf9ce1c6e1ca282447c7` | MATCH, both orders |
| `chapter-6/6.21--automatic-var-in-nested-loop-reinits.sv` | `6c25054f8e747af47f9d992b` | `77d3ca843a7ff62a46dcf56c987161340799a73d8466b4c74fdd5b191727d56b` | MATCH, both orders |
| `chapter-6/6.21--static-init-needs-explicit-keyword.sv` | `f1666f0737a476d93253e692` | `7a914047c259e1333bfab5d60be710586f964994d93ae49a3451170cf86de147` | HORIZON |
| `chapter-7/7.4.1--packed-array-part-select-variable-base.sv` | `b6915182839fa9fb34cc77e1` | `1eeca6466141b63bf6f496149c7fdbf41c05fd3f5b0945116bba35243482f8ea` | MATCH, both orders |
| `chapter-9/9.3.1--sequential-block-escaped-identifier.sv` | `d872ac86417ebe14b5d79e7f` | `e2bd206d9f47da4e741a59d6479e98e01b9a85719c42526f4020d2a88f4dfb13` | MATCH, both orders |
| `chapter-9/9.3.4--named-block-hierarchy-reference-v3.sv` | `ddbdf90d91c264f774d532c9` | `2577c4c30dd999b33c60332de9f5d735cdb6af1834cc75c35649b49fae4542a9` | MATCH, both orders |
| `chapter-9/9.3.4--named-block-local-vars-accessible-hierarchically.sv` | `9d23b7884492e3ad1d6d566c` | `65042cd0ea1ed4e79d3d0615094fbe12afaf581809ede4dec598817fab16ba5c` | MATCH, both orders |
| `chapter-9/9.3.4--named-block-vars-are-static-unique-location.sv` | `d3503bbea8363669b9a0a41e` | `d8f83b2ef7bf039e8882f176e62264f681e9f630b466fd1010bc8d5be245807d` | MATCH, both orders |
| `chapter-9/9.3.5--statement-label-creates-named-block-v3.sv` | `24b1b7c69eefe15fd05e637d` | `ba7cfb15f8fefbd0f6a14dc2ea403c5d82efaef3de70d83c41488af753c4d579` | MATCH, both orders |

Broader paired-model regression telemetry covers all 1,141 changed prior clean
extractions: 1,116 completed pairs, 17 runtime-refusal pairs and eight
input-required loader-refusal pairs, with no differences. It is not independent reference
conformance. All 32 reference receipts, including the four model refusals and
one horizon, were authenticated against their complete outputs and provenance.
