# Area C — ISA models: build vs. import

Scope: Sail / sail-riscv, the Sail→Lean backend (cloned and inspected directly,
not just read about), the field of alternative ISA-model efforts, and the
cv32e40p/PULP vendor-extension gap. Everything under "Sail→Lean backend: hands-on
findings" is first-hand (cloned the repos in `/tmp` and read the generated code,
build logs, and CI config myself) rather than abstract-skimmed; everything else is
cited from primary sources (READMEs, papers, the actual `cv32e40p` checkout at
`/home/thomas-ahle/rtl/cv32e40p` already present on this machine).

## 1. Sail and sail-riscv

**Sail** (Armstrong, Bauereiss, Campbell, Reid, Gray, Norton, Mundkur, Wassell,
French, Pulte, Flur, Stark, Krishnaswami, Sewell — *ISA Semantics for ARMv8-A,
RISC-V, and CHERI-MIPS*, POPL/PACMPL 2019) is an imperative, first-order DSL with
lightweight dependent bitvector types, designed to capture vendor pseudocode-style
ISA definitions once and compile them to (a) an executable emulator (OCaml/C) and
(b) definitions in multiple theorem provers (originally Isabelle, HOL4, Coq/Rocq;
Lean added later — see §2). The paper's headline result was large,
validated-against-hardware models of ARMv8-A, RISC-V, and CHERI-MIPS, sufficient to
boot operating systems.

**sail-riscv** (github.com/riscv/sail-riscv, moved from `rems-project` to the
`riscv` org in 2021 when **adopted by RISC-V International**) is the RISC-V
Foundation's own formal spec, referenced directly from the `riscv-isa-manual`
repository (a `sail` branch of the manual embeds the Sail definitions inline as
the normative cross-check). Concretely, from the checked-out source
(`/tmp/sail-riscv-sparse`, sparse-checked from `riscv/sail-riscv@master`):

- **Coverage**: a single Sail source models RV32 *and* RV64 uniformly — `xlen` is
  a config parameter (`config/config.json.in`: `"base": {"xlen": @CONFIG__BASE__XLEN@,
  "E": false, ...}`), not two duplicated models. RV32IMC is a subset selection of
  the same model (disable everything but I/M/C via the JSON config), not a
  separate build. Compressed (`C`), M, A, F/D, and essentially every ratified
  extension through Zk*/Zv*(vector)/Zc* are present; the model is genuinely
  broader than CV32E40P needs (it also carries the whole vector and scalar-crypto
  extension surface, S-mode/hypervisor state, PMP, etc.).
- **WARL/CSR handling**: not just declared abstractly — every WARL/WLRL field has
  a concrete `legalize_<csr>` function that masks/coerces a written value to the
  legal set on `write_CSR`. E.g. `legalize_misa`, `legalize_mstatus`,
  `legalize_tvec` in `sys_regs.sail` (mirrored 1:1 in the generated
  `SysRegs.lean`, see §2) — `legalize_mstatus` alone is a ~50-line nested chain
  of `_update_Mstatus_<field>` calls, each gated by `currentlyEnabled Ext_S` /
  `Ext_U` / `hartSupports Ext_Zicfilp` etc., i.e. WARL legality is *config- and
  extension-conditional*, which is exactly the shape cv32e40p needs (M/U-only,
  most S-mode fields tied off).
- **Interrupt semantics**: `sys_control.sail` (`SysControl.lean`:
  `exception_delegatee`, `getPendingSet`, `dispatchInterrupt`, `trap_handler`) —
  the standard non-CLIC mip/mie fixed-priority scheme from privileged-spec
  §3.1.9. No CLIC/Smclic support is present, which happens to match cv32e40p
  (which also implements only the basic, non-CLIC scheme — see §4).
- **Extension mechanism**: a documented process (`doc/AddingExtensions.md`) for
  adding a self-contained extension — new `model/extension/<ext>/*.sail` files
  for types/utils/instructions, an entry in `extensions.sail`, a `"supported"`
  flag in the JSON config, `is_CSR_accessible`/`read_CSR`/`write_CSR` clauses for
  new CSRs, and a `currentlyEnabled` gate (with a `sys_enable_experimental_extensions()`
  escape hatch for unratified work). This is the same mechanism used upstream for
  every non-trivial standard extension (vector, crypto, bit-manip), so it is a
  real, exercised pattern — see §4 for why it doesn't fully cover cv32e40p's
  PULP extensions.
- **Spec version tracked**: sail-riscv tracks the *current* ratified privileged
  spec (post-20211203, with active branches for newer ratifications like
  Smcsrind) — this is the important mismatch against cv32e40p; see §4.
- **License/provenance**: BSD 2-clause (confirmed at
  `github.com/riscv/sail-riscv/blob/master/LICENCE`), original authorship SRI
  International + University of Cambridge/Edinburgh (REMS project), now formally
  governed by RISC-V International. The whole REMS ecosystem (sail compiler
  itself, isla, asl_to_sail) is consistently BSD-2-Clause. Clean to vendor
  bit-layout tables, constants, or transliterate short functions with
  attribution.

## 2. The Sail→Lean backend: hands-on findings

I cloned and inspected the actual artifacts rather than relying on descriptions:

```
/tmp/sail-riscv-lean   (github.com/opencompl/sail-riscv-lean)
/tmp/lean-sail         (github.com/rems-project/lean-sail, tag v5 — the shared runtime library)
/tmp/sail-riscv-sparse (github.com/riscv/sail-riscv, sparse checkout of config/doc/model dirs)
```

**Who's doing this, and why.** Developed by Tobias Grosser and Leo Stefanesco
(Cambridge), James Parker, Lee Newcomb, Ben Selfridge, Ben Hamlin (Galois Inc.),
Jakob von Raumer and Ryan Lahfa (LindyLabs), with Peter Sewell, Alasdair
Armstrong, and Brian Campbell (the original Sail/sail-riscv authors) consulting.
**Funded by the Ethereum Foundation's Verified zkEVM project** — i.e. the
motivating use case is proving a RISC-V-based zkVM circuit refines the ISA
spec, which is structurally the same problem shape as ours (implementation ⊑
ISA-level golden model). The same contributors are upstreaming improvements to
Lean's core `BitVec` library (shared with std4/mathlib) as part of this effort.

**Maturity — concrete, not asserted.** The repo has a `.github/workflows` cron
job (`schedule: "0 6 * * *"`) that **regenerates the Lean model from sail-riscv
master daily** and commits the result; the checkout I have is from *today's* run
(commit `0742125`, message "Update main to output generated at"). `build_log.txt`
(committed, real CI output) shows `lake build` completing all 135 targets:
`Build completed successfully (135 jobs)` — the whole translation genuinely
type-checks against current Lean/current sail-riscv, continuously, not as a
one-off snapshot. Stats: **175,768 lines, 4,779 `def`s, 206 inductives, 185
abbreviations**, 160 `.lean` files.

**Is it executable?** No — the README says so explicitly ("neither executable
nor polished in any way") and I did not find a way to `#eval` an instruction
step; `noncomputable section` wraps every file. The underlying runtime
(`lean-sail`, `Sail/ConcurrencyInterfaceV1.lean`) itself *is* a concrete,
computable `EStateM`-based state monad (`SequentialState` = register map +
byte-addressed memory `HashMap` + a `ChoiceSource`-threaded oracle state for
`undefined_*` values — **structurally identical to our own `ScheduleOracle`/
`RandOracle` design**: nondeterminism is an explicit oracle parameter, not
hidden), so the *runtime* is not the obstacle; the non-computability is coming
from how Sail's general-recursion / pattern-match translation is encoded for
some subset of the 4,779 generated definitions (I did not fully diagnose which,
given time budget — flagged as an open question, not a settled one).

**Term style — read directly, not summarized.** `execute_RTYPE` in
`InstsEnd.lean` (the RV32I `ADD`/`SUB`/`AND`/... family):

```lean
def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  (wX_bits rd
    (← do
      match op with
      | .ADD => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))
      | .SLT => (pure (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))))
      ...
      | .SUB => (pure ((← (rX_bits rs1)) - (← (rX_bits rs2))))))
  (pure RETIRE_SUCCESS)
```

This individual definition is *fine* — compact, readable, monadic in an
unsurprising way. But two costs show up at scale, both directly load-bearing for
our "prover-readable goals" constraint:

1. **Per-file boilerplate.** Every file that touches instruction semantics opens
   ~130 namespaces before a single real definition (`open zvk_vsm4r_funct6`,
   `open wxfunct6`, `open vregidx`, ... — one per instruction-format type across
   the *entire* ISA, because Sail's `Functions` namespace is global and the
   backend re-opens everything per file rather than scoping per-instruction).
   `BaseInsts.lean` and `ZicsrTypes.lean` both start with the *same* ~130-line
   `open` block despite touching disjoint instruction families.
2. **File size / decode nesting.** `InstsEnd.lean` — the file holding
   `execute_RTYPE` above — is **72,378 lines** in one file, because it's the
   single dispatch point for every extension's decode *and* execute clauses
   (base I, M, A, F/D, Zb*, Zk*, the entire V extension, scalar crypto...). The
   generated `encdec_*` decode function nests one `match` arm per instruction
   inside the next as it walks the opcode/funct3/funct7 fields, so indentation
   at instruction #200-or-so in the table is already >100 columns deep (e.g.
   line 557 of `InstsEnd.lean`, decoding `RTYPE ADD`, is indented to column
   ~98). This is a direct, measured cost against goal legibility, not a
   hypothetical one — and it scales with *the whole ISA the source model
   supports*, most of which (V, crypto, S-mode) cv32e40p doesn't implement and
   we'd have no proof obligations about.
3. **CSR update chains.** `legalize_mstatus` (SysRegs.lean:1012) is a single
   50-line expression of literally nested `_update_Mstatus_MPELP (_update_Mstatus_SPELP
   (_update_Mstatus_TSR (... 15 fields deep ...)))` — correct, but exactly the
   shape our spec surface's design explicitly avoids (deep nesting instead of
   named intermediate steps a prover can pattern-match on).

**Axioms — and they're the honest kind.** Exactly one file,
`RiscvExtras.lean`, carries `axiom` declarations (~40 of them), and every one is
a genuine external boundary that Sail's own `extern` mechanism declares in the
*source* spec, not a shortcut invented by the Lean backend: terminal I/O
(`plat_term_write`/`plat_term_read`), the LR/SC reservation-set primitives
(`load_reservation`/`match_reservation`/`cancel_reservation`), the hardware RNG
hook (`get_16_random_bits`), an experimental-extension gate, and the IEEE‑754
softfloat operations (`riscv_f16Add` … `riscv_f64Sqrt`, format conversions) that
upstream Sail itself implements by calling out to a C softfloat library rather
than defining in Sail. This is structurally identical to our own DPI
axiom-contract stance (gallery example 9) — a genuinely good sign, not a
compromise specific to the Lean backend.

**Bottom line on the backend itself**: it is real, live (daily-regenerated,
CI-verified), funded, and produced by credible people including some of Sail's
original authors — this is not a toy side-project. But by its own maintainers'
description it is "work-in-progress," not executable, and — independent of that
caveat — its *style* (mechanical per-file namespace floods, monolithic
72K-line decode files spanning extensions we don't need, deeply nested CSR
update chains) is a poor match for "prover-readable goals" if imported whole.
sail-riscv itself, in its own upstream README, calls its Lean output
"experimental," alongside Isabelle and Rocq as the more mature targets.

## 3. Alternatives surveyed

| Effort | Language/host | Status | Relevant angle |
|---|---|---|---|
| **Forvis** (Rishiyur Nikhil, ex-Bluespec) | "extremely elementary" Haskell | One of several 2019-era entrants to the RISC-V Foundation's ISA-Formal-Spec comparison (`riscvarchive/ISA_Formal_Spec_Public_Review`); sequential one-instruction-at-a-time interpreter. Sail has since become the Foundation's adopted model — Forvis is a historical alternative, not currently the community's reference. |
| **GRIFT** (Galois, BESSPIN suite) | dependently-typed GHC Haskell | Represents instruction semantics as **symbolic bitvector expressions**, not direct state-machine functions — an SMT-friendly representation choice worth noting on its own merits (closer to what a `bv_decide`-style backend wants), distinct from Sail/Forvis's direct-interpreter style. Also part of the 2019 Foundation review round; not evidence it's currently maintained. |
| **ASL** (Arm's own spec language) | Arm-internal + open `asl-translator`/`asl_to_sail` tooling | Arm's ground truth for A/R/M-profile, used to test both Verilog and silicon. Not RISC-V-relevant directly, but the ASL→Sail translation (Reid et al.) is precedent for "translate an authoritative-but-foreign spec language into Sail" — not directly applicable since cv32e40p's PULP extensions have no ASL-equivalent source to translate from. |
| **L3** (Fox & Myreen, 2010) | HOL4-embedded DSL | Sail's acknowledged predecessor; used for CakeML's ARM backend and CHERI-MIPS proofs. Superseded by Sail for new work per the POPL'19 paper's own framing. |
| **riscv-coq** (Samuel Gruetter, MIT-PLV; a.k.a. "riscv-semantics"/"riscv-plv") | Coq/Rocq, hand-written | *A Multipurpose Formal RISC-V Specification Without Creating New Tools* — deliberately hand-written directly in the target prover rather than generated, specifically to stay usable inside downstream Coq proofs (bedrock2 compiler correctness, and `bedrock2/processor` proves it matches Kami's hardware-centric RV32I spec). This is the closest existing precedent to "hand-write a small, orthogonal ISA model directly in your proof assistant for legibility," in a different prover. |
| **Kami RV32** (MIT-PLV, ICFP'17 + follow-ups) | Coq, labeled-transition-system hardware DSL | Already reviewed per your prior-adoptions list for its *sequentialization/discipline* metatheory — noting here only the RV32 ISA-model angle: its RISC-V case study is proved equivalent to riscv-coq's ISA-level spec, i.e. two independently-styled Coq artifacts (hardware-centric vs. software-centric) cross-checked against each other rather than one being "the" import target. |
| **LNSym** (AWS/Lean FRO, `leanprover/LNSym`) | Lean 4, **hand-written** | Not RISC-V (it's Armv8), but the most directly relevant precedent inside our own toolchain: AWS hand-wrote Arm instruction semantics *directly in Lean* (not generated from ASL) specifically to get a symbolic simulator with conformance-tested, idiomatic, executable specs for crypto-primitive verification. Confirms hand-writing-in-Lean is a proven, currently-used path for exactly this kind of hardware/software-boundary verification at a company with real resources, not a purely theoretical alternative to importing. |

**A second, independent signal inside the Lean community itself**: a
leanprover-community Zulip thread ("RISC-V ISA in Lean," #236449-Program-verification)
shows a *third*, unrelated hand-written RISC-V-in-Lean effort (user "SnowFox,"
guided by Mario Carneiro, who previously built an x86-in-Lean model). Their
first design — one inductive constructor per opcode (63 variants) — hit real
performance problems (`no_confusion` generation is quadratic in Lean, so lots of
constructors is directly costly), and Carneiro's fix was explicitly a
legibility move: "bucketing based on format shape is the obvious thing to do" —
collapsing to five semantic variants (branch/jump/arithmetic/load/store) instead
of mirroring the opcode table 1:1, on the principle that "it's very important
that a formalization of the spec makes as much orthogonality explicit as
possible." This is an independent confirmation, from people with no stake in
our project, that literal/generated opcode-by-opcode encodings (which is what
Sail's decode tree *is*, by construction — see the 72K-line `InstsEnd.lean`
above) fight the prover, and that a hand-designed orthogonal AST is the
community's own remedy.

## 4. cv32e40p's PULP extensions vs. the standard model

Checked directly against the checkout at `/home/thomas-ahle/rtl/cv32e40p`:

- **Version skew is real and material, not hypothetical.** `docs/source/intro.rst`
  states plainly: *"CV32E40P implements the Machine ISA version 1.11"* (RISC-V
  privileged spec, doc version **20190608**-Base-Ratified) and the unprivileged
  ISA per doc version **20191213**. Mainline sail-riscv tracks the *current*
  ratified privileged spec (20211203 and later amendments — e.g. active
  `Smcsrind` branches). Between those versions several WARL/WLRL
  classifications changed (per the RISC-V spec's own 20211203 changelog:
  `mstatus` moved from WLRL to WARL; `pmpaddr`/`pmpcfg` moved from WIRI to
  WARL). This means `legalize_mstatus` et al. as found in current sail-riscv
  cannot be assumed correct-by-import for cv32e40p's actually-implemented
  behavior — it needs a real audit against the 1.11 text and against
  `cv32e40p_cs_registers.sv` (already flagged in our own census as the single
  highest-`Unsupported`-count file: 88 nodes, 33 params, 8 for/13 if), not an
  assumption of compatibility.
- **Ordinary custom instructions fit the extension mechanism.** SIMD
  dot-products, MAC, half-word multiply-with-shift, post-increment load/store —
  these are self-contained new opcodes in the RISC-V-reserved `custom-0`/`custom-1`
  encoding space, i.e. exactly what `doc/AddingExtensions.md`'s pattern (new
  instruction file + decode/execute clauses + config gate) is for. No encoding
  conflict risk with the standard extensions sail-riscv already models.
- **Hardware loops (HWLoop) do *not* fit that mechanism.** Per
  `docs/source/corev_hw_loop.rst`: HWLoop is not a discrete instruction's
  semantics but a **persistent, CSR-driven implicit fetch-time PC redirect** —
  while `lpcountX > 0`, every fetch reaching `PC == lpendX - 4` branches back to
  `lpstartX` and decrements `lpcountX`, with zero-cycle overhead, entirely
  outside normal instruction execution. It has intricate, explicitly documented
  interaction with interrupts/debug (a whole section of the manual walks
  through the required `MEPC`/`lpcountX` save-restore sequence an interrupt
  handler must perform). Sail's execution model is fundamentally "decode one
  instruction, run its `execute_*` clause, compute the next PC" — HWLoop
  requires modifying the **fetch/step function itself**, a core-model change,
  not a leaf extension file in the documented sense. Nothing in the surveyed
  literature (Sail, GRIFT, Forvis, riscv-coq, Kami) has PULP/Xpulp coverage; this
  is greenfield modeling work regardless of the Area-C verdict below.

## Answers to the three key questions

**(1) Build vs. import, and the goal-legibility cost.** **Import is not
viable as a source of theorem-facing Lean terms**, on the backend's *own*
admission (non-executable, "work-in-progress") and independent of that, on
legibility grounds we can measure directly: 175K generated lines dominated by
~130-line `open` floods per file, a 72K-line single decode/execute file mixing
in the entire V/crypto/S-mode surface cv32e40p doesn't have, and 50-line
single-expression CSR update chains — the opposite of the shallow, named,
port/state-only spec surface `docs/sv-spec-surface.md` commits us to. **Build**
is the right call: hand-write a small, orthogonal RV32IMC + M/U-mode-only Lean
ISA model in our own idiom (mirroring the SnowFox/Carneiro semantic-bucketing
lesson and the LNSym hand-written-in-Lean precedent), sized to exactly what
cv32e40p implements rather than the full ratified ISA. The correct role for
sail-riscv is as a **validation oracle, not a term source**: (a) differential-test
our hand-written Lean model against the Sail C/OCaml emulator's concrete traces,
the same pattern already used for the SV lane against Xcelium; (b)
**transliterate**, not import, the small number of fiddly bit-exact tables that
are genuinely error-prone to re-derive from prose — CSR bit-field layouts,
exception-code numbering, interrupt priority ordering — reading them out of the
short, readable Sail *source* functions (e.g. `legalize_tvec` is ~15 lines and
perfectly legible in isolation) rather than the generated Lean.
**Recommendation: build, validate against Sail, harvest bit-tables by hand.**

**(2) CSR/WARL/interrupt semantics.** sail-riscv expresses these exactly the way
we'd want to imitate: WARL fields are concrete `legalize_<csr> : old → written →
SailM legal` functions gated by `currentlyEnabled <ext>` (config-conditional,
not hardcoded), and interrupt dispatch is a priority-ordered
`getPendingSet`/`dispatchInterrupt` pair over `mip`/`mie` with a separate
`trap_handler` for vectoring/delegation — the standard non-CLIC scheme, which
matches cv32e40p. The *shape* of these functions is worth copying into our
hand-written model (small, named, config-gated helper functions per CSR/per
trap-dispatch-step) even though the specific field values must be re-derived
for the 1.11 spec cv32e40p actually implements, not lifted verbatim from
current sail-riscv.

**(3) Licensing/provenance.** Clean. sail-riscv (and the whole REMS ecosystem:
sail compiler, isla, asl_to_sail) is BSD-2-Clause, and sail-riscv is formally
governed/adopted by RISC-V International — safe to vendor constants, bit
layouts, or transliterated short functions with attribution. One gap: I could
not confirm a `LICENSE` file in the `lean-sail` runtime library's `v5` tag from
a shallow clone (its sibling repos are uniformly BSD-2-Clause, so this is very
likely the same, but should be confirmed with the maintainers before vendoring
anything from it specifically) — moot under the "build, validate, harvest
tables" recommendation above, since we would not be importing `lean-sail` or
its generated output as a dependency.

## Sources

- Armstrong et al., *ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS*, POPL/PACMPL 2019 — https://www.cl.cam.ac.uk/~pes20/sail/popl2019.html
- sail-riscv (RISC-V International) — https://github.com/riscv/sail-riscv , README, `doc/AddingExtensions.md`, `config/config.json.in`, `LICENCE` (all read from a local sparse checkout of master)
- sail-riscv-lean — https://github.com/opencompl/sail-riscv-lean (cloned to `/tmp/sail-riscv-lean`, README, `build_log.txt`, `.github/workflows/`, `LeanRV64D/*.lean` read directly)
- lean-sail runtime — https://github.com/rems-project/lean-sail (cloned to `/tmp/lean-sail`, tag v5, `Sail/ConcurrencyInterfaceV1.lean` read directly)
- Setting up SAIL for porting to Lean — https://pixel-druid.com/articles/setting-up-sail-for-porting-to-lean (fetched; turned out to document the Coq path, not Lean — noted as a dead end, not cited for Lean claims)
- Forvis — https://github.com/rsnikhil/Forvis_RISCV-ISA-Spec
- GRIFT — https://github.com/GaloisInc/grift , *GRIFT: A richly-typed, deeply-embedded RISC-V semantics written in Haskell*, SpISA'19 — https://www.cl.cam.ac.uk/~jrh13/spisa19/paper_10.pdf
- ASL — https://alastairreid.github.io/RelatedWork/notes/asl/ ; asl-translator — https://github.com/GaloisInc/asl-translator
- L3 / *Taming an Authoritative Armv8 ISA Specification*, ITP 2022 — https://cakeml.org/itp22-armv8.pdf
- riscv-coq / *A Multipurpose Formal RISC-V Specification Without Creating New Tools* — https://people.csail.mit.edu/bthom/riscv-spec.pdf , https://github.com/mit-plv/riscv-semantics
- Kami — https://github.com/mit-plv/kami , ICFP'17 paper — http://plv.csail.mit.edu/kami/papers/icfp17.pdf
- LNSym — https://github.com/leanprover/LNSym
- leanprover-community Zulip, "RISC-V ISA in Lean" — https://leanprover-community.github.io/archive/stream/236449-Program-verification/topic/RISC-V.20ISA.20in.20Lean.html
- cv32e40p — local checkout `/home/thomas-ahle/rtl/cv32e40p`: `docs/source/intro.rst`, `docs/source/exceptions_interrupts.rst`, `docs/source/corev_hw_loop.rst`, `rtl/cv32e40p_int_controller.sv`
- `docs/cv32e40p-coverage.md` and `docs/DESIGN.md` (this repo) for our own extraction-coverage baseline and cross-cutting design principles
