# RV differential oracle: sail-riscv C emulator (pinned prebuilt binary)

`harness/rv/diff_test.py` validates `LeanModels/Rv/**` (the RV32IMC+M-mode
ISA model) differentially against the **sail-riscv C emulator** — the RISC-V
golden model (github.com/riscv/sail-riscv, BSD-2-Clause, RISC-V
International). Per `docs/litreview/SYNTHESIS.md`, sail is used as a
*validation oracle only*, never as a term source.

This directory holds the pinned prebuilt release binary (gitignored, like
the OpenVAF checkout under `extractors/veriloga/`). To (re)provision:

```sh
cd tools/rv-oracle
curl -sLO https://github.com/riscv/sail-riscv/releases/download/0.13.1/sail-riscv-Linux-x86_64.tar.gz
tar xzf sail-riscv-Linux-x86_64.tar.gz
./sail-riscv-Linux-x86_64/bin/sail_riscv_sim --version   # expect 0.13.1
```

`tools/ci.sh` skips the `rv-harness` step when the binary is absent
(infrastructure absence, not evidence of divergence). A different location
can be pointed to with `RV_SAIL_SIM=/path/to/sail_riscv_sim`.

The emulator runs with `--rv32 --config-override
harness/rv/sail_rv32imc_override.json`, which scopes it to exactly the
model's fragment: `rv32imc_zicsr_zifencei`, machine mode only, privileged
spec v1.11, PMP absent, misaligned data access allowed. The known WARL
scope divergences between sail's choices and the CV32E40P RTL choices the
model implements are documented in `docs/rv-model.md`.
