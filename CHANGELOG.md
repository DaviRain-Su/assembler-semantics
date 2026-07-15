# Changelog

## 0.1.0 — 2026-07-16

### Phase 1 complete (ISA semantics foundation)

- **L2/L3/L4:** Opcode (V3), Instr, Encode/decode, Machine, small-step `Step`, fuel `runFuel` / `interp`
- **ALU:** classic ops (blueshift execute) + SIMD-0174 PQR
- **Host:** log stubs, abort-halt, memcpy/memmove/memset/memcmp, set/get return data
- **Meta:** step determinism, `runFuel` halt invariant, encode semantic goldens
- **ProofForge bridge:** `Api`, `Observation`, `AccountLayout`, `CounterScenario`, interface contract
- **Tooling:** `tools/diff_oracle` vectors + CI workflow

### Not in this release

- Full ELF / pest assembler
- Universal encode ∀-preservation proof
- Complete Solana account/CPI model
- Agave binary compatibility certificate
