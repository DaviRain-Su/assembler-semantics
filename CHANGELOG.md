# Changelog

## 0.1.3 — 2026-07-16

### Assembly-layer lock-in + adequacy

- `docs/SCOPE.md`: explicit in/out of scope; integration handoff at `Array Instr`
- Full `runFuel` ↔ `Steps` / `Run` adequacy (`runFuel_halted_steps`, `steps_runFuel_halted`, …)
- `Api`: stable `asm*` names for integrators; keep `pf*` aliases
- DESIGN/README: this package = ISA brick only (not compiler, not ELF)

## 0.1.2 — 2026-07-16

### Meta-theory + consumer docs

- `SameExec.lean`: general theorem `sameExec_execInstr` (`sameExec i j → execInstr equal`)
  via `forExec` projection and `execInstr_forExec`
- `docs/for-proof-forge-consumers.md`: product pipeline (Plan→AstNode→.s→sbpf→ELF) vs
  this package’s L2/L3/L4 role; what Lean needs to “拼汇编”

## 0.1.1 — 2026-07-16

### Encode / well-formed preservation

- `WellFormed`: operand shape + `Instr.encodable` (V3-safe, no host name, imm fits i32 field)
- `EncodePreserve`: `sameExec`, `roundTripSameExec`, sample suite across op classes
- Closed-world `execInstr` agreement after `decodeEncode?` (batch + program redecode)
- Documents that decode is not bit-identical (fills unused regs/offs); equality is execution-relevant

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
