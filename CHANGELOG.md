# Changelog

## 0.1.6 — 2026-07-16

### Layout formalization + roadmap

- `docs/ROADMAP.md`: deferred items (∀ roundTrip, coinductive bisim, solanalib bridge)
  and **active** direction (index ↔ byte layout lemmas)
- `ByteLayout` refactored to list prefix-sum `offsetsFrom` / `findOffsetIdx`
- Theorems: `sizeBytes_*`, `byteOffsets_size`, `index_to_byte_to_index`,
  `indexToByte_byteToIndex`, `byte_to_index_to_byte`, `byteOffsets_zero`
- Api: `asmIndexByteRoundtrip`, `asmIndexToByte_byteToIndex`
- ByteBisim: `entry_toBytePc_zero` from layout facts

## 0.1.5 — 2026-07-16

### P0–P2 priority package (round-trip, bisim, size, adequacy, freeze)

- **P0 RoundTrip:** V3-safe opcode witness table (`all_v3_safe_opcodes_have_roundtrip_witness`),
  binImm/ja/lddw batteries, constructor samples; still not a full `∀ encodable → roundTrip` proof
- **P0 ByteBisim:** fuel-bounded list↔byte lockstep suite + outcome agreement; `machine_with_pc_id`
- **P0 divergences:** expanded `vectors.json` (classic/pqr/programs/divergences) + `docs/divergences.md`
- **P1 EncodeSize:** theorems `encodeInstr_size`, `encodeProgram_size` (length = `sizeBytes` / `totalBytes`)
- **P1 Adequacy non-halt:** `steps_runFuel_outOfFuel`, stuck/outOfFuel not-halted, first-step stuck inversion
- **P2:** CounterScenario fuel tuned for faster `native_decide`; `Corpus` module; `docs/API_FREEZE.md`;
  Api exports `asmEncode_size` / `asmV3SafeRoundTripWitnesses`

## 0.1.4 — 2026-07-16

### Byte-PC execution + thicker oracles

- `ByteLayout`: instruction index ↔ byte offset map for a `Program`
- `ByteStep`: `execStepBytes` / `runFuelBytes` (list step under the hood; PC is byte offset)
- Samples: list vs byte halt agreement; redecode + byte run
- `Api.asmStepBytes` / `asmRunBytes`
- Expanded `tools/diff_oracle` classic + PQR vectors

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
