# Roadmap (assembly layer)

This package is the **sBPF ISA / encode brick** (see `SCOPE.md`). Below is what is
**done enough for integrators**, what is **intentionally deferred**, and what we
work on next without drifting off-scope.

## Done enough for current consumers

| Area | Status |
|------|--------|
| L2 `Instr` / `Program`, L4 `Step` / `runFuel` | usable |
| `runFuel` ↔ `Steps` / `Run` adequacy (halt + non-halt basics) | theorems |
| V3 encode/decode + `sameExec` / sample + **V3-safe witness** round-trip | certified suite |
| `encodeInstr_size` / `encodeProgram_size` | theorems |
| Byte-PC view (`ByteLayout` / `ByteStep`) + computational list↔byte bisim | suite |
| Stable `Api` (`asm*`) + freeze policy | `API_FREEZE.md` |
| Oracle vectors + divergence notes | `divergences.md`, `tools/diff_oracle/` |

## Intentionally deferred (valuable, not blocking)

These stay on the backlog until a real consumer pain appears. They are **not**
required to call this package “usable” for ProofForge L2 handoff.

### 1. Full `∀ i, encodable i → roundTripSameExec i`

- **Why valuable:** ironclad encode/decode for every legal field combination.
- **Why deferred:** needs large op-class case analysis; **witness table + batteries**
  already cover the practical integrator surface.
- **Trigger to start:** a real bug or integration failure where a concrete
  encodable instruction fails round-trip, or a consumer needs the ∀ statement
  in a larger proof.
- **Cheaper intermediate:** prove round-trip per high-traffic class
  (`binImm`, `binReg`, `jump*`, `lddw`, `exit`) only.

### 2. Coinductive / fuel-∀ list↔byte bisimulation

- **Why valuable:** shows byte-PC API is observationally the same machine for
  arbitrary programs and fuel.
- **Why deferred:** `execStepBytes` is **definitionally** list-step + PC convert;
  computational bisim suite already covers jumps / `lddw` / call.
- **Trigger to start:** a stable consumer that **only** has bytecode (no list
  `Program`) and needs a proof, not just tests.
- **Cheaper intermediate (preferred next):** formal **layout** facts —
  `byteOffsets` length, strict increase, **index ↔ byte invertibility** at
  instruction starts. That unblocks simulation lemmas without full coinduction.

### 3. solanalib (or Agave) bridge in this repo

- **Why valuable:** second external oracle; catches real divergences.
- **Why deferred / external:** out of **this** package’s ownership; AST and
  dependency churn belong in ProofForge or a dedicated diff harness.
- **Here we keep:** `docs/divergences.md` + `vectors.json` as the contract.
- **Trigger to start:** release policy requires multi-oracle CI, or sbpf alone is
  insufficient for a disputed opcode.

## Active direction (on-scope, high leverage)

**Priority:** L3↔L4 layout formalization — *meaningful, not off-course*.

### Landed (0.1.6)

1. Proof-friendly `offsetsFrom` / `findOffsetIdx` (list prefix-sum; no `Id.run`).
2. Lemmas in `ByteLayout`:
   - `sizeBytes ∈ {8,16}`, `0 < sizeBytes`, `8 ≤ sizeBytes`
   - `byteOffsets.size = P.size`, `byteOffsets_zero`
   - **`index_to_byte_to_index`** / `indexToByte_byteToIndex`
   - **`byte_to_index_to_byte`** at instruction starts
3. Api: `asmIndexByteRoundtrip`, `asmIndexToByte_byteToIndex`
4. ByteBisim: `toBytePc_pc0` / `entry_toBytePc_zero` from layout facts

### Next small steps (still on-scope)

1. One-step `execStepBytes` sim under alignment (use layout round-trip).
2. Strict mono of `offsetsFrom` as a named theorem (used inside round-trip already).
3. Keep expanding **safe-to-diff** classic vectors; keep PQR Lean-only.

## Out of direction (still out of scope)

- Text `.s` parser, ELF, full compiler IR→sBPF proofs, full CPI/account model.
  See `SCOPE.md`.

## Suggested order of attack

```text
layout index↔byte lemmas     ← now
    │
    ├─► (optional) one-step execStepBytes sim under alignment
    │
    ├─► on demand: per-class roundTrip theorems
    │
    └─► only if bytecode-only consumer: multi-step/coinductive bisim

solanalib bridge  →  external harness, not this repo’s core
∀ encodable roundTrip  →  after layout + any real encode bug
```

## Version note

Track shipped slices in `CHANGELOG.md`. This file is planning intent, not a
semver promise.
