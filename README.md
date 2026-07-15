# assembler-semantics

Formal semantics for **sBPF** (Solana BPF) in Lean 4, methodologically aligned
with [powdr-labs/yul-semantics](https://github.com/powdr-labs/yul-semantics).

This repository defines **ISA semantics + instruction encoding**. It is the
foundation for a future verified assembler. The executable reference
implementation is [blueshift-gg/sbpf](https://github.com/blueshift-gg/sbpf).

See [`DESIGN.md`](./DESIGN.md) for scope, L0–L5 layering, V3 encoding notes, and
what is deliberately **not** formalized (parser, ELF packaging, full runtime).

## Design in short

- **Ground truth:** small-step execution of *resolved* instructions (`Step` /
  `execStep`), not `.s` text parsing.
- **Words:** `BitVec 64` registers; memory map matches sbpf VM regions.
- **Compute units:** not modeled (Phase 1).
- **Syscalls:** abstract `Dialect` (open world); closed dialect leaves them stuck.
- **Assembler tool:** stays in Rust as an oracle; Lean owns meaning of instructions.

## Building

Requires the toolchain in [`lean-toolchain`](./lean-toolchain) ([elan](https://github.com/leanprover/elan)).

```sh
lake build
```

No Mathlib dependency for the core skeleton (faster cold builds).

## Layout

| Module | Role |
|--------|------|
| `Opcode` | Opcode enum, V3 byte maps, op classes |
| `Instr` | Resolved instruction AST + program |
| `Encode` / `EncodeLemmas` | encode/decode + V3 round-trip facts |
| `Machine` | Registers, PC, memory, call stack |
| `Alu` | Classic ALU + SIMD-0174 PQR |
| `Dialect` | Syscall relation (`closed` / `noop` / `stub`) |
| `Step` | Single-step exec + relational `Step` |
| `Run` / `Interp` | Fuel multi-step runner |
| `Determinism` / `Adequacy` | Meta-theory (core lemmas) |
| `Examples` / `DiffTests` | `native_decide` goldens vs sbpf traces |

See also [`docs/diff-oracle.md`](./docs/diff-oracle.md).

## What reuses sbpf vs what is rewritten in Lean

| Reuse as oracle / spec | Rewrite in Lean |
|------------------------|-----------------|
| Opcode table & execute sources | Opcode, Step, Machine |
| Assembler fixtures & VM runs | (differential tests later) |
| Parser, macros, ELF emit | **not** Phase 1 |

## License

TBD (sbpf is Apache-2.0 / MIT; yul-semantics is Apache-2.0).
