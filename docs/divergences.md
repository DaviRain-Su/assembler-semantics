# Known semantic divergences (assembly layer)

This table documents intentional or historical differences between **this
package**, **blueshift `sbpf` execute**, and **other oracles** (Agave,
solanalib). Integrators should not assume bit-identity across all three.

| Topic | assembler-semantics | blueshift execute | Notes |
|-------|---------------------|-------------------|--------|
| Target arch | **V3 first** (`ofByteV3?`) | V0/V3 options | Jump32 overrides classic PQR bytes under V3 |
| Classic PQR bytes (udiv32, uhmul64, …) | **Not V3-safe** (`encodable = false`) | Opcode exists; **execute often unimplemented** | Prefer SIMD-0174 mnemonics / V3 jump32 |
| PQR ops (lmul/uhmul/sdiv/…) | **Implemented** (SIMD-0174) | Largely **InvalidInstruction** in `execute/*` | Do not diff these against blueshift execute |
| 32-bit add/sub/mul result | Sign-extend to 64 (sbpf classic path) | Same for classic alu32 | V3/SIMD-0174 may zero-extend add32 — we follow blueshift classic for non-PQR |
| `mov32` reg | Sign-extend low 32 (V3 / SIMD-0174 note) | Zero-extend in classic path | Documented divergence |
| `sub*_imm` operand order | `dst - imm` (classic) | Same | SIMD-0174 proposes `imm - dst` for V2+; we stay classic until pinned otherwise |
| Jump offset unit | **Instruction index** (+1 per list instr; lddw one element) | Same in sbpf VM instr vector | Byte-PC view maps via `byteOffsets` |
| Host syscalls | Thin `Dialect` / `hostExec` stubs | Full runtime handlers | Only log/mem/return_data/abort covered |
| Compute units | **Not modeled** | Metered in VM | Gas-free like yul-semantics |
| solanalib.SBPF | Not linked | N/A | Future external diff only; separate instruction AST |

## Differential policy

1. **Safe to diff vs blueshift execute:** classic ALU64/32 (non-PQR), load/store, jumps, internal call/exit, endian.
2. **Lean-only goldens:** PQR, V3 jump32 encoding, host stubs.
3. **Vectors:** `tools/diff_oracle/vectors.json` + `DiffTests.lean` (+ `divergences` section in the JSON).

## Vector buckets (oracle harness)

| Bucket | Purpose |
|--------|---------|
| `classic` | sbpf-style ALU goldens (safe external diff) |
| `pqr` | SIMD-0174 ops (Lean-only until sbpf execute catches up) |
| `programs` | multi-instruction halt traces (mov/add, jeq, lddw, call) |
| `divergences` | machine-readable summary of this table |

## How to extend

When adding an opcode behavior, update this table if it differs from blueshift or
solanalib, and add a `DiffTests` / vector entry in the appropriate bucket.
