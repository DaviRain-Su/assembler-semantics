# assembler-semantics

Formal **assembly-layer** semantics for **sBPF** (Solana BPF) in Lean 4.

**Scope (locked):** resolved instructions (L2), encode/decode (L3), small-step
execution (L4), thin host dialect. **Not** text parsers, ELF linkers, or
high-level compilers—those combine with this package via
[`SbpfSemantics.Api`](./SbpfSemantics/Api.lean).

See [`docs/SCOPE.md`](./docs/SCOPE.md) · [`DESIGN.md`](./DESIGN.md).

Executable reference: [blueshift-gg/sbpf](https://github.com/blueshift-gg/sbpf)
(instruction execute/encode as oracle).

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
| `Encode` / `WellFormed` / `EncodePreserve` / `EncodeSem` | encode/decode, WF, round-trip + exec preserve |
| `Machine` | Registers, PC, memory, call stack |
| `Alu` | Classic ALU + SIMD-0174 PQR |
| `Dialect` / `Host` | Syscall hosts (`closed` / `noop` / `stub` / `host`) |
| `Step` | Single-step exec + relational `Step` |
| `Run` / `Interp` | Fuel multi-step runner |
| `Determinism` / `Adequacy` | Meta-theory (halt + non-halt adequacy) |
| `EncodeSize` / `RoundTrip` / `ByteBisim` | encode length, V3 witnesses, list↔byte PC |
| `Corpus` | hand-written L2 regression programs |
| `Examples` / `DiffTests` | `native_decide` goldens vs sbpf traces |

See also:

- [`docs/SCOPE.md`](./docs/SCOPE.md) — locked assembly-layer scope
- [`docs/ROADMAP.md`](./docs/ROADMAP.md) — deferred work vs next layout focus
- [`docs/API_FREEZE.md`](./docs/API_FREEZE.md) — stable `asm*` surface
- [`docs/divergences.md`](./docs/divergences.md) — Lean vs sbpf / solanalib diffs
- [`docs/for-proof-forge-consumers.md`](./docs/for-proof-forge-consumers.md) — **what PF needs / how Lean 拼汇编 fits**
- [`docs/proof-forge-interface.md`](./docs/proof-forge-interface.md) — stable API surface
- [`docs/diff-oracle.md`](./docs/diff-oracle.md) and [`tools/diff_oracle/`](./tools/diff_oracle/)

### Integrators (any package)

```lean
import SbpfSemantics.Api
open SbpfSemantics
-- asmRun / asmEncode / asmStep / Observation / asmDefaultHost
-- legacy aliases: pfRun, pfEncode, …
```

## What reuses sbpf vs what is rewritten in Lean

| Reuse as oracle / spec | Rewrite in Lean |
|------------------------|-----------------|
| Opcode table & execute sources | Opcode, Step, Machine |
| Assembler fixtures & VM runs | (differential tests later) |
| Parser, macros, ELF emit | **not** Phase 1 |

## Phase 1 status

**Complete** for the scoped deliverable: sBPF ISA semantics + encoding + host
stubs + ProofForge observation API + Counter L2 scenarios. See `CHANGELOG.md`.

```bash
lake build
python3 tools/diff_oracle/check_vectors.py
```

## License

Apache-2.0 (see [`LICENSE`](./LICENSE)).
