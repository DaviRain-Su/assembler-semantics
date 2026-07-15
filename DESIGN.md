# sBPF Semantics — Design

This repository defines a formal semantics for **sBPF** (Solana BPF) in Lean 4,
following the methodological template of
[powdr-labs/yul-semantics](https://github.com/powdr-labs/yul-semantics)
and aligned with the *target* role of
[powdr-labs/evm-semantics](https://github.com/powdr-labs/evm-semantics)
(not `yul-compiler`).

## Positioning (locked)

**We only perfect the assembly / ISA layer** so other systems can combine with us:

| We own | We do **not** own |
|--------|-------------------|
| L2 resolved `Instr` / `Program` | L0 `.s` parse, macros |
| L3 encode/decode (V3) | L1 label AST / pretty-print |
| L4 small-step + fuel run + adequacy | High-level IR / DSL / Plan |
| Thin L5 host dialect interface | Full Solana runtime / CPI / ELF |

Integrators (e.g. ProofForge) lower **to** `Array Instr`, then use `Api` for
run / observe / encode. ELF packaging stays in external `sbpf` tools.
Verified *compilers* (IR→sBPF), if any, are separate packages that **depend on**
this one—analogous to `yul-compiler` depending on `yul-semantics` + `evm-semantics`.

**Authoritative scope note:** [`docs/SCOPE.md`](docs/SCOPE.md).

Primary executable reference:
[blueshift-gg/sbpf](https://github.com/blueshift-gg/sbpf)
(`crates/common` execute + encode; assembler only as oracle).

## Guiding decisions

### 1. What “semantics” means here

We formalize **what resolved sBPF instructions mean when executed**, not how
`.s` source text is lexed or how ELF headers are laid out.

```
L0  .s text (+ macros/includes)     — OUT (other tools)
L1  surface AST (labels as names)   — OUT (integrators)
L2  resolved program (Instr list)   — ★ THIS REPO
L3  bytecode bytes                  — ★ THIS REPO
L4  machine execution               — ★ THIS REPO
L5  host syscalls (thin Dialect)    — ★ interface + stubs only
```

### 2. Ground truth is a small-step relation

sBPF is a PC-based register machine. Ground truth is a **small-step** judgment
(or equivalently, an executable total `execStep` with a matching relation):

> given program `P`, machine state `m`, and current instruction `i = P[m.pc]`,
> step to `m'`.

A fuel-indexed multi-step interpreter is a *derived* view, to be tied by
adequacy (soundness + completeness for terminating runs), following yul-semantics.

We deliberately **do not** force Yul-style structured big-step for control flow;
that model fits Yul blocks/`for`/`break`, not jump offsets.

### 3. Compute units (gas) are not modeled (Phase 1)

Alignment with yul-semantics §1: functional equivalence does not track CU.
`sol_remaining_compute_units` is a nondeterministic/oracle read if exposed.

### 4. Target architecture: sBPF V3 first

`SbpfArch::V3` is the assembler default. Decode uses `Opcode.try_from_sbpf_v3`
semantics: certain classic bytes are **reassigned to jump32** ops.

**Implication:** under V3, some classic opcodes share bytes with jump32 and do
not round-trip through `ofByteV3?`. Documented conflicts (from sbpf):

| Byte | Classic | V3 preferred |
|------|---------|--------------|
| 0x46 / 0x4e | udiv32 | jset32 |
| 0x66 / 0x6e | urem32 | jsgt32 |
| 0xc6 / 0xce | sdiv32 | jslt32 |
| 0x36 / 0x3e | uhmul64 | jge32 |
| 0x56 / 0x5e | udiv64 | jne32 |
| 0x76 / 0x7e | urem64 | jsge32 |
| 0xb6 / 0xbe | shmul64 | jle32 |
| 0xd6 / 0xde | sdiv64 | jsle32 |

Round-trip theorems are stated for **V3-safe** opcodes (no conflict, or the
V3-preferred constructor).

### 5. Words are `BitVec 64`

Registers and ALU are 64-bit. 32-bit ops truncate / zero-extend as in
`crates/common/src/execute/alu32.rs`. Lean `BitVec` enables future `bv_decide`
automation without requiring Mathlib for the core skeleton.

### 6. Syscalls are a `Dialect` (open world)

Internal `call` (PC-relative), `callx`, and `exit` are closed ISA.

`call` with a **syscall name** (resolved assembler form) invokes
`Dialect.syscall`. Full Solana runtime / CPI / crypto is **not** inlined;
clients supply a relation or executable stub (like Yul `evmWithExternal` /
keccak oracles).

### 7. Assembler tooling stays in Rust (for now)

Not formalized in Phase 1:

- pest grammar / dual syntax (default vs llvm)
- preprocessor (`.include`, `.macro`)
- full ELF section emission, dynsym, debug info
- debugger, CLI, analyzer, IR

Reusable as **oracles**: assemble fixtures in Rust, load resolved bytecode into
Lean, compare runs against `SbpfVm`.

## Machine model

- **Registers:** `r0`–`r10` (`Fin 11` → `BitVec 64`).
- **PC:** instruction index (not byte offset); `lddw` still advances one logical
  instruction in the program list after resolution (size is an encoding concern).
- **Memory regions:** rodata `0x0`, stack `0x200000000`, heap `0x300000000`,
  input `0x400000000` (from `vm/memory.rs`).
- **Call stack:** saves `r6`–`r9` and FP (`r10`); frame size 4096.
- **Entry:** `r1 = inputStart`, `r10 = initial FP`, `pc = 0`.
- **Halt:** `exit` with empty call stack halts with code `r0`.

## What is proven / planned

| Artifact | Status |
|----------|--------|
| Opcode enum + V3 byte maps | done |
| Instr AST + encode/decode | done |
| Machine + closed execStep | done |
| Classic ALU (match sbpf execute) | done |
| PQR ALU (SIMD-0174) | done |
| Relational Step + Run | done |
| Determinism (closed step) | done |
| Fuel interpreter + adequacy skeleton | done |
| Syscall dialect (`closed`/`noop`/`stub`) | done |
| Diff goldens (`DiffTests` + `tools/diff_oracle`) | done |
| Encode semantic preservation (concrete programs) | done (`EncodeSem`) |
| Host memory syscalls + abort halt | done (`Host`) |
| ProofForge Api + Observation + bridge sketch | done |
| Account input cells + CounterScenario | done |
| Opcode coverage table (138) | done |
| Return data host (`sol_set/get_return_data`) | done |
| **Phase 1 delivery** | **complete** |
| WellFormed + encodable (V3-safe, imm fits) | done |
| EncodePreserve: sameExec round-trip + exec agree | done (sample suite + program-level) |
| `sameExec → execInstr` general theorem | done (`SameExec.lean`) |
| `runFuel` ↔ `Steps` / `Run` adequacy | done (`Adequacy.lean`) |
| Consumer docs + `docs/SCOPE.md` | done |
| Stable `Api` (`asm*` + legacy `pf*`) | done |
| Universal ∀ encodable → roundTrip proof | optional later |
| Label resolution / ELF packing | **out of scope** |
| Full Solana account/CPI / IR compiler | **out of scope** |

## Reference map (sbpf → Lean)

| sbpf path | Lean |
|-----------|------|
| `common/opcode.rs` | `Opcode.lean` |
| `common/instruction.rs` encode | `Encode.lean` |
| `common/execute/*` | `Step.lean` / `Interp.lean` |
| `vm/memory.rs`, `vm/vm.rs` | `Machine.lean` |
| `common/syscalls.rs` | `Dialect.lean` |
| assembler fixtures | `Examples.lean` + external oracle |

## ProofForge interface

This package is the **Solana sBPF ISA foundation** for ProofForge (V1 formal
lane and V2 `new_design` materializer). It is methodologically the Solana
counterpart of EVM's `yul-semantics` / powdr bridge.

- **Contract:** [`docs/proof-forge-interface.md`](docs/proof-forge-interface.md)
- **Stable import:** `import SbpfSemantics.Api`
- **Diff surface:** `Observation` / `runObserved` / `traceObserved`
- **Sketch:** `SbpfSemantics.BridgeSketch` (hand-lowered increment fragment)

Dependency is **one-way**: ProofForge may pin this repo; this repo never
imports ProofForge. Product emit (`.s` → sbpf → ELF) may stay external;
this package owns **meaning** of resolved instructions and observations.

## Non-goals (Phase 1)

- Binary compatibility proof against Agave `solana_rbpf` (second oracle later).
- Verified text parser or macro expansion.
- CU accounting and denial-of-service bounds.
- Full cryptographic fidelity of syscalls.
- ProofForge DSL, account layout, CPI policy, or ELF packaging.
