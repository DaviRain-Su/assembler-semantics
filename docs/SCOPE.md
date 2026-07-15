# Scope: assembly / ISA layer only

**This repository owns one layer only:** the **resolved sBPF instruction machine**
and its **byte encoding**.

It is deliberately **not** a full Solana compiler, not a text assembler product,
and not an ELF linker. Those integrate **on top of** or **beside** this package.

## In scope (make this excellent)

| Layer | Content | Modules |
|-------|---------|---------|
| **L2** | Resolved `Instr` / `Program` (numeric operands) | `Instr`, `WellFormed` |
| **L3** | Encode / decode (V3) | `Encode`, `EncodePreserve`, `SameExec` |
| **L3↔L4** | Byte-PC view over encoded stream | `ByteLayout`, `ByteStep` |
| **L4** | Small-step + fuel run (list PC) | `Step`, `Run`, `Interp`, `Adequacy` |
| **L5 thin** | Host *interface* + minimal stubs | `Dialect`, `Host` |
| **Observation** | Diff surface for integrators | `Observation`, `Api` |

Goals for this layer:

1. Clear, stable **Api** for other Lean packages to depend on.
2. Executable semantics + relational `Step` with adequacy.
3. Encoding facts so L2 ↔ L3 is trustworthy.
4. Thin host dialect so integrators plug real Solana runtime later.
5. L3↔L4 **layout** facts (index ↔ byte at instruction starts) — see `ByteLayout`.

Planning (deferred vs next): **`docs/ROADMAP.md`**.

## Out of scope (other components own these)

| Layer | Owner (examples) |
|-------|------------------|
| L0 `.s` text parse / macros | blueshift `sbpf` assembler, or a future text tool |
| L1 surface AST + labels | ProofForge `AstNode` / lowerer |
| High-level IR / business DSL | ProofForge Semantic / IR |
| Verified *compiler* IR→sBPF | Future “yul-compiler analogue”, not this repo |
| ELF / sections / dynsym / deploy | `sbpf` CLI, Solana toolchain |
| Full account / CPI / Agave fidelity | Runtime / formal host projects |

## Integration contract (how others plug in)

```text
  [upstream]  lower / resolve labels
        │
        ▼
   Program := Array Instr     ← hand off HERE
        │
        ├─► runObserved / Step / Run     (meaning)
        └─► encodeProgram / decode       (bytes)
        │
        ▼
  [downstream] optional: wrap bytes in ELF, or pretty-print .s
```

Upstream must produce **L2** (no free labels, optional `syscall` names for host).
Downstream may:

- call `pfRun` / `Observation` for tests and proofs;
- call `pfEncode` then feed bytes to an external packager;
- instantiate `ExecDialect` for richer host behavior.

See also `docs/for-proof-forge-consumers.md` and `docs/proof-forge-interface.md`.

## Positioning vs powdr stack

| powdr | This package |
|-------|----------------|
| `yul-semantics` | partial analogue only for **target** machine of a Solana backend |
| `evm-semantics` | **closest match** (instruction / VM semantics) |
| `yul-compiler` | **not this repo** (IR→machine compile proofs) |
| solc / deploy packaging | **sbpf / ELF tools** (not this repo) |

We stay the **sBPF instruction semantics + encode** brick so compilers and
toolchains can combine us without forking an ad-hoc interpreter.
