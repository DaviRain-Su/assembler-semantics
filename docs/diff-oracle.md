# Differential testing oracle

## Goal

Keep Lean `execStep` aligned with blueshift
[`sbpf`](https://github.com/blueshift-gg/sbpf) for ops that crate implements, and
with [SIMD-0174](https://github.com/solana-foundation/solana-improvement-documents/blob/main/proposals/0174-sbpf-arithmetics-improvements.md)
for PQR ops not yet in `crates/common/src/execute/*`.

## Lean side

Golden vectors live in `SbpfSemantics/DiffTests.lean` (`native_decide`).

## Rust side (manual / future CI)

```bash
# clone reference
git clone --depth 1 https://github.com/blueshift-gg/sbpf.git /tmp/sbpf

# run common execute unit tests (source of many goldens)
cd /tmp/sbpf && cargo test -p sbpf-common
```

Suggested automation (not checked in yet):

1. For each golden in `DiffTests`: export `(opcode, dst, imm, reg_in) → reg_out`.
2. Drive `MockVm` + `execute_*` in a small Rust binary.
3. Compare `reg_out` bit-patterns.

## Assembler fixtures

`sbpf/crates/assembler/tests/fixtures/*.s` exercise **encoding**, not execution.
Pipeline for encoding diffs:

1. `sbpf` assemble fixture → ELF/text bytes.
2. Strip to `.text` instruction stream.
3. Lean `decodeProgram?` → compare opcode sequence to expected L2 program.

## Known intentional divergences

| Area | Lean | blueshift execute |
|------|------|-------------------|
| PQR (`lmul`/`uhmul`/…) | SIMD-0174 | not implemented (InvalidInstruction) |
| `mov32` reg | sign-extend (SIMD-0174 / V3) | zero-extend classic path |
| Syscalls | `Dialect` stubs | full runtime / handler trait |
