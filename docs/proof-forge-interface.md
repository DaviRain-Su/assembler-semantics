# ProofForge ↔ assembler-semantics interface contract

Status: **normative for this repo's public surface**.  
Consumer: ProofForge V1 formal Solana lane and ProofForge V2 (`new_design`) Solana materializer.

This repository is the **sBPF ISA semantics** foundation (L2–L4). It is **not**
a product compiler, account model, or ELF packager.

## Dependency direction

```text
ProofForge / ProofForgeV2
    │  optional Lake require / fixed git rev  (never the reverse)
    ▼
assembler-semantics  (this package: SbpfSemantics)
    │  differential oracle (optional)
    ▼
blueshift sbpf · Mollusk · solanalib · Agave
```

- **This package must not import ProofForge.**
- ProofForge may depend on a **pinned** revision of this package for formal /
  runtime-trace lanes only; product emit may keep using text `.s` + external
  `sbpf` unchanged (parent `docs/solana-sbpf-solanalib-bridge.md`).

## Layer map

| Layer | Owner | This package |
|-------|--------|--------------|
| `program` DSL / Typed / Semantic | ProofForge | **out** |
| Portable IR / SolanaPlan / accounts / CPI policy | ProofForge | **out** |
| Lowering Plan → resolved instruction list | ProofForge materializer | **producer of L2** |
| L2 `Program` (`Array Instr`) | shared wire type | **in** (`Instr`) |
| L3 bytes encode/decode | shared | **in** (`Encode`) |
| L4 small-step / fuel run | ISA ground truth | **in** (`Step`, `Run`, `Interp`) |
| L5 host syscalls | abstract Dialect | **in** (`Dialect`, `Host`) |
| ELF / IDL / deploy | ProofForge + toolchain | **out** |

## Stable API (import `SbpfSemantics.Api`)

| Symbol | Role |
|--------|------|
| `Instr`, `Program`, `Opcode` | L2 program model |
| `Machine`, `Memory`, `Machine.entry` | abstract machine |
| `ExecDialect`, `closedExec`, `stubExec`, `hostExec` | host plug-in |
| `execStep`, `Step`, `runFuel`, `interp`, `interpEntry` | execution |
| `Outcome` | `halted` / `stuck` / `outOfFuel` |
| `encodeInstr`, `encodeProgram`, `decodeInstr?`, `decodeProgram?` | L3 |
| `Observation`, `observe`, `TraceEvent` | PF differential surface (incl. `returnData`) |
| `runObserved` / `pfRun` / `pfRunMachine` | fuel run → final observation |
| `AccountLayout` / `pfEntryCell` | input-region cells for portable state |
| `CounterScenario` | init / increment / get L2 programs + goldens |
| `Machine.readyForNext` | multi-entrypoint scenario chaining |
| `Instr.wellFormed` / `Instr.encodable` | shape + V3-safe encode domain |
| `Instr.sameExec` / `decodeEncode?` | execution-relevant encode round-trip |

### What is *not* stable (may change without major version)

- Internal ALU helper names in `Alu.lean`
- Exact `Machine` field layout beyond documented accessors
- Incomplete PQR edge cases vs future Agave alignment
- Full cryptographic syscall fidelity

## Observation contract (for IR ⇝ sBPF diff)

ProofForge should compare **observations**, not full machine equality.

```lean
structure Observation where
  outcome : Outcome
  r0      : Word          -- return / exit code convention
  r1      : Word          -- often input pointer
  r10     : Word          -- frame pointer
  pc      : Nat
  halted  : Option Word
```

Optional extensions (versioned later):

- stack/heap/input **slices** at declared offsets (account data windows)
- ordered log names (host log stub)
- return-data blob (when modeled)

**Matching rule for Phase-1 Counter-style programs:**

1. Same `Outcome` constructor (`halted c` with same `c`, or both `stuck`).
2. Same `r0` when halted successfully after `exit`.
3. For state-carrying programs: PF declares memory windows; compare those
   windows only (not entire heap).

## Host / Dialect contract

| Dialect | Use |
|---------|-----|
| `closedExec` | pure ALU / control-flow tests; any syscall → stuck |
| `stubExec` | log names succeed as no-ops; abort stuck |
| `hostExec` | log + abort-halt + memcpy/memmove/memset/memcmp |

ProofForge account/CPI reality **extends** `ExecDialect` (or a future
`SolanaRuntimeDialect`) rather than forking `Step`. ISA step rules stay fixed.

Syscall ABI: arguments in **`r1`–`r5`**, return value written to **`r0`** by
`execSyscall` (see `Host.lean`).

## Materializer obligations (ProofForge side)

When emitting into this semantics, the materializer must produce:

1. **Resolved** `Program` (no free labels; jump `off` / call imm numeric).
2. Instruction indices as PC (not raw byte offsets). `lddw` is one list element.
3. Entry state consistent with `Machine.entry` unless a documented custom
   loader fills `input` / `rodata` / registers.
4. Syscall names only via `Instr.syscall` (L2); they are **not** in 8-byte
   encodings (use reloc/dynsym in product ELF path separately).
5. V3 opcode semantics when claiming V3 ELF (`Opcode.ofByteV3?`).

## Semantic preservation claim shapes

**A. Encode (this package, partial):**  
`redecodeProgram? (encodeProgram P) = some P'` ⇒ for listed closed programs,
`outcomeOf P = outcomeOf P'` (`EncodeSem.lean`).

**B. Lowering (ProofForge, future):**  
If `lower(IR) = P` and `IR.step` yields observable `O`, then
`runObserved hostExec P fuel m0` yields `O'` with `O ~ O'` under the
observation relation.

**C. External oracle (CI):**  
Same L2 program: Lean `runObserved` vs blueshift `SbpfVm` / Mollusk on
matching host stubs (`tools/diff_oracle`, `docs/diff-oracle.md`).

## Clean-room note for ProofForge V2

V2 may treat this package as an **optional formal/runtime-trace dependency**
with exact pin + checksum (same class as solc/WABT pins). It must not pull
parent `ProofForge/` product sources. Research-only references live under
V2 `docs/research/` without becoming a runtime fallback.

## Versioning

- Package version: Lake `version` in `lakefile.toml`.
- Interface digest: hash of this file + `SbpfSemantics/Api.lean` exports.
- Breaking changes (remove/rename Api symbols, change Observation fields,
  change step meaning of an opcode) require version bump and a note in
  `CHANGELOG` (when introduced).

## Related documents

- [`DESIGN.md`](../DESIGN.md) — ISA design decisions  
- [`docs/diff-oracle.md`](diff-oracle.md) — external differential testing  
- Parent research (not a dependency):  
  `proof_forge/docs/solana-sbpf-solanalib-bridge.md`  
  `proof_forge/new_design/docs/targets/02-solana.md`
