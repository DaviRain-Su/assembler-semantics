# What ProofForge needs vs what this repo provides

This note answers two questions for Solana only:

1. **What does the main ProofForge product need** to emit programs?
2. **What must Lean supply** to “拼汇编” (build assembly), before external
   `sbpf` turns `.s` into an ELF?

It is the consumer-facing companion to `DESIGN.md` and
`proof-forge-interface.md`.

---

## End-to-end product pipeline (ProofForge today)

```text
  program / portable IR.Module
           │
           ▼
  SolanaPlan  (accounts, layouts, discriminators, CPI sites, …)
           │
           ▼
  lower  ──►  Array AstNode     ← “拼汇编”的主战场（Lean）
           │     • labels still symbolic
           │     • .section / .globl / instructions
           ▼
  render ──►  .s text           ← Asm.renderNodes
           │
           ▼
  external sbpf assemble/link ──► ELF (+ IDL, package, …)
```

Parent-repo map (research reference, not a dependency of this package):

| Stage | Typical module (ProofForge) |
|-------|------------------------------|
| Plan | `Backend/Solana/Plan.lean` |
| IR → nodes | `SbpfAsm/*`, `Plan.lowerFromPlan` |
| Nodes → text | `Asm.lean` (`AstNode.render`) |
| Package / IDL | `Package.lean`, `Idl.lean` |
| Formal side path | `BpfEncode`, `LabeledSbpf`, `SbpfInterpreter` |

**ELF is not produced in Lean.** Lean produces **assembly text (or L2
instructions)**; the **sBPF toolchain** (blueshift `sbpf` or Solana platform
tools) produces ELF.

---

## Question 1 — Main project components (by role)

### A. Product emit (must exist in ProofForge)

| Component | Role | In this repo? |
|-----------|------|----------------|
| Semantic / IR | Business meaning, portable | No |
| SolanaPlan | Accounts, layout, entrypoints | No |
| Lowering | IR/Plan → **surface assembly AST** (labels, sections) | No |
| Pretty-printer | AST → `.s` string | No |
| IDL / package / manifest | Client + deploy metadata | No |
| Shell-out to `sbpf` | `.s` → ELF | No (external tool) |

### B. Meaning of the emitted code (can live here)

| Component | Role | In this repo? |
|-----------|------|----------------|
| Resolved instruction model | L2 after labels fixed | **Yes** (`Instr`) |
| Opcode / encode / decode | Bytes ↔ instr | **Yes** |
| Small-step semantics | What code *does* | **Yes** (`Step`) |
| Host stubs | Syscalls for traces | **Yes** (`Host`) |
| Observation | Diff surface for IR ⇝ sBPF | **Yes** |

### C. Optional formal lanes (ProofForge may pin this package)

```text
AstNode ──resolve──► Instr list ──encode──► bytes
                         │
                         ▼
                      Step / runObserved   ← this package
                         │
                         ▼
              compare to IR.Semantics / tests
```

Product path can stay: `AstNode → .s → sbpf → ELF`.  
Formal path uses this package as **oracle of instruction meaning**, not as
the packager.

---

## Question 2 — “用 Lean 拼汇编”需要什么？

“拼汇编” = **build a valid sBPF assembly program in Lean**, not link an ELF.

### Minimum layers (surface → resolved)

```text
L0  .s text string          (what sbpf reads)
 ↑ render
L1  Surface AST             labels, sections, directives, symbolic imm/off
 ↑ lower / resolve
L2  Resolved Instr list     numeric offsets/imm only   ← THIS REPO’S MODEL
 ↑ encode
L3  Bytecode                8/16-byte instructions
```

| Layer | Needed to “拼汇编” | Who owns it |
|-------|-------------------|-------------|
| **L1 surface AST** | Yes — sections, labels, `call sol_log_`, jump targets as names | **ProofForge** (`AstNode`) |
| **Label resolution** | Yes — turn names → PC offsets / reloc | ProofForge (or future L1→L2 here) |
| **L2 Instr** | Yes — final instruction facts | **This repo** (canonical model) |
| **Pretty-print L1→L0** | Yes — for product | ProofForge `Asm.render` |
| **encode L2→L3** | Optional for product; required for formal/bytes | **This repo** |
| **ELF** | Product only | **sbpf / platform tools** |

### What Lean must implement to *generate* assembly (product)

1. **Instruction vocabulary** — opcode + operand shapes (registers, imm, mem).  
2. **Program structure** — entrypoint, sections (`.text` / rodata), globals.  
3. **Control structure** — labels, forward/back jumps, internal calls.  
4. **Solana program skeleton** — entrypoint preamble, account pointer math,
   discriminators (from Plan/StateLayout).  
5. **Syscall names as symbols** — e.g. `call sol_set_return_data` (relocated
   by assembler).  
6. **Render to `.s`** — text compatible with the chosen assembler (default vs
   llvm syntax if needed).  
7. **Hand off** — write file + invoke `sbpf` / linker (outside Lean proof).

### What Lean does *not* need for product ELF

- Full pest parser of `.s`  
- Dynamic linker / dynsym emission (assembler does)  
- Complete Solana runtime inside Lean  

### What this repo adds for *correctness* of that assembly

| Need | Mechanism here |
|------|----------------|
| “Does this instruction mean X?” | `execInstr` / `Step` |
| “Is encoding faithful?” | `WellFormed`, `encodable`, `sameExec`, `EncodePreserve` |
| “Can we run a lowered Counter fragment?” | `CounterScenario`, `Observation` |
| “Host effects for traces?” | `hostExec` (memcpy, return data, abort, …) |

ProofForge lowerer should eventually target either:

- **L1** `AstNode` (product), then resolve to **L2** for checks; or  
- emit **L2** `SbpfSemantics.Instr` and pretty-print from L2 (if you add a
  printer later).

Today parent emit is L1-centric; this package is L2-centric. The **bridge** is
label resolution + mapping `AstNode` → `Instr` (still a ProofForge or future
adapter job).

---

## Mapping: parent formal pieces ↔ this package

| ProofForge (parent) | assembler-semantics |
|---------------------|---------------------|
| `Asm.AstNode` | surface (not modeled) |
| `LabeledSbpf` / resolved | ≈ `Instr` |
| `BpfEncode` | ≈ `Encode` |
| `SbpfInterpreter` / `SbpfExec` | ≈ `Step` / `Interp` |
| solanalib bridge | external; optional second oracle |

This package aims to be a **clean, pin-able ISA kernel** so ProofForge does not
have to grow another ad-hoc interpreter for every formal experiment.

---

## Practical recommendation (for PF authors)

1. **Keep product path:** Plan → AstNode → `.s` → `sbpf` → ELF.  
2. **Pin this package** for formal/trace: resolve to `Instr`, run
   `pfRun` / `Observation`, optionally `pfEncode`.  
3. **Do not** move ELF linking into Lean.  
4. **Do** keep account layout / CPI policy in Plan (product); only pass
   simplified cells into this machine when testing portable fragments
   (`AccountLayout` / `CounterScenario` as the L2 target shape).

---

## What we still deepen *in this repo only*

Independent of ProofForge product work:

1. General theorems: `encodable → roundTrip`, `sameExec → execInstr` eq  
2. Full `runFuel` / `Steps` adequacy  
3. Optional byte-PC machine  
4. Richer diff vectors  

See `CHANGELOG.md` / `DESIGN.md` for status.
