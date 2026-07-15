import SbpfSemantics.Basic
import SbpfSemantics.Opcode
import SbpfSemantics.Instr
import SbpfSemantics.Encode
import SbpfSemantics.Machine
import SbpfSemantics.Dialect
import SbpfSemantics.Host
import SbpfSemantics.Step
import SbpfSemantics.Run
import SbpfSemantics.Interp
import SbpfSemantics.Observation

/-!
# SbpfSemantics.Api

**Stable export surface** for ProofForge (and other consumers).

Prefer `import SbpfSemantics.Api` over reaching into internal modules when
depending on this package. Symbols listed here are covered by
`docs/proof-forge-interface.md`.
-/

namespace SbpfSemantics

-- Re-export core types by being imported; this module is the documentation
-- anchor. Additional aliases keep the contract readable in one place.

/-- Alias: L2 program. -/
abbrev PfProgram := Program

/-- Alias: resolved instruction. -/
abbrev PfInstr := Instr

/-- Alias: abstract machine. -/
abbrev PfMachine := Machine

/-- Alias: host dialect for execution. -/
abbrev PfHost := ExecDialect

/-- Recommended default host for PF Solana traces that need memory syscalls. -/
def pfDefaultHost : ExecDialect := hostExec

/-- Closed host for pure instruction fragments. -/
def pfClosedHost : ExecDialect := closedExec

/-- Run with observation (entry machine). -/
def pfRun (D : ExecDialect) (P : Program) (fuel : Nat := 10_000)
    (input : Array UInt8 := #[]) (rodata : Array UInt8 := #[]) : Observation :=
  runObservedEntry D P fuel input rodata

/-- Encode a PF-lowered program to bytecode (V3 bytes). -/
def pfEncode (P : Program) : Array UInt8 :=
  encodeProgram P

/-- Decode bytecode to a program (V3). -/
def pfDecode? (bs : Array UInt8) : Option Program :=
  decodeProgram? bs

end SbpfSemantics
