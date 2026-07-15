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
import SbpfSemantics.AccountLayout
import SbpfSemantics.WellFormed
import SbpfSemantics.EncodePreserve
import SbpfSemantics.SameExec
import SbpfSemantics.Adequacy
import SbpfSemantics.ByteLayout
import SbpfSemantics.ByteStep
import SbpfSemantics.ByteBisim
import SbpfSemantics.EncodeSize
import SbpfSemantics.RoundTrip

/-!
# SbpfSemantics.Api

**Stable integration surface** for external packages (ProofForge, tests, tools).

Import only this module when depending on the assembly-layer library:

```lean
import SbpfSemantics.Api
open SbpfSemantics
```

Scope: L2 resolved programs, L3 encode/decode, L4 step/run, thin L5 host.
See `docs/SCOPE.md`.
-/

namespace SbpfSemantics

/-! ### Type aliases (integration vocabulary) -/

abbrev AsmProgram := Program
abbrev AsmInstr := Instr
abbrev AsmMachine := Machine
abbrev AsmHost := ExecDialect
abbrev AsmOutcome := Outcome
abbrev AsmObservation := Observation

/-! ### Hosts -/

/-- Pure ALU / control: syscalls stuck. -/
def asmClosedHost : ExecDialect := closedExec

/-- Log + mem + return_data + abort-halt (default for fragment tests). -/
def asmDefaultHost : ExecDialect := hostExec

/-- Log-only stubs; abort stuck. -/
def asmStubHost : ExecDialect := stubExec

/-! ### Run / observe -/

def asmRun (D : ExecDialect) (P : Program) (fuel : Nat := 10_000)
    (input : Array UInt8 := #[]) (rodata : Array UInt8 := #[]) : Observation :=
  runObservedEntry D P fuel input rodata

def asmRunMachine (D : ExecDialect) (P : Program) (m : Machine) (fuel : Nat := 10_000) :
    Observation :=
  runObserved D P fuel m

def asmStep (D : ExecDialect) (P : Program) (m : Machine) : Option Machine :=
  execStep D P m

/-! ### Encode / decode -/

def asmEncode (P : Program) : Array UInt8 :=
  encodeProgram P

def asmDecode? (bs : Array UInt8) : Option Program :=
  decodeProgram? bs

def asmEncodeInstr (i : Instr) : Array UInt8 :=
  encodeInstr i

def asmDecodeInstr? (bs : Array UInt8) (idx : Nat := 0) : Option (Instr × Nat) :=
  decodeInstr? bs idx

def asmEncodable (i : Instr) : Bool :=
  Instr.encodable i

def asmSameExec (i j : Instr) : Bool :=
  Instr.sameExec i j

def asmRoundTrip (i : Instr) : Bool :=
  roundTripSameExec i

/-- Encode length equals `sizeBytes` (theorem `encodeInstr_size`). -/
theorem asmEncodeInstr_size (i : Instr) : (asmEncodeInstr i).size = i.sizeBytes :=
  encodeInstr_size i

/-- Whole-program encode length equals layout `totalBytes`. -/
theorem asmEncode_size (P : Program) : (asmEncode P).size = P.totalBytes :=
  encodeProgram_size P

/-- Every V3-safe opcode has a round-tripping witness (see `RoundTrip`). -/
theorem asmV3SafeRoundTripWitnesses :
    allV3SafeWitnessRoundTrip = true :=
  all_v3_safe_opcodes_have_roundtrip_witness

/-- Layout: list index → byte offset → list index (in-range PC). -/
theorem asmIndexByteRoundtrip (P : Program) (pc : Nat) (h : pc < P.size) :
    byteOffsetToIndex? P.byteOffsets
        (P.byteOffsets[pc]'(by simpa [byteOffsets_size] using h)) = some pc :=
  index_to_byte_to_index P pc h

/-- Layout: Option-form index ↔ byte round-trip. -/
theorem asmIndexToByte_byteToIndex (P : Program) (pc : Nat) (h : pc < P.size) :
    (indexToByteOffset? P.byteOffsets pc).bind (byteOffsetToIndex? P.byteOffsets) =
      some pc :=
  indexToByte_byteToIndex P pc h

/-! ### Machine helpers -/

def asmEntry (input : Array UInt8 := #[]) (rodata : Array UInt8 := #[]) : Machine :=
  Machine.entry input rodata

def asmEntryCell (value : Word) (cell : InputCell := counterCell) : Machine :=
  Machine.entryWithCell cell value

def asmReadyForNext (m : Machine) : Machine :=
  m.readyForNext

/-! ### Backward-compatible PF-prefixed names -/

abbrev PfProgram := AsmProgram
abbrev PfInstr := AsmInstr
abbrev PfMachine := AsmMachine
abbrev PfHost := AsmHost

def pfDefaultHost : ExecDialect := asmDefaultHost
def pfClosedHost : ExecDialect := asmClosedHost

def pfRun (D : ExecDialect) (P : Program) (fuel : Nat := 10_000)
    (input : Array UInt8 := #[]) (rodata : Array UInt8 := #[]) : Observation :=
  asmRun D P fuel input rodata

def pfRunMachine (D : ExecDialect) (P : Program) (m : Machine) (fuel : Nat := 10_000) :
    Observation :=
  asmRunMachine D P m fuel

def pfEncode (P : Program) : Array UInt8 := asmEncode P
def pfDecode? (bs : Array UInt8) : Option Program := asmDecode? bs
def pfEntryCell (value : Word) (cell : InputCell := counterCell) : Machine :=
  asmEntryCell value cell
def pfEncodable (i : Instr) : Bool := asmEncodable i
def pfSameExec (i j : Instr) : Bool := asmSameExec i j

/-! ### Byte-PC view (encoded stream) -/

/-- Step treating `m.pc` as a byte offset into `encodeProgram P`. -/
def asmStepBytes (D : ExecDialect) (P : Program) (m : Machine) : Option Machine :=
  execStepBytes D P m

def asmRunBytes (D : ExecDialect) (P : Program) (fuel : Nat := 10_000)
    (input : Array UInt8 := #[]) (rodata : Array UInt8 := #[]) : Machine × Outcome :=
  runFuelBytes D P fuel (entryBytes input rodata)

end SbpfSemantics
