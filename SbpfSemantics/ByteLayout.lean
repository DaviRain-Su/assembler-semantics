import SbpfSemantics.Instr
import SbpfSemantics.Encode

/-!
# SbpfSemantics.ByteLayout

Map between **instruction-index PC** (list machine) and **byte offset PC**
(bytecode stream). Used to step encoded programs without changing L4 ground
truth (`execStep` still runs on list indices).
-/

namespace SbpfSemantics

/-- Start byte offset of each instruction; `offsets.size = P.size`,
`offsets[i]` is the byte index of instruction `i`. -/
def Program.byteOffsets (P : Program) : Array Nat :=
  Id.run do
    let mut acc : Array Nat := #[]
    let mut off : Nat := 0
    for i in P do
      acc := acc.push off
      off := off + i.sizeBytes
    pure acc

/-- Total encoded size in bytes. -/
def Program.totalBytes (P : Program) : Nat :=
  P.foldl (init := 0) fun n i => n + i.sizeBytes

/-- Look up list index whose instruction starts at exact byte offset `b`. -/
def byteOffsetToIndex? (offsets : Array Nat) (b : Nat) : Option Nat :=
  Id.run do
    let mut i : Nat := 0
    for off in offsets do
      if off == b then return some i
      i := i + 1
    pure none

/-- Byte offset of instruction index `pc` (if in range). -/
def indexToByteOffset? (offsets : Array Nat) (pc : Nat) : Option Nat :=
  offsets[pc]?

/-- `encodeProgram` length matches sum of instruction sizes. -/
theorem encode_size_eq_totalBytes_sample :
    let P : Program := #[
      Instr.binImm .Mov64Imm ⟨0, by omega⟩ 1#64,
      Instr.lddw ⟨1, by omega⟩ 0x100#64,
      Instr.exit
    ]
    (encodeProgram P).size = P.totalBytes := by
  native_decide

example :
    let P : Program := #[Instr.lddw ⟨0, by omega⟩ 0#64, Instr.exit]
    P.byteOffsets = #[0, 16] ∧ P.totalBytes = 24 := by
  native_decide

example :
    let P : Program := #[Instr.exit, Instr.binImm .Add64Imm ⟨0, by omega⟩ 1#64]
    byteOffsetToIndex? P.byteOffsets 8 = some 1 := by
  native_decide

end SbpfSemantics
