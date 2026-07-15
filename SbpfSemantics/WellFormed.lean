import SbpfSemantics.Basic
import SbpfSemantics.Opcode
import SbpfSemantics.Instr
import SbpfSemantics.Encode

/-!
# SbpfSemantics.WellFormed

Structural well-formedness of resolved instructions: required operands present
for each `OpClass`. This is the domain of encode/decode round-trip and of
`execInstr` success (modulo runtime faults like /0 or OOB memory).
-/

namespace SbpfSemantics

/-- Operand shape required by `opClass` (independent of concrete opcode). -/
def OpClass.wellFormed : OpClass → Instr → Bool
  | .loadImm, i => i.dst.isSome && i.imm.isSome
  | .loadMem, i => i.dst.isSome && i.src.isSome && i.off.isSome
  | .storeImm, i => i.dst.isSome && i.off.isSome && i.imm.isSome
  | .storeReg, i => i.dst.isSome && i.src.isSome && i.off.isSome
  | .binImm, i => i.dst.isSome && i.imm.isSome
  | .binReg, i => i.dst.isSome && i.src.isSome
  | .unary, i => i.dst.isSome
  | .endian, i => i.dst.isSome && i.imm.isSome
  | .jump, i => i.off.isSome
  | .jumpImm, i => i.dst.isSome && i.imm.isSome && i.off.isSome
  | .jump32Imm, i => i.dst.isSome && i.imm.isSome && i.off.isSome
  | .jumpReg, i => i.dst.isSome && i.src.isSome && i.off.isSome
  | .jump32Reg, i => i.dst.isSome && i.src.isSome && i.off.isSome
  | .callImm, i =>
      -- either relative call (imm) or host syscall (name); not both required
      i.imm.isSome || i.syscall.isSome
  | .callReg, i => i.dst.isSome
  | .exit, _ => true

/-- Instruction is structurally well-formed for its opcode class. -/
def Instr.wellFormed (i : Instr) : Bool :=
  i.opcode.opClass.wellFormed i

/-- Immediate fits in the signed 32-bit field used by non-`lddw` encoding:
`imm = signExtend 64 (truncate 32 imm)`. -/
def immFitsI32 (w : Word) : Bool :=
  w == imm32AsWord (BitVec.truncate 32 w)

/-- Fields that participate in the 8/16-byte encoding (no host names). -/
def Instr.encodable (i : Instr) : Bool :=
  Opcode.v3RoundTrip i.opcode &&
  i.syscall.isNone &&
  i.wellFormed &&
  match i.opcode.opClass with
  | .loadImm => true  -- full 64-bit imm for lddw
  | .callReg => true  -- target in dst; imm field carries reg number
  | .exit => true
  | .jump => true     -- only off
  | .unary => true
  | .binReg | .loadMem | .storeReg | .jumpReg | .jump32Reg => true
  | .binImm | .storeImm | .endian | .jumpImm | .jump32Imm | .callImm =>
      match i.imm with
      | some w => immFitsI32 w
      | none => false

/-- Smart constructors produce well-formed instructions. -/
example : Instr.wellFormed (.binImm .Add64Imm ⟨0, by omega⟩ 1#64) = true := by
  native_decide
example : Instr.wellFormed (.binReg .Add64Reg ⟨0, by omega⟩ ⟨1, by omega⟩) = true := by
  native_decide
example : Instr.wellFormed (.lddw ⟨2, by omega⟩ 0#64) = true := by
  native_decide
example : Instr.wellFormed (.exit) = true := by
  native_decide
example : Instr.wellFormed (.callSyscall "sol_log_") = true := by
  native_decide
example : Instr.encodable (.callSyscall "sol_log_") = false := by
  native_decide  -- host names are not in the byte encoding
example : Instr.encodable (.binImm .Add64Imm ⟨1, by omega⟩ 10#64) = true := by
  native_decide
example : Instr.encodable (.binImm .Udiv32Imm ⟨1, by omega⟩ 1#64) = false := by
  native_decide  -- not V3-safe
example : Instr.encodable (.jumpImm .Jset32Imm ⟨0, by omega⟩ 0#64 1#16) = true := by
  native_decide  -- V3-preferred at that byte

/-- Immediates outside i32 range are not encodable for binImm. -/
example :
    Instr.encodable (.binImm .Mov64Imm ⟨0, by omega⟩ (1#64 <<< 40)) = false := by
  native_decide

end SbpfSemantics
