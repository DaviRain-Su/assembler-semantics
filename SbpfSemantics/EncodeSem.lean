import SbpfSemantics.EncodePreserve
import SbpfSemantics.Interp

/-!
# SbpfSemantics.EncodeSem

Program-level encode semantic preservation examples. Instruction-level
round-trip and `sameExec` live in `EncodePreserve.lean`.
-/

namespace SbpfSemantics

private def r0 : Reg := ⟨0, by omega⟩

def sampleProg : Program :=
  #[
    .binImm .Mov64Imm r0 2#64,
    .binImm .Add64Imm r0 3#64,
    .exit
  ]

def outcomeOf (P : Program) : Outcome :=
  (interpEntry closedExec P 40).2

theorem encode_preserves_interp_sample :
    outcomeOf sampleProg = .halted 5#64 := by
  native_decide

theorem encode_preserves_interp_sample_redecode :
    (redecodeProgram? sampleProg).map outcomeOf = some (.halted 5#64) := by
  native_decide

def sampleJump : Program :=
  #[
    .binImm .Mov64Imm r0 0#64,
    .jumpImm .JeqImm r0 0#64 (BitVec.ofInt 16 1),
    .binImm .Add64Imm r0 1#64,
    .exit
  ]

theorem encode_preserves_interp_jump :
    outcomeOf sampleJump = .halted 0#64 := by
  native_decide

theorem encode_preserves_interp_jump_redecode :
    (redecodeProgram? sampleJump).map outcomeOf = some (.halted 0#64) := by
  native_decide

def sampleMem : Program :=
  #[
    .binImm .Mov64Imm r0 0xab#64,
    .storeReg .Stxdw ⟨10, by omega⟩ r0 (BitVec.ofInt 16 (-8)),
    .loadMem .Ldxdw ⟨1, by omega⟩ ⟨10, by omega⟩ (BitVec.ofInt 16 (-8)),
    .binReg .Mov64Reg r0 ⟨1, by omega⟩,
    .exit
  ]

theorem encode_preserves_interp_mem :
    outcomeOf sampleMem = .halted 0xab#64 := by
  native_decide

theorem encode_preserves_interp_mem_redecode :
    (redecodeProgram? sampleMem).map outcomeOf = some (.halted 0xab#64) := by
  native_decide

end SbpfSemantics
