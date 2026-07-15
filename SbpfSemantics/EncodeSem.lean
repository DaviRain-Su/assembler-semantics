import SbpfSemantics.Encode
import SbpfSemantics.Step
import SbpfSemantics.Interp

/-!
# SbpfSemantics.EncodeSem

Semantic preservation for the encode/decode pipeline at L2 ↔ L3:

* **Normalization:** `decodeInstr? (encodeInstr i)` recovers an instruction
  that agrees with `i` on the fields execution cares about (after fill-ins of
  unused operands with zero, and dropping `syscall` names which are not in the
  8-byte encoding).
* **Program-level:** re-decoding an encoded program preserves whole-program
  `interp` outcomes for closed-world examples (no host names).
-/

namespace SbpfSemantics

/-- Drop host-only data and normalize optional fields the way decode would. -/
def Instr.stripHost (i : Instr) : Instr :=
  { i with syscall := none }

/-- Executable fields recovered after encode→decode (ignoring unused zeros). -/
structure InstrCore where
  opcode : Opcode
  dst    : Option Reg
  src    : Option Reg
  /-- Present for ops that use off in execution; else ignored. -/
  off    : Option Off16
  imm    : Option Word
  deriving DecidableEq, Repr

def Instr.toCore (i : Instr) : InstrCore where
  opcode := i.opcode
  dst := i.dst
  src := i.src
  off := i.off
  imm := i.imm

/-- Decode after encode, when successful. -/
def decodeEncode? (i : Instr) : Option Instr :=
  (decodeInstr? (encodeInstr i) 0).map (·.1)

/-- Program re-decoded from its own encoding. -/
def redecodeProgram? (P : Program) : Option Program :=
  decodeProgram? (encodeProgram P)

/-- Concrete: encode→decode preserves opcode for `mov64 r0, 42`. -/
theorem decodeEncode_mov64_opcode :
    (decodeEncode? (.binImm .Mov64Imm ⟨0, by omega⟩ 42#64)).map (·.opcode)
      = some .Mov64Imm := by
  native_decide

theorem decodeEncode_mov64_dst :
    (decodeEncode? (.binImm .Mov64Imm ⟨0, by omega⟩ 42#64)).map (·.dst)
      = some (some ⟨0, by omega⟩) := by
  native_decide

/-- Concrete: `add64` round-trips opcode. -/
theorem decodeEncode_add64_opcode :
    (decodeEncode? (.binImm .Add64Imm ⟨1, by omega⟩ 10#64)).map (·.opcode)
      = some .Add64Imm := by
  native_decide

/-- Concrete: `exit` round-trips. -/
theorem decodeEncode_exit_opcode :
    (decodeEncode? .exit).map (·.opcode) = some .Exit := by
  native_decide

/-- Concrete: `ja` keeps opcode. -/
theorem decodeEncode_ja_opcode :
    (decodeEncode? (.ja (BitVec.ofInt 16 3))).map (·.opcode) = some .Ja := by
  native_decide

/-- Whole program: encode → decode yields a program with the same length. -/
def sampleProg : Program :=
  #[
    .binImm .Mov64Imm ⟨0, by omega⟩ 2#64,
    .binImm .Add64Imm ⟨0, by omega⟩ 3#64,
    .exit
  ]

theorem redecode_sample_length :
    (redecodeProgram? sampleProg).map (·.size) = some 3 := by
  native_decide

def outcomeOf (P : Program) : Outcome :=
  (interpEntry closedExec P 40).2

/-- **Semantic preservation (concrete):** re-decoded program same halt code. -/
theorem encode_preserves_interp_sample :
    outcomeOf sampleProg = .halted 5#64 := by
  native_decide

theorem encode_preserves_interp_sample_redecode :
    (redecodeProgram? sampleProg).map outcomeOf = some (.halted 5#64) := by
  native_decide

/-- Jump program still halts the same after redecode. -/
def sampleJump : Program :=
  #[
    .binImm .Mov64Imm ⟨0, by omega⟩ 0#64,
    .jumpImm .JeqImm ⟨0, by omega⟩ 0#64 (BitVec.ofInt 16 1),
    .binImm .Add64Imm ⟨0, by omega⟩ 1#64,
    .exit
  ]

theorem encode_preserves_interp_jump :
    outcomeOf sampleJump = .halted 0#64 := by
  native_decide

theorem encode_preserves_interp_jump_redecode :
    (redecodeProgram? sampleJump).map outcomeOf = some (.halted 0#64) := by
  native_decide

/-- Memory program (stack via r10) preserves halt after redecode. -/
def sampleMem : Program :=
  #[
    .binImm .Mov64Imm ⟨0, by omega⟩ 0xab#64,
    .storeReg .Stxdw ⟨10, by omega⟩ ⟨0, by omega⟩ (BitVec.ofInt 16 (-8)),
    .loadMem .Ldxdw ⟨1, by omega⟩ ⟨10, by omega⟩ (BitVec.ofInt 16 (-8)),
    .binReg .Mov64Reg ⟨0, by omega⟩ ⟨1, by omega⟩,
    .exit
  ]

theorem encode_preserves_interp_mem :
    outcomeOf sampleMem = .halted 0xab#64 := by
  native_decide

theorem encode_preserves_interp_mem_redecode :
    (redecodeProgram? sampleMem).map outcomeOf = some (.halted 0xab#64) := by
  native_decide

/-- Single-step: re-decoded `mov64` writes the same `r0`. -/
theorem encode_preserves_execInstr_mov64 :
    let i := Instr.binImm .Mov64Imm ⟨0, by omega⟩ 7#64
    let m := Machine.entry
    let r0 := fun (m : Machine) => m.getReg ⟨0, by omega⟩
    (decodeEncode? i).bind (fun i' => (execInstr closedExec m i').map r0)
      = (execInstr closedExec m i).map r0 := by
  native_decide

end SbpfSemantics
