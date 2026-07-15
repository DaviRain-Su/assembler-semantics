import SbpfSemantics.WellFormed
import SbpfSemantics.Encode
import SbpfSemantics.Step
import SbpfSemantics.Interp
import SbpfSemantics.Host

/-!
# SbpfSemantics.EncodePreserve

**V3-safe encode/decode round-trip** and **execution preservation**.

Decode does not recover bit-identical `Instr` values: unused operands become
zeros/`some r0`, and non-`lddw` immediates are sign-extended from 32 bits.
We therefore compare instructions up to **execution-relevant** fields
(`sameExec`):

1. Encodable samples satisfy `roundTripSameExec`.
2. After `decodeEncode?`, closed-world `execInstr` agrees on registers / halt / pc.
-/

namespace SbpfSemantics

/-- Decode after encode. -/
def decodeEncode? (i : Instr) : Option Instr :=
  (decodeInstr? (encodeInstr i) 0).map (·.1)

/-- Program re-decoded from its own encoding. -/
def redecodeProgram? (P : Program) : Option Program :=
  decodeProgram? (encodeProgram P)

/-- Canonical form: encode then decode. -/
def Instr.normalize? (i : Instr) : Option Instr :=
  decodeEncode? i

/-- Execution-relevant field agreement (per `opClass`). -/
def Instr.sameExec (i j : Instr) : Bool :=
  i.opcode == j.opcode &&
  match i.opcode.opClass with
  | .loadImm => i.dst == j.dst && i.imm == j.imm
  | .loadMem => i.dst == j.dst && i.src == j.src && i.off == j.off
  | .storeImm => i.dst == j.dst && i.off == j.off && i.imm == j.imm
  | .storeReg => i.dst == j.dst && i.src == j.src && i.off == j.off
  | .binImm => i.dst == j.dst && i.imm == j.imm
  | .binReg => i.dst == j.dst && i.src == j.src
  | .unary => i.dst == j.dst
  | .endian => i.dst == j.dst && i.imm == j.imm
  | .jump => i.off == j.off
  | .jumpImm | .jump32Imm => i.dst == j.dst && i.imm == j.imm && i.off == j.off
  | .jumpReg | .jump32Reg => i.dst == j.dst && i.src == j.src && i.off == j.off
  | .callImm => i.imm == j.imm && i.syscall == j.syscall
  | .callReg => i.dst == j.dst
  | .exit => true

/-- `decodeEncode?` succeeds and result is `sameExec`-equal. -/
def roundTripSameExec (i : Instr) : Bool :=
  match decodeEncode? i with
  | some j => Instr.sameExec i j
  | none => false

private def r0 : Reg := ⟨0, by omega⟩
private def r1 : Reg := ⟨1, by omega⟩
private def r2 : Reg := ⟨2, by omega⟩

/-- Representative encodable instructions across op classes. -/
def encodePreserveSamples : Array Instr := #[
  .binImm .Mov64Imm r0 1#64,
  .binImm .Add64Imm r1 7#64,
  .binImm .Lmul64Imm r0 3#64,
  .binImm .Xor64Imm r0 0xff#64,
  .binReg .Sub64Reg r0 r1,
  .binReg .Mov32Reg r0 r1,
  .lddw r2 0xdeadbeefcafebabe#64,
  .loadMem .Ldxb r0 r1 4#16,
  .loadMem .Ldxdw r0 r1 (BitVec.ofInt 16 (-8)),
  .storeImm .Stw r1 0#16 0#64,
  .storeReg .Stxb r1 r0 1#16,
  .storeReg .Stxdw r1 r0 0#16,
  .unary .Neg32 r0,
  .unary .Neg64 r0,
  .ja 5#16,
  .ja (BitVec.ofInt 16 (-3)),
  .jumpImm .JneImm r0 0#64 (BitVec.ofInt 16 (-1)),
  .jumpImm .JeqImm r0 0#64 (BitVec.ofInt 16 2),
  .jumpReg .JeqReg r0 r1 2#16,
  .jumpImm .Jgt32Imm r0 9#64 0#16,
  .jumpImm .Jeq32Imm r0 1#64 (BitVec.ofInt 16 1),
  .callRel 4#64,
  .callRel (BitVec.ofInt 64 (-2)),
  .callx r2,
  .exit,
  { opcode := .Le, dst := some r0, imm := some 32#64 },
  { opcode := .Be, dst := some r0, imm := some 64#64 }
]

theorem samples_all_encodable :
    encodePreserveSamples.all Instr.encodable = true := by
  native_decide

theorem samples_all_roundTrip :
    encodePreserveSamples.all roundTripSameExec = true := by
  native_decide

/-- After normalize, unused fields may differ; `sameExec` still holds. -/
def add64_normalize_differs_structurally : Bool :=
  let i := Instr.binImm .Add64Imm r1 1#64
  match decodeEncode? i with
  | none => false
  | some j => (!decide (i = j)) && Instr.sameExec i j

example : add64_normalize_differs_structurally = true := by native_decide

/-! ### Execution preservation -/

/-- Compare closed-world step results on r0 / halted / pc. -/
def execAgree (i j : Instr) (m : Machine) : Bool :=
  match execInstr closedExec m i, execInstr closedExec m j with
  | none, none => true
  | some m1, some m2 =>
      m1.getReg r0 == m2.getReg r0 &&
      m1.getReg r1 == m2.getReg r1 &&
      m1.halted == m2.halted &&
      m1.pc == m2.pc
  | _, _ => false

def execPreserveSample (i : Instr) : Bool :=
  match decodeEncode? i with
  | none => false
  | some j =>
      let m := (Machine.entry).setReg r0 2#64 |>.setReg r1 3#64
      execAgree i j m

theorem exec_preserve_batch :
    encodePreserveSamples.all execPreserveSample = true := by
  native_decide

theorem exec_preserves_mov64 :
    let i := Instr.binImm .Mov64Imm r0 99#64
    execPreserveSample i = true := by
  native_decide

theorem exec_preserves_add64 :
    let i := Instr.binImm .Add64Imm r0 5#64
    execPreserveSample i = true := by
  native_decide

theorem exec_preserves_lddw :
    let i := Instr.lddw r1 0xabc#64
    execPreserveSample i = true := by
  native_decide

theorem exec_preserves_exit :
    execPreserveSample .exit = true := by
  native_decide

/-- Program-level: redecode preserves closed interp halt. -/
theorem redecode_preserves_program :
    let P : Program := #[
      .binImm .Mov64Imm r0 4#64,
      .binImm .Mul64Imm r0 2#64,
      .exit
    ]
    let o1 := (interpEntry closedExec P 20).2
    let o2 :=
      match redecodeProgram? P with
      | some P' => (interpEntry closedExec P' 20).2
      | none => Outcome.stuck
    (o1 == Outcome.halted 8#64) && (o2 == Outcome.halted 8#64) = true := by
  native_decide

/-- Non-encodable (displaced V3) fails round-trip under `sameExec` for original opcode. -/
example :
    roundTripSameExec (.binImm .Udiv32Imm r0 1#64) = false := by
  native_decide

/-- Host syscall names do not encode. -/
example :
    roundTripSameExec (.callSyscall "sol_log_") = false := by
  native_decide

end SbpfSemantics
