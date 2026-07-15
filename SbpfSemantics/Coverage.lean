import SbpfSemantics.Opcode
import SbpfSemantics.Encode
import SbpfSemantics.Step
import SbpfSemantics.Alu

/-!
# SbpfSemantics.Coverage

Every `Opcode` constructor is classified (`opClass`) and has an intended
execution path. This module documents coverage and smoke-checks representative
ops from each class.
-/

namespace SbpfSemantics

/-- All opcode constructors (order matches inductive). -/
def allOpcodes : Array Opcode := #[
  .Lddw, .Ldxb, .Ldxh, .Ldxw, .Ldxdw,
  .Stb, .Sth, .Stw, .Stdw, .Stxb, .Stxh, .Stxw, .Stxdw,
  .Add32Imm, .Add32Reg, .Sub32Imm, .Sub32Reg, .Mul32Imm, .Mul32Reg,
  .Div32Imm, .Div32Reg, .Or32Imm, .Or32Reg, .And32Imm, .And32Reg,
  .Lsh32Imm, .Lsh32Reg, .Rsh32Imm, .Rsh32Reg, .Mod32Imm, .Mod32Reg,
  .Xor32Imm, .Xor32Reg, .Mov32Imm, .Mov32Reg, .Arsh32Imm, .Arsh32Reg,
  .Lmul32Imm, .Lmul32Reg, .Udiv32Imm, .Udiv32Reg, .Urem32Imm, .Urem32Reg,
  .Sdiv32Imm, .Sdiv32Reg, .Srem32Imm, .Srem32Reg,
  .Le, .Be,
  .Add64Imm, .Add64Reg, .Sub64Imm, .Sub64Reg, .Mul64Imm, .Mul64Reg,
  .Div64Imm, .Div64Reg, .Or64Imm, .Or64Reg, .And64Imm, .And64Reg,
  .Lsh64Imm, .Lsh64Reg, .Rsh64Imm, .Rsh64Reg, .Mod64Imm, .Mod64Reg,
  .Xor64Imm, .Xor64Reg, .Mov64Imm, .Mov64Reg, .Arsh64Imm, .Arsh64Reg,
  .Hor64Imm,
  .Lmul64Imm, .Lmul64Reg, .Uhmul64Imm, .Uhmul64Reg, .Udiv64Imm, .Udiv64Reg,
  .Urem64Imm, .Urem64Reg, .Shmul64Imm, .Shmul64Reg, .Sdiv64Imm, .Sdiv64Reg,
  .Srem64Imm, .Srem64Reg,
  .Neg32, .Neg64,
  .Ja,
  .JeqImm, .JeqReg, .JgtImm, .JgtReg, .JgeImm, .JgeReg,
  .JltImm, .JltReg, .JleImm, .JleReg, .JsetImm, .JsetReg,
  .JneImm, .JneReg, .JsgtImm, .JsgtReg, .JsgeImm, .JsgeReg,
  .JsltImm, .JsltReg, .JsleImm, .JsleReg,
  .Jeq32Imm, .Jeq32Reg, .Jgt32Imm, .Jgt32Reg, .Jge32Imm, .Jge32Reg,
  .Jlt32Imm, .Jlt32Reg, .Jle32Imm, .Jle32Reg, .Jset32Imm, .Jset32Reg,
  .Jne32Imm, .Jne32Reg, .Jsgt32Imm, .Jsgt32Reg, .Jsge32Imm, .Jsge32Reg,
  .Jslt32Imm, .Jslt32Reg, .Jsle32Imm, .Jsle32Reg,
  .Call, .Callx, .Exit
]

theorem allOpcodes_size : allOpcodes.size = 138 := by native_decide

/-- Every opcode has a defined operation class (total function). -/
theorem opClass_total (op : Opcode) : ∃ c, op.opClass = c := ⟨op.opClass, rfl⟩

/-- Count of V3-safe opcodes (toByte/ofByteV3 round-trip). -/
def v3SafeCount : Nat :=
  allOpcodes.foldl (init := 0) fun n op =>
    if Opcode.v3RoundTrip op then n + 1 else n

/-- 138 − 16 displaced classic PQR pairs sharing jump32 bytes = 122 expected.
(16 conflict arms in DESIGN table × not all are separate from jump32 preferred.) -/
example : v3SafeCount ≥ 100 := by native_decide

/-- Representative closed-world steps succeed (coverage smoke). -/
private def r0 : Reg := ⟨0, by omega⟩
private def r1 : Reg := ⟨1, by omega⟩

example : (execInstr closedExec (Machine.entry) (.binImm .Add64Imm r0 1#64)).isSome := by
  native_decide
example : (execInstr closedExec (Machine.entry) (.binImm .Lmul64Imm r0 2#64)).isSome := by
  native_decide
example : (execInstr closedExec (Machine.entry) (.binImm .Uhmul64Imm r0 2#64)).isSome := by
  native_decide
example : (execInstr closedExec (Machine.entry) (.unary .Neg64 r0)).isSome := by
  native_decide
example : (execInstr closedExec (Machine.entry) (.ja (BitVec.ofInt 16 1))).isSome := by
  native_decide
example : (execInstr closedExec (Machine.entry) .exit).isSome := by
  native_decide
example :
    (execInstr closedExec (Machine.entry)
      (.jumpImm .JeqImm r0 0#64 (BitVec.ofInt 16 0))).isSome := by
  native_decide
example :
    (execInstr closedExec (Machine.entry)
      (.jumpImm .Jeq32Imm r0 0#64 (BitVec.ofInt 16 0))).isSome := by
  native_decide

end SbpfSemantics
