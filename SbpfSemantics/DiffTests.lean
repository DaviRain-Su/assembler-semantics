import SbpfSemantics.Interp
import SbpfSemantics.Alu
import SbpfSemantics.Host

/-!
# SbpfSemantics.DiffTests

Golden execution traces for differential testing against blueshift `sbpf`
(`crates/common` execute tests) and hand-checked PQR cases (SIMD-0174).

These are Lean-native oracles: values mirror Rust unit tests such as
`test_add64_imm` (r1: 5 + 10 = 15). A future harness can feed the same
vectors into `SbpfVm` and compare.
-/

namespace SbpfSemantics.DiffTests

open SbpfSemantics

private def r0 : Reg := ⟨0, by omega⟩
private def r1 : Reg := ⟨1, by omega⟩
private def r2 : Reg := ⟨2, by omega⟩

/-- Run one instruction on a machine with given `r1`, return new `r1`. -/
def stepR1 (op : Opcode) (imm : Word) (r1val : Word) : Option Word :=
  let m0 := (Machine.entry).setReg r1 r1val
  let i := Instr.binImm op r1 imm
  (execInstr closedExec m0 i).map (·.getReg r1)

/-- From sbpf `test_add64_imm`: r1=5, add64 10 → 15. -/
example : stepR1 .Add64Imm 10#64 5#64 = some 15#64 := by native_decide

/-- From sbpf `test_sub64_imm`: r1=10, sub64 3 → 7. -/
example : stepR1 .Sub64Imm 3#64 10#64 = some 7#64 := by native_decide

/-- From sbpf `test_mul64_imm`: r1=6, mul64 5 → 30. -/
example : stepR1 .Mul64Imm 5#64 6#64 = some 30#64 := by native_decide

/-- From sbpf `test_div64_imm`: r1=20, div64 5 → 4. -/
example : stepR1 .Div64Imm 5#64 20#64 = some 4#64 := by native_decide

/-- Division by zero stuck. -/
example : stepR1 .Div64Imm 0#64 10#64 = none := by native_decide

/-- From sbpf `test_or64_imm`: r1=0xf0, or64 0x0f → 0xff. -/
example : stepR1 .Or64Imm 0x0f#64 0xf0#64 = some 0xff#64 := by native_decide

/-- From sbpf `test_and64_imm`: r1=0xff, and64 0x0f → 0x0f. -/
example : stepR1 .And64Imm 0x0f#64 0xff#64 = some 0x0f#64 := by native_decide

/-- From sbpf `test_lsh64_imm`: r1=1, lsh64 4 → 0x10. -/
example : stepR1 .Lsh64Imm 4#64 1#64 = some 0x10#64 := by native_decide

/-- From sbpf `test_rsh64_imm`: r1=0xf0, rsh64 4 → 0x0f. -/
example : stepR1 .Rsh64Imm 4#64 0xf0#64 = some 0x0f#64 := by native_decide

/-- From sbpf `test_mod64_imm`: r1=15, mod64 7 → 1. -/
example : stepR1 .Mod64Imm 7#64 15#64 = some 1#64 := by native_decide

/-- Arithmetic shift: -16 >>> 2 → -4. -/
example :
    stepR1 .Arsh64Imm 2#64 (BitVec.ofInt 64 (-16)) = some (BitVec.ofInt 64 (-4)) := by
  native_decide

/-- From sbpf `test_add32_imm`: r1=5, add32 10 → 15. -/
example : stepR1 .Add32Imm 10#64 5#64 = some 15#64 := by native_decide

/-- mul32 imm sign-extends. -/
example : stepR1 .Mul32Imm 5#64 6#64 = some 30#64 := by native_decide

/-- Unary neg64. -/
example :
    let m0 := (Machine.entry).setReg r1 5#64
    (execInstr closedExec m0 (.unary .Neg64 r1)).map (·.getReg r1) =
      some (BitVec.ofInt 64 (-5)) := by
  native_decide

/-- PQR: lmul64 same as low 64 of product. -/
example : stepR1 .Lmul64Imm 5#64 6#64 = some 30#64 := by native_decide

/-- PQR: udiv64. -/
example : stepR1 .Udiv64Imm 5#64 20#64 = some 4#64 := by native_decide

/-- PQR: uhmul64 — high half of 2^32 * 2^32 = 2^64 → high = 1. -/
example : stepR1 .Uhmul64Imm (1#64 <<< 32) (1#64 <<< 32) = some 1#64 := by native_decide

/-- PQR: sdiv64 of -10 / 3 → -3 (toward zero). -/
example :
    stepR1 .Sdiv64Imm 3#64 (BitVec.ofInt 64 (-10)) = some (BitVec.ofInt 64 (-3)) := by
  native_decide

/-- Full program: mov/add/exit matching combined sbpf-style trace. -/
def progTrace : Program :=
  #[
    .binImm .Mov64Imm r0 5#64,
    .binImm .Add64Imm r0 10#64,
    .exit
  ]

example : (interpEntry closedExec progTrace 10).2 = .halted 15#64 := by native_decide

/-- lddw + add (byte-wide insn). -/
def progLddw : Program :=
  #[.lddw r0 0x100#64, .binImm .Add64Imm r0 1#64, .exit]

example : (interpEntry closedExec progLddw 10).2 = .halted 0x101#64 := by native_decide

/-- Internal call + exit. -/
def progCall : Program :=
  #[.callRel 1#64, .exit, .binImm .Mov64Imm r0 7#64, .exit]

example : (interpEntry closedExec progCall 20).2 = .halted 7#64 := by native_decide

/-- Syscall stub: log then exit with r0 unchanged except syscall return 0. -/
def progLog : Program :=
  #[
    .binImm .Mov64Imm r0 99#64,
    .callSyscall "sol_log_",
    .exit
  ]

example : (interpEntry stubExec progLog 10).2 = .halted 0#64 := by native_decide

/-- Closed dialect sticks on syscall. -/
example : (interpEntry closedExec progLog 10).2 = .stuck := by native_decide

/-- abort is stuck under stubExec (no halt). -/
def progAbort : Program := #[.callSyscall "abort", .exit]

example : (interpEntry stubExec progAbort 5).2 = .stuck := by native_decide

/-- abort under hostExec halts the machine. -/
example : (interpEntry hostExec progAbort 5).2 = .halted 1#64 := by native_decide

/-- memset via host: write 4 bytes of 0xab at FP-8, load back low byte. -/
def progMemset : Program :=
  #[
    -- r1 = dst = r10 - 8, r2 = c = 0xab, r3 = n = 4
    .binReg .Mov64Reg r1 ⟨10, by omega⟩,
    .binImm .Add64Imm r1 (BitVec.ofInt 64 (-8)),
    .binImm .Mov64Imm r2 0xab#64,
    .binImm .Mov64Imm ⟨3, by omega⟩ 4#64,
    .callSyscall "sol_memset_",
    .loadMem .Ldxb r0 ⟨10, by omega⟩ (BitVec.ofInt 16 (-8)),
    .exit
  ]

example : (interpEntry hostExec progMemset 40).2 = .halted 0xab#64 := by native_decide

end SbpfSemantics.DiffTests
