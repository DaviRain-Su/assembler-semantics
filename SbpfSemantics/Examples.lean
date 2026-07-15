import SbpfSemantics.Interp
import SbpfSemantics.Encode

/-!
# SbpfSemantics.Examples

End-to-end smoke tests via `native_decide`, analogous to yul-semantics Examples.
-/


namespace SbpfSemantics

private def r0 : Reg := ⟨0, by omega⟩
private def r1 : Reg := ⟨1, by omega⟩
private def r2 : Reg := ⟨2, by omega⟩

/-- `mov64 r0, 42; exit` returns 42. -/
def progReturn42 : Program :=
  #[.binImm .Mov64Imm r0 42#64, .exit]

example :
    let (m, o) := interpEntry closedExec progReturn42 10
    o = .halted 42#64 ∧ m.getReg r0 = 42#64 := by
  native_decide

/-- add64 then exit: r0 = 2 + 3. -/
def progAdd : Program :=
  #[
    .binImm .Mov64Imm r0 2#64,
    .binImm .Add64Imm r0 3#64,
    .exit
  ]

example :
    (interpEntry closedExec progAdd 10).2 = .halted 5#64 := by
  native_decide

/-- Conditional jump: if r0 == 0 skip add. -/
def progJump : Program :=
  #[
    .binImm .Mov64Imm r0 0#64,
    -- jeq r0, 0, +1  (skip next)
    .jumpImm .JeqImm r0 0#64 (BitVec.ofInt 16 1),
    .binImm .Add64Imm r0 1#64,
    .exit
  ]

example :
    (interpEntry closedExec progJump 20).2 = .halted 0#64 := by
  native_decide

/-- Internal call: call +1; callee sets r0=7; exit returns to exit. -/
def progCall : Program :=
  #[
    -- 0: call +1  (to index 2)
    .callRel 1#64,
    -- 1: exit (return here after callee)
    .exit,
    -- 2: mov64 r0, 7; exit (returns)
    .binImm .Mov64Imm r0 7#64,
    .exit
  ]

example :
    (interpEntry closedExec progCall 20).2 = .halted 7#64 := by
  native_decide

/-- Encode/decode recovers `Mov64Imm` opcode. -/
example :
    (decodeInstr? (encodeInstr (.binImm .Mov64Imm r0 42#64)) 0).map (·.1.opcode)
      = some .Mov64Imm := by
  native_decide

/-- Memory store/load on stack via FP (r10). -/
def progMem : Program :=
  #[
    -- stxdw [r10-8], r1  but r1 is input ptr; use r0
    .binImm .Mov64Imm r0 0xdeadbeef#64,
    .storeReg .Stxdw ⟨10, by omega⟩ r0 (BitVec.ofInt 16 (-8)),
    .loadMem .Ldxdw r1 ⟨10, by omega⟩ (BitVec.ofInt 16 (-8)),
    .binReg .Mov64Reg r0 r1,
    .exit
  ]

example :
    (interpEntry closedExec progMem 20).2 = .halted 0xdeadbeef#64 := by
  native_decide

end SbpfSemantics
