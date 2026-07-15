import SbpfSemantics.Basic
import SbpfSemantics.Opcode
import SbpfSemantics.Instr
import SbpfSemantics.Machine
import SbpfSemantics.Dialect
import SbpfSemantics.Alu

/-!
# SbpfSemantics.Step

Small-step executable semantics for resolved instructions, derived from
blueshift `sbpf` `crates/common/src/execute/*` (classic) and SIMD-0174 (PQR).

Ground truth for an `ExecDialect` is the partial function `execStep`;
the relational form is `Step D P m m'`.
-/

namespace SbpfSemantics

/-- Fetch instruction at PC. -/
def fetch (P : Program) (m : Machine) : Option Instr :=
  if m.halted.isSome then none else P[m.pc]?

private def requireReg (r? : Option Reg) : Option Reg := r?
private def requireOff (o? : Option Off16) : Option Off16 := o?
private def requireImm (i? : Option Word) : Option Word := i?

/-- Jump: PC := PC + 1 + signed_off. -/
def doJump (m : Machine) (off : Off16) : Machine :=
  let pc' := (m.pc : Int) + 1 + off.toInt
  m.setPc pc'.toNat

def execEndian (m : Machine) (op : Opcode) (dst : Reg) (imm : Word) : Option Machine :=
  let w := m.getReg dst
  let bits := imm.toNat
  match op, bits with
  | .Le, 16 => some (put64 m dst (w &&& 0xffff#64))
  | .Le, 32 => some (put64 m dst (w &&& 0xffffffff#64))
  | .Le, 64 => some (m.advancePc)
  | .Be, 16 =>
      let x := (w &&& 0xffff#64).toNat
      let swapped := ((x &&& 0xff) <<< 8) + ((x >>> 8) &&& 0xff)
      some (put64 m dst (BitVec.ofNat 64 swapped))
  | .Be, 32 =>
      let x := (w &&& 0xffffffff#64).toNat
      let swapped :=
        ((x &&& 0xff) <<< 24) + (((x >>> 8) &&& 0xff) <<< 16) +
        (((x >>> 16) &&& 0xff) <<< 8) + ((x >>> 24) &&& 0xff)
      some (put64 m dst (BitVec.ofNat 64 swapped))
  | .Be, 64 =>
      let x := w.toNat
      let b0 := x &&& 0xff
      let b1 := (x >>> 8) &&& 0xff
      let b2 := (x >>> 16) &&& 0xff
      let b3 := (x >>> 24) &&& 0xff
      let b4 := (x >>> 32) &&& 0xff
      let b5 := (x >>> 40) &&& 0xff
      let b6 := (x >>> 48) &&& 0xff
      let b7 := (x >>> 56) &&& 0xff
      let swapped :=
        (b0 <<< 56) + (b1 <<< 48) + (b2 <<< 40) + (b3 <<< 32) +
        (b4 <<< 24) + (b5 <<< 16) + (b6 <<< 8) + b7
      some (put64 m dst (BitVec.ofNat 64 swapped))
  | _, _ => none

def condJump (m : Machine) (take : Bool) (off : Off16) : Machine :=
  if take then doJump m off else m.advancePc

def execJumpImm (m : Machine) (op : Opcode) (dst : Reg) (imm : Word) (off : Off16) : Option Machine :=
  let a := m.getReg dst
  let b := imm
  let a32 := toWord32 a
  let b32 := toWord32 imm
  match op with
  | .JeqImm  => some (condJump m (a == b) off)
  | .JneImm  => some (condJump m (a != b) off)
  | .JgtImm  => some (condJump m (a > b) off)
  | .JgeImm  => some (condJump m (a ≥ b) off)
  | .JltImm  => some (condJump m (a < b) off)
  | .JleImm  => some (condJump m (a ≤ b) off)
  | .JsetImm => some (condJump m ((a &&& b) != 0#64) off)
  | .JsgtImm => some (condJump m (a.toInt > b.toInt) off)
  | .JsgeImm => some (condJump m (a.toInt ≥ b.toInt) off)
  | .JsltImm => some (condJump m (a.toInt < b.toInt) off)
  | .JsleImm => some (condJump m (a.toInt ≤ b.toInt) off)
  | .Jeq32Imm  => some (condJump m (a32 == b32) off)
  | .Jne32Imm  => some (condJump m (a32 != b32) off)
  | .Jgt32Imm  => some (condJump m (a32 > b32) off)
  | .Jge32Imm  => some (condJump m (a32 ≥ b32) off)
  | .Jlt32Imm  => some (condJump m (a32 < b32) off)
  | .Jle32Imm  => some (condJump m (a32 ≤ b32) off)
  | .Jset32Imm => some (condJump m ((a32 &&& b32) != 0#32) off)
  | .Jsgt32Imm => some (condJump m (a32.toInt > b32.toInt) off)
  | .Jsge32Imm => some (condJump m (a32.toInt ≥ b32.toInt) off)
  | .Jslt32Imm => some (condJump m (a32.toInt < b32.toInt) off)
  | .Jsle32Imm => some (condJump m (a32.toInt ≤ b32.toInt) off)
  | _ => none

def execJumpReg (m : Machine) (op : Opcode) (dst src : Reg) (off : Off16) : Option Machine :=
  let a := m.getReg dst
  let b := m.getReg src
  let a32 := toWord32 a
  let b32 := toWord32 b
  match op with
  | .JeqReg  => some (condJump m (a == b) off)
  | .JneReg  => some (condJump m (a != b) off)
  | .JgtReg  => some (condJump m (a > b) off)
  | .JgeReg  => some (condJump m (a ≥ b) off)
  | .JltReg  => some (condJump m (a < b) off)
  | .JleReg  => some (condJump m (a ≤ b) off)
  | .JsetReg => some (condJump m ((a &&& b) != 0#64) off)
  | .JsgtReg => some (condJump m (a.toInt > b.toInt) off)
  | .JsgeReg => some (condJump m (a.toInt ≥ b.toInt) off)
  | .JsltReg => some (condJump m (a.toInt < b.toInt) off)
  | .JsleReg => some (condJump m (a.toInt ≤ b.toInt) off)
  | .Jeq32Reg  => some (condJump m (a32 == b32) off)
  | .Jne32Reg  => some (condJump m (a32 != b32) off)
  | .Jgt32Reg  => some (condJump m (a32 > b32) off)
  | .Jge32Reg  => some (condJump m (a32 ≥ b32) off)
  | .Jlt32Reg  => some (condJump m (a32 < b32) off)
  | .Jle32Reg  => some (condJump m (a32 ≤ b32) off)
  | .Jset32Reg => some (condJump m ((a32 &&& b32) != 0#32) off)
  | .Jsgt32Reg => some (condJump m (a32.toInt > b32.toInt) off)
  | .Jsge32Reg => some (condJump m (a32.toInt ≥ b32.toInt) off)
  | .Jslt32Reg => some (condJump m (a32.toInt < b32.toInt) off)
  | .Jsle32Reg => some (condJump m (a32.toInt ≤ b32.toInt) off)
  | _ => none

/-- Internal relative call: imm is instruction-offset (signed). -/
def execCallRel (m : Machine) (off : Word) : Option Machine := do
  let fr : CallFrame := {
    returnPc := m.pc + 1
    savedR6 := m.getReg ⟨6, by omega⟩
    savedR7 := m.getReg ⟨7, by omega⟩
    savedR8 := m.getReg ⟨8, by omega⟩
    savedR9 := m.getReg ⟨9, by omega⟩
    savedFp := m.getReg ⟨10, by omega⟩
  }
  let m ← m.pushFrame fr
  let m := m.setReg ⟨10, by omega⟩ (fr.savedFp + stackFrameSize)
  let target := (m.pc : Int) + 1 + off.toInt
  pure (m.setPc target.toNat)

/-- Host syscall via dialect; return value written to `r0`. -/
def execSyscall (D : ExecDialect) (m : Machine) (name : String) : Option Machine := do
  let (m', r) ← D.syscallFn name m
  some ((m'.setReg ⟨0, by omega⟩ r).advancePc)

def execCallx (m : Machine) (r : Reg) : Option Machine := do
  if r.val ≥ 10 then none
  else
    let target := (m.getReg r).toNat
    let fr : CallFrame := {
      returnPc := m.pc + 1
      savedR6 := m.getReg ⟨6, by omega⟩
      savedR7 := m.getReg ⟨7, by omega⟩
      savedR8 := m.getReg ⟨8, by omega⟩
      savedR9 := m.getReg ⟨9, by omega⟩
      savedFp := m.getReg ⟨10, by omega⟩
    }
    let m ← m.pushFrame fr
    let m := m.setReg ⟨10, by omega⟩ (fr.savedFp + stackFrameSize)
    pure (m.setPc target)

def execExit (m : Machine) : Option Machine :=
  match m.popFrame with
  | some (fr, m) =>
      let m := m.setReg ⟨6, by omega⟩ fr.savedR6
      let m := m.setReg ⟨7, by omega⟩ fr.savedR7
      let m := m.setReg ⟨8, by omega⟩ fr.savedR8
      let m := m.setReg ⟨9, by omega⟩ fr.savedR9
      let m := m.setReg ⟨10, by omega⟩ fr.savedFp
      some (m.setPc fr.returnPc)
  | none =>
      some (m.halt (m.getReg ⟨0, by omega⟩))

/-- Execute a single resolved instruction (no fetch). -/
def execInstr (D : ExecDialect) (m : Machine) (i : Instr) : Option Machine :=
  if m.halted.isSome then none
  else
    match i.opcode.opClass with
    | .loadImm => do
        let dst ← requireReg i.dst
        let imm ← requireImm i.imm
        some (put64 m dst imm)
    | .loadMem => do
        let dst ← requireReg i.dst
        let src ← requireReg i.src
        let off ← requireOff i.off
        let addr := calcAddr (m.getReg src) off
        match i.opcode with
        | .Ldxb =>
            let v ← m.mem.readU8 addr
            some (put64 m dst v)
        | .Ldxh =>
            let v ← m.mem.readU16 addr
            some (put64 m dst v)
        | .Ldxw =>
            let v ← m.mem.readU32 addr
            some (put64 m dst v)
        | .Ldxdw =>
            let v ← m.mem.readU64 addr
            some (put64 m dst v)
        | _ => none
    | .storeImm => do
        let dst ← requireReg i.dst
        let off ← requireOff i.off
        let imm ← requireImm i.imm
        let addr := calcAddr (m.getReg dst) off
        match i.opcode with
        | .Stb =>
            let mem ← m.mem.writeU8 addr imm
            some ({ m with mem := mem }.advancePc)
        | .Sth =>
            let mem ← m.mem.writeU16 addr imm
            some ({ m with mem := mem }.advancePc)
        | .Stw =>
            let mem ← m.mem.writeU32 addr imm
            some ({ m with mem := mem }.advancePc)
        | .Stdw =>
            let mem ← m.mem.writeU64 addr imm
            some ({ m with mem := mem }.advancePc)
        | _ => none
    | .storeReg => do
        let dst ← requireReg i.dst
        let src ← requireReg i.src
        let off ← requireOff i.off
        let addr := calcAddr (m.getReg dst) off
        let v := m.getReg src
        match i.opcode with
        | .Stxb =>
            let mem ← m.mem.writeU8 addr v
            some ({ m with mem := mem }.advancePc)
        | .Stxh =>
            let mem ← m.mem.writeU16 addr v
            some ({ m with mem := mem }.advancePc)
        | .Stxw =>
            let mem ← m.mem.writeU32 addr v
            some ({ m with mem := mem }.advancePc)
        | .Stxdw =>
            let mem ← m.mem.writeU64 addr v
            some ({ m with mem := mem }.advancePc)
        | _ => none
    | .binImm => do
        let dst ← requireReg i.dst
        let imm ← requireImm i.imm
        match i.opcode with
        | .Add64Imm | .Sub64Imm | .Mul64Imm | .Div64Imm | .Mod64Imm
        | .Or64Imm | .And64Imm | .Xor64Imm | .Mov64Imm
        | .Lsh64Imm | .Rsh64Imm | .Arsh64Imm | .Hor64Imm
        | .Lmul64Imm | .Uhmul64Imm | .Udiv64Imm | .Urem64Imm
        | .Shmul64Imm | .Sdiv64Imm | .Srem64Imm =>
            execBin64Imm m i.opcode dst imm
        | .Add32Imm | .Sub32Imm | .Mul32Imm | .Div32Imm | .Mod32Imm
        | .Or32Imm | .And32Imm | .Xor32Imm | .Mov32Imm
        | .Lsh32Imm | .Rsh32Imm | .Arsh32Imm
        | .Lmul32Imm | .Udiv32Imm | .Urem32Imm | .Sdiv32Imm | .Srem32Imm =>
            execBin32Imm m i.opcode dst imm
        | _ => none
    | .binReg => do
        let dst ← requireReg i.dst
        let src ← requireReg i.src
        match i.opcode with
        | .Add64Reg | .Sub64Reg | .Mul64Reg | .Div64Reg | .Mod64Reg
        | .Or64Reg | .And64Reg | .Xor64Reg | .Mov64Reg
        | .Lsh64Reg | .Rsh64Reg | .Arsh64Reg
        | .Lmul64Reg | .Uhmul64Reg | .Udiv64Reg | .Urem64Reg
        | .Shmul64Reg | .Sdiv64Reg | .Srem64Reg =>
            execBin64Reg m i.opcode dst src
        | .Add32Reg | .Sub32Reg | .Mul32Reg | .Div32Reg | .Mod32Reg
        | .Or32Reg | .And32Reg | .Xor32Reg | .Mov32Reg
        | .Lsh32Reg | .Rsh32Reg | .Arsh32Reg
        | .Lmul32Reg | .Udiv32Reg | .Urem32Reg | .Sdiv32Reg | .Srem32Reg =>
            execBin32Reg m i.opcode dst src
        | _ => none
    | .unary => do
        let dst ← requireReg i.dst
        execUnary m i.opcode dst
    | .endian => do
        let dst ← requireReg i.dst
        let imm ← requireImm i.imm
        execEndian m i.opcode dst imm
    | .jump => do
        let off ← requireOff i.off
        some (doJump m off)
    | .jumpImm | .jump32Imm => do
        let dst ← requireReg i.dst
        let imm ← requireImm i.imm
        let off ← requireOff i.off
        execJumpImm m i.opcode dst imm off
    | .jumpReg | .jump32Reg => do
        let dst ← requireReg i.dst
        let src ← requireReg i.src
        let off ← requireOff i.off
        execJumpReg m i.opcode dst src off
    | .callImm =>
        match i.syscall with
        | some name => execSyscall D m name
        | none =>
          match i.imm with
          | some off => execCallRel m off
          | none => none
    | .callReg => do
        let r ← requireReg i.dst
        execCallx m r
    | .exit => execExit m

/-- One machine step: fetch + execute. -/
def execStep (D : ExecDialect) (P : Program) (m : Machine) : Option Machine := do
  let i ← fetch P m
  execInstr D m i

/-- Relational small-step: the graph of `execStep`. -/
def Step (D : ExecDialect) (P : Program) (m m' : Machine) : Prop :=
  execStep D P m = some m'

/-- Determinism of a single step (immediate from `Option`). -/
theorem Step.det (D : ExecDialect) (P : Program) (m m₁ m₂ : Machine)
    (h1 : Step D P m m₁) (h2 : Step D P m m₂) : m₁ = m₂ := by
  simp only [Step] at h1 h2
  exact Option.some.inj (h1.symm.trans h2)

end SbpfSemantics
