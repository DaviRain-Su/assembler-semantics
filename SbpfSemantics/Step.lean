import SbpfSemantics.Basic
import SbpfSemantics.Opcode
import SbpfSemantics.Instr
import SbpfSemantics.Machine
import SbpfSemantics.Dialect

/-!
# SbpfSemantics.Step

Small-step executable semantics for resolved instructions, derived from
blueshift `sbpf` `crates/common/src/execute/*`.

Ground truth for the closed dialect is the partial function `execInstr`;
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

/-- 64-bit binary op with immediate. -/
def execBin64Imm (m : Machine) (op : Opcode) (dst : Reg) (imm : Word) : Option Machine :=
  let a := m.getReg dst
  let b := imm
  match op with
  | .Add64Imm => some ((m.setReg dst (a + b)).advancePc)
  | .Sub64Imm => some ((m.setReg dst (a - b)).advancePc)
  | .Mul64Imm => some ((m.setReg dst (a * b)).advancePc)
  | .Or64Imm  => some ((m.setReg dst (a ||| b)).advancePc)
  | .And64Imm => some ((m.setReg dst (a &&& b)).advancePc)
  | .Xor64Imm => some ((m.setReg dst (a ^^^ b)).advancePc)
  | .Mov64Imm => some ((m.setReg dst b).advancePc)
  | .Lsh64Imm => some ((m.setReg dst (a <<< b.toNat)).advancePc)
  | .Rsh64Imm => some ((m.setReg dst (a >>> b.toNat)).advancePc)
  | .Arsh64Imm =>
      -- arithmetic shift: cast via signed Int
      let sh := b.toNat
      let v := BitVec.ofInt 64 (a.toInt >>> sh)
      some ((m.setReg dst v).advancePc)
  | .Div64Imm | .Mod64Imm =>
      if b == 0#64 then none
      else
        let v := if op == .Div64Imm then a / b else a % b
        some ((m.setReg dst v).advancePc)
  | .Hor64Imm => some ((m.setReg dst (a ||| (b <<< 32))).advancePc)
  | _ => none

/-- 64-bit binary op with register source. -/
def execBin64Reg (m : Machine) (op : Opcode) (dst src : Reg) : Option Machine :=
  let a := m.getReg dst
  let b := m.getReg src
  match op with
  | .Add64Reg => some ((m.setReg dst (a + b)).advancePc)
  | .Sub64Reg => some ((m.setReg dst (a - b)).advancePc)
  | .Mul64Reg => some ((m.setReg dst (a * b)).advancePc)
  | .Or64Reg  => some ((m.setReg dst (a ||| b)).advancePc)
  | .And64Reg => some ((m.setReg dst (a &&& b)).advancePc)
  | .Xor64Reg => some ((m.setReg dst (a ^^^ b)).advancePc)
  | .Mov64Reg => some ((m.setReg dst b).advancePc)
  | .Lsh64Reg => some ((m.setReg dst (a <<< b.toNat)).advancePc)
  | .Rsh64Reg => some ((m.setReg dst (a >>> b.toNat)).advancePc)
  | .Arsh64Reg =>
      let v := BitVec.ofInt 64 (a.toInt >>> b.toNat)
      some ((m.setReg dst v).advancePc)
  | .Div64Reg | .Mod64Reg =>
      if b == 0#64 then none
      else
        let v := if op == .Div64Reg then a / b else a % b
        some ((m.setReg dst v).advancePc)
  | _ => none

/-- 32-bit ALU with imm: operate on low 32, zero-extend result (sbpf convention for many ops). -/
def execBin32Imm (m : Machine) (op : Opcode) (dst : Reg) (imm : Word) : Option Machine :=
  let a32 := toWord32 (m.getReg dst)
  let b32 := toWord32 imm
  let put (v32 : Word32) := (m.setReg dst (ofWord32 v32)).advancePc
  match op with
  | .Add32Imm => some (put (a32 + b32))
  | .Sub32Imm => some (put (a32 - b32))
  | .Mul32Imm => some (put (a32 * b32))
  | .Or32Imm  => some (put (a32 ||| b32))
  | .And32Imm => some (put (a32 &&& b32))
  | .Xor32Imm => some (put (a32 ^^^ b32))
  | .Mov32Imm => some (put b32)
  | .Lsh32Imm => some (put (a32 <<< b32.toNat))
  | .Rsh32Imm => some (put (a32 >>> b32.toNat))
  | .Arsh32Imm =>
      let v := BitVec.ofInt 32 (a32.toInt >>> b32.toNat)
      some (put v)
  | .Div32Imm | .Mod32Imm =>
      if b32 == 0#32 then none
      else
        let v := if op == .Div32Imm then a32 / b32 else a32 % b32
        some (put v)
  | _ => none

def execBin32Reg (m : Machine) (op : Opcode) (dst src : Reg) : Option Machine :=
  let a32 := toWord32 (m.getReg dst)
  let b32 := toWord32 (m.getReg src)
  let put (v32 : Word32) := (m.setReg dst (ofWord32 v32)).advancePc
  match op with
  | .Add32Reg => some (put (a32 + b32))
  | .Sub32Reg => some (put (a32 - b32))
  | .Mul32Reg => some (put (a32 * b32))
  | .Or32Reg  => some (put (a32 ||| b32))
  | .And32Reg => some (put (a32 &&& b32))
  | .Xor32Reg => some (put (a32 ^^^ b32))
  | .Mov32Reg => some (put b32)
  | .Lsh32Reg => some (put (a32 <<< b32.toNat))
  | .Rsh32Reg => some (put (a32 >>> b32.toNat))
  | .Arsh32Reg =>
      let v := BitVec.ofInt 32 (a32.toInt >>> b32.toNat)
      some (put v)
  | .Div32Reg | .Mod32Reg =>
      if b32 == 0#32 then none
      else
        let v := if op == .Div32Reg then a32 / b32 else a32 % b32
        some (put v)
  | _ => none

def execUnary (m : Machine) (op : Opcode) (dst : Reg) : Option Machine :=
  match op with
  | .Neg64 =>
      let v := 0#64 - m.getReg dst
      some ((m.setReg dst v).advancePc)
  | .Neg32 =>
      let v32 := 0#32 - toWord32 (m.getReg dst)
      some ((m.setReg dst (ofWord32 v32)).advancePc)
  | _ => none

def execEndian (m : Machine) (op : Opcode) (dst : Reg) (imm : Word) : Option Machine :=
  let w := m.getReg dst
  let bits := imm.toNat
  match op, bits with
  | .Le, 16 =>
      -- little-endian convert: on LE host this is identity on the low bits
      some ((m.setReg dst (w &&& 0xffff#64)).advancePc)
  | .Le, 32 => some ((m.setReg dst (w &&& 0xffffffff#64)).advancePc)
  | .Le, 64 => some (m.advancePc)
  | .Be, 16 =>
      let x := (w &&& 0xffff#64).toNat
      let swapped := ((x &&& 0xff) <<< 8) + ((x >>> 8) &&& 0xff)
      some ((m.setReg dst (BitVec.ofNat 64 swapped)).advancePc)
  | .Be, 32 =>
      let x := (w &&& 0xffffffff#64).toNat
      let swapped :=
        ((x &&& 0xff) <<< 24) + (((x >>> 8) &&& 0xff) <<< 16) +
        (((x >>> 16) &&& 0xff) <<< 8) + ((x >>> 24) &&& 0xff)
      some ((m.setReg dst (BitVec.ofNat 64 swapped)).advancePc)
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
      some ((m.setReg dst (BitVec.ofNat 64 swapped)).advancePc)
  | _, _ => none

def condJump (m : Machine) (take : Bool) (off : Off16) : Machine :=
  if take then doJump m off else m.advancePc

def execJumpImm (m : Machine) (op : Opcode) (dst : Reg) (imm : Word) (off : Off16) : Option Machine :=
  let a := m.getReg dst
  -- 64-bit path: imm as sign-extended i32 pattern already in Word for simple imms
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

/-- Execute a single resolved instruction (no fetch). Syscalls use `D`. -/
def execInstr (_D : ExecDialect) (m : Machine) (i : Instr) : Option Machine :=
  if m.halted.isSome then none
  else
    match i.opcode.opClass with
    | .loadImm => do
        let dst ← requireReg i.dst
        let imm ← requireImm i.imm
        -- lddw
        some ((m.setReg dst imm).advancePc)
    | .loadMem => do
        let dst ← requireReg i.dst
        let src ← requireReg i.src
        let off ← requireOff i.off
        let addr := calcAddr (m.getReg src) off
        match i.opcode with
        | .Ldxb =>
            let v ← m.mem.readU8 addr
            some ((m.setReg dst v).advancePc)
        | .Ldxh =>
            let v ← m.mem.readU16 addr
            some ((m.setReg dst v).advancePc)
        | .Ldxw =>
            let v ← m.mem.readU32 addr
            some ((m.setReg dst v).advancePc)
        | .Ldxdw =>
            let v ← m.mem.readU64 addr
            some ((m.setReg dst v).advancePc)
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
        | .Lsh64Imm | .Rsh64Imm | .Arsh64Imm | .Hor64Imm =>
            execBin64Imm m i.opcode dst imm
        | .Add32Imm | .Sub32Imm | .Mul32Imm | .Div32Imm | .Mod32Imm
        | .Or32Imm | .And32Imm | .Xor32Imm | .Mov32Imm
        | .Lsh32Imm | .Rsh32Imm | .Arsh32Imm =>
            execBin32Imm m i.opcode dst imm
        | _ =>
            -- remaining specialized mul/div variants: fall back to 64/32 patterns if named
            none
    | .binReg => do
        let dst ← requireReg i.dst
        let src ← requireReg i.src
        match i.opcode with
        | .Add64Reg | .Sub64Reg | .Mul64Reg | .Div64Reg | .Mod64Reg
        | .Or64Reg | .And64Reg | .Xor64Reg | .Mov64Reg
        | .Lsh64Reg | .Rsh64Reg | .Arsh64Reg =>
            execBin64Reg m i.opcode dst src
        | .Add32Reg | .Sub32Reg | .Mul32Reg | .Div32Reg | .Mod32Reg
        | .Or32Reg | .And32Reg | .Xor32Reg | .Mov32Reg
        | .Lsh32Reg | .Rsh32Reg | .Arsh32Reg =>
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
        -- Phase 1: imm is always a relative PC offset (internal call).
        -- Named syscalls are modeled by a separate constructor later / Dialect
        -- when the assembler resolves them as `Call` with a side table.
        -- For now use Dialect only when imm is none and we pass a name via src — not used.
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
