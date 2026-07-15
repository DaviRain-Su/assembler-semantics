import SbpfSemantics.Basic
import SbpfSemantics.Opcode
import SbpfSemantics.Machine

/-!
# SbpfSemantics.Alu

ALU / PQR helpers used by `Step`.

* **Classic** ops (`add`/`mul`/`div`/`mod`/`neg`, …) follow blueshift
  `crates/common/src/execute/alu{32,64}.rs` so fixtures can match that VM.
* **PQR** ops (`lmul`/`uhmul`/`shmul`/`udiv`/`sdiv`/…) follow
  [SIMD-0174](https://github.com/solana-foundation/solana-improvement-documents/blob/main/proposals/0174-sbpf-arithmetics-improvements.md)
  (not yet executed in blueshift `execute/*`).
-/

namespace SbpfSemantics

/-- Zero-extend low 32 bits into a word. -/
def zext32 (w : Word32) : Word := ofWord32 w

/-- Sign-extend low 32 bits of a word into a full word (V3 `mov32` reg). -/
def sext32Word (w : Word) : Word :=
  BitVec.signExtend 64 (toWord32 w)

/-- `i32` min as `Word32`. -/
def word32Min : Word32 := BitVec.ofInt 32 (Int.neg (2 ^ 31))

/-- `i64` min as `Word`. -/
def word64Min : Word := BitVec.ofInt 64 (Int.neg (2 ^ 63))

/-- Toward-zero signed division on `Int` (hardware-like). -/
def intTdiv (a b : Int) : Int := Int.tdiv a b

def intTmod (a b : Int) : Int := Int.tmod a b

/-- High 64 bits of unsigned 64×64 → 128 product. -/
def uhmul64 (a b : Word) : Word :=
  BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64)

/-- High 64 bits of signed 64×64 → 128 product (floor toward −∞). -/
def shmul64 (a b : Word) : Word :=
  BitVec.ofInt 64 (Int.fdiv (a.toInt * b.toInt) (2 ^ 64))

/-- Signed 64-bit div; `none` on /0 or overflow (MIN / -1). -/
def sdiv64? (a b : Word) : Option Word :=
  if b == 0#64 then none
  else if a == word64Min && b == BitVec.ofInt 64 (-1) then none
  else some (BitVec.ofInt 64 (intTdiv a.toInt b.toInt))

def srem64? (a b : Word) : Option Word :=
  if b == 0#64 then none
  else if a == word64Min && b == BitVec.ofInt 64 (-1) then none
  else some (BitVec.ofInt 64 (intTmod a.toInt b.toInt))

def sdiv32? (a b : Word32) : Option Word32 :=
  if b == 0#32 then none
  else if a == word32Min && b == BitVec.ofInt 32 (-1) then none
  else some (BitVec.ofInt 32 (intTdiv a.toInt b.toInt))

def srem32? (a b : Word32) : Option Word32 :=
  if b == 0#32 then none
  else if a == word32Min && b == BitVec.ofInt 32 (-1) then none
  else some (BitVec.ofInt 32 (intTmod a.toInt b.toInt))

/-- Advance PC after writing `dst`. -/
def put64 (m : Machine) (dst : Reg) (v : Word) : Machine :=
  (m.setReg dst v).advancePc

/-- Classic 32-bit result: zero-extend (sbpf `as u64` from `u32` path). -/
def put32z (m : Machine) (dst : Reg) (v : Word32) : Machine :=
  put64 m dst (zext32 v)

/-- Classic 32-bit result with sign-extension (sbpf add/sub/mul path via `i32 as i64`). -/
def put32s (m : Machine) (dst : Reg) (v : Word32) : Machine :=
  put64 m dst (BitVec.signExtend 64 v)

/-- 64-bit binary op with immediate (classic + PQR). -/
def execBin64Imm (m : Machine) (op : Opcode) (dst : Reg) (imm : Word) : Option Machine :=
  let a := m.getReg dst
  let b := imm
  match op with
  | .Add64Imm => some (put64 m dst (a + b))
  | .Sub64Imm => some (put64 m dst (a - b))
  | .Mul64Imm | .Lmul64Imm => some (put64 m dst (a * b))
  | .Or64Imm  => some (put64 m dst (a ||| b))
  | .And64Imm => some (put64 m dst (a &&& b))
  | .Xor64Imm => some (put64 m dst (a ^^^ b))
  | .Mov64Imm => some (put64 m dst b)
  | .Lsh64Imm => some (put64 m dst (a <<< b.toNat))
  | .Rsh64Imm => some (put64 m dst (a >>> b.toNat))
  | .Arsh64Imm => some (put64 m dst (BitVec.ofInt 64 (a.toInt >>> b.toNat)))
  | .Hor64Imm => some (put64 m dst (a ||| (b <<< 32)))
  | .Div64Imm | .Mod64Imm | .Udiv64Imm | .Urem64Imm =>
      if b == 0#64 then none
      else
        let v := match op with
          | .Div64Imm | .Udiv64Imm => a / b
          | _ => a % b
        some (put64 m dst v)
  | .Uhmul64Imm => some (put64 m dst (uhmul64 a b))
  | .Shmul64Imm => some (put64 m dst (shmul64 a b))
  | .Sdiv64Imm => (sdiv64? a b).map (put64 m dst)
  | .Srem64Imm => (srem64? a b).map (put64 m dst)
  | _ => none

def execBin64Reg (m : Machine) (op : Opcode) (dst src : Reg) : Option Machine :=
  let a := m.getReg dst
  let b := m.getReg src
  match op with
  | .Add64Reg => some (put64 m dst (a + b))
  | .Sub64Reg => some (put64 m dst (a - b))
  | .Mul64Reg | .Lmul64Reg => some (put64 m dst (a * b))
  | .Or64Reg  => some (put64 m dst (a ||| b))
  | .And64Reg => some (put64 m dst (a &&& b))
  | .Xor64Reg => some (put64 m dst (a ^^^ b))
  | .Mov64Reg => some (put64 m dst b)
  | .Lsh64Reg => some (put64 m dst (a <<< b.toNat))
  | .Rsh64Reg => some (put64 m dst (a >>> b.toNat))
  | .Arsh64Reg => some (put64 m dst (BitVec.ofInt 64 (a.toInt >>> b.toNat)))
  | .Div64Reg | .Mod64Reg | .Udiv64Reg | .Urem64Reg =>
      if b == 0#64 then none
      else
        let v := match op with
          | .Div64Reg | .Udiv64Reg => a / b
          | _ => a % b
        some (put64 m dst v)
  | .Uhmul64Reg => some (put64 m dst (uhmul64 a b))
  | .Shmul64Reg => some (put64 m dst (shmul64 a b))
  | .Sdiv64Reg => (sdiv64? a b).map (put64 m dst)
  | .Srem64Reg => (srem64? a b).map (put64 m dst)
  | _ => none

/-- 32-bit binary with imm. Classic add/sub/mul sign-extend (sbpf); logical/div zero-extend;
PQR 32-bit zero-extends (SIMD-0174). -/
def execBin32Imm (m : Machine) (op : Opcode) (dst : Reg) (imm : Word) : Option Machine :=
  let a32 := toWord32 (m.getReg dst)
  let b32 := toWord32 imm
  match op with
  | .Add32Imm => some (put32s m dst (a32 + b32))
  | .Sub32Imm => some (put32s m dst (a32 - b32))
  | .Mul32Imm => some (put32s m dst (a32 * b32))
  | .Lmul32Imm => some (put32z m dst (a32 * b32))
  | .Or32Imm  => some (put32z m dst (a32 ||| b32))
  | .And32Imm => some (put32z m dst (a32 &&& b32))
  | .Xor32Imm => some (put32z m dst (a32 ^^^ b32))
  | .Mov32Imm => some (put32z m dst b32)
  | .Lsh32Imm => some (put32z m dst (a32 <<< b32.toNat))
  | .Rsh32Imm => some (put32z m dst (a32 >>> b32.toNat))
  | .Arsh32Imm => some (put32z m dst (BitVec.ofInt 32 (a32.toInt >>> b32.toNat)))
  | .Div32Imm | .Mod32Imm | .Udiv32Imm | .Urem32Imm =>
      if b32 == 0#32 then none
      else
        let v := match op with
          | .Div32Imm | .Udiv32Imm => a32 / b32
          | _ => a32 % b32
        some (put32z m dst v)
  | .Sdiv32Imm => (sdiv32? a32 b32).map (put32z m dst)
  | .Srem32Imm => (srem32? a32 b32).map (put32z m dst)
  | _ => none

def execBin32Reg (m : Machine) (op : Opcode) (dst src : Reg) : Option Machine :=
  let a32 := toWord32 (m.getReg dst)
  let b32 := toWord32 (m.getReg src)
  match op with
  | .Add32Reg => some (put32s m dst (a32 + b32))
  | .Sub32Reg => some (put32s m dst (a32 - b32))
  | .Mul32Reg => some (put32s m dst (a32 * b32))
  | .Lmul32Reg => some (put32z m dst (a32 * b32))
  | .Or32Reg  => some (put32z m dst (a32 ||| b32))
  | .And32Reg => some (put32z m dst (a32 &&& b32))
  | .Xor32Reg => some (put32z m dst (a32 ^^^ b32))
  -- V3 / SIMD-0174: mov32 reg is explicit sign-extension of low 32 bits of src
  | .Mov32Reg => some (put64 m dst (sext32Word (m.getReg src)))
  | .Lsh32Reg => some (put32z m dst (a32 <<< b32.toNat))
  | .Rsh32Reg => some (put32z m dst (a32 >>> b32.toNat))
  | .Arsh32Reg => some (put32z m dst (BitVec.ofInt 32 (a32.toInt >>> b32.toNat)))
  | .Div32Reg | .Mod32Reg | .Udiv32Reg | .Urem32Reg =>
      if b32 == 0#32 then none
      else
        let v := match op with
          | .Div32Reg | .Udiv32Reg => a32 / b32
          | _ => a32 % b32
        some (put32z m dst v)
  | .Sdiv32Reg => (sdiv32? a32 b32).map (put32z m dst)
  | .Srem32Reg => (srem32? a32 b32).map (put32z m dst)
  | _ => none

def execUnary (m : Machine) (op : Opcode) (dst : Reg) : Option Machine :=
  match op with
  | .Neg64 => some (put64 m dst (0#64 - m.getReg dst))
  | .Neg32 =>
      let v32 := 0#32 - toWord32 (m.getReg dst)
      -- sbpf: `(result as u32 as u64)` after i32 neg — zero-extend of bit pattern
      some (put32z m dst v32)
  | _ => none

end SbpfSemantics
