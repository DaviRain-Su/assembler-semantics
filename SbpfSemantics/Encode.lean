import SbpfSemantics.Basic
import SbpfSemantics.Opcode
import SbpfSemantics.Instr

/-!
# SbpfSemantics.Encode

Instruction encode/decode matching `Instruction::to_bytes` /
`from_bytes_sbpf_v3` in blueshift sbpf.

Layout of an 8-byte instruction:
```
  byte0: opcode
  byte1: (src << 4) | dst
  byte2-3: offset (i16 LE)
  byte4-7: imm (i32 LE)
```
`lddw` appends 8 more bytes: zeros + high 32 bits of imm.
`callx` encodes the target register in the **imm** field with dst/src zeroed
(see sbpf `to_bytes` special case).
-/


namespace SbpfSemantics

/-- Low 8 bits of a natural as `UInt8`. -/
private def u8OfNat (n : Nat) : UInt8 := UInt8.ofNat n

/-- Pack `src` (high nibble) and `dst` (low nibble). -/
def packRegs (dst src : Nat) : UInt8 :=
  u8OfNat ((src <<< 4) + (dst &&& 0xf))

def regNum : Option Reg → Nat
  | none => 0
  | some r => r.val

/-- Signed i16 bytes (LE) from `Off16`. -/
def offBytes (o : Off16) : UInt8 × UInt8 :=
  let n := o.toNat
  (u8OfNat (n &&& 0xff), u8OfNat ((n >>> 8) &&& 0xff))

/-- Low 32 bits of a word as four LE bytes (two's complement bit pattern). -/
def imm32Bytes (w : Word) : Array UInt8 :=
  let n := (w &&& 0xffffffff#64).toNat
  #[
    u8OfNat (n &&& 0xff),
    u8OfNat ((n >>> 8) &&& 0xff),
    u8OfNat ((n >>> 16) &&& 0xff),
    u8OfNat ((n >>> 24) &&& 0xff)
  ]

/-- Encode one resolved instruction to bytes (V3 encode via `Opcode.toByte`). -/
def encodeInstr (i : Instr) : Array UInt8 :=
  -- callx: target register goes in imm; dst field zero (sbpf special case)
  let dstN :=
    match i.opcode with
    | .Callx => 0
    | _ => regNum i.dst
  let srcN := regNum i.src
  let offV : Off16 := i.off.getD 0#16
  let immV : Word :=
    match i.opcode, i.dst with
    | .Callx, some r => BitVec.ofNat 64 r.val
    | _, _ => i.imm.getD 0#64
  let (o0, o1) := offBytes offV
  let immBs := imm32Bytes immV
  let head : Array UInt8 :=
    #[i.opcode.toByte, packRegs dstN srcN, o0, o1] ++ immBs
  if i.opcode.isWide then
    let hi := immV >>> 32
    head ++ #[0, 0, 0, 0] ++ imm32Bytes hi
  else
    head

/-- Decode LE u16. -/
private def readU16LE (b0 b1 : UInt8) : Off16 :=
  BitVec.ofNat 16 (b0.toNat + (b1.toNat <<< 8))

/-- Decode LE i32 bit-pattern into low 32 bits of a word, sign-extended to 64
for the imm field used by execution (matching decode of i32 then cast). -/
private def readImm32LE (b0 b1 b2 b3 : UInt8) : Word :=
  let n := b0.toNat + (b1.toNat <<< 8) + (b2.toNat <<< 16) + (b3.toNat <<< 24)
  imm32AsWord (BitVec.ofNat 32 n)

private def readU32LE (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat + (b1.toNat <<< 8) + (b2.toNat <<< 16) + (b3.toNat <<< 24)

/-- Build a register index if `n < 11`. -/
def regOfNat? (n : Nat) : Option Reg :=
  if h : n < 11 then some ⟨n, h⟩ else none

/-- Decode one instruction from a byte array at `idx` (V3). Returns instruction
and next index. -/
def decodeInstr? (bs : Array UInt8) (idx : Nat) : Option (Instr × Nat) := do
  if _h : idx + 8 ≤ bs.size then
    let op ← Opcode.ofByteV3? bs[idx]!
    let reg := bs[idx+1]!.toNat
    let dstN := reg &&& 0xf
    let srcN := reg >>> 4
    let off := readU16LE bs[idx+2]! bs[idx+3]!
    let immLowBits := readU32LE bs[idx+4]! bs[idx+5]! bs[idx+6]! bs[idx+7]!
    let dst? := regOfNat? dstN
    let src? := regOfNat? srcN
    if op.isWide then
      if idx + 16 ≤ bs.size then
        let immHigh := readU32LE bs[idx+12]! bs[idx+13]! bs[idx+14]! bs[idx+15]!
        let imm : Word :=
          BitVec.ofNat 64 (immLowBits + (immHigh <<< 32))
        pure ({
          opcode := op
          dst := dst?
          src := none
          off := none
          imm := some imm
        }, idx + 16)
      else none
    else
      -- callx: target reg recovered from imm (sbpf encode convention)
      if op == .Callx then
        let t := immLowBits &&& 0xf
        let target := regOfNat? t
        pure ({
          opcode := op
          dst := target
          src := none
          off := none
          imm := none
        }, idx + 8)
      else
        let immW := imm32AsWord (BitVec.ofNat 32 immLowBits)
        pure ({
          opcode := op
          dst := dst?
          src := src?
          off := some off
          imm := some immW
        }, idx + 8)
  else
    none

/-- Decode a full bytecode stream into a program (sequential instructions). -/
partial def decodeProgram? (bs : Array UInt8) : Option Program :=
  let rec go (idx : Nat) (acc : Array Instr) : Option Program :=
    if idx ≥ bs.size then some acc
    else
      match decodeInstr? bs idx with
      | none => none
      | some (i, idx') =>
        if idx' ≤ idx then none else go idx' (acc.push i)
  go 0 #[]

/-- Encode a whole program. -/
def encodeProgram (p : Program) : Array UInt8 :=
  p.foldl (init := #[]) fun acc i => acc ++ encodeInstr i

/-- Opcodes whose V3 decode matches `toByte` (no jump32 displacement). -/
def Opcode.v3RoundTrip (op : Opcode) : Bool :=
  match Opcode.ofByteV3? op.toByte with
  | some op' => op' == op
  | none => false

/-- Smoke: `lddw` encodes to 16 bytes. -/
example : (encodeInstr (.lddw ⟨1, by omega⟩ 0x123456789abcdef0#64)).size = 16 := by
  native_decide

/-- Smoke: `add64` imm encodes to 8 bytes. -/
example :
    (encodeInstr (.binImm .Add64Imm ⟨1, by omega⟩ 10#64)).size = 8 := by
  native_decide

/-- Smoke: V3 round-trip of opcode byte for `Add64Imm`. -/
example : Opcode.v3RoundTrip .Add64Imm = true := by native_decide

/-- Smoke: displaced classic opcode does *not* V3-round-trip (`Udiv32Imm` → jset32). -/
example : Opcode.v3RoundTrip .Udiv32Imm = false := by native_decide

end SbpfSemantics
