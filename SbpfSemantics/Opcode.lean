/-!
# SbpfSemantics.Opcode

sBPF opcodes as used by [blueshift-gg/sbpf](https://github.com/blueshift-gg/sbpf)
`crates/common/src/opcode.rs`. Phase 1 targets **sBPF V3** encoding/decoding.

## V3 byte conflicts

Under V3, several classic opcode bytes are reassigned to `*32` jump variants.
`ofByteV3` prefers the jump32 mapping (matching `Opcode::try_from_sbpf_v3`).
Opcodes displaced by that mapping do not round-trip under V3 decode.
-/

namespace SbpfSemantics

/-- sBPF opcode mnemonic (resolved; imm vs reg are distinct constructors). -/
inductive Opcode where
  | Lddw
  | Ldxb
  | Ldxh
  | Ldxw
  | Ldxdw
  | Stb
  | Sth
  | Stw
  | Stdw
  | Stxb
  | Stxh
  | Stxw
  | Stxdw
  | Add32Imm
  | Add32Reg
  | Sub32Imm
  | Sub32Reg
  | Mul32Imm
  | Mul32Reg
  | Div32Imm
  | Div32Reg
  | Or32Imm
  | Or32Reg
  | And32Imm
  | And32Reg
  | Lsh32Imm
  | Lsh32Reg
  | Rsh32Imm
  | Rsh32Reg
  | Mod32Imm
  | Mod32Reg
  | Xor32Imm
  | Xor32Reg
  | Mov32Imm
  | Mov32Reg
  | Arsh32Imm
  | Arsh32Reg
  | Lmul32Imm
  | Lmul32Reg
  | Udiv32Imm
  | Udiv32Reg
  | Urem32Imm
  | Urem32Reg
  | Sdiv32Imm
  | Sdiv32Reg
  | Srem32Imm
  | Srem32Reg
  | Le
  | Be
  | Add64Imm
  | Add64Reg
  | Sub64Imm
  | Sub64Reg
  | Mul64Imm
  | Mul64Reg
  | Div64Imm
  | Div64Reg
  | Or64Imm
  | Or64Reg
  | And64Imm
  | And64Reg
  | Lsh64Imm
  | Lsh64Reg
  | Rsh64Imm
  | Rsh64Reg
  | Mod64Imm
  | Mod64Reg
  | Xor64Imm
  | Xor64Reg
  | Mov64Imm
  | Mov64Reg
  | Arsh64Imm
  | Arsh64Reg
  | Hor64Imm
  | Lmul64Imm
  | Lmul64Reg
  | Uhmul64Imm
  | Uhmul64Reg
  | Udiv64Imm
  | Udiv64Reg
  | Urem64Imm
  | Urem64Reg
  | Shmul64Imm
  | Shmul64Reg
  | Sdiv64Imm
  | Sdiv64Reg
  | Srem64Imm
  | Srem64Reg
  | Neg32
  | Neg64
  | Ja
  | JeqImm
  | JeqReg
  | JgtImm
  | JgtReg
  | JgeImm
  | JgeReg
  | JltImm
  | JltReg
  | JleImm
  | JleReg
  | JsetImm
  | JsetReg
  | JneImm
  | JneReg
  | JsgtImm
  | JsgtReg
  | JsgeImm
  | JsgeReg
  | JsltImm
  | JsltReg
  | JsleImm
  | JsleReg
  | Jeq32Imm
  | Jeq32Reg
  | Jgt32Imm
  | Jgt32Reg
  | Jge32Imm
  | Jge32Reg
  | Jlt32Imm
  | Jlt32Reg
  | Jle32Imm
  | Jle32Reg
  | Jset32Imm
  | Jset32Reg
  | Jne32Imm
  | Jne32Reg
  | Jsgt32Imm
  | Jsgt32Reg
  | Jsge32Imm
  | Jsge32Reg
  | Jslt32Imm
  | Jslt32Reg
  | Jsle32Imm
  | Jsle32Reg
  | Call
  | Callx
  | Exit
  deriving DecidableEq, Repr, Inhabited

/-- Encode opcode to its bytecode byte (`From<Opcode> for u8` in sbpf). -/
def Opcode.toByte : Opcode → UInt8
  | .Lddw => 0x18
  | .Ldxb => 0x71
  | .Ldxh => 0x69
  | .Ldxw => 0x61
  | .Ldxdw => 0x79
  | .Stb => 0x72
  | .Sth => 0x6a
  | .Stw => 0x62
  | .Stdw => 0x7a
  | .Stxb => 0x73
  | .Stxh => 0x6b
  | .Stxw => 0x63
  | .Stxdw => 0x7b
  | .Add32Imm => 0x04
  | .Add32Reg => 0x0c
  | .Sub32Imm => 0x14
  | .Sub32Reg => 0x1c
  | .Mul32Imm => 0x24
  | .Mul32Reg => 0x2c
  | .Div32Imm => 0x34
  | .Div32Reg => 0x3c
  | .Or32Imm => 0x44
  | .Or32Reg => 0x4c
  | .And32Imm => 0x54
  | .And32Reg => 0x5c
  | .Lsh32Imm => 0x64
  | .Lsh32Reg => 0x6c
  | .Rsh32Imm => 0x74
  | .Rsh32Reg => 0x7c
  | .Mod32Imm => 0x94
  | .Mod32Reg => 0x9c
  | .Xor32Imm => 0xa4
  | .Xor32Reg => 0xac
  | .Mov32Imm => 0xb4
  | .Mov32Reg => 0xbc
  | .Arsh32Imm => 0xc4
  | .Arsh32Reg => 0xcc
  | .Lmul32Imm => 0x86
  | .Lmul32Reg => 0x8e
  | .Udiv32Imm => 0x46
  | .Udiv32Reg => 0x4e
  | .Urem32Imm => 0x66
  | .Urem32Reg => 0x6e
  | .Sdiv32Imm => 0xc6
  | .Sdiv32Reg => 0xce
  | .Srem32Imm => 0xe6
  | .Srem32Reg => 0xee
  | .Le => 0xd4
  | .Be => 0xdc
  | .Add64Imm => 0x07
  | .Add64Reg => 0x0f
  | .Sub64Imm => 0x17
  | .Sub64Reg => 0x1f
  | .Mul64Imm => 0x27
  | .Mul64Reg => 0x2f
  | .Div64Imm => 0x37
  | .Div64Reg => 0x3f
  | .Or64Imm => 0x47
  | .Or64Reg => 0x4f
  | .And64Imm => 0x57
  | .And64Reg => 0x5f
  | .Lsh64Imm => 0x67
  | .Lsh64Reg => 0x6f
  | .Rsh64Imm => 0x77
  | .Rsh64Reg => 0x7f
  | .Mod64Imm => 0x97
  | .Mod64Reg => 0x9f
  | .Xor64Imm => 0xa7
  | .Xor64Reg => 0xaf
  | .Mov64Imm => 0xb7
  | .Mov64Reg => 0xbf
  | .Arsh64Imm => 0xc7
  | .Arsh64Reg => 0xcf
  | .Hor64Imm => 0xf7
  | .Lmul64Imm => 0x96
  | .Lmul64Reg => 0x9e
  | .Uhmul64Imm => 0x36
  | .Uhmul64Reg => 0x3e
  | .Udiv64Imm => 0x56
  | .Udiv64Reg => 0x5e
  | .Urem64Imm => 0x76
  | .Urem64Reg => 0x7e
  | .Shmul64Imm => 0xb6
  | .Shmul64Reg => 0xbe
  | .Sdiv64Imm => 0xd6
  | .Sdiv64Reg => 0xde
  | .Srem64Imm => 0xf6
  | .Srem64Reg => 0xfe
  | .Neg32 => 0x84
  | .Neg64 => 0x87
  | .Ja => 0x05
  | .JeqImm => 0x15
  | .JeqReg => 0x1d
  | .JgtImm => 0x25
  | .JgtReg => 0x2d
  | .JgeImm => 0x35
  | .JgeReg => 0x3d
  | .JltImm => 0xa5
  | .JltReg => 0xad
  | .JleImm => 0xb5
  | .JleReg => 0xbd
  | .JsetImm => 0x45
  | .JsetReg => 0x4d
  | .JneImm => 0x55
  | .JneReg => 0x5d
  | .JsgtImm => 0x65
  | .JsgtReg => 0x6d
  | .JsgeImm => 0x75
  | .JsgeReg => 0x7d
  | .JsltImm => 0xc5
  | .JsltReg => 0xcd
  | .JsleImm => 0xd5
  | .JsleReg => 0xdd
  | .Jeq32Imm => 0x16
  | .Jeq32Reg => 0x1e
  | .Jgt32Imm => 0x26
  | .Jgt32Reg => 0x2e
  | .Jge32Imm => 0x36
  | .Jge32Reg => 0x3e
  | .Jlt32Imm => 0xa6
  | .Jlt32Reg => 0xae
  | .Jle32Imm => 0xb6
  | .Jle32Reg => 0xbe
  | .Jset32Imm => 0x46
  | .Jset32Reg => 0x4e
  | .Jne32Imm => 0x56
  | .Jne32Reg => 0x5e
  | .Jsgt32Imm => 0x66
  | .Jsgt32Reg => 0x6e
  | .Jsge32Imm => 0x76
  | .Jsge32Reg => 0x7e
  | .Jslt32Imm => 0xc6
  | .Jslt32Reg => 0xce
  | .Jsle32Imm => 0xd6
  | .Jsle32Reg => 0xde
  | .Call => 0x85
  | .Callx => 0x8d
  | .Exit => 0x95

/-- Classic (pre-V3 override) decode. -/
def Opcode.ofByteClassic? (b : UInt8) : Option Opcode :=
  match b with
  | 0x04 => some .Add32Imm
  | 0x05 => some .Ja
  | 0x07 => some .Add64Imm
  | 0x0c => some .Add32Reg
  | 0x0f => some .Add64Reg
  | 0x14 => some .Sub32Imm
  | 0x15 => some .JeqImm
  | 0x17 => some .Sub64Imm
  | 0x18 => some .Lddw
  | 0x1c => some .Sub32Reg
  | 0x1d => some .JeqReg
  | 0x1f => some .Sub64Reg
  | 0x24 => some .Mul32Imm
  | 0x25 => some .JgtImm
  | 0x27 => some .Mul64Imm
  | 0x2c => some .Mul32Reg
  | 0x2d => some .JgtReg
  | 0x2f => some .Mul64Reg
  | 0x34 => some .Div32Imm
  | 0x35 => some .JgeImm
  | 0x36 => some .Uhmul64Imm
  | 0x37 => some .Div64Imm
  | 0x3c => some .Div32Reg
  | 0x3d => some .JgeReg
  | 0x3e => some .Uhmul64Reg
  | 0x3f => some .Div64Reg
  | 0x44 => some .Or32Imm
  | 0x45 => some .JsetImm
  | 0x46 => some .Udiv32Imm
  | 0x47 => some .Or64Imm
  | 0x4c => some .Or32Reg
  | 0x4d => some .JsetReg
  | 0x4e => some .Udiv32Reg
  | 0x4f => some .Or64Reg
  | 0x54 => some .And32Imm
  | 0x55 => some .JneImm
  | 0x56 => some .Udiv64Imm
  | 0x57 => some .And64Imm
  | 0x5c => some .And32Reg
  | 0x5d => some .JneReg
  | 0x5e => some .Udiv64Reg
  | 0x5f => some .And64Reg
  | 0x61 => some .Ldxw
  | 0x62 => some .Stw
  | 0x63 => some .Stxw
  | 0x64 => some .Lsh32Imm
  | 0x65 => some .JsgtImm
  | 0x66 => some .Urem32Imm
  | 0x67 => some .Lsh64Imm
  | 0x69 => some .Ldxh
  | 0x6a => some .Sth
  | 0x6b => some .Stxh
  | 0x6c => some .Lsh32Reg
  | 0x6d => some .JsgtReg
  | 0x6e => some .Urem32Reg
  | 0x6f => some .Lsh64Reg
  | 0x71 => some .Ldxb
  | 0x72 => some .Stb
  | 0x73 => some .Stxb
  | 0x74 => some .Rsh32Imm
  | 0x75 => some .JsgeImm
  | 0x76 => some .Urem64Imm
  | 0x77 => some .Rsh64Imm
  | 0x79 => some .Ldxdw
  | 0x7a => some .Stdw
  | 0x7b => some .Stxdw
  | 0x7c => some .Rsh32Reg
  | 0x7d => some .JsgeReg
  | 0x7e => some .Urem64Reg
  | 0x7f => some .Rsh64Reg
  | 0x84 => some .Neg32
  | 0x85 => some .Call
  | 0x86 => some .Lmul32Imm
  | 0x87 => some .Neg64
  | 0x8d => some .Callx
  | 0x8e => some .Lmul32Reg
  | 0x94 => some .Mod32Imm
  | 0x95 => some .Exit
  | 0x96 => some .Lmul64Imm
  | 0x97 => some .Mod64Imm
  | 0x9c => some .Mod32Reg
  | 0x9e => some .Lmul64Reg
  | 0x9f => some .Mod64Reg
  | 0xa4 => some .Xor32Imm
  | 0xa5 => some .JltImm
  | 0xa7 => some .Xor64Imm
  | 0xac => some .Xor32Reg
  | 0xad => some .JltReg
  | 0xaf => some .Xor64Reg
  | 0xb4 => some .Mov32Imm
  | 0xb5 => some .JleImm
  | 0xb6 => some .Shmul64Imm
  | 0xb7 => some .Mov64Imm
  | 0xbc => some .Mov32Reg
  | 0xbd => some .JleReg
  | 0xbe => some .Shmul64Reg
  | 0xbf => some .Mov64Reg
  | 0xc4 => some .Arsh32Imm
  | 0xc5 => some .JsltImm
  | 0xc6 => some .Sdiv32Imm
  | 0xc7 => some .Arsh64Imm
  | 0xcc => some .Arsh32Reg
  | 0xcd => some .JsltReg
  | 0xce => some .Sdiv32Reg
  | 0xcf => some .Arsh64Reg
  | 0xd4 => some .Le
  | 0xd5 => some .JsleImm
  | 0xd6 => some .Sdiv64Imm
  | 0xdc => some .Be
  | 0xdd => some .JsleReg
  | 0xde => some .Sdiv64Reg
  | 0xe6 => some .Srem32Imm
  | 0xee => some .Srem32Reg
  | 0xf6 => some .Srem64Imm
  | 0xf7 => some .Hor64Imm
  | 0xfe => some .Srem64Reg
  | _ => none

/-- V3 decode: jump32 overrides first, then classic (`try_from_sbpf_v3`). -/
def Opcode.ofByteV3? (b : UInt8) : Option Opcode :=
  match b with
  | 0x16 => some .Jeq32Imm
  | 0x1e => some .Jeq32Reg
  | 0x26 => some .Jgt32Imm
  | 0x2e => some .Jgt32Reg
  | 0x36 => some .Jge32Imm
  | 0x3e => some .Jge32Reg
  | 0x46 => some .Jset32Imm
  | 0x4e => some .Jset32Reg
  | 0x56 => some .Jne32Imm
  | 0x5e => some .Jne32Reg
  | 0x66 => some .Jsgt32Imm
  | 0x6e => some .Jsgt32Reg
  | 0x76 => some .Jsge32Imm
  | 0x7e => some .Jsge32Reg
  | 0xa6 => some .Jlt32Imm
  | 0xae => some .Jlt32Reg
  | 0xb6 => some .Jle32Imm
  | 0xbe => some .Jle32Reg
  | 0xc6 => some .Jslt32Imm
  | 0xce => some .Jslt32Reg
  | 0xd6 => some .Jsle32Imm
  | 0xde => some .Jsle32Reg
  | _ => ofByteClassic? b

/-- Default decode for this formalization: V3. -/
abbrev Opcode.ofByte? := Opcode.ofByteV3?

/-- Whether this opcode uses a 16-byte encoding (only `lddw`). -/
def Opcode.isWide : Opcode → Bool
  | .Lddw => true
  | _ => false

def Opcode.sizeBytes (op : Opcode) : Nat := if op.isWide then 16 else 8

inductive OpClass where
  | loadImm | loadMem | storeImm | storeReg
  | binImm | binReg | unary | endian
  | jump | jumpImm | jumpReg | jump32Imm | jump32Reg
  | callImm | callReg | exit
  deriving DecidableEq, Repr

def Opcode.opClass : Opcode → OpClass
  | .Lddw => .loadImm
  | .Ldxb => .loadMem
  | .Ldxh => .loadMem
  | .Ldxw => .loadMem
  | .Ldxdw => .loadMem
  | .Stb => .storeImm
  | .Sth => .storeImm
  | .Stw => .storeImm
  | .Stdw => .storeImm
  | .Stxb => .storeReg
  | .Stxh => .storeReg
  | .Stxw => .storeReg
  | .Stxdw => .storeReg
  | .Add32Imm => .binImm
  | .Add32Reg => .binReg
  | .Sub32Imm => .binImm
  | .Sub32Reg => .binReg
  | .Mul32Imm => .binImm
  | .Mul32Reg => .binReg
  | .Div32Imm => .binImm
  | .Div32Reg => .binReg
  | .Or32Imm => .binImm
  | .Or32Reg => .binReg
  | .And32Imm => .binImm
  | .And32Reg => .binReg
  | .Lsh32Imm => .binImm
  | .Lsh32Reg => .binReg
  | .Rsh32Imm => .binImm
  | .Rsh32Reg => .binReg
  | .Mod32Imm => .binImm
  | .Mod32Reg => .binReg
  | .Xor32Imm => .binImm
  | .Xor32Reg => .binReg
  | .Mov32Imm => .binImm
  | .Mov32Reg => .binReg
  | .Arsh32Imm => .binImm
  | .Arsh32Reg => .binReg
  | .Lmul32Imm => .binImm
  | .Lmul32Reg => .binReg
  | .Udiv32Imm => .binImm
  | .Udiv32Reg => .binReg
  | .Urem32Imm => .binImm
  | .Urem32Reg => .binReg
  | .Sdiv32Imm => .binImm
  | .Sdiv32Reg => .binReg
  | .Srem32Imm => .binImm
  | .Srem32Reg => .binReg
  | .Le => .endian
  | .Be => .endian
  | .Add64Imm => .binImm
  | .Add64Reg => .binReg
  | .Sub64Imm => .binImm
  | .Sub64Reg => .binReg
  | .Mul64Imm => .binImm
  | .Mul64Reg => .binReg
  | .Div64Imm => .binImm
  | .Div64Reg => .binReg
  | .Or64Imm => .binImm
  | .Or64Reg => .binReg
  | .And64Imm => .binImm
  | .And64Reg => .binReg
  | .Lsh64Imm => .binImm
  | .Lsh64Reg => .binReg
  | .Rsh64Imm => .binImm
  | .Rsh64Reg => .binReg
  | .Mod64Imm => .binImm
  | .Mod64Reg => .binReg
  | .Xor64Imm => .binImm
  | .Xor64Reg => .binReg
  | .Mov64Imm => .binImm
  | .Mov64Reg => .binReg
  | .Arsh64Imm => .binImm
  | .Arsh64Reg => .binReg
  | .Hor64Imm => .binImm
  | .Lmul64Imm => .binImm
  | .Lmul64Reg => .binReg
  | .Uhmul64Imm => .binImm
  | .Uhmul64Reg => .binReg
  | .Udiv64Imm => .binImm
  | .Udiv64Reg => .binReg
  | .Urem64Imm => .binImm
  | .Urem64Reg => .binReg
  | .Shmul64Imm => .binImm
  | .Shmul64Reg => .binReg
  | .Sdiv64Imm => .binImm
  | .Sdiv64Reg => .binReg
  | .Srem64Imm => .binImm
  | .Srem64Reg => .binReg
  | .Neg32 => .unary
  | .Neg64 => .unary
  | .Ja => .jump
  | .JeqImm => .jumpImm
  | .JeqReg => .jumpReg
  | .JgtImm => .jumpImm
  | .JgtReg => .jumpReg
  | .JgeImm => .jumpImm
  | .JgeReg => .jumpReg
  | .JltImm => .jumpImm
  | .JltReg => .jumpReg
  | .JleImm => .jumpImm
  | .JleReg => .jumpReg
  | .JsetImm => .jumpImm
  | .JsetReg => .jumpReg
  | .JneImm => .jumpImm
  | .JneReg => .jumpReg
  | .JsgtImm => .jumpImm
  | .JsgtReg => .jumpReg
  | .JsgeImm => .jumpImm
  | .JsgeReg => .jumpReg
  | .JsltImm => .jumpImm
  | .JsltReg => .jumpReg
  | .JsleImm => .jumpImm
  | .JsleReg => .jumpReg
  | .Jeq32Imm => .jump32Imm
  | .Jeq32Reg => .jump32Reg
  | .Jgt32Imm => .jump32Imm
  | .Jgt32Reg => .jump32Reg
  | .Jge32Imm => .jump32Imm
  | .Jge32Reg => .jump32Reg
  | .Jlt32Imm => .jump32Imm
  | .Jlt32Reg => .jump32Reg
  | .Jle32Imm => .jump32Imm
  | .Jle32Reg => .jump32Reg
  | .Jset32Imm => .jump32Imm
  | .Jset32Reg => .jump32Reg
  | .Jne32Imm => .jump32Imm
  | .Jne32Reg => .jump32Reg
  | .Jsgt32Imm => .jump32Imm
  | .Jsgt32Reg => .jump32Reg
  | .Jsge32Imm => .jump32Imm
  | .Jsge32Reg => .jump32Reg
  | .Jslt32Imm => .jump32Imm
  | .Jslt32Reg => .jump32Reg
  | .Jsle32Imm => .jump32Imm
  | .Jsle32Reg => .jump32Reg
  | .Call => .callImm
  | .Callx => .callReg
  | .Exit => .exit

end SbpfSemantics
