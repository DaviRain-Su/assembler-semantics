/-!
# SbpfSemantics.Basic

Shared primitives for the sBPF formalization: registers, words, offsets, and
memory-map constants matching blueshift `sbpf` (`crates/vm/src/memory.rs`).
-/

namespace SbpfSemantics

/-- Register indices `r0`–`r10` (11 registers). -/
abbrev Reg := Fin 11

/-- 64-bit machine word (register width). -/
abbrev Word := BitVec 64

/-- 32-bit view used by 32-bit ALU and jump32 ops. -/
abbrev Word32 := BitVec 32

/-- Signed 16-bit instruction offset field. -/
abbrev Off16 := BitVec 16

/-- Signed 32-bit immediate field (low half of a wide imm for `lddw`). -/
abbrev Imm32 := BitVec 32

/-- Frame-pointer / callee-saved snapshot used by internal calls. -/
structure CallFrame where
  returnPc : Nat
  savedR6 : Word
  savedR7 : Word
  savedR8 : Word
  savedR9 : Word
  savedFp : Word
  deriving Repr, Inhabited

/-- Virtual address map (from `sbpf` `Memory`). -/
def rodataStart : Word := 0x0#64
def stackStart  : Word := 0x200000000#64
def heapStart   : Word := 0x300000000#64
def inputStart  : Word := 0x400000000#64

/-- Stack frame size (4 KiB), matching `Memory::STACK_FRAME_SIZE`. -/
def stackFrameSize : Word := 4096#64

/-- Default max call depth used when constructing machines. -/
def defaultMaxCallDepth : Nat := 64

/-- Zero word. -/
def word0 : Word := 0#64

/-- Sign-extend a 32-bit immediate to a 64-bit word (as in jump imm compares).

In sbpf jump-immediate paths, the imm is taken as `i32` then cast to `u64`
via `(imm as i32 as i64) as u64` for 64-bit compares. -/
def imm32AsWord (i : Imm32) : Word :=
  BitVec.signExtend 64 i

/-- Low 32 bits of a word, zero-extended back to 64 (common after 32-bit ALU). -/
def low32 (w : Word) : Word :=
  w &&& 0xffffffff#64

/-- Truncate word to 32 bits. -/
def toWord32 (w : Word) : Word32 :=
  BitVec.truncate 32 w

/-- Zero-extend 32 → 64. -/
def ofWord32 (w : Word32) : Word :=
  BitVec.zeroExtend 64 w

/-- Address = base + signed offset (wrapping), matching `calculate_address`. -/
def calcAddr (base : Word) (off : Off16) : Word :=
  BitVec.ofInt 64 (base.toInt + off.toInt)

end SbpfSemantics
