import SbpfSemantics.Basic
import SbpfSemantics.Opcode

/-!
# SbpfSemantics.Instr

Resolved instruction AST: all label/identifier operands have already been turned
into numeric offsets/immediates (L2 in `DESIGN.md`). This matches the post-
`resolve_label_references` form consumed by encoding and execution in sbpf.
-/


namespace SbpfSemantics

/-- A fully resolved sBPF instruction.

Fields that an encoding does not use are stored as `none` / zero and ignored by
`encode` / `execStep`, matching `sbpf_common::instruction::Instruction` after
label resolution (no `Either::Left` identifiers). -/
structure Instr where
  opcode : Opcode
  dst    : Option Reg := none
  src    : Option Reg := none
  off    : Option Off16 := none
  /-- Immediate. For `lddw` this is the full 64-bit value; for other ops the
  low 32 bits are encoded (with sign extension on decode of the i32 field). -/
  imm    : Option Word := none
  deriving Repr, Inhabited, DecidableEq

/-- Program = ordered list of resolved instructions (PC is an index into this). -/
abbrev Program := Array Instr

/-- Optional read-only data blob mapped at `rodataStart`. -/
structure Object where
  code   : Program
  rodata : Array UInt8 := #[]
  deriving Inhabited

namespace Instr

def sizeBytes (i : Instr) : Nat := i.opcode.sizeBytes

/-- Smart constructors used by examples and tests. -/
def binImm (op : Opcode) (dst : Reg) (imm : Word) : Instr :=
  { opcode := op, dst := some dst, imm := some imm }

def binReg (op : Opcode) (dst src : Reg) : Instr :=
  { opcode := op, dst := some dst, src := some src }

def loadMem (op : Opcode) (dst src : Reg) (off : Off16) : Instr :=
  { opcode := op, dst := some dst, src := some src, off := some off }

def storeImm (op : Opcode) (dst : Reg) (off : Off16) (imm : Word) : Instr :=
  { opcode := op, dst := some dst, off := some off, imm := some imm }

def storeReg (op : Opcode) (dst src : Reg) (off : Off16) : Instr :=
  { opcode := op, dst := some dst, src := some src, off := some off }

def unary (op : Opcode) (dst : Reg) : Instr :=
  { opcode := op, dst := some dst }

def ja (off : Off16) : Instr :=
  { opcode := .Ja, off := some off }

def jumpImm (op : Opcode) (dst : Reg) (imm : Word) (off : Off16) : Instr :=
  { opcode := op, dst := some dst, imm := some imm, off := some off }

def jumpReg (op : Opcode) (dst src : Reg) (off : Off16) : Instr :=
  { opcode := op, dst := some dst, src := some src, off := some off }

def lddw (dst : Reg) (imm : Word) : Instr :=
  { opcode := .Lddw, dst := some dst, imm := some imm }

def callRel (off : Word) : Instr :=
  { opcode := .Call, imm := some off }

def callx (target : Reg) : Instr :=
  { opcode := .Callx, dst := some target }

def exit : Instr :=
  { opcode := .Exit }

end Instr

end SbpfSemantics
