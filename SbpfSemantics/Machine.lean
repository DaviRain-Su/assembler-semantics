import SbpfSemantics.Basic
import SbpfSemantics.Instr

/-!
# SbpfSemantics.Machine

Abstract machine state: registers, PC, call stack, and the four memory regions
from blueshift `sbpf` `crates/vm/src/memory.rs`.
-/


namespace SbpfSemantics

/-- Which virtual region an address falls into. -/
inductive MemRegion where
  | rodata | stack | heap | input
  deriving DecidableEq, Repr

/-- Flat byte stores for each region (`Array` for simple random access). -/
structure Memory where
  rodata : Array UInt8 := #[]
  stack  : Array UInt8 := #[]
  heap   : Array UInt8 := #[]
  input  : Array UInt8 := #[]
  deriving Inhabited

namespace Memory

def stackSize (maxDepth : Nat) : Nat :=
  stackFrameSize.toNat * maxDepth

def initial (input rodata : Array UInt8) (maxDepth : Nat := defaultMaxCallDepth)
    (heapSize : Nat := 32768) : Memory where
  input := input
  rodata := rodata
  stack := Array.replicate (stackSize maxDepth) 0
  heap := Array.replicate heapSize 0

def initialFp (_m : Memory) : Word :=
  stackStart + stackFrameSize

/-- Translate a virtual address to region + offset. -/
def translate (m : Memory) (addr : Word) : Option (MemRegion × Nat) :=
  let a := addr.toNat
  if a ≥ inputStart.toNat then
    let off := a - inputStart.toNat
    if off < m.input.size then some (.input, off) else none
  else if a ≥ heapStart.toNat then
    let off := a - heapStart.toNat
    if off < m.heap.size then some (.heap, off) else none
  else if a ≥ stackStart.toNat then
    let off := a - stackStart.toNat
    if off < m.stack.size then some (.stack, off) else none
  else
    let off := a
    if off < m.rodata.size then some (.rodata, off) else none

def getByte (m : Memory) (addr : Word) : Option UInt8 := do
  let (reg, off) ← m.translate addr
  match reg with
  | .rodata => m.rodata[off]?
  | .stack  => m.stack[off]?
  | .heap   => m.heap[off]?
  | .input  => m.input[off]?

def setByte (m : Memory) (addr : Word) (b : UInt8) : Option Memory := do
  let (reg, off) ← m.translate addr
  match reg with
  | .rodata => none  -- read-only
  | .stack =>
    some { m with stack := m.stack.set! off b }
  | .heap =>
    some { m with heap := m.heap.set! off b }
  | .input =>
    -- input is typically read-only in real loaders; sbpf MockVm may allow writes.
    -- We allow writes for now to match a permissive host.
    some { m with input := m.input.set! off b }

def readU8 (m : Memory) (addr : Word) : Option Word := do
  let b ← m.getByte addr
  pure (BitVec.ofNat 64 b.toNat)

def readU16 (m : Memory) (addr : Word) : Option Word := do
  let b0 ← m.getByte addr
  let b1 ← m.getByte (addr + 1#64)
  pure (BitVec.ofNat 64 (b0.toNat + (b1.toNat <<< 8)))

def readU32 (m : Memory) (addr : Word) : Option Word := do
  let b0 ← m.getByte addr
  let b1 ← m.getByte (addr + 1#64)
  let b2 ← m.getByte (addr + 2#64)
  let b3 ← m.getByte (addr + 3#64)
  pure (BitVec.ofNat 64
    (b0.toNat + (b1.toNat <<< 8) + (b2.toNat <<< 16) + (b3.toNat <<< 24)))

def readU64 (m : Memory) (addr : Word) : Option Word := do
  let lo ← m.readU32 addr
  let hi ← m.readU32 (addr + 4#64)
  pure (lo ||| (hi <<< 32))

def writeU8 (m : Memory) (addr : Word) (v : Word) : Option Memory :=
  m.setByte addr (UInt8.ofNat (v.toNat &&& 0xff))

def writeU16 (m : Memory) (addr : Word) (v : Word) : Option Memory := do
  let m ← m.setByte addr (UInt8.ofNat (v.toNat &&& 0xff))
  m.setByte (addr + 1#64) (UInt8.ofNat ((v.toNat >>> 8) &&& 0xff))

def writeU32 (m : Memory) (addr : Word) (v : Word) : Option Memory := do
  let m ← m.setByte addr (UInt8.ofNat (v.toNat &&& 0xff))
  let m ← m.setByte (addr + 1#64) (UInt8.ofNat ((v.toNat >>> 8) &&& 0xff))
  let m ← m.setByte (addr + 2#64) (UInt8.ofNat ((v.toNat >>> 16) &&& 0xff))
  m.setByte (addr + 3#64) (UInt8.ofNat ((v.toNat >>> 24) &&& 0xff))

def writeU64 (m : Memory) (addr : Word) (v : Word) : Option Memory := do
  let m ← m.writeU32 addr v
  m.writeU32 (addr + 4#64) (v >>> 32)

/-- Read `n` consecutive bytes starting at `addr`. -/
def readBytes (m : Memory) (addr : Word) (n : Nat) : Option (Array UInt8) :=
  let rec go (i : Nat) (acc : Array UInt8) : Option (Array UInt8) :=
    if i ≥ n then some acc
    else do
      let b ← m.getByte (addr + BitVec.ofNat 64 i)
      go (i + 1) (acc.push b)
  go 0 #[]

/-- Write bytes starting at `addr` (fails on OOB / rodata). -/
def writeBytes (m : Memory) (addr : Word) (bs : Array UInt8) : Option Memory :=
  let rec go (i : Nat) (m : Memory) : Option Memory :=
    if h : i < bs.size then do
      let m ← m.setByte (addr + BitVec.ofNat 64 i) bs[i]
      go (i + 1) m
    else some m
  go 0 m

/-- Fill `n` bytes at `addr` with `c`. -/
def memset (m : Memory) (addr : Word) (c : UInt8) (n : Nat) : Option Memory :=
  m.writeBytes addr (Array.replicate n c)

/-- Non-overlapping check used by `sol_memcpy_`. -/
def nonoverlapping (src srcLen dst dstLen : Nat) : Bool :=
  if src > dst then src - dst ≥ dstLen
  else dst - src ≥ srcLen

end Memory

/-- Full machine state. -/
structure Machine where
  regs       : Vector Word 11 := Vector.replicate 11 word0
  pc         : Nat := 0
  mem        : Memory := {}
  frames     : List CallFrame := []
  maxDepth   : Nat := defaultMaxCallDepth
  halted     : Option Word := none
  /-- Last `sol_set_return_data` payload (host-visible). -/
  returnData : Array UInt8 := #[]
  deriving Inhabited

namespace Machine

def getReg (m : Machine) (r : Reg) : Word :=
  m.regs[r]

def setReg (m : Machine) (r : Reg) (v : Word) : Machine :=
  { m with regs := m.regs.set r v }

def advancePc (m : Machine) : Machine :=
  { m with pc := m.pc + 1 }

def setPc (m : Machine) (pc : Nat) : Machine :=
  { m with pc := pc }

def callDepth (m : Machine) : Nat := m.frames.length

/-- Entry machine: `r1 = input`, `r10 = FP`, code supplied externally via Program. -/
def entry (input rodata : Array UInt8 := #[]) (maxDepth : Nat := defaultMaxCallDepth) : Machine :=
  let mem := Memory.initial input rodata maxDepth
  let m : Machine := { mem := mem, maxDepth := maxDepth }
  let m := m.setReg ⟨1, by omega⟩ inputStart
  m.setReg ⟨10, by omega⟩ mem.initialFp

def pushFrame (m : Machine) (fr : CallFrame) : Option Machine :=
  if m.callDepth ≥ m.maxDepth then none
  else some { m with frames := fr :: m.frames }

def popFrame (m : Machine) : Option (CallFrame × Machine) :=
  match m.frames with
  | [] => none
  | fr :: rest => some (fr, { m with frames := rest })

def halt (m : Machine) (code : Word) : Machine :=
  { m with halted := some code }

/-- Reset control state for a new entrypoint invocation while keeping memory
(and thus account/input data). Used by multi-instruction PF scenarios. -/
def readyForNext (m : Machine) : Machine :=
  let m : Machine := {
    m with
    halted := none
    pc := 0
    frames := []
    returnData := #[]
    regs := Vector.replicate 11 word0
  }
  let m := m.setReg ⟨1, by omega⟩ inputStart
  m.setReg ⟨10, by omega⟩ m.mem.initialFp

end Machine

end SbpfSemantics
