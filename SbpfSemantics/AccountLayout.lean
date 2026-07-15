import SbpfSemantics.Basic
import SbpfSemantics.Machine

/-!
# SbpfSemantics.AccountLayout

Minimal **input-region** helpers for ProofForge Solana scenarios.

Not a full Solana account serializer. Provides a flat LE layout that materializers
can target for portable Counter-style state living in the VM input region
(`inputStart`).
-/

namespace SbpfSemantics

/-- Offset of an 8-byte LE `UInt64` cell inside the input region. -/
structure InputCell where
  offset : Nat
  deriving Repr, DecidableEq

/-- Default cell used by Counter scenarios (256 bytes into input). -/
def counterCell : InputCell := ⟨0x100⟩

/-- Absolute virtual address of a cell. -/
def InputCell.addr (c : InputCell) : Word :=
  inputStart + BitVec.ofNat 64 c.offset

/-- Encode `Word` as 8 LE bytes. -/
def wordToLE (w : Word) : Array UInt8 :=
  let n := w.toNat
  #[
    UInt8.ofNat (n &&& 0xff),
    UInt8.ofNat ((n >>> 8) &&& 0xff),
    UInt8.ofNat ((n >>> 16) &&& 0xff),
    UInt8.ofNat ((n >>> 24) &&& 0xff),
    UInt8.ofNat ((n >>> 32) &&& 0xff),
    UInt8.ofNat ((n >>> 40) &&& 0xff),
    UInt8.ofNat ((n >>> 48) &&& 0xff),
    UInt8.ofNat ((n >>> 56) &&& 0xff)
  ]

/-- Decode 8 LE bytes to `Word` (pads with 0). -/
def wordFromLE (bs : Array UInt8) : Word :=
  let b (i : Nat) : Nat := (bs[i]?.getD 0).toNat
  BitVec.ofNat 64 (
    b 0 + (b 1 <<< 8) + (b 2 <<< 16) + (b 3 <<< 24) +
    (b 4 <<< 32) + (b 5 <<< 40) + (b 6 <<< 48) + (b 7 <<< 56))

/-- Build an input blob large enough for `cell`, with `value` at that cell. -/
def mkInputWithCell (cell : InputCell) (value : Word) : Array UInt8 :=
  let size := cell.offset + 8
  let base := Array.replicate size 0
  let bytes := wordToLE value
  Id.run do
    let mut a := base
    for i in [0:8] do
      a := a.set! (cell.offset + i) bytes[i]!
    pure a

/-- Read a cell from a machine's input region (via virtual address). -/
def Machine.loadCell (m : Machine) (cell : InputCell) : Option Word := do
  let bs ← m.mem.readBytes cell.addr 8
  pure (wordFromLE bs)

/-- Write a cell into the machine input region. -/
def Machine.storeCell (m : Machine) (cell : InputCell) (v : Word) : Option Machine := do
  let mem ← m.mem.writeBytes cell.addr (wordToLE v)
  pure { m with mem := mem }

/-- Entry machine with a single initialized cell in input. -/
def Machine.entryWithCell (cell : InputCell) (value : Word)
    (maxDepth : Nat := defaultMaxCallDepth) : Machine :=
  Machine.entry (mkInputWithCell cell value) #[] maxDepth

end SbpfSemantics
