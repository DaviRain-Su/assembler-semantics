import SbpfSemantics.ByteLayout
import SbpfSemantics.Step
import SbpfSemantics.Run
import SbpfSemantics.EncodePreserve
import SbpfSemantics.SameExec
import SbpfSemantics.Observation

/-!
# SbpfSemantics.ByteStep

**Byte-PC execution** over `encodeProgram P`, implemented by:

1. mapping byte PC → list index via `byteOffsets`;
2. taking a list-machine `execStep`;
3. mapping the resulting list PC back to a byte offset.

Ground truth remains the list machine; this is the integration view for
bytecode consumers (and a step toward linking L3 streams to L4).
-/

namespace SbpfSemantics

/-- One step where `m.pc` is a **byte** offset into `encodeProgram P`. -/
def execStepBytes (D : ExecDialect) (P : Program) (m : Machine) : Option Machine :=
  if m.halted.isSome then none
  else
    let offs := P.byteOffsets
    match byteOffsetToIndex? offs m.pc with
    | none => none
    | some listPc =>
        let mList := { m with pc := listPc }
        match execStep D P mList with
        | none => none
        | some m' =>
            if m'.halted.isSome then
              -- keep byte PC at the faulting/exit instruction start
              some { m' with pc := m.pc }
            else
              match indexToByteOffset? offs m'.pc with
              | some b => some { m' with pc := b }
              | none => none

/-- Fuel runner for byte-PC machines. -/
def runFuelBytes (D : ExecDialect) (P : Program) : Nat → Machine → Machine × Outcome
  | 0, m =>
      match m.halted with
      | some c => (m, .halted c)
      | none => (m, .outOfFuel)
  | fuel + 1, m =>
      match m.halted with
      | some c => (m, .halted c)
      | none =>
        match execStepBytes D P m with
        | none => (m, .stuck)
        | some m' => runFuelBytes D P fuel m'

/-- Entry machine with byte PC = 0 (same as list PC 0). -/
def entryBytes (input : Array UInt8 := #[]) (rodata : Array UInt8 := #[]) : Machine :=
  Machine.entry input rodata  -- pc = 0

/-- Lift a list-PC machine to byte-PC using program layout. -/
def toBytePc (P : Program) (m : Machine) : Option Machine :=
  match indexToByteOffset? P.byteOffsets m.pc with
  | some b => some { m with pc := b }
  | none =>
      if m.halted.isSome then some m else none

/-- Project byte-PC machine back to list-PC. -/
def toListPc (P : Program) (m : Machine) : Option Machine :=
  if m.halted.isSome then
    -- recover list index of current byte pc if possible
    match byteOffsetToIndex? P.byteOffsets m.pc with
    | some i => some { m with pc := i }
    | none => some m
  else
    match byteOffsetToIndex? P.byteOffsets m.pc with
    | some i => some { m with pc := i }
    | none => none

/-! ### Agreement samples (list PC vs byte PC) -/

private def r0 : Reg := ⟨0, by omega⟩

def byteStepSampleProg : Program :=
  #[
    .binImm .Mov64Imm r0 2#64,
    .binImm .Add64Imm r0 3#64,
    .exit
  ]

/-- One sequential step: list and byte machines agree on regs/halt after convert. -/
def listByteStepAgree (D : ExecDialect) (P : Program) (mList : Machine) : Bool :=
  match execStep D P mList, toBytePc P mList with
  | none, _ => true  -- both should stuck similarly only if byte also fails
  | some mL', some mB0 =>
      match execStepBytes D P mB0, toBytePc P mL' with
      | some mB', some mL'b =>
          mB'.getReg r0 == mL'b.getReg r0 &&
          mB'.halted == mL'b.halted &&
          mB'.pc == mL'b.pc
      | none, none => true
      | _, _ => false
  | some _, none => false

theorem sample_first_step_list_byte_agree :
    listByteStepAgree closedExec byteStepSampleProg (Machine.entry) = true := by
  native_decide

/-- Full run: halt code matches list `runFuel`. -/
theorem sample_run_list_byte_halt :
    let P := byteStepSampleProg
    let oL := (runFuel closedExec P 20 (Machine.entry)).2
    let oB := (runFuelBytes closedExec P 20 (entryBytes)).2
    (oL == .halted 5#64) && (oB == .halted 5#64) = true := by
  native_decide

/-- Jump program agreement on halt. -/
def byteJumpProg : Program :=
  #[
    .binImm .Mov64Imm r0 0#64,
    .jumpImm .JeqImm r0 0#64 (BitVec.ofInt 16 1),
    .binImm .Add64Imm r0 1#64,
    .exit
  ]

theorem jump_run_list_byte_halt :
    let oL := (runFuel closedExec byteJumpProg 30 (Machine.entry)).2
    let oB := (runFuelBytes closedExec byteJumpProg 30 (entryBytes)).2
    (oL == .halted 0#64) && (oB == .halted 0#64) = true := by
  native_decide

/-- Encoded stream length equals layout total; decode recovers length. -/
theorem sample_encode_decode_len :
    let P := byteStepSampleProg
    let bs := encodeProgram P
    bs.size = P.totalBytes &&
      (decodeProgram? bs).map (·.size) == some P.size := by
  native_decide

/-- After redecode, byte-step run still halts the same. -/
def redecode_byte_run_ok : Bool :=
  let P := byteStepSampleProg
  match redecodeProgram? P with
  | none => false
  | some P' =>
      (runFuelBytes closedExec P' 20 (entryBytes)).2 == .halted 5#64

theorem sample_redecode_byte_run : redecode_byte_run_ok = true := by
  native_decide

end SbpfSemantics
