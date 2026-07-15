import SbpfSemantics.EncodePreserve
import SbpfSemantics.WellFormed
import SbpfSemantics.Coverage
import SbpfSemantics.Opcode
import SbpfSemantics.EncodeSize

/-!
# SbpfSemantics.RoundTrip

Stronger round-trip coverage: every **V3-safe** opcode has at least one
`encodable` witness instruction that `roundTripSameExec`s, plus structural
lemmas for common constructors and an encode-size link.

A full `∀ i, encodable i → roundTripSameExec i` is the ideal statement; proving
it in general needs a complete case analysis on encode/decode. Here we certify
the property on a **complete opcode witness table** and constructor families
that cover the practical integrator surface.
-/

namespace SbpfSemantics

private def r0 : Reg := ⟨0, by omega⟩
private def r1 : Reg := ⟨1, by omega⟩

/-- Build a minimal encodable instruction for a V3-safe opcode, if possible. -/
def witnessFor (op : Opcode) : Option Instr :=
  if !Opcode.v3RoundTrip op then none
  else
    let i : Instr :=
      match op.opClass with
      | .loadImm => .lddw r0 0x0123456789abcdef#64
      | .loadMem => .loadMem op r0 r1 0#16
      | .storeImm => .storeImm op r0 0#16 0#64
      | .storeReg => .storeReg op r0 r1 0#16
      | .binImm => .binImm op r0 1#64
      | .binReg => .binReg op r0 r1
      | .unary => .unary op r0
      | .endian => { opcode := op, dst := some r0, imm := some 64#64 }
      | .jump => .ja 1#16
      | .jumpImm | .jump32Imm => .jumpImm op r0 0#64 1#16
      | .jumpReg | .jump32Reg => .jumpReg op r0 r1 1#16
      | .callImm => .callRel 1#64
      | .callReg => .callx r0
      | .exit => .exit
    if Instr.encodable i then some i else none

/-- All V3-safe opcodes admit a round-tripping witness. -/
def allV3SafeWitnessRoundTrip : Bool :=
  allOpcodes.all fun op =>
    if Opcode.v3RoundTrip op then
      match witnessFor op with
      | none => false
      | some i => roundTripSameExec i
    else true

theorem all_v3_safe_opcodes_have_roundtrip_witness :
    allV3SafeWitnessRoundTrip = true := by
  native_decide

/-- Count of V3-safe opcodes (witness domain). -/
def v3SafeOpcodeCount : Nat :=
  allOpcodes.foldl (init := 0) fun n op =>
    if Opcode.v3RoundTrip op then n + 1 else n

example : v3SafeOpcodeCount ≥ 100 := by native_decide

/-- Every witness is encodable when present. -/
def allWitnessesEncodable : Bool :=
  allOpcodes.all fun op =>
    match witnessFor op with
    | none => true
    | some i => Instr.encodable i

theorem witnesses_encodable : allWitnessesEncodable = true := by
  native_decide

/-- Expanded imm battery for binImm ops. -/
def binImmBattery : Array Instr :=
  #[0, 1, 2, 255, 256, 0x7fffffff, BitVec.ofInt 64 (-1), BitVec.ofInt 64 (-128)].map
    (fun imm => .binImm .Add64Imm r0 imm)

theorem binImm_battery_roundTrip :
    binImmBattery.all (fun i => !Instr.encodable i || roundTripSameExec i) = true := by
  native_decide

/-! ### Structural constructor lemmas (concrete + batteries) -/

theorem roundTrip_exit : roundTripSameExec .exit = true := by native_decide

theorem roundTrip_ja_pos : roundTripSameExec (.ja 5#16) = true := by native_decide
theorem roundTrip_ja_neg :
    roundTripSameExec (.ja (BitVec.ofInt 16 (-3))) = true := by native_decide

theorem roundTrip_mov64_sample :
    roundTripSameExec (.binImm .Mov64Imm r0 42#64) = true := by native_decide

theorem roundTrip_lddw_sample :
    roundTripSameExec (.lddw r0 0xdeadbeefcafebabe#64) = true := by native_decide

theorem roundTrip_callx_sample :
    roundTripSameExec (.callx r0) = true := by native_decide

/-- Offsets battery for unconditional jumps. -/
def jaBattery : Array Instr :=
  #[0, 1, 2, 7, BitVec.ofInt 16 (-1), BitVec.ofInt 16 (-8)].map Instr.ja

theorem ja_battery_roundTrip :
    jaBattery.all roundTripSameExec = true := by native_decide

/-- lddw imm battery. -/
def lddwBattery : Array Instr :=
  #[0, 1, 0xffffffff#64, 0x0123456789abcdef#64].map (fun imm => .lddw r0 imm)

theorem lddw_battery_roundTrip :
    lddwBattery.all roundTripSameExec = true := by native_decide

/-- Encodable witnesses also have correct encode size. -/
def witnessesEncodeSizeOk : Bool :=
  allOpcodes.all fun op =>
    match witnessFor op with
    | none => true
    | some i => (encodeInstr i).size == i.sizeBytes

theorem witnesses_encode_size : witnessesEncodeSizeOk = true := by
  native_decide

/-- Link: `encodeInstr_size` holds definitionally for every instruction. -/
theorem encode_size_of_any (i : Instr) :
    (encodeInstr i).size = i.sizeBytes :=
  encodeInstr_size i

/-- Cross-class samples (from EncodePreserve) all round-trip. -/
theorem encodePreserve_roundTrip :
    encodePreserveSamples.all roundTripSameExec = true :=
  samples_all_roundTrip

end SbpfSemantics
