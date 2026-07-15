import SbpfSemantics.Encode
import SbpfSemantics.Opcode

/-!
# SbpfSemantics.EncodeLemmas

Encode/decode facts for V3-safe opcodes and concrete instruction round-trips.
-/

namespace SbpfSemantics

/-- V3-safe: decode of the encoded opcode byte recovers `op`. -/
theorem Opcode.ofByteV3_toByte_of_v3RoundTrip (op : Opcode)
    (h : Opcode.v3RoundTrip op = true) :
    Opcode.ofByteV3? op.toByte = some op := by
  simp only [Opcode.v3RoundTrip] at h
  cases h' : Opcode.ofByteV3? op.toByte with
  | none => simp [h'] at h
  | some op' =>
      simp only [h', beq_iff_eq] at h
      exact h ▸ rfl

/-- Concrete: `Add64Imm` is V3-safe. -/
theorem add64Imm_v3RoundTrip : Opcode.v3RoundTrip .Add64Imm = true := by native_decide

theorem add64Imm_ofByte_toByte :
    Opcode.ofByteV3? Opcode.Add64Imm.toByte = some .Add64Imm := by native_decide

/-- Concrete encode/decode recovers opcode for `mov64 r0, 42`. -/
theorem encode_decode_mov64_opcode :
    (decodeInstr? (encodeInstr (.binImm .Mov64Imm ⟨0, by omega⟩ 42#64)) 0).map (·.1.opcode)
      = some .Mov64Imm := by
  native_decide

/-- Concrete encode/decode recovers opcode for `add64 r1, 10`. -/
theorem encode_decode_add64_opcode :
    (decodeInstr? (encodeInstr (.binImm .Add64Imm ⟨1, by omega⟩ 10#64)) 0).map (·.1.opcode)
      = some .Add64Imm := by
  native_decide

/-- Concrete encode/decode recovers opcode for `ja +2`. -/
theorem encode_decode_ja_opcode :
    (decodeInstr? (encodeInstr (.ja (BitVec.ofInt 16 2))) 0).map (·.1.opcode)
      = some .Ja := by
  native_decide

/-- `lddw` wide encoding is 16 bytes and decodes as `Lddw`. -/
theorem encode_decode_lddw_opcode :
    let bs := encodeInstr (.lddw ⟨2, by omega⟩ 0x1122334455667788#64)
    bs.size = 16 ∧
      (decodeInstr? bs 0).map (·.1.opcode) = some .Lddw := by
  native_decide

/-- Displaced classic opcode does not V3-round-trip (documents V3 jump32 override). -/
theorem udiv32Imm_not_v3RoundTrip : Opcode.v3RoundTrip .Udiv32Imm = false := by
  native_decide

theorem jset32Imm_v3RoundTrip : Opcode.v3RoundTrip .Jset32Imm = true := by
  native_decide

end SbpfSemantics
