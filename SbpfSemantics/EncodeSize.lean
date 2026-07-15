import SbpfSemantics.Encode
import SbpfSemantics.Instr
import SbpfSemantics.ByteLayout

/-!
# SbpfSemantics.EncodeSize

Encoded byte length matches `Instr.sizeBytes` and program `totalBytes`.
-/

namespace SbpfSemantics

theorem imm32Bytes_size (w : Word) : (imm32Bytes w).size = 4 := by
  simp [imm32Bytes]

/-- Every instruction encodes to exactly `sizeBytes` bytes (8, or 16 for `lddw`). -/
theorem encodeInstr_size (i : Instr) :
    (encodeInstr i).size = i.sizeBytes := by
  dsimp [encodeInstr, Instr.sizeBytes, Opcode.sizeBytes]
  split
  · simp [imm32Bytes]
  · simp [imm32Bytes]

/-- Additive fold of instruction sizes is linear in the initial accumulator. -/
theorem foldl_sizeBytes (init : Nat) (xs : List Instr) :
    xs.foldl (fun n i => n + i.sizeBytes) init =
      init + xs.foldl (fun n i => n + i.sizeBytes) 0 := by
  induction xs generalizing init with
  | nil => simp
  | cons i rest ih =>
      simp only [List.foldl_cons]
      rw [ih (init + i.sizeBytes), ih (0 + i.sizeBytes)]
      omega

theorem foldl_encode_size (acc : Array UInt8) (xs : List Instr) :
    (xs.foldl (fun a i => a ++ encodeInstr i) acc).size =
      acc.size + xs.foldl (fun n i => n + i.sizeBytes) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons i rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Array.size_append, encodeInstr_size]
      -- goal: acc.size + i.sizeBytes + foldl rest 0
      --      = acc.size + foldl rest (0 + i.sizeBytes)
      rw [foldl_sizeBytes (0 + i.sizeBytes) rest]
      omega

theorem encodeProgram_size (P : Program) :
    (encodeProgram P).size = P.totalBytes := by
  simp only [encodeProgram, Program.totalBytes]
  have h := foldl_encode_size #[] P.toList
  simpa [Array.foldl_toList] using h

example : (encodeInstr .exit).size = 8 :=
  encodeInstr_size .exit

example : (encodeInstr (.lddw ⟨0, by omega⟩ 1#64)).size = 16 :=
  encodeInstr_size (.lddw ⟨0, by omega⟩ 1#64)

end SbpfSemantics
