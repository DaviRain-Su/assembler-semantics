import SbpfSemantics.EncodePreserve
import SbpfSemantics.Step

/-!
# SbpfSemantics.SameExec

General lemmas connecting `sameExec` to `execInstr`:

* `forExec` projects to fields that `execInstr` reads.
* `execInstr_forExec`: execution ignores non-relevant fields.
* `sameExec_execInstr`: `sameExec i j` ⇒ equal `execInstr` results.
-/

namespace SbpfSemantics

/-- Fields that affect `execInstr` for this opcode class (others cleared). -/
def Instr.forExec (i : Instr) : Instr :=
  match i.opcode.opClass with
  | .loadImm =>
      { opcode := i.opcode, dst := i.dst, imm := i.imm }
  | .loadMem =>
      { opcode := i.opcode, dst := i.dst, src := i.src, off := i.off }
  | .storeImm =>
      { opcode := i.opcode, dst := i.dst, off := i.off, imm := i.imm }
  | .storeReg =>
      { opcode := i.opcode, dst := i.dst, src := i.src, off := i.off }
  | .binImm =>
      { opcode := i.opcode, dst := i.dst, imm := i.imm }
  | .binReg =>
      { opcode := i.opcode, dst := i.dst, src := i.src }
  | .unary =>
      { opcode := i.opcode, dst := i.dst }
  | .endian =>
      { opcode := i.opcode, dst := i.dst, imm := i.imm }
  | .jump =>
      { opcode := i.opcode, off := i.off }
  | .jumpImm | .jump32Imm =>
      { opcode := i.opcode, dst := i.dst, imm := i.imm, off := i.off }
  | .jumpReg | .jump32Reg =>
      { opcode := i.opcode, dst := i.dst, src := i.src, off := i.off }
  | .callImm =>
      { opcode := i.opcode, imm := i.imm, syscall := i.syscall }
  | .callReg =>
      { opcode := i.opcode, dst := i.dst }
  | .exit =>
      { opcode := i.opcode }

/-- `execInstr` depends only on `forExec` fields. -/
theorem execInstr_forExec (D : ExecDialect) (m : Machine) (i : Instr) :
    execInstr D m i = execInstr D m (Instr.forExec i) := by
  rcases i with ⟨op, dst, src, off, imm, sys⟩
  cases op <;> simp [execInstr, Instr.forExec, Opcode.opClass]

/-- From Boolean `sameExec`, recover equality of `forExec` projections. -/
theorem sameExec_forExec_eq (i j : Instr) (h : Instr.sameExec i j = true) :
    Instr.forExec i = Instr.forExec j := by
  rcases i with ⟨opi, di, si, oi, ii, yi⟩
  rcases j with ⟨opj, dj, sj, oj, ij, yj⟩
  simp only [Instr.sameExec, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hop, hrest⟩ := h
  cases hop
  -- opi = opj
  simp only [Instr.forExec, Opcode.opClass] at hrest ⊢
  cases opi <;> simp_all [beq_iff_eq, Bool.and_eq_true]

/-- **Main theorem:** execution-relevant equality implies equal `execInstr`. -/
theorem sameExec_execInstr (D : ExecDialect) (m : Machine) (i j : Instr)
    (h : Instr.sameExec i j = true) :
    execInstr D m i = execInstr D m j := by
  have hfe := sameExec_forExec_eq i j h
  calc
    execInstr D m i = execInstr D m (Instr.forExec i) := execInstr_forExec D m i
    _ = execInstr D m (Instr.forExec j) := by rw [hfe]
    _ = execInstr D m j := (execInstr_forExec D m j).symm

/-- Successful normalize with `sameExec` preserves execution. -/
theorem normalize_execInstr (D : ExecDialect) (m : Machine) (i j : Instr)
    (_hn : decodeEncode? i = some j) (hrt : Instr.sameExec i j = true) :
    execInstr D m i = execInstr D m j :=
  sameExec_execInstr D m i j hrt

/-- If `roundTripSameExec i`, normalize preserves `execInstr`. -/
theorem roundTripSameExec_execInstr (D : ExecDialect) (m : Machine) (i : Instr)
    (h : roundTripSameExec i = true) :
    match decodeEncode? i with
    | none => True
    | some j => execInstr D m i = execInstr D m j := by
  simp only [roundTripSameExec] at h
  cases hde : decodeEncode? i with
  | none => simp
  | some j =>
      simp only [hde] at h
      exact sameExec_execInstr D m i j h

end SbpfSemantics
