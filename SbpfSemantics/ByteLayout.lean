import SbpfSemantics.Instr
import SbpfSemantics.Encode

/-!
# SbpfSemantics.ByteLayout

Map between **instruction-index PC** (list machine) and **byte offset PC**
(bytecode stream). Used to step encoded programs without changing L4 ground
truth (`execStep` still runs on list indices).

Definitions are **list prefix-sums** so layout facts (length, mono, index↔byte)
are provable without `Id.run` loops.
-/

namespace SbpfSemantics

/-! ### Instruction width -/

/-- Encoded width is always 8 or 16 bytes. -/
theorem sizeBytes_eq_eight_or_sixteen (i : Instr) :
    i.sizeBytes = 8 ∨ i.sizeBytes = 16 := by
  simp only [Instr.sizeBytes, Opcode.sizeBytes]
  split <;> simp

theorem sizeBytes_pos (i : Instr) : 0 < i.sizeBytes := by
  cases sizeBytes_eq_eight_or_sixteen i with
  | inl h => omega
  | inr h => omega

theorem sizeBytes_ge_eight (i : Instr) : 8 ≤ i.sizeBytes := by
  cases sizeBytes_eq_eight_or_sixteen i with
  | inl h => omega
  | inr h => omega

/-! ### Prefix-sum layout -/

/-- Start byte offsets for each instruction, beginning at `start`. -/
def offsetsFrom : List Instr → Nat → List Nat
  | [], _ => []
  | i :: rest, start => start :: offsetsFrom rest (start + i.sizeBytes)

/-- Start byte offset of each instruction; `offsets.size = P.size`. -/
def Program.byteOffsets (P : Program) : Array Nat :=
  (offsetsFrom P.toList 0).toArray

/-- Total encoded size in bytes. -/
def Program.totalBytes (P : Program) : Nat :=
  P.foldl (init := 0) fun n i => n + i.sizeBytes

/-- Linear search: first list index whose offset equals `b`. -/
def findOffsetIdx : List Nat → Nat → Nat → Option Nat
  | [], _, _ => none
  | o :: rest, b, idx => if o == b then some idx else findOffsetIdx rest b (idx + 1)

/-- Look up list index whose instruction starts at exact byte offset `b`. -/
def byteOffsetToIndex? (offsets : Array Nat) (b : Nat) : Option Nat :=
  findOffsetIdx offsets.toList b 0

/-- Byte offset of instruction index `pc` (if in range). -/
def indexToByteOffset? (offsets : Array Nat) (pc : Nat) : Option Nat :=
  offsets[pc]?

/-! ### offsetsFrom basics -/

theorem offsetsFrom_length (xs : List Instr) (start : Nat) :
    (offsetsFrom xs start).length = xs.length := by
  induction xs generalizing start with
  | nil => rfl
  | cons _i rest ih => simp [offsetsFrom, ih]

theorem byteOffsets_size (P : Program) : P.byteOffsets.size = P.size := by
  simp [Program.byteOffsets, offsetsFrom_length]

theorem offsetsFrom_cons (i : Instr) (rest : List Instr) (start : Nat) :
    offsetsFrom (i :: rest) start =
      start :: offsetsFrom rest (start + i.sizeBytes) :=
  rfl

/-- Every listed offset is at least `start`. -/
theorem offsetsFrom_mem_ge (xs : List Instr) (start : Nat) :
    ∀ o ∈ offsetsFrom xs start, start ≤ o := by
  induction xs generalizing start with
  | nil =>
      intro o h; cases h
  | cons i rest ih =>
      intro o h
      simp only [offsetsFrom, List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_refl _
      · have := ih (start + i.sizeBytes) o h
        have hi := sizeBytes_pos i
        omega

/-- Offsets of the tail are strictly past the head start. -/
theorem offsetsFrom_tail_gt (i : Instr) (rest : List Instr) (start : Nat) :
    ∀ o ∈ offsetsFrom rest (start + i.sizeBytes), start < o := by
  intro o h
  have := offsetsFrom_mem_ge rest (start + i.sizeBytes) o h
  have hi := sizeBytes_pos i
  omega

/-! ### findOffsetIdx -/

theorem findOffsetIdx_cons_ne (o b : Nat) (rest : List Nat) (idx : Nat) (h : o ≠ b) :
    findOffsetIdx (o :: rest) b idx = findOffsetIdx rest b (idx + 1) := by
  simp [findOffsetIdx, h]

/-- Shifting the search base adds to a successful index. -/
theorem findOffsetIdx_base_add (xs : List Nat) (b base : Nat) :
    findOffsetIdx xs b base =
      (findOffsetIdx xs b 0).map (fun k => k + base) := by
  induction xs generalizing base with
  | nil => simp [findOffsetIdx]
  | cons o rest ih =>
      by_cases heq : o = b
      · subst heq
        simp [findOffsetIdx]
      · have h1 := ih (base + 1)
        have h0 := ih 1
        simp only [findOffsetIdx, beq_iff_eq, heq, ↓reduceIte]
        -- both sides reduce to findOffsetIdx rest ...
        cases hr : findOffsetIdx rest b 0 with
        | none =>
            simp [h1, h0, hr]
        | some k =>
            simp [h1, h0, hr]
            omega

/-! ### Index → byte → index (core) -/

/-- Looking up the byte offset of list index `pc` recovers `pc`. -/
theorem findOffsetIdx_offsetsFrom (xs : List Instr) (start pc : Nat)
    (h : pc < xs.length) :
    findOffsetIdx (offsetsFrom xs start)
        ((offsetsFrom xs start)[pc]'(by simpa [offsetsFrom_length] using h)) 0 =
      some pc := by
  induction xs generalizing start pc with
  | nil => cases h
  | cons i rest ih =>
      cases pc with
      | zero =>
          simp [offsetsFrom, findOffsetIdx]
      | succ pc =>
          have hpc : pc < rest.length := by
            simp only [List.length_cons] at h
            omega
          -- Unfold head
          simp only [offsetsFrom, List.getElem_cons_succ]
          -- b = tail[pc]
          have hb_mem :
              (offsetsFrom rest (start + i.sizeBytes))[pc]'(by
                  simpa [offsetsFrom_length] using hpc) ∈
                offsetsFrom rest (start + i.sizeBytes) :=
            List.getElem_mem _
          have hne : start ≠
              (offsetsFrom rest (start + i.sizeBytes))[pc]'(by
                  simpa [offsetsFrom_length] using hpc) := by
            have := offsetsFrom_tail_gt i rest start _ hb_mem
            omega
          rw [findOffsetIdx_cons_ne start _ _ 0 hne]
          -- IH at base 0
          have ih0 := ih (start + i.sizeBytes) pc hpc
          -- shift base 0 → 1
          have hshift :=
            findOffsetIdx_base_add
              (offsetsFrom rest (start + i.sizeBytes))
              ((offsetsFrom rest (start + i.sizeBytes))[pc]'(by
                  simpa [offsetsFrom_length] using hpc))
              1
          -- find ... 1 = map (+1) (find ... 0) = map (+1) (some pc) = some (pc+1)
          rw [hshift, ih0]
          simp

/-- Array/list bridge for `byteOffsets`. -/
theorem byteOffsets_toList (P : Program) :
    P.byteOffsets.toList = offsetsFrom P.toList 0 := by
  simp [Program.byteOffsets]

theorem byteOffsets_getElem (P : Program) (pc : Nat) (h : pc < P.size) :
    P.byteOffsets[pc]'(by simpa [byteOffsets_size] using h) =
      (offsetsFrom P.toList 0)[pc]'(by
        simpa [offsetsFrom_length, Array.length_toList] using h) := by
  simp [Program.byteOffsets]

/-- Program form: index → byte → index. -/
theorem index_to_byte_to_index (P : Program) (pc : Nat) (h : pc < P.size) :
    byteOffsetToIndex? P.byteOffsets
        (P.byteOffsets[pc]'(by simpa [byteOffsets_size] using h)) = some pc := by
  simp only [byteOffsetToIndex?, byteOffsets_toList, byteOffsets_getElem P pc h]
  exact findOffsetIdx_offsetsFrom P.toList 0 pc (by
    simpa [Array.length_toList] using h)

/-- `indexToByteOffset?` is array indexing. -/
theorem indexToByteOffset?_eq (offsets : Array Nat) (pc : Nat) :
    indexToByteOffset? offsets pc = offsets[pc]? :=
  rfl

/-- In-range PC yields `some` byte offset. -/
theorem indexToByteOffset?_isSome (P : Program) (pc : Nat) (h : pc < P.size) :
    ∃ b, indexToByteOffset? P.byteOffsets pc = some b := by
  refine ⟨P.byteOffsets[pc]'(by simpa [byteOffsets_size] using h), ?_⟩
  simp only [indexToByteOffset?]
  exact Array.getElem?_eq_getElem _

/-- Option-form round-trip: index → byte → index. -/
theorem indexToByte_byteToIndex (P : Program) (pc : Nat) (h : pc < P.size) :
    (indexToByteOffset? P.byteOffsets pc).bind (byteOffsetToIndex? P.byteOffsets) =
      some pc := by
  have hpc : pc < P.byteOffsets.size := by simpa [byteOffsets_size] using h
  have hb : indexToByteOffset? P.byteOffsets pc =
      some (P.byteOffsets[pc]'hpc) := by
    simp only [indexToByteOffset?]
    exact Array.getElem?_eq_getElem hpc
  simp only [hb, Option.bind_some]
  exact index_to_byte_to_index P pc h

/-- Byte → index → byte when `b` is the start of instruction `pc`. -/
theorem byte_to_index_to_byte (P : Program) (pc : Nat) (h : pc < P.size) :
    let b := P.byteOffsets[pc]'(by simpa [byteOffsets_size] using h)
    (byteOffsetToIndex? P.byteOffsets b).bind (indexToByteOffset? P.byteOffsets) =
      some b := by
  intro b
  rw [index_to_byte_to_index P pc h, Option.bind_some]
  have hpc : pc < P.byteOffsets.size := by simpa [byteOffsets_size] using h
  simp only [indexToByteOffset?, Array.getElem?_eq_getElem hpc]
  rfl

/-- First instruction of a non-empty program starts at byte 0. -/
theorem byteOffsets_zero (P : Program) (h : 0 < P.size) :
    P.byteOffsets[0]'(by simpa [byteOffsets_size] using h) = 0 := by
  -- P.toList is non-empty when size > 0
  have hlen : 0 < P.toList.length := by
    simpa using h
  cases hxs : P.toList with
  | nil =>
      simp [hxs] at hlen
  | cons i rest =>
      -- rewrite byteOffsets via toList
      have : P.byteOffsets = (offsetsFrom (i :: rest) 0).toArray := by
        simp [Program.byteOffsets, hxs]
      simp [this, offsetsFrom]

/-! ### Samples (regression) -/

theorem encode_size_eq_totalBytes_sample :
    let P : Program := #[
      Instr.binImm .Mov64Imm ⟨0, by omega⟩ 1#64,
      Instr.lddw ⟨1, by omega⟩ 0x100#64,
      Instr.exit
    ]
    (encodeProgram P).size = P.totalBytes := by
  native_decide

example :
    let P : Program := #[Instr.lddw ⟨0, by omega⟩ 0#64, Instr.exit]
    P.byteOffsets = #[0, 16] ∧ P.totalBytes = 24 := by
  native_decide

example :
    let P : Program := #[Instr.exit, Instr.binImm .Add64Imm ⟨0, by omega⟩ 1#64]
    byteOffsetToIndex? P.byteOffsets 8 = some 1 := by
  native_decide

example :
    let P : Program := #[Instr.exit, Instr.binImm .Add64Imm ⟨0, by omega⟩ 1#64]
    byteOffsetToIndex? P.byteOffsets (P.byteOffsets[0]!) = some 0 ∧
      byteOffsetToIndex? P.byteOffsets (P.byteOffsets[1]!) = some 1 := by
  native_decide

end SbpfSemantics
