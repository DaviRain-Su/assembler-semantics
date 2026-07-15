import SbpfSemantics.ByteStep
import SbpfSemantics.Step
import SbpfSemantics.Run

/-!
# SbpfSemantics.ByteBisim

List-PC vs byte-PC agreement.

**Definitional link:** `execStepBytes` is implemented by converting byte PC → list
index, running list `execStep`, then converting the result PC back to a byte
offset (or freezing the byte PC on halt). Therefore, for any program whose
`byteOffsets` are a correct layout of `P`, multi-step runs agree on
registers / halt / returnData whenever the byte PC stays aligned to instruction
starts (the normal case for sequential and jump execution).

We certify this with:

1. A **definitional** lemma that `{ m with pc := m.pc } = m`.
2. A fuel-bounded **computational bisimulation** checker over representative
   programs (including jumps, `lddw`, calls).
3. Outcome agreement (`runFuel` vs `runFuelBytes`) on the same suite.

A fully general `∀ fuel` coinductive bisimulation is future work; the suite plus
the definitional reduction of `execStepBytes` is the integrator guarantee.
-/

namespace SbpfSemantics

/-- Structure update at the current PC is the identity (byte-step uses this shape).

In Lean this is definitional after eta for structures, so both sides reduce equal. -/
theorem machine_with_pc_id (m : Machine) : { m with pc := m.pc } = m :=
  rfl

/-- `execStep` is insensitive to a no-op PC rewrite. -/
theorem execStep_with_pc_id (D : ExecDialect) (P : Program) (m : Machine) :
    execStep D P { m with pc := m.pc } = execStep D P m :=
  rfl

/-- Fuel-bounded lockstep: list and byte machines agree on observable state. -/
def bisimFuel (D : ExecDialect) (P : Program) (fuel : Nat) (mList : Machine) : Bool :=
  match toBytePc P mList with
  | none => mList.halted.isSome
  | some mByte =>
      let rec go (fuel : Nat) (mL mB : Machine) : Bool :=
        match fuel with
        | 0 => true
        | fuel + 1 =>
          match mL.halted, mB.halted with
          | some c1, some c2 => c1 == c2
          | none, none =>
              match execStep D P mL, execStepBytes D P mB with
              | none, none => true
              | some mL', some mB' =>
                  mL'.regs.toList == mB'.regs.toList &&
                  mL'.halted == mB'.halted &&
                  mL'.returnData == mB'.returnData &&
                  (if mL'.halted.isSome then true
                   else
                    match toBytePc P mL' with
                    | some mLb => mLb.pc == mB'.pc
                    | none => false) &&
                  go fuel mL' mB'
              | _, _ => false
          | _, _ => false
      go fuel mList mByte

private def r0 : Reg := ⟨0, by omega⟩

def bisimProgs : Array Program := #[
  #[.binImm .Mov64Imm r0 2#64, .binImm .Add64Imm r0 3#64, .exit],
  #[.binImm .Mov64Imm r0 0#64, .jumpImm .JeqImm r0 0#64 (BitVec.ofInt 16 1),
    .binImm .Add64Imm r0 1#64, .exit],
  #[.binImm .Mov64Imm r0 1#64, .jumpImm .JneImm r0 0#64 (BitVec.ofInt 16 1),
    .binImm .Add64Imm r0 9#64, .exit],
  #[.lddw r0 0x100#64, .binImm .Add64Imm r0 1#64, .exit],
  #[.binImm .Mov64Imm r0 1#64, .unary .Neg64 r0, .exit],
  #[.callRel 1#64, .exit, .binImm .Mov64Imm r0 7#64, .exit],
  #[.binImm .Mov64Imm r0 5#64, .binReg .Mov64Reg ⟨1, by omega⟩ r0,
    .binReg .Add64Reg r0 ⟨1, by omega⟩, .exit]
]

theorem bisim_progs_ok :
    bisimProgs.all (fun P => bisimFuel closedExec P 64 (Machine.entry)) = true := by
  native_decide

theorem bisim_entry_byte0 :
    (toBytePc byteStepSampleProg (Machine.entry)).map (·.pc) = some 0 := by
  native_decide

/-- Multi-fuel run outcomes match on the sample suite. -/
def runOutcomeAgree (P : Program) : Bool :=
  let oL := (runFuel closedExec P 64 (Machine.entry)).2
  let oB := (runFuelBytes closedExec P 64 (entryBytes)).2
  oL == oB

theorem bisim_progs_run_outcomes :
    bisimProgs.all runOutcomeAgree = true := by
  native_decide

/-- Sample: first instruction offset maps back (layout injectivity at starts). -/
theorem sample_offset_roundtrip :
    let P := byteStepSampleProg
    let b := (P.byteOffsets)[0]!
    byteOffsetToIndex? P.byteOffsets b = some 0 := by
  native_decide

/-- Concrete one-step: list and byte agree after first mov (from ByteStep). -/
theorem sample_step_regs_agree :
    listByteStepAgree closedExec byteStepSampleProg (Machine.entry) = true :=
  sample_first_step_list_byte_agree

end SbpfSemantics
