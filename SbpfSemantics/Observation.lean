import SbpfSemantics.Basic
import SbpfSemantics.Machine
import SbpfSemantics.Step
import SbpfSemantics.Run
import SbpfSemantics.Interp
import SbpfSemantics.Dialect

/-!
# SbpfSemantics.Observation

Frame-boundary observations for ProofForge differential testing.

ProofForge should compare `Observation` values (and optional memory windows),
not full `Machine` equality. See `docs/proof-forge-interface.md`.
-/

namespace SbpfSemantics

/-- Portable observation of a finished (or stuck) run. -/
structure Observation where
  outcome    : Outcome
  r0         : Word
  r1         : Word
  r10        : Word
  pc         : Nat
  halted     : Option Word
  returnData : Array UInt8 := #[]
  deriving DecidableEq, Repr

/-- Project machine + outcome to an observation. -/
def observe (m : Machine) (o : Outcome) : Observation where
  outcome := o
  r0 := m.getReg ⟨0, by omega⟩
  r1 := m.getReg ⟨1, by omega⟩
  r10 := m.getReg ⟨10, by omega⟩
  pc := m.pc
  halted := m.halted
  returnData := m.returnData

/-- Fuel run returning the final observation. -/
def runObserved (D : ExecDialect) (P : Program) (fuel : Nat) (m : Machine) : Observation :=
  let (m', o) := runFuel D P fuel m
  observe m' o

def runObservedEntry (D : ExecDialect) (P : Program) (fuel : Nat)
    (input : Array UInt8 := #[]) (rodata : Array UInt8 := #[]) : Observation :=
  runObserved D P fuel (Machine.entry input rodata)

/-- Optional memory window for account-data style diffs. -/
structure MemWindow where
  addr : Word
  len  : Nat
  deriving Repr

/-- Read a window; `none` if any byte is OOB. -/
def Machine.readWindow (m : Machine) (w : MemWindow) : Option (Array UInt8) :=
  m.mem.readBytes w.addr w.len

/-- Two observations agree on control/result fields (PF Phase-1 default). -/
def Observation.controlEq (a b : Observation) : Prop :=
  a.outcome = b.outcome ∧ a.r0 = b.r0

/-- Decidable control equality for tests. -/
def Observation.controlEqb (a b : Observation) : Bool :=
  decide (a.outcome = b.outcome) && decide (a.r0 = b.r0)

/-- One step of an observed multi-step trace (for lockstep with IR). -/
structure TraceEvent where
  pcBefore : Nat
  r0       : Word
  r1       : Word
  pcAfter  : Nat
  deriving Repr, DecidableEq

/-- Snapshot registers after a step (no outcome classification). -/
def Machine.snap (m : Machine) (pcBefore : Nat) : TraceEvent where
  pcBefore := pcBefore
  r0 := m.getReg ⟨0, by omega⟩
  r1 := m.getReg ⟨1, by omega⟩
  pcAfter := m.pc

/-- Collect up to `fuel` successful-step snapshots, plus final observation. -/
def traceObserved (D : ExecDialect) (P : Program) (fuel : Nat) (m0 : Machine) :
    List TraceEvent × Observation :=
  let rec go (fuel : Nat) (m : Machine) (acc : List TraceEvent) :
      List TraceEvent × Observation :=
    match m.halted with
    | some c => (acc.reverse, observe m (.halted c))
    | none =>
      match fuel with
      | 0 => (acc.reverse, observe m .outOfFuel)
      | fuel + 1 =>
        let pc0 := m.pc
        match execStep D P m with
        | none => (acc.reverse, observe m .stuck)
        | some m' => go fuel m' (m'.snap pc0 :: acc)
  go fuel m0 []

end SbpfSemantics
