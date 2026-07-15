import SbpfSemantics.Api
import SbpfSemantics.AccountLayout
import SbpfSemantics.Instr
import SbpfSemantics.Observation
import SbpfSemantics.Run

/-!
# SbpfSemantics.CounterScenario

End-to-end **portable Counter** fragments for ProofForge differentials.

Layout:
- logical `count : UInt64` lives at `counterCell` in the input region
  (stand-in for account data).
- Programs load/add/store that cell, optionally publish return data, then `exit`.

This is intentionally simpler than full EmitSBPF Counter (no discriminator,
owner checks, or CPI). It is the contract shape PF materializers should hit
first when wiring `Semantic.Program` → L2.
-/

namespace SbpfSemantics.CounterScenario

open SbpfSemantics

private def r0 : Reg := ⟨0, by omega⟩
private def r1 : Reg := ⟨1, by omega⟩
private def r2 : Reg := ⟨2, by omega⟩

/-- `r2 := address of counter cell` (absolute VA). -/
def loadCellPtr : Instr :=
  .lddw r2 counterCell.addr

/-- Load count into `r0`. -/
def loadCount : Array Instr :=
  #[loadCellPtr, .loadMem .Ldxdw r0 r2 0#16]

/-- Store `r0` back to the cell (reloads pointer). -/
def storeCount : Array Instr :=
  #[loadCellPtr, .storeReg .Stxdw r2 r0 0#16]

/-- Publish 8-byte LE `r0` via `sol_set_return_data` using `[r10-8]`.

Syscall return value overwrites `r0` with 0 (Solana ABI); we reload the
published word from the stack so `exit` still returns the count in `r0`. -/
def setReturnR0 : Array Instr :=
  #[
    .storeReg .Stxdw ⟨10, by omega⟩ r0 (BitVec.ofInt 16 (-8)),
    .binReg .Mov64Reg r1 ⟨10, by omega⟩,
    .binImm .Add64Imm r1 (BitVec.ofInt 64 (-8)),
    .binImm .Mov64Imm r2 8#64,
    .callSyscall "sol_set_return_data",
    .loadMem .Ldxdw r0 ⟨10, by omega⟩ (BitVec.ofInt 16 (-8))
  ]

/-- `get`: load count → return data → exit with r0 = count. -/
def progGet : Program :=
  loadCount ++ setReturnR0 ++ #[.exit]

/-- `increment(delta)`: count := count + delta; store; return; exit. -/
def progIncrement (delta : Word) : Program :=
  loadCount ++
    #[.binImm .Add64Imm r0 delta] ++
    storeCount ++
    setReturnR0 ++
    #[.exit]

/-- `initialize(v)`: count := v; store; exit. -/
def progInit (v : Word) : Program :=
  #[.binImm .Mov64Imm r0 v] ++ storeCount ++ #[.exit]

/-- Run get on initial count `c`. -/
def runGet (c : Word) (fuel : Nat := 128) : Observation :=
  runObserved pfDefaultHost progGet fuel (Machine.entryWithCell counterCell c)

/-- Run increment-by-`d` starting from count `c`. -/
def runInc (c d : Word) (fuel : Nat := 256) : Observation :=
  runObserved pfDefaultHost (progIncrement d) fuel (Machine.entryWithCell counterCell c)

/-- Sequential init → get on the same memory (new invocation via `readyForNext`). -/
def runInitThenGet (v : Word) (fuel : Nat := 256) : Observation × Observation :=
  let m0 := Machine.entryWithCell counterCell 0#64
  let (m1, o1) := runFuel pfDefaultHost (progInit v) fuel m0
  let obs1 := observe m1 o1
  let obs2 := runObserved pfDefaultHost progGet fuel m1.readyForNext
  (obs1, obs2)

/-- Sequential init → inc → get (each entrypoint is a fresh invocation). -/
def runInitIncGet (v d : Word) (fuel : Nat := 512) : Observation × Observation × Observation :=
  let m0 := Machine.entryWithCell counterCell 0#64
  let (m1, o1) := runFuel pfDefaultHost (progInit v) fuel m0
  let (m2, o2) := runFuel pfDefaultHost (progIncrement d) fuel m1.readyForNext
  let obs3 := runObserved pfDefaultHost progGet fuel m2.readyForNext
  (observe m1 o1, observe m2 o2, obs3)

-- Goldens ---------------------------------------------------------------

example : (runGet 0#64).r0 = 0#64 := by native_decide
example : (runGet 0#64).outcome = .halted 0#64 := by native_decide
example : (runGet 7#64).r0 = 7#64 := by native_decide

example : (runInc 0#64 1#64).r0 = 1#64 := by native_decide
example : (runInc 5#64 3#64).r0 = 8#64 := by native_decide

example :
    let (oi, og) := runInitThenGet 9#64
    oi.r0 = 9#64 ∧ og.r0 = 9#64 := by
  native_decide

example :
    let (oi, oinc, og) := runInitIncGet 0#64 1#64
    oi.r0 = 0#64 ∧ oinc.r0 = 1#64 ∧ og.r0 = 1#64 := by
  native_decide

/-- Return data carries LE encoding of the count after get. -/
example :
    (runGet 0x0102030405060708#64).returnData = wordToLE 0x0102030405060708#64 := by
  native_decide

/-- Encode/redecode preserves get observation for count=3. -/
example :
    (pfDecode? (pfEncode progGet)).map
        (fun P' =>
          (runObserved pfDefaultHost P' 128 (Machine.entryWithCell counterCell 3#64)).r0)
      = some 3#64 := by
  native_decide

end SbpfSemantics.CounterScenario
