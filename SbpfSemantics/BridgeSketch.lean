import SbpfSemantics.Api
import SbpfSemantics.Instr

/-!
# SbpfSemantics.BridgeSketch

Minimal sketch of how ProofForge Solana lowering would *use* this package.

Not a full Counter materializer: no account scan, no IDL, no CPI. It shows:

1. Hand-lowered L2 `Program` (what a materializer must emit).
2. `pfRun` / `Observation` as the differential surface.
3. Encode→redecode still yields the same halt observation.
-/

namespace SbpfSemantics.BridgeSketch

open SbpfSemantics

private def r0 : Reg := ⟨0, by omega⟩
private def r1 : Reg := ⟨1, by omega⟩
private def r2 : Reg := ⟨2, by omega⟩

/-- Stand-in for “increment delta into r0 then exit” (pure ALU fragment).

ProofForge would lower `entry increment(delta)` body arithmetic similarly,
then wrap with account loads/stores + discriminator dispatch in real emit. -/
def incrementFragment (delta : Word) : Program :=
  #[
    .binImm .Mov64Imm r0 0#64,       -- count := 0  (would be loaded from account)
    .binImm .Add64Imm r0 delta,      -- count := count + delta
    .exit                            -- return count in r0
  ]

/-- Reference observation for increment-by-1 from zero. -/
def incrementObs : Observation :=
  pfRun pfClosedHost (incrementFragment 1#64) 32

example : incrementObs.outcome = .halted 1#64 := by native_decide
example : incrementObs.r0 = 1#64 := by native_decide

/-- Encode preservation for the fragment (same as EncodeSem style). -/
example :
    (pfDecode? (pfEncode (incrementFragment 3#64))).map
        (fun P => (pfRun pfClosedHost P 32).r0)
      = some 3#64 := by
  native_decide

/-- View-style fragment: return constant in r0 (get). -/
def getFragment (count : Word) : Program :=
  #[.binImm .Mov64Imm r0 count, .exit]

example : (pfRun pfClosedHost (getFragment 7#64) 16).r0 = 7#64 := by native_decide

/-- Host sketch: write a byte via memset then “return” it in r0. -/
def memsetReturnByte : Program :=
  #[
    .binReg .Mov64Reg r1 ⟨10, by omega⟩,
    .binImm .Add64Imm r1 (BitVec.ofInt 64 (-8)),
    .binImm .Mov64Imm r2 0x11#64,
    .binImm .Mov64Imm ⟨3, by omega⟩ 1#64,
    .callSyscall "sol_memset_",
    .loadMem .Ldxb r0 ⟨10, by omega⟩ (BitVec.ofInt 16 (-8)),
    .exit
  ]

example : (pfRun pfDefaultHost memsetReturnByte 64).outcome = .halted 0x11#64 := by
  native_decide

/-- Control-equality helper used by PF tests (only outcome + r0). -/
example :
    let a := pfRun pfClosedHost (incrementFragment 2#64) 32
    let b := pfRun pfClosedHost (incrementFragment 2#64) 32
    Observation.controlEqb a b = true := by
  native_decide

end SbpfSemantics.BridgeSketch
