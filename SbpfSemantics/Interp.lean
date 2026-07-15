import SbpfSemantics.Run

/-!
# SbpfSemantics.Interp

Executable fuel-indexed interpreter — computational content of `runFuel`.
-/


namespace SbpfSemantics

/-- Run until halt / stuck / out-of-fuel. -/
def interp (D : ExecDialect) (P : Program) (fuel : Nat) (m : Machine) : Machine × Outcome :=
  runFuel D P fuel m

/-- Convenience: run from entry with empty input. -/
def interpEntry (D : ExecDialect) (P : Program) (fuel : Nat)
    (input : Array UInt8 := #[])
    (rodata : Array UInt8 := #[]) : Machine × Outcome :=
  interp D P fuel (Machine.entry input rodata)

end SbpfSemantics
