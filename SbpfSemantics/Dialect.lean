import SbpfSemantics.Basic
import SbpfSemantics.Machine

/-!
# SbpfSemantics.Dialect

Syscall / host effect abstraction (open world), analogous to yul-semantics'
`Dialect` for built-ins.

Phase 1 provides:
- a relational interface (`Dialect`)
- a closed executable dialect that leaves all syscalls stuck (`closedExec`)
- a trivial executable dialect that no-ops known log-like names
-/


namespace SbpfSemantics

/-- Relational host: given a syscall name and pre-state, a possible post-state
and return value in `r0`. -/
structure Dialect where
  /-- Possible results of a named syscall. -/
  Syscall : String → Machine → Machine → Word → Prop

/-- Executable host for the fuel interpreter. -/
structure ExecDialect extends Dialect where
  syscallFn : String → Machine → Option (Machine × Word)
  /-- Agreement: executable results inhabit the relation. -/
  lawful : ∀ name m m' r, syscallFn name m = some (m', r) → Syscall name m m' r

/-- Closed world: no syscall ever succeeds. -/
def closedDialect : Dialect where
  Syscall := fun _ _ _ _ => False

def closedExec : ExecDialect where
  toDialect := closedDialect
  syscallFn := fun _ _ => none
  lawful := by intro _ _ _ _ h; cases h

/-- Trivial host: every name returns 0 and leaves the machine unchanged.
Useful for smoke tests that only care that `call sol_log_` does not get stuck. -/
def noopDialect : Dialect where
  Syscall := fun _ m m' r => m' = m ∧ r = word0

def noopExec : ExecDialect where
  toDialect := noopDialect
  syscallFn := fun _ m => some (m, word0)
  lawful := by
    intro _ m m' r h
    simp only [Option.some.injEq] at h
    rcases h with ⟨⟨⟩⟩
    exact ⟨rfl, rfl⟩

end SbpfSemantics
