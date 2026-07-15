import SbpfSemantics.Basic
import SbpfSemantics.Machine

/-!
# SbpfSemantics.Dialect

Syscall / host effect abstraction (open world), analogous to yul-semantics'
`Dialect` for built-ins.
-/

namespace SbpfSemantics

/-- Relational host: given a syscall name and pre-state, a possible post-state
and return value placed in `r0` by the caller (`execSyscall`). -/
structure Dialect where
  Syscall : String → Machine → Machine → Word → Prop

/-- Executable host for the fuel interpreter. -/
structure ExecDialect extends Dialect where
  syscallFn : String → Machine → Option (Machine × Word)
  lawful : ∀ name m m' r, syscallFn name m = some (m', r) → Syscall name m m' r

/-- Closed world: no syscall ever succeeds. -/
def closedDialect : Dialect where
  Syscall := fun _ _ _ _ => False

def closedExec : ExecDialect where
  toDialect := closedDialect
  syscallFn := fun _ _ => none
  lawful := by intro _ _ _ _ h; cases h

/-- Trivial host: every name returns 0 and leaves the machine unchanged. -/
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

/-- Names treated as pure log syscalls by the default stub host. -/
def isLogSyscall (name : String) : Bool :=
  name == "sol_log_" || name == "sol_log_64_" || name == "sol_log_data" ||
    name == "sol_log_pubkey" || name == "sol_log_compute_units_"

/-- Logging stub host: log-like names leave state unchanged and return 0;
`abort` / unknown names stuck (`none`) — safer default than `noopExec`. -/
def stubDialect : Dialect where
  Syscall := fun name m m' r => isLogSyscall name = true ∧ m' = m ∧ r = word0

def stubExec : ExecDialect where
  toDialect := stubDialect
  syscallFn := fun name m =>
    if isLogSyscall name then some (m, word0) else none
  lawful := by
    intro name m m' r h
    by_cases hlog : isLogSyscall name = true
    · simp [hlog, Option.some.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨hlog, rfl, rfl⟩
    · simp [hlog] at h

end SbpfSemantics
