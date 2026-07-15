import SbpfSemantics.Step

/-!
# SbpfSemantics.Run

Multi-step execution: fuel-indexed relation and outcome classification.
-/


namespace SbpfSemantics

/-- Whole-program outcome. -/
inductive Outcome where
  | halted (code : Word)
  | stuck
  | outOfFuel
  deriving DecidableEq, Repr

/-- Fuel-indexed multi-step to a final observation. -/
def runFuel (D : ExecDialect) (P : Program) : Nat → Machine → Machine × Outcome
  | 0, m =>
      match m.halted with
      | some c => (m, .halted c)
      | none => (m, .outOfFuel)
  | fuel + 1, m =>
      match m.halted with
      | some c => (m, .halted c)
      | none =>
        match execStep D P m with
        | none => (m, .stuck)
        | some m' => runFuel D P fuel m'

/-- Relational multi-step of exactly `n` successful steps. -/
inductive Steps (D : ExecDialect) (P : Program) : Nat → Machine → Machine → Prop where
  | zero (m : Machine) : Steps D P 0 m m
  | succ {n m m' m''} :
      Step D P m m' → Steps D P n m' m'' → Steps D P (n + 1) m m''

/-- `Run`: reaches a halted state in some number of steps. -/
def Run (D : ExecDialect) (P : Program) (m m' : Machine) (code : Word) : Prop :=
  ∃ n, Steps D P n m m' ∧ m'.halted = some code

end SbpfSemantics
