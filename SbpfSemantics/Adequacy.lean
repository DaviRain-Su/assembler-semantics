import SbpfSemantics.Interp
import SbpfSemantics.Observation
import SbpfSemantics.Determinism

/-!
# SbpfSemantics.Adequacy

Link between the fuel-indexed interpreter (`runFuel` / `execStep`) and the
relational judgments (`Step` / `Steps` / `Run`).
-/

namespace SbpfSemantics

/-- One-step soundness: interpreter success implies relational Step. -/
theorem execStep_sound (D : ExecDialect) (P : Program) (m m' : Machine)
    (h : execStep D P m = some m') : Step D P m m' := h

/-- One-step completeness: relational Step implies interpreter success. -/
theorem execStep_complete (D : ExecDialect) (P : Program) (m m' : Machine)
    (h : Step D P m m') : execStep D P m = some m' := h

/-- If `runFuel` reports halted with code `c`, the final machine carries that halt. -/
theorem runFuel_halted_code (D : ExecDialect) (P : Program) (fuel : Nat) (m m' : Machine)
    (c : Word) (h : runFuel D P fuel m = (m', .halted c)) : m'.halted = some c := by
  induction fuel generalizing m with
  | zero =>
      simp only [runFuel] at h
      cases hm : m.halted <;> simp_all
  | succ fuel ih =>
      simp only [runFuel] at h
      cases hm : m.halted with
      | some c0 =>
          simp_all
      | none =>
          cases hs : execStep D P m with
          | none => simp_all
          | some m1 =>
              simp only [hm, hs] at h
              exact ih m1 h

/-- Alias used by the ProofForge interface docs. -/
theorem runFuel_halted_inv (D : ExecDialect) (P : Program) (fuel : Nat) (m m' : Machine)
    (c : Word) (h : runFuel D P fuel m = (m', .halted c)) :
    m'.halted = some c :=
  runFuel_halted_code D P fuel m m' c h

/-- Zero steps: `Steps 0` is reflexivity. -/
theorem Steps_zero (D : ExecDialect) (P : Program) (m : Machine) :
    Steps D P 0 m m :=
  Steps.zero m

/-- One relational step is a length-1 chain. -/
theorem Steps_one (D : ExecDialect) (P : Program) (m m' : Machine)
    (h : Step D P m m') : Steps D P 1 m m' :=
  Steps.succ h (Steps.zero m')

/-- Deterministic step ⇒ identical observations after the step. -/
theorem step_observation_det (D : ExecDialect) (P : Program) (m m₁ m₂ : Machine)
    (h1 : Step D P m m₁) (h2 : Step D P m m₂) :
    observe m₁ (match m₁.halted with | some c => .halted c | none => .outOfFuel) =
    observe m₂ (match m₂.halted with | some c => .halted c | none => .outOfFuel) := by
  have := Step.det D P m m₁ m₂ h1 h2
  subst this
  rfl

/-- Equal-length `Steps` chains agree on halt codes. -/
theorem Run_code_unique_of_same_length (D : ExecDialect) (P : Program)
    (n : Nat) (m m₁ m₂ : Machine) (c₁ c₂ : Word)
    (h1 : Steps D P n m m₁) (h2 : Steps D P n m m₂)
    (hc1 : m₁.halted = some c₁) (hc2 : m₂.halted = some c₂) :
    c₁ = c₂ := by
  have eqm := Steps.det D P n m m₁ m₂ h1 h2
  subst eqm
  have : some c₁ = some c₂ := by
    rw [← hc1, hc2]
  exact Option.some.inj this

end SbpfSemantics
