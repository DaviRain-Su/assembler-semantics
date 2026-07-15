import SbpfSemantics.Run

/-!
# SbpfSemantics.Determinism

Closed-world single-step determinism is immediate from `execStep` being a
function. Multi-step uniqueness follows by induction on `Steps`.
-/


namespace SbpfSemantics

theorem Steps.det (D : ExecDialect) (P : Program) :
    ∀ n m m₁ m₂, Steps D P n m m₁ → Steps D P n m m₂ → m₁ = m₂ := by
  intro n m m₁ m₂ h1
  induction h1 generalizing m₂ with
  | zero =>
      intro h2; cases h2; rfl
  | succ hstep _ ih =>
      intro h2
      cases h2 with
      | succ hstep' hrest =>
          have := Step.det D P _ _ _ hstep hstep'
          subst this
          exact ih _ hrest

/-- Placeholder: full multi-length `Run` confluence is deferred. -/
theorem Run.det_placeholder (_D : ExecDialect) (_P : Program) (_m _m₁ _m₂ : Machine)
    (_c₁ _c₂ : Word) : True := trivial

/-- Functional multi-step of fixed length is unique. -/
example (D : ExecDialect) (P : Program) (n : Nat) (m m₁ m₂ : Machine)
    (h1 : Steps D P n m m₁) (h2 : Steps D P n m m₂) : m₁ = m₂ :=
  Steps.det D P n m m₁ m₂ h1 h2

end SbpfSemantics
