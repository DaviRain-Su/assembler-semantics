import SbpfSemantics.Interp
import SbpfSemantics.Observation
import SbpfSemantics.Determinism

/-!
# SbpfSemantics.Adequacy

Link between the fuel-indexed interpreter (`runFuel` / `execStep`) and the
relational judgments (`Step` / `Steps` / `Run`).
-/

namespace SbpfSemantics

/-! ### One step -/

theorem execStep_sound (D : ExecDialect) (P : Program) (m m' : Machine)
    (h : execStep D P m = some m') : Step D P m m' := h

theorem execStep_complete (D : ExecDialect) (P : Program) (m m' : Machine)
    (h : Step D P m m') : execStep D P m = some m' := h

theorem Step_not_halted {D : ExecDialect} {P : Program} {m m' : Machine}
    (h : Step D P m m') : m.halted = none := by
  simp only [Step, execStep, fetch] at h
  cases hm : m.halted with
  | some _ => simp [hm] at h
  | none => rfl

/-! ### Halt code integrity -/

theorem runFuel_halted_code (D : ExecDialect) (P : Program) (fuel : Nat) (m m' : Machine)
    (c : Word) (h : runFuel D P fuel m = (m', .halted c)) : m'.halted = some c := by
  induction fuel generalizing m with
  | zero =>
      simp only [runFuel] at h
      cases hm : m.halted <;> simp_all
  | succ fuel ih =>
      simp only [runFuel] at h
      cases hm : m.halted with
      | some c0 => simp_all
      | none =>
          cases hs : execStep D P m with
          | none => simp_all
          | some m1 =>
              simp only [hm, hs] at h
              exact ih m1 h

theorem runFuel_halted_inv (D : ExecDialect) (P : Program) (fuel : Nat) (m m' : Machine)
    (c : Word) (h : runFuel D P fuel m = (m', .halted c)) :
    m'.halted = some c :=
  runFuel_halted_code D P fuel m m' c h

theorem runFuel_already_halted (D : ExecDialect) (P : Program) (fuel : Nat)
    (m : Machine) (c : Word) (hm : m.halted = some c) :
    runFuel D P fuel m = (m, .halted c) := by
  cases fuel with
  | zero => simp [runFuel, hm]
  | succ _ => simp [runFuel, hm]

/-! ### Steps basics -/

theorem Steps_zero (D : ExecDialect) (P : Program) (m : Machine) :
    Steps D P 0 m m :=
  Steps.zero m

theorem Steps_one (D : ExecDialect) (P : Program) (m m' : Machine)
    (h : Step D P m m') : Steps D P 1 m m' :=
  Steps.succ h (Steps.zero m')

theorem Steps_trans (D : ExecDialect) (P : Program) :
    ∀ n k m mid mfin,
      Steps D P n m mid → Steps D P k mid mfin → Steps D P (n + k) m mfin := by
  intro n k m mid mfin h1
  induction h1 generalizing k mfin with
  | zero =>
      intro h2; simpa using h2
  | succ hstep _ ih =>
      intro h2
      have h := ih k mfin h2
      -- Steps (n+k) mid' mfin; need Steps (n+1+k)
      simpa [Nat.succ_add] using Steps.succ hstep h

/-! ### Soundness -/

theorem runFuel_halted_steps (D : ExecDialect) (P : Program) :
    ∀ fuel m mfin c,
      runFuel D P fuel m = (mfin, .halted c) →
      ∃ n, n ≤ fuel ∧ Steps D P n m mfin ∧ mfin.halted = some c := by
  intro fuel
  induction fuel with
  | zero =>
      intro m mfin c h
      simp only [runFuel] at h
      cases hm : m.halted with
      | none => simp [hm] at h
      | some c0 =>
          simp [hm] at h
          obtain ⟨rfl, hEq⟩ := h
          cases hEq
          exact ⟨0, Nat.le_refl 0, Steps.zero m, hm⟩
  | succ fuel ih =>
      intro m mfin c h
      simp only [runFuel] at h
      cases hm : m.halted with
      | some c0 =>
          simp [hm] at h
          obtain ⟨rfl, hEq⟩ := h
          cases hEq
          exact ⟨0, Nat.zero_le _, Steps.zero m, hm⟩
      | none =>
          cases hs : execStep D P m with
          | none => simp [hm, hs] at h
          | some m1 =>
              simp only [hm, hs] at h
              obtain ⟨n, hle, hsteps, hh⟩ := ih m1 mfin c h
              exact ⟨n + 1, Nat.succ_le_succ hle, Steps.succ hs hsteps, hh⟩

/-! ### Completeness -/

theorem steps_runFuel_halted (D : ExecDialect) (P : Program) :
    ∀ n fuel m mfin c,
      Steps D P n m mfin →
      mfin.halted = some c →
      n ≤ fuel →
      runFuel D P fuel m = (mfin, .halted c) := by
  intro n fuel m mfin c hs
  induction hs generalizing fuel with
  | zero m0 =>
      intro hh _hle
      exact runFuel_already_halted D P fuel m0 c hh
  | succ hstep hrest ih =>
      intro hh hle
      cases fuel with
      | zero =>
          exact (Nat.not_succ_le_zero _ hle).elim
      | succ fuel =>
          have hle' := Nat.le_of_succ_le_succ hle
          have hnh := Step_not_halted hstep
          -- runFuel (fuel+1) m = match halted / execStep
          rw [runFuel, hnh, show execStep D P _ = some _ from hstep]
          exact ih fuel hh hle'

/-! ### Run packaging -/

theorem Run_of_runFuel (D : ExecDialect) (P : Program) (fuel : Nat) (m mfin : Machine)
    (c : Word) (h : runFuel D P fuel m = (mfin, .halted c)) : Run D P m mfin c := by
  obtain ⟨n, _, hs, hh⟩ := runFuel_halted_steps D P fuel m mfin c h
  exact ⟨n, hs, hh⟩

theorem runFuel_of_Run (D : ExecDialect) (P : Program) (m mfin : Machine) (c : Word)
    (h : Run D P m mfin c) :
    ∃ fuel, runFuel D P fuel m = (mfin, .halted c) := by
  obtain ⟨n, hs, hh⟩ := h
  exact ⟨n, steps_runFuel_halted D P n n m mfin c hs hh (Nat.le_refl n)⟩

/-! ### Observation corollaries -/

theorem step_observation_det (D : ExecDialect) (P : Program) (m m₁ m₂ : Machine)
    (h1 : Step D P m m₁) (h2 : Step D P m m₂) :
    observe m₁ (match m₁.halted with | some c => .halted c | none => .outOfFuel) =
    observe m₂ (match m₂.halted with | some c => .halted c | none => .outOfFuel) := by
  have := Step.det D P m m₁ m₂ h1 h2
  subst this
  rfl

theorem Run_code_unique_of_same_length (D : ExecDialect) (P : Program)
    (n : Nat) (m m₁ m₂ : Machine) (c₁ c₂ : Word)
    (h1 : Steps D P n m m₁) (h2 : Steps D P n m m₂)
    (hc1 : m₁.halted = some c₁) (hc2 : m₂.halted = some c₂) :
    c₁ = c₂ := by
  have eqm := Steps.det D P n m m₁ m₂ h1 h2
  subst eqm
  exact Option.some.inj (hc1.symm.trans hc2)

theorem runObserved_outcome_of_Run (D : ExecDialect) (P : Program) (m mfin : Machine)
    (c : Word) (h : Run D P m mfin c) :
    ∃ fuel, (runObserved D P fuel m).outcome = .halted c := by
  obtain ⟨fuel, hr⟩ := runFuel_of_Run D P m mfin c h
  refine ⟨fuel, ?_⟩
  simp [runObserved, hr, observe]

end SbpfSemantics
