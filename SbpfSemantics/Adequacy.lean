import SbpfSemantics.Interp

/-!
# SbpfSemantics.Adequacy

Adequacy skeleton: `runFuel` agrees with the relational `Steps` story for the
executable dialect.

Full Yul-style adequacy (soundness at any fuel + completeness at large fuel for
all terminating relational runs) is left as follow-up work; here we record the
statement shape and prove the easy one-step directions plus a halt-code lemma.
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

end SbpfSemantics
