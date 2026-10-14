import OAI.NumberTheory.DirichletL.Nonvanishing

/-!
# The seven-eighths zero-free half-plane

Every Dirichlet L-function is zero-free in `7 / 8 < re s`, apart from the
principal character's pole at `s = 1`. This is Theorem 1.1 of OpenAI's
*The Quasi-Riemann Hypothesis*, formalized in the vendored OAI library.
-/

namespace Erdos408

/-- Dirichlet L-functions do not vanish to the right of `7 / 8`, away from the
principal character's pole at `1`. -/
theorem LFunction_ne_zero_of_seven_eighths_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs hpole

end Erdos408
