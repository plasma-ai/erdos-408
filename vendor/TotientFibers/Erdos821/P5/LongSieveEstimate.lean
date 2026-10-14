import Erdos821.P5.LongSieve

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- §4 sieve replacement and harmonic summation. The polynomial is chosen
before the interval, modulus and frequency. Only the divisor-progression
cancellation bound remains as an explicit input. -/
theorem rough_sieve_cancellation (hsieve : Blueprint.RoughPolynomial) :
    ∃ K : ℝ, 0 < K ∧ ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → Even h →
      ∀ z : ℝ, 2 ≤ z → ∃ lam : ℕ → ℝ,
        (∀ d, |lam d| ≤ 1) ∧
        (∀ d, lam d ≠ 0 → Squarefree d ∧ (d : ℝ) ≤ z ^ (4 * h + 2) ∧
          d.primeFactors ⊆ Blueprint.primesUpTo z) ∧
        ∀ (P lo hi u B : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r),
          0 < P → 1 ≤ lo → P ≤ lo → lo ≤ hi → hi ≤ 2 * P → 0 ≤ B →
          (∀ d ∈ Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊,
            ‖∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (fun n => d ∣ n),
              characterMellinTerm χ u n‖ ≤ B / d) →
          ‖∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (rough z),
            characterMellinTerm χ u n‖ ≤
              K * (Real.exp (-(h : ℝ)) + z ^ (4 * h + 2) / P + B * Real.log (2 * z)) := by
  classical
  obtain ⟨K, hK, h₀, hsieve⟩ := hsieve
  refine ⟨K, hK, h₀, ?_⟩
  intro h hh he z hz
  obtain ⟨lam, hcoeff, hsupport, hupper, hharm, herror⟩ := hsieve h hh he z hz
  refine ⟨lam, hcoeff, hsupport, ?_⟩
  intro P lo hi u B r χ hP hlo hPlo hlohi hhi hB hcancel
  let s := Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊
  let D := z ^ (4 * h + 2)
  let f := characterMellinTerm χ u
  have hnlo (n : ℕ) (hn : n ∈ s) : lo ≤ (n : ℝ) :=
    Nat.le_of_ceil_le (Finset.mem_Icc.mp hn).1
  have hnpos (n : ℕ) (hn : n ∈ s) : 0 < n := by
    have : 0 < (n : ℝ) := hP.trans_le (hPlo.trans (hnlo n hn))
    exact_mod_cast this
  have hsup (n : ℕ) (hn : n ∈ s) :
      roughIndicator z n ≤ divisorPolynomial lam n := hupper n (hnpos n hn)
  have hf (n : ℕ) (hn : n ∈ s) : ‖f n‖ ≤ P⁻¹ :=
    characterMellinTerm_norm_le χ u P n hP (hPlo.trans (hnlo n hn))
  have herr := rough_replacement_error s z P lam f hP hsup hf
  have hmass : (∑ n ∈ s, (divisorPolynomial lam n - roughIndicator z n)) ≤
      K * (P * Real.exp (-(h : ℝ)) + D) := by
    apply (herror lo hi hlo hlohi).trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    exact add_le_add
      (mul_le_mul_of_nonneg_right (by linarith : hi - lo ≤ P) (Real.exp_pos _).le) le_rfl
  have herr' :
      ‖(∑ n ∈ s.filter (rough z), f n) -
        ∑ n ∈ s, (divisorPolynomial lam n : ℂ) * f n‖ ≤
      K * (Real.exp (-(h : ℝ)) + D / P) := by
    apply herr.trans
    calc
      _ ≤ K * (P * Real.exp (-(h : ℝ)) + D) / P :=
        div_le_div_of_nonneg_right hmass hP.le
      _ = _ := by field_simp
  have hlam : ∀ d, lam d ≠ 0 → 0 < d ∧ (d : ℝ) ≤ D := by
    intro d hd
    exact ⟨Nat.pos_of_ne_zero (hsupport d hd).1.ne_zero, (hsupport d hd).2.1⟩
  have hpoly : ‖∑ n ∈ s, (divisorPolynomial lam n : ℂ) * f n‖ ≤
      B * (K * Real.log (2 * z)) := by
    apply (divisor_polynomial_bound s D B lam f hnpos hlam hcancel).trans
    exact mul_le_mul_of_nonneg_left hharm hB
  calc
    _ ≤ ‖(∑ n ∈ s.filter (rough z), f n) -
        ∑ n ∈ s, (divisorPolynomial lam n : ℂ) * f n‖ +
        ‖∑ n ∈ s, (divisorPolynomial lam n : ℂ) * f n‖ := norm_le_norm_sub_add _ _
    _ ≤ K * (Real.exp (-(h : ℝ)) + D / P) + B * (K * Real.log (2 * z)) :=
      add_le_add herr' hpoly
    _ = _ := by dsimp [D]; ring

end Erdos821.P5Core
