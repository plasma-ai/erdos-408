import Erdos821.P5.ExceptionalTheorem

/-!
# The exceptional set

S16 of `blueprint/two_sided_correlation.md` §6.4 (PD (6.36); WD Lemma 5.2), from the vendored
`Erdos821.Blueprint.Analytic.exceptional_times` at `(a, b, A) = (0.27, 0.36, A + 1)`, with
`coeff' p = coeff p · p/(2P)`, so that `primePolynomial s coeff' = P⁻¹ ∑ coeff(p) p^{it}/2`.
-/

namespace Erdos408.TwoSided.TupleHigh

open Filter

/-- `exp(i t log y) = y^{it}` for `y > 0`. -/
theorem mellin_eq_cpow {y : ℝ} (hy : 0 < y) (t : ℝ) :
    Erdos821.Blueprint.Analytic.mellin y t = (y : ℂ) ^ ((t : ℂ) * Complex.I) := by
  rw [Erdos821.Blueprint.Analytic.mellin, Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'),
    ← Complex.ofReal_log hy.le]
  ring_nf

open scoped Classical in
/-- **S16 (exceptional unit intervals).** For every `A > 0` there is `K > 0` such that,
eventually, the integers `j` such that `[j, j + 1]` meets
`{|t| ≤ T_max : |P⁻¹ ∑_{p ∈ s} coeff(p) p^{it}| > L^{-A}}` number at most
`exp(K (L^{0.36} + L^{0.73} log L))`. -/
theorem exists_card_exceptional_le (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (Y P Tmax : ℝ) (s : Finset ℕ) (coeff : ℕ → ℂ),
        x ^ (1 / 2 : ℝ) ≤ Y → Y ≤ x ^ 2 → 0 ≤ Tmax → Tmax ≤ Y →
        Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ P → P ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) →
        (∀ p ∈ s, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) → (∀ p ∈ s, ‖coeff p‖ ≤ 1) →
        (((Finset.Icc (-⌈Tmax⌉ - 1) ⌈Tmax⌉).filter fun j : ℤ =>
            ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ j + 1 ∧ |t| ≤ Tmax ∧
              Real.log x ^ (-A) <
                ‖(P : ℂ)⁻¹ * ∑ p ∈ s, coeff p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖).card : ℝ) ≤
          Real.exp (K * (Real.log x ^ (0.36 : ℝ) +
            Real.log x ^ (0.73 : ℝ) * Real.log (Real.log x))) := by
  obtain ⟨K, hK, hev⟩ := Erdos821.Blueprint.Analytic.exceptional_times 0.27 0.36 (A + 1)
    (by norm_num) (by norm_num) (by norm_num) (by linarith)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hev, Real.tendsto_log_atTop.eventually_ge_atTop 2] with x hx hL
  intro Y P Tmax s coeff hY₁ hY₂ hT₀ hTY hP₁ hP₂ hs hcoeff
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP₁
  set coeff' : ℕ → ℂ := fun p => coeff p * (p : ℂ) / (2 * P) with hcoeff'
  have hc' : ∀ p ∈ s, ‖coeff' p‖ ≤ 1 := by
    intro p hp
    rw [hcoeff', norm_div, norm_mul, Complex.norm_natCast, div_le_one (by
      rw [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hP0.le]
      positivity)]
    rw [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hP0.le]
    calc ‖coeff p‖ * p ≤ 1 * (2 * P) :=
          mul_le_mul (hcoeff p hp) (hs p hp).2.2 (Nat.cast_nonneg _) zero_le_one
      _ = 2 * P := one_mul _
  obtain ⟨hfin, hcard⟩ := hx Y P Tmax s coeff' hY₁ hY₂ hT₀ hTY hP₁ hP₂ hs hc'
  rw [show (1 : ℝ) - 0.27 = 0.73 by norm_num] at hcard
  refine le_trans ?_ hcard
  rw [← Set.ncard_coe_finset]
  refine Nat.cast_le.2 (Set.ncard_le_ncard (fun j hj => ?_) hfin)
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hj
  obtain ⟨-, t, ht₁, ht₂, ht₃, ht₄⟩ := hj
  refine ⟨t, ht₁, ht₂, ht₃, ?_⟩
  -- `primePolynomial s coeff' t = (P⁻¹ ∑ coeff(p) p^{it}) / 2`
  have hpoly : Erdos821.Blueprint.Analytic.primePolynomial s coeff' t =
      ((P : ℂ)⁻¹ * ∑ p ∈ s, coeff p * (p : ℂ) ^ ((t : ℂ) * Complex.I)) / 2 := by
    rw [Erdos821.Blueprint.Analytic.primePolynomial, Erdos821.Blueprint.Analytic.dp,
      Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hP0 (hs p hp).2.1
    rw [mellin_eq_cpow hp0, Complex.ofReal_natCast, hcoeff']
    have : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
    have : (P : ℂ) ≠ 0 := by exact_mod_cast hP0.ne'
    field_simp
  rw [hpoly, norm_div, Complex.norm_ofNat]
  have hL0 : 0 < Real.log x := by linarith
  have hsplit : Real.log x ^ (-(A + 1)) = Real.log x ^ (-A) / Real.log x := by
    rw [neg_add, Real.rpow_add hL0, Real.rpow_neg_one, div_eq_mul_inv]
  change Real.log x ^ (-(A + 1)) < _
  rw [hsplit, div_lt_div_iff₀ hL0 (by norm_num)]
  have : 0 < Real.log x ^ (-A) := by positivity
  nlinarith

end Erdos408.TwoSided.TupleHigh
