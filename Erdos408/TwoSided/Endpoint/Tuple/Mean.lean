module

public import Erdos408.OneSided.Analysis.Divisor

/-!
# The restricted mean value

E7 of `blueprint/two_sided_correlation.md` §6.3 (PD (6.35)). On the set where `|P_s| ≤ θ`,
bound `|P_s Q|² ≤ θ² |Q|²`, enlarge the set to `(a, b]` and apply the mean value theorem
`OneSided.integral_norm_dirichlet_sq_le` to `Q`.
-/

@[expose] public section

namespace Erdos408.TwoSided.TupleHigh

open MeasureTheory

/-- `t ↦ ∑_{p ∈ s} c_p p^{it}` is measurable (`0^{it}` included). -/
theorem measurable_dirichletSum (s : Finset ℕ) (c : ℕ → ℂ) :
    Measurable fun t : ℝ => ∑ p ∈ s, c p * (p : ℂ) ^ ((t : ℂ) * Complex.I) :=
  Finset.measurable_sum _ fun _ _ =>
    measurable_const.mul (measurable_const.pow (Complex.measurable_ofReal.mul_const _))

/-- `t ↦ ∑_{n ∈ [1, N]} c_n n^{it}` is continuous. -/
theorem continuous_dirichletSum_Icc (N : ℕ) (c : ℕ → ℂ) :
    Continuous fun t : ℝ => ∑ n ∈ Finset.Icc 1 N, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
  refine continuous_finsetSum _ fun n hn => continuous_const.mul ?_
  have hn0 : n ≠ 0 := by rw [Finset.mem_Icc] at hn; omega
  simp_rw [OneSided.natCast_cpow_mul_I hn0]
  fun_prop

/-- **E7 (ordinary times).** On `{t ∈ (a, b] : |P_s(t)| ≤ θ}`,
`∫ |P_s Q|² ≤ θ² (b - a + 8N(1 + log N)) ∑ |q_n|²` for `Q(t) = ∑_{n ≤ N} q_n n^{it}`. -/
theorem setIntegral_ordinary_le (s : Finset ℕ) (cs : ℕ → ℂ) (N : ℕ) (cq : ℕ → ℂ)
    {a b θ : ℝ} (hab : a ≤ b) :
    ∫ t in {t ∈ Set.Ioc a b | ‖∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ θ},
        ‖(∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)) *
          ∑ n ∈ Finset.Icc 1 N, cq n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      θ ^ 2 * ((b - a + 8 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖cq n‖ ^ 2) := by
  set Ps := fun t : ℝ => ∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)
  set Q := fun t : ℝ => ∑ n ∈ Finset.Icc 1 N, cq n * (n : ℂ) ^ ((t : ℂ) * Complex.I)
  set O := {t ∈ Set.Ioc a b | ‖Ps t‖ ≤ θ}
  have hO : MeasurableSet O :=
    measurableSet_Ioc.inter (measurableSet_le (measurable_dirichletSum s cs).norm
      measurable_const)
  have hQ : Continuous fun t => θ ^ 2 * ‖Q t‖ ^ 2 :=
    continuous_const.mul ((continuous_dirichletSum_Icc N cq).norm.pow 2)
  have hint : IntegrableOn (fun t => θ ^ 2 * ‖Q t‖ ^ 2) (Set.Ioc a b) :=
    hQ.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  -- on `O`, `|P_s Q|² ≤ θ² |Q|²`
  have h₁ : ∫ t in O, ‖Ps t * Q t‖ ^ 2 ≤ ∫ t in O, θ ^ 2 * ‖Q t‖ ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => by positivity)
      (hint.mono_set fun t ht => ht.1) ((ae_restrict_iff' hO).2
        (Filter.Eventually.of_forall fun t ht => ?_))
    show ‖Ps t * Q t‖ ^ 2 ≤ θ ^ 2 * ‖Q t‖ ^ 2
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ht.2 2) (by positivity)
  -- enlarge `O` to `(a, b]` and apply the mean value theorem
  have h₂ : ∫ t in O, θ ^ 2 * ‖Q t‖ ^ 2 ≤ ∫ t in Set.Ioc a b, θ ^ 2 * ‖Q t‖ ^ 2 :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun t => by positivity)
      (Filter.Eventually.of_forall fun t ht => ht.1)
  have h₃ : ∫ t in Set.Ioc a b, θ ^ 2 * ‖Q t‖ ^ 2 = θ ^ 2 * ∫ t in a..b, ‖Q t‖ ^ 2 := by
    rw [integral_const_mul, intervalIntegral.integral_of_le hab]
  exact h₁.trans (h₂.trans (h₃.trans_le (mul_le_mul_of_nonneg_left
    (OneSided.integral_norm_dirichlet_sq_le N cq a b) (sq_nonneg θ))))

end Erdos408.TwoSided.TupleHigh
