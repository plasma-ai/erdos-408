import Erdos821.P5.LocalEnergyTask
import Erdos821.P5MarkedEnergy.Factorization

/-! Parseval's identity on an interval of length at most one, as an upper bound
for the additive energy of a finite exponential sum. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos821.P5Marked
open Blueprint.Analytic

theorem continuous_e : Continuous e := by unfold e; fun_prop

theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

theorem conj_e (t : ℝ) : (starRingEnd ℂ) (e t) = e (-t) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem integral_e_int (k : ℤ) (a : ℝ) :
    ∫ θ in a..(a + 1), e (k * θ) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [e]
  · have hc : (2 * Real.pi * k * Complex.I : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      simp [Real.pi_ne_zero, this, Complex.I_ne_zero]
    have h := integral_exp_mul_complex (a := a) (b := a + 1) hc
    have hfun : (fun θ : ℝ => e (k * θ)) = fun θ : ℝ => Complex.exp (2 * Real.pi * k * Complex.I * θ) := by
      funext θ; unfold e; congr 1; push_cast; ring
    rw [hfun, h]
    have hper : Complex.exp (2 * Real.pi * k * Complex.I * ((a + 1 : ℝ) : ℂ)) =
        Complex.exp (2 * Real.pi * k * Complex.I * (a : ℂ)) := by
      have : (2 * Real.pi * k * Complex.I * ((a + 1 : ℝ) : ℂ)) =
          2 * Real.pi * k * Complex.I * (a : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hper, sub_self, zero_div]

/-- Parseval on a unit interval. -/
theorem parseval_unit (s : Finset ℕ) (c : ℕ → ℂ) (a : ℝ) :
    ∫ θ in a..(a + 1), ‖∑ n ∈ s, c n * e (θ * n)‖ ^ 2 = ∑ n ∈ s, ‖c n‖ ^ 2 := by
  set z : ℝ → ℂ := fun θ => ∑ n ∈ s, c n * e (θ * n) with hz
  have hpt : ∀ θ : ℝ, (((‖z θ‖ ^ 2 : ℝ)) : ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, c n * (starRingEnd ℂ) (c m) * e (((n : ℤ) - m : ℤ) * θ) := by
    intro θ
    have h1 : (((‖z θ‖ ^ 2 : ℝ)) : ℂ) = z θ * (starRingEnd ℂ) (z θ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h1]
    simp only [hz, map_sum, map_mul, conj_e]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro n _
    apply Finset.sum_congr rfl; intro m _
    have he : e (θ * n) * e (-(θ * m)) = e (((n : ℤ) - m : ℤ) * θ) := by
      rw [← e_add']; congr 1; push_cast; ring
    rw [← he]; ring
  have hcont : ∀ n m : ℕ, Continuous (fun θ : ℝ => c n * (starRingEnd ℂ) (c m) *
      e (((n : ℤ) - m : ℤ) * θ)) := by
    intro n m
    exact continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_id))
  apply Complex.ofReal_injective
  have hint : ∫ θ in a..(a + 1), (((‖z θ‖ ^ 2 : ℝ)) : ℂ) = ∫ θ in a..(a + 1),
      ∑ n ∈ s, ∑ m ∈ s, c n * (starRingEnd ℂ) (c m) * e (((n : ℤ) - m : ℤ) * θ) :=
    intervalIntegral.integral_congr (fun θ _ => hpt θ)
  rw [← intervalIntegral.integral_ofReal, hint]
  rw [intervalIntegral.integral_finsetSum (fun n _ =>
    (continuous_finsetSum _ fun m _ => hcont n m).intervalIntegrable _ _)]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_finsetSum (fun m _ => (hcont n m).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_e_int]
  rw [Finset.sum_eq_single n]
  · simp only [sub_self, if_true, mul_one]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · intro m _ hmn
    have : ((n : ℤ) - m : ℤ) ≠ 0 := by
      intro h; apply hmn; omega
    rw [if_neg this, mul_zero]
  · intro h; exact absurd hn h

/-- Parseval as an upper bound on any interval of length at most one. -/
theorem parseval_le (s : Finset ℕ) (c : ℕ → ℂ) (a b : ℝ) (hab : a ≤ b) (hba : b ≤ a + 1) :
    ∫ θ in a..b, ‖∑ n ∈ s, c n * e (θ * n)‖ ^ 2 ≤ ∑ n ∈ s, ‖c n‖ ^ 2 := by
  rw [← parseval_unit s c a]
  have hcont : Continuous (fun θ : ℝ => ‖∑ n ∈ s, c n * e (θ * n)‖ ^ 2) := by
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro n _
    exact continuous_const.mul (continuous_e.comp (continuous_id.mul continuous_const))
  apply intervalIntegral.integral_mono_interval le_rfl hab hba
  · exact Filter.Eventually.of_forall fun θ => by positivity
  · exact hcont.intervalIntegrable _ _

end Erdos821.P5Marked
