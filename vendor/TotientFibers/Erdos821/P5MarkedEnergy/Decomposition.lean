import Erdos821.P5MarkedEnergy.Parseval
import Erdos821.P5MarkedEnergy.MellinBox

/-! Splitting the arc energy into finitely many pieces and a square-summable
error. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos821.P5Marked
open Blueprint.Analytic P5Core

theorem continuous_localAdditivePolynomial' (s : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (localAdditivePolynomial s a) := by
  unfold localAdditivePolynomial
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul (continuous_e.comp (continuous_id.mul continuous_const))

theorem energy_decomposition {ι : Type*} [Fintype ι] (S : Finset ℕ) (coeff : ℕ → ℂ)
    (θ0 H : ℝ) (hH : 2 ≤ H) (s : ι → Finset ℕ) (bb : ι → ℕ → ℂ) (ε : ℕ → ℂ)
    (hdec : ∀ n ∈ S, coeff n * e (θ0 * n) = ∑ i, bb i n + ε n)
    (hsupp : ∀ i, ∀ n ∈ S, n ∉ s i → bb i n = 0) (hsub : ∀ i, s i ⊆ S) :
    ∫ β in (-1 / H)..(1 / H), ‖localAdditivePolynomial S coeff (θ0 + β)‖ ^ 2 ≤
      2 * (Fintype.card ι : ℝ) * (∑ i, ∫ β in (-1 / H)..(1 / H),
          ‖localAdditivePolynomial (s i) (bb i) β‖ ^ 2) +
        2 * ∑ n ∈ S, ‖ε n‖ ^ 2 := by
  have hHpos : 0 < H := by linarith
  set Z : ℝ → ℂ := fun β => ∑ n ∈ S, ε n * e (β * n) with hZ
  have hpt : ∀ β, localAdditivePolynomial S coeff (θ0 + β) =
      ∑ i, localAdditivePolynomial (s i) (bb i) β + Z β := by
    intro β
    unfold localAdditivePolynomial
    have h1 : ∀ n ∈ S, coeff n * e ((θ0 + β) * n) = (∑ i, bb i n + ε n) * e (β * n) := by
      intro n hn
      rw [← hdec n hn, add_mul, e_add', mul_assoc]
    rw [Finset.sum_congr rfl h1]
    simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    symm
    apply Finset.sum_subset (hsub i)
    intro n hn hns
    rw [hsupp i n hn hns, zero_mul]
  have hcX : ∀ i, Continuous (localAdditivePolynomial (s i) (bb i)) :=
    fun i => continuous_localAdditivePolynomial' _ _
  have hcZ : Continuous Z := continuous_localAdditivePolynomial' S ε
  have hle : ∀ β, ‖localAdditivePolynomial S coeff (θ0 + β)‖ ^ 2 ≤
      2 * (Fintype.card ι : ℝ) * ∑ i, ‖localAdditivePolynomial (s i) (bb i) β‖ ^ 2 +
        2 * ‖Z β‖ ^ 2 := by
    intro β
    rw [hpt β]
    have h1 := norm_add_le (∑ i, localAdditivePolynomial (s i) (bb i) β) (Z β)
    have h2 := norm_sum_sq_le_card (Finset.univ : Finset ι)
      (fun i => localAdditivePolynomial (s i) (bb i) β)
    rw [Finset.card_univ] at h2
    have h3 : ‖∑ i, localAdditivePolynomial (s i) (bb i) β + Z β‖ ^ 2 ≤
        2 * ‖∑ i, localAdditivePolynomial (s i) (bb i) β‖ ^ 2 + 2 * ‖Z β‖ ^ 2 := by
      calc _ ≤ (‖∑ i, localAdditivePolynomial (s i) (bb i) β‖ + ‖Z β‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ _ := by nlinarith [sq_nonneg (‖∑ i, localAdditivePolynomial (s i) (bb i) β‖ - ‖Z β‖)]
    nlinarith
  have hab : -1 / H ≤ 1 / H := by
    rw [neg_div]; have : 0 < 1 / H := by positivity
    linarith
  have hlen : 1 / H ≤ -1 / H + 1 := by
    have : 1 / H ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hHpos (by norm_num)]; linarith
    rw [neg_div]; linarith
  have hint_le : ∫ β in (-1 / H)..(1 / H), ‖localAdditivePolynomial S coeff (θ0 + β)‖ ^ 2 ≤
      ∫ β in (-1 / H)..(1 / H), (2 * (Fintype.card ι : ℝ) *
        ∑ i, ‖localAdditivePolynomial (s i) (bb i) β‖ ^ 2 + 2 * ‖Z β‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on hab
    · exact (((continuous_localAdditivePolynomial' S coeff).comp
        (continuous_const.add continuous_id)).norm.pow 2).intervalIntegrable _ _
    · apply Continuous.intervalIntegrable
      exact (continuous_const.mul (continuous_finsetSum _ fun i _ => (hcX i).norm.pow 2)).add
        (continuous_const.mul (hcZ.norm.pow 2))
    · intro β _; exact hle β
  refine hint_le.trans ?_
  have ii1 : IntervalIntegrable (fun β => 2 * (Fintype.card ι : ℝ) *
      ∑ i, ‖localAdditivePolynomial (s i) (bb i) β‖ ^ 2) volume (-1 / H) (1 / H) :=
    (continuous_const.mul (continuous_finsetSum _ fun i _ => (hcX i).norm.pow 2)).intervalIntegrable _ _
  have ii2 : IntervalIntegrable (fun β => 2 * ‖Z β‖ ^ 2) volume (-1 / H) (1 / H) :=
    (continuous_const.mul (hcZ.norm.pow 2)).intervalIntegrable _ _
  have ii3 : ∀ i ∈ (Finset.univ : Finset ι), IntervalIntegrable
      (fun β => ‖localAdditivePolynomial (s i) (bb i) β‖ ^ 2) volume (-1 / H) (1 / H) :=
    fun i _ => ((hcX i).norm.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ii1 ii2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum ii3]
  have hpars : ∫ β in (-1 / H)..(1 / H), ‖Z β‖ ^ 2 ≤ ∑ n ∈ S, ‖ε n‖ ^ 2 :=
    parseval_le S ε _ _ hab hlen
  have h2 : 2 * ∫ β in (-1 / H)..(1 / H), ‖Z β‖ ^ 2 ≤ 2 * ∑ n ∈ S, ‖ε n‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hpars (by norm_num)
  linarith

end Erdos821.P5Marked
