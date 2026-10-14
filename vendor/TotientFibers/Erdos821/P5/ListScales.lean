import Erdos821.P5.HarmonicLists
import Erdos821.P5.LongGrowth

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem admissible_count_le (P : Geometry) (G : PrimeGroups) (x : ℝ)
    (hG : Admissible P x G) : (G.size : ℝ) ≤ 2 * P.C₀ * T x := by
  have hcard : G.big.card + G.small.card = G.size := by
    simpa only [PrimeGroups.big, Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ G.small)
  have hR : (G.big.card : ℝ) + G.small.card = G.size := by exact_mod_cast hcard
  linarith [hG.1.2, hG.2.1.2]

theorem admissible_prime_upper (P : Geometry) (G : PrimeGroups) (x : ℝ)
    (hL : 1 ≤ L x) (hG : Admissible P x G) (g : Fin G.size) (p : ℕ)
    (hp : p ∈ G.primes g) : (p : ℝ) ≤ Real.exp (L x ^ P.d) := by
  have h := hG.2.2.2.1 g p hp
  split_ifs at h with hs
  · exact h.2.trans (Real.exp_le_exp.mpr
      (Real.rpow_le_rpow_of_exponent_le hL
        (le_of_lt (lt_trans P.ordered.2.2.1 P.ordered.2.2.2.1))))
  · exact h.2

theorem listProduct_log_le (P : Geometry) (G : PrimeGroups) (x : ℝ) (M : ℕ)
    (a : G.graph.Labels M) (hL : 1 ≤ L x) (hG : Admissible P x G) :
    Real.log (listProduct G.graph a) ≤ (M : ℝ) * G.size * L x ^ P.d := by
  have hp (g : Fin G.size) (i : Fin M) : 0 < ((a g i).val : ℝ) := by
    exact_mod_cast (G.prime g _ (a g i).property).pos
  have hlog (g : Fin G.size) (i : Fin M) : Real.log ((a g i).val : ℝ) ≤ L x ^ P.d := by
    apply (Real.log_le_log (hp g i) (admissible_prime_upper P G x hL hG g _ (a g i).property)).trans
    exact (Real.log_exp _).le
  unfold listProduct
  simp only [Nat.cast_prod]
  rw [Real.log_prod (fun g hg => (Finset.prod_pos (fun i hi => hp g i)).ne')]
  simp_rw [Real.log_prod (fun i hi => (hp _ i).ne')]
  calc
    _ ≤ ∑ g : Fin G.size, ∑ i : Fin M, L x ^ P.d :=
      Finset.sum_le_sum (fun g hg => Finset.sum_le_sum (fun i hi => hlog g i))
    _ = _ := by simp; ring

/-- Fixed list length only affects the threshold; every label product is subpower. -/
theorem eventual_listProduct_le (P : Geometry) (M : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ L x ∧
      ∀ (G : PrimeGroups), Admissible P x G →
        ∀ a : G.graph.Labels M, (listProduct G.graph a : ℝ) ≤ x ^ γ := by
  let β := 2 * (M : ℝ) * P.C₀
  have hβ : 0 ≤ β := by
    have hC₀ := P.positive.2.1
    dsimp [β]
    positivity
  have hβ1 : 0 < β + 1 := by linarith
  have hr : 0 < 1 - P.d := by linarith [P.ordered.2.2.2.2]
  have he := (Real.tendsto_log_atTop.eventually
    (eventual_log_le_rpow_mul (1 - P.d) (γ / (β + 1)) hr (div_pos hγ hβ1)))
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with x hx hxx
  refine ⟨hx.1, ?_⟩
  intro G hG a
  have hL : 0 < L x := lt_of_lt_of_le zero_lt_one hx.1
  have hT : 0 ≤ T x := Real.log_nonneg hx.1
  have hβc : β * (γ / (β + 1)) ≤ γ := by
    calc
      _ ≤ (β + 1) * (γ / (β + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_pos hγ hβ1).le
      _ = γ := by field_simp
  have hpow : L x ^ (1 - P.d) * L x ^ P.d = L x := by
    rw [← Real.rpow_add hL]
    simp
  have hlog : Real.log (listProduct G.graph a) ≤ γ * L x := by
    calc
      _ ≤ (M : ℝ) * G.size * L x ^ P.d := listProduct_log_le P G x M a hx.1 hG
      _ ≤ β * T x * L x ^ P.d := by
        have hs := mul_le_mul_of_nonneg_left (admissible_count_le P G x hG) (Nat.cast_nonneg M : 0 ≤ (M : ℝ))
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL.le _)
        simpa only [β, mul_assoc, mul_left_comm, mul_comm] using hs
      _ ≤ β * (γ / (β + 1) * L x ^ (1 - P.d)) * L x ^ P.d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx.2 hβ)
          (Real.rpow_nonneg hL.le _)
      _ = (β * (γ / (β + 1))) * (L x ^ (1 - P.d) * L x ^ P.d) := by ring
      _ = (β * (γ / (β + 1))) * L x := by rw [hpow]
      _ ≤ γ * L x := mul_le_mul_of_nonneg_right hβc hL.le
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hxx
  rw [Real.rpow_def_of_pos hxpos]
  have hdpos : 0 < (listProduct G.graph a : ℝ) := by exact_mod_cast listProduct_pos G.graph a
  calc
    _ = Real.exp (Real.log (listProduct G.graph a)) := (Real.exp_log hdpos).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by simpa only [L, mul_comm] using hlog)

end Erdos821.P5Core
