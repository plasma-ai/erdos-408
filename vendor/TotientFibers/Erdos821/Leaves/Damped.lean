import Mathlib
import Erdos821.Blueprint.Graph
import Erdos821.Blueprint.Analytic

open scoped BigOperators
open Filter Topology

attribute [local instance] Classical.propDecidable

namespace Erdos821.GraphLemmas

theorem tendsto_pow_mul_geometric (k : ℕ) (r : ℝ) (hr : ‖r‖ < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ k * r ^ n)) atTop (𝓝 0) := by
  have hsumm : Summable (fun n : ℕ => ((n : ℝ) ^ k * r ^ n)) :=
    summable_pow_mul_geometric_of_norm_lt_one k hr
  have hco : Tendsto (fun n : ℕ => ((n : ℝ) ^ k * r ^ n)) Filter.cofinite (𝓝 0) :=
    hsumm.tendsto_cofinite_zero
  rwa [Nat.cofinite_eq_atTop] at hco

theorem bounded_pow_mul_geometric (k : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C, ∀ n : ℕ, ((n : ℝ) ^ k * r ^ n) ≤ C := by
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have htend := tendsto_pow_mul_geometric k r hr_norm
  have hbdd : Bornology.IsBounded (Set.range (fun n : ℕ => ((n : ℝ) ^ k * r ^ n))) :=
    Metric.isBounded_range_of_tendsto _ htend
  rw [Metric.isBounded_range_iff] at hbdd
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨C + (((0 : ℕ) : ℝ) ^ k * r ^ (0 : ℕ)), ?_⟩
  intro n
  have hdist := hC n 0
  have hle : ((n : ℝ) ^ k * r ^ n) - (((0 : ℕ) : ℝ) ^ k * r ^ (0 : ℕ)) ≤ C := by
    calc ((n : ℝ) ^ k * r ^ n) - (((0 : ℕ) : ℝ) ^ k * r ^ (0 : ℕ))
        ≤ |((n : ℝ) ^ k * r ^ n) - (((0 : ℕ) : ℝ) ^ k * r ^ (0 : ℕ))| := le_abs_self _
      _ = dist (((n : ℝ) ^ k * r ^ n)) (((0 : ℕ) : ℝ) ^ k * r ^ (0 : ℕ)) := by
          rw [Real.dist_eq]
      _ ≤ C := hdist
  linarith

theorem sqrt_pow_eq (q : ℝ) (hq : 0 < q) (z : ℕ) :
    q ^ (((z : ℕ) : ℝ) / 2) = (Real.sqrt q) ^ z := by
  have hq0 : 0 ≤ q := le_of_lt hq
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq0]
  congr 1
  ring

theorem vinv_bound (v V : ℝ) (hv : 0 < v) (hV : v ≤ V) (t tMax : ℕ) (ht : t ≤ tMax) :
    V ^ (-(t : ℤ)) ≤ max 1 ((v⁻¹) ^ tMax) := by
  have hVpos : 0 < V := lt_of_lt_of_le hv hV
  have hVt : 0 < V ^ t := pow_pos hVpos t
  have hvt : 0 < v ^ t := pow_pos hv t
  have hle : v ^ t ≤ V ^ t := pow_le_pow_left₀ (le_of_lt hv) hV t
  have hVinv : V ^ (-(t : ℤ)) = ((V ^ t)⁻¹) := by
    rw [zpow_neg, zpow_natCast]
  have hvinv : ((V ^ t)⁻¹) ≤ ((v ^ t)⁻¹) := by
    rw [inv_le_inv₀ hVt hvt]
    exact hle
  have hvinv2 : ((v ^ t)⁻¹) = (v⁻¹) ^ t := by
    rw [inv_pow]
  rw [hvinv2] at hvinv
  rw [hVinv]
  -- now goal (V^t)⁻¹ ≤ max..., with hvinv : (V^t)⁻¹ ≤ (v⁻¹)^t
  have hmax : (v⁻¹) ^ t ≤ max 1 ((v⁻¹) ^ tMax) := by
    by_cases hge : 1 ≤ v⁻¹
    · have hmono : (v⁻¹) ^ t ≤ (v⁻¹) ^ tMax :=
        pow_le_pow_right₀ hge ht
      calc (v⁻¹) ^ t ≤ (v⁻¹) ^ tMax := hmono
        _ ≤ max 1 ((v⁻¹) ^ tMax) := le_max_right _ _
    · have hlt : v⁻¹ < 1 := lt_of_not_ge hge
      have hv0 : 0 ≤ v⁻¹ := le_of_lt (inv_pos.mpr hv)
      have hle1 : (v⁻¹) ^ t ≤ 1 := pow_le_one₀ hv0 (le_of_lt hlt)
      calc (v⁻¹) ^ t ≤ 1 := hle1
        _ ≤ max 1 ((v⁻¹) ^ tMax) := le_max_left _ _
  exact le_trans hvinv hmax

theorem desc_le (z t tMax : ℕ) (ht : t ≤ tMax) :
    (z + t).descFactorial t ≤ (z + tMax) ^ tMax := by
  have h1 : (z + t).descFactorial t ≤ (z + t) ^ t :=
    Nat.descFactorial_le_pow _ _
  have h2 : (z + t) ^ t ≤ (z + tMax) ^ t := by
    apply Nat.pow_le_pow_left
    exact Nat.add_le_add_left ht z
  have h3 : (z + tMax) ^ t ≤ (z + tMax) ^ tMax := by
    by_cases hb : 1 ≤ z + tMax
    · exact Nat.pow_le_pow_right hb ht
    · have h0 : z + tMax = 0 := Nat.lt_one_iff.mp (lt_of_not_ge hb)
      have hz : z = 0 := by omega
      have htM : tMax = 0 := by omega
      subst hz; subst htM
      have ht0 : t = 0 := Nat.le_zero.mp ht
      subst ht0
      simp
  exact le_trans (le_trans h1 h2) h3

theorem bounded_shifted (tMax : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C, ∀ z : ℕ, ((((z + tMax : ℕ) : ℝ) ^ tMax) * r ^ z) ≤ C := by
  choose C hC using fun m => bounded_pow_mul_geometric m r hr0 hr1
  refine ⟨∑ m ∈ Finset.range (tMax + 1),
    ((tMax : ℝ) ^ (tMax - m) * (tMax.choose m : ℝ) * C m), ?_⟩
  intro z
  have hexpand : ((((z + tMax : ℕ) : ℝ) ^ tMax)) =
      ∑ m ∈ Finset.range (tMax + 1),
        ((z : ℝ) ^ m * (tMax : ℝ) ^ (tMax - m) * (tMax.choose m : ℝ)) := by
    rw [Nat.cast_add, add_pow]
  rw [hexpand, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m hm
  have hbound := hC m z
  have hnonneg : 0 ≤ (tMax : ℝ) ^ (tMax - m) * (tMax.choose m : ℝ) := by
    positivity
  calc ((z : ℝ) ^ m * (tMax : ℝ) ^ (tMax - m) * (tMax.choose m : ℝ)) * r ^ z
      = ((z : ℝ) ^ m * r ^ z) * ((tMax : ℝ) ^ (tMax - m) * (tMax.choose m : ℝ)) := by ring
    _ ≤ C m * ((tMax : ℝ) ^ (tMax - m) * (tMax.choose m : ℝ)) :=
        mul_le_mul_of_nonneg_right hbound hnonneg
    _ = (tMax : ℝ) ^ (tMax - m) * (tMax.choose m : ℝ) * C m := by ring

end Erdos821.GraphLemmas

namespace Erdos821.Blueprint.Graph

theorem damped_factorial_bound (q v : ℝ) (hq : 0 < q) (hq' : q < 1) (hv : 0 < v)
    (tMax : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (t z : ℕ) (V : ℝ), t ≤ tMax → v ≤ V →
      V ^ (-(t : ℤ)) * ((z + t).descFactorial t : ℝ) * q ^ ((z : ℝ) / 2) ≤ C := by
  -- r = sqrt q
  set r : ℝ := Real.sqrt q with hr_def
  have hr0 : 0 ≤ r := Real.sqrt_nonneg q
  have hr1 : r < 1 := by
    have hlt : Real.sqrt q < Real.sqrt 1 :=
      Real.sqrt_lt_sqrt (le_of_lt hq) hq'
    rwa [Real.sqrt_one] at hlt
  have hr_pow : ∀ z : ℕ, q ^ (((z : ℕ) : ℝ) / 2) = r ^ z :=
    fun z => Erdos821.GraphLemmas.sqrt_pow_eq q hq z
  obtain ⟨C0, hC0⟩ := Erdos821.GraphLemmas.bounded_shifted tMax r hr0 hr1
  -- C_v for V part
  set Cv : ℝ := max 1 ((v⁻¹) ^ tMax) with hCv_def
  have hCv_pos : 0 < Cv := lt_max_iff.mpr (Or.inl one_pos)
  have hCv_ge : ∀ t : ℕ, t ≤ tMax → ∀ V : ℝ, v ≤ V → V ^ (-(t : ℤ)) ≤ Cv := by
    intro t ht V hV
    have hle := Erdos821.GraphLemmas.vinv_bound v V hv hV t tMax ht
    rw [hCv_def]
    exact hle
  -- C0 may not be positive; take max with 0? Actually terms nonnegative, so C0 ≥ 0?
  -- For safety, final C = max 1 (Cv * max 0 C0)? Simpler: C = max 1 (Cv * C0) with C0 possibly negative?
  -- Since C0 bounds nonnegative terms, C0 ≥ 0? Let's ensure final C > 0 and bounds.
  -- First, show C0 ≥ 0? Since term at z=0 is nonnegative and ≤ C0, C0 ≥ term ≥ 0.
  have hC0_nonneg : 0 ≤ C0 := by
    have h0 := hC0 0
    have hterm_nonneg : 0 ≤ ((((0 + tMax : ℕ) : ℝ) ^ tMax) * r ^ (0 : ℕ)) := by
      positivity
    linarith
  refine ⟨max 1 (Cv * C0), lt_max_iff.mpr (Or.inl one_pos), ?_⟩
  intro t z V ht hV
  have hVle := hCv_ge t ht V hV
  have hdesc_nat : (z + t).descFactorial t ≤ (z + tMax) ^ tMax :=
    Erdos821.GraphLemmas.desc_le z t tMax ht
  have hdescR : (((z + t).descFactorial t : ℕ) : ℝ) ≤ ((((z + tMax : ℕ)) : ℝ) ^ tMax) := by
    exact_mod_cast hdesc_nat
  have hr_eq := hr_pow z
  have hshift := hC0 z
  -- nonnegativity
  have hVpos : 0 < V := lt_of_lt_of_le hv hV
  have hVpow_pos : 0 < V ^ (-(t : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    exact inv_pos.mpr (pow_pos hVpos t)
  have hdesc_nonneg : 0 ≤ (((z + t).descFactorial t : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq_nonneg : 0 ≤ q ^ (((z : ℕ) : ℝ) / 2) := le_of_lt (Real.rpow_pos_of_pos hq _)
  have hr_pow_nonneg : 0 ≤ r ^ z := pow_nonneg hr0 z
  -- rewrite q^... to r^z
  rw [hr_eq]
  -- V^(-t) * desc * r^z = V^(-t) * (desc * r^z) ≤ Cv * C0 ≤ max...
  have hdesc_r : (((z + t).descFactorial t : ℕ) : ℝ) * r ^ z ≤ ((((z + tMax : ℕ)) : ℝ) ^ tMax) * r ^ z := by
    apply mul_le_mul_of_nonneg_right hdescR hr_pow_nonneg
  have hdesc_r_bound : (((z + t).descFactorial t : ℕ) : ℝ) * r ^ z ≤ C0 := le_trans hdesc_r hshift
  have hV_nonneg : 0 ≤ V ^ (-(t : ℤ)) := le_of_lt hVpow_pos
  have hprod_nonneg : 0 ≤ (((z + t).descFactorial t : ℕ) : ℝ) * r ^ z :=
    mul_nonneg hdesc_nonneg hr_pow_nonneg
  calc V ^ (-(t : ℤ)) * (((z + t).descFactorial t : ℕ) : ℝ) * r ^ z
      = V ^ (-(t : ℤ)) * ((((z + t).descFactorial t : ℕ) : ℝ) * r ^ z) := by ring
    _ ≤ Cv * C0 := mul_le_mul hVle hdesc_r_bound hprod_nonneg (le_trans (by positivity : (0:ℝ) ≤ 1) (le_max_left _ _))
    _ ≤ max 1 (Cv * C0) := le_max_right _ _

example : @Erdos821.Blueprint.Graph.damped_factorial_bound =
    @Erdos821.Blueprint.Graph.damped_factorial_bound := rfl

end Erdos821.Blueprint.Graph

