import Erdos821.P5.EndpointRoughBounds
import Erdos821.P5.GroupFreeBounds
import Erdos821.P5.LongGrowth

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- Any fixed logarithmic power is eventually absorbed by exp(sqrt(log x)). -/
theorem eventual_log_rpow_le_exp_sqrt (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ L x ∧ L x ^ A ≤ Real.exp (Real.sqrt (L x)) := by
  let v := |A| + 1
  have hv : 0 < v := by dsimp [v]; positivity
  have he := Real.tendsto_log_atTop.eventually
    (eventual_log_le_rpow_mul (1 / 2) v⁻¹ (by norm_num) (inv_pos.mpr hv))
  filter_upwards [he] with x hx
  have hL : 0 < L x := lt_of_lt_of_le zero_lt_one hx.1
  refine ⟨hx.1, ?_⟩
  have hlog : Real.log (L x) ≤ v⁻¹ * Real.sqrt (L x) := by
    simpa only [L, Real.sqrt_eq_rpow] using hx.2
  have hc : |A| * v⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hv]
    dsimp [v]
    linarith
  rw [Real.rpow_def_of_pos hL]
  apply Real.exp_le_exp.mpr
  calc
    Real.log (L x) * A ≤ Real.log (L x) * |A| :=
      mul_le_mul_of_nonneg_left (le_abs_self A) (Real.log_nonneg hx.1)
    _ ≤ (v⁻¹ * Real.sqrt (L x)) * |A| := mul_le_mul_of_nonneg_right hlog (abs_nonneg A)
    _ = (|A| * v⁻¹) * Real.sqrt (L x) := by ring
    _ ≤ 1 * Real.sqrt (L x) := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
    _ = _ := one_mul _

theorem endpoint_norm_exp_le (G : PrimeGroups) (x C τ η : ℝ) (E : Endpoint)
    (hL : 1 ≤ L x) (hE : EndpointBound x C τ η E) (n : ℕ) :
    ‖endpoint G x E n‖ ≤ L x ^ (2 * C) *
      Real.exp (2 * Real.log 2 * Real.log (groupFreePart G n : ℝ) / Real.sqrt (L x)) := by
  have hLpos : 0 < L x := by linarith
  have hW : 1 < W x := by
    unfold W
    exact Real.one_lt_exp_iff.mpr (Real.sqrt_pos.mpr hLpos)
  have hd := roughDivisorCountTask_proof (W x) (groupFreePart G n) hW (groupFreePart_pos G n)
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg _ : 0 ≤
      (((groupFreePart G n).divisors.filter (rough (W x))).card : ℝ)) hd 2
  have hexp : (Real.exp (Real.log 2 * Real.log (groupFreePart G n : ℝ) / Real.log (W x))) ^ 2 =
      Real.exp (2 * Real.log 2 * Real.log (groupFreePart G n : ℝ) / Real.sqrt (L x)) := by
    rw [pow_two, ← Real.exp_add]
    simp only [W, Real.log_exp]
    congr 1
    ring
  apply (endpoint_norm_rough_divisors_le G x C τ η E hL hE n).trans
  rw [← hexp]
  exact mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hLpos.le _)

theorem endpoint_log_exponent_le (G : PrimeGroups) (x r : ℝ) (n : ℕ)
    (hx : 1 ≤ x) (hL : 1 ≤ L x) (hn : 0 < n) (hnx : (n : ℝ) ≤ x ^ r) :
    2 * Real.log 2 * Real.log (groupFreePart G n : ℝ) / Real.sqrt (L x) ≤
      (2 * r * Real.log 2) * Real.sqrt (L x) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hLpos : 0 < L x := by linarith
  have hs : 0 < Real.sqrt (L x) := Real.sqrt_pos.mpr hLpos
  have hNpos : 0 < (groupFreePart G n : ℝ) := by exact_mod_cast groupFreePart_pos G n
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hNle : (groupFreePart G n : ℝ) ≤ n := by
    exact_mod_cast Nat.le_of_dvd hn (groupFreePart_dvd G n)
  have hlogN : Real.log (groupFreePart G n : ℝ) ≤ r * L x := by
    calc
      _ ≤ Real.log (n : ℝ) := Real.log_le_log hNpos hNle
      _ ≤ Real.log (x ^ r) := Real.log_le_log hnpos hnx
      _ = _ := by rw [Real.log_rpow hxpos]; rfl
  apply (div_le_iff₀ hs).mpr
  have heq : (2 * r * Real.log 2) * Real.sqrt (L x) * Real.sqrt (L x) =
      2 * Real.log 2 * (r * L x) := by
    calc
      _ = (2 * r * Real.log 2) * (Real.sqrt (L x)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hLpos.le]; ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hlogN (by positivity)

/-- Uniform pointwise endpoint bound for positive integers of bounded power size. -/
theorem eventual_endpoint_sup (C r : ℝ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ L x ∧
      ∀ (G : PrimeGroups) (τ η : ℝ) (E : Endpoint), EndpointBound x C τ η E →
        ∀ n : ℕ, 0 < n → (n : ℝ) ≤ x ^ r →
          ‖endpoint G x E n‖ ≤ Real.exp ((1 + 2 * r * Real.log 2) * Real.sqrt (L x)) := by
  filter_upwards [eventual_log_rpow_le_exp_sqrt (2 * C), eventually_ge_atTop (1 : ℝ)] with x hx hxx
  refine ⟨hx.1, ?_⟩
  intro G τ η E hE n hn hnx
  have harg := endpoint_log_exponent_le G x r n hxx hx.1 hn hnx
  calc
    _ ≤ L x ^ (2 * C) *
        Real.exp (2 * Real.log 2 * Real.log (groupFreePart G n : ℝ) / Real.sqrt (L x)) :=
      endpoint_norm_exp_le G x C τ η E hx.1 hE n
    _ ≤ Real.exp (Real.sqrt (L x)) * Real.exp ((2 * r * Real.log 2) * Real.sqrt (L x)) :=
      mul_le_mul hx.2 (Real.exp_le_exp.mpr harg) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos821.P5Core
