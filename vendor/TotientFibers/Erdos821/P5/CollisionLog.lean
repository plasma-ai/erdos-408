import Erdos821.P5.EndpointShiftCollision
import Erdos821.P5.LongGrowth

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem endpoint_shift_sum_free_multiples_log :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (C τ η X Y R : ℝ) (E H : Endpoint) (p D : ℕ) (k : ℤ),
        EndpointBound x C τ η E → EndpointBound x C τ η H →
        0 < X → 0 < R → 1 ≤ p → (p : ℝ) ≤ Y → p ∣ D →
        p.primeFactors ⊆ Finset.univ.biUnion G.primes →
        Y ≤ x ^ (2 : ℕ) → Y ≤ R * X →
        ∀ s : Finset ℕ,
          (∀ n ∈ s, X ≤ (n : ℝ)) →
          (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ Y ∧ p ∣ n ∧
            0 < (n : ℤ) + k * (D : ℤ) ∧
            ((n : ℤ) + k * (D : ℤ)).toNat ≤ Y) →
          (∑ n ∈ s, ‖endpoint G x E n‖ *
            ‖endpoint G x H ((n : ℤ) + k * (D : ℤ)).toNat‖ / (n : ℝ)) ≤
            K * R * L x ^ (4 * C + c) / p := by
  obtain ⟨c, K, hc, hK, hm⟩ := endpoint_shift_sum_free_multiples
  refine ⟨c, K * (3 : ℝ) ^ c, hc, mul_pos hK (Real.rpow_pos_of_pos (by norm_num) c), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hL
  intro G C τ η X Y R E H p D k hE hH hX hR hp hpY hpD hprimes hYx hYRX s hlo hs
  change 1 ≤ L x at hL
  have hLpos : 0 < L x := by linarith
  have hxpos : 0 < x := by linarith
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hppos : 0 < (p : ℝ) := by linarith
  have hYpos : 0 < Y := hppos.trans_le hpY
  have harg : 1 ≤ 2 * Y / (p : ℝ) := (le_div_iff₀ hppos).mpr (by linarith)
  have hlog0 : 0 ≤ Real.log (2 * Y / p) := Real.log_nonneg harg
  have hlog : Real.log (2 * Y / p) ≤ 3 * L x := by
    have hargle : 2 * Y / (p : ℝ) ≤ 2 * x ^ (2 : ℕ) :=
      (div_le_self (by positivity : 0 ≤ 2 * Y) hpR).trans (by gcongr)
    have hlogx : Real.log (2 * x ^ (2 : ℕ)) = Real.log 2 + 2 * L x := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hxpos.ne'), Real.log_pow]
      simp only [L, Nat.cast_ofNat]
    apply (Real.log_le_log (by positivity) hargle).trans
    rw [hlogx]
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hYX : Y / X ≤ R := (div_le_iff₀ hX).mpr (by simpa [mul_comm] using hYRX)
  have hpow : Real.log (2 * Y / p) ^ c ≤ (3 * L x) ^ c :=
    Real.rpow_le_rpow hlog0 hlog hc
  have hb := hm G x C τ η X Y E H p D k hL hE hH hX hp hpY hpD hprimes s hlo hs
  calc
    _ ≤ (K * (Y / p) * L x ^ (4 * C) * Real.log (2 * Y / p) ^ c) / X := hb
    _ = K * (Y / X) * L x ^ (4 * C) * Real.log (2 * Y / p) ^ c / p := by ring
    _ ≤ K * R * L x ^ (4 * C) * (3 * L x) ^ c / p := by gcongr
    _ = (K * (3 : ℝ) ^ c) * R * L x ^ (4 * C + c) / p := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hLpos.le,
        Real.rpow_add hLpos]
      ring

/-- Every fixed logarithmic power times this prime-scale error has arbitrary
logarithmic saving. The exponent a only needs to be positive. -/
theorem eventual_log_power_mul_exp_neg (a A B : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ L x ∧
      L x ^ B * Real.exp (-(L x ^ a)) ≤ L x ^ (-A) := by
  let v := |A + B| + 1
  have hv : 0 < v := by dsimp [v]; positivity
  have he := Real.tendsto_log_atTop.eventually
    (eventual_log_le_rpow_mul a v⁻¹ ha (inv_pos.mpr hv))
  filter_upwards [he] with x hx
  change 1 ≤ L x ∧ Real.log (L x) ≤ v⁻¹ * L x ^ a at hx
  have hL : 0 < L x := by linarith [hx.1]
  refine ⟨hx.1, ?_⟩
  have hlog : Real.log (L x) ≤ v⁻¹ * L x ^ a := by simpa only [L] using hx.2
  have hc : |A + B| * v⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hv]
    dsimp [v]
    linarith
  have hb : Real.log (L x) * (A + B) ≤ L x ^ a := by
    calc
      _ ≤ Real.log (L x) * |A + B| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (Real.log_nonneg hx.1)
      _ ≤ (v⁻¹ * L x ^ a) * |A + B| :=
        mul_le_mul_of_nonneg_right hlog (abs_nonneg _)
      _ = (|A + B| * v⁻¹) * L x ^ a := by ring
      _ ≤ 1 * L x ^ a := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hL.le a)
      _ = _ := one_mul _
  have hB : L x ^ B = Real.exp (Real.log (L x) * B) := Real.rpow_def_of_pos hL B
  have hA : L x ^ (-A) = Real.exp (Real.log (L x) * (-A)) := Real.rpow_def_of_pos hL (-A)
  rw [hB, hA, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

theorem eventual_constant_log_power_mul_exp_neg (a A B K : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ L x ∧
      K * L x ^ B * Real.exp (-(L x ^ a)) ≤ L x ^ (-A) := by
  filter_upwards [eventual_log_power_mul_exp_neg a A (B + 1) ha,
    Real.tendsto_log_atTop.eventually_ge_atTop K] with x hx hK
  change K ≤ L x at hK
  refine ⟨hx.1, ?_⟩
  have hLpos : 0 < L x := by linarith [hx.1]
  calc
    _ ≤ L x * L x ^ B * Real.exp (-(L x ^ a)) := by gcongr
    _ = L x ^ (B + 1) * Real.exp (-(L x ^ a)) := by
      rw [Real.rpow_add hLpos, Real.rpow_one]
      ring
    _ ≤ _ := hx.2

end Erdos821.P5Core
