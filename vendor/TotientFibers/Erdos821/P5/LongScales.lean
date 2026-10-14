import Erdos821.P5.LongGrowth

noncomputable section
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- The selected depth still gives a subpower sieve level uniformly in the
allowed logarithmic character moduli. -/
theorem eventual_rough_level (h₀ : ℕ) (τ C : ℝ) (hτ : 0 < τ) (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ L x ∧
      (W x ^ (4 * roughDepth h₀ x + 2)) * L x ^ C ≤ x ^ (τ / 4) := by
  let H : ℝ := 8 * h₀ + 18
  have hH : 0 < H := by dsimp [H]; positivity
  have hp := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    Real.tendsto_log_atTop).eventually_ge_atTop (8 * H / τ)
  have hl := Real.tendsto_log_atTop.eventually
    (eventual_log_le_rpow_mul 1 (τ / (8 * C)) (by norm_num) (by positivity))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hp, hl] with x hx hp hl
  have hL1 : 1 ≤ L x := hl.1
  have hLpos : 0 < L x := by linarith
  have hlog : Real.log (L x) ≤ τ / (8 * C) * L x := by simpa only [L, Real.rpow_one] using hl.2
  have hClog : C * Real.log (L x) ≤ (τ / 8) * L x := by
    have h := mul_le_mul_of_nonneg_left hlog hC.le
    have heq : C * (τ / (8 * C) * L x) = (τ / 8) * L x := by field_simp
    rwa [heq] at h
  have hHp : H ≤ (τ / 8) * L x ^ (1 / 4 : ℝ) := by
    change 8 * H / τ ≤ L x ^ (1 / 4 : ℝ) at hp
    have h := (div_le_iff₀ hτ).mp hp
    nlinarith
  have hprod : L x ^ (1 / 4 : ℝ) * L x ^ (3 / 4 : ℝ) = L x := by
    rw [← Real.rpow_add hLpos]
    norm_num
  have hsmall : H * L x ^ (3 / 4 : ℝ) ≤ (τ / 8) * L x := by
    have h := mul_le_mul_of_nonneg_right hHp (Real.rpow_nonneg hLpos.le (3 / 4 : ℝ))
    nlinarith [hprod]
  have hlevel := (rough_level_exponent_le h₀ x hL1).trans hsmall
  refine ⟨hx, hL1, ?_⟩
  calc
    _ = Real.exp (Real.sqrt (L x) * ((4 * roughDepth h₀ x + 2 : ℕ) : ℝ) +
        C * Real.log (L x)) := by
      rw [W, ← Real.exp_nat_mul, Real.rpow_def_of_pos hLpos, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((τ / 4) * L x) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.rpow_def_of_pos (by linarith : 0 < x)]; dsimp [L]; congr 1; ring

/-- The sieve error decays faster than every prescribed logarithmic power. -/
theorem eventual_rough_depth_error (h₀ : ℕ) (A : ℝ) (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ L x ∧
      Real.exp (-(roughDepth h₀ x : ℝ)) ≤ L x ^ (-A) := by
  have he := Real.tendsto_log_atTop.eventually
    (eventual_log_le_rpow_mul (1 / 4) (2 / A) (by norm_num) (by positivity))
  filter_upwards [he] with x hx
  change 1 ≤ L x ∧ Real.log (L x) ≤ 2 / A * L x ^ (1 / 4 : ℝ) at hx
  have hLpos : 0 < L x := by linarith [hx.1]
  have h := mul_le_mul_of_nonneg_left hx.2 hA.le
  have heq : A * (2 / A * L x ^ (1 / 4 : ℝ)) = 2 * L x ^ (1 / 4 : ℝ) := by field_simp
  rw [heq] at h
  refine ⟨hx.1, ?_⟩
  rw [Real.rpow_def_of_pos hLpos]
  exact Real.exp_le_exp.mpr (by nlinarith [roughDepth_lower h₀ x])

/-- The eventual geometry and the normalized sieve-level error. -/
theorem eventual_rough_geometry (h₀ : ℕ) (τ C : ℝ) (hτ : 0 < τ) (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ L x ∧ 2 ≤ W x ∧
      ∀ (P : ℝ) (q : ℕ), x ^ τ / 2 ≤ P → (q : ℝ) ≤ L x ^ C →
        1 ≤ P ∧ 1 ≤ x ^ (τ / 2) ∧
          W x ^ (4 * roughDepth h₀ x + 2) * q * x ^ (τ / 2) ≤ P ∧
          W x ^ (4 * roughDepth h₀ x + 2) / P ≤ 2 * x ^ (-(3 * τ / 4)) := by
  have hp := (tendsto_rpow_atTop (by positivity : 0 < τ / 4)).eventually_ge_atTop (2 : ℝ)
  filter_upwards [eventual_rough_level h₀ τ C hτ hC, hp] with x hx hp
  have hxpos : 0 < x := by linarith [hx.1]
  have hLpos : 0 < L x := by linarith [hx.2.1]
  have hs1 : 1 ≤ Real.sqrt (L x) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hLpos.le).mpr
    simpa using hx.2.1
  have hW2 : 2 ≤ W x := by
    dsimp [W]
    linarith [Real.add_one_le_exp (Real.sqrt (L x))]
  refine ⟨hx.1, hx.2.1, hW2, ?_⟩
  intro P q hP hq
  let D := W x ^ (4 * roughDepth h₀ x + 2)
  have hDpos : 0 < D := by dsimp [D, W]; positivity
  have hLC1 : 1 ≤ L x ^ C := Real.one_le_rpow hx.2.1 hC.le
  have hDq : D * q ≤ x ^ (τ / 4) :=
    (mul_le_mul_of_nonneg_left hq hDpos.le).trans hx.2.2
  have hD : D ≤ x ^ (τ / 4) := by
    apply le_trans _ hx.2.2
    nlinarith [mul_le_mul_of_nonneg_left hLC1 hDpos.le]
  have hxtau : 2 ≤ x ^ τ := hp.trans (Real.rpow_le_rpow_of_exponent_le hx.1 (by linarith))
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hX1 : 1 ≤ x ^ (τ / 2) := Real.one_le_rpow hx.1 (by positivity)
  have hsplit : x ^ (3 * τ / 4) * x ^ (τ / 4) = x ^ τ := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hgeom : D * q * x ^ (τ / 2) ≤ P := by
    calc
      _ ≤ x ^ (τ / 4) * x ^ (τ / 2) :=
        mul_le_mul_of_nonneg_right hDq (Real.rpow_nonneg hxpos.le _)
      _ = x ^ (3 * τ / 4) := by rw [← Real.rpow_add hxpos]; congr 1; ring
      _ ≤ x ^ τ / 2 := by
        have h := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hxpos.le (3 * τ / 4))
        rw [hsplit] at h
        linarith
      _ ≤ P := hP
  have hratio : x ^ (-(3 * τ / 4)) = x ^ (τ / 4) / x ^ τ := by
    rw [← Real.rpow_sub hxpos]
    congr 1
    ring
  have herr : D / P ≤ 2 * x ^ (-(3 * τ / 4)) := by
    calc
      _ ≤ x ^ (τ / 4) / P := div_le_div_of_nonneg_right hD hPpos.le
      _ ≤ x ^ (τ / 4) / (x ^ τ / 2) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hxpos.le _) (by positivity) hP
      _ = _ := by rw [hratio]; field_simp
  exact ⟨hP1, hX1, hgeom, herr⟩

end Erdos821.P5Core
