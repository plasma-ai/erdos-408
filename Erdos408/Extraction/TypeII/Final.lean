import Erdos408.Extraction.TypeII.Numeric

/-!
# Collecting the bounds

With `u = L^{1/200}` bounding every factor of size `L^{o(1)}`,

  `j B₄ ≤ C₄ x L^{-3} u⁴`  and  `j B₅ ≤ C₅ x L^{-1.1} u⁶`,

so that `|Comp_j - Prox_j| ≤ (C₄ + C₅)(x/L) L^{-1/20}`.
-/

namespace Erdos408.TypeII

open Finset Real Filter

/-- The E4 bound against the fudge factor `u`. -/
theorem bound4_le {q : ℝ} {K : ℕ} {CN c E₂ κ CΦ C₂ : ℝ} {M : ℕ → ℝ} {x γ : ℝ} {A r : ℕ}
    {u : ℝ} (hx : 1 < x) (hκ : 1 < κ) (hL : 1 ≤ Real.log x) (hu : 1 ≤ u) (hM0 : 0 ≤ M 0)
    (hM1 : 0 ≤ M 1) (hC₂ : 0 ≤ C₂)
    (hSE0 : 0 ≤ endBound q K CN c E₂ x) (hF1 : endBound q K CN c E₂ x ≤ u)
    (hF2 : 2 ^ (K * inertPerCluster K CN x) * normBound q K CN c E₂ x ≤ u)
    (hF2' : 0 ≤ normBound q K CN c E₂ x)
    (hF3 : (r + 2 : ℝ) ≤ u)
    (hF4 : ((r + 1 : ℕ) * recipSum x γ ⌊κ * x + 1⌋₊ + highProd x ⌊κ * x + 1⌋₊ (r + 1 : ℕ)) ^
      (r + 1) ≤ u)
    (hF4' : 0 ≤ (r + 1 : ℕ) * recipSum x γ ⌊κ * x + 1⌋₊ + highProd x ⌊κ * x + 1⌋₊ (r + 1 : ℕ))
    (hF5 : (recipSum x γ ⌊κ * x + 1⌋₊ + highProd x ⌊κ * x + 1⌋₊ 1) ^ (r + 1) ≤ u)
    (hF5' : 0 ≤ recipSum x γ ⌊κ * x + 1⌋₊ + highProd x ⌊κ * x + 1⌋₊ 1)
    (hF6 : logLog x ^ (CΦ * 1) ≤ u)
    (hN : (⌊κ * x + 1⌋₊ : ℝ) ≤ 2 * κ * x) (hA : (A : ℝ) ≤ 5 * Real.log x ^ 4)
    (hτ : (3 * Real.log x ^ (-3 : ℝ) * (κ * x + 1) + 1) / x ≤ 7 * κ * Real.log x ^ (-3 : ℝ))
    (hκx : 4 * (κ * x + 1) ≤ 8 * κ * x) :
    (r + 2 : ℝ) * bound4 q K CN c E₂ κ CΦ C₂ M x γ (Real.log x ^ (-3 : ℝ)) A (r + 1) ≤
      (2 * κ * M 0 + 25 * M 0 * C₂ * κ + 56 * κ ^ 2 * M 1) * x * Real.log x ^ (-3 : ℝ) *
        u ^ 4 := by
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hκ0 : 0 < κ := by linarith
  have hu0 : 0 ≤ u := by linarith
  set w := L ^ (-3 : ℝ) with hw
  have hw0 : 0 < w := by positivity
  have hL3 : L ^ (3 : ℝ) = L ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast L 3
  have hwinv : w = (L ^ (3 : ℕ))⁻¹ := by rw [hw, Real.rpow_neg hL0.le, hL3]
  have hLm12 : L ^ (-12 : ℝ) = (L ^ (12 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hL0.le]; congr 1; exact_mod_cast Real.rpow_natCast L 12
  -- the three terms
  have hT1 : M 0 * endBound q K CN c E₂ x * (⌊κ * x + 1⌋₊ / L ^ (3 : ℝ)) *
      ((r + 1 : ℕ) * recipSum x γ ⌊κ * x + 1⌋₊ + highProd x ⌊κ * x + 1⌋₊ (r + 1 : ℕ)) ^ (r + 1) ≤
      M 0 * u * (2 * κ * x * w) * u := by
    have hNw : (⌊κ * x + 1⌋₊ : ℝ) / L ^ (3 : ℝ) ≤ 2 * κ * x * w := by
      rw [hwinv, hL3, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hN (by positivity)
    gcongr
  have hT2 : (A : ℝ) ^ 2 * (M 0 * (2 ^ (K * inertPerCluster K CN x) *
      normBound q K CN c E₂ x * (C₂ * (κ * x) * L ^ (-12 : ℝ)))) ≤
      25 * M 0 * C₂ * κ * x * w * u := by
    have hA2 : (A : ℝ) ^ 2 ≤ 25 * L ^ 8 := by
      have := pow_le_pow_left₀ (Nat.cast_nonneg A) hA 2
      calc (A : ℝ) ^ 2 ≤ (5 * L ^ 4) ^ 2 := this
        _ = 25 * L ^ 8 := by ring
    have hL8 : L ^ 8 * L ^ (-12 : ℝ) ≤ w := by
      rw [hLm12, hwinv]
      have h1 : L ^ 8 * (L ^ (12 : ℕ))⁻¹ = (L ^ (4 : ℕ))⁻¹ := by field_simp
      rw [h1]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hL (by norm_num))
    have hLr : 0 ≤ L ^ (-12 : ℝ) := by positivity
    calc (A : ℝ) ^ 2 * (M 0 * (2 ^ (K * inertPerCluster K CN x) *
          normBound q K CN c E₂ x * (C₂ * (κ * x) * L ^ (-12 : ℝ))))
        ≤ 25 * L ^ 8 * (M 0 * (u * (C₂ * (κ * x) * L ^ (-12 : ℝ)))) := by gcongr
      _ = 25 * M 0 * C₂ * κ * x * u * (L ^ 8 * L ^ (-12 : ℝ)) := by ring
      _ ≤ 25 * M 0 * C₂ * κ * x * u * w := by gcongr
      _ = 25 * M 0 * C₂ * κ * x * w * u := by ring
  have hT3 : M 1 * logLog x ^ (CΦ * 1) * ((3 * L ^ (-3 : ℝ) * (κ * x + 1) + 1) / x) *
      endBound q K CN c E₂ x * (4 * (κ * x + 1)) *
      (recipSum x γ ⌊κ * x + 1⌋₊ + highProd x ⌊κ * x + 1⌋₊ 1) ^ (r + 1) ≤
      M 1 * u * (7 * κ * w) * u * (8 * κ * x) * u := by
    have hτ0 : 0 ≤ (3 * L ^ (-3 : ℝ) * (κ * x + 1) + 1) / x := by positivity
    have hT0 : 0 ≤ logLog x ^ (CΦ * 1) := Real.rpow_nonneg (Real.log_nonneg hL) _
    gcongr
  unfold bound4
  have hsum := add_le_add (add_le_add hT1 hT2) hT3
  have hr2 : (0 : ℝ) ≤ r + 2 := by positivity
  have hD0 : 0 ≤ M 0 * u * (2 * κ * x * w) * u + 25 * M 0 * C₂ * κ * x * w * u +
      M 1 * u * (7 * κ * w) * u * (8 * κ * x) * u := by positivity
  calc (r + 2 : ℝ) * _ ≤ u * (M 0 * u * (2 * κ * x * w) * u + 25 * M 0 * C₂ * κ * x * w * u +
        M 1 * u * (7 * κ * w) * u * (8 * κ * x) * u) :=
        (mul_le_mul_of_nonneg_left hsum hr2).trans (mul_le_mul_of_nonneg_right hF3 hD0)
    _ = (2 * κ * M 0 * u ^ 3 + 25 * M 0 * C₂ * κ * u ^ 2 + 56 * κ ^ 2 * M 1 * u ^ 4) * x * w := by
        ring
    _ ≤ (2 * κ * M 0 * u ^ 4 + 25 * M 0 * C₂ * κ * u ^ 4 + 56 * κ ^ 2 * M 1 * u ^ 4) * x * w := by
        have h3 : u ^ 3 ≤ u ^ 4 := pow_le_pow_right₀ hu (by norm_num)
        have h2 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu (by norm_num)
        gcongr
    _ = _ := by ring

/-- The E5 bound against the fudge factor `u`. -/
theorem bound5_le {q : ℝ} {K : ℕ} {CN c E₂ κ : ℝ} {M : ℕ → ℝ} {x γ cW SP c₃ CW : ℝ}
    {K' r : ℕ} {u : ℝ} (hx : 1 < x) (hκ : 1 < κ) (hL : 1 ≤ Real.log x) (hu : 1 ≤ u)
    (hM0 : 0 ≤ M 0) (hc₃ : 0 < c₃) (hCW : 0 ≤ CW) (hγ : 0 < γ)
    (hSE0 : 0 ≤ endBound q K CN c E₂ x) (hF1 : endBound q K CN c E₂ x ≤ u)
    (hF3 : (r + 2 : ℝ) ≤ u) (hcW0 : 0 ≤ cW) (hcW : cW ≤ CW * u / Real.log x)
    (hN : (⌊κ * x + 1⌋₊ : ℝ) ≤ 2 * κ * x) (hP0 : 0 ≤ highProd x ⌊κ * x + 1⌋₊ 1)
    (hPr : highProd x ⌊κ * x + 1⌋₊ 1 ^ r ≤ u) (hP1 : highProd x ⌊κ * x + 1⌋₊ 1 ≤ u)
    (hK' : (K' : ℝ) ≤ 3 * Real.log x ^ (9 / 10 : ℝ)) (hSP0 : 0 ≤ SP)
    (hSP : SP ≤ 2 * Real.log x ^ (45 / 100 : ℝ))
    (hY0 : 0 ≤ Real.log (proxyCutoff x)) (hY : Real.log (proxyCutoff x) ≤ Real.log x)
    (hγ2 : 1 / γ ^ 2 ≤ u) :
    (r + 2 : ℝ) * bound5 q K CN c E₂ κ M x γ cW SP c₃ K' r ≤
      2 * κ * M 0 * CW * (6 * CW + 4 / c₃) * x * Real.log x ^ (-1 : ℝ) *
        Real.log x ^ (-(1 / 10) : ℝ) * u ^ 6 := by
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hκ0 : 0 < κ := by linarith
  have hu0 : 0 ≤ u := by linarith
  set e := L ^ (-(1 / 10) : ℝ) with he
  have he0 : 0 < e := by positivity
  have hLinv : L ^ (-1 : ℝ) = L⁻¹ := Real.rpow_neg_one L
  -- the strip term
  have hstrip : 2 * cW * K' ≤ 6 * CW * u * e := by
    have h1 : L ^ (9 / 10 : ℝ) / L = e := by
      rw [he, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hL0]; norm_num
    calc 2 * cW * K' ≤ 2 * (CW * u / L) * (3 * L ^ (9 / 10 : ℝ)) := by gcongr
      _ = 6 * CW * u * (L ^ (9 / 10 : ℝ) / L) := by ring
      _ = 6 * CW * u * e := by rw [h1]
  -- the candidate-logarithm term
  have hlogt : 2 * SP * highProd x ⌊κ * x + 1⌋₊ 1 * (Real.log (proxyCutoff x) / c₃) /
      (γ ^ 2 * L ^ (19 / 10 : ℝ)) ≤ 4 / c₃ * u ^ 2 * e := by
    have hL19 : 0 < L ^ (19 / 10 : ℝ) := by positivity
    have h1 : L ^ (45 / 100 : ℝ) * L / L ^ (19 / 10 : ℝ) ≤ e := by
      rw [← Real.rpow_add_one hL0.ne', ← Real.rpow_sub hL0, he]
      exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    calc 2 * SP * highProd x ⌊κ * x + 1⌋₊ 1 * (Real.log (proxyCutoff x) / c₃) /
          (γ ^ 2 * L ^ (19 / 10 : ℝ))
        = 2 * SP * highProd x ⌊κ * x + 1⌋₊ 1 * (Real.log (proxyCutoff x) / c₃) *
            (1 / γ ^ 2) / L ^ (19 / 10 : ℝ) := by
          field_simp
      _ ≤ 2 * (2 * L ^ (45 / 100 : ℝ)) * u * (L / c₃) * u / L ^ (19 / 10 : ℝ) := by
          gcongr
      _ = 4 / c₃ * u ^ 2 * (L ^ (45 / 100 : ℝ) * L / L ^ (19 / 10 : ℝ)) := by ring
      _ ≤ 4 / c₃ * u ^ 2 * e := by gcongr
  have hbr : 2 * cW * K' + 2 * SP * highProd x ⌊κ * x + 1⌋₊ 1 *
      (Real.log (proxyCutoff x) / c₃) / (γ ^ 2 * L ^ (19 / 10 : ℝ)) ≤
      (6 * CW + 4 / c₃) * u ^ 2 * e := by
    have : 6 * CW * u * e ≤ 6 * CW * u ^ 2 * e := by
      have : u ≤ u ^ 2 := by nlinarith
      gcongr
    nlinarith
  have hbr0 : 0 ≤ 2 * cW * K' + 2 * SP * highProd x ⌊κ * x + 1⌋₊ 1 *
      (Real.log (proxyCutoff x) / c₃) / (γ ^ 2 * L ^ (19 / 10 : ℝ)) := by positivity
  unfold bound5
  have hcWN : cW * ⌊κ * x + 1⌋₊ ≤ CW * u / L * (2 * κ * x) := by gcongr
  calc (r + 2 : ℝ) * (M 0 * endBound q K CN c E₂ x * cW * ⌊κ * x + 1⌋₊ *
        highProd x ⌊κ * x + 1⌋₊ 1 ^ r * (2 * cW * K' + 2 * SP * highProd x ⌊κ * x + 1⌋₊ 1 *
          (Real.log (proxyCutoff x) / c₃) / (γ ^ 2 * L ^ (19 / 10 : ℝ))))
      = (r + 2 : ℝ) * (M 0 * endBound q K CN c E₂ x * (cW * ⌊κ * x + 1⌋₊) *
          highProd x ⌊κ * x + 1⌋₊ 1 ^ r * (2 * cW * K' + 2 * SP * highProd x ⌊κ * x + 1⌋₊ 1 *
            (Real.log (proxyCutoff x) / c₃) / (γ ^ 2 * L ^ (19 / 10 : ℝ)))) := by ring
    _ ≤ u * (M 0 * u * (CW * u / L * (2 * κ * x)) * u * ((6 * CW + 4 / c₃) * u ^ 2 * e)) := by
        gcongr
    _ = 2 * κ * M 0 * CW * (6 * CW + 4 / c₃) * x * L⁻¹ * e * u ^ 6 := by
        field_simp
    _ = _ := by rw [hLinv]

/-- Combining the two bounds with `u = L^{1/200}`. -/
theorem combine_le {x C₄ C₅ : ℝ} (hL : 1 ≤ Real.log x) (hx : 0 < x) (hC₄ : 0 ≤ C₄)
    (hC₅ : 0 ≤ C₅) :
    C₄ * x * Real.log x ^ (-3 : ℝ) * (Real.log x ^ (1 / 200 : ℝ)) ^ 4 +
        C₅ * x * Real.log x ^ (-1 : ℝ) * Real.log x ^ (-(1 / 10) : ℝ) *
          (Real.log x ^ (1 / 200 : ℝ)) ^ 6 ≤
      (C₄ + C₅) * (x / Real.log x) * Real.log x ^ (-(1 / 20) : ℝ) := by
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hu4 : (L ^ (1 / 200 : ℝ)) ^ 4 = L ^ (4 / 200 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hu6 : (L ^ (1 / 200 : ℝ)) ^ 6 = L ^ (6 / 200 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hdiv : x / L = x * L ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have h1 : L ^ (-3 : ℝ) * L ^ (4 / 200 : ℝ) ≤ L ^ (-1 : ℝ) * L ^ (-(1 / 20) : ℝ) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have h2 : L ^ (-1 : ℝ) * L ^ (-(1 / 10) : ℝ) * L ^ (6 / 200 : ℝ) ≤
      L ^ (-1 : ℝ) * L ^ (-(1 / 20) : ℝ) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  rw [hu4, hu6, hdiv]
  have e1 : C₄ * x * L ^ (-3 : ℝ) * L ^ (4 / 200 : ℝ) =
      C₄ * x * (L ^ (-3 : ℝ) * L ^ (4 / 200 : ℝ)) := by ring
  have e2 : C₅ * x * L ^ (-1 : ℝ) * L ^ (-(1 / 10) : ℝ) * L ^ (6 / 200 : ℝ) =
      C₅ * x * (L ^ (-1 : ℝ) * L ^ (-(1 / 10) : ℝ) * L ^ (6 / 200 : ℝ)) := by ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ C₄ * x by positivity)
  have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ C₅ * x by positivity)
  nlinarith

end Erdos408.TypeII
