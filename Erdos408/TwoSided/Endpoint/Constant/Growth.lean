import Erdos408.TwoSided.Endpoint.Constant.High

/-!
# The constants of the constant part

The parameter bookkeeping of S19 (`blueprint/two_sided_correlation.md` §6.6, E10): with
`δ = L^{-D}`, `θ = L^{-A_s}`, `c = L^{B'}`, `H_max = L^{C_W + 1}` and `K_c = L^{d+3}`, the box
bound of `integral_boxSum_le` is a sum of powers of `L` and of the absolute savings
`x^{-1/100}`, `J_B x^{-1/150}`; times the `I⁴ ≤ 256 L^{4 + 4D}` boxes it is `O(L^{-A₀})` once
the exponents are chosen as in `exists_integral_const_high_le`.
-/

namespace Erdos408.TwoSided.ConstHigh

open Filter

/-- `L^a L^b ≤ L^e` for `L ≥ 1` and `a + b ≤ e`. -/
theorem rpow_mul_rpow_le {L a b e : ℝ} (hL : 1 ≤ L) (h : a + b ≤ e) : L ^ a * L ^ b ≤ L ^ e := by
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hL h

/-- `(L^a)² = L^{2a}`. -/
theorem rpow_sq_eq {L a : ℝ} (hL : 0 < L) : (L ^ a) ^ 2 = L ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  norm_num
  ring_nf

/-- The class bound in powers of `L`. -/
theorem classBound_le_rpow {x D As B' G Nexp C₈ CW Z CNN JB : ℝ} (hx : 1 ≤ x)
    (hL1 : 1 ≤ Real.log x) (hCNN : 0 ≤ CNN) (hJB : 0 ≤ JB)
    (hxC : x ^ (-(1 / 100 : ℝ)) ≤ Real.log x ^ (-G))
    (hxD : JB * x ^ (-(1 / 150 : ℝ)) ≤ Real.log x ^ (-G))
    (eA : -(2 * As) + 3 - D + 2 * CW ≤ -Z) (eB : -(2 * D) + 2 * C₈ - B' ≤ -Z)
    (eC : -(2 * D) + 2 * C₈ - G ≤ -Z) (eE : -(2 * D) + 1 - Nexp ≤ -Z) :
    classBound x (Real.log x ^ (-D)) (Real.log x ^ (-As)) (Real.log x ^ B') C₈ CNN Nexp JB
        (Real.log x ^ (CW + 1)) ≤
      (195 + 18 * (2304 + 629 + 65 * CNN)) * Real.log x ^ (-Z) := by
  set L := Real.log x with hL
  have hL0 : 0 < L := by linarith
  have hLZ : 0 ≤ L ^ (-Z) := Real.rpow_nonneg hL0.le _
  have hx0 : 0 < x := by linarith
  -- the ordinary times
  have h1 : (L ^ (-As)) ^ 2 * ((17 + 48 * L) * (3 * L ^ (-D) * (L ^ (CW + 1)) ^ 2)) ≤
      195 * L ^ (-Z) := by
    have h65 : 17 + 48 * L ≤ 65 * L := by linarith
    calc (L ^ (-As)) ^ 2 * ((17 + 48 * L) * (3 * L ^ (-D) * (L ^ (CW + 1)) ^ 2))
        ≤ (L ^ (-As)) ^ 2 * ((65 * L) * (3 * L ^ (-D) * (L ^ (CW + 1)) ^ 2)) := by gcongr
      _ = 195 * (L ^ (2 * -As) * L ^ (1 : ℝ) * L ^ (-D) * L ^ (2 * (CW + 1))) := by
          rw [rpow_sq_eq hL0, rpow_sq_eq hL0, Real.rpow_one]
          ring
      _ ≤ 195 * L ^ (-Z) := by
          gcongr
          simp only [← Real.rpow_add hL0]
          exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  -- the medium range, the high range and the model error
  have hδ2 : 2 * (3 * L ^ (-D)) ^ 2 = 18 * L ^ (-(2 * D)) := by
    rw [mul_pow, rpow_sq_eq hL0]
    ring_nf
  have hX : (x ^ (-(1 / 150 : ℝ))) ^ 2 * x ^ (1 / 300 : ℝ) = x ^ (-(1 / 100 : ℝ)) := by
    rw [rpow_sq_eq hx0, ← Real.rpow_add hx0]
    norm_num
  have hε : 24 / x ^ (1 / 300 : ℝ) + x ^ (-(1 / 150 : ℝ)) ≤ 25 * x ^ (-(1 / 300 : ℝ)) := by
    rw [Real.rpow_neg hx0.le (1 / 300), div_eq_mul_inv]
    have : x ^ (-(1 / 150 : ℝ)) ≤ x ^ (-(1 / 300 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    rw [Real.rpow_neg hx0.le (1 / 300)] at this
    linarith
  have hε2 : (24 / x ^ (1 / 300 : ℝ) + x ^ (-(1 / 150 : ℝ))) ^ 2 ≤ 625 * x ^ (-(1 / 150 : ℝ)) := by
    have h0 : 0 ≤ 24 / x ^ (1 / 300 : ℝ) + x ^ (-(1 / 150 : ℝ)) := by positivity
    calc (24 / x ^ (1 / 300 : ℝ) + x ^ (-(1 / 150 : ℝ))) ^ 2 ≤ (25 * x ^ (-(1 / 300 : ℝ))) ^ 2 :=
          pow_le_pow_left₀ h0 hε 2
      _ = 625 * x ^ (-(1 / 150 : ℝ)) := by rw [mul_pow, rpow_sq_eq hx0]; norm_num
  have hB : (L ^ C₈) ^ 2 * (2304 / L ^ B' + 4 * (x ^ (-(1 / 150 : ℝ))) ^ 2 * x ^ (1 / 300 : ℝ))
      ≤ 2304 * L ^ (2 * C₈ - B') + 4 * L ^ (2 * C₈ - G) := by
    rw [mul_assoc 4, hX, rpow_sq_eq hL0, div_eq_mul_inv, ← Real.rpow_neg hL0.le, mul_add]
    have e1 : L ^ (2 * C₈) * (2304 * L ^ (-B')) = 2304 * L ^ (2 * C₈ - B') := by
      rw [sub_eq_add_neg, Real.rpow_add hL0]
      ring
    have e2 : L ^ (2 * C₈) * (4 * x ^ (-(1 / 100 : ℝ))) ≤ 4 * L ^ (2 * C₈ - G) := by
      rw [sub_eq_add_neg, Real.rpow_add hL0]
      have := mul_le_mul_of_nonneg_left hxC (Real.rpow_nonneg hL0.le (2 * C₈))
      linarith
    linarith
  have hD : JB * (L ^ C₈ * (24 / x ^ (1 / 300 : ℝ) + x ^ (-(1 / 150 : ℝ)))) ^ 2 ≤
      625 * L ^ (2 * C₈ - G) := by
    rw [mul_pow, rpow_sq_eq hL0, sub_eq_add_neg, Real.rpow_add hL0]
    have hC8 : 0 ≤ L ^ (2 * C₈) := Real.rpow_nonneg hL0.le _
    calc JB * (L ^ (2 * C₈) * (24 / x ^ (1 / 300 : ℝ) + x ^ (-(1 / 150 : ℝ))) ^ 2)
        ≤ JB * (L ^ (2 * C₈) * (625 * x ^ (-(1 / 150 : ℝ)))) := by gcongr
      _ = 625 * L ^ (2 * C₈) * (JB * x ^ (-(1 / 150 : ℝ))) := by ring
      _ ≤ 625 * L ^ (2 * C₈) * L ^ (-G) := by gcongr
      _ = 625 * (L ^ (2 * C₈) * L ^ (-G)) := by ring
  have hE : (17 + 48 * L) * (CNN * L ^ (-Nexp)) ≤ 65 * CNN * L ^ (1 - Nexp) := by
    have h65 : 17 + 48 * L ≤ 65 * L := by linarith
    have hN0 : 0 ≤ CNN * L ^ (-Nexp) := mul_nonneg hCNN (Real.rpow_nonneg hL0.le _)
    calc (17 + 48 * L) * (CNN * L ^ (-Nexp)) ≤ 65 * L * (CNN * L ^ (-Nexp)) := by gcongr
      _ = 65 * CNN * (L ^ (1 : ℝ) * L ^ (-Nexp)) := by rw [Real.rpow_one]; ring
      _ = 65 * CNN * L ^ (1 - Nexp) := by rw [← Real.rpow_add hL0]; ring_nf
  have hsum : 2 * (3 * L ^ (-D)) ^ 2 *
      ((L ^ C₈) ^ 2 * (2304 / L ^ B' + 4 * (x ^ (-(1 / 150 : ℝ))) ^ 2 * x ^ (1 / 300 : ℝ)) +
        JB * (L ^ C₈ * (24 / x ^ (1 / 300 : ℝ) + x ^ (-(1 / 150 : ℝ)))) ^ 2 +
        (17 + 48 * L) * (CNN * L ^ (-Nexp))) ≤
      18 * (2304 + 629 + 65 * CNN) * L ^ (-Z) := by
    rw [hδ2]
    have hD2 : 0 ≤ 18 * L ^ (-(2 * D)) := by positivity
    have hle := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hB hD) hE) hD2
    refine hle.trans ?_
    have p1 : L ^ (-(2 * D)) * L ^ (2 * C₈ - B') ≤ L ^ (-Z) := rpow_mul_rpow_le hL1 (by linarith)
    have p2 : L ^ (-(2 * D)) * L ^ (2 * C₈ - G) ≤ L ^ (-Z) := rpow_mul_rpow_le hL1 (by linarith)
    have p3 : L ^ (-(2 * D)) * L ^ (1 - Nexp) ≤ L ^ (-Z) := rpow_mul_rpow_le hL1 (by linarith)
    have q3 := mul_le_mul_of_nonneg_left p3 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18 * 65) hCNN)
    nlinarith
  rw [classBound]
  linarith

/-- `(L^a)^n = L^{na}`. -/
theorem rpow_pow_eq {L a : ℝ} (hL : 0 < L) (n : ℕ) : (L ^ a) ^ n = L ^ (n * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le, mul_comm]

/-- The corner-error bound in powers of `L`. -/
theorem errBound_le_rpow {x D CW d' M₁ E : ℝ} (hL1 : 1 ≤ Real.log x)
    (e : -(5 * D) + 2 * d' + 2 * (CW + 1) + 1 ≤ -E) :
    errBound x (Real.log x ^ (-D)) (Real.log x ^ d') M₁ (Real.log x ^ (CW + 1)) ≤
      3888 * 258 * M₁ ^ 2 * Real.log x ^ (-E) := by
  set L := Real.log x with hL
  have hL0 : 0 < L := by linarith
  rw [errBound, rpow_pow_eq hL0, rpow_sq_eq hL0, rpow_sq_eq hL0]
  have h1 : 66 + 192 * L ≤ 258 * L ^ (1 : ℝ) := by rw [Real.rpow_one]; linarith
  have hM : 0 ≤ M₁ ^ 2 := sq_nonneg _
  have h2 : L ^ ((5 : ℕ) * -D) * L ^ (2 * d') * L ^ (2 * (CW + 1)) * L ^ (1 : ℝ) ≤ L ^ (-E) := by
    simp only [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by push_cast; linarith)
  calc 3888 * L ^ ((5 : ℕ) * -D) * L ^ (2 * d') * M₁ ^ 2 * L ^ (2 * (CW + 1)) * (66 + 192 * L)
      ≤ 3888 * L ^ ((5 : ℕ) * -D) * L ^ (2 * d') * M₁ ^ 2 * L ^ (2 * (CW + 1)) *
          (258 * L ^ (1 : ℝ)) := by gcongr
    _ = 3888 * 258 * M₁ ^ 2 *
          (L ^ ((5 : ℕ) * -D) * L ^ (2 * d') * L ^ (2 * (CW + 1)) * L ^ (1 : ℝ)) := by ring
    _ ≤ 3888 * 258 * M₁ ^ 2 * L ^ (-E) := by gcongr

/-- **The total bound.** With `I ≤ 4L^{1+D}` boxes, `k ≤ L^{C_m}`, the class bound at most
`c₁ L^{-Z}` for `Z = A₀ + 4 + 4D + 2d' + 2C_m` and the corner error at most
`c₂ L^{-(A₀ + 4 + 4D)}`, the sum over the boxes is at most
`256 (8M₀² c₁ + 2c₂) L^{-A₀}`. -/
theorem total_le_rpow {x D As B' C₈ CNN Nexp JB CW d' M₀ M₁ Cm A₀ c₁ c₂ : ℝ} {I k : ℕ}
    (hx : 1 ≤ x) (hL1 : 1 ≤ Real.log x) (hδ : 0 ≤ Real.log x ^ (-D)) (hc : 0 < Real.log x ^ B')
    (hCNN : 0 ≤ CNN) (hJB : 0 ≤ JB) (hI : (I : ℝ) ≤ 4 * Real.log x ^ (1 + D))
    (hk : (k : ℝ) ≤ Real.log x ^ Cm)
    (hcls : classBound x (Real.log x ^ (-D)) (Real.log x ^ (-As)) (Real.log x ^ B') C₈ CNN Nexp
      JB (Real.log x ^ (CW + 1)) ≤ c₁ * Real.log x ^ (-(A₀ + 4 + 4 * D + 2 * d' + 2 * Cm)))
    (herr : errBound x (Real.log x ^ (-D)) (Real.log x ^ d') M₁ (Real.log x ^ (CW + 1)) ≤
      c₂ * Real.log x ^ (-(A₀ + 4 + 4 * D))) :
    (I : ℝ) ^ 2 * ((I : ℝ) ^ 2 * boxBound x (Real.log x ^ (-D)) (Real.log x ^ (-As))
        (Real.log x ^ B') C₈ CNN Nexp JB (Real.log x ^ (CW + 1)) (Real.log x ^ d') M₀ M₁ k) ≤
      256 * (8 * M₀ ^ 2 * c₁ + 2 * c₂) * Real.log x ^ (-A₀) := by
  set L := Real.log x with hL
  have hL0 : 0 < L := by linarith
  have hcB := classBound_nonneg (θ := L ^ (-As)) (C₈ := C₈) (Nexp := Nexp) (Hc := L ^ (CW + 1))
    hx hδ hc hCNN hJB
  have hc₁ : 0 ≤ c₁ * L ^ (-(A₀ + 4 + 4 * D + 2 * d' + 2 * Cm)) := hcB.trans hcls
  have hc₂ : 0 ≤ c₂ * L ^ (-(A₀ + 4 + 4 * D)) :=
    (errBound_nonneg hx (Real.rpow_nonneg hL0.le _)).trans herr
  have hc₁' : 0 ≤ c₁ := nonneg_of_mul_nonneg_left hc₁ (Real.rpow_pos_of_pos hL0 _)
  have hc₂' : 0 ≤ c₂ := nonneg_of_mul_nonneg_left hc₂ (Real.rpow_pos_of_pos hL0 _)
  -- the box bound
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkk : (k : ℝ) * (k * classBound x (L ^ (-D)) (L ^ (-As)) (L ^ B') C₈ CNN Nexp JB
      (L ^ (CW + 1))) ≤ L ^ Cm * (L ^ Cm * (c₁ * L ^ (-(A₀ + 4 + 4 * D + 2 * d' + 2 * Cm)))) := by
    gcongr
  have hW : (2 * L ^ d' * M₀) ^ 2 = 4 * M₀ ^ 2 * L ^ (2 * d') := by
    rw [mul_pow, mul_pow, rpow_sq_eq hL0]
    ring
  have hpow : L ^ (2 * d') * (L ^ Cm * (L ^ Cm * L ^ (-(A₀ + 4 + 4 * D + 2 * d' + 2 * Cm)))) =
      L ^ (-(A₀ + 4 + 4 * D)) := by
    simp only [← Real.rpow_add hL0]
    congr 1
    ring
  have hbox : boxBound x (L ^ (-D)) (L ^ (-As)) (L ^ B') C₈ CNN Nexp JB (L ^ (CW + 1))
      (L ^ d') M₀ M₁ k ≤ (8 * M₀ ^ 2 * c₁ + 2 * c₂) * L ^ (-(A₀ + 4 + 4 * D)) := by
    rw [boxBound, hW]
    have hM : 0 ≤ 4 * M₀ ^ 2 * L ^ (2 * d') := by positivity
    have h1 := mul_le_mul_of_nonneg_left hkk hM
    have h2 : 4 * M₀ ^ 2 * L ^ (2 * d') * (L ^ Cm * (L ^ Cm *
        (c₁ * L ^ (-(A₀ + 4 + 4 * D + 2 * d' + 2 * Cm))))) =
        4 * M₀ ^ 2 * c₁ * L ^ (-(A₀ + 4 + 4 * D)) := by
      rw [← hpow]
      ring
    nlinarith
  have hI2 : (I : ℝ) ^ 2 * (I : ℝ) ^ 2 ≤ 256 * L ^ (4 + 4 * D) := by
    have hI0 : (0 : ℝ) ≤ I := Nat.cast_nonneg I
    have h4 : (I : ℝ) ^ 2 * (I : ℝ) ^ 2 = (I : ℝ) ^ 4 := by ring
    rw [h4]
    calc (I : ℝ) ^ 4 ≤ (4 * L ^ (1 + D)) ^ 4 := pow_le_pow_left₀ hI0 hI 4
      _ = 256 * L ^ (4 + 4 * D) := by
          rw [mul_pow, rpow_pow_eq hL0]
          push_cast
          ring_nf
  have hbB : 0 ≤ (8 * M₀ ^ 2 * c₁ + 2 * c₂) * L ^ (-(A₀ + 4 + 4 * D)) := by positivity
  calc (I : ℝ) ^ 2 * ((I : ℝ) ^ 2 * boxBound x (L ^ (-D)) (L ^ (-As)) (L ^ B') C₈ CNN Nexp JB
        (L ^ (CW + 1)) (L ^ d') M₀ M₁ k)
      ≤ (I : ℝ) ^ 2 * (I : ℝ) ^ 2 * ((8 * M₀ ^ 2 * c₁ + 2 * c₂) * L ^ (-(A₀ + 4 + 4 * D))) := by
        rw [← mul_assoc]
        gcongr
    _ ≤ 256 * L ^ (4 + 4 * D) * ((8 * M₀ ^ 2 * c₁ + 2 * c₂) * L ^ (-(A₀ + 4 + 4 * D))) := by
        gcongr
    _ = 256 * (8 * M₀ ^ 2 * c₁ + 2 * c₂) * (L ^ (4 + 4 * D) * L ^ (-(A₀ + 4 + 4 * D))) := by
        ring
    _ = 256 * (8 * M₀ ^ 2 * c₁ + 2 * c₂) * L ^ (-A₀) := by
        rw [← Real.rpow_add hL0]
        congr 2
        ring

/-- The growth facts in `L` alone used by S19. -/
theorem eventually_constGrowth_log (Cm D G K : ℝ) (hK : 0 ≤ K) : ∀ᶠ L : ℝ in atTop,
    4 ≤ L ∧ K * (L ^ (0.36 : ℝ) + L ^ (0.73 : ℝ) * Real.log L) + G * Real.log L ≤ L / 150 ∧
      (Cm + 2) * Real.log L + L ^ (0.36 : ℝ) ≤ L ^ (0.38 : ℝ) ∧
      L ^ (0.47 : ℝ) + Real.log 16 ≤ L ∧ D * Real.log L + Real.log 2 ≤ L ^ (0.27 : ℝ) := by
  have hK1 : 0 < K + 1 := by linarith
  filter_upwards [eventually_ge_atTop 4,
    IntegerKernel.eventually_rpow_le_mul_rpow (a := 0.36) (b := 1) (by norm_num)
      (ε := 1 / (600 * (K + 1))) (by positivity),
    IntegerKernel.eventually_log_le_mul_rpow (b := 0.01) (by norm_num) (ε := 1) one_pos,
    IntegerKernel.eventually_rpow_le_mul_rpow (a := 0.74) (b := 1) (by norm_num)
      (ε := 1 / (600 * (K + 1))) (by positivity),
    IntegerKernel.eventually_log_le_mul_rpow (b := 1) one_pos (ε := 1 / (600 * (|G| + 1)))
      (by positivity),
    IntegerKernel.eventually_log_le_mul_rpow (b := 0.38) (by norm_num)
      (ε := 1 / (2 * (|Cm + 2| + 1))) (by positivity),
    IntegerKernel.eventually_rpow_le_mul_rpow (a := 0.36) (b := 0.38) (by norm_num)
      (ε := 1 / 2) (by norm_num),
    IntegerKernel.eventually_rpow_le_mul_rpow (a := 0.47) (b := 1) (by norm_num)
      (ε := 1 / 2) (by norm_num),
    IntegerKernel.eventually_const_le_mul_rpow (Real.log 16) (b := 1) one_pos (ε := 1 / 2)
      (by norm_num),
    IntegerKernel.eventually_log_le_mul_rpow (b := 0.27) (by norm_num)
      (ε := 1 / (2 * (|D| + 1))) (by positivity),
    IntegerKernel.eventually_const_le_mul_rpow (Real.log 2) (b := 0.27) (by norm_num)
      (ε := 1 / 2) (by norm_num)]
    with L hL4 h36 hlog1 h74 hlogG hlog38 h3638 h47 h16 hlog27 h2
  rw [Real.rpow_one] at h36 h74 hlogG h47 h16
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  -- `x ≤ ε' y` with `ε' = c/(c' (|a| + 1))` gives `|a| x ≤ y/c'`
  have absorb : ∀ (a y z c' : ℝ), 0 < c' → 0 ≤ y → z ≤ 1 / (c' * (|a| + 1)) * y →
      |a| * z ≤ y / c' := by
    intro a y z c' hc' hy hz
    have h1 : |a| * z ≤ |a| * (1 / (c' * (|a| + 1)) * y) :=
      mul_le_mul_of_nonneg_left hz (abs_nonneg a)
    have h2 : |a| * (1 / (c' * (|a| + 1)) * y) ≤ y / c' := by
      rw [show |a| * (1 / (c' * (|a| + 1)) * y) = |a| / (|a| + 1) * (y / c') by
        field_simp]
      exact mul_le_of_le_one_left (by positivity)
        ((div_le_one (by positivity)).2 (by linarith))
    linarith
  have hKabs : |K| = K := abs_of_nonneg hK
  refine ⟨hL4, ?_, ?_, ?_, ?_⟩
  · have e1 : K * L ^ (0.36 : ℝ) ≤ L / 600 := by
      have := absorb K L (L ^ (0.36 : ℝ)) 600 (by norm_num) hL0.le
        (by rw [hKabs]; exact h36)
      rwa [hKabs] at this
    have e2 : K * (L ^ (0.73 : ℝ) * Real.log L) ≤ L / 600 := by
      have h73 : L ^ (0.73 : ℝ) * Real.log L ≤ L ^ (0.74 : ℝ) := by
        calc L ^ (0.73 : ℝ) * Real.log L ≤ L ^ (0.73 : ℝ) * (1 * L ^ (0.01 : ℝ)) :=
              mul_le_mul_of_nonneg_left hlog1 (Real.rpow_nonneg hL0.le _)
          _ = L ^ (0.74 : ℝ) := by
              rw [one_mul, ← Real.rpow_add hL0]
              norm_num
      have := absorb K L (L ^ (0.73 : ℝ) * Real.log L) 600 (by norm_num) hL0.le
        (by rw [hKabs]; exact h73.trans h74)
      rwa [hKabs] at this
    have e3 : G * Real.log L ≤ L / 600 := by
      have := absorb G L (Real.log L) 600 (by norm_num) hL0.le hlogG
      exact (mul_le_mul_of_nonneg_right (le_abs_self G) hlog0).trans this
    nlinarith
  · have e1 : (Cm + 2) * Real.log L ≤ L ^ (0.38 : ℝ) / 2 := by
      have := absorb (Cm + 2) (L ^ (0.38 : ℝ)) (Real.log L) 2 (by norm_num)
        (Real.rpow_nonneg hL0.le _) hlog38
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0).trans this
    linarith
  · linarith
  · have e1 : D * Real.log L ≤ L ^ (0.27 : ℝ) / 2 := by
      have := absorb D (L ^ (0.27 : ℝ)) (Real.log L) 2 (by norm_num)
        (Real.rpow_nonneg hL0.le _) hlog27
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0).trans this
    linarith

/-- The growth facts in `x` used by S19, with `L = log x`. -/
theorem eventually_constScales (Cm D G K B' : ℝ) (hK : 0 ≤ K) : ∀ᶠ x : ℝ in atTop,
    2 ≤ x ∧ 4 ≤ Real.log x ∧ x ^ (-(1 / 100 : ℝ)) ≤ Real.log x ^ (-G) ∧
      Real.exp (K * (Real.log x ^ (0.36 : ℝ) + Real.log x ^ (0.73 : ℝ) *
        Real.log (Real.log x))) * x ^ (-(1 / 150 : ℝ)) ≤ Real.log x ^ (-G) ∧
      Real.log x ^ (Cm + 2) * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤
        Real.exp (Real.log x ^ (0.38 : ℝ)) ∧
      16 * Real.exp (Real.log x ^ (0.47 : ℝ)) ≤ x ∧
      2 * Real.log x ^ D ≤ Real.exp (Real.log x ^ (0.27 : ℝ)) ∧
      4 * Real.log x ^ D ≤ x ∧ Real.log x ^ B' ≤ x * Real.log x ^ (Cm + 2) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_constGrowth_log Cm D G K hK),
    eventually_ge_atTop 2, (isLittleO_log_rpow_rpow_atTop G (by norm_num : (0 : ℝ) < 1 / 100)).bound
      one_pos, eventually_log_rpow_le_self (D + 1), eventually_log_rpow_le_self (B' - Cm - 2)]
    with x hg hx2 hG hD1 hB
  obtain ⟨hL4, hJ, h38, h47, h27⟩ := hg
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hL
  have hL0 : 0 < L := by linarith
  have hexp : Real.exp L = x := Real.exp_log hx0
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _), Real.norm_of_nonneg
    (Real.rpow_nonneg hx0.le _), one_mul] at hG
  refine ⟨hx2, hL4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.rpow_neg hx0.le, Real.rpow_neg hL0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hL0 _) hG
  · rw [Real.rpow_def_of_pos hx0 (-(1 / 150 : ℝ)), Real.rpow_def_of_pos hL0 (-G),
      ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [Real.rpow_def_of_pos hL0 (Cm + 2), ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  · calc 16 * Real.exp (L ^ (0.47 : ℝ)) = Real.exp (Real.log 16 + L ^ (0.47 : ℝ)) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ Real.exp L := Real.exp_le_exp.2 (by linarith)
      _ = x := hexp
  · rw [Real.rpow_def_of_pos hL0 D, show (2 : ℝ) = Real.exp (Real.log 2) by
      rw [Real.exp_log (by norm_num)], ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [Real.rpow_add hL0, Real.rpow_one] at hD1
    have : 0 ≤ L ^ D := Real.rpow_nonneg hL0.le _
    nlinarith
  · have : L ^ B' = L ^ (B' - Cm - 2) * L ^ (Cm + 2) := by
      rw [← Real.rpow_add hL0]
      ring_nf
    rw [this]
    exact mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hL0.le _)

/-- The scale facts of package E at `Y ∈ [x e^{L^{0.38}}, x e^{L^{0.47}}]` and
`T₀ = x L^{C_m + 2}`. -/
theorem time_scales {x Y Cm : ℝ} (hx2 : 2 ≤ x) (hL1 : 1 ≤ Real.log x)
    (h38 : Real.log x ^ (Cm + 2) * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤
      Real.exp (Real.log x ^ (0.38 : ℝ)))
    (h47 : 16 * Real.exp (Real.log x ^ (0.47 : ℝ)) ≤ x)
    (hY₁ : x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ Y)
    (hY₂ : Y ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ))) :
    x * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Y ∧ 8 * Y ≤ x ^ 3 ∧ x ^ (1 / 2 : ℝ) ≤ Y ∧
      Y ≤ x ^ 2 ∧ x * Real.log x ^ (Cm + 2) * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Y ∧
      0 ≤ x * Real.log x ^ (Cm + 2) ∧ x * Real.log x ^ (Cm + 2) ≤ Y ∧ 2 * Y + 1 ≤ x ^ 3 := by
  set L := Real.log x with hL
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := by linarith
  have hE36 : Real.exp (L ^ (0.36 : ℝ)) ≤ Real.exp (L ^ (0.38 : ℝ)) :=
    Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have h1E : 1 ≤ Real.exp (L ^ (0.36 : ℝ)) := Real.one_le_exp (by positivity)
  have hYx : x * Real.exp (L ^ (0.36 : ℝ)) ≤ Y := (mul_le_mul_of_nonneg_left hE36 hx0.le).trans hY₁
  have hxY : x ≤ Y := (le_mul_of_one_le_right hx0.le h1E).trans hYx
  have h16 : 16 * Y ≤ x ^ 2 := by
    calc 16 * Y ≤ x * (16 * Real.exp (L ^ (0.47 : ℝ))) := by linarith
      _ ≤ x * x := mul_le_mul_of_nonneg_left h47 hx0.le
      _ = x ^ 2 := by ring
  have hx3 : 2 * x ^ 2 ≤ x ^ 3 := by
    have : 2 * x ^ 2 ≤ x * x ^ 2 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
    linarith [show x * x ^ 2 = x ^ 3 by ring]
  have hx21 : 4 ≤ x ^ 2 := by nlinarith
  have hLC : 0 ≤ L ^ (Cm + 2) := Real.rpow_nonneg hL0.le _
  have hT : x * L ^ (Cm + 2) * Real.exp (L ^ (0.36 : ℝ)) ≤ Y := by
    calc x * L ^ (Cm + 2) * Real.exp (L ^ (0.36 : ℝ)) =
          x * (L ^ (Cm + 2) * Real.exp (L ^ (0.36 : ℝ))) := by ring
      _ ≤ x * Real.exp (L ^ (0.38 : ℝ)) := mul_le_mul_of_nonneg_left h38 hx0.le
      _ ≤ Y := hY₁
  have hT0 : 0 ≤ x * L ^ (Cm + 2) := mul_nonneg hx0.le hLC
  refine ⟨hYx, by linarith, ?_, by linarith, hT, hT0,
    (le_mul_of_one_le_right hT0 h1E).trans hT, by linarith⟩
  have : x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith)
    (by norm_num)
  rw [Real.rpow_one] at this
  linarith

/-- The grid step `δ = L^{-D}`: `δ ≤ 1/2`, `δ e^{L^{0.27}}/2 ≥ 1` and `δ x ≥ 4`. -/
theorem grid_scales {x D : ℝ} (hL4 : 4 ≤ Real.log x) (hD : 1 ≤ D)
    (h27 : 2 * Real.log x ^ D ≤ Real.exp (Real.log x ^ (0.27 : ℝ)))
    (h4D : 4 * Real.log x ^ D ≤ x) :
    0 < Real.log x ^ (-D) ∧ Real.log x ^ (-D) ≤ 1 / 2 ∧
      1 ≤ Real.log x ^ (-D) * (Real.exp (Real.log x ^ (0.27 : ℝ)) / 2) ∧
      4 ≤ Real.log x ^ (-D) * x := by
  set L := Real.log x with hL
  have hL0 : 0 < L := by linarith
  have hLD : 0 < L ^ D := Real.rpow_pos_of_pos hL0 D
  have hδdef : L ^ (-D) = (L ^ D)⁻¹ := Real.rpow_neg hL0.le D
  refine ⟨Real.rpow_pos_of_pos hL0 _, ?_, ?_, ?_⟩
  · rw [hδdef]
    have : L ≤ L ^ D := by
      calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
        _ ≤ L ^ D := Real.rpow_le_rpow_of_exponent_le (by linarith) hD
    rw [inv_le_comm₀ hLD (by norm_num)]
    linarith
  · rw [hδdef, ← div_eq_inv_mul, le_div_iff₀ hLD]
    linarith
  · rw [hδdef, ← div_eq_inv_mul, le_div_iff₀ hLD]
    linarith

/-- The grid of `I = ⌈3L^{1+D}⌉` steps `δ = L^{-D}` reaches `x³ - 1 ≥ 2Y`, and
`I ≤ 4L^{1+D}`. -/
theorem grid_reach {x Y D : ℝ} (hx0 : 0 < x) (hL1 : 1 ≤ Real.log x) (hD : 0 ≤ D)
    (hY : 2 * Y + 1 ≤ x ^ 3) :
    (⌈3 * Real.log x ^ (1 + D)⌉₊ : ℝ) ≤ 4 * Real.log x ^ (1 + D) ∧
      2 * Y ≤ grid (Real.log x ^ (-D)) ⌈3 * Real.log x ^ (1 + D)⌉₊ := by
  set L := Real.log x with hL
  have hL0 : 0 < L := by linarith
  set I := ⌈3 * L ^ (1 + D)⌉₊ with hIdef
  have hLD : 0 < L ^ D := Real.rpow_pos_of_pos hL0 D
  have hLD1 : L ^ (1 + D) = L * L ^ D := by rw [Real.rpow_add hL0, Real.rpow_one]
  refine ⟨?_, ?_⟩
  · have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 * L ^ (1 + D) by positivity)
    have h2 : 1 ≤ L ^ (1 + D) := Real.one_le_rpow hL1 (by linarith)
    rw [← hIdef] at h1
    linarith
  · have hIδ : 3 * L ≤ I * L ^ (-D) := by
      have h1 : 3 * L ^ (1 + D) ≤ I := Nat.le_ceil _
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos hL0 (-D)).le
      rw [hLD1, Real.rpow_neg hL0.le] at h2
      rw [Real.rpow_neg hL0.le]
      calc 3 * L = 3 * (L * L ^ D) * (L ^ D)⁻¹ := by field_simp
        _ ≤ I * (L ^ D)⁻¹ := h2
    have h3 : x ^ 3 ≤ Real.exp (I * L ^ (-D)) := by
      calc x ^ 3 = Real.exp L ^ 3 := by rw [Real.exp_log hx0]
        _ = Real.exp (3 * L) := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ Real.exp (I * L ^ (-D)) := Real.exp_le_exp.2 hIδ
    have h4 := Nat.lt_floor_add_one (Real.exp (I * L ^ (-D)))
    rw [grid]
    linarith

open scoped Classical in
/-- **S19 at fixed `x`, in powers of `L`.** `integral_twistedPoly_const_le` with
`δ = L^{-D}`, `θ = L^{-A_s}`, `c = L^{B'}`, `H_max = L^{C_W + 1}`, `K_c = L^{d'}` and
`I = ⌈3L^{1+D}⌉`, followed by `total_le_rpow`. -/
theorem integral_twistedPoly_const_le_rpow {x Y σ T₀ a b C₈ CNN Nexp JB D As B' G CW d' Cm A₀
    M₀ M₁ : ℝ} {h : ℤ} {k : ℕ} {Ps : Finset ℕ} {H A₀' : ℕ → ℂ} {κ : ℂ} {ψ : ℝ → ℂ}
    (hab : a ≤ b) (hc : 2 ≤ Real.log x ^ B')
    (hint : ∀ t ∈ Set.Icc a b, Real.log x ^ B' ≤ |t| ∧ |t| ≤ T₀) (hba : b - a ≤ T₀)
    (hσ : |σ| ≤ Real.log x ^ B' / 2) (hx2 : 2 ≤ x) (hL1 : 1 ≤ Real.log x)
    (hδ0 : 0 < Real.log x ^ (-D)) (hδ : Real.log x ^ (-D) ≤ 1 / 2) (hD : 0 ≤ D)
    (hψ : ∀ y, ψ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) (hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hM₀ : ∀ y, ‖ψ y‖ ≤ M₀) (hM₁ : ∀ y, ‖iteratedDeriv 1 ψ y‖ ≤ M₁)
    (hκ : ‖κ‖ ≤ Real.log x ^ d')
    (hPs : ∀ p ∈ Ps, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)))
    (hk : 1 ≤ k) (hkL : (k : ℝ) ≤ Real.log x ^ Cm) (hH : ∀ n, ‖H n‖ ≤ Real.log x ^ (CW + 1))
    (hY₁ : x * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Y) (hY₂ : 8 * Y ≤ x ^ 3)
    (hT₀ : T₀ * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Y)
    (hδx : 1 ≤ Real.log x ^ (-D) * (Real.exp (Real.log x ^ (0.27 : ℝ)) / 2))
    (hδx' : 4 ≤ Real.log x ^ (-D) * x)
    (hE10 : ∀ (R : ℝ) (β lo hi : ℕ) (u : ℝ), x ^ (99 / 100 : ℝ) ≤ R → R ≤ lo + 1 →
      (hi : ℝ) ≤ 2 * R → 1 ≤ |u| → |u| ≤ x ^ 3 →
      ‖(R : ℂ)⁻¹ * ∑ n ∈ (Finset.Ioc lo hi).filter (· ≡ β [MOD k]),
          (∑ d ∈ n.divisors, A₀' d) * (n : ℂ) ^ ((u : ℂ) * Complex.I)‖ ≤
        Real.log x ^ C₈ * (12 / |u| + x ^ (-(1 / 150 : ℝ))))
    (hmodel : ∀ R : ℝ, 1 ≤ R → ∑ n ∈ Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊,
      ‖H n - ∑ d ∈ n.divisors, A₀' d‖ ^ 2 ≤ CNN * R * Real.log x ^ (-Nexp))
    (hOrd : ∀ (s : Finset ℕ) (cs : ℕ → ℂ) (N : ℕ) (cq : ℕ → ℂ) {a b θ : ℝ}, a ≤ b →
      ∫ t in {t ∈ Set.Ioc a b | ‖∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ θ},
          ‖(∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)) *
            ∑ n ∈ Finset.Icc 1 N, cq n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
        θ ^ 2 * ((b - a + 8 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖cq n‖ ^ 2))
    (hJB : 0 ≤ JB)
    (hS16 : ∀ (P : ℝ) (s : Finset ℕ) (coeff : ℕ → ℂ),
      Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ P → P ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) →
      (∀ p ∈ s, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) → (∀ p ∈ s, ‖coeff p‖ ≤ 1) →
      (((Finset.Icc (-⌈T₀⌉ - 1) ⌈T₀⌉).filter fun j : ℤ =>
          ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ j + 1 ∧ |t| ≤ T₀ ∧
            Real.log x ^ (-As) <
              ‖(P : ℂ)⁻¹ * ∑ p ∈ s, coeff p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖).card : ℝ) ≤
        JB)
    (h2Y : 2 * Y + 1 ≤ x ^ 3) (hCNN : 0 ≤ CNN)
    (hxC : x ^ (-(1 / 100 : ℝ)) ≤ Real.log x ^ (-G))
    (hxD : JB * x ^ (-(1 / 150 : ℝ)) ≤ Real.log x ^ (-G))
    (eA : -(2 * As) + 3 - D + 2 * CW ≤ -(A₀ + 4 + 4 * D + 2 * d' + 2 * Cm))
    (eB : -(2 * D) + 2 * C₈ - B' ≤ -(A₀ + 4 + 4 * D + 2 * d' + 2 * Cm))
    (eC : -(2 * D) + 2 * C₈ - G ≤ -(A₀ + 4 + 4 * D + 2 * d' + 2 * Cm))
    (eE : -(2 * D) + 1 - Nexp ≤ -(A₀ + 4 + 4 * D + 2 * d' + 2 * Cm))
    (eF : -(5 * D) + 2 * d' + 2 * (CW + 1) + 1 ≤ -(A₀ + 4 + 4 * D)) :
    ∫ t in a..b, ‖twistedPoly Y (fun w => ψ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * κ *
        ∑ p ∈ Ps.filter (· ∣ w), H (w / p)) h k t‖ ^ 2 ≤
      256 * (8 * M₀ ^ 2 * (195 + 18 * (2304 + 629 + 65 * CNN)) +
        2 * (3888 * 258 * M₁ ^ 2)) * Real.log x ^ (-A₀) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hIle, hI⟩ := grid_reach (Y := Y) hx0 hL1 hD h2Y
  refine (integral_twistedPoly_const_le hab hc hint hba hσ (by linarith) hδ0 hδ hψ hψd hM₀ hM₁
    hκ hPs hk hH hY₁ hY₂ hT₀ hδx hδx' hE10 hmodel hOrd hJB hS16 hx2 hI).trans ?_
  exact total_le_rpow (by linarith) hL1 hδ0.le (by linarith) hCNN hJB hIle hkL
    (classBound_le_rpow (by linarith) hL1 hCNN hJB hxC hxD eA eB eC eE)
    (errBound_le_rpow hL1 eF)

end Erdos408.TwoSided.ConstHigh
