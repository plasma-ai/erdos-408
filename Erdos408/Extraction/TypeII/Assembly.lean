import Erdos408.Extraction.TypeII.Main

/-!
# Assembly of E4–E5

The counting input of E5 at one scale, and the bound `|Comp_j - Prox_j| ≤ C (x/L) L^{-1/20}`
from the facts that hold at every large `x`.
-/

namespace Erdos408.TypeII

open Finset Real Filter

/-- The count `∑_{m ≤ w} W(m) ≤ (A₁/c₃ + 1) w / (γ L)` at one scale. -/
theorem count_at {A₁ C₁r c₃ EM2 : ℝ} (hA₁ : 0 < A₁) (hc₃ : 0 < c₃)
    (hG : ∀ (x : ℝ) (j W : ℕ) (θ : ℝ), 1 ≤ Real.log x → 1 ≤ j → 2 ≤ proxyCutoff x →
      C₁r ≤ Real.log (proxyCutoff x) → 0 < θ →
      ∑ m ∈ Icc 1 W, dampedWeight x j m ≤
        A₁ * W / Real.log (proxyCutoff x) * ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ +
          (W : ℝ) ^ θ * ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-θ))⁻¹)
    (hEM2 : ∀ y z : ℝ, 2 ≤ y → y ≤ z →
      |∑ p ∈ primesIoc y z, (1 : ℝ) / p - Real.log (Real.log z / Real.log y)| ≤ EM2 / Real.log y)
    {x γ : ℝ} {j N : ℕ} (hsf : ScaleFacts x γ j N) (hL : 1 < Real.log x)
    (hL28 : 2 ≤ Real.log x ^ (28 / 100 : ℝ))
    (hPiY : c₃ / Real.log (proxyCutoff x) ≤ ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p))
    (hlogY : 0 < Real.log (proxyCutoff x)) (hC₁ : C₁r ≤ Real.log (proxyCutoff x))
    (hrank : 2 * Real.exp 1 * (Real.log (Real.log x ^ (45 / 100 : ℝ) / Real.log 2) +
        EM2 / Real.log 2 + 1 / 2) + Real.log (Real.log (proxyCutoff x) / c₃) ≤
      γ * Real.log x ^ (55 / 100 : ℝ)) :
    ∀ w : ℝ, 0 ≤ w → ∑ m ∈ Icc 1 N, (if (m : ℝ) ≤ w then proxyEnv x γ j m else 0) ≤
      (A₁ / c₃ + 1) / (γ * Real.log x) * w := by
  have hY2 : 2 ≤ proxyCutoff x := by
    have h1 : (1 : ℝ) ≤ Real.log x ^ (45 / 100 : ℝ) := Real.one_le_rpow hL.le (by norm_num)
    have := Real.add_one_le_exp (Real.log x ^ (45 / 100 : ℝ))
    linarith [hsf.cutoff_gt]
  set θ := 1 - Real.log x ^ (-(45 / 100) : ℝ) with hθ
  have hη : Real.log x ^ (-(45 / 100) : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hL (by norm_num)
  have hθ0 : 0 < θ := by linarith
  have hθ1 : θ ≤ 1 := by have : 0 ≤ Real.log x ^ (-(45 / 100) : ℝ) := by positivity
                         linarith
  have hS := sum_candidate_inv_le (x := x) hsf.log_ge hEM2
  have hsmall := rankin_small hsf.one_lt hsf.log_ge hL28 hc₃ hlogY hS hrank
  intro w hw
  exact sum_proxyEnv_count_le hsf.log_ge hsf.gamma_pos hsf.one_le_j hA₁ hc₃ hθ0 hlogY hPiY
    (fun W => hG x j W θ hsf.log_ge hsf.one_le_j hY2 hC₁ hθ0) hsmall N w hw

/-- The exponent of `endBound_le_exp`. -/
noncomputable def endExp (q : ℝ) (K : ℕ) (CN c E₂ : ℝ) : ℝ :=
  K * (Real.log 2 + Real.log (2 / (1 - q))) * (|CN| + 2) + 60 +
    |Real.log ((2 / c + 1) ^ 3 + (E₂ + 2) ^ 3)|

/-- The facts used at one large scale `x`. -/
structure LargeX (q : ℝ) (K : ℕ) (CN c Ch Cj κ CΦ C₂ c₃ C₁r E₂ L₀ EM1 EM2 : ℝ) (x : ℝ) :
    Prop where
  box : BoxBound q K c Ch Cj κ C₂ x
  x4 : 4 * κ + 4 ≤ x
  L16 : 16 ≤ Real.log x
  LL0 : L₀ ≤ Real.log x
  T50 : 50 ≤ logLog x
  s1 : 1 ≤ logLogLog x
  gamma_low : logLog x ^ (-21 : ℝ) ≤ presieveExponent c Ch x
  gamma_le : presieveExponent c Ch x ≤ 1
  lay : 2 * (|CN| * logLogLog x + 2) * K ≤ 4 / 100 * logLog x
  small : Real.exp (2 * Real.log x ^ (19 / 100 : ℝ)) ≤ x ^ (c / logLog x ^ 20)
  T21 : logLog x ^ (21 : ℝ) ≤ Real.log x ^ (72 / 100 : ℝ)
  T25 : logLog x ^ (25 : ℝ) ≤ Real.log x ^ (1 / 2 : ℝ)
  Tc : 1 / c₃ ≤ logLog x ^ (4 : ℕ)
  jY : 2 * ((|Cj| + 1) * (logLogLog x + 1)) + 4 ≤ Real.log x ^ (1 / 2 : ℝ)
  N2 : (⌊κ * x + 1⌋₊ : ℝ) + 1 ≤ x ^ 2
  L3 : Real.log x ^ 3 ≤ κ * x
  C1 : C₁r ≤ Real.log x / logLog x ^ 25
  EM2g : EM2 ≤ logLog x ^ (-21 : ℝ) * Real.log x
  EM2Y : EM2 ≤ Real.log x / logLog x ^ 25
  EM1L : EM1 ≤ Real.log x ^ (45 / 100 : ℝ)
  rank : 2 * Real.exp 1 * (Real.log (Real.log x ^ (45 / 100 : ℝ) / Real.log 2) +
      EM2 / Real.log 2 + 1 / 2) + Real.log (Real.log x / logLog x ^ 25 / c₃) ≤
    logLog x ^ (-21 : ℝ) * Real.log x ^ (55 / 100 : ℝ)
  L28 : 2 ≤ Real.log x ^ (28 / 100 : ℝ)
  expR : Real.exp ((2 * (|Cj| + 1) + 216 * (|Cj| + 1) ^ 2) * (logLogLog x ^ 3 + 1)) ≤
    Real.log x ^ (1 / 200 : ℝ)
  expE : Real.exp (endExp q K CN c E₂ * (logLogLog x ^ 2 + 1)) ≤ Real.log x ^ (1 / 200 : ℝ)
  F3 : (|Cj| + 1) * (logLogLog x + 1) + 1 ≤ Real.log x ^ (1 / 200 : ℝ)
  TPhi : logLog x ^ (CΦ * 1) ≤ Real.log x ^ (1 / 200 : ℝ)
  T42 : logLog x ^ (42 : ℝ) ≤ Real.log x ^ (1 / 200 : ℝ)

/-- The bound `|Comp_j - Prox_j| ≤ C (x/L) L^{-1/20}` at one large scale. -/
theorem final_at {q cw : ℝ} (hq : 0 < q) (hq₁ : q < 1) (hcw : 0 ≤ cw) (hcw₁ : cw ≤ 1)
    {K : ℕ} (hK : 1 ≤ K) {CN c Ch Cj κ CΦ C₂ c₃ A₁ C₁r E₂ L₀ EM1 EM2 : ℝ} {M : ℕ → ℝ}
    (hc : 0 < c) (hκ : 1 < κ) (hC₂ : 0 ≤ C₂) (hc₃ : 0 < c₃)
    (hmert : ∀ y : ℝ, 2 ≤ y → c₃ / Real.log y ≤ ∏ p ∈ primesIcc 2 y, (1 - (1 : ℝ) / p))
    (hA₁ : 0 < A₁)
    (hG : ∀ (x : ℝ) (j W : ℕ) (θ : ℝ), 1 ≤ Real.log x → 1 ≤ j → 2 ≤ proxyCutoff x →
      C₁r ≤ Real.log (proxyCutoff x) → 0 < θ →
      ∑ m ∈ Icc 1 W, dampedWeight x j m ≤
        A₁ * W / Real.log (proxyCutoff x) * ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ +
          (W : ℝ) ^ θ * ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-θ))⁻¹)
    (hE₂0 : 0 ≤ E₂) (hE₂ : ∀ y : ℝ, 2 ≤ y → ∑ p ∈ primesIoc 1 y, (1 : ℝ) / p ≤ logLog y + E₂)
    (hL₀ : ∀ x a : ℝ, L₀ ≤ Real.log x → 1 / 10 ≤ a → 1 / 2 ≤ harmonicMass (band x a))
    (hEM10 : 0 ≤ EM1)
    (hEM1 : ∀ y z : ℝ, 1 ≤ y → y ≤ z →
      |∑ p ∈ primesIoc y z, Real.log p / p - Real.log (z / y)| ≤ EM1)
    (hEM2 : ∀ y z : ℝ, 2 ≤ y → y ≤ z →
      |∑ p ∈ primesIoc y z, (1 : ℝ) / p - Real.log (Real.log z / Real.log y)| ≤ EM2 / Real.log y)
    {x : ℝ} (hX : LargeX q K CN c Ch Cj κ CΦ C₂ c₃ C₁r E₂ L₀ EM1 EM2 x) :
    ∀ k ≤ 2, ∀ (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) (Φ : ℝ → ℝ) (j : ℕ),
      AdmissibleSlots c x u v → (∀ Q, 0 ≤ B Q ∧ B Q ≤ 1) → IsCutoff κ CΦ M x Φ →
      2 ≤ j → j ≤ compositeCutoff Cj x →
      |compositeSum q cw K CN x (presieveExponent c Ch x) κ j Φ u v B -
          proxySum q cw K CN x (presieveExponent c Ch x) κ j Φ u v B| ≤
        (2 * κ * M 0 + 25 * M 0 * C₂ * κ + 56 * κ ^ 2 * M 1 +
          2 * κ * M 0 * (A₁ / c₃ + 1) * (6 * (A₁ / c₃ + 1) + 4 / c₃)) *
          (x / Real.log x) * Real.log x ^ (-(1 / 20) : ℝ) := by
  intro k hk u v B Φ j hadm hB hΦ hj2 hjJ
  obtain ⟨r, rfl⟩ : ∃ r, j = r + 2 := ⟨j - 2, by omega⟩
  set γ := presieveExponent c Ch x
  set N := ⌊κ * x + 1⌋₊
  set L := Real.log x
  set T := logLog x
  set s := logLogLog x
  set b := |Cj| + 1 with hbdef
  have hb0 : 0 ≤ b := by positivity
  have hL1 : 1 ≤ L := by linarith [hX.L16]
  have hL0 : 0 < L := by linarith
  have hT1 : 1 ≤ T := by linarith [hX.T50]
  have hT0 : 0 < T := by linarith
  have hs0 : 0 ≤ s := by linarith [hX.s1]
  have hx2 : 2 ≤ x := by linarith [hX.x4]
  have hx0 : 0 < x := by linarith
  have hu1 : 1 ≤ L ^ (1 / 200 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  -- the number of factors
  have hjs : ((r + 2 : ℕ) : ℝ) ≤ Cj * s + 1 := by
    unfold compositeCutoff at hjJ
    by_cases hCs : 0 ≤ Cj * s
    · have := Nat.ceil_lt_add_one hCs
      have : ((r + 2 : ℕ) : ℝ) ≤ ⌈Cj * s⌉₊ := by exact_mod_cast hjJ
      linarith
    · push Not at hCs
      rw [Nat.ceil_eq_zero.2 hCs.le] at hjJ
      omega
  have hRb : ((r + 2 : ℕ) : ℝ) ≤ b * (s + 1) := by
    have : Cj * s ≤ |Cj| * s := mul_le_mul_of_nonneg_right (le_abs_self _) hs0
    rw [hbdef]
    nlinarith [abs_nonneg Cj]
  -- scale facts
  have hjY : 2 * ((r + 2 : ℕ) : ℝ) + 4 ≤ L ^ (1 / 2 : ℝ) := by linarith [hX.jY]
  have hsf := scaleFacts_of hc₃ hmert hκ hx2 hX.L16 hX.T50 hX.gamma_low hX.T21
    hX.T25 hX.Tc (j := r + 2) (by omega) hjY
  have hsf1 := scaleFacts_of hc₃ hmert hκ hx2 hX.L16 hX.T50 hX.gamma_low hX.T21
    hX.T25 hX.Tc (j := 1) le_rfl (by
      have : (0 : ℝ) ≤ (r + 2 : ℕ) := Nat.cast_nonneg _
      push_cast at hjY ⊢; linarith)
  -- the endpoint
  have hV : ∀ a : ℝ, 1 / 10 ≤ a → 1 / 2 ≤ harmonicMass (band x a) := fun a ha =>
    hL₀ x a hX.LL0 ha
  have hlay : 2 * ((inertPerCluster K CN x : ℝ) + 1) * K ≤ 4 / 100 * T := by
    have h1 : (inertPerCluster K CN x : ℝ) ≤ |CN| * s + 1 := inertPerCluster_le hK hs0
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have h2 : 2 * ((inertPerCluster K CN x : ℝ) + 1) * K ≤ 2 * (|CN| * s + 2) * K :=
      mul_le_mul_of_nonneg_right (by linarith) hK0
    linarith [hX.lay]
  have hE := endpointData_of hq hq₁ hcw hcw₁ hK hc hx2 (by linarith [hX.L16]) hT0 hlay hV
    hX.small hE₂
    hE₂0 hk hadm hB
  have hSE0 : 0 ≤ endBound q K CN c E₂ x := by
    have := hE.norm_pos
    unfold endBound
    have : 0 < 1 - q := by linarith
    positivity
  have hF1 : endBound q K CN c E₂ x ≤ L ^ (1 / 200 : ℝ) :=
    (endBound_le_exp hq hq₁ hK hc hE₂0 hT1 hs0).trans hX.expE
  have hF3 : (r + 2 : ℝ) ≤ L ^ (1 / 200 : ℝ) := by
    have := hX.F3
    push_cast at hRb
    nlinarith
  -- the factor sums
  have hlogY : Real.log (proxyCutoff x) = L / T ^ 25 := by unfold proxyCutoff; rw [Real.log_exp]
  have hγ2 : 2 ≤ x ^ γ := by
    have h1 : Real.exp 2 ≤ Real.exp (L ^ (28 / 100 : ℝ)) := Real.exp_le_exp.2 hX.L28
    have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    linarith [hsf.exp_le_rpow]
  have hEγ : EM2 ≤ Real.log (x ^ γ) := by
    rw [Real.log_rpow hx0]
    have := mul_le_mul_of_nonneg_right hX.gamma_low hL0.le
    linarith [hX.EM2g]
  have hEY : EM2 ≤ Real.log (proxyCutoff x) := by rw [hlogY]; exact hX.EM2Y
  have hRY : 2 * (b * (s + 1)) ≤ proxyCutoff x := by
    have h1 : L ^ (1 / 2 : ℝ) ≤ L / T ^ 25 := by
      rw [le_div_iff₀ (by positivity)]
      have : T ^ (25 : ℕ) = T ^ (25 : ℝ) := by norm_cast
      rw [this]
      calc L ^ (1 / 2 : ℝ) * T ^ (25 : ℝ) ≤ L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) := by
            gcongr; exact hX.T25
        _ = L := by rw [← Real.rpow_add hL0]; norm_num
    have h2 : L / T ^ 25 ≤ proxyCutoff x := by
      unfold proxyCutoff
      have := Real.add_one_le_exp (L / T ^ 25)
      linarith
    linarith [hX.jY]
  have hN2' : ((N : ℕ) : ℝ) ≤ x ^ 2 := by linarith [hX.N2]
  have hfs := factor_sums_le hb0 hEM2 hκ hx2 hL1 hT1 hs0 hN2' hsf1 hX.gamma_low hX.gamma_le hγ2
    hEγ hEY hlogY hRY hX.expR (R := r + 1) (by
      have : ((r + 1 : ℕ) : ℝ) ≤ ((r + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : r + 1 ≤ r + 2)
      linarith) (by omega)
  obtain ⟨hF4, hF5, hPr, hP1⟩ := hfs
  -- E4
  have hE4 := final_E4 hq₁ hE hV hX.box hC₂ hΦ hκ hX.x4 hL1 hT0 hX.N2 hX.L3 hsf hjs hSE0 hF1
    hF3 hF4 hF5 hX.TPhi
  -- E5
  have hPiY := hmert (proxyCutoff x) (by
    have h1 : (1 : ℝ) ≤ L ^ (45 / 100 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have := Real.add_one_le_exp (L ^ (45 / 100 : ℝ))
    linarith [hsf.cutoff_gt])
  have hlogY0 : 0 < Real.log (proxyCutoff x) := by rw [hlogY]; positivity
  have hcount := count_at (N := N) hA₁ hc₃ hG hEM2 hsf (by linarith [hX.L16]) hX.L28 hPiY hlogY0
    (by rw [hlogY]; exact hX.C1) (by
      rw [hlogY]
      have := mul_le_mul_of_nonneg_right hX.gamma_low (show 0 ≤ L ^ (55 / 100 : ℝ) by positivity)
      linarith [hX.rank])
  have hSP := sum_candidate_log_le hL1 hEM1
  have hE5 := final_E5 hq₁ hE hV hΦ hκ hX.x4 hL1 hT1 hsf hX.gamma_low hX.gamma_le hc₃
    (CW := A₁ / c₃ + 1) (by positivity) hPiY hcount hSP hX.EM1L hEM10 hSE0 hF1 hF3
    (by simpa using hPr) hP1 hX.T42
  -- combine
  rw [compositeSum_eq, proxySum_eq]
  have hM0 : 0 ≤ M 0 := (abs_nonneg _).trans (by simpa using hΦ.2.2.2 0 0)
  have hM1 : 0 ≤ M 1 := by
    have h := cutoff_deriv_bound_nonneg hΦ 1
    push_cast at h
    exact nonneg_of_mul_nonneg_left h (by positivity)
  have hcomb := combine_le hL1 hx0 (C₄ := 2 * κ * M 0 + 25 * M 0 * C₂ * κ + 56 * κ ^ 2 * M 1)
    (C₅ := 2 * κ * M 0 * (A₁ / c₃ + 1) * (6 * (A₁ / c₃ + 1) + 4 / c₃)) (by positivity)
    (by positivity)
  calc _ ≤ _ + _ := abs_sub_le _ (∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 2) => Icc 1 N),
        cutPsi Φ (endpoint q cw K CN x u v B) x (∏ i, m i) *
          ∏ i, unstrippedProxy x γ (r + 2) (m i)) _
    _ ≤ _ := add_le_add hE4 hE5
    _ ≤ _ := hcomb

end Erdos408.TypeII
