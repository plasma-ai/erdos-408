module

public import Erdos408.Extraction.TypeII.Final

/-!
# E4–E5 at large `x`

The pointwise facts at one large scale, and the assembly of `|Comp_j - Prox_j|`.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real Filter

/-- The scale facts at a large `x`. -/
theorem scaleFacts_of {c Ch κ c₃ : ℝ} {x : ℝ} {j : ℕ} (hc₃ : 0 < c₃)
    (hmert : ∀ y : ℝ, 2 ≤ y → c₃ / Real.log y ≤ ∏ p ∈ primesIcc 2 y, (1 - (1 : ℝ) / p))
    (hκ : 1 < κ) (hx : 2 ≤ x) (hL : 16 ≤ Real.log x) (hT : 50 ≤ logLog x)
    (hγ : logLog x ^ (-21 : ℝ) ≤ presieveExponent c Ch x)
    (h21 : logLog x ^ (21 : ℝ) ≤ Real.log x ^ (72 / 100 : ℝ))
    (h25 : logLog x ^ (25 : ℝ) ≤ Real.log x ^ (1 / 2 : ℝ))
    (hTc : 1 / c₃ ≤ logLog x ^ (4 : ℕ))
    (hj : 1 ≤ j) (hjY : 2 * (j : ℝ) + 4 ≤ Real.log x ^ (1 / 2 : ℝ)) :
    ScaleFacts x (presieveExponent c Ch x) j ⌊κ * x + 1⌋₊ := by
  set γ := presieveExponent c Ch x
  set L := Real.log x
  set T := logLog x
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by linarith
  have hγ0 : 0 < γ := lt_of_lt_of_le (by positivity) hγ
  have h25' : T ^ (25 : ℝ) ≤ L ^ (72 / 100 : ℝ) :=
    h25.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  have hexpγ := exp_le_rpow_gamma hx0 hL0 hT0 hγ h21
  have hexpY := exp_le_proxyCutoff hL0 hT0 h25'
  have hT25 : T ^ (25 : ℕ) = T ^ (25 : ℝ) := by norm_cast
  have hlogY : Real.log (proxyCutoff x) = L / T ^ 25 := by unfold proxyCutoff; rw [Real.log_exp]
  -- `L / T^{25} ≥ L^{1/2}`
  have hYL : L ^ (1 / 2 : ℝ) ≤ L / T ^ 25 := by
    rw [le_div_iff₀ (by positivity), hT25]
    calc L ^ (1 / 2 : ℝ) * T ^ (25 : ℝ) ≤ L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) := by gcongr
      _ = L := by rw [← Real.rpow_add hL0]; norm_num
  have hY2 : 2 ≤ proxyCutoff x := by
    have h1 : (1 : ℝ) ≤ L ^ (28 / 100 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have := Real.add_one_le_exp (L ^ (28 / 100 : ℝ))
    linarith
  refine ⟨by linarith, by linarith, hγ0, hj, ?_, ?_, ?_, ?_, hexpγ, hexpY, ?_⟩
  · exact one_le_prod_mul hc₃ hmert (by linarith) hT0 hγ hY2 hTc
  · -- `exp(L^{0.45}) < Y`
    unfold proxyCutoff
    rw [Real.exp_lt_exp]
    have h1 : L ^ (45 / 100 : ℝ) < L ^ (1 / 2 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
    have h2 : L ^ (1 / 2 : ℝ) ≤ L / T ^ 25 := hYL
    exact lt_of_lt_of_le h1 h2
  · -- `Y ≤ x^γ`
    have hγT : 1 ≤ γ * T ^ (25 : ℕ) := by
      have h1 := mul_le_mul_of_nonneg_right hγ (show 0 ≤ T ^ (25 : ℕ) by positivity)
      have h2 : T ^ (-21 : ℝ) * T ^ (25 : ℕ) = T ^ (4 : ℕ) := by
        rw [hT25, ← Real.rpow_add hT0]; norm_num
      have h3 : (1 : ℝ) ≤ T ^ (4 : ℕ) := one_le_pow₀ (by linarith)
      linarith
    unfold proxyCutoff
    rw [Real.rpow_def_of_pos hx0, Real.exp_le_exp, div_le_iff₀ (pow_pos hT0 25)]
    have := mul_le_mul_of_nonneg_left hγT hL0.le
    linarith
  · -- `Y ≤ M`
    have h1 : proxyCutoff x ≤ x := by
      have hle : L / T ^ 25 ≤ L := by
        rw [div_le_iff₀ (pow_pos hT0 25)]
        have : 1 ≤ T ^ 25 := one_le_pow₀ (by linarith)
        nlinarith
      calc proxyCutoff x = Real.exp (L / T ^ 25) := rfl
        _ ≤ Real.exp L := Real.exp_le_exp.2 hle
        _ = x := Real.exp_log hx0
    have h2 : x ≤ (⌊κ * x + 1⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (κ * x + 1)
      nlinarith
    linarith
  · -- `j < Y`
    have h1 : (j : ℝ) < L ^ (1 / 2 : ℝ) := by linarith
    have h2 : L / T ^ 25 ≤ proxyCutoff x := by
      unfold proxyCutoff
      have := Real.add_one_le_exp (L / T ^ 25)
      linarith
    linarith

/-- The factor sums at a large `x`: with `u = L^{1/200}`, the powers of the factor sums are
at most `u` for every number `R ≤ C_j s + 1` of companion factors. -/
theorem factor_sums_le {EM2 c Ch κ b : ℝ} {x : ℝ} (hb : 0 ≤ b)
    (hEM2 : ∀ y z : ℝ, 2 ≤ y → y ≤ z →
      |∑ p ∈ primesIoc y z, (1 : ℝ) / p - Real.log (Real.log z / Real.log y)| ≤ EM2 / Real.log y)
    (hκ : 1 < κ) (hx : 2 ≤ x) (hL : 1 ≤ Real.log x) (hT : 1 ≤ logLog x)
    (hs : 0 ≤ logLogLog x) (hN2 : ((⌊κ * x + 1⌋₊ : ℕ) : ℝ) ≤ x ^ 2)
    (hsf : ScaleFacts x (presieveExponent c Ch x) 1 ⌊κ * x + 1⌋₊)
    (hγ : logLog x ^ (-21 : ℝ) ≤ presieveExponent c Ch x)
    (hγ1 : presieveExponent c Ch x ≤ 1) (hγ2 : 2 ≤ x ^ presieveExponent c Ch x)
    (hEγ : EM2 ≤ Real.log (x ^ presieveExponent c Ch x))
    (hEY : EM2 ≤ Real.log (proxyCutoff x))
    (hlogY : Real.log (proxyCutoff x) = Real.log x / logLog x ^ 25)
    (hRY : 2 * (b * (logLogLog x + 1)) ≤ proxyCutoff x)
    (hexp : Real.exp ((2 * b + 216 * b ^ 2) * (logLogLog x ^ 3 + 1)) ≤ Real.log x ^ (1 / 200 : ℝ))
    {R : ℕ} (hR : (R : ℝ) ≤ b * (logLogLog x + 1)) (hR1 : 1 ≤ R) :
    ((R : ℝ) * recipSum x (presieveExponent c Ch x) ⌊κ * x + 1⌋₊ +
        highProd x ⌊κ * x + 1⌋₊ R) ^ R ≤ Real.log x ^ (1 / 200 : ℝ) ∧
      (recipSum x (presieveExponent c Ch x) ⌊κ * x + 1⌋₊ + highProd x ⌊κ * x + 1⌋₊ 1) ^ R ≤
        Real.log x ^ (1 / 200 : ℝ) ∧
      highProd x ⌊κ * x + 1⌋₊ 1 ^ (R - 1) ≤ Real.log x ^ (1 / 200 : ℝ) ∧
      highProd x ⌊κ * x + 1⌋₊ 1 ≤ Real.log x ^ (1 / 200 : ℝ) := by
  set γ := presieveExponent c Ch x
  set N := ⌊κ * x + 1⌋₊
  set s := logLogLog x
  set T := logLog x
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by linarith
  have hγ0 : 0 < γ := hsf.gamma_pos
  have hxγN : x ^ γ ≤ N := by
    have h1 : x ^ γ ≤ x := by
      calc x ^ γ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hγ1
        _ = x := Real.rpow_one x
    have h2 : x ≤ (N : ℝ) := by
      have := Nat.lt_floor_add_one (κ * x + 1)
      nlinarith
    linarith
  have hlogN : Real.log N ≤ 2 * L := by
    have hN0 : (0 : ℝ) < N := by linarith [Real.rpow_pos_of_pos hx0 γ]
    calc Real.log N ≤ Real.log (x ^ 2) := Real.log_le_log hN0 hN2
      _ = 2 * L := by rw [Real.log_pow]; push_cast; ring
  -- `∑_{x^γ < p ≤ M} 1/p ≤ log 2 + 21 s + 1`
  have hrec : recipSum x γ N ≤ Real.log 2 + 21 * s + 1 := by
    refine (recipSum_le hEM2 hγ2 hxγN hEγ).trans ?_
    have hlg : Real.log (x ^ γ) = γ * L := Real.log_rpow hx0 γ
    have hq : Real.log N / Real.log (x ^ γ) ≤ 2 * T ^ (21 : ℝ) := by
      rw [hlg, div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hγ (show 0 ≤ 2 * T ^ (21 : ℝ) * L by positivity)
      have e : 2 * T ^ (21 : ℝ) * L * T ^ (-21 : ℝ) = 2 * L := by
        rw [mul_comm (2 * T ^ (21 : ℝ)) L, mul_assoc, mul_assoc, ← Real.rpow_add hT0]
        norm_num; ring
      nlinarith
    have hq0 : 0 < Real.log N / Real.log (x ^ γ) := by
      have h1 : 0 < Real.log N := Real.log_pos (by linarith)
      have h2 : 0 < Real.log (x ^ γ) := Real.log_pos (by linarith)
      positivity
    have := Real.log_le_log hq0 hq
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hT0] at this
    have hs' : Real.log T = s := rfl
    linarith
  -- `∏_{Y < p ≤ M} (1 - ρ/p)⁻¹ ≤ exp(2ρ(log 2 + 25 s + 1))`
  have hY1 : 1 < proxyCutoff x := by
    have : (1 : ℝ) ≤ Real.exp (L ^ (45 / 100 : ℝ)) := Real.one_le_exp (by positivity)
    linarith [hsf.cutoff_gt]
  have hN1 : (1 : ℝ) < N := lt_of_lt_of_le hY1 hsf.cutoff_le_N
  have hhigh : ∀ ρ : ℝ, 0 ≤ ρ → 2 * ρ ≤ proxyCutoff x →
      highProd x N ρ ≤ Real.exp (2 * ρ * (Real.log 2 + 25 * s + 1)) := by
    intro ρ hρ hρY
    have hY2 : 2 ≤ proxyCutoff x := by
      have h1 : (1 : ℝ) ≤ L ^ (45 / 100 : ℝ) := Real.one_le_rpow hL (by norm_num)
      have := Real.add_one_le_exp (L ^ (45 / 100 : ℝ))
      linarith [hsf.cutoff_gt]
    refine (highProd_le hρ hEM2 hY2 hρY hsf.cutoff_le_N hEY).trans (Real.exp_le_exp.2 ?_)
    have hlY : 0 < Real.log (proxyCutoff x) := by rw [hlogY]; positivity
    have hq : Real.log N / Real.log (proxyCutoff x) ≤ 2 * T ^ 25 := by
      rw [hlogY, div_le_iff₀ (by positivity)]
      field_simp
      linarith
    have hq0 : 0 < Real.log N / Real.log (proxyCutoff x) := by
      have h1 : 0 < Real.log N := Real.log_pos hN1
      positivity
    have := Real.log_le_log hq0 hq
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    have hs' : Real.log T = s := rfl
    push_cast at this
    nlinarith
  -- apply the power bound
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hR1' : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hrec0 := recipSum_nonneg x γ N
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrec' : recipSum x γ N ≤ Real.log 2 + 25 * s + 1 := by linarith
  have hYR : 2 * (R : ℝ) ≤ proxyCutoff x := by nlinarith
  have hY1' : 2 * (1 : ℝ) ≤ proxyCutoff x := by nlinarith
  have hhR := hhigh R hR0 hYR
  have hh1 := hhigh 1 zero_le_one hY1'
  have hmono : Real.exp (2 * 1 * (Real.log 2 + 25 * s + 1)) ≤
      Real.exp (2 * R * (Real.log 2 + 25 * s + 1)) := by
    apply Real.exp_le_exp.2
    have : 0 ≤ Real.log 2 + 25 * s + 1 := by positivity
    nlinarith
  have hhP0 : 0 ≤ highProd x N 1 := highProd_nonneg (by linarith)
  have hhPR0 : 0 ≤ highProd x N R := highProd_nonneg (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (factor_pow_le hs hR0 hb hR hrec' (by positivity) ?_ R le_rfl).trans hexp
    linarith
  · refine (factor_pow_le hs hR0 hb hR hrec' (by positivity) ?_ R le_rfl).trans hexp
    have : recipSum x γ N ≤ R * recipSum x γ N := le_mul_of_one_le_left hrec0 hR1'
    linarith
  · refine (factor_pow_le hs hR0 hb hR (by positivity) hhP0 ?_ (R - 1)
      (by push_cast [Nat.cast_sub hR1]; linarith)).trans hexp
    linarith
  · have := (factor_pow_le hs hR0 hb hR (by positivity) hhP0 (by linarith) 1
      (by push_cast; linarith)).trans hexp
    rwa [pow_one] at this

/-- E4 at a large `x`: `|Comp_j - Prox_j^0| ≤ C₄ x L^{-3} u⁴`. -/
theorem final_E4 {q cw : ℝ} (hq₁ : q < 1) {K : ℕ} {CN c Ch Cj κ CΦ C₂ x E₂ : ℝ}
    {M : ℕ → ℝ} {Φ : ℝ → ℝ} {k : ℕ} {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ}
    (hE : EndpointData q cw K CN x u v B (normBound q K CN c E₂ x))
    (hV : ∀ a : ℝ, 1 / 10 ≤ a → 1 / 2 ≤ harmonicMass (band x a))
    (hbox : BoxBound q K c Ch Cj κ C₂ x) (hC₂ : 0 ≤ C₂) (hΦ : IsCutoff κ CΦ M x Φ)
    (hκ : 1 < κ) (hx4 : 4 * κ + 4 ≤ x) (hL : 1 ≤ Real.log x) (hT : 0 < logLog x)
    (hN2 : (⌊κ * x + 1⌋₊ : ℝ) + 1 ≤ x ^ 2)
    (hL3 : Real.log x ^ 3 ≤ κ * x) {r : ℕ}
    (hsf : ScaleFacts x (presieveExponent c Ch x) (r + 2) ⌊κ * x + 1⌋₊)
    (hj2 : ((r + 2 : ℕ) : ℝ) ≤ Cj * logLogLog x + 1)
    (hSE0 : 0 ≤ endBound q K CN c E₂ x)
    (hF1 : endBound q K CN c E₂ x ≤ Real.log x ^ (1 / 200 : ℝ))
    (hF3 : (r + 2 : ℝ) ≤ Real.log x ^ (1 / 200 : ℝ))
    (hF4 : ((r + 1 : ℕ) * recipSum x (presieveExponent c Ch x) ⌊κ * x + 1⌋₊ +
      highProd x ⌊κ * x + 1⌋₊ (r + 1 : ℕ)) ^ (r + 1) ≤ Real.log x ^ (1 / 200 : ℝ))
    (hF5 : (recipSum x (presieveExponent c Ch x) ⌊κ * x + 1⌋₊ + highProd x ⌊κ * x + 1⌋₊ 1) ^
      (r + 1) ≤ Real.log x ^ (1 / 200 : ℝ))
    (hF6 : logLog x ^ (CΦ * 1) ≤ Real.log x ^ (1 / 200 : ℝ)) :
    |∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 2) => Icc 1 ⌊κ * x + 1⌋₊),
        cutPsi Φ (endpoint q cw K CN x u v B) x (∏ i, m i) *
          ∏ i, primeWeight x (presieveExponent c Ch x) (m i) -
      ∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 2) => Icc 1 ⌊κ * x + 1⌋₊),
        cutPsi Φ (endpoint q cw K CN x u v B) x (∏ i, m i) *
          ∏ i, unstrippedProxy x (presieveExponent c Ch x) (r + 2) (m i)| ≤
      (2 * κ * M 0 + 25 * M 0 * C₂ * κ + 56 * κ ^ 2 * M 1) * x * Real.log x ^ (-3 : ℝ) *
        (Real.log x ^ (1 / 200 : ℝ)) ^ 4 := by
  set γ := presieveExponent c Ch x
  set N := ⌊κ * x + 1⌋₊
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hκ0 : 0 < κ := by linarith
  have hx0 : 0 < x := by linarith
  have hxκ : κ ≤ x := by linarith
  have hκx1 : 1 ≤ κ * x := by nlinarith
  have hsq : 4 * (κ * x + 1) ≤ x ^ 2 := by nlinarith
  set δ := L ^ (-3 : ℝ) with hδ
  have hδ0 : 0 < δ := by positivity
  have hL3' : L ^ (3 : ℝ) = L ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast L 3
  have hδinv : δ = (L ^ (3 : ℕ))⁻¹ := by rw [hδ, Real.rpow_neg hL0.le, hL3']
  have hδ1 : δ ≤ 1 := by
    rw [hδinv]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  have hxγ : 1 ≤ x ^ γ := Real.one_le_rpow hsf.one_lt.le hsf.gamma_pos.le
  set A := ⌈2 * Real.log (N + 1) / δ⌉₊ with hAdef
  have hA := gridPt_ge hxγ hδ0 hδ1 N
  have hAle : (A : ℝ) ≤ 5 * L ^ 4 := by
    have h1 : (A : ℝ) < 2 * Real.log (N + 1) / δ + 1 := Nat.ceil_lt_add_one
      (div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by
        have := Nat.cast_nonneg (α := ℝ) N; linarith))) hδ0.le)
    have h2 : Real.log ((N : ℝ) + 1) ≤ 2 * L := by
      calc Real.log ((N : ℝ) + 1) ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) hN2
        _ = 2 * L := by rw [Real.log_pow]; push_cast; ring
    have h3 : 2 * Real.log (N + 1) / δ ≤ 4 * L ^ 4 := by
      rw [hδinv, div_inv_eq_mul]
      calc 2 * Real.log ((N : ℝ) + 1) * L ^ 3 ≤ 2 * (2 * L) * L ^ 3 := by gcongr
        _ = 4 * L ^ 4 := by ring
    have h4 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL
    linarith
  have hE4 := abs_comp_sub_prox0_le hq₁ hE hV hbox hC₂ hΦ hκ hxκ hsq (R := r + 1) (by omega)
    hsf hj2 hδ0.le hδ1 hA
  have hu : 1 ≤ L ^ (1 / 200 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hM0 : 0 ≤ M 0 := (abs_nonneg _).trans (by simpa using hΦ.2.2.2 0 0)
  have hM1 : 0 ≤ M 1 := by
    have h := cutoff_deriv_bound_nonneg hΦ 1
    push_cast at h
    exact nonneg_of_mul_nonneg_left h (by positivity)
  have hF2 : 2 ^ (K * inertPerCluster K CN x) * normBound q K CN c E₂ x ≤
      L ^ (1 / 200 : ℝ) := by
    refine le_trans ?_ hF1
    unfold endBound
    have h1 : (1 : ℝ) ≤ (2 / (1 - q)) ^ K := one_le_pow₀ (by
      rw [le_div_iff₀ (by linarith)]; linarith [hE.q_pos])
    have hN0 := hE.norm_pos
    have h2 : (0 : ℝ) < 2 ^ (K * inertPerCluster K CN x) := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 (mul_pos h2 hN0).le
    calc 2 ^ (K * inertPerCluster K CN x) * normBound q K CN c E₂ x
        = 2 ^ (K * inertPerCluster K CN x) * normBound q K CN c E₂ x * 1 := by ring
      _ ≤ 2 ^ (K * inertPerCluster K CN x) * normBound q K CN c E₂ x * (2 / (1 - q)) ^ K := h3
      _ = _ := by ring
  have hN : (N : ℝ) ≤ 2 * κ * x := by
    have := Nat.floor_le (show 0 ≤ κ * x + 1 by positivity)
    linarith
  have hτ : (3 * L ^ (-3 : ℝ) * (κ * x + 1) + 1) / x ≤ 7 * κ * L ^ (-3 : ℝ) := by
    rw [div_le_iff₀ hx0]
    have hδx : 1 ≤ κ * x * δ := by
      rw [hδinv, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]; exact hL3
    have h1 : 3 * δ ≤ 3 * δ * (κ * x) := le_mul_of_one_le_right (by positivity) hκx1
    linarith
  have hκx : 4 * (κ * x + 1) ≤ 8 * κ * x := by linarith
  have hb4 := bound4_le (A := A) hsf.one_lt hκ hL hu hM0 hM1 hC₂ hSE0 hF1 hF2 hE.norm_pos.le
    hF3 hF4 (by
      have := recipSum_nonneg x γ N
      have : 0 ≤ highProd x N (r + 1 : ℕ) := highProd_nonneg (by
        have := hsf.j_lt_cutoff
        push_cast at this ⊢
        linarith)
      positivity) hF5 (by
      have := recipSum_nonneg x γ N
      have : 0 ≤ highProd x N 1 := highProd_nonneg (by
        have := hsf.j_lt_cutoff
        push_cast at this
        linarith)
      positivity) hF6 hN hAle hτ hκx
  refine hE4.trans (le_of_eq_of_le ?_ hb4)
  push_cast
  ring

/-- E5 at a large `x`: `|Prox_j^0 - Prox_j| ≤ C₅ x L^{-1} L^{-1/10} u⁶`. -/
theorem final_E5 {q cw : ℝ} (hq₁ : q < 1) {K : ℕ} {CN c Ch κ CΦ x E₂ : ℝ}
    {M : ℕ → ℝ} {Φ : ℝ → ℝ} {k : ℕ} {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ}
    (hE : EndpointData q cw K CN x u v B (normBound q K CN c E₂ x))
    (hV : ∀ a : ℝ, 1 / 10 ≤ a → 1 / 2 ≤ harmonicMass (band x a)) (hΦ : IsCutoff κ CΦ M x Φ)
    (hκ : 1 < κ) (hx4 : 4 * κ + 4 ≤ x) (hL : 1 ≤ Real.log x) (hT : 1 ≤ logLog x) {r : ℕ}
    (hsf : ScaleFacts x (presieveExponent c Ch x) (r + 2) ⌊κ * x + 1⌋₊)
    (hγ : logLog x ^ (-21 : ℝ) ≤ presieveExponent c Ch x) (hγ1 : presieveExponent c Ch x ≤ 1)
    {c₃ CW EM1 : ℝ} (hc₃ : 0 < c₃) (hCW : 0 ≤ CW)
    (hPiY : c₃ / Real.log (proxyCutoff x) ≤ ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p))
    (hcount : ∀ w : ℝ, 0 ≤ w → ∑ m ∈ Icc 1 ⌊κ * x + 1⌋₊,
      (if (m : ℝ) ≤ w then proxyEnv x (presieveExponent c Ch x) (r + 2) m else 0) ≤
        CW / (presieveExponent c Ch x * Real.log x) * w)
    (hSP : ∑ p ∈ candidatePrimes x, Real.log p / p ≤ Real.log x ^ (45 / 100 : ℝ) + EM1)
    (hEM1 : EM1 ≤ Real.log x ^ (45 / 100 : ℝ)) (hEM10 : 0 ≤ EM1)
    (hSE0 : 0 ≤ endBound q K CN c E₂ x)
    (hF1 : endBound q K CN c E₂ x ≤ Real.log x ^ (1 / 200 : ℝ))
    (hF3 : (r + 2 : ℝ) ≤ Real.log x ^ (1 / 200 : ℝ))
    (hPr : highProd x ⌊κ * x + 1⌋₊ 1 ^ r ≤ Real.log x ^ (1 / 200 : ℝ))
    (hP1 : highProd x ⌊κ * x + 1⌋₊ 1 ≤ Real.log x ^ (1 / 200 : ℝ))
    (hT42 : logLog x ^ (42 : ℝ) ≤ Real.log x ^ (1 / 200 : ℝ)) :
    |∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 2) => Icc 1 ⌊κ * x + 1⌋₊),
        cutPsi Φ (endpoint q cw K CN x u v B) x (∏ i, m i) *
          ∏ i, unstrippedProxy x (presieveExponent c Ch x) (r + 2) (m i) -
      ∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 2) => Icc 1 ⌊κ * x + 1⌋₊),
        cutPsi Φ (endpoint q cw K CN x u v B) x (∏ i, m i) *
          ∏ i, strippedProxy x (presieveExponent c Ch x) (r + 2) (m i)| ≤
      2 * κ * M 0 * CW * (6 * CW + 4 / c₃) * x * Real.log x ^ (-1 : ℝ) *
        Real.log x ^ (-(1 / 10) : ℝ) * (Real.log x ^ (1 / 200 : ℝ)) ^ 6 := by
  set γ := presieveExponent c Ch x
  set N := ⌊κ * x + 1⌋₊
  set L := Real.log x
  set T := logLog x
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by linarith
  have hκ0 : 0 < κ := by linarith
  have hx0 : 0 < x := by linarith
  have hxκ : κ ≤ x := by linarith
  have hκx : κ * x ≤ x ^ 2 := by nlinarith
  have hγ0 := hsf.gamma_pos
  have hlogY : Real.log (proxyCutoff x) = L / T ^ 25 := by unfold proxyCutoff; rw [Real.log_exp]
  have hlogY0 : 0 < Real.log (proxyCutoff x) := by rw [hlogY]; positivity
  have hlogYL : Real.log (proxyCutoff x) ≤ L := by
    rw [hlogY, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ T ^ 25 := one_le_pow₀ hT
    nlinarith
  set K' := ⌈L ^ (9 / 10 : ℝ) / Real.log 2⌉₊ with hK'def
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK' : Real.exp (L ^ (9 / 10 : ℝ)) ≤ 2 ^ K' := by
    have h2K : Real.exp (K' * Real.log 2) = (2 : ℝ) ^ K' := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [← h2K]
    apply Real.exp_le_exp.2
    have := Nat.le_ceil (L ^ (9 / 10 : ℝ) / Real.log 2)
    rw [div_le_iff₀ hl2] at this
    linarith
  have hK'le : (K' : ℝ) ≤ 3 * L ^ (9 / 10 : ℝ) := by
    have h1 : (K' : ℝ) < L ^ (9 / 10 : ℝ) / Real.log 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : L ^ (9 / 10 : ℝ) / Real.log 2 ≤ 2 * L ^ (9 / 10 : ℝ) := by
      rw [div_le_iff₀ hl2]
      have := Real.log_two_gt_d9
      nlinarith [Real.rpow_nonneg hL0.le (9 / 10 : ℝ)]
    have h3 : (1 : ℝ) ≤ L ^ (9 / 10 : ℝ) := Real.one_le_rpow hL (by norm_num)
    linarith
  have hcW0 : 0 ≤ CW / (γ * L) := by positivity
  have hE5 := abs_prox0_sub_prox_le hq₁ hE hV hΦ hκ hxκ hκx hsf hγ1 hc₃ hlogY0 hPiY hcW0 hcount
    hSP hK'
  have hu : 1 ≤ L ^ (1 / 200 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hM0 : 0 ≤ M 0 := (abs_nonneg _).trans (by simpa using hΦ.2.2.2 0 0)
  -- `1/γ ≤ T^{21} ≤ T^{42} ≤ u`
  have hγinv : 1 / γ ≤ T ^ (21 : ℝ) := by
    rw [div_le_iff₀ hγ0]
    have h1 := mul_le_mul_of_nonneg_left hγ (show 0 ≤ T ^ (21 : ℝ) by positivity)
    have e : T ^ (21 : ℝ) * T ^ (-21 : ℝ) = 1 := by rw [← Real.rpow_add hT0]; norm_num
    linarith
  have hT2142 : T ^ (21 : ℝ) ≤ T ^ (42 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have hcW : CW / (γ * L) ≤ CW * L ^ (1 / 200 : ℝ) / L := by
    have h1 : 1 / γ ≤ L ^ (1 / 200 : ℝ) := hγinv.trans (hT2142.trans hT42)
    calc CW / (γ * L) = CW / L * (1 / γ) := by field_simp
      _ ≤ CW / L * L ^ (1 / 200 : ℝ) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = CW * L ^ (1 / 200 : ℝ) / L := by ring
  have hγ2 : 1 / γ ^ 2 ≤ L ^ (1 / 200 : ℝ) := by
    refine le_trans ?_ hT42
    have h1 : 1 / γ ^ 2 = (1 / γ) ^ 2 := by rw [one_div_pow]
    rw [h1]
    calc (1 / γ) ^ 2 ≤ (T ^ (21 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hγinv 2
      _ = T ^ (42 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  have hN : (N : ℝ) ≤ 2 * κ * x := by
    have := Nat.floor_le (show 0 ≤ κ * x + 1 by positivity)
    have : 1 ≤ κ * x := by nlinarith
    linarith
  have hP0 : 0 ≤ highProd x N 1 := highProd_nonneg (by
    have := hsf.j_lt_cutoff
    push_cast at this
    linarith)
  have hSP2 : L ^ (45 / 100 : ℝ) + EM1 ≤ 2 * L ^ (45 / 100 : ℝ) := by linarith
  have hb5 := bound5_le (q := q) (K := K) (CN := CN) (c := c) (E₂ := E₂) (κ := κ) (M := M)
    (x := x) (γ := γ) (cW := CW / (γ * L)) (SP := L ^ (45 / 100 : ℝ) + EM1) (c₃ := c₃)
    (CW := CW) (K' := K') (r := r) hsf.one_lt hκ hL hu hM0 hc₃ hCW hγ0 hSE0 hF1 hF3 hcW0 hcW hN
    hP0 hPr hP1 hK'le (by positivity) hSP2 hlogY0.le hlogYL hγ2
  refine hE5.trans (le_of_eq_of_le ?_ hb5)
  ring

end Erdos408.TypeII
