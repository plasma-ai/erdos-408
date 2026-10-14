import Erdos408.Extraction.TypeII.Telescope

/-!
# The endpoint bounds at one scale

The explicit size `𝒩 = (2/(1-q))^{K N'} S_B` of the remainders, with
`S_B = (2T²⁰/c + 1)³ + (T + E₂ + 1)³` bounding `|f_𝔟 - C_𝔟|` on `[1, x²]`, and the bound
`|P (f_𝔟 - C_𝔟)| ≤ 2^{K N'} (2/(1-q))^K 𝒩` on `[1, x²]`.
-/

namespace Erdos408.TypeII

open Finset Real

/-- The bound `S_B` for the centred slot statistic on `[1, x²]`. -/
noncomputable def slotBound (c E₂ x : ℝ) : ℝ :=
  (2 * logLog x ^ 20 / c + 1) ^ 3 + (logLog x + E₂ + 1) ^ 3

/-- The bound `𝒩` for the remainders. -/
noncomputable def normBound (q : ℝ) (K : ℕ) (CN c E₂ x : ℝ) : ℝ :=
  (2 / (1 - q)) ^ (K * inertPerCluster K CN x) * slotBound c E₂ x

/-- The bound for the endpoint `P (f_𝔟 - C_𝔟)`. -/
noncomputable def endBound (q : ℝ) (K : ℕ) (CN c E₂ x : ℝ) : ℝ :=
  2 ^ (K * inertPerCluster K CN x) * (2 / (1 - q)) ^ K * normBound q K CN c E₂ x

theorem slotBound_pos {c E₂ x : ℝ} (hc : 0 < c) (hE₂ : 0 ≤ E₂) (hT : 0 ≤ logLog x) :
    1 ≤ slotBound c E₂ x := by
  unfold slotBound
  have h1 : 1 ≤ (2 * logLog x ^ 20 / c + 1) ^ 3 := one_le_pow₀ (by
    have : 0 ≤ 2 * logLog x ^ 20 / c := by positivity
    linarith)
  have h2 : 0 ≤ (logLog x + E₂ + 1) ^ 3 := by positivity
  linarith

/-- `|f_𝔟(h) - C_𝔟| ≤ S_B` on `[1, x²]`. -/
theorem abs_slot_sub_le {c E₂ x : ℝ} (hx : 2 ≤ x) (hc : 0 < c) (hT : 0 < logLog x)
    (hE₂ : ∀ y : ℝ, 2 ≤ y → ∑ p ∈ primesIoc 1 y, (1 : ℝ) / p ≤ logLog y + E₂) (hE₂0 : 0 ≤ E₂)
    {k : ℕ} (hk : k ≤ 2) {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ}
    (hadm : AdmissibleSlots c x u v) (hB : ∀ Q, 0 ≤ B Q ∧ B Q ≤ 1) {h : ℕ} (h1 : 1 ≤ h)
    (hh : (h : ℝ) ≤ x ^ 2) : |slotCount x u v B h - slotMean x u v B| ≤ slotBound c E₂ x := by
  have hf0 := slotCount_nonneg (x := x) u v (fun Q => (hB Q).1) h
  have hC0 := slotMean_nonneg (x := x) u v (fun Q => (hB Q).1)
  have hx1 : (1 : ℝ) < x := by linarith
  have hf := slotCount_le hx1 hc hT u v hB hadm.1 h1 hh
  have hu : ∀ i, 0 < u i := fun i => lt_of_lt_of_le (by positivity) (hadm.1 i)
  have hv : ∑ i, v i ≤ 1 := by
    have := hadm.2
    have : 0 ≤ c / logLog x ^ 20 := by positivity
    linarith
  have hC := slotMean_le hx1 u v hB hu hv
  have hsum := hE₂ x hx
  have hk3 : k + 1 ≤ 3 := by omega
  have hb1 : (2 * logLog x ^ 20 / c) ^ (k + 1) ≤ (2 * logLog x ^ 20 / c + 1) ^ 3 := by
    have h0 : 0 ≤ 2 * logLog x ^ 20 / c := by positivity
    calc (2 * logLog x ^ 20 / c) ^ (k + 1) ≤ (2 * logLog x ^ 20 / c + 1) ^ (k + 1) :=
          pow_le_pow_left₀ h0 (by linarith) _
      _ ≤ (2 * logLog x ^ 20 / c + 1) ^ 3 := pow_le_pow_right₀ (by linarith) hk3
  have hs0 : 0 ≤ ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p := sum_nonneg fun _ _ => by positivity
  have hb2 : (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (k + 1) ≤ (logLog x + E₂ + 1) ^ 3 := by
    calc (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (k + 1) ≤ (logLog x + E₂ + 1) ^ (k + 1) :=
          pow_le_pow_left₀ hs0 (by linarith) _
      _ ≤ (logLog x + E₂ + 1) ^ 3 := pow_le_pow_right₀ (by linarith) hk3
  unfold slotBound
  rw [abs_le]
  constructor <;> linarith

/-- The endpoint data at `x`. -/
theorem endpointData_of {q cw : ℝ} (hq : 0 < q) (hq₁ : q < 1) (hcw : 0 ≤ cw) (hcw₁ : cw ≤ 1)
    {K : ℕ} (hK : 1 ≤ K) {CN c E₂ x : ℝ} (hc : 0 < c) (hx : 2 ≤ x) (hL : 1 < Real.log x)
    (hT : 0 < logLog x)
    (hlay : 2 * ((inertPerCluster K CN x : ℝ) + 1) * K ≤ 4 / 100 * logLog x)
    (hV : ∀ a : ℝ, 1 / 10 ≤ a → 1 / 2 ≤ harmonicMass (band x a))
    (hsmall : Real.exp (2 * Real.log x ^ (19 / 100 : ℝ)) ≤ x ^ (c / logLog x ^ 20))
    (hE₂ : ∀ y : ℝ, 2 ≤ y → ∑ p ∈ primesIoc 1 y, (1 : ℝ) / p ≤ logLog y + E₂) (hE₂0 : 0 ≤ E₂)
    {k : ℕ} (hk : k ≤ 2) {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ}
    (hadm : AdmissibleSlots c x u v) (hB : ∀ Q, 0 ≤ B Q ∧ B Q ≤ 1) :
    EndpointData q cw K CN x u v B (normBound q K CN c E₂ x) where
  one_le_K := hK
  q_pos := hq
  log_gt := hL
  logLog_pos := hT
  layout := hlay
  small a ha p hp i := by
    have hL0 : 0 < Real.log x := by linarith
    have h1 : Real.log x ^ a ≤ Real.log x ^ (19 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL.le ha
    refine (band_le hp).trans ?_
    calc Real.exp (2 * Real.log x ^ a) ≤ Real.exp (2 * Real.log x ^ (19 / 100 : ℝ)) :=
          Real.exp_le_exp.2 (by linarith)
      _ ≤ x ^ (c / logLog x ^ 20) := hsmall
      _ ≤ x ^ u i := Real.rpow_le_rpow_of_exponent_le (by linarith) (hadm.1 i)
  norm_pos := by
    unfold normBound
    have h1 := slotBound_pos (E₂ := E₂) (x := x) hc hE₂0 hT.le
    have h2 : 0 < 1 - q := by linarith
    have h3 : 0 < 2 / (1 - q) := by positivity
    positivity
  rest_le S hS h h1 hh := by
    have hV' : ∀ (c : Fin K) i, i < inertPerCluster K CN x →
        1 / 2 ≤ harmonicMass (band x (inertExponent K x c i)) := fun c' i hi =>
      hV _ (by linarith [(inertExponent_mem hK hT hlay c'.isLt hi).1])
    refine (abs_monoRest_le hq hq₁ hcw hcw₁ u v B hS hV' h).trans ?_
    unfold normBound
    have h2 : 0 < 1 - q := by linarith
    have h3 : 0 ≤ (2 / (1 - q)) ^ (K * inertPerCluster K CN x) := by positivity
    exact mul_le_mul_of_nonneg_left (abs_slot_sub_le hx hc hT hE₂ hE₂0 hk hadm hB h1 hh) h3

/-- `|P (f_𝔟 - C_𝔟)| ≤ 2^{K N'} (2/(1-q))^K 𝒩` on `[1, x²]`. -/
theorem abs_endpoint_le {q cw : ℝ} (hq₁ : q < 1) {K : ℕ} {CN c E₂ x : ℝ} {k : ℕ}
    {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ}
    (hE : EndpointData q cw K CN x u v B (normBound q K CN c E₂ x))
    (hV : ∀ a : ℝ, 1 / 10 ≤ a → 1 / 2 ≤ harmonicMass (band x a)) {h : ℕ} (h1 : 1 ≤ h)
    (hh : (h : ℝ) ≤ x ^ 2) :
    |endpoint q cw K CN x u v B h| ≤ endBound q K CN c E₂ x := by
  have hq := hE.q_pos
  rw [endpoint_eq_sum q cw hq.ne' K CN x u v B]
  have hW : ∀ S ∈ clusterSets K (inertPerCluster K CN x),
      |markedWeight Finset.univ q (fun i => band x (distExponent K x S i)) h| ≤
        (2 / (1 - q)) ^ K := by
    intro S hS
    rw [markedWeight_eq_prod hq.ne', abs_prod]
    rw [show (2 / (1 - q)) ^ K = ∏ _i : Fin K, 2 / (1 - q) by
      rw [prod_const, card_univ, Fintype.card_fin]]
    refine prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
    have hd : distIndex S i < inertPerCluster K CN x :=
      mem_range.1 (((mem_clusterSets.1 hS) i).2 (distIndex_mem ((mem_clusterSets.1 hS) i).1))
    have hwin := inertExponent_mem hE.one_le_K hE.logLog_pos hE.layout i.isLt hd
    have hVi := hV (distExponent K x S i) (by unfold distExponent; linarith [hwin.1])
    rw [abs_of_nonneg (bandWeight_nonneg hq _ _ _)]
    refine (bandWeight_le hq hq₁ _ _ _ (by linarith)).trans ?_
    rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
    nlinarith
  calc _ ≤ ∑ S ∈ clusterSets K (inertPerCluster K CN x),
        |markedWeight Finset.univ q (fun i => band x (distExponent K x S i)) h *
          monoRest q cw K x u v B S h| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ clusterSets K (inertPerCluster K CN x),
          (2 / (1 - q)) ^ K * normBound q K CN c E₂ x := by
        refine sum_le_sum fun S hS => ?_
        rw [abs_mul]
        exact mul_le_mul (hW S hS) (hE.rest_le S hS h h1 hh) (abs_nonneg _) (by
          have : 0 < 1 - q := by linarith
          positivity)
    _ ≤ 2 ^ (K * inertPerCluster K CN x) * ((2 / (1 - q)) ^ K * normBound q K CN c E₂ x) := by
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (card_clusterSets_le _ _) (by
          have := hE.norm_pos
          have : 0 < 1 - q := by linarith
          positivity)
    _ = endBound q K CN c E₂ x := by unfold endBound; ring

end Erdos408.TypeII
