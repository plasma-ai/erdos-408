import Erdos408.TwoSided.Endpoint.Constant

/-!
# Package E: the endpoint mean square

Interface E of `blueprint/two_sided_correlation.md` §3.3 (PD §§6.4–6.6, S11–S19): the Mellin
mean square (6.24) of the first endpoint of a comparison, with any additive twist `e(hw/k)`,
`k ≤ L^{C_m}`, is `O(L^{-A₀})` under the premises AP1 and AP2. Split `|t| ≤ T₀ = x L^{C_m + 2}`
at `L^{B'}`, with `B' = max(B_min, B_con) + |E|`:

* `|t| ≤ L^{B'}`: Lemma E2 with the divisor model E1 (`exists_integral_lowFrequency_le`).
* `L^{B'} ≤ |t| ≤ T₀`: `𝒰 = 𝒰_tup - 𝒰_con + (𝒰 - 𝒰_tup + 𝒰_con)`. The tuple part uses AP1
  and AP2 (`exists_integral_tuple_high_le`), the constant part is unconditional
  (`exists_integral_const_high_le`), and the remainder lives on the exceptional positions
  of E3–E4 (`exists_integral_removal_le`).

The premise precision `A'` comes from the tuple part and does not depend on `E` (§1.3).
-/

namespace Erdos408.TwoSided

open Filter

/-- **Interface E.** For the fixed data, `m₀`, `C_m`, `A₀` and the derivative bounds `M₁` of
the pieces there is `A'` such that for every `E, κ'` there is `C_E` with: eventually, under
`PrimeTwistBound x A' E C_m κ'` and `IntegerKernelBound x C_m κ'`, for all admissible data,
every pattern `C` with at most `m₀` free slots in the big groups, every test `b` that ignores
the small groups, every piece `ψ₁` supported in `[1, 2]`, scale
`Y ∈ [x e^{L^{0.38}}, x e^{L^{0.47}}]`, twist `|σ| ≤ L^{C_m}` and centre `h/k`, `k ≤ L^{C_m}`,
`∫_{|t| ≤ T₀} |Y⁻¹ ∑_w 𝒰(w) e(hw/k) w^{it}|² dt ≤ C_E L^{-A₀}`. -/
theorem exists_endpoint_meanSquare
    (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ) (d : ℕ)
    (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) (hc₀ : 0 < c₀)
    (hvlo : 0 < vlo) (halo : 1 / 10 < alo) (hal : alo ≤ ahi) (hahi : ahi < 1 / 5) (hc : 0 < c)
    (m₀ : ℕ) (Cm A₀ : ℝ) (M₁ : ℕ → ℝ) :
    ∃ A' : ℝ, ∀ E κ' : ℝ, ∃ CE : ℝ, ∀ᶠ x : ℝ in atTop,
      PrimeTwistBound x A' E Cm κ' → IntegerKernelBound x Cm κ' →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v → (∀ Q, |Bc Q| ≤ 1) →
        ∀ (J : ℕ) (C : ι → Finset (Fin J)) (b : (ι → Fin (J + 1) → ℕ) → ℂ),
          (∀ g, (C g).card ≤ m₀) → (∀ g ∉ big, C g = ∅) → (∀ p, ‖b p‖ ≤ 1) →
          (∀ p p', (∀ g ∈ big, p g = p' g) → b p = b p') →
        ∀ ψ₁ : ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁ →
          (∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) → (∀ (j : ℕ) (y : ℝ), ‖iteratedDeriv j ψ₁ y‖ ≤ M₁ j) →
        ∀ (Y σ : ℝ) (k : ℕ) (h : ℤ),
          x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ Y →
          Y ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ)) →
          |σ| ≤ Real.log x ^ Cm → 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm →
          ∫ t in -(x * Real.log x ^ (Cm + 2))..(x * Real.log x ^ (Cm + 2)),
              ‖(Y : ℂ)⁻¹ * ∑ w ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊,
                  endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ w *
                    Complex.exp (2 * Real.pi * Complex.I * (h * w / k : ℝ)) *
                    (w : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
            CE * Real.log x ^ (-A₀) := by
  obtain ⟨A', Bmin, htup⟩ := exists_integral_tuple_high_le q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d
    hq hq₁ hq₀ hq₀₁ hvlo halo hal hahi hc m₀ Cm A₀ M₁
  obtain ⟨Bcon, hcon⟩ := exists_integral_const_high_le q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d
    hq hq₁ hq₀ hq₀₁ hvlo halo hal hahi hc m₀ Cm A₀ M₁
  obtain ⟨CR, herr⟩ := exists_integral_removal_le q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d hq hq₁
    hq₀ hq₀₁ hvlo halo hal hahi hc m₀ Cm M₁
  refine ⟨A', fun E κ' => ?_⟩
  -- the split point `L^{B'}`
  set B' : ℝ := max Bmin Bcon + |E| with hB'
  have hB₁ : Bmin ≤ B' := by linarith [le_max_left Bmin Bcon, abs_nonneg E]
  have hB₂ : E + Bmin ≤ B' := by linarith [le_max_left Bmin Bcon, le_abs_self E]
  have hB₃ : Bcon ≤ B' := by linarith [le_max_right Bmin Bcon, abs_nonneg E]
  obtain ⟨CT, htupx⟩ := htup E κ' B' hB₁ hB₂
  obtain ⟨CK, hconx⟩ := hcon B' hB₃
  obtain ⟨CL, hlowx⟩ := exists_integral_lowFrequency_le q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d hq
    hq₁ hq₀ hq₀₁ hvlo halo hal hahi hc m₀ Cm A₀ M₁ B'
  refine ⟨CL + 6 * (|CT| + |CK| + 2), ?_⟩
  filter_upwards [htupx, hconx, hlowx, herr,
    OneSided.eventually_mul_rpow_mul_exp_le (by norm_num : (0 : ℝ) < 0.27) 1 CR A₀,
    eventually_exp_neg_margin_le hc (A₀ + CR), eventually_log_rpow_le_self B',
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0,
    Real.tendsto_log_atTop.eventually_gt_atTop 1, eventually_gt_atTop 0]
    with x htupx hconx hlowx herr he₁ he₂ hxB hT hL hx0
  intro hAP1 hAP2 ι _ _ P big hadm r a u v Bc hin hsl hBc J C b hC hCb hb hbb ψ₁ hψ hψs hψd Y σ
    k h hY₁ hY₂ hσ hk₁ hk₂
  simp only [Function.comp_apply] at hT
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY₁
  -- a small group
  obtain ⟨gs, hgs⟩ : ∃ gs, gs ∉ big := by
    have hcard : 0 < (Finset.univ \ big).card := by
      have := hadm.2.1
      exact_mod_cast lt_of_lt_of_le (mul_pos hc₀ hT) this
    obtain ⟨gs, hgs⟩ := Finset.card_pos.1 hcard
    exact ⟨gs, (Finset.mem_sdiff.1 hgs).2⟩
  -- the pieces
  set U := endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ
  set Ut := tupleCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ
  set Uc := constCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ
  set Ue : ℕ → ℂ := fun w => U w - Ut w + Uc w
  set T₀ := x * L ^ (Cm + 2)
  have hT₀ : L ^ B' ≤ T₀ := by
    have : 1 ≤ L ^ (Cm + 2) := by
      have hCm : 0 ≤ Cm := by
        by_contra hneg
        have : L ^ Cm < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk₁
        linarith
      exact Real.one_le_rpow hL.le (by linarith)
    calc L ^ B' ≤ x := hxB
      _ = x * 1 := (mul_one x).symm
      _ ≤ T₀ := mul_le_mul_of_nonneg_left this hx0.le
  have hLB : 0 ≤ L ^ B' := by positivity
  have hdec : U = fun w => Ut w - Uc w + Ue w := by
    funext w
    simp only [Ue]
    ring
  obtain ⟨ht₁, ht₂⟩ := htupx hAP1 hAP2 P big hadm gs hgs r a u v Bc hin hsl hBc J C b hC hCb hb
    hbb ψ₁ hψ hψs hψd Y σ k h hY₁ hY₂ hσ hk₁ hk₂
  obtain ⟨hc₁, hc₂⟩ := hconx P big hadm gs hgs r a u v Bc hin hsl hBc J C b hC hCb hb hbb ψ₁ hψ
    hψs hψd Y σ k h hY₁ hY₂ hσ hk₁ hk₂
  have hlo := hlowx P big hadm r a u v Bc hin hsl hBc J C b hC hb ψ₁ hψ hψs hψd Y σ k h hY₁
    hY₂ hσ hk₁ hk₂
  have he := herr P big hadm gs hgs r a u v Bc hin hsl hBc J C b hC hCb hb hbb ψ₁ hψ hψs hψd Y
    σ k h hY₁ hY₂ hσ hk₁ hk₂
  rw [one_mul] at he₁
  -- the remainder is at most `2 L^{-A₀}`
  have hemar : Real.exp (-(c * L / Real.log L ^ 20)) ≤ L ^ (-(A₀ + CR)) := he₂
  have hR : ∫ t in -T₀..T₀, ‖twistedPoly Y Ue h k t‖ ^ 2 ≤ 2 * L ^ (-A₀) := by
    refine he.trans ?_
    rw [mul_add]
    have : L ^ CR * Real.exp (-(c * L / Real.log L ^ 20)) ≤ L ^ (-A₀) := by
      calc L ^ CR * Real.exp (-(c * L / Real.log L ^ 20)) ≤ L ^ CR * L ^ (-(A₀ + CR)) := by
            gcongr
        _ = L ^ (-A₀) := by rw [← Real.rpow_add hL0]; ring_nf
    linarith
  -- each high range
  have hhigh : ∀ t₁ t₂ : ℝ, -T₀ ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T₀ →
      (∫ t in t₁..t₂, ‖twistedPoly Y Ut h k t‖ ^ 2) ≤ CT * L ^ (-A₀) →
      (∫ t in t₁..t₂, ‖twistedPoly Y Uc h k t‖ ^ 2) ≤ CK * L ^ (-A₀) →
      ∫ t in t₁..t₂, ‖twistedPoly Y U h k t‖ ^ 2 ≤ 3 * (|CT| + |CK| + 2) * L ^ (-A₀) := by
    intro t₁ t₂ h₁ h₁₂ h₂ hTt hCt
    rw [hdec]
    refine (integral_norm_twistedPoly_sub_add_le hY0 Ut Uc Ue h k h₁₂).trans ?_
    have hEt := (integral_norm_twistedPoly_sq_mono hY0 Ue h k h₁ h₁₂ h₂).trans hR
    have hp : 0 < L ^ (-A₀) := by positivity
    nlinarith [le_abs_self CT, le_abs_self CK]
  -- split `[-T₀, T₀]` at `±L^{B'}`
  have hi : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun t => ‖twistedPoly Y U h k t‖ ^ 2) MeasureTheory.volume t₁ t₂ :=
    fun t₁ t₂ => (continuous_norm_twistedPoly_sq hY0 U h k).intervalIntegrable t₁ t₂
  show ∫ t in -T₀..T₀, ‖twistedPoly Y U h k t‖ ^ 2 ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-T₀) (-(L ^ B')))
    (hi (-(L ^ B')) T₀), ← intervalIntegral.integral_add_adjacent_intervals
    (hi (-(L ^ B')) (L ^ B')) (hi (L ^ B') T₀)]
  have h₁ := hhigh (-T₀) (-(L ^ B')) le_rfl (by linarith) (by linarith) ht₂ hc₂
  have h₂ := hhigh (L ^ B') T₀ (by linarith) hT₀ le_rfl ht₁ hc₁
  linarith

end Erdos408.TwoSided
