import Erdos821.P4Probe.CostParameters

set_option autoImplicit false
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

lemma normBound_mono {α : Type*} (mass : α → ℝ) (K : α → α → ℂ)
    {C D : ℝ} (hK : NormBound mass K C) (hCD : C ≤ D) : NormBound mass K D := by
  intro s t f g
  exact (hK s t f g).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

lemma eventual_group_bounds (F : FixedData) :
    ∀ᶠ x : ℝ in atTop, 2 ≤ L x ∧
      ∀ P : PrimeGroups, P.Admissible F x →
        3 ≤ Fintype.card P.BigGroup ∧
        (∀ g, 0 < P.V g) ∧
        (Fintype.card P.BigGroup : ℝ) ≤ F.C₀ * T x := by
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  have hT : Tendsto T atTop atTop := Real.tendsto_log_atTop.comp hL
  filter_upwards [hL.eventually_ge_atTop 2, hT.eventually_ge_atTop (3 / F.c₀)] with x hx htx
  refine ⟨hx, ?_⟩
  intro P hP
  have hn : (3 : ℝ) ≤ (Fintype.card P.BigGroup : ℝ) := by
    rw [bigGroup_card]
    calc
      _ = F.c₀ * (3 / F.c₀) := by field_simp [F.c₀_pos.ne']
      _ ≤ F.c₀ * T x := mul_le_mul_of_nonneg_left htx F.c₀_pos.le
      _ ≤ _ := hP.2.2.1
  exact ⟨by exact_mod_cast hn,
    fun g => F.vMin_pos.trans_le (hP.2.2.2.2.1 g).1,
    by simpa only [bigGroup_card] using hP.2.2.2.1⟩

/-- Assembly of the exact construction once the two pure finite tasks are
proved. Parameters and C1 precede J0, as required by thm:ideal. -/
theorem symmetricProbeTask_of_finite (hsym : SymmetricFullComponentTask)
    (hcancel : FiniteProbeCancellationTask) : SymmetricProbeTask := by
  intro hc F E C₄ hE hC₄
  obtain ⟨m, hm, hbpos, hb1, hblog⟩ :=
    exists_small_probe_beta F.ell F.ell_pos F.c₀ E F.c₀_pos hE
  let A : ℝ := E + 2 + (m : ℝ) * F.C₀ * Real.log 3
  have hC₀ : 0 < F.C₀ := F.C₀_pos
  have hA : 0 < A := by
    have : 0 ≤ (m : ℝ) * F.C₀ * Real.log 3 :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    dsimp [A]
    linarith
  obtain ⟨q, h, ξ, hq, hh, hξ, hcomp⟩ :=
    localComparison_of_estimate F m A C₄ hA hC₄ hc
  let J₀ := m + (m + F.ell) * (m + F.ell - 1)
  let C₁ : ℝ := (m : ℝ) * F.C₀ * Real.log 2 + 4 * q + 2 * ξ + 1
  refine ⟨m, J₀, C₁, q, h, ξ, hq, hh, hξ, ?_⟩
  intro J hJ
  have hmJ : m ≤ J := by dsimp [J₀] at hJ; omega
  have hlarge : (m + F.ell) * (m + F.ell - 1) ≤ J + F.ell := by
    dsimp [J₀] at hJ
    omega
  filter_upwards [hcomp, eventual_group_bounds F] with x hx hbounds
  intro P hP hint
  obtain ⟨hn, hv, hnupper⟩ := hbounds.2 P hP
  obtain ⟨block, hblock⟩ := balanced_block_lower (α := P.BigGroup) hn
  let B := probeFamily F P J m hmJ block ⌊L x ^ q⌋₊ (L x ^ (-h)) (L x ^ (-ξ))
  refine ⟨B, probeFamily_residual F P J m hmJ block _ _ _, ?_, ?_⟩
  · exact family_cost_power F P J m hmJ block x q h ξ hbounds.1 hq hξ hnupper
  · intro θ ζ hζ
    have hB := hcancel hsym F P J m hmJ block ⌊L x ^ q⌋₊
      (L x ^ (-h)) (L x ^ (-ξ)) θ ζ (L x ^ (-A)) hv hm hlarge
      (Real.rpow_nonneg (by linarith [hbounds.1]) _) (hx P hP hint ζ hζ)
    apply normBound_mono _ _ hB
    have hfull (side : Bool) :
        Real.sqrt (probeBeta F.ell m ^
          (Finset.univ.filter (fun g : P.BigGroup => block g = side)).card) ≤
        L x ^ (-(E + 2)) := by
      apply sqrt_beta_power_le _ F.c₀ E _ _ hbpos hb1 F.c₀_pos
        (by linarith [hbounds.1]) hblog
      calc
        _ ≤ (Fintype.card P.BigGroup : ℝ) / 3 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          simpa only [bigGroup_card, T] using hP.2.2.1
        _ ≤ _ := hblock side
    have herr : (3 : ℝ) ^ (m * Fintype.card P.BigGroup) * L x ^ (-A) ≤
        L x ^ (-(E + 2)) := by
      have hpow := probe_power_le 3 F.C₀ m (Fintype.card P.BigGroup) (L x)
        (by norm_num) (by linarith [hbounds.1]) hnupper
      calc
        _ ≤ L x ^ ((m : ℝ) * F.C₀ * Real.log 3) * L x ^ (-A) :=
          mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by linarith [hbounds.1]) _)
        _ = _ := by
          rw [← Real.rpow_add (by linarith [hbounds.1] : 0 < L x)]
          congr 1
          dsimp [A]
          ring
    have hsum := add_le_add (add_le_add (hfull false) (hfull true)) herr
    exact hsum.trans (by
      convert three_errors_le (L x) E hbounds.1 using 1 <;> ring)

end
end Erdos821.P4Probe
