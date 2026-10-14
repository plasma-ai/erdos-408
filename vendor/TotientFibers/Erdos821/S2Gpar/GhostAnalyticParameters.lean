import Erdos821.S2.AnalyticParametersTasks
import Erdos821.S34.ScaleGrowth

noncomputable section
open Filter
open scoped BigOperators

namespace Erdos821.S2Gpar

open Erdos821.Blueprint.Graph

theorem eventually_N_plus_one_le_half_exp (F : FixedData) :
    ∀ᶠ x : ℝ in atTop,
      (N x : ℝ) + 1 ≤ (1 / 2) * Real.exp ((L x) ^ F.c) := by
  have hc : 0 < F.c := lt_trans F.a_pos (lt_trans F.ab F.bc)
  have hscale₀ := Erdos821.S34Core.eventually_power_le_label_scale
    1 F.c (1 / 10) hc (by norm_num : (0 : ℝ) < 1 / 10)
  have hscale : ∀ᶠ x : ℝ in atTop,
      (L x) ^ (1 : ℝ) ≤ (1 / 10) * Real.exp ((L x) ^ F.c) := by
    filter_upwards [hscale₀] with x hx
    simpa [Erdos821.Blueprint.Analytic.L, Erdos821.Blueprint.Graph.L] using hx
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [hscale, hL.eventually_ge_atTop 1] with x hx hLx
  have hLpow : (L x) ^ (1 : ℝ) = L x := Real.rpow_one _
  have hscale' : L x ≤ (1 / 10) * Real.exp ((L x) ^ F.c) := by
    simpa only [hLpow] using hx
  have hpow₀ : (L x) ^ ((52 : ℝ) / 100) ≤ (L x) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hLx (by norm_num : (52 : ℝ) / 100 ≤ 1)
  have hpow : (L x) ^ ((52 : ℝ) / 100) ≤ L x := by
    simpa only [Real.rpow_one] using hpow₀
  have hceil : (R x : ℝ) < (L x) ^ ((52 : ℝ) / 100) + 1 := by
    dsimp [R]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith) _)
  have hR : (R x : ℝ) ≤ L x + 1 := by
    calc
      (R x : ℝ) ≤ (L x) ^ ((52 : ℝ) / 100) + 1 := hceil.le
      _ ≤ L x + 1 := by simpa [add_comm] using add_le_add_right hpow 1
  have hN : (N x : ℝ) + 1 ≤ 5 * L x := by
    dsimp [N]
    push_cast
    calc
      2 * (R x : ℝ) + 1 ≤ 2 * (L x + 1) + 1 := by
        gcongr
      _ ≤ 5 * L x := by nlinarith [hLx]
  calc
    (N x : ℝ) + 1 ≤ 5 * L x := hN
    _ ≤ (1 / 2) * Real.exp ((L x) ^ F.c) := by
      calc
        5 * L x ≤ 5 * ((1 / 10) * Real.exp ((L x) ^ F.c)) :=
          mul_le_mul_of_nonneg_left hscale' (by norm_num)
        _ = (1 / 2) * Real.exp ((L x) ^ F.c) := by ring

theorem baselinePrime_ge_half_of_scale
    (F : FixedData) (x : ℝ) (p : ℕ)
    (_hL : 1 ≤ L x)
    (hN : (N x : ℝ) + 1 ≤ (1 / 2) * Real.exp ((L x) ^ F.c))
    (hp : Real.exp ((L x) ^ F.c) ≤ (p : ℝ))
    (hppos : 0 < (p : ℝ)) :
    1 / 2 ≤ baselinePrime F (N x) p := by
  have heta (i : Fin (N x + 1)) : eta F (N x) i ≤ 1 := by
    unfold eta
    have hv : 0 ≤ visitQ F.q (N x) i := by
      unfold visitQ
      split
      · exact Real.sqrt_nonneg _
      · exact F.q_pos.le
    linarith
  have hsum :
      (∑ i : Fin (N x + 1), eta F (N x) i) ≤ ((N x + 1 : ℕ) : ℝ) := by
    calc
      (∑ i : Fin (N x + 1), eta F (N x) i) ≤
          ∑ _i : Fin (N x + 1), (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => heta i)
      _ = ((N x + 1 : ℕ) : ℝ) := by simp
  have hN' : ((N x + 1 : ℕ) : ℝ) ≤ (1 / 2) * Real.exp ((L x) ^ F.c) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hN
  have hpHalf : ((N x + 1 : ℕ) : ℝ) ≤ (p : ℝ) / 2 := by
    calc
      ((N x + 1 : ℕ) : ℝ) ≤ Real.exp ((L x) ^ F.c) / 2 := by nlinarith [hN']
      _ ≤ (p : ℝ) / 2 := div_le_div_of_nonneg_right hp (by norm_num)
  have hinvprod : (p : ℝ)⁻¹ * ((N x + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hpHalf (inv_nonneg.mpr hppos.le)
    have heq : (p : ℝ)⁻¹ * ((p : ℝ) / 2) = 1 / 2 := by
      field_simp [ne_of_gt hppos]
    rw [heq] at hmul
    exact hmul
  have hprod :
      (p : ℝ)⁻¹ * (∑ i : Fin (N x + 1), eta F (N x) i) ≤ 1 / 2 := by
    calc
      _ ≤ (p : ℝ)⁻¹ * ((N x + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hppos.le)
      _ ≤ 1 / 2 := hinvprod
  unfold baselinePrime
  linarith

theorem GhostAnalyticParametersTask_proof :
    ∀ (F : FixedData) (r : MemoryParameters F),
      Erdos821.S2Core.GhostAnalyticParametersTask F r := by
  intro F r
  let Acoef : ℝ := 4 * max 1 F.vMax * r.v / r.rho
  let Cv : ℝ := Acoef * F.C₀
  have hmax : 0 < max 1 F.vMax := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hv : 0 < r.v := lt_trans zero_lt_one r.v_gt
  have hAcoefPos : 0 < Acoef := by
    dsimp [Acoef]
    exact div_pos (mul_pos (mul_pos (by norm_num) hmax) hv) r.rho_pos
  have hAcoef : 0 ≤ Acoef := hAcoefPos.le
  have hCv : 0 ≤ Cv := by dsimp [Cv]; exact mul_nonneg hAcoef F.C₀_pos.le
  have hscale := eventually_N_plus_one_le_half_exp F
  have hgood : ∀ᶠ x : ℝ in atTop,
      Real.exp 1 ≤ x ∧ (N x : ℝ) + 1 ≤ (1 / 2) * Real.exp ((L x) ^ F.c) := by
    filter_upwards [hscale, eventually_ge_atTop (Real.exp 1)] with x hxscale hxexp
    exact ⟨hxexp, hxscale⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hgood
  refine ⟨Cv, hCv, x₀, ?_⟩
  intro x hx P hP
  rcases hx₀ x hx with ⟨hxexp, hN⟩
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hxexp
  have hL : 1 ≤ L x := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hxexp
    simpa only [L, Real.log_exp] using hlog
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL
  rcases hP with ⟨_, _, _, hBigCount, hV, hPrime⟩
  have hVpos : ∀ g : P.Group, 0 < P.V g ∧ P.V g ≤ F.vMax := by
    intro g
    rcases hV g with ⟨hlo, hhi⟩
    exact ⟨lt_of_lt_of_le F.vMin_pos hlo, hhi⟩
  have hBaselineHalf : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      (1 / 2 : ℝ) ≤ baselinePrime F (N x) p.val := by
    intro g p
    have hrange := hPrime g.val p.val p.property
    rw [g.property] at hrange
    have hpLower : Real.exp ((L x) ^ F.c) ≤ (p.val : ℝ) := hrange.1
    have hpPos : 0 < (p.val : ℝ) := by
      exact_mod_cast (P.prime g.val p.val p.property).pos
    exact baselinePrime_ge_half_of_scale F x p.val hL hN hpLower hpPos
  have hBaseline : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      0 < baselinePrime F (N x) p.val := by
    intro g p
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hBaselineHalf g p)
  refine ⟨hVpos, ?_, ?_, ?_⟩
  · exact hBaseline
  · intro g
    have hVg : 0 < P.V g.val := (hVpos g.val).1
    calc
      (∑ p : P.Prime g.val, tiltedMu F P (N x) g.val p) ≤
          ∑ p : P.Prime g.val,
            2 * (P.V g.val)⁻¹ * (p.val : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p _
        have hpPos : 0 < (p.val : ℝ) := by
          exact_mod_cast (P.prime g.val p.val p.property).pos
        have hbase := hBaselineHalf g p
        have hden : P.V g.val * (p.val : ℝ) * (1 / 2) ≤
            P.V g.val * (p.val : ℝ) * baselinePrime F (N x) p.val := by
          have hmul := mul_le_mul_of_nonneg_left hbase
            (mul_nonneg hVg.le hpPos.le)
          simpa [mul_assoc] using hmul
        have hminPos : 0 < P.V g.val * (p.val : ℝ) * (1 / 2) := by positivity
        have hmaxPos : 0 < P.V g.val * (p.val : ℝ) *
            baselinePrime F (N x) p.val := by positivity
        calc
          tiltedMu F P (N x) g.val p =
              (P.V g.val * (p.val : ℝ) * baselinePrime F (N x) p.val)⁻¹ := rfl
          _ ≤ (P.V g.val * (p.val : ℝ) * (1 / 2))⁻¹ :=
            (inv_le_inv₀ hmaxPos hminPos).mpr hden
          _ = 2 * (P.V g.val)⁻¹ * (p.val : ℝ)⁻¹ := by
            field_simp [ne_of_gt hVg, ne_of_gt hpPos] <;> ring
      _ = 2 * (P.V g.val)⁻¹ *
          (∑ p : P.Prime g.val, (p.val : ℝ)⁻¹) := by
        rw [← Finset.mul_sum]
      _ = 2 := by
        have hVsum : (∑ p : P.Prime g.val, (p.val : ℝ)⁻¹) = P.V g.val := by
          change (∑ p ∈ (P.primes g.val).attach, (p.val : ℝ)⁻¹) =
            ∑ p ∈ P.primes g.val, (p : ℝ)⁻¹
          exact Finset.sum_attach (P.primes g.val) (fun p : ℕ => (p : ℝ)⁻¹)
        rw [hVsum]
        field_simp [ne_of_gt hVg]
  · calc
      (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card =
          Real.exp (Acoef * (P.bigGroups.card : ℝ)) := by
            dsimp [Acoef]
            rw [← Real.exp_nat_mul]
            congr 1 <;> ring
      _ ≤ Real.exp (Acoef * (F.C₀ * T x)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hBigCount hAcoef
      _ = (L x) ^ Cv := by
        rw [Real.rpow_def_of_pos hLpos]
        congr 1
        dsimp [Cv, Acoef, T, L]
        ring

example (F : FixedData) (r : MemoryParameters F) :
    Erdos821.S2Core.GhostAnalyticParametersTask F r :=
  GhostAnalyticParametersTask_proof F r


end Erdos821.S2Gpar
