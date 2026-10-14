import Erdos821.S2.TailAbsorptionTask
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter

namespace Erdos821.S2Tail

open Erdos821.Blueprint.Graph

/-- The graph scales satisfy the crude polynomial bounds needed for the tail. -/
theorem tail_scale_bounds : ∀ᶠ x : ℝ in atTop,
    1 ≤ L x ∧ 0 ≤ T x ∧ T x ≤ (L x) ^ ((1 : ℝ) / 10) ∧
      (N x : ℝ) * T x ≤ 4 * L x ∧
      ((N x + 1 : ℕ) : ℝ) * T x ≤ 5 * L x := by
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  have hsmall : (fun x : ℝ => Real.log (L x)) =o[atTop]
      fun x => (L x) ^ ((1 : ℝ) / 10) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 10)).comp_tendsto hL
  filter_upwards [hL.eventually_ge_atTop 1, hsmall.bound (by norm_num : (0 : ℝ) < 1)] with x hx hsmallx
  have hLpos : 0 < L x := by linarith
  have hLnonneg : 0 ≤ L x := hLpos.le
  have hTnonneg : 0 ≤ T x := Real.log_nonneg hx
  have hlogNonneg : 0 ≤ Real.log (L x) := Real.log_nonneg hx
  have hpowNonneg : 0 ≤ (L x) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hLnonneg _
  have hTle : T x ≤ (L x) ^ ((1 : ℝ) / 10) := by
    change ‖Real.log (L x)‖ ≤ 1 * ‖(L x) ^ ((1 : ℝ) / 10)‖ at hsmallx
    have habs : |Real.log (L x)| ≤ 1 * |(L x) ^ ((1 : ℝ) / 10)| := by
      simpa only [Real.norm_eq_abs] using hsmallx
    rw [abs_of_nonneg hlogNonneg, abs_of_nonneg hpowNonneg] at habs
    simpa [T] using habs
  let w : ℝ := (L x) ^ ((52 : ℝ) / 100)
  have hwge : 1 ≤ w := by
    dsimp [w]
    exact Real.one_le_rpow hx (by norm_num)
  have hceil : (R x : ℝ) < w + 1 := by
    dsimp [R, w]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg hLnonneg _)
  have hN : (N x : ℝ) ≤ 4 * w := by
    calc
      (N x : ℝ) = 2 * (R x : ℝ) := by simp [N]
      _ ≤ 2 * (w + 1) := by nlinarith
      _ ≤ 4 * w := by nlinarith
  have hNplus : ((N x + 1 : ℕ) : ℝ) ≤ 5 * w := by
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hwpow : w * (L x) ^ ((1 : ℝ) / 10) ≤ L x := by
    have hadd : (52 : ℝ) / 100 + (1 : ℝ) / 10 ≤ 1 := by norm_num
    calc
      w * (L x) ^ ((1 : ℝ) / 10) = (L x) ^ ((52 : ℝ) / 100 + (1 : ℝ) / 10) := by
        dsimp [w]
        rw [← Real.rpow_add hLpos]
      _ ≤ (L x) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hadd
      _ = L x := Real.rpow_one _
  have hwt : w * T x ≤ L x := by
    calc
      w * T x ≤ w * (L x) ^ ((1 : ℝ) / 10) := mul_le_mul_of_nonneg_left hTle (by positivity)
      _ ≤ L x := hwpow
  have hNT : (N x : ℝ) * T x ≤ 4 * L x := by
    calc
      (N x : ℝ) * T x ≤ (4 * w) * T x := mul_le_mul_of_nonneg_right hN hTnonneg
      _ = 4 * (w * T x) := by ring
      _ ≤ 4 * L x := mul_le_mul_of_nonneg_left hwt (by norm_num)
  have hNplusT : ((N x + 1 : ℕ) : ℝ) * T x ≤ 5 * L x := by
    calc
      ((N x + 1 : ℕ) : ℝ) * T x ≤ (5 * w) * T x := mul_le_mul_of_nonneg_right hNplus hTnonneg
      _ = 5 * (w * T x) := by ring
      _ ≤ 5 * L x := mul_le_mul_of_nonneg_left hwt (by norm_num)
  exact ⟨hx, hTnonneg, hTle, hNT, hNplusT⟩

theorem TailAbsorptionTask_proof : Erdos821.S2Core.TailAbsorptionTask := by
  intro Ccap Cpath E hCcap hCpath hE
  let D : ℝ := 4 * Ccap * Real.log 2 + 5 * Cpath + 4 * E
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hDsmall : ∀ᶠ x : ℝ in atTop, D / Real.log 2 ≤ L x := by
    exact Real.tendsto_log_atTop.eventually_ge_atTop (D / Real.log 2)
  have hgood : ∀ᶠ x : ℝ in atTop, ∀ cap : ℕ,
      (cap : ℝ) ≤ Ccap * (N x : ℝ) * T x →
      (2 : ℝ) ^ ((cap : ℤ) - (memoryCutoff x : ℤ)) *
          (L x) ^ (Cpath * (N x + 1 : ℕ)) ≤
        (L x) ^ (-E * (N x : ℝ)) := by
    filter_upwards [tail_scale_bounds, hDsmall] with x hs hsD cap hcap
    rcases hs with ⟨hLone, hTnonneg, hTle, hNT, hNplusT⟩
    let n : ℝ := (N x : ℝ)
    let n1 : ℝ := ((N x + 1 : ℕ) : ℝ)
    let l : ℝ := L x
    let t : ℝ := T x
    have hnT : n * t ≤ 4 * l := by simpa [n, l, t] using hNT
    have hn1T : n1 * t ≤ 5 * l := by simpa [n1, l, t] using hNplusT
    have hcap' : (cap : ℝ) ≤ Ccap * n * t := by simpa [n, t] using hcap
    have hLpos : 0 < l := by dsimp [l]; linarith
    have hcut : l ^ (2 : ℕ) ≤ (memoryCutoff x : ℝ) := by
      dsimp [l, memoryCutoff]
      exact Nat.le_ceil _
    have hCcapLog : 0 ≤ Ccap * Real.log 2 := mul_nonneg hCcap.le hlog2.le
    have hE : 0 ≤ E := hE.le
    have htermCap : Ccap * n * t * Real.log 2 ≤ 4 * Ccap * Real.log 2 * l := by
      calc
        Ccap * n * t * Real.log 2 = (Ccap * Real.log 2) * (n * t) := by ring
        _ ≤ (Ccap * Real.log 2) * (4 * l) :=
          mul_le_mul_of_nonneg_left hnT hCcapLog
        _ = 4 * Ccap * Real.log 2 * l := by ring
    have htermPath : Cpath * n1 * t ≤ 5 * Cpath * l := by
      calc
        Cpath * n1 * t = Cpath * (n1 * t) := by ring
        _ ≤ Cpath * (5 * l) := mul_le_mul_of_nonneg_left hn1T hCpath
        _ = 5 * Cpath * l := by ring
    have htermE : E * n * t ≤ 4 * E * l := by
      calc
        E * n * t = E * (n * t) := by ring
        _ ≤ E * (4 * l) := mul_le_mul_of_nonneg_left hnT hE
        _ = 4 * E * l := by ring
    have hsum : Ccap * n * t * Real.log 2 + Cpath * n1 * t + E * n * t ≤ D * l := by
      dsimp [D]
      linarith [htermCap, htermPath, htermE]
    have hcapLog : (cap : ℝ) * Real.log 2 ≤ Ccap * n * t * Real.log 2 :=
      mul_le_mul_of_nonneg_right hcap' hlog2.le
    have hcutLog : l ^ (2 : ℕ) * Real.log 2 ≤
        (memoryCutoff x : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hcut hlog2.le
    have hDle : D ≤ Real.log 2 * l := by
      calc
        D ≤ l * Real.log 2 := (div_le_iff₀ hlog2).mp (by simpa [l] using hsD)
        _ = Real.log 2 * l := by ring
    have hDmul : D * l ≤ l ^ (2 : ℕ) * Real.log 2 := by
      calc
        D * l ≤ (Real.log 2 * l) * l := mul_le_mul_of_nonneg_right hDle hLpos.le
        _ = l ^ (2 : ℕ) * Real.log 2 := by ring
    have hExponent :
        (((cap : ℤ) - (memoryCutoff x : ℤ) : ℤ) : ℝ) * Real.log 2 +
          Cpath * n1 * t + E * n * t ≤ 0 := by
      have hcast : (((cap : ℤ) - (memoryCutoff x : ℤ) : ℤ) : ℝ) =
          (cap : ℝ) - (memoryCutoff x : ℝ) := by simp
      calc
        _ = ((cap : ℝ) - (memoryCutoff x : ℝ)) * Real.log 2 +
              Cpath * n1 * t + E * n * t := by rw [hcast]
        _ ≤ Ccap * n * t * Real.log 2 + Cpath * n1 * t + E * n * t -
              l ^ (2 : ℕ) * Real.log 2 := by nlinarith [hcapLog, hcutLog]
        _ ≤ D * l - l ^ (2 : ℕ) * Real.log 2 := by linarith [hsum]
        _ ≤ 0 := sub_nonpos.mpr hDmul
    have hBase : (2 : ℝ) ^ ((cap : ℤ) - (memoryCutoff x : ℤ)) =
        Real.exp (Real.log 2 *
          (((cap : ℤ) - (memoryCutoff x : ℤ) : ℤ) : ℝ)) := by
      rw [← Real.rpow_intCast (2 : ℝ) ((cap : ℤ) - (memoryCutoff x : ℤ))]
      exact Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _
    have hPowL (a : ℝ) : l ^ a = Real.exp (Real.log l * a) :=
      Real.rpow_def_of_pos hLpos a
    rw [hBase, hPowL, hPowL, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [show Real.log l = t by rfl]
    dsimp [n, n1, t, l] at hExponent ⊢
    nlinarith [hExponent]
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hgood
  exact ⟨x₀, fun x hx cap hcap => hx₀ x hx cap hcap⟩


end Erdos821.S2Tail
