import Erdos821.S2.AnalyticParametersTasks
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open Filter
open Asymptotics

namespace Erdos821.S2Nondiv

open Erdos821.S2
open Erdos821.S2Core

/-- A fixed logarithmic power is eventually smaller than an exponential of a
positive power of the logarithm. -/
theorem log_power_lt_exp_power_eventually (c C : ℝ) (hc : 0 < c) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, (L x) ^ C < Real.exp ((L x) ^ c) := by
  have hlittle : (fun t : ℝ => Real.log t) =o[atTop] fun t => t ^ c :=
    isLittleO_log_rpow_atTop hc
  let m : ℕ := Nat.ceil |C| + 1
  have hcoeff : |C| < (m : ℝ) := by
    dsimp [m]
    calc
      |C| ≤ (Nat.ceil |C| : ℝ) := Nat.le_ceil _
      _ < (Nat.ceil |C| : ℝ) + 1 := by linarith
      _ = ((Nat.ceil |C| + 1 : ℕ) : ℝ) := by simp
  have hbound : ∀ᶠ t : ℝ in atTop, (m : ℝ) * ‖Real.log t‖ ≤ ‖t ^ c‖ :=
    (isLittleO_iff_nat_mul_le').1 hlittle m
  have hlarge : ∀ᶠ t : ℝ in atTop,
      (m : ℝ) * ‖Real.log t‖ ≤ ‖t ^ c‖ ∧ 1 < t :=
    hbound.and (eventually_gt_atTop 1)
  obtain ⟨T, hT⟩ := (eventually_atTop.1 hlarge)
  refine ⟨Real.exp T, ?_⟩
  intro x hx
  have hTx : T ≤ L x := by
    change T ≤ Real.log x
    calc
      T = Real.log (Real.exp T) := by simp
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos T) hx
  have hT' := hT (L x) hTx
  rcases hT' with ⟨hTbound, hTpos⟩
  have hlogpos : 0 < Real.log (L x) := Real.log_pos hTpos
  have hLpos : 0 < L x := by linarith
  have hpowpos : 0 < (L x) ^ c := Real.rpow_pos_of_pos hLpos c
  have hTbound' : (m : ℝ) * Real.log (L x) ≤ (L x) ^ c := by
    simpa only [Real.norm_eq_abs, abs_of_pos hlogpos, abs_of_pos hpowpos] using hTbound
  have hgap : C * Real.log (L x) < (L x) ^ c := by
    calc
      C * Real.log (L x) ≤ |C| * Real.log (L x) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (le_of_lt hlogpos)
      _ < (m : ℝ) * Real.log (L x) := mul_lt_mul_of_pos_right hcoeff hlogpos
      _ ≤ (L x) ^ c := hTbound'
  rw [Real.rpow_def_of_pos hLpos C]
  exact Real.exp_lt_exp.mpr (by simpa [mul_comm] using hgap)

/-- A prime in a big group eventually exceeds every prescribed power of `log x`,
so it cannot divide a nonzero integer of that size. -/
theorem BigPrimeNondivTask_proof : BigPrimeNondivTask := by
  intro F C₂
  have hc : 0 < F.c := lt_trans (lt_trans F.a_pos F.ab) F.bc
  obtain ⟨x₀, hxlarge⟩ := log_power_lt_exp_power_eventually F.c C₂ hc
  refine ⟨x₀, ?_⟩
  intro x hx P hP k hk hsize g p hdiv
  have hAd := hP.2.2.2.2.2 g.val p.val p.property
  rw [g.property] at hAd
  have hpLower : Real.exp ((L x) ^ F.c) ≤ (p.val : ℝ) := hAd.1
  have hprimeLarge : (L x) ^ C₂ < (p.val : ℝ) :=
    lt_of_lt_of_le (hxlarge x hx) hpLower
  have hsize' : (|k| : ℝ) < (p.val : ℝ) := lt_of_le_of_lt hsize hprimeLarge
  have hdivAbs : (p.val : ℤ) ∣ |k| := (dvd_abs _ _).2 hdiv
  have hdivBound : (p.val : ℤ) ≤ |k| := Int.le_of_dvd hk hdivAbs
  have hdivBound' : (p.val : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hdivBound
  linarith


end Erdos821.S2Nondiv
