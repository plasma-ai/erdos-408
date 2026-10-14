import Mathlib
import OAI.NumberTheory.PrimeGaps.Main
import OAI.NumberTheory.PrimeGaps.MangoldtBounds
import Erdos821.Blueprint.Classical

open scoped BigOperators
open Filter MeasureTheory

namespace Erdos821.DivisorHarmonic

open OAI.LargePrimeGaps

/-- Siegel--Walfisz for a nonprincipal character at an arbitrary level,
with the explicit cost of removing primes dividing the level. -/
theorem primeCharacterError_nonprincipal_bound (A B : ℝ)
    (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∀ y : ℝ, ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q,
      0 < q → 2 ≤ y → 1 ≤ Real.log y →
      (Real.log y) ^ (2 * A + 2) ≤ y →
      (q : ℝ) ≤ (Real.log y) ^ B → χ ≠ 1 →
      ‖primeCharacterError y χ‖ ≤
        M * y * (Real.log y) ^ (-A) +
          (Nat.log 2 ⌊y⌋₊ : ℝ) * Real.log q := by
  obtain ⟨M, hM, hbound⟩ := primeCharacterError_log_bound A B hA hB
  refine ⟨M, hM, ?_⟩
  intro y q χ hq hy hlog hpower hqlog hχ
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hcond : (χ.conductor : ℝ) ≤ (Real.log y) ^ B := by
    calc
      (χ.conductor : ℝ) ≤ q := by
        exact_mod_cast Nat.le_of_dvd hq χ.conductor_dvd_level
      _ ≤ (Real.log y) ^ B := hqlog
  letI : NeZero χ.conductor :=
    ⟨Nat.ne_of_gt (Nat.pos_of_dvd_of_pos χ.conductor_dvd_level hq)⟩
  have hprim : χ.primitiveCharacter ≠ 1 := by
    intro h
    exact hχ ((primitiveCharacter_eq_one_iff hq χ).mp h)
  have hmain := hbound χ.conductor χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive y hy hlog hpower hcond
  calc
    ‖primeCharacterError y χ‖ ≤
        ‖primeCharacterError y χ.primitiveCharacter‖ +
          (Nat.log 2 ⌊y⌋₊ : ℝ) * Real.log q :=
      primeCharacterError_le_primitive y hq χ
    _ ≤ M * y * (Real.log y) ^ (-A) +
          (Nat.log 2 ⌊y⌋₊ : ℝ) * Real.log q := by
      exact add_le_add hmain le_rfl

/-- The character sum weighted by the Chebyshev theta coefficients. -/
noncomputable def thetaCharacterPrefix {q : ℕ}
    (y : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, χ (n : ZMod q) * (theta n : ℂ)

/-- Replacing von Mangoldt weights by prime logarithmic weights costs at most
the elementary prime-power error. -/
theorem thetaCharacterPrefix_norm_le {q : ℕ} (y : ℝ)
    (χ : DirichletCharacter ℂ q) (hy : 1 ≤ y) (hχ : χ ≠ 1) :
    ‖thetaCharacterPrefix y χ‖ ≤
      ‖primeCharacterError y χ‖ + 2 * Real.sqrt y * Real.log y := by
  let X : ℕ := ⌊y⌋₊
  have hX : 1 ≤ X := by
    apply (Nat.le_floor_iff (show 0 ≤ y by linarith)).2
    exact_mod_cast hy
  have hXreal : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXle : (X : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hsum :
      primeCharacterPrefix y χ - thetaCharacterPrefix y χ =
        ∑ n ∈ Finset.Ioc 0 X,
          χ (n : ZMod q) *
            ((ArithmeticFunction.vonMangoldt n - theta n : ℝ) : ℂ) := by
    simp only [primeCharacterPrefix, thetaCharacterPrefix, X]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    rw [← mul_sub]
  have hdiff :
      ‖primeCharacterPrefix y χ - thetaCharacterPrefix y χ‖ ≤
        2 * Real.sqrt (X : ℝ) * Real.log (X : ℝ) := by
    rw [hsum]
    calc
      ‖∑ n ∈ Finset.Ioc 0 X,
          χ (n : ZMod q) *
            ((ArithmeticFunction.vonMangoldt n - theta n : ℝ) : ℂ)‖ ≤
          ∑ n ∈ Finset.Ioc 0 X,
            ‖χ (n : ZMod q) *
              ((ArithmeticFunction.vonMangoldt n - theta n : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ioc 0 X,
            (ArithmeticFunction.vonMangoldt n - theta n : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnonneg :
              0 ≤ ArithmeticFunction.vonMangoldt n - theta n :=
            sub_nonneg.mpr (theta_le_vonMangoldt n)
          calc
            ‖χ (n : ZMod q) *
                ((ArithmeticFunction.vonMangoldt n - theta n : ℝ) : ℂ)‖ =
                ‖χ (n : ZMod q)‖ *
                  ‖((ArithmeticFunction.vonMangoldt n - theta n : ℝ) : ℂ)‖ :=
                    norm_mul _ _
            _ = ‖χ (n : ZMod q)‖ *
                  (ArithmeticFunction.vonMangoldt n - theta n : ℝ) := by
                    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
            _ ≤ 1 * (ArithmeticFunction.vonMangoldt n - theta n : ℝ) :=
              mul_le_mul_of_nonneg_right (χ.norm_le_one _) hnonneg
            _ = ArithmeticFunction.vonMangoldt n - theta n := by ring
      _ = Chebyshev.psi (X : ℝ) - Chebyshev.theta (X : ℝ) :=
        sum_vonMangoldt_sub_theta X
      _ ≤ 2 * Real.sqrt (X : ℝ) * Real.log (X : ℝ) :=
        Chebyshev.psi_sub_theta_le hXreal
  have hlogXnonneg : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hXreal
  have hlogXle : Real.log (X : ℝ) ≤ Real.log y :=
    Real.log_le_log (by linarith) hXle
  have hsqrtXle : Real.sqrt (X : ℝ) ≤ Real.sqrt y := Real.sqrt_le_sqrt hXle
  have hmain :
      2 * Real.sqrt (X : ℝ) * Real.log (X : ℝ) ≤
        2 * Real.sqrt y * Real.log y := by
    have hprod := mul_le_mul hsqrtXle hlogXle hlogXnonneg (Real.sqrt_nonneg y)
    calc
      2 * Real.sqrt (X : ℝ) * Real.log (X : ℝ) =
          2 * (Real.sqrt (X : ℝ) * Real.log (X : ℝ)) := by ring
      _ ≤ 2 * (Real.sqrt y * Real.log y) := mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 2 * Real.sqrt y * Real.log y := by ring
  have herr : ‖primeCharacterError y χ‖ = ‖primeCharacterPrefix y χ‖ := by
    simp [primeCharacterError, hχ]
  calc
    ‖thetaCharacterPrefix y χ‖ =
        ‖primeCharacterPrefix y χ -
          (primeCharacterPrefix y χ - thetaCharacterPrefix y χ)‖ := by
            congr 1
            ring
    _ ≤ ‖primeCharacterPrefix y χ‖ +
          ‖primeCharacterPrefix y χ - thetaCharacterPrefix y χ‖ := norm_sub_le _ _
    _ ≤ ‖primeCharacterError y χ‖ + 2 * Real.sqrt y * Real.log y := by
      rw [herr]
      exact add_le_add (le_rfl) (hdiff.trans hmain)

/-- Uniform power saving for the theta-character prefix of nonprincipal characters. -/
theorem thetaCharacterPrefix_log_bound (A B : ℝ)
    (hA : 0 < A) (hB : 0 < B) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ y : ℝ in atTop,
      ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q,
        0 < q → (q : ℝ) ≤ (Real.log y) ^ B → χ ≠ 1 →
        ‖thetaCharacterPrefix y χ‖ ≤ K * y * (Real.log y) ^ (-A) := by
  let c₀ : ℝ := (Real.log 2)⁻¹
  have hc₀ : 0 < c₀ := by
    dsimp [c₀]
    positivity
  obtain ⟨M, hM, hSW⟩ :=
    primeCharacterError_nonprincipal_bound (A + 1) B (by linarith) hB
  have hlogEvent : ∀ᶠ y : ℝ in atTop, 2 ≤ Real.log y := by
    filter_upwards [eventually_ge_atTop (Real.exp 2)] with y hy
    calc
      2 = Real.log (Real.exp 2) := by simp
      _ ≤ Real.log y := Real.log_le_log (Real.exp_pos _) hy
  have hSWPowerEvent : ∀ᶠ y : ℝ in atTop,
      (Real.log y) ^ (2 * (A + 1) + 2) ≤ y := by
    simpa only [Real.rpow_one] using
      (eventually_log_rpow_le_rpow (2 * (A + 1) + 2) (by norm_num : (0 : ℝ) < 1))
  have hConductorPowerEvent : ∀ᶠ y : ℝ in atTop,
      (Real.log y) ^ (A + B + 3) ≤ Real.sqrt y := by
    filter_upwards [eventually_log_rpow_le_rpow (A + B + 3)
      (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))] with y hy
    simpa only [Real.sqrt_eq_rpow] using hy
  have hPrimePowerEvent : ∀ᶠ y : ℝ in atTop,
      (Real.log y) ^ (A + 2) ≤ Real.sqrt y := by
    filter_upwards [eventually_log_rpow_le_rpow (A + 2)
      (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))] with y hy
    simpa only [Real.sqrt_eq_rpow] using hy
  have hLargeEvent : ∀ᶠ y : ℝ in atTop, c₀ ^ 2 ≤ y :=
    eventually_ge_atTop (c₀ ^ 2)
  have hEvents : ∀ᶠ y : ℝ in atTop,
      2 ≤ Real.log y ∧
      (Real.log y) ^ (2 * (A + 1) + 2) ≤ y ∧
      (Real.log y) ^ (A + B + 3) ≤ Real.sqrt y ∧
      (Real.log y) ^ (A + 2) ≤ Real.sqrt y ∧ c₀ ^ 2 ≤ y := by
    filter_upwards [hlogEvent, hSWPowerEvent, hConductorPowerEvent,
      hPrimePowerEvent, hLargeEvent] with y hlog hSWp hCp hPp hlarge
    exact ⟨hlog, hSWp, hCp, hPp, hlarge⟩
  refine ⟨M + 2, by linarith, ?_⟩
  filter_upwards [hEvents] with y hY
  rcases hY with ⟨hLtwo, hSWpower, hCpower, hPpower, hlarge⟩
  intro q χ hq hqlog hχ
  let L : ℝ := Real.log y
  have hLtwo' : 2 ≤ L := by simpa [L] using hLtwo
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hypos : 0 < y := by
    have hc₀sq : 0 < c₀ ^ 2 := sq_pos_of_pos hc₀
    exact lt_of_lt_of_le hc₀sq hlarge
  have hSWpower' : L ^ (2 * (A + 1) + 2) ≤ y := by
    simpa [L] using hSWpower
  have hYexp : Real.exp L = y := by
    dsimp [L]
    exact Real.exp_log hypos
  have hYtwo : 2 ≤ y := by
    calc
      2 ≤ Real.exp 2 := by
        have h := Real.add_one_le_exp 2
        linarith
      _ ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
      _ = y := hYexp
  have hlog1 : 1 ≤ Real.log y := by simpa [L] using hLone
  have herror := hSW y q χ hq hYtwo hlog1 hSWpower' hqlog hχ
  have htheta := thetaCharacterPrefix_norm_le y χ (by linarith) hχ
  have hXone : 1 ≤ ⌊y⌋₊ := by
    apply (Nat.le_floor_iff (show 0 ≤ y by linarith)).2
    exact_mod_cast (show (1 : ℝ) ≤ y by linarith)
  have hXne : ⌊y⌋₊ ≠ 0 := by omega
  have hXle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hNatPow : 2 ^ Nat.log 2 ⌊y⌋₊ ≤ ⌊y⌋₊ :=
    Nat.pow_log_le_self 2 hXne
  have hNatPowReal : (2 : ℝ) ^ Nat.log 2 ⌊y⌋₊ ≤ (⌊y⌋₊ : ℝ) := by
    exact_mod_cast hNatPow
  have hNatLogMul :
      (Nat.log 2 ⌊y⌋₊ : ℝ) * Real.log 2 ≤ L := by
    calc
      _ = Real.log ((2 : ℝ) ^ Nat.log 2 ⌊y⌋₊) := by
        rw [Real.log_pow]
      _ ≤ Real.log y :=
        Real.log_le_log (by positivity) (hNatPowReal.trans hXle)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNatLog :
      (Nat.log 2 ⌊y⌋₊ : ℝ) ≤ L / Real.log 2 := by
    apply (le_div_iff₀ hlog2pos).2
    simpa [mul_comm] using hNatLogMul
  have hqone : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
  have hqreal : 1 ≤ (q : ℝ) := by exact_mod_cast hqone
  have hlogqnonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqreal
  have hlogqle : Real.log (q : ℝ) ≤ (q : ℝ) := Real.log_le_self (by positivity)
  have hmulRpow (u v : ℝ) : L ^ u * L ^ v = L ^ (u + v) := by
    rw [← Real.rpow_add hLpos]
  have hLmul (u : ℝ) : L ^ u * L = L ^ (u + 1) := by
    calc
      L ^ u * L = L ^ u * L ^ 1 := by rw [Real.rpow_one]
      _ = L ^ (u + 1) := hmulRpow u 1
  have hconductor :
      (Nat.log 2 ⌊y⌋₊ : ℝ) * Real.log (q : ℝ) ≤ c₀ * L ^ (B + 1) := by
    calc
      _ ≤ (L / Real.log 2) * Real.log (q : ℝ) :=
        mul_le_mul_of_nonneg_right hNatLog hlogqnonneg
      _ ≤ (L / Real.log 2) * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hlogqle (by positivity)
      _ ≤ (L / Real.log 2) * L ^ B :=
        mul_le_mul_of_nonneg_left hqlog (by positivity)
      _ = c₀ * L ^ (B + 1) := by
        dsimp [c₀]
        calc
          _ = (Real.log 2)⁻¹ * (L ^ B * L) := by ring
          _ = (Real.log 2)⁻¹ * L ^ (B + 1) := by rw [hLmul B]
  have hconductorAbs :
      (Nat.log 2 ⌊y⌋₊ : ℝ) * Real.log (q : ℝ) ≤ y / L ^ A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hLpos A)).2
    calc
      _ * L ^ A ≤ c₀ * L ^ (B + 1) * L ^ A :=
        mul_le_mul_of_nonneg_right hconductor (by positivity)
      _ = c₀ * L ^ (A + B + 1) := by
        calc
          _ = c₀ * (L ^ (B + 1) * L ^ A) := by ring
          _ = c₀ * L ^ (A + B + 1) := by
            rw [hmulRpow (B + 1) A]
            congr 1
            simp [add_comm, add_assoc]
      _ ≤ c₀ * L ^ (A + B + 3) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hLone (by linarith)) hc₀.le
      _ ≤ c₀ * Real.sqrt y := mul_le_mul_of_nonneg_left hCpower hc₀.le
      _ ≤ y := by
        have hsqrtSq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (by linarith)
        have hsqrtSq' : Real.sqrt y * Real.sqrt y = y := by
          simpa only [pow_two] using hsqrtSq
        have hc₀sqrt : c₀ ≤ Real.sqrt y := by
          nlinarith [hsqrtSq', hlarge, sq_nonneg (c₀ - Real.sqrt y),
            Real.sqrt_nonneg y, hc₀.le]
        calc
          c₀ * Real.sqrt y ≤ Real.sqrt y * Real.sqrt y :=
            mul_le_mul_of_nonneg_right hc₀sqrt (Real.sqrt_nonneg y)
          _ = y := hsqrtSq'
  have hprimePower :
      2 * Real.sqrt y * L ≤ y / L ^ A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hLpos A)).2
    have hLprod : L * L ^ A = L ^ (A + 1) := by
      calc
        _ = L ^ 1 * L ^ A := by rw [Real.rpow_one]
        _ = L ^ (1 + A) := hmulRpow 1 A
        _ = L ^ (A + 1) := by congr 1; ring
    have hstep : 2 * L ^ (A + 1) ≤ L ^ (A + 2) := by
      calc
        _ = L ^ (A + 1) * 2 := by ring
        _ ≤ L ^ (A + 1) * L :=
          mul_le_mul_of_nonneg_left hLtwo' (Real.rpow_nonneg (le_of_lt hLpos) _)
        _ = L ^ (A + 2) := by
          calc
            _ = L ^ (A + 1 + 1) := hLmul (A + 1)
            _ = L ^ (A + 2) := by congr 1; ring
    calc
      _ = Real.sqrt y * (2 * (L * L ^ A)) := by ring
      _ = Real.sqrt y * (2 * L ^ (A + 1)) := by rw [hLprod]
      _ ≤ Real.sqrt y * L ^ (A + 2) :=
        mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg y)
      _ ≤ Real.sqrt y * Real.sqrt y :=
        mul_le_mul_of_nonneg_left hPpower (Real.sqrt_nonneg y)
      _ = y := by
        simpa only [pow_two] using (Real.sq_sqrt (by linarith : 0 ≤ y))
  have hmainSW :
      M * y * L ^ (-(A + 1)) ≤ M * (y / L ^ A) := by
    calc
      _ ≤ M * y * L ^ (-A) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hLone (by linarith))
          (mul_nonneg hM.le hypos.le)
      _ = M * (y / L ^ A) := by
        rw [Real.rpow_neg hLpos.le]
        ring
  calc
    ‖thetaCharacterPrefix y χ‖ ≤
        ‖primeCharacterError y χ‖ + 2 * Real.sqrt y * L := by
      simpa [L] using htheta
    _ ≤ (M * y * L ^ (-(A + 1)) +
          (Nat.log 2 ⌊y⌋₊ : ℝ) * Real.log (q : ℝ)) +
          2 * Real.sqrt y * L := add_le_add herror le_rfl
    _ ≤ M * (y / L ^ A) + (y / L ^ A) + (y / L ^ A) := by
      exact add_le_add (add_le_add hmainSW hconductorAbs) hprimePower
    _ = (M + 2) * y * L ^ (-A) := by
      rw [Real.rpow_neg hLpos.le]
      ring

/-- The Mellin weight dual to the theta coefficients. -/
noncomputable def thetaMellinWeight (t y : ℝ) : ℂ :=
  Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ * (Real.log y : ℂ)⁻¹

/-- The derivative of the Mellin-over-prime weight has the usual `(|t|+2)/(y² log y)` bound. -/
theorem thetaMellinWeight_deriv_norm_le (t y : ℝ) (hy : 0 < y)
    (hlog : 1 ≤ Real.log y) :
    ‖deriv (thetaMellinWeight t) y‖ ≤ (|t| + 2) / (y ^ 2 * Real.log y) := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hlogpos : 0 < Real.log y := lt_of_lt_of_le (by norm_num) hlog
  have hlogC : (Real.log y : ℂ) ≠ 0 := by exact_mod_cast hlogpos.ne'
  have hm : HasDerivAt (fun z : ℝ => Erdos821.Blueprint.Analytic.mellin z t)
      ((Complex.I * (t : ℂ) * (y : ℂ)⁻¹) *
        Erdos821.Blueprint.Analytic.mellin y t) y := by
    have hlog' := HasDerivAt.ofReal_comp (Real.hasDerivAt_log hy.ne')
    convert (hlog'.const_mul (Complex.I * (t : ℂ))).cexp using 1 <;>
      simp [Erdos821.Blueprint.Analytic.mellin] <;> ring
  have hid : HasDerivAt (fun z : ℝ => (z : ℂ)) 1 y :=
    HasDerivAt.ofReal_comp (hasDerivAt_id y)
  have hyInv := hid.inv hyC
  have hlogInv :=
    (HasDerivAt.ofReal_comp (Real.hasDerivAt_log hy.ne')).inv hlogC
  have hweight := (hm.mul hyInv).mul hlogInv
  change ‖deriv ((fun z : ℝ => Erdos821.Blueprint.Analytic.mellin z t) *
    (fun z : ℝ => (z : ℂ))⁻¹ *
    (fun z : ℝ => (Real.log z : ℂ))⁻¹) y‖ ≤ _
  rw [hweight.deriv]
  change ‖((Complex.I * (t : ℂ) * (y : ℂ)⁻¹ *
      Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ +
      Erdos821.Blueprint.Analytic.mellin y t * (-1 / (y : ℂ) ^ 2)) *
      (Real.log y : ℂ)⁻¹ +
      Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ *
        (-((y⁻¹ : ℝ) : ℂ) / (Real.log y : ℂ) ^ 2))‖ ≤ _
  have hmnorm : ‖Erdos821.Blueprint.Analytic.mellin y t‖ = 1 := by
    simp [Erdos821.Blueprint.Analytic.mellin, Complex.norm_exp, Complex.mul_re]
  have hInorm : ‖Complex.I‖ = 1 := by simp
  have hynorm : ‖(y : ℂ)‖ = y := by simp [abs_of_pos hy]
  have hlognorm : ‖(Real.log y : ℂ)‖ = Real.log y := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogpos]
  have hterm₁ :
      ‖Complex.I * (t : ℂ) * (y : ℂ)⁻¹ *
        Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹‖ = |t| / y ^ 2 := by
    simp [norm_inv, hmnorm, hInorm, hynorm, Complex.norm_real, Real.norm_eq_abs]
    ring
  have hterm₂ :
      ‖Erdos821.Blueprint.Analytic.mellin y t * (-1 / (y : ℂ) ^ 2)‖ = 1 / y ^ 2 := by
    simp [norm_div, hmnorm, hynorm, Complex.norm_real, Real.norm_eq_abs]
  have hterm₃ :
      ‖Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ *
        (-((y⁻¹ : ℝ) : ℂ) / (Real.log y : ℂ) ^ 2)‖ =
        1 / (y ^ 2 * (Real.log y) ^ 2) := by
    simp [norm_mul, norm_div, norm_inv, hmnorm, hynorm, hlognorm,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy, abs_of_pos hlogpos]
    ring
  calc
    _ ≤ ‖Complex.I * (t : ℂ) * (y : ℂ)⁻¹ *
          Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ +
          Erdos821.Blueprint.Analytic.mellin y t * (-1 / (y : ℂ) ^ 2)‖ *
        ‖((Real.log y : ℂ)⁻¹)‖ +
        ‖Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ *
          (-((y⁻¹ : ℝ) : ℂ) / (Real.log y : ℂ) ^ 2)‖ := by
      calc
        _ ≤ ‖(Complex.I * (t : ℂ) * (y : ℂ)⁻¹ *
              Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ +
              Erdos821.Blueprint.Analytic.mellin y t * (-1 / (y : ℂ) ^ 2)) *
              (Real.log y : ℂ)⁻¹‖ +
            ‖Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ *
              (-((y⁻¹ : ℝ) : ℂ) / (Real.log y : ℂ) ^ 2)‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul]
    _ ≤ (|t| / y ^ 2 + 1 / y ^ 2) * (1 / Real.log y) +
          1 / (y ^ 2 * (Real.log y) ^ 2) := by
      have hab := norm_add_le
        (Complex.I * (t : ℂ) * (y : ℂ)⁻¹ *
          Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹)
        (Erdos821.Blueprint.Analytic.mellin y t * (-1 / (y : ℂ) ^ 2))
      calc
        _ ≤ (‖Complex.I * (t : ℂ) * (y : ℂ)⁻¹ *
              Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹‖ +
              ‖Erdos821.Blueprint.Analytic.mellin y t * (-1 / (y : ℂ) ^ 2)‖) *
              ‖(Real.log y : ℂ)⁻¹‖ +
            ‖Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ *
              (-((y⁻¹ : ℝ) : ℂ) / (Real.log y : ℂ) ^ 2)‖ := by
          exact add_le_add (mul_le_mul_of_nonneg_right hab (norm_nonneg _)) le_rfl
        _ = _ := by
          rw [hterm₁, hterm₂, hterm₃, norm_inv, hlognorm]
          simp [one_div]
    _ ≤ (|t| + 2) / (y ^ 2 * Real.log y) := by
      have hinv : 1 / Real.log y ≤ 1 := by
        apply (div_le_iff₀ hlogpos).2
        linarith
      have hden : 0 < y ^ 2 * Real.log y := by positivity
      have hEq : (|t| / y ^ 2 + 1 / y ^ 2) * (1 / Real.log y) +
          1 / (y ^ 2 * (Real.log y) ^ 2) =
          (|t| + 1 + 1 / Real.log y) / (y ^ 2 * Real.log y) := by
        field_simp
      rw [hEq]
      apply (div_le_div_iff₀ hden hden).2
      nlinarith [abs_nonneg t]





end Erdos821.DivisorHarmonic

namespace Erdos821.Blueprint

open Analytic
open OAI.LargePrimeGaps

set_option maxHeartbeats 1000000 in
/-- The harmonic character estimate follows from the theta-character prefix bound by Abel
summation with the Mellin-over-prime weight. -/
theorem HarmonicCharacters_proof : HarmonicCharacters := by
  intro c C B A hc hC hB hA
  let E : ℝ := A + B + 2
  let D : ℝ := 2 * E / c
  let β : ℝ := 2 * B / c
  have hE : 0 < E := by dsimp [E]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  obtain ⟨M, hM, hThetaEventually⟩ :=
    Erdos821.DivisorHarmonic.thetaCharacterPrefix_log_bound D β hD hβ
  obtain ⟨Yθ, hThetaFrom⟩ := Filter.eventually_atTop.1 hThetaEventually
  let Ybig : ℝ := max 1 Yθ
  have hLogLim : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hULim : Tendsto (fun x : ℝ => (Real.log x) ^ (c / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < c / 2)).comp hLogLim
  have hXEvents : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ 1 ≤ Real.log x ∧ 3 ≤ (Real.log x) ^ (c / 2) ∧
        Real.log Ybig ≤ (Real.log x) ^ (c / 2) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      hLogLim.eventually_ge_atTop 1, hULim.eventually_ge_atTop 3,
      hULim.eventually_ge_atTop (Real.log Ybig)] with x hx hL hU hY
    exact ⟨hx, hL, hU, hY⟩
  refine ⟨(2 + 6 * C) * M, by positivity, ?_⟩
  filter_upwards [hXEvents] with x hx
  rcases hx with ⟨hx2, hLone, hu3, hYbigLog⟩
  let L : ℝ := Real.log x
  let u : ℝ := L ^ (c / 2)
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hLone' : 1 ≤ L := by simpa [L] using hLone
  have hu3' : 3 ≤ u := by simpa [L, u] using hu3
  have hYbigLog' : Real.log Ybig ≤ u := by simpa [L, u] using hYbigLog
  have hU_sq : u ^ 2 = L ^ c := by
    dsimp [u]
    rw [pow_two, ← Real.rpow_add hLpos]
    congr 1
    ring
  have hExp2u : 2 ≤ Real.exp (2 * u) := by
    have h := Real.add_one_le_exp (2 * u)
    linarith [hu3']
  have hExpU : 2 * Real.exp u ≤ Real.exp (L ^ c) := by
    calc
      2 * Real.exp u ≤ Real.exp u * Real.exp (2 * u) := by
        nlinarith [Real.exp_pos u, hExp2u]
      _ = Real.exp (u + 2 * u) := by rw [← Real.exp_add]
      _ ≤ Real.exp (u ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hu3']
      _ = Real.exp (L ^ c) := by rw [hU_sq]
  have hLpow : 1 ≤ L ^ c := by
    calc
      1 = (1 : ℝ) ^ c := by simp
      _ ≤ L ^ c := Real.rpow_le_rpow (by norm_num) hLone' (by linarith)
  have hExpLtwo : 2 ≤ Real.exp (L ^ c) := by
    have h := Real.add_one_le_exp (L ^ c)
    linarith [hLpow]
  intro lo hi t r χ hlo hlohi hhi hr hrLog hχ ht
  let a : ℕ := ⌈lo⌉₊
  let n : ℕ := a - 1
  let m : ℕ := ⌊hi⌋₊
  have hloPos : 0 < lo := by
    have hlo' : Real.exp (L ^ c) ≤ lo := by simpa [L, Analytic.L] using hlo
    exact (Real.exp_pos _).trans_le hlo'
  have haPos : 1 ≤ a := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro ha0
    have hloNonpos : lo ≤ 0 := (Nat.ceil_eq_zero.mp (by simpa [a] using ha0))
    linarith
  have hna : n + 1 = a := by
    dsimp [n]
    exact Nat.sub_add_cancel haPos
  have haLeLo : lo ≤ (a : ℝ) := by
    dsimp [a]
    exact_mod_cast Nat.le_ceil lo
  have hnCast : (n : ℝ) = (a : ℝ) - 1 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    simp
  have hloLarge : 2 ≤ lo := by
    calc
      2 ≤ Real.exp (L ^ c) := hExpLtwo
      _ ≤ lo := hlo
  have hloExp : Real.exp (L ^ c) ≤ lo := by simpa [L, Analytic.L] using hlo
  have hnLeLo : lo - 1 ≤ (n : ℝ) := by
    rw [hnCast]
    linarith
  have hnHalf : lo / 2 ≤ (n : ℝ) := by
    have : lo / 2 ≤ lo - 1 := by linarith
    exact this.trans hnLeLo
  have hnExp : Real.exp u ≤ (n : ℝ) := by
    have huExp : Real.exp u ≤ Real.exp (L ^ c) / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      nlinarith [hExpU]
    calc
      Real.exp u ≤ Real.exp (L ^ c) / 2 := huExp
      _ ≤ lo / 2 := by exact div_le_div_of_nonneg_right hloExp (by norm_num)
      _ ≤ (n : ℝ) := hnHalf
  have hYθLe : Yθ ≤ Real.exp u := by
    have hYexp : Ybig ≤ Real.exp u := by
      calc
        Ybig = Real.exp (Real.log Ybig) := by
          rw [Real.exp_log]
          dsimp [Ybig]
          positivity
        _ ≤ Real.exp u := Real.exp_le_exp.mpr hYbigLog'
    exact le_trans (le_max_right 1 Yθ) hYexp
  have hnYθ : Yθ ≤ (n : ℝ) := hYθLe.trans hnExp
  have hnOne : 1 ≤ (n : ℝ) := by
    have h : 1 < Real.exp u := by
      have := Real.add_one_le_exp u
      have huPos : 0 < u := by linarith
      linarith
    linarith
  have hnNatOne : 1 ≤ n := by exact_mod_cast hnOne
  have hnm : n ≤ m := by
    have hhiFloor : hi ≤ ((m + 1 : ℕ) : ℝ) := by
      dsimp [m]
      exact_mod_cast (Nat.lt_floor_add_one hi).le
    have haUpper : a ≤ m + 1 := by
      dsimp [a]
      apply Nat.ceil_le.mpr
      exact hlohi.trans hhiFloor
    dsimp [n]
    omega
  have hnmReal : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hmOne : 1 ≤ (m : ℝ) := by exact hnOne.trans hnmReal
  have hmPos : 0 < (m : ℝ) := by linarith
  have hmLeHi : (m : ℝ) ≤ hi := by
    dsimp [m]
    exact Nat.floor_le (by linarith [hloPos, hlohi])
  have hLogN : u ≤ Real.log (n : ℝ) := by
    calc
      u = Real.log (Real.exp u) := by rw [Real.log_exp]
      _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos _) hnExp
  have hBetaPow : u ^ β = L ^ B := by
    dsimp [β]
    rw [← Real.rpow_mul hLpos.le (c / 2) (2 * B / c)]
    congr 1
    field_simp
  have hDPow : u ^ (-D) = L ^ (-E) := by
    dsimp [D]
    rw [← Real.rpow_mul hLpos.le (c / 2) (- (2 * E / c))]
    congr 1
    field_simp
  have hLocalTheta (y : ℝ) (hny : (n : ℝ) ≤ y) :
      ‖Erdos821.DivisorHarmonic.thetaCharacterPrefix y χ‖ ≤
        M * y * L ^ (-E) := by
    have hyPos : 0 < y := by linarith [hnOne]
    have hLogLower : u ≤ Real.log y := by
      calc
        u ≤ Real.log (n : ℝ) := hLogN
        _ ≤ Real.log y := Real.log_le_log (by linarith [hnOne]) hny
    have hqβ : (r : ℝ) ≤ (Real.log y) ^ β := by
      calc
        (r : ℝ) ≤ L ^ B := hrLog
        _ = u ^ β := hBetaPow.symm
        _ ≤ (Real.log y) ^ β :=
          Real.rpow_le_rpow (by positivity) hLogLower hβ.le
    have hTheta := hThetaFrom y (hnYθ.trans hny) r χ (by omega) hqβ hχ
    have hPower : (Real.log y) ^ (-D) ≤ L ^ (-E) := by
      calc
        (Real.log y) ^ (-D) ≤ u ^ (-D) :=
          Real.rpow_le_rpow_of_nonpos (by linarith [hLogN]) hLogLower (by linarith [hD])
        _ = L ^ (-E) := hDPow
    exact hTheta.trans <| mul_le_mul_of_nonneg_left hPower
      (mul_nonneg hM.le hyPos.le)
  let coeff : ℕ → ℂ := fun k =>
    if n < k then χ (k : ZMod r) * (theta k : ℂ) else 0
  let partialTheta : ℝ → ℂ := fun y =>
    ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, coeff k
  have hPrefix (y : ℝ) (hny : (n : ℝ) ≤ y) :
      partialTheta y = Erdos821.DivisorHarmonic.thetaCharacterPrefix y χ -
        Erdos821.DivisorHarmonic.thetaCharacterPrefix (n : ℝ) χ := by
    have hfloor : n ≤ ⌊y⌋₊ := (Nat.le_floor_iff (by linarith [hny])).2 hny
    have hfiltered :
        (Finset.Icc 0 ⌊y⌋₊).filter (fun k => n < k) = Finset.Ioc n ⌊y⌋₊ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hlocal :
        (∑ k ∈ Finset.Icc 0 ⌊y⌋₊, coeff k) =
          ∑ k ∈ Finset.Ioc n ⌊y⌋₊, χ (k : ZMod r) * (theta k : ℂ) := by
      change (∑ k ∈ Finset.Icc 0 ⌊y⌋₊,
        if n < k then χ (k : ZMod r) * (theta k : ℂ) else 0) = _
      rw [← hfiltered]
      simp only [Finset.sum_filter]
    have hsplit :
        (∑ k ∈ Finset.Ioc 0 ⌊y⌋₊, χ (k : ZMod r) * (theta k : ℂ)) =
          (∑ k ∈ Finset.Ioc 0 n, χ (k : ZMod r) * (theta k : ℂ)) +
            ∑ k ∈ Finset.Ioc n ⌊y⌋₊, χ (k : ZMod r) * (theta k : ℂ) := by
      rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le n) hfloor]
      exact Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_rfl : n ≤ n))
    have hTn : Erdos821.DivisorHarmonic.thetaCharacterPrefix (n : ℝ) χ =
        ∑ k ∈ Finset.Ioc 0 n, χ (k : ZMod r) * (theta k : ℂ) := by
      simp [Erdos821.DivisorHarmonic.thetaCharacterPrefix]
    calc
      partialTheta y = ∑ k ∈ Finset.Ioc n ⌊y⌋₊,
          χ (k : ZMod r) * (theta k : ℂ) := hlocal
      _ = (∑ k ∈ Finset.Ioc 0 ⌊y⌋₊,
            χ (k : ZMod r) * (theta k : ℂ)) -
          ∑ k ∈ Finset.Ioc 0 n, χ (k : ZMod r) * (theta k : ℂ) := by
            rw [hsplit]
            abel
      _ = Erdos821.DivisorHarmonic.thetaCharacterPrefix y χ -
            Erdos821.DivisorHarmonic.thetaCharacterPrefix (n : ℝ) χ := by
              rw [Erdos821.DivisorHarmonic.thetaCharacterPrefix, hTn]
  have hPrefixNorm (y : ℝ) (hny : (n : ℝ) ≤ y) :
      ‖partialTheta y‖ ≤ 2 * M * y * L ^ (-E) := by
    rw [hPrefix y hny]
    have hyBound := hLocalTheta y hny
    have hnBound := hLocalTheta (n : ℝ) le_rfl
    calc
      ‖Erdos821.DivisorHarmonic.thetaCharacterPrefix y χ -
          Erdos821.DivisorHarmonic.thetaCharacterPrefix (n : ℝ) χ‖ ≤
          ‖Erdos821.DivisorHarmonic.thetaCharacterPrefix y χ‖ +
            ‖Erdos821.DivisorHarmonic.thetaCharacterPrefix (n : ℝ) χ‖ := norm_sub_le _ _
      _ ≤ M * y * L ^ (-E) + M * (n : ℝ) * L ^ (-E) := add_le_add hyBound hnBound
      _ ≤ 2 * M * y * L ^ (-E) := by
        have hMR : 0 ≤ M * L ^ (-E) :=
          mul_nonneg hM.le (Real.rpow_nonneg hLpos.le _)
        calc
          _ = M * L ^ (-E) * (y + (n : ℝ)) := by ring
          _ ≤ M * L ^ (-E) * (y + y) :=
            mul_le_mul_of_nonneg_left (by linarith [hny]) hMR
          _ = 2 * M * y * L ^ (-E) := by ring
  have haEq : a = n + 1 := hna.symm
  have hPrimeInterval :
      (Finset.Icc a m).filter Nat.Prime = (Finset.Ioc n m).filter Nat.Prime := by
    have haSucc : a = Nat.succ n := by omega
    rw [haSucc]
    have hIcc : Finset.Icc (Nat.succ n) m = Finset.Ioc n m := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hIcc]
  let weight : ℝ → ℂ := Erdos821.DivisorHarmonic.thetaMellinWeight t
  have hWeightedEq :
      (∑ p ∈ (Finset.Icc a m).filter Nat.Prime,
          χ (p : ZMod r) * mellin (p : ℝ) t / (p : ℂ)) =
        ∑ k ∈ Finset.Ioc n m, weight (k : ℝ) * coeff k := by
    rw [hPrimeInterval, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    have hnk : n < k := (Finset.mem_Ioc.mp hk).1
    by_cases hprime : Nat.Prime k
    · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hprime.pos
      have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hprime.ne_zero
      have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
      have hlogne : (Real.log (k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlogpos.ne'
      simp only [weight, coeff, if_pos hnk,
        Erdos821.DivisorHarmonic.thetaMellinWeight,
        OAI.LargePrimeGaps.theta, if_pos hprime]
      field_simp [hkC, hlogne]
      have hkCast : ((k : ℝ) : ℂ) = (k : ℂ) := by norm_cast
      rw [hkCast]
    · simp only [coeff, if_pos hnk, OAI.LargePrimeGaps.theta, if_neg hprime]
      simp [Nat.cast_zero]
  let s : Set ℝ := Set.Ioi 1
  have hlogRealCD : ContDiffOn ℝ 2 Real.log s := by
    apply (Real.contDiffOn_log (n := 2)).mono
    intro y hy
    change y ≠ 0
    have hy1 : 1 < y := Set.mem_Ioi.mp hy
    linarith
  have hlogComplexCD : ContDiffOn ℝ 2 (fun y : ℝ => (Real.log y : ℂ)) s := by
    change ContDiffOn ℝ 2 (Complex.ofRealCLM ∘ Real.log) s
    exact hlogRealCD.continuousLinearMap_comp Complex.ofRealCLM
  have hinnerCD : ContDiffOn ℝ 2
      (fun y : ℝ => Complex.I * (t : ℂ) * (Real.log y : ℂ)) s := by
    have h := ContDiffOn.const_smul (Complex.I * (t : ℂ)) hlogComplexCD
    simpa only [smul_eq_mul] using h
  have hmellinCD : ContDiffOn ℝ 2 (fun y : ℝ => mellin y t) s := by
    change ContDiffOn ℝ 2
      (fun y : ℝ => Complex.exp (Complex.I * (t : ℂ) * (Real.log y : ℂ))) s
    exact Complex.contDiff_exp.comp_contDiffOn hinnerCD
  have hyComplexCD : ContDiffOn ℝ 2 (fun y : ℝ => (y : ℂ)) s :=
    Complex.ofRealCLM.contDiff.contDiffOn
  have hyInvCD : ContDiffOn ℝ 2 (fun y : ℝ => (y : ℂ)⁻¹) s :=
    hyComplexCD.inv (by
      intro y hy
      exact_mod_cast (ne_of_gt (lt_trans zero_lt_one (Set.mem_Ioi.mp hy))))
  have hlogInvCD : ContDiffOn ℝ 2 (fun y : ℝ => (Real.log y : ℂ)⁻¹) s :=
    hlogComplexCD.inv (by
      intro y hy
      exact_mod_cast (Real.log_pos (Set.mem_Ioi.mp hy)).ne')
  have hweightCD : ContDiffOn ℝ 2 weight s := by
    change ContDiffOn ℝ 2
      (fun y : ℝ => mellin y t * (y : ℂ)⁻¹ * (Real.log y : ℂ)⁻¹) s
    exact (hmellinCD.mul hyInvCD).mul hlogInvCD
  have hwDiff : ∀ y ∈ Set.Icc (n : ℝ) (m : ℝ),
      DifferentiableAt ℝ weight y := by
    intro y hy
    have hygt1 : y ∈ s := by
      have hnexp1 : 1 < (n : ℝ) := by linarith [hnExp, Real.add_one_le_exp u]
      exact Set.mem_Ioi.mpr (lt_of_lt_of_le hnexp1 hy.1)
    exact (hweightCD.differentiableOn (by norm_num) y hygt1).differentiableAt
      (isOpen_Ioi.mem_nhds hygt1)
  have hderivCont : ContinuousOn (deriv weight) s :=
    (hweightCD.deriv_of_isOpen (m := 0) isOpen_Ioi (by norm_num)).continuousOn
  have hIccSub : Set.Icc (n : ℝ) (m : ℝ) ⊆ Set.Ioi 1 := by
    intro y hy
    have hnexp1 : 1 < (n : ℝ) := by linarith [hnExp, Real.add_one_le_exp u]
    exact lt_of_lt_of_le hnexp1 hy.1
  have hderivIntegrable : IntegrableOn (deriv weight) (Set.Icc (n : ℝ) (m : ℝ)) :=
    (hderivCont.mono hIccSub).integrableOn_Icc
  have hProdIntegrable : IntegrableOn
      (fun y : ℝ => deriv weight y * partialTheta y) (Set.Icc (n : ℝ) (m : ℝ)) := by
    simpa only [partialTheta] using
      (integrableOn_mul_sum_Icc coeff (by positivity : (0 : ℝ) ≤ (n : ℝ)) hderivIntegrable)
  have hNormIntegrable : IntegrableOn
      (fun y : ℝ => ‖deriv weight y * partialTheta y‖) (Set.Icc (n : ℝ) (m : ℝ)) :=
    hProdIntegrable.norm
  let R : ℝ := 2 * M * (|t| + 2) * L ^ (-E)
  have hRnonneg : 0 ≤ R := by dsimp [R]; positivity
  have hInvLog (y : ℝ) (hy : (n : ℝ) ≤ y) :
      1 ≤ Real.log y := by
    have hly : u ≤ Real.log y := by
      calc
        u ≤ Real.log (n : ℝ) := hLogN
        _ ≤ Real.log y := Real.log_le_log (by linarith [hnOne]) hy
    linarith [hu3']
  have hIntPointwise (y : ℝ) (hy : y ∈ Set.Icc (n : ℝ) (m : ℝ)) :
      ‖deriv weight y * partialTheta y‖ ≤ R * y⁻¹ := by
    have hypos : 0 < y := by linarith [hnOne, hy.1]
    have hlogy := hInvLog y hy.1
    have hderiv := Erdos821.DivisorHarmonic.thetaMellinWeight_deriv_norm_le t y hypos hlogy
    have hpartialTheta := hPrefixNorm y hy.1
    have hdenCompare : (|t| + 2) / (y ^ 2 * Real.log y) ≤ (|t| + 2) / y ^ 2 := by
      have hden₁ : 0 < y ^ 2 * Real.log y := by positivity
      have hden₂ : 0 < y ^ 2 := by positivity
      have hdenOrder : y ^ 2 ≤ y ^ 2 * Real.log y := by
        calc
          y ^ 2 = y ^ 2 * 1 := by ring
          _ ≤ y ^ 2 * Real.log y :=
            mul_le_mul_of_nonneg_left hlogy (sq_nonneg y)
      apply (div_le_div_iff₀ hden₁ hden₂).2
      exact mul_le_mul_of_nonneg_left hdenOrder (by positivity)
    calc
      ‖deriv weight y * partialTheta y‖ = ‖deriv weight y‖ * ‖partialTheta y‖ := norm_mul _ _
      _ ≤ ((|t| + 2) / (y ^ 2 * Real.log y)) *
            (2 * M * y * L ^ (-E)) :=
          mul_le_mul hderiv hpartialTheta (norm_nonneg _) (by positivity)
      _ ≤ ((|t| + 2) / y ^ 2) * (2 * M * y * L ^ (-E)) :=
          mul_le_mul_of_nonneg_right hdenCompare (by positivity)
      _ = R * y⁻¹ := by
        dsimp [R]
        field_simp
  have hRIntContinuous : ContinuousOn (fun y : ℝ => R * y⁻¹)
      (Set.Icc (n : ℝ) (m : ℝ)) := by
    intro y hy
    have hypos : y ≠ 0 := by linarith [hnOne, hy.1]
    fun_prop (disch := assumption)
  have hRIntIntegrable :
      IntegrableOn (fun y : ℝ => R * y⁻¹) (Set.Icc (n : ℝ) (m : ℝ)) := by
    exact hRIntContinuous.integrableOn_Icc (μ := volume)
  have hIntLe :
      (∫ y in (n : ℝ)..(m : ℝ), ‖deriv weight y * partialTheta y‖) ≤
        ∫ y in (n : ℝ)..(m : ℝ), R * y⁻¹ :=
    intervalIntegral.integral_mono_on hnmReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hnmReal).2 hNormIntegrable)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hnmReal).2 hRIntIntegrable)
      hIntPointwise
  have hLogRatio : Real.log ((m : ℝ) / (n : ℝ)) ≤ C * L := by
    have hnCastPos : 0 < (n : ℝ) := by linarith [hnOne]
    have hnCastOne : 1 ≤ (n : ℝ) := hnOne
    have hmNonneg : 0 ≤ (m : ℝ) := by linarith [hmOne]
    have hratio : (m : ℝ) / (n : ℝ) ≤ (m : ℝ) := by
      apply (div_le_iff₀ hnCastPos).2
      nlinarith [mul_le_mul_of_nonneg_left hnCastOne hmNonneg]
    have hratioPos : 0 < (m : ℝ) / (n : ℝ) := by positivity
    have hhiPos : 0 < hi := by linarith [hmPos, hmLeHi]
    calc
      Real.log ((m : ℝ) / (n : ℝ)) ≤ Real.log (m : ℝ) :=
        Real.log_le_log hratioPos hratio
      _ ≤ Real.log hi := Real.log_le_log hmPos hmLeHi
      _ ≤ C * L := by
        calc
          Real.log hi ≤ Real.log (x ^ C) := Real.log_le_log hhiPos hhi
          _ = C * L := by simp [L, Analytic.L, Real.log_rpow hxpos]
  have hIntNorm :
      ‖∫ y in (n : ℝ)..(m : ℝ), deriv weight y * partialTheta y‖ ≤ R * (C * L) := by
    calc
      _ ≤ ∫ y in (n : ℝ)..(m : ℝ), ‖deriv weight y * partialTheta y‖ :=
        intervalIntegral.norm_integral_le_integral_norm hnmReal
      _ ≤ ∫ y in (n : ℝ)..(m : ℝ), R * y⁻¹ := hIntLe
      _ = R * Real.log ((m : ℝ) / (n : ℝ)) := by
        rw [intervalIntegral.integral_const_mul,
          integral_inv_of_pos (by linarith [hnOne]) hmPos]
      _ ≤ R * (C * L) := mul_le_mul_of_nonneg_left hLogRatio hRnonneg
  have hPlo : partialTheta (n : ℝ) = 0 := by
    rw [hPrefix (n : ℝ) le_rfl]
    simp
  have hPhi : partialTheta (m : ℝ) =
      Erdos821.DivisorHarmonic.thetaCharacterPrefix (m : ℝ) χ -
        Erdos821.DivisorHarmonic.thetaCharacterPrefix (n : ℝ) χ :=
    hPrefix (m : ℝ) (by exact_mod_cast hnm)
  have hPhiNorm : ‖partialTheta (m : ℝ)‖ ≤ 2 * M * (m : ℝ) * L ^ (-E) :=
    hPrefixNorm (m : ℝ) (by exact_mod_cast hnm)
  have hWeightNorm : ‖weight (m : ℝ)‖ ≤ 1 / (m : ℝ) := by
    have hmLog : 1 ≤ Real.log (m : ℝ) := hInvLog (m : ℝ) (by exact_mod_cast hnm)
    have hmLogPos : 0 < Real.log (m : ℝ) := by linarith
    have hmellin : ‖mellin (m : ℝ) t‖ = 1 := by
      have harg :
          Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ) =
            Complex.I * (t : ℂ) * Complex.log (m : ℂ) := by
        exact congrArg (fun z : ℂ => Complex.I * (t : ℂ) * z)
          (Complex.ofReal_log (by positivity : 0 ≤ (m : ℝ)))
      have hRe : (Complex.I * (t : ℂ) * Complex.log (m : ℂ)).re = 0 := by
        rw [Complex.mul_re]
        simp [Complex.mul_re, Complex.mul_im, Complex.log_im, Complex.natCast_arg]
      calc
        ‖mellin (m : ℝ) t‖ =
            Real.exp ((Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ)).re) := by
              rw [Erdos821.Blueprint.Analytic.mellin, Complex.norm_exp]
        _ = Real.exp ((Complex.I * (t : ℂ) * Complex.log (m : ℂ)).re) := by rw [harg]
        _ = 1 := by rw [hRe]; simp
    have hmCast : ‖(m : ℂ)‖ = (m : ℝ) := by simp [abs_of_pos hmPos]
    have hlogCast : ‖(Real.log (m : ℝ) : ℂ)‖ = Real.log (m : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmLogPos]
    have hlogInv : 1 / Real.log (m : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hmLogPos).2
      linarith
    calc
      ‖weight (m : ℝ)‖ =
          (1 / (m : ℝ)) * (1 / Real.log (m : ℝ)) := by
            change ‖mellin (m : ℝ) t * (m : ℂ)⁻¹ *
              (Real.log (m : ℝ) : ℂ)⁻¹‖ = _
            rw [norm_mul, norm_mul, hmellin, norm_inv, hmCast, norm_inv, hlogCast]
            simp [one_div]
      _ ≤ (1 / (m : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hlogInv (by positivity)
      _ = 1 / (m : ℝ) := by ring
  have hAbel :=
    sum_mul_eq_sub_sub_integral_mul' (c := coeff) hnm hwDiff hderivIntegrable
  have hsumM :
      (∑ k ∈ Finset.Icc 0 m, coeff k) = partialTheta (m : ℝ) := by
    simp [partialTheta]
  have hsumN :
      (∑ k ∈ Finset.Icc 0 n, coeff k) = partialTheta (n : ℝ) := by
    simp [partialTheta]
  have hSetIntegralNorm :
      ‖∫ y in Set.Ioc (n : ℝ) (m : ℝ), deriv weight y * partialTheta y‖ ≤
        R * (C * L) := by
    rw [← intervalIntegral.integral_of_le hnmReal]
    exact hIntNorm
  have hAbelBound :
      ‖∑ k ∈ Finset.Ioc n m, weight (k : ℝ) * coeff k‖ ≤
        (2 + 6 * C) * M * L ^ (-A) := by
    rw [hAbel, hsumM, hsumN, hPlo]
    simp only [mul_zero, sub_zero]
    calc
      ‖weight (m : ℝ) * partialTheta (m : ℝ) -
          ∫ y in Set.Ioc (n : ℝ) (m : ℝ), deriv weight y * partialTheta y‖ ≤
          ‖weight (m : ℝ) * partialTheta (m : ℝ)‖ +
            ‖∫ y in Set.Ioc (n : ℝ) (m : ℝ), deriv weight y * partialTheta y‖ := norm_sub_le _ _
      _ ≤ (2 * M * L ^ (-E)) + R * (C * L) := by
        have hend : ‖weight (m : ℝ) * partialTheta (m : ℝ)‖ ≤ 2 * M * L ^ (-E) := by
          have hmne : (m : ℝ) ≠ 0 := hmPos.ne'
          calc
            _ = ‖weight (m : ℝ)‖ * ‖partialTheta (m : ℝ)‖ := norm_mul _ _
            _ ≤ (1 / (m : ℝ)) * (2 * M * (m : ℝ) * L ^ (-E)) :=
              mul_le_mul hWeightNorm hPhiNorm (norm_nonneg _) (by positivity)
            _ = 2 * M * L ^ (-E) * ((m : ℝ)⁻¹ * (m : ℝ)) := by ring
            _ = 2 * M * L ^ (-E) := by rw [inv_mul_cancel₀ hmne, mul_one]
        exact add_le_add hend hSetIntegralNorm
      _ ≤ (2 + 6 * C) * M * L ^ (-A) := by
        dsimp [R]
        have hLB : 1 ≤ L ^ B := by
          calc
            1 = L ^ (0 : ℝ) := by simp
            _ ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le hLone' (by linarith)
        have htAbs : |t| + 2 ≤ 3 * L ^ B := by
          have ht' : |t| ≤ L ^ B := ht
          linarith
        have hExpE : B + 1 - E = -A - 1 := by dsimp [E]; ring
        have hExpEndpoint : -E ≤ -A := by dsimp [E]; linarith
        have hExpInt : B + 1 - E ≤ -A := by rw [hExpE]; linarith
        have hEndpoint : 2 * M * L ^ (-E) ≤ 2 * M * L ^ (-A) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hLone' hExpEndpoint) (by positivity)
        have hIntegral :
            (2 * M * (|t| + 2) * L ^ (-E)) * (C * L) ≤
              6 * M * C * L ^ (B + 1 - E) := by
          calc
            _ ≤ (2 * M * (3 * L ^ B) * L ^ (-E)) * (C * L) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left htAbs (by positivity))
                  (Real.rpow_nonneg hLpos.le _)) (by positivity)
            _ = 6 * M * C * L ^ (B + 1 - E) := by
              have hpow : L ^ B * L ^ (-E) * L = L ^ (B + 1 - E) := by
                have hLpowOne : L ^ (1 : ℝ) = L := Real.rpow_one L
                calc
                  _ = L ^ B * (L ^ (-E) * L ^ (1 : ℝ)) := by
                    conv_rhs => rw [hLpowOne]
                    ring
                  _ = L ^ B * L ^ (-E + 1) := by rw [← Real.rpow_add hLpos]
                  _ = L ^ (B + (-E + 1)) := by rw [← Real.rpow_add hLpos]
                  _ = L ^ (B + 1 - E) := by congr 1 <;> ring
              calc
                _ = 6 * M * C * (L ^ B * L ^ (-E) * L) := by ring
                _ = 6 * M * C * L ^ (B + 1 - E) := by rw [hpow]
        calc
          2 * M * L ^ (-E) + (2 * M * (|t| + 2) * L ^ (-E)) * (C * L) ≤
              2 * M * L ^ (-A) + 6 * M * C * L ^ (B + 1 - E) :=
                add_le_add hEndpoint hIntegral
          _ ≤ 2 * M * L ^ (-A) + 6 * M * C * L ^ (-A) := by
                exact add_le_add le_rfl
                  (mul_le_mul_of_nonneg_left
                    (Real.rpow_le_rpow_of_exponent_le hLone' hExpInt) (by positivity))
          _ = (2 + 6 * C) * M * L ^ (-A) := by ring
  rw [hWeightedEq]
  exact hAbelBound

example : type_of% @HarmonicCharacters_proof = HarmonicCharacters := rfl


end Erdos821.Blueprint
