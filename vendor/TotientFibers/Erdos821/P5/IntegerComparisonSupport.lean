import Erdos821.P5.SmoothComparisonIntegral
import Erdos821.P5.FourierArcTask

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic

def natIntegerSupport (s : Finset ℕ) : Finset ℤ :=
  s.map (⟨fun n => (n : ℤ), Int.ofNat_injective⟩ : ℕ ↪ ℤ)

def natIntegerCoefficient (a : ℕ → ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then a n.toNat else 0

@[simp] theorem natIntegerCoefficient_nat (a : ℕ → ℂ) (n : ℕ) :
    natIntegerCoefficient a (n : ℤ) = a n := by
  simp [natIntegerCoefficient]

theorem sum_natIntegerSupport (s : Finset ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ natIntegerSupport s, f n) = ∑ n ∈ s, f (n : ℤ) := by
  simp [natIntegerSupport, Finset.sum_map]

theorem integerAdditivePolynomial_nat (s : Finset ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    integerAdditivePolynomial (natIntegerSupport s) (natIntegerCoefficient a) θ =
      localAdditivePolynomial s a θ := by
  simp [integerAdditivePolynomial, natIntegerSupport, Finset.sum_map,
    localAdditivePolynomial]

theorem integerCoefficient_square_sum (s : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ natIntegerSupport s, ‖natIntegerCoefficient a n‖ ^ 2) = sqNorm s a := by
  simp [natIntegerSupport, Finset.sum_map, sqNorm]

theorem localAdditivePolynomial_continuous (s : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (localAdditivePolynomial s a) := by
  unfold localAdditivePolynomial e
  fun_prop

def comparisonTargetRoots (lo hi Y : ℝ) : Finset ℕ :=
  Finset.Icc ⌈lo / 4 * Y⌉₊ ⌊(2 * hi + 5 * lo / 4) * Y⌋₊

theorem comparisonSmoothTarget_zero_outside (G : PrimeGroups) (x Y a lo hi : ℝ)
    (hlo : 0 < lo) (hhi : lo < hi) (hY : 0 < Y) (E : Endpoint) (mark : ℕ → ℂ)
    (n : ℕ) (hn : n ∉ comparisonTargetRoots lo hi Y) :
    comparisonSmoothTarget G x Y a lo hi hlo hhi E mark n = 0 := by
  have hz : comparisonTargetSizeCutoff lo hi hlo hhi ((n : ℝ) / Y) = 0 := by
    by_contra hne
    have hp := comparisonTargetSizeCutoff_support lo hi hlo hhi
      (Function.mem_support.mpr hne)
    apply hn
    apply Finset.mem_Icc.mpr
    exact ⟨Nat.ceil_le.mpr ((le_div_iff₀ hY).mp hp.1),
      Nat.le_floor ((div_le_iff₀ hY).mp hp.2)⟩
  simp [comparisonSmoothTarget, hz]

/-- The finite integer pairing includes exactly the positive shifted target.
The target coefficient vanishes off its fixed finite support. -/
theorem natural_shift_eq_integer_pairing (s t : Finset ℕ) (a b : ℕ → ℂ) (d : ℤ)
    (hpos : ∀ n ∈ s, 0 ≤ (n : ℤ) + d)
    (hb : ∀ n, n ∉ t → b n = 0) :
    (∑ n ∈ s, star (a n) * b ((n : ℤ) + d).toNat) =
      ∑ n ∈ natIntegerSupport s, ∑ m ∈ natIntegerSupport t,
        if m = n + d then star (natIntegerCoefficient a n) *
          natIntegerCoefficient b m else 0 := by
  rw [sum_natIntegerSupport]
  simp_rw [sum_natIntegerSupport, natIntegerCoefficient_nat]
  apply Finset.sum_congr rfl
  intro n hn
  have hd : (((n : ℤ) + d).toNat : ℤ) = (n : ℤ) + d :=
    Int.toNat_of_nonneg (hpos n hn)
  symm
  rw [Finset.sum_eq_single ((n : ℤ) + d).toNat]
  · simp [hd]
  · intro m hm hmn
    have hne : (m : ℤ) ≠ (n : ℤ) + d := by
      intro heq
      apply hmn
      exact_mod_cast heq.trans hd.symm
    simp [hne]
  · intro hnot
    simp [hd, hb _ hnot]

theorem natural_shift_eq_fourier_integral (hfourier : FourierArcTask)
    (s t : Finset ℕ) (a b : ℕ → ℂ) (d : ℤ)
    (hpos : ∀ n ∈ s, 0 ≤ (n : ℤ) + d)
    (hb : ∀ n, n ∉ t → b n = 0) :
    (∑ n ∈ s, star (a n) * b ((n : ℤ) + d).toNat) =
      ∫ θ in (0 : ℝ)..1,
        star (localAdditivePolynomial s a θ) * localAdditivePolynomial t b θ *
          e (-θ * d) := by
  rw [natural_shift_eq_integer_pairing s t a b d hpos hb, hfourier.1]
  simp_rw [integerAdditivePolynomial_nat]

theorem natural_fourier_parseval (hfourier : FourierArcTask)
    (s : Finset ℕ) (a : ℕ → ℂ) :
    (∫ θ in (0 : ℝ)..1, ‖localAdditivePolynomial s a θ‖ ^ 2) = sqNorm s a := by
  have h := hfourier.2.1 (natIntegerSupport s) (natIntegerCoefficient a)
  simp_rw [integerAdditivePolynomial_nat] at h
  exact h.trans (integerCoefficient_square_sum s a)

theorem finite_shift_law_eq_fourier_integral (hfourier : FourierArcTask)
    {ι : Type*} (U : Finset ι) (w : ι → ℂ) (d : ι → ℤ)
    (s t : Finset ℕ) (a b : ℕ → ℂ)
    (hpos : ∀ u ∈ U, ∀ n ∈ s, 0 ≤ (n : ℤ) + d u)
    (hb : ∀ n, n ∉ t → b n = 0) :
    (∑ u ∈ U, w u * ∑ n ∈ s, star (a n) * b ((n : ℤ) + d u).toNat) =
      ∫ θ in (0 : ℝ)..1,
        star (localAdditivePolynomial s a θ) * localAdditivePolynomial t b θ *
          (∑ u ∈ U, w u * e (-θ * d u)) := by
  have hi (u : ι) : IntervalIntegrable
      (fun θ => w u * (star (localAdditivePolynomial s a θ) *
        localAdditivePolynomial t b θ * e (-θ * d u))) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (((localAdditivePolynomial_continuous s a).star.mul
      (localAdditivePolynomial_continuous t b)).mul (by unfold e; fun_prop))
  calc
    _ = ∑ u ∈ U, w u * ∫ θ in (0 : ℝ)..1,
        star (localAdditivePolynomial s a θ) * localAdditivePolynomial t b θ *
          e (-θ * d u) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [natural_shift_eq_fourier_integral hfourier s t a b (d u) (hpos u hu) hb]
    _ = ∫ θ in (0 : ℝ)..1, ∑ u ∈ U, w u *
        (star (localAdditivePolynomial s a θ) * localAdditivePolynomial t b θ *
          e (-θ * d u)) := by
      simp_rw [← intervalIntegral.integral_const_mul]
      exact (intervalIntegral.integral_finsetSum (fun u hu => hi u)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp only
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring

end Erdos821.P5Core
