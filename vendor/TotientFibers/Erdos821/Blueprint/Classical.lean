import Erdos821.Blueprint.Analytic

/-! Package P1. Each proposition spells out the needed uniformity. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Erdos821.Blueprint
open Analytic

def primesUpTo (y : ℝ) : Finset ℕ := (Finset.Icc 1 ⌊y⌋₊).filter Nat.Prime
def sieveProduct (y : ℝ) : ℝ := ∏ p ∈ primesUpTo y, (1 - (p : ℝ)⁻¹)
def shiftedSieveProduct (y : ℝ) : ℝ :=
  ∏ p ∈ (primesUpTo y).erase 2, (1 - ((p : ℝ) - 1)⁻¹)
def li (y : ℝ) : ℝ := ∫ t : ℝ in (2 : ℝ)..y, (Real.log t)⁻¹

def PrimeProgressions : Prop :=
  ∀ A C : ℝ, 0 < A → 0 < C → ∃ K : ℝ, 0 < K ∧
    ∀ᶠ y : ℝ in atTop, ∀ r a : ℕ, 1 ≤ r → (r : ℝ) ≤ Real.log y ^ C →
      Nat.Coprime a r →
      |(((primesUpTo y).filter (fun p => p % r = a % r)).card : ℝ) -
          li y / (Nat.totient r : ℝ)| ≤ K * y * Real.log y ^ (-A)

def MertensEstimates : Prop :=
  (∃ K : ℝ, ∀ y : ℝ, 2 ≤ y →
    |(∑ p ∈ primesUpTo y, (p : ℝ)⁻¹) - Real.log (Real.log y)| ≤ K) ∧
  Tendsto (fun y : ℝ => Real.log y * sieveProduct y) atTop
    (nhds (Real.exp (-Real.eulerMascheroniConstant)))

def HarmonicCharacters : Prop :=
  ∀ c C B A : ℝ, 0 < c → 0 < C → 0 < B → 0 < A →
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (lo hi t : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r),
        Real.exp (L x ^ c) ≤ lo → lo ≤ hi → hi ≤ x ^ C →
        1 ≤ r → (r : ℝ) ≤ L x ^ B → χ ≠ 1 → |t| ≤ L x ^ B →
        ‖∑ p ∈ ((Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter Nat.Prime),
          χ (p : ZMod r) * mellin p t / (p : ℂ)‖ ≤ K * L x ^ (-A)

def DivisorMoments : Prop :=
  ∀ k : ℕ, ∃ C K : ℝ, 0 < K ∧ ∀ Y : ℝ, 1 ≤ Y →
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k / n) ≤
      K * Real.log (2 * Y) ^ C ∧
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k) ≤
      K * Y * Real.log (2 * Y) ^ C

def MeanSquares : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (Y : ℕ) (a : ℕ → ℂ) (lo hi : ℝ), lo ≤ hi →
    (∫ t : ℝ in lo..hi, ‖dp (Finset.Icc 1 Y) a t‖ ^ 2) ≤
      K * (hi - lo + Y * Real.log (2 * Y)) * sqNorm (Finset.Icc 1 Y) a ∧
    ∀ E : Finset ℝ, (∀ t ∈ E, lo ≤ t ∧ t ≤ hi) →
      (∀ t ∈ E, ∀ u ∈ E, t ≠ u → 1 ≤ |t - u|) →
      (∑ t ∈ E, ‖dp (Finset.Icc 1 Y) a t‖ ^ 2) ≤
        K * (hi - lo + 1 + Y * Real.log (2 * Y)) * Real.log (2 * Y) ^ 2 *
          sqNorm (Finset.Icc 1 Y) a

/-- Logarithmic loss in the available OAI large sieve is harmless here. -/
def MultiplicativeLargeSieve : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (N R : ℕ) (a : ℕ → ℂ),
    (∑ r : Fin R, ((r.val + 1 : ℕ) : ℝ) / Nat.totient (r.val + 1) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (r.val + 1))).filter
        DirichletCharacter.IsPrimitive,
          ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod (r.val + 1))‖ ^ 2) ≤
      K * (N + 1 + (R : ℝ) ^ 2 * Real.log (2 * R)) * sqNorm (Finset.Icc 1 N) a

def DerivativeTests : Prop :=
  (∃ K : ℝ, 0 < K ∧ ∀ (lo hi lam : ℝ) (j : ℤ) (f : ℝ → ℝ),
    lo ≤ hi → 0 < lam → lam ≤ 1 / 2 → DifferentiableOn ℝ f (Set.Icc lo hi) →
    (MonotoneOn (deriv f) (Set.Icc lo hi) ∨ AntitoneOn (deriv f) (Set.Icc lo hi)) →
    (∀ y ∈ Set.Icc lo hi, j + lam ≤ deriv f y ∧ deriv f y ≤ j + 1 - lam) →
    ‖∑ n ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, e (f n)‖ ≤ K / lam) ∧
  (∀ C : ℝ, 1 ≤ C → ∃ K : ℝ, 0 < K ∧ ∀ (lo hi lam : ℝ) (f : ℝ → ℝ),
    lo ≤ hi → 0 < lam → ContDiffOn ℝ 2 f (Set.Icc lo hi) →
    (∀ y ∈ Set.Icc lo hi, lam ≤ |iteratedDeriv 2 f y| ∧
      |iteratedDeriv 2 f y| ≤ C * lam) →
    ‖∑ n ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, e (f n)‖ ≤
      K * ((hi - lo + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹))

/-- A Fourier coefficient measure is an explicit factorization, not an abstract oracle.
The derivatives can grow by a fixed power per order; the frequency cutoff is fixed
before the requested saving A. -/
def FourierSeparation : Prop :=
  ∀ b : ℕ, ∀ C R : ℝ, 0 < C → 0 < R → ∀ bounds : ℕ → ℝ,
    (∀ j, 0 ≤ bounds j) → ∃ C' K : ℝ, C < C' ∧ 0 < K ∧
      ∀ A : ℝ, 0 < A → ∃ KA : ℝ, 0 < KA ∧
      ∀ᶠ x : ℝ in atTop, ∀ F : (Fin b → ℝ) → ℂ,
        ContDiff ℝ ∞ F → Function.support F ⊆ Metric.closedBall 0 R →
        (∀ j y, ‖iteratedFDeriv ℝ j F y‖ ≤ bounds j * L x ^ (C * (j + 1))) →
        ∃ a : (Fin b → ℝ) → ℂ,
          Integrable a ∧ (∫ ξ, ‖a ξ‖) ≤ L x ^ K ∧
          (∀ y, F y = ∫ ξ, a ξ * e (∑ i, ξ i * y i)) ∧
          (∫ ξ in {ξ : Fin b → ℝ | L x ^ C' < ‖ξ‖}, ‖a ξ‖) ≤ KA * L x ^ (-A)

structure ClassicalInputs : Prop where
  progressions : PrimeProgressions
  mertens : MertensEstimates
  harmonic : HarmonicCharacters
  divisors : DivisorMoments
  means : MeanSquares
  largeSieve : MultiplicativeLargeSieve
  derivatives : DerivativeTests
  separation : FourierSeparation

-- `classical_inputs` is proved in `Erdos821/P1/ClassicalInputs.lean`.

end Erdos821.Blueprint
