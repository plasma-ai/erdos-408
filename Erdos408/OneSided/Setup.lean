import Erdos408.Hypotheses
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Setup for the one-sided Type II estimate

The objects of `blueprint/one_sided_type_ii.md` §§0–1 and §3: the varying data of
`OneSidedTypeII` at one `x`, its hypotheses, the parameter choices, and the two squares
compared in the proof.

* `Data` bundles the band exponents, the scale exponent, the scales `H_m, H_n`, the
  invariant endpoint `F` and the coefficients `α, β`. `Admissible` is the list of
  hypotheses of `OneSidedTypeII` on them apart from the twisted cancellation P4
  (`TwistBound`) and the kernel premise (G) (`KernelBound`).
* The exponents `D₁, E₀, G, A₀, K₀, B, A` of blueprint §1 depend only on `(D_*, C)`.
* `cauchySquare` is the Cauchy square `Q_Y` of PD (3.8): pairs of label products
  `a, b ≍ Y` with `mn - 1 = ah`, `rs - 1 = bh` for a common `h`.
* `majorSquare` is the major sum `Q_Y^maj` of PD (5.1), in which the equation
  `bmn - ars = b - a` is replaced by the major-arc kernel `𝓗_𝔐`.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real

/-- The varying data of `OneSidedTypeII` at one `x`: the band exponents, the scale exponent
`γ`, the scales `H_m, H_n`, the invariant endpoint `F` and the coefficients `α, β`. -/
structure Data (K : ℕ) where
  a : Fin K → ℝ
  γ : ℝ
  Hm : ℝ
  Hn : ℝ
  F : ℕ → ℂ
  α : ℕ → ℂ
  β : ℕ → ℂ

namespace Data

variable {K : ℕ} (d : Data K)

/-- `X = H_m H_n`. -/
def X : ℝ := d.Hm * d.Hn

/-- The range `[H_m, 2H_m]` of the marked variable. -/
def mRange : Finset ℕ := Icc ⌈d.Hm⌉₊ ⌊2 * d.Hm⌋₊

/-- The range `[H_n, 2H_n]` of the unmarked variable. -/
def nRange : Finset ℕ := Icc ⌈d.Hn⌉₊ ⌊2 * d.Hn⌋₊

/-- The label tuples: one prime from each band. -/
def labels (x : ℝ) : Finset (Fin K → ℕ) := Fintype.piFinset fun i => band x (d.a i)

/-- `∏_i V_i`, the product of the harmonic masses of the bands. -/
def bandMass (x : ℝ) : ℝ := ∏ i, harmonicMass (band x (d.a i))

end Data

variable {K : ℕ}

/-- The hypotheses of `OneSidedTypeII` on the varying data at `x`, apart from the twisted
cancellation P4 and the kernel premise (G). -/
structure Admissible (C CX alo ahi g x : ℝ) (d : Data K) : Prop where
  window : ∀ i, alo ≤ d.a i ∧ d.a i ≤ ahi
  gap : ∀ i j : Fin K, i < j → d.a i + g ≤ d.a j
  γ_ge : Real.log x ^ (-(1 / 100 : ℝ)) ≤ d.γ
  Hm_ge : x ^ d.γ ≤ d.Hm
  Hn_ge : x ^ d.γ ≤ d.Hn
  X_ge : x / CX ≤ d.Hm * d.Hn
  X_le : d.Hm * d.Hn ≤ CX * x
  F_le : ∀ h, ‖d.F h‖ ≤ 1
  F_inv : ∀ i h, ∀ p ∈ band x (d.a i), d.F (p * h) = d.F h
  α_supp : ∀ m, d.α m ≠ 0 →
    d.Hm ≤ m ∧ (m : ℝ) ≤ 2 * d.Hm ∧ IsRough x m ∧ ‖d.α m‖ ≤ Real.log x ^ C
  β_supp : ∀ n, d.β n ≠ 0 →
    d.Hn ≤ n ∧ (n : ℝ) ≤ 2 * d.Hn ∧ IsRough x n ∧ ‖d.β n‖ ≤ Real.log x ^ C

/-- P4: the twisted cancellation of `α`, for characters of modulus at most `L^{A₀}` and
frequencies `|t| ≤ 2 X L^B`. -/
def TwistBound (A₀ B A c₄ x : ℝ) (d : Data K) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → (k : ℝ) ≤ Real.log x ^ A₀ → ∀ (χ : DirichletCharacter ℂ k) (t : ℝ),
    |t| ≤ 2 * (d.Hm * d.Hn) * Real.log x ^ B →
    ‖(d.Hm : ℂ)⁻¹ * ∑ m ∈ Finset.Icc ⌈d.Hm⌉₊ ⌊2 * d.Hm⌋₊,
        d.α m * χ m * (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ c₄ * Real.log x ^ (-A)

/-- (G): the integer kernel at the scale `H_n`, for `1 ≤ |Δ| ≤ 4 X L^B + 2`. -/
def KernelBound (B cG x : ℝ) (d : Data K) : Prop :=
  ∀ Δ : ℝ, 1 ≤ |Δ| → |Δ| ≤ 4 * (d.Hm * d.Hn) * Real.log x ^ B + 2 →
    d.Hn⁻¹ * ‖∑ n ∈ Finset.Icc ⌈d.Hn⌉₊ ⌊2 * d.Hn⌋₊, (n : ℂ) ^ ((Δ : ℂ) * Complex.I)‖ ≤
      cG * (|Δ|⁻¹ + Real.exp (-Real.log x ^ (0.95 : ℝ)))

/-- `ω(n)`: the number of band primes dividing `n`. -/
def bandCount (x : ℝ) (d : Data K) (n : ℕ) : ℕ := ∑ i, primeCount (band x (d.a i)) n

/-- The one-sided Type II sum `∑ α_m β_n F(mn - 1) 𝒲(mn - 1)`. -/
def typeIISum (q x : ℝ) (d : Data K) : ℂ :=
  ∑ m ∈ Finset.Icc ⌈d.Hm⌉₊ ⌊2 * d.Hm⌋₊, ∑ n ∈ Finset.Icc ⌈d.Hn⌉₊ ⌊2 * d.Hn⌋₊,
    d.α m * d.β n * d.F (m * n - 1) *
      markedWeight Finset.univ q (fun i => band x (d.a i)) (m * n - 1)

/-! ### Parameters (blueprint §1) -/

/-- `D₁ = 2D_* + 2`, the precision of the Cauchy square. -/
def squarePrec (Dstar : ℝ) : ℝ := 2 * Dstar + 2

/-- `E₀ = D₁ + 4C + 2`, the precision of the determinant moment. -/
def momentPrec (Dstar C : ℝ) : ℝ := squarePrec Dstar + 4 * C + 2

/-- `G = E₀ + 4`, the contraction of one signed edge. -/
def edgePrec (Dstar C : ℝ) : ℝ := momentPrec Dstar C + 4

/-- `A₀ = G + 1`, the arc exponent and the modulus exponent of P4. -/
def arcExp (Dstar C : ℝ) : ℝ := edgePrec Dstar C + 1

/-- `K₀ = ⌈200 (G + 3)⌉`, so that `.005 K ≥ G + 3`. -/
def bandThreshold (Dstar C : ℝ) : ℕ := ⌈200 * (edgePrec Dstar C + 3)⌉₊

/-- `K₀ ≥ 1`: with no bands the label products are `1`, below every dyad, and the Cauchy
reduction says nothing. -/
theorem one_le_bandThreshold {Dstar C : ℝ} (hD : 0 < Dstar) (hC : 0 < C) :
    1 ≤ bandThreshold Dstar C := by
  unfold bandThreshold edgePrec momentPrec squarePrec
  exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne'

/-- `D = D₁ + 1`, the precision of the major term. -/
def majorPrec (Dstar : ℝ) : ℝ := squarePrec Dstar + 1

/-- `C₄ = 4C + 4`, the logarithmic loss in the mean value of `M_α N_β`. -/
def meanExp (C : ℝ) : ℝ := 4 * C + 4

/-- `B = D + 13A₀ + C₄`, the retained frequency exponent of P4 and (G) (blueprint §6.4). -/
def freqExp (Dstar C : ℝ) : ℝ := majorPrec Dstar + 13 * arcExp Dstar C + meanExp C

/-- `A' = 4(D + 13A₀) + 3C₄ + B`, the precision of the energy `∫ |B_λ M_α N_β|²`. -/
def energyExp (Dstar C : ℝ) : ℝ :=
  4 * (majorPrec Dstar + 13 * arcExp Dstar C) + 3 * meanExp C + freqExp Dstar C

/-- `A'' = A' + 4A₀ + 4`, the precision of the isolated energy `∫ |P_s M_α N_β|²`. -/
def isolatedExp (Dstar C : ℝ) : ℝ := energyExp Dstar C + 4 * arcExp Dstar C + 4

/-- `A_s = (A'' + C₄ + B + 2)/2`, the threshold of the sparse frequencies. -/
def sparseExp (Dstar C : ℝ) : ℝ := (isolatedExp Dstar C + meanExp C + freqExp Dstar C + 2) / 2

/-- `A = (A'' + 2C + 4)/2`, the precision of P4. -/
def twistExp (Dstar C : ℝ) : ℝ := (isolatedExp Dstar C + 2 * C + 4) / 2

/-! ### Cutoffs and arcs -/

/-- The dyadic bump `η(y) = s(y) - s(y/2)` with `s(y) = smoothTransition (y - 1)`. It is
smooth, supported in `[1, 4]`, and `∑_j η(b / 2^j) = 1` for `b ≥ 2`. -/
def dyadicBump (y : ℝ) : ℝ := smoothTransition (y - 1) - smoothTransition (y / 2 - 1)

/-- The plateau `ψ(t) = smoothTransition (5 - |t|)`: smooth, equal to one on `[-4, 4]` and
supported in `[-5, 5]`. -/
def plateau (t : ℝ) : ℝ := smoothTransition (5 - |t|)

/-- `∫_𝔐 e(θ n) dθ`, summed arc by arc over `|θ - h/k| ≤ 2 L^{A₀} / Y` with
`1 ≤ k ≤ L^{A₀}` and `(h, k) = 1`. -/
def arcIntegral (A₀ x Y : ℝ) (n : ℤ) : ℂ :=
  ∑ k ∈ Icc 1 ⌊Real.log x ^ A₀⌋₊, ∑ h ∈ (range k).filter (fun h => Nat.Coprime h k),
    ∫ θ in (-(2 * Real.log x ^ A₀ / Y))..(2 * Real.log x ^ A₀ / Y),
      Complex.exp (2 * π * Complex.I * ((((h : ℝ) / k + θ) * n : ℝ) : ℂ))

/-- The major-arc kernel `𝓗_𝔐(t; a, b) = ψ(t / Y) ∫_𝔐 e(θ (t - b + a)) dθ` of PD `eq:det-major`. -/
def majorWeight (A₀ x Y : ℝ) (t a b : ℤ) : ℂ :=
  (plateau (t / Y) : ℂ) * arcIntegral A₀ x Y (t - b + a)

/-! ### The two squares -/

open scoped Classical in
/-- The Cauchy square `Q_Y` of PD (3.8): label products `a = ∏ p_i`, `b = ∏ p'_i`, and
`mn - 1 = ah`, `rs - 1 = bh` for a common `h ≥ 1`. -/
def cauchySquare (x : ℝ) (d : Data K) (Y : ℝ) : ℂ :=
  ((d.bandMass x)⁻¹ ^ 2 : ℝ) *
    ∑ p ∈ d.labels x, ∑ p' ∈ d.labels x,
      (dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) : ℝ) *
        ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, ∑ r ∈ d.mRange, ∑ s ∈ d.nRange,
          if ∃ h, 1 ≤ h ∧ m * n - 1 = (∏ i, p i) * h ∧ r * s - 1 = (∏ i, p' i) * h then
            d.α m * star (d.α r) * d.β n * star (d.β s)
          else 0

/-- The major sum `Q_Y^maj` of PD (5.1): as `cauchySquare`, with the equation
`bmn - ars = b - a` replaced by `𝓗_𝔐(bmn - ars; a, b)`, and with no condition on the
label products. -/
def majorSquare (A₀ x : ℝ) (d : Data K) (Y : ℝ) : ℂ :=
  ((d.bandMass x)⁻¹ ^ 2 : ℝ) *
    ∑ p ∈ d.labels x, ∑ p' ∈ d.labels x,
      (dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) : ℝ) *
        ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, ∑ r ∈ d.mRange, ∑ s ∈ d.nRange,
          d.α m * star (d.α r) * d.β n * star (d.β s) *
            majorWeight A₀ x Y
              ((∏ i, p' i : ℕ) * m * n - (∏ i, p i : ℕ) * r * s) (∏ i, p i : ℕ) (∏ i, p' i : ℕ)

end Erdos408.OneSided
