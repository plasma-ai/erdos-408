import Erdos821.P3Clean.ActiveDensity

/-! Shared density factors cancel under the square-root identification. -/

noncomputable section

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem sqrt_density_balance (A B P Q : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hP : 0 < P) (hQ : 0 < Q) (h : A * Q = B * P) :
    Real.sqrt A / Real.sqrt B * Q = Real.sqrt P * Real.sqrt Q := by
  have hx : 0 ≤ Real.sqrt A / Real.sqrt B * Q :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hQ.le
  have hy : 0 ≤ Real.sqrt P * Real.sqrt Q := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (sq_eq_sq₀ hx hy).mp
  simp only [mul_pow, div_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le,
    Real.sq_sqrt hP.le, Real.sq_sqrt hQ.le]
  calc
    _ = (A * Q) / B * Q := by field_simp [hB.ne']
    _ = _ := by rw [h]; field_simp [hB.ne']

theorem normalizedFreshDensityFactor (F : FixedData) (P : PrimeGroups) (n : ℕ)
    {J m : ℕ} (ν : Pattern P J F.ell m) (a b : P.BigLabels (J + F.ell))
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (h : ν.matchesBig a b) :
    Real.sqrt (activeDensity F n a) / Real.sqrt (activeDensity F n b) * tiltedFreshMass F n ν b =
      ν.freshMass b * (Real.sqrt (freshDensity F n ν a) * Real.sqrt (freshDensity F n ν b)) := by
  rw [tiltedFreshMass_density]
  have he := sqrt_density_balance
    (activeDensity F n a) (activeDensity F n b) (freshDensity F n ν a) (freshDensity F n ν b)
    (activeDensity_pos F n hb a) (activeDensity_pos F n hb b)
    (freshDensity_pos F n ν hb a) (freshDensity_pos F n ν hb b)
    (density_reversal F n ν a b h)
  calc
    _ = ν.freshMass b *
        (Real.sqrt (activeDensity F n a) / Real.sqrt (activeDensity F n b) * freshDensity F n ν b) := by ring
    _ = _ := by rw [he]


end Erdos821.P3Clean
