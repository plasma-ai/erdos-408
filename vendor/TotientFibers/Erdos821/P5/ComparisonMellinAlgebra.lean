import Erdos821.P5.ComparisonCellScales
import Erdos821.P5.MellinPatternIntegral

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- The source sequence after harmonic normalization and cutoff separation.
The mark function and every argument are independent of the free products. -/
def comparisonMellinSource (G : PrimeGroups) (x Y a v : ℝ) (E : Endpoint)
    (mark : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((Y : ℂ) / (n : ℂ)) * mellin n (-a) * mellin ((n : ℝ) / Y) (-v) *
    endpoint G x E n * star (mark n)

def comparisonMellinTarget (G : PrimeGroups) (x a : ℝ) (E : Endpoint)
    (mark : ℕ → ℂ) (n : ℕ) : ℂ :=
  mellin n a * endpoint G x E n * mark n

/-- A unit-norm test on one free product after separating the cutoff. -/
def comparisonMellinTest (U a₁ a₂ v : ℝ) (D : ℕ) : ℂ :=
  mellin D (-a₁ - a₂) * mellin ((D : ℝ) / U) (-v)

@[simp] theorem comparisonMellinTest_norm (U a₁ a₂ v : ℝ) (D : ℕ) :
    ‖comparisonMellinTest U a₁ a₂ v D‖ = 1 := by
  simp [comparisonMellinTest]

theorem comparisonMellinSource_norm (G : PrimeGroups) (x Y a v : ℝ)
    (E : Endpoint) (mark : ℕ → ℂ) (n : ℕ) :
    ‖comparisonMellinSource G x Y a v E mark n‖ =
      |Y| / n * ‖endpoint G x E n‖ * ‖mark n‖ := by
  simp [comparisonMellinSource, Complex.norm_real]

theorem comparisonMellinTarget_norm (G : PrimeGroups) (x a : ℝ)
    (E : Endpoint) (mark : ℕ → ℂ) (n : ℕ) :
    ‖comparisonMellinTarget G x a E mark n‖ = ‖endpoint G x E n‖ * ‖mark n‖ := by
  simp [comparisonMellinTarget]

/-- The cell scale moves entirely into two separate free-product tests. -/
theorem comparison_cutoff_mellin_split (Z UA UB w DA DB v : ℝ)
    (hZ : 0 < Z) (hUA : 0 < UA) (hUB : 0 < UB)
    (hw : 0 < w) (hDA : 0 < DA) (hDB : 0 < DB) :
    mellin (w / (Z * (DA * DB))) v =
      mellin (w / (Z * (UA * UB))) v *
        mellin (DA / UA) (-v) * mellin (DB / UB) (-v) := by
  have hy : w / (Z * (DA * DB)) =
      (w / (Z * (UA * UB))) / ((DA / UA) * (DB / UB)) := by
    field_simp
  rw [hy, mellin_div _ _ _ (div_pos hw (mul_pos hZ (mul_pos hUA hUB)))
    (mul_pos (div_pos hDA hUA) (div_pos hDB hUB)),
    mellin_mul _ _ _ (div_pos hDA hUA) (div_pos hDB hUB)]
  ring

/-- Exact scalar factorization before Fourier inversion. The source and
target sequences use no free product; the two free tests have norm one. -/
theorem comparison_mellin_scalar_factor (G : PrimeGroups) (x Z UA UB a₁ a₂ v : ℝ)
    (E H : Endpoint) (mark₁ mark₂ : ℕ → ℂ) (w w' DA DB : ℕ)
    (hZ : 0 < Z) (hUA : 0 < UA) (hUB : 0 < UB)
    (hw : 0 < w) (hw' : 0 < w') (hDA : 0 < DA) (hDB : 0 < DB) :
    (mellin ((w : ℝ) / (Z * (DA * DB : ℕ))) v / (w : ℂ)) *
      mellin ((w : ℝ) / (DA * DB : ℕ)) a₁ *
      mellin ((w' : ℝ) / (DA * DB : ℕ)) a₂ *
      star (endpoint G x E w) * endpoint G x H w' * (mark₁ w * mark₂ w') =
    (Z * (UA * UB) : ℂ)⁻¹ * comparisonMellinTest UA a₁ a₂ v DA *
      comparisonMellinTest UB a₁ a₂ v DB *
      star (comparisonMellinSource G x (Z * (UA * UB)) a₁ v E mark₁ w) *
      comparisonMellinTarget G x a₂ H mark₂ w' := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hw'R : (0 : ℝ) < w' := by exact_mod_cast hw'
  have hDAR : (0 : ℝ) < DA := by exact_mod_cast hDA
  have hDBR : (0 : ℝ) < DB := by exact_mod_cast hDB
  have hDC : (0 : ℝ) < (DA : ℝ) * DB := mul_pos hDAR hDBR
  have hY : (Z * (UA * UB) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos hZ (mul_pos hUA hUB)).ne'
  have hp (a : ℝ) : mellin ((DA : ℝ) * DB) (-a) =
      mellin DA (-a) * mellin DB (-a) := mellin_mul _ _ _ hDAR hDBR
  have hmerge (D : ℝ) : mellin D (-a₁) * mellin D (-a₂) =
      mellin D (-a₁ - a₂) := by rw [← mellin_add]; congr 1
  push_cast
  rw [comparison_cutoff_mellin_split Z UA UB w DA DB v hZ hUA hUB hwR hDAR hDBR,
    mellin_div _ _ _ hwR hDC, mellin_div _ _ _ hw'R hDC, hp a₁, hp a₂]
  simp only [comparisonMellinTest, comparisonMellinSource, comparisonMellinTarget,
    star_mul, star_div₀, star_mellin, neg_neg, star_star, star_natCast]
  have hstarY : star ((Z * (UA * UB) : ℝ) : ℂ) = ((Z * (UA * UB) : ℝ) : ℂ) := by simp
  rw [hstarY]
  have hcancel : (Z * (UA * UB) : ℂ)⁻¹ * ((Z * (UA * UB) : ℝ) : ℂ) = 1 := by
    push_cast
    exact inv_mul_cancel₀ hY
  have hm : mellin DA (-a₁) * mellin DA (-a₂) *
      (mellin DB (-a₁) * mellin DB (-a₂)) =
      mellin DA (-a₁ - a₂) * mellin DB (-a₁ - a₂) := by
    rw [hmerge, hmerge]
  calc
    _ = ((Z * (UA * UB) : ℂ)⁻¹ * ((Z * (UA * UB) : ℝ) : ℂ)) *
        (mellin ((w : ℝ) / (Z * (UA * UB))) v *
          mellin ((DA : ℝ) / UA) (-v) * mellin ((DB : ℝ) / UB) (-v) *
          mellin w a₁ * mellin w' a₂ * star (endpoint G x E w) *
          endpoint G x H w' * mark₁ w * mark₂ w' / (w : ℂ) *
          (mellin DA (-a₁) * mellin DA (-a₂) *
            (mellin DB (-a₁) * mellin DB (-a₂)))) := by
            rw [hcancel]
            ring
    _ = _ := by
      rw [hm]
      push_cast
      ring


end Erdos821.P5Core
