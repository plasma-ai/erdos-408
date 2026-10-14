import Erdos821.P5.FullResidualStripping
import Erdos821.P5.MellinCutoffBridge

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

theorem imaginaryPower_eq_mellin (D : ℕ) (ζ : ℝ) :
    imaginaryPower D ζ = mellin D ζ := by
  unfold imaginaryPower Blueprint.Analytic.mellin
  congr 1
  ring

theorem mellin_div (a b v : ℝ) (ha : 0 < a) (hb : 0 < b) :
    mellin (a / b) v = mellin a v * mellin b (-v) := by
  simp only [Blueprint.Analytic.mellin, Real.log_div ha.ne' hb.ne']
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem physicalPatternBody_frequency {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ v : ℝ)
    (ν : Pattern G J F.ell m) (u : G.Aux J) (n n' : ℤ)
    (a b : G.Labels (J + F.ell)) :
    physicalPatternBody (B.model k (ζ - v)) ν u n n' a b =
      mellin (ν.D a u) (-v) * physicalPatternBody (B.model k ζ) ν u n n' a b := by
  let c : ℂ := (ν.physicalTargetMass * (B.model k ζ).damping n *
    (B.model k ζ).damping n' : ℝ) *
      ν.coefficient (G.restrictBig a) (G.restrictBig b) (fun g => u g.val)
  change (if (G.physical (J + F.ell) n a ∧ G.physical (J + F.ell) n' b) ∧
      ν.compatible a b ∧ ν.ban a b u ∧ n' = n + k * (ν.D a u : ℤ)
    then c * imaginaryPower (ν.D a u) (ζ - v) else 0) =
    mellin (ν.D a u) (-v) *
    (if (G.physical (J + F.ell) n a ∧ G.physical (J + F.ell) n' b) ∧
      ν.compatible a b ∧ ν.ban a b u ∧ n' = n + k * (ν.D a u : ℤ)
    then c * imaginaryPower (ν.D a u) ζ else 0)
  by_cases h : (G.physical (J + F.ell) n a ∧ G.physical (J + F.ell) n' b) ∧
    ν.compatible a b ∧ ν.ban a b u ∧ n' = n + k * (ν.D a u : ℤ)
  · rw [if_pos h, if_pos h, imaginaryPower_eq_mellin, imaginaryPower_eq_mellin,
      sub_eq_add_neg, mellin_add]
    ring
  · simp only [if_neg h, mul_zero]

/-- The source multiplier used on an actual dyad. Conjugation supplies the
positive Mellin frequency and the harmonic factor after division by X. -/
def mellinPairingSource (X Z : ℝ) (f : ℤ → ℂ) (v : ℝ) (n : ℤ) : ℂ :=
  ((X : ℂ) / (n : ℂ)) * mellin ((n : ℝ) / Z) (-v) * f n

theorem mellinPairingSource_norm_le (X Z : ℝ) (f : ℤ → ℂ) (v : ℝ)
    (hX : 0 < X) (n : ℤ) (hn : X ≤ (n : ℝ)) :
    ‖mellinPairingSource X Z f v n‖ ≤ ‖f n‖ := by
  have hnpos : 0 < (n : ℝ) := hX.trans_le hn
  have hc : ‖(X : ℂ) / (n : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (div_pos hX hnpos)]
    exact (div_le_one hnpos).mpr hn
  simp only [mellinPairingSource, norm_mul, norm_mellin, mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) hc

theorem normalized_mellin_gated_term {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ v X Z : ℝ)
    (ν : Pattern G J F.ell m) (u : G.Aux J) (T : Finset ℤ)
    (f g : ℤ → ℂ) (n : ℤ) (a b : G.Labels (J + F.ell))
    (hX : X ≠ 0) (hZ : 0 < Z) (hn : 0 < (n : ℝ)) :
    (X : ℂ)⁻¹ * gatedPatternTerm (B.model k (ζ - v)) ν u T
      (mellinPairingSource X Z f v) g (fun _ _ => 1) n a b =
    (mellin ((n : ℝ) / (Z * (ν.D a u : ℝ))) v / (n : ℂ)) *
      gatedPatternTerm (B.model k ζ) ν u T f g (fun _ _ => 1) n a b := by
  have hD : 0 < (ν.D a u : ℝ) := by
    rw [pattern_D_split]
    exact_mod_cast Nat.mul_pos (sharedProduct_pos ν a) (freeProduct_pos ν u)
  have hphase : mellin ((n : ℝ) / (Z * (ν.D a u : ℝ))) v =
      mellin ((n : ℝ) / Z) v * mellin (ν.D a u) (-v) := by
    rw [show (n : ℝ) / (Z * (ν.D a u : ℝ)) = ((n : ℝ) / Z) / (ν.D a u : ℝ) by ring,
      mellin_div _ _ _ (div_pos hn hZ) hD]
  have hXC : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hstarQuot : star ((X : ℂ) / (n : ℂ)) = (X : ℂ) / (n : ℂ) := by simp
  have ht : patternTarget (B.model k (ζ - v)) ν u n a =
      patternTarget (B.model k ζ) ν u n a := rfl
  simp only [gatedPatternTerm, ht, mellinPairingSource, star_mul,
    star_mellin, neg_neg, hstarQuot, one_mul]
  by_cases hT : patternTarget (B.model k ζ) ν u n a ∈ T
  · rw [if_pos hT, if_pos hT, physicalPatternBody_frequency, hphase]
    field_simp [hXC]
  · simp only [if_neg hT, mul_zero]

end Erdos821.P5Core
