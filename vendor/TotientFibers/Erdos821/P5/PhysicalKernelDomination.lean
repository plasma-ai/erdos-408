module

public import Erdos821.P5.DyadicTransference
public import Erdos821.S2.CountableSchur

@[expose] public section

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

theorem pattern_auxMass_nonneg {G : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (u : G.Aux J) (hV : ∀ g, 0 ≤ G.V g) :
    0 ≤ ν.auxMass u := listLaw_nonneg G u hV

theorem physicalRaw_true_eq_norm_patterns {F : FixedData} {G : PrimeGroups} {J m : ℕ}
    (A : Model F G J m) (hV : ∀ g, 0 ≤ G.V g) (n n' : ℤ) (a b : A.Labels) :
    A.physicalRaw true (n, a) (n', b) =
      ((∑ v : Fin A.patternCount, ∑ u : G.Aux J,
        (A.pattern v).auxMass u * ‖physicalPatternBody A (A.pattern v) u n n' a b‖ : ℝ) : ℂ) := by
  by_cases hp : G.physical (J + F.ell) n a ∧ G.physical (J + F.ell) n' b
  · simp only [Model.physicalRaw, hp, and_self, ite_true, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    have hmass : 0 ≤ (A.pattern v).physicalTargetMass := physicalTargetMass_nonneg (A.pattern v) hV
    have hdn : 0 ≤ A.damping n := Real.rpow_nonneg F.q_pos.le _
    have hdn' : 0 ≤ A.damping n' := Real.rpow_nonneg F.q_pos.le _
    unfold physicalPatternBody
    simp only [hp, true_and]
    split_ifs <;> simp only [norm_mul, imaginaryPower_eq_mellin, norm_mellin,
      mul_one, Complex.norm_real, Real.norm_of_nonneg hmass, Real.norm_of_nonneg hdn,
      Real.norm_of_nonneg hdn', Complex.ofReal_mul, Complex.ofReal_zero,
      norm_zero, mul_zero] <;> ring
  · simp only [Model.physicalRaw, hp, ite_false, physicalPatternBody, false_and,
      ite_false, norm_zero, mul_zero, Finset.sum_const_zero, Complex.ofReal_zero]

theorem physicalRaw_true_eq_norm {F : FixedData} {G : PrimeGroups} {J m : ℕ}
    (A : Model F G J m) (hV : ∀ g, 0 ≤ G.V g) (z z' : A.State) :
    A.physicalRaw true z z' = (‖A.physicalRaw true z z'‖ : ℝ) := by
  rw [physicalRaw_true_eq_norm_patterns A hV z.1 z'.1 z.2 z'.2]
  have hs : 0 ≤ ∑ v : Fin A.patternCount, ∑ u : G.Aux J,
      (A.pattern v).auxMass u * ‖physicalPatternBody A (A.pattern v) u z.1 z'.1 z.2 z'.2‖ :=
    Finset.sum_nonneg (fun v hv => Finset.sum_nonneg (fun u hu =>
      mul_nonneg (pattern_auxMass_nonneg (A.pattern v) u hV) (norm_nonneg _)))
  rw [Complex.norm_real, Real.norm_of_nonneg hs]

theorem physicalRaw_norm_le_absolute {F : FixedData} {G : PrimeGroups} {J m : ℕ}
    (A : Model F G J m) (hV : ∀ g, 0 ≤ G.V g) (z z' : A.State) :
    ‖A.physicalRaw false z z'‖ ≤ ‖A.physicalRaw true z z'‖ := by
  rw [physicalRaw_false_eq_patterns A z.1 z'.1 z.2 z'.2,
    physicalRaw_true_eq_norm_patterns A hV z.1 z'.1 z.2 z'.2]
  have hs : 0 ≤ ∑ v : Fin A.patternCount, ∑ u : G.Aux J,
      (A.pattern v).auxMass u * ‖physicalPatternBody A (A.pattern v) u z.1 z'.1 z.2 z'.2‖ :=
    Finset.sum_nonneg (fun v hv => Finset.sum_nonneg (fun u hu =>
      mul_nonneg (pattern_auxMass_nonneg (A.pattern v) u hV) (norm_nonneg _)))
  rw [Complex.norm_real, Real.norm_of_nonneg hs]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun v hv => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun u hu => ?_))
  simp only [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (pattern_auxMass_nonneg (A.pattern v) u hV)]
  exact le_rfl

theorem physicalKernel_norm_le_absolute {F : FixedData} {G : PrimeGroups} {J m : ℕ}
    (A : Model F G J m) (hV : ∀ g, 0 ≤ G.V g) (z z' : A.State) :
    ‖A.physicalKernel false z z'‖ ≤ ‖A.physicalKernel true z z'‖ := by
  have hs : 0 ≤ ∑ π : G.Permutations (J + F.ell), ∑ τ : G.Permutations (J + F.ell),
      ‖A.physicalRaw true (z.1, G.act π z.2) (z'.1, G.act τ z'.2)‖ :=
    Finset.sum_nonneg (fun π hπ => Finset.sum_nonneg (fun τ hτ => norm_nonneg _))
  have htrue : (∑ π : G.Permutations (J + F.ell), ∑ τ : G.Permutations (J + F.ell),
      A.physicalRaw true (z.1, G.act π z.2) (z'.1, G.act τ z'.2)) =
      ((∑ π : G.Permutations (J + F.ell), ∑ τ : G.Permutations (J + F.ell),
        ‖A.physicalRaw true (z.1, G.act π z.2) (z'.1, G.act τ z'.2)‖ : ℝ) : ℂ) := by
    simp_rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun π hπ => Finset.sum_congr rfl
      (fun τ hτ => physicalRaw_true_eq_norm A hV _ _))
  unfold Model.physicalKernel
  rw [norm_mul, norm_mul, htrue, Complex.norm_real, Real.norm_of_nonneg hs]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun π hπ => ?_))
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun τ hτ =>
    physicalRaw_norm_le_absolute A hV _ _))

theorem physicalKernel_zero_of_not_physical {F : FixedData} {G : PrimeGroups} {J m : ℕ}
    (A : Model F G J m) (absolute : Bool) (z z' : A.State)
    (h : ¬ G.physical (J + F.ell) z.1 z.2 ∨ ¬ G.physical (J + F.ell) z'.1 z'.2) :
    A.physicalKernel absolute z z' = 0 := by
  rcases h with h | h <;>
    simp [Model.physicalKernel, Model.physicalRaw, physical_act_iff, h]

end Erdos821.P5Core
