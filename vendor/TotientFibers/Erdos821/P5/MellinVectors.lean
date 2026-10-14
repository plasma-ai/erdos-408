import Erdos821.P5.Schur

noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem mellin_add (n t u : ℝ) : mellin n (t + u) = mellin n t * mellin n u := by
  simp [Blueprint.Analytic.mellin, add_mul, mul_add, Complex.exp_add]

@[simp] theorem star_mellin (n t : ℝ) : star (mellin n t) = mellin n (-t) := by
  simp [Blueprint.Analytic.mellin, Complex.star_def, ← Complex.exp_conj]

theorem mellin_sub (n t u : ℝ) : mellin n (t - u) = mellin n t * star (mellin n u) := by
  rw [sub_eq_add_neg, mellin_add, star_mellin]

def dpVector (I : Finset ℕ) (c : ℕ → ℂ) : EuclideanSpace ℂ ↥I :=
  WithLp.toLp 2 (fun n : ↥I => c n.val)

def mellinVector (I : Finset ℕ) (t : ℝ) : EuclideanSpace ℂ ↥I :=
  dpVector I (fun n => star (Blueprint.Analytic.mellin n t))

theorem dpVector_norm_sq (I : Finset ℕ) (c : ℕ → ℂ) :
    ‖dpVector I c‖ ^ 2 = sqNorm I c := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ n : ↥I, ‖c n.val‖ ^ 2) = ∑ n ∈ I, ‖c n‖ ^ 2
  exact (Finset.sum_subtype I (by simp) (fun n => ‖c n‖ ^ 2)).symm

theorem dpVector_inner (I : Finset ℕ) (c d : ℕ → ℂ) :
    ⟪dpVector I c, dpVector I d⟫_ℂ = ∑ n ∈ I, d n * star (c n) := by
  change (∑ n : ↥I, d n.val * star (c n.val)) = ∑ n ∈ I, d n * star (c n)
  exact (Finset.sum_subtype I (by simp) (fun n => d n * star (c n))).symm

theorem mellinVector_sample (I : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    ⟪mellinVector I t, dpVector I c⟫_ℂ = dp I c t := by
  rw [mellinVector, dpVector_inner]
  simp only [star_star, dp]

theorem mellinVector_gram (I : Finset ℕ) (t u : ℝ) :
    ⟪mellinVector I t, mellinVector I u⟫_ℂ = dp I (fun _ => 1) (t - u) := by
  rw [mellinVector, mellinVector, dpVector_inner]
  simp only [star_star, dp, one_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [mellin_sub]
  ring

def extendCoefficients (s : Finset ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ s then c n else 0

theorem dp_extend (s I : Finset ℕ) (c : ℕ → ℂ) (hSI : s ⊆ I) (t : ℝ) :
    dp I (extendCoefficients s c) t = dp s c t := by
  classical
  unfold dp
  calc
    _ = ∑ n ∈ s, extendCoefficients s c n * mellin n t :=
      (Finset.sum_subset hSI (fun n _ hn => by simp [extendCoefficients, hn])).symm
    _ = _ := Finset.sum_congr rfl (fun n hn => by simp [extendCoefficients, hn])

theorem sqNorm_extend (s I : Finset ℕ) (c : ℕ → ℂ) (hSI : s ⊆ I) :
    sqNorm I (extendCoefficients s c) = sqNorm s c := by
  classical
  unfold sqNorm
  calc
    _ = ∑ n ∈ s, ‖extendCoefficients s c n‖ ^ 2 :=
      (Finset.sum_subset hSI (fun n _ hn => by simp [extendCoefficients, hn])).symm
    _ = _ := Finset.sum_congr rfl (fun n hn => by simp [extendCoefficients, hn])

end Erdos821.P5Core
