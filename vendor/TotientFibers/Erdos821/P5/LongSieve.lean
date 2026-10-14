import Erdos821.P5.Basic
import Erdos821.Blueprint.Sieve

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Analytic

def roughIndicator (z : ℝ) (n : ℕ) : ℝ := if rough z n then 1 else 0

def divisorPolynomial (lam : ℕ → ℝ) (n : ℕ) : ℝ := ∑ d ∈ n.divisors, lam d

def characterMellinTerm {r : ℕ} (χ : DirichletCharacter ℂ r) (u : ℝ) (n : ℕ) : ℂ :=
  χ (n : ZMod r) * mellin n u / (n : ℂ)

theorem characterMellinTerm_norm_le {r : ℕ} (χ : DirichletCharacter ℂ r)
    (u P : ℝ) (n : ℕ) (hP : 0 < P) (hn : P ≤ (n : ℝ)) :
    ‖characterMellinTerm χ u n‖ ≤ P⁻¹ := by
  have hnpos : 0 < (n : ℝ) := hP.trans_le hn
  rw [characterMellinTerm, norm_div, norm_mul, norm_mellin, mul_one,
    Complex.norm_natCast]
  calc
    ‖χ (n : ZMod r)‖ / (n : ℝ) ≤ 1 / (n : ℝ) :=
      div_le_div_of_nonneg_right (χ.norm_le_one _) hnpos.le
    _ ≤ P⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hP hn

/-- Nonnegative sieve error survives interval restriction and a bounded complex weight. -/
theorem rough_replacement_error (s : Finset ℕ) (z P : ℝ) (lam : ℕ → ℝ)
    (f : ℕ → ℂ) (_hP : 0 < P)
    (hupper : ∀ n ∈ s, roughIndicator z n ≤ divisorPolynomial lam n)
    (hf : ∀ n ∈ s, ‖f n‖ ≤ P⁻¹) :
    ‖(∑ n ∈ s.filter (rough z), f n) -
      ∑ n ∈ s, (divisorPolynomial lam n : ℂ) * f n‖ ≤
      (∑ n ∈ s, (divisorPolynomial lam n - roughIndicator z n)) / P := by
  classical
  have hind : (∑ n ∈ s.filter (rough z), f n) =
      ∑ n ∈ s, (roughIndicator z n : ℂ) * f n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : rough z n <;> simp [roughIndicator, h]
  rw [hind, norm_sub_rev, ← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ n ∈ s, ((divisorPolynomial lam n - roughIndicator z n : ℝ) : ℂ) * f n‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      push_cast
      ring
    _ ≤ ∑ n ∈ s, ‖((divisorPolynomial lam n - roughIndicator z n : ℝ) : ℂ) * f n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ s, (divisorPolynomial lam n - roughIndicator z n) * P⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have he : 0 ≤ divisorPolynomial lam n - roughIndicator z n := sub_nonneg.mpr (hupper n hn)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
      exact mul_le_mul_of_nonneg_left (hf n hn) he
    _ = _ := by rw [← Finset.sum_mul]; simp only [div_eq_mul_inv]

/-- Finite divisor expansion retains the full coefficient support. -/
theorem divisor_polynomial_expand (s : Finset ℕ) (D : ℝ) (lam : ℕ → ℝ)
    (f : ℕ → ℂ) (hs : ∀ n ∈ s, 0 < n)
    (hlam : ∀ d, lam d ≠ 0 → 0 < d ∧ (d : ℝ) ≤ D) :
    (∑ n ∈ s, (divisorPolynomial lam n : ℂ) * f n) =
      ∑ d ∈ Finset.Icc 1 ⌊D⌋₊, (lam d : ℂ) * ∑ n ∈ s.filter (fun n => d ∣ n), f n := by
  classical
  have hexpand (n : ℕ) (hn : n ∈ s) :
      (divisorPolynomial lam n : ℂ) =
        ∑ d ∈ Finset.Icc 1 ⌊D⌋₊, if d ∣ n then (lam d : ℂ) else 0 := by
    rw [divisorPolynomial, Complex.ofReal_sum]
    calc
      _ = ∑ d ∈ n.divisors.filter (fun d => d ∈ Finset.Icc 1 ⌊D⌋₊), (lam d : ℂ) := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro d hd hnot
        have hz : lam d = 0 := by
          by_contra hz
          have hmem := Finset.mem_Icc.mpr ⟨(hlam d hz).1, Nat.le_floor (hlam d hz).2⟩
          exact hnot (Finset.mem_filter.mpr ⟨hd, hmem⟩)
        simp [hz]
      _ = ∑ d ∈ (Finset.Icc 1 ⌊D⌋₊).filter (fun d => d ∣ n), (lam d : ℂ) := by
        apply Finset.sum_congr ?_ (fun _ _ => rfl)
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hd, _⟩, hI⟩
          exact ⟨hI, hd⟩
        · rintro ⟨hI, hd⟩
          exact ⟨⟨hd, (hs n hn).ne'⟩, hI⟩
      _ = _ := Finset.sum_filter _ _
  calc
    _ = ∑ n ∈ s, ∑ d ∈ Finset.Icc 1 ⌊D⌋₊,
        if d ∣ n then (lam d : ℂ) * f n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hexpand n hn, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> simp
    _ = ∑ d ∈ Finset.Icc 1 ⌊D⌋₊, ∑ n ∈ s,
        if d ∣ n then (lam d : ℂ) * f n else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]

/-- Cancellation on divisor progressions costs the harmonic coefficient mass. -/
theorem divisor_polynomial_bound (s : Finset ℕ) (D B : ℝ) (lam : ℕ → ℝ)
    (f : ℕ → ℂ) (hs : ∀ n ∈ s, 0 < n)
    (hlam : ∀ d, lam d ≠ 0 → 0 < d ∧ (d : ℝ) ≤ D)
    (hbound : ∀ d ∈ Finset.Icc 1 ⌊D⌋₊,
      ‖∑ n ∈ s.filter (fun n => d ∣ n), f n‖ ≤ B / d) :
    ‖∑ n ∈ s, (divisorPolynomial lam n : ℂ) * f n‖ ≤
      B * ∑ d ∈ Finset.Icc 1 ⌊D⌋₊, |lam d| / d := by
  classical
  rw [divisor_polynomial_expand s D lam f hs hlam]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊D⌋₊,
        ‖(lam d : ℂ) * ∑ n ∈ s.filter (fun n => d ∣ n), f n‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊D⌋₊, |lam d| * (B / d) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbound d hd) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

end Erdos821.P5Core
