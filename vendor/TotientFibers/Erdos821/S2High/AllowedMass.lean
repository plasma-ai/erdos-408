import Erdos821.S2High.PivotMoments

noncomputable section
open scoped BigOperators

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph

theorem tiltedMass_avoiding_finite_set_ge_half (F : FixedData) (P : PrimeGroups) (x : ℝ)
    (n : ℕ) (hP : P.Admissible F x)
    (hcut : (n + 1 : ℝ) ≤ Real.exp ((L x) ^ F.c) / 2)
    (g : P.BigGroup) (forbidden : Finset (P.Prime g.val)) (m : ℕ)
    (hcard : forbidden.card ≤ m)
    (hsmall : m * (2 / (F.vMin * Real.exp ((L x) ^ F.c))) ≤ 1 / 2) :
    (∑ p ∈ Finset.univ.filter (fun p : P.Prime g.val => p ∉ forbidden),
      tiltedMu F P n g.val p) ≥ 1 / 2 := by
  classical
  have hm := tiltedMu_group_mass_bounds F P x n hP hcut g
  let a : ℝ := 2 / (F.vMin * Real.exp ((L x) ^ F.c))
  have hden : 0 < F.vMin * Real.exp ((L x) ^ F.c) :=
    mul_pos F.vMin_pos (Real.exp_pos _)
  have ha : 0 ≤ a := (div_pos two_pos hden).le
  have htotal : 1 ≤ ∑ p : P.Prime g.val, tiltedMu F P n g.val p := hm.2.1
  have hbad : (∑ p ∈ forbidden, tiltedMu F P n g.val p) ≤ m * a := by
    calc
      (∑ p ∈ forbidden, tiltedMu F P n g.val p) ≤ ∑ p ∈ forbidden, a :=
        Finset.sum_le_sum fun p hp => by simpa [a] using (hm.1 p).2
      _ = (forbidden.card : ℝ) * a := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * a := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) ha
  have hbad' : (∑ p ∈ forbidden, tiltedMu F P n g.val p) ≤ 1 / 2 := by
    calc
      _ ≤ (m : ℝ) * a := hbad
      _ = m * (2 / (F.vMin * Real.exp ((L x) ^ F.c))) := by simp [a]
      _ ≤ 1 / 2 := hsmall
  have hsplit : (∑ p : P.Prime g.val, tiltedMu F P n g.val p) =
      (∑ p ∈ Finset.univ.filter (fun p : P.Prime g.val => p ∈ forbidden),
        tiltedMu F P n g.val p) +
      ∑ p ∈ Finset.univ.filter (fun p : P.Prime g.val => p ∉ forbidden),
        tiltedMu F P n g.val p := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun p : P.Prime g.val => p ∈ forbidden)]
  have hfilter : Finset.univ.filter (fun p : P.Prime g.val => p ∈ forbidden) = forbidden := by
    ext p
    simp
  have hbadEq : (∑ p ∈ forbidden, tiltedMu F P n g.val p) =
      (∑ p ∈ Finset.univ.filter (fun p : P.Prime g.val => p ∈ forbidden),
        tiltedMu F P n g.val p) := by rw [hfilter]
  rw [← hbadEq] at hsplit
  rw [hsplit] at htotal
  linarith


end Erdos821.S2High
