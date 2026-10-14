import Erdos821.P3Clean.MatrixSandwich

/-! Sparse coefficients for conditioning a finite fibre at each residue state. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

def fibreCoefficient {X Y D : Type*} (s : Y → Finset X) (p : X → D) (c : Y → ℂ)
    (d : D) (y : Y) (a : X × Y) : ℂ :=
  if y = a.2 ∧ a.1 ∈ s a.2 ∧ p a.1 = d then c a.2 else 0

theorem finiteLinearMap_fibre {X Y D : Type*} [Fintype X] [Fintype Y]
    (s : Y → Finset X) (p : X → D) (c : Y → ℂ) (d : D) (f : X × Y → ℂ) (y : Y) :
    finiteLinearMap (fibreCoefficient s p c d) f y =
      c y * ∑ x ∈ (s y).filter (fun x => p x = d), f (x, y) := by
  classical
  simp only [finiteLinearMap, Fintype.sum_prod_type, fibreCoefficient]
  simp [ite_and, mul_ite, ite_mul, Finset.sum_ite_mem, Finset.mul_sum, Finset.sum_filter]

theorem fibre_entry_sum {X Y D : Type*} [Fintype Y] [Fintype D]
    (s : Y → Finset X) (p : X → D) (c : Y → ℂ) (mass : Y → ℝ)
    (H : D → Y → Y → ℂ) (a b : X × Y) :
    (∑ d : D, ∑ y : Y, ∑ z : Y,
      (mass y : ℂ) * star (fibreCoefficient s p c d y a) * H d y z *
        fibreCoefficient s p c d z b) =
      if a.1 ∈ s a.2 ∧ b.1 ∈ s b.2 ∧ p a.1 = p b.1 then
        (mass a.2 : ℂ) * star (c a.2) * H (p a.1) a.2 b.2 * c b.2 else 0 := by
  classical
  rcases a with ⟨x, y⟩
  rcases b with ⟨w, z⟩
  simp only [fibreCoefficient]
  by_cases hx : x ∈ s y <;> by_cases hw : w ∈ s z <;> by_cases hp : p x = p w
  all_goals simp [hx, hw, hp, apply_ite, ite_and, mul_ite, ite_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', mul_assoc]

def fibreMass {X Y : Type*} (s : Y → Finset X) (m : ℝ) (mass : Y → ℝ) (a : X × Y) : ℝ :=
  if a.1 ∈ s a.2 then m * mass a.2 else 0

theorem fibreMass_entry {X Y D : Type*} [Fintype Y] [Fintype D]
    (s : Y → Finset X) (p : X → D) (c : Y → ℂ) (m : ℝ) (mass : Y → ℝ)
    (K : (X × Y) → (X × Y) → ℂ) (H : D → Y → Y → ℂ)
    (hentry : ∀ a b, (m : ℂ) * K a b =
      if a.1 ∈ s a.2 ∧ b.1 ∈ s b.2 ∧ p a.1 = p b.1 then
        star (c a.2) * c b.2 * H (p a.1) a.2 b.2 else 0)
    (a b : X × Y) :
    (fibreMass s m mass a : ℂ) * K a b =
      ∑ d, ∑ y, ∑ z, (mass y : ℂ) * star (fibreCoefficient s p c d y a) *
        H d y z * fibreCoefficient s p c d z b := by
  classical
  rw [fibre_entry_sum]
  by_cases ha : a.1 ∈ s a.2
  · simp only [fibreMass, if_pos ha, Complex.ofReal_mul]
    calc
      _ = (mass a.2 : ℂ) * ((m : ℂ) * K a b) := by ring
      _ = _ := by
        rw [hentry]
        by_cases h : a.1 ∈ s a.2 ∧ b.1 ∈ s b.2 ∧ p a.1 = p b.1
        · simp only [if_pos h]
          ring
        · simp only [if_neg h, mul_zero]
  · simp [fibreMass, ha]

theorem fibreMass_energy {X Y : Type*} [Fintype X] [Fintype Y]
    (s : Y → Finset X) (m : ℝ) (mass : Y → ℝ) (f : X × Y → ℂ) :
    (∑ a : X × Y, fibreMass s m mass a * ‖f a‖ ^ 2) =
      ∑ y : Y, mass y * (m * ∑ x ∈ s y, ‖f (x, y)‖ ^ 2) := by
  classical
  simp only [Fintype.sum_prod_type, fibreMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem fibre_energy_bound {X Y D : Type*} [Fintype X] [Fintype Y] [Fintype D]
    (s : Y → Finset X) (p : X → D) (c : Y → ℂ) (m S : ℝ) (mass : Y → ℝ)
    (hm : ∀ y, 0 ≤ mass y)
    (hper : ∀ y (f : X → ℂ),
      (∑ d : D, ‖c y * ∑ x ∈ (s y).filter (fun x => p x = d), f x‖ ^ 2) ≤
        S * (m * ∑ x ∈ s y, ‖f x‖ ^ 2)) (f : X × Y → ℂ) :
    (∑ d : D, ∑ y : Y, mass y * ‖finiteLinearMap (fibreCoefficient s p c d) f y‖ ^ 2) ≤
      S * ∑ a : X × Y, fibreMass s m mass a * ‖f a‖ ^ 2 := by
  classical
  rw [fibreMass_energy, Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro y _
  simp only [finiteLinearMap_fibre]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (hper y (fun x => f (x, y))) (hm y)).trans_eq (by ring)

theorem normBound_fibreSandwich {X Y D : Type*} [Fintype X] [Fintype Y] [Fintype D]
    (s : Y → Finset X) (p : X → D) (c : Y → ℂ) (m : ℝ) (mass : Y → ℝ)
    (K : (X × Y) → (X × Y) → ℂ) (H : D → Y → Y → ℂ) (C S : ℝ)
    (hm : ∀ y, 0 ≤ mass y) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hH : ∀ d, NormBound mass (H d) C)
    (hper : ∀ y (f : X → ℂ),
      (∑ d : D, ‖c y * ∑ x ∈ (s y).filter (fun x => p x = d), f x‖ ^ 2) ≤
        S * (m * ∑ x ∈ s y, ‖f x‖ ^ 2))
    (hentry : ∀ a b, (m : ℂ) * K a b =
      if a.1 ∈ s a.2 ∧ b.1 ∈ s b.2 ∧ p a.1 = p b.1 then
        star (c a.2) * c b.2 * H (p a.1) a.2 b.2 else 0) :
    NormBound (fibreMass s m mass) K (C * S) := by
  apply normBound_matrixSandwich _ mass K H (fibreCoefficient s p c) C S hm hC hS hH
  · exact fibre_energy_bound s p c m S mass hm hper
  · exact fibreMass_entry s p c m mass K H hentry


end Erdos821.P3Clean
