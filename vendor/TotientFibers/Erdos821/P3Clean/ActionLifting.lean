import Erdos821.P3Clean.FourierLifting

/-! Transferring from the regular translation representation to finite weighted orbits. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem weighted_fibre_forms_bound {α β : Type*} [Fintype α] [Fintype β]
    (mass : α → ℝ) (weight : β → ℝ) (K : β → α → α → ℂ) (C : ℝ)
    (hm : ∀ a, 0 ≤ mass a) (hw : ∀ j, 0 ≤ weight j) (hC : 0 ≤ C)
    (hK : ∀ j, NormBound mass (K j) C) (f g : β → α → ℂ) :
    ‖∑ j, (weight j : ℂ) *
      ∑ a, ∑ b, (mass a : ℂ) * star (f j a) * K j a b * g j b‖ ≤
      C * Real.sqrt (∑ j, weight j * ∑ a, mass a * ‖f j a‖ ^ 2) *
        Real.sqrt (∑ j, weight j * ∑ b, mass b * ‖g j b‖ ^ 2) := by
  have hf (j : β) : 0 ≤ weight j * ∑ a, mass a * ‖f j a‖ ^ 2 :=
    mul_nonneg (hw j) (Finset.sum_nonneg (fun a _ => mul_nonneg (hm a) (sq_nonneg _)))
  have hg (j : β) : 0 ≤ weight j * ∑ b, mass b * ‖g j b‖ ^ 2 :=
    mul_nonneg (hw j) (Finset.sum_nonneg (fun b _ => mul_nonneg (hm b) (sq_nonneg _)))
  have hscale (j : β) (U V : ℝ) : weight j * (C * Real.sqrt U * Real.sqrt V) =
      C * (Real.sqrt (weight j * U) * Real.sqrt (weight j * V)) := by
    rw [Real.sqrt_mul (hw j), Real.sqrt_mul (hw j)]
    have he := Real.sq_sqrt (hw j)
    calc
      _ = C * ((Real.sqrt (weight j)) ^ 2 * (Real.sqrt U * Real.sqrt V)) := by rw [he]; ring
      _ = _ := by ring
  calc
    _ ≤ ∑ j, ‖(weight j : ℂ) *
        ∑ a, ∑ b, (mass a : ℂ) * star (f j a) * K j a b * g j b‖ := norm_sum_le _ _
    _ = ∑ j, weight j *
        ‖∑ a, ∑ b, (mass a : ℂ) * star (f j a) * K j a b * g j b‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)]
    _ ≤ ∑ j, weight j * (C * Real.sqrt (∑ a, mass a * ‖f j a‖ ^ 2) *
        Real.sqrt (∑ b, mass b * ‖g j b‖ ^ 2)) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hK j Finset.univ Finset.univ (f j) (g j)) (hw j)
    _ = C * ∑ j, Real.sqrt (weight j * ∑ a, mass a * ‖f j a‖ ^ 2) *
        Real.sqrt (weight j * ∑ b, mass b * ‖g j b‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact hscale j _ _
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le Finset.univ hf hg) hC

theorem weighted_orbit_sum_real {G V : Type*} [Fintype G] [Fintype V]
    (act : G → V ≃ V) (weight : V → ℝ)
    (hw : ∀ r v, weight (act r v) = weight v) (f : V → ℝ) :
    (∑ v : V, ∑ r : G, weight v * f (act r v)) =
      (Fintype.card G : ℝ) * ∑ v : V, weight v * f v := by
  rw [Finset.sum_comm]
  have h (r : G) : (∑ v : V, weight v * f (act r v)) = ∑ v : V, weight v * f v := by
    have hh := Equiv.sum_comp (act r) (fun v => weight v * f v)
    simpa only [hw] using hh
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem weighted_orbit_sum_complex {G V : Type*} [Fintype G] [Fintype V]
    (act : G → V ≃ V) (weight : V → ℝ)
    (hw : ∀ r v, weight (act r v) = weight v) (f : V → ℂ) :
    (∑ v : V, ∑ r : G, (weight v : ℂ) * f (act r v)) =
      (Fintype.card G : ℂ) * ∑ v : V, (weight v : ℂ) * f v := by
  rw [Finset.sum_comm]
  have h (r : G) : (∑ v : V, (weight v : ℂ) * f (act r v)) =
      ∑ v : V, (weight v : ℂ) * f v := by
    have hh := Equiv.sum_comp (act r) (fun v => (weight v : ℂ) * f v)
    simpa only [hw] using hh
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem orbit_energy {α G V : Type*} [Fintype α] [Fintype G] [Fintype V]
    (mass : α → ℝ) (weight : V → ℝ) (act : G → V ≃ V)
    (hw : ∀ r v, weight (act r v) = weight v) (f : α × V → ℂ) :
    (∑ v : V, weight v * ∑ p : α × G, mass p.1 * ‖f (p.1, act p.2 v)‖ ^ 2) =
      (Fintype.card G : ℝ) * ∑ p : α × V, mass p.1 * weight p.2 * ‖f p‖ ^ 2 := by
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ a : α, ∑ v : V, ∑ r : G, weight v * (mass a * ‖f (a, act r v)‖ ^ 2)) =
        ∑ a : α, (Fintype.card G : ℝ) * ∑ v : V, weight v * (mass a * ‖f (a, v)‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      exact weighted_orbit_sum_real act weight hw (fun v => mass a * ‖f (a, v)‖ ^ 2)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro v _
      ring

theorem orbit_regular_form {α G V : Type*} [Fintype α] [AddCommGroup G]
    [Fintype G] [Fintype V] (mass : α → ℝ) (weight : V → ℝ)
    (act : G → V ≃ V) (hw : ∀ r v, weight (act r v) = weight v)
    (hact : ∀ r d v, act (r + d) v = act d (act r v))
    (H : α → α → G → ℂ) (f g : α × V → ℂ) :
    (∑ v : V, (weight v : ℂ) *
      ∑ p : α × G, ∑ q : α × G,
        (mass p.1 : ℂ) * star (f (p.1, act p.2 v)) * translationLift H p q *
          g (q.1, act q.2 v)) =
      (Fintype.card G : ℂ) * ∑ a : α, ∑ b : α, ∑ d : G, ∑ v : V,
        (weight v : ℂ) * ((mass a : ℂ) * star (f (a, v)) * H a b d * g (b, act d v)) := by
  classical
  simp only [translationLift_form, hact, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  conv_lhs =>
    arg 2
    ext v
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simpa only [Finset.mul_sum] using weighted_orbit_sum_complex act weight hw
    (fun v => (mass a : ℂ) * star (f (a, v)) * H a b d * g (b, act d v))

theorem controlled_translation_form_bound {α G V : Type*} [Fintype α] [AddCommGroup G]
    [Fintype G] [Fintype V] (mass : α → ℝ) (weight : V → ℝ)
    (act : G → V ≃ V) (hw : ∀ r v, weight (act r v) = weight v)
    (hact : ∀ r d v, act (r + d) v = act d (act r v))
    (H : α → α → G → ℂ) (C : ℝ)
    (hm : ∀ a, 0 ≤ mass a) (hw0 : ∀ v, 0 ≤ weight v) (hC : 0 ≤ C)
    (hH : ∀ ψ : AddChar G ℂ, NormBound mass (fourierFibre H ψ) C)
    (f g : α × V → ℂ) :
    ‖∑ a : α, ∑ b : α, ∑ d : G, ∑ v : V,
      (weight v : ℂ) * ((mass a : ℂ) * star (f (a, v)) * H a b d * g (b, act d v))‖ ≤
      C * Real.sqrt (∑ p : α × V, mass p.1 * weight p.2 * ‖f p‖ ^ 2) *
        Real.sqrt (∑ p : α × V, mass p.1 * weight p.2 * ‖g p‖ ^ 2) := by
  have hreg := normBound_translationLift mass H C hm hC hH
  have h := weighted_fibre_forms_bound (fun p : α × G => mass p.1) weight
    (fun _ => translationLift H) C (fun p => hm p.1) hw0 hC (fun _ => hreg)
    (fun v p => f (p.1, act p.2 v)) (fun v p => g (p.1, act p.2 v))
  rw [orbit_regular_form mass weight act hw hact H f g,
    orbit_energy mass weight act hw f, orbit_energy mass weight act hw g] at h
  simp only [norm_mul, Complex.norm_natCast] at h
  have hn : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [Real.sqrt_mul hn.le, Real.sqrt_mul hn.le] at h
  have heq (U V : ℝ) : C * (Real.sqrt (Fintype.card G : ℝ) * Real.sqrt U) *
      (Real.sqrt (Fintype.card G : ℝ) * Real.sqrt V) =
      (Fintype.card G : ℝ) * (C * Real.sqrt U * Real.sqrt V) := by
    calc
      _ = (Real.sqrt (Fintype.card G : ℝ)) ^ 2 *
          (C * Real.sqrt U * Real.sqrt V) := by ring
      _ = _ := by rw [Real.sq_sqrt hn.le]
  rw [heq] at h
  exact le_of_mul_le_mul_left h hn


end Erdos821.P3Clean
