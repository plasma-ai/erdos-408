import Erdos821.P3Clean.Contractions
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! Finite Fourier identities for the residue translations of a clean edge. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

variable {G : Type*} [AddCommGroup G] [Fintype G]

def finiteFourier (f : G → ℂ) (ψ : AddChar G ℂ) : ℂ :=
  ∑ r : G, star (ψ r) * f r

theorem character_orthogonality (r s : G) :
    (∑ ψ : AddChar G ℂ, ψ r * star (ψ s)) =
      if r = s then (Fintype.card G : ℂ) else 0 := by
  classical
  simp_rw [Complex.star_def, ← AddChar.inv_apply_eq_conj,
    ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul]
  simpa only [← sub_eq_add_neg, sub_eq_zero] using AddChar.sum_apply_eq_ite (r - s)

theorem finiteFourier_inner (f g : G → ℂ) :
    (∑ ψ : AddChar G ℂ, star (finiteFourier f ψ) * finiteFourier g ψ) =
      (Fintype.card G : ℂ) * ∑ r : G, star (f r) * g r := by
  classical
  simp only [finiteFourier, star_sum, star_mul, star_star]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    (∑ ψ : AddChar G ℂ, ∑ r : G, ∑ s : G,
        (star (f r) * ψ r) * (star (ψ s) * g s)) =
        ∑ r : G, ∑ s : G, (star (f r) * g s) *
          ∑ ψ : AddChar G ℂ, ψ r * star (ψ s) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ψ _
      ring
    _ = _ := by
      simp only [character_orthogonality, mul_ite, mul_zero]
      simp [Finset.mul_sum, mul_comm, mul_left_comm]

theorem finiteFourier_parseval (f : G → ℂ) :
    (∑ ψ : AddChar G ℂ, ‖finiteFourier f ψ‖ ^ 2) =
      (Fintype.card G : ℝ) * ∑ r : G, ‖f r‖ ^ 2 := by
  have h := finiteFourier_inner f f
  simp only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_sum,
    ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul] at h
  exact_mod_cast h

theorem finiteFourier_translate (f : G → ℂ) (d : G) (ψ : AddChar G ℂ) :
    finiteFourier (fun r => f (r + d)) ψ = ψ d * finiteFourier f ψ := by
  classical
  unfold finiteFourier
  have h (r : G) : star (ψ r) * f (r + d) =
      ψ d * (star (ψ (r + d)) * f (r + d)) := by
    rw [AddChar.map_add_eq_mul, star_mul]
    have hψ : ψ d * star (ψ d) = 1 := by
      simp [Complex.star_def, Complex.mul_conj', ψ.norm_apply]
    calc
      _ = (ψ d * star (ψ d)) * (star (ψ r) * f (r + d)) := by rw [hψ, one_mul]
      _ = _ := by ring
  simp_rw [h]
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight d)
    (fun r => star (ψ (r + d)) * f (r + d))
    (fun r => star (ψ r) * f r) (fun _ => rfl)

theorem finiteFourier_convolution (H g : G → ℂ) (ψ : AddChar G ℂ) :
    finiteFourier (fun r => ∑ d : G, H d * g (r + d)) ψ =
      (∑ d : G, H d * ψ d) * finiteFourier g ψ := by
  classical
  change (∑ r : G, star (ψ r) * ∑ d : G, H d * g (r + d)) = _
  rw [Finset.sum_mul]
  conv_lhs =>
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  have h : (∑ r : G, star (ψ r) * (H d * g (r + d))) =
      H d * finiteFourier (fun r => g (r + d)) ψ := by
    simp only [finiteFourier, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [h, finiteFourier_translate]
  ring

theorem finiteFourier_convolution_form (H f g : G → ℂ) :
    (∑ ψ : AddChar G ℂ,
      star (finiteFourier f ψ) * (∑ d : G, H d * ψ d) * finiteFourier g ψ) =
      (Fintype.card G : ℂ) *
        ∑ r : G, ∑ d : G, star (f r) * H d * g (r + d) := by
  have h := finiteFourier_inner f (fun r => ∑ d : G, H d * g (r + d))
  simp only [finiteFourier_convolution, Finset.mul_sum] at h
  simpa only [Finset.mul_sum, Finset.sum_mul, mul_assoc] using h



end Erdos821.P3Clean
