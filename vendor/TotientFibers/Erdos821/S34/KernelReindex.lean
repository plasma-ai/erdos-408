import Erdos821.S34.KernelTransport

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem sum_quad_reorder {α β γ δ M : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype δ] [AddCommMonoid M] (F : α → β → γ → δ → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d :=
      Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, F a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d :=
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem transpose_kernel_pairing {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (K : α → α → ℂ) (H : β → β → ℂ)
    (f : β → ℂ) (g : α → ℂ) (phase : α → β → ℂ) :
    (∑ X, ∑ Y, (w X : ℂ) * (v Y : ℂ) * star (f Y) * g X *
      (∑ D, ∑ E, (w D : ℂ) * (v E : ℂ) * K D X * H E Y * phase D E)) =
      ∑ D, ∑ E, (w D : ℂ) * (v E : ℂ) *
        (∑ X, (w X : ℂ) * K D X * g X) *
        (∑ Y, (v Y : ℂ) * H E Y * star (f Y)) * phase D E := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sum_quad_reorder]
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro E _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro X _
  apply Finset.sum_congr rfl
  intro Y _
  ring

end
end Erdos821.S34Core
