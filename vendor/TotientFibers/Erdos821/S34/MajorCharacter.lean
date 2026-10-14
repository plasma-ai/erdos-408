import Erdos821.S34.RationalCharacterTasks
import Erdos821.S34.CharacterReproduction
import Erdos821.S34.MajorPointwise

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem sum_triple_reorder {α β γ M : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [AddCommMonoid M] (F : α → β → γ → M) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ a, ∑ b, F a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, F a b c := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem finite_character_kernel_integral {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (w : α → ℝ) (v : β → ℝ) (K : α → ℂ) (H : β → ℂ)
    (coeff : γ → ℂ) (χ : γ → α → ℂ) (ψ : γ → β → ℂ) :
    (∑ D, ∑ E, (w D : ℂ) * (v E : ℂ) * K D * H E *
      (∑ c, coeff c * χ c D * ψ c E)) =
      ∑ c, coeff c * (∑ D, (w D : ℂ) * K D * χ c D) *
        (∑ E, (v E : ℂ) * H E * ψ c E) := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sum_triple_reorder]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro D _
  ring

theorem rational_kernel_reproduction (hfourier : RationalFourierTask)
    (hind : PrimitiveInductionTask) (G : PrimeGroups) (a b : Fin G.size → ℕ)
    (Q r : ℕ) (u : ℤ) (h ξ ε : ℝ) (hr : 1 ≤ r) (hrQ : r ≤ Q)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (X : Tuple G a) (Y : Tuple G b)
    (hcopA : ∀ D : Tuple G a, Nat.Coprime (product G a D) r)
    (hcopB : ∀ E : Tuple G b, Nat.Coprime (product G b E) r)
    (hrepA : ∀ χ ∈ primitiveCharacters Q,
      ‖cellApply G a Q h ξ (fun D => charValue χ (product G a D)) X - charValue χ (product G a X)‖ ≤ ε)
    (hrepB : ∀ χ ∈ primitiveCharacters Q,
      ‖cellApply G b Q h ξ (fun E => charValue χ (product G b E)) Y - charValue χ (product G b Y)‖ ≤ ε) :
    ‖expect G a (fun D => expect G b (fun E =>
      cellKernel G a Q h ξ (product G a D) (product G a X) *
      cellKernel G b Q h ξ (product G b E) (product G b Y) *
        e ((u : ℝ) * (product G a D * product G b E) / r))) -
      e ((u : ℝ) * (product G a X * product G b Y) / r)‖ ≤
        3 * ε * Real.sqrt (r.totient : ℝ) := by
  obtain ⟨coeff, hcoeff, hexp⟩ := hfourier r u hr
  let A := fun ψ : DirichletCharacter ℂ r =>
    expect G a (fun D => cellKernel G a Q h ξ (product G a D) (product G a X) * ψ (product G a D : ZMod r))
  let B := fun ψ : DirichletCharacter ℂ r =>
    expect G b (fun E => cellKernel G b Q h ξ (product G b E) (product G b Y) * ψ (product G b E : ZMod r))
  let vA := fun ψ : DirichletCharacter ℂ r => ψ (product G a X : ZMod r)
  let vB := fun ψ : DirichletCharacter ℂ r => ψ (product G b Y : ZMod r)
  have ha (ψ : DirichletCharacter ℂ r) : ‖A ψ - vA ψ‖ ≤ ε := by
    obtain ⟨χ, hχ, hψ⟩ := hind Q r hr hrQ ψ
    have he (D : Tuple G a) : charValue χ (product G a D) = ψ (product G a D : ZMod r) := hψ _ (hcopA D)
    have ht := hrepA χ hχ
    simpa only [cellApply, A, vA, he] using ht
  have hb (ψ : DirichletCharacter ℂ r) : ‖B ψ - vB ψ‖ ≤ ε := by
    obtain ⟨χ, hχ, hψ⟩ := hind Q r hr hrQ ψ
    have he (E : Tuple G b) : charValue χ (product G b E) = ψ (product G b E : ZMod r) := hψ _ (hcopB E)
    have ht := hrepB χ hχ
    simpa only [cellApply, B, vB, he] using ht
  have hphase (D : Tuple G a) (E : Tuple G b) :
      e ((u : ℝ) * (product G a D * product G b E) / r) =
        ∑ ψ, coeff ψ * ψ (product G a D : ZMod r) * ψ (product G b E : ZMod r) := by
    have ht := hexp (product G a D * product G b E) ((hcopA D).mul_left (hcopB E))
    simpa only [Nat.cast_mul, map_mul, mul_assoc] using ht
  have hraw : e ((u : ℝ) * (product G a X * product G b Y) / r) = ∑ ψ, coeff ψ * vA ψ * vB ψ := hphase X Y
  have hintegral : expect G a (fun D => expect G b (fun E =>
      cellKernel G a Q h ξ (product G a D) (product G a X) *
      cellKernel G b Q h ξ (product G b E) (product G b Y) *
      e ((u : ℝ) * (product G a D * product G b E) / r))) = ∑ ψ, coeff ψ * A ψ * B ψ := by
    simp only [hphase, expect, Finset.mul_sum]
    have ht := finite_character_kernel_integral (tupleWeight G a) (tupleWeight G b)
      (fun D => cellKernel G a Q h ξ (product G a D) (product G a X))
      (fun E => cellKernel G b Q h ξ (product G b E) (product G b Y))
      coeff (fun ψ D => ψ (product G a D : ZMod r)) (fun ψ E => ψ (product G b E : ZMod r))
    simpa only [A, B, expect, Finset.mul_sum, mul_assoc] using ht
  rw [hintegral, hraw]
  exact (finite_character_reproduction_error coeff vA vB A B ε hε hε1
    (fun ψ => ψ.norm_le_one _) (fun ψ => ψ.norm_le_one _) ha hb).trans
      (mul_le_mul_of_nonneg_left hcoeff (by positivity))

end
end Erdos821.S34Core
