import Mathlib

/-! Constraining one fresh coordinate: an injective relabelling of that coordinate into all
values multiplies the constrained mass by the total value mass. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos821.P3High

theorem relabel_sum_le {X Q : Type*} [DecidableEq X] (f : X → ℝ) (T S : Finset X)
    (Q' : Finset Q) (Φ : X → Q → X) (μ : Q → ℝ) (μ0 c : ℝ)
    (hfS : ∀ x ∈ S, 0 ≤ f x) (hfT : ∀ x ∈ T, 0 ≤ f x) (hμ0 : 0 ≤ μ0) (hc : 0 < c)
    (hmass : c ≤ ∑ p ∈ Q', μ p)
    (hmaps : ∀ x ∈ T, ∀ p ∈ Q', Φ x p ∈ S)
    (hinj : ∀ x1 ∈ T, ∀ p1 ∈ Q', ∀ x2 ∈ T, ∀ p2 ∈ Q',
      Φ x1 p1 = Φ x2 p2 → x1 = x2 ∧ p1 = p2)
    (hscale : ∀ x ∈ T, ∀ p ∈ Q', f x * μ p = f (Φ x p) * μ0) :
    ∑ x ∈ T, f x ≤ μ0 / c * ∑ x ∈ S, f x := by
  have hT0 : 0 ≤ ∑ x ∈ T, f x := Finset.sum_nonneg hfT
  have hinjOn : Set.InjOn (fun z : X × Q => Φ z.1 z.2) ↑(T ×ˢ Q') := by
    intro z1 hz1 z2 hz2 h
    rw [Finset.coe_product, Set.mem_prod] at hz1 hz2
    have := hinj z1.1 hz1.1 z1.2 hz1.2 z2.1 hz2.1 z2.2 hz2.2 h
    exact Prod.ext this.1 this.2
  have hsub : (T ×ˢ Q').image (fun z : X × Q => Φ z.1 z.2) ⊆ S := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    rw [Finset.mem_product] at hz
    exact hmaps z.1 hz.1 z.2 hz.2
  have key : (∑ x ∈ T, f x) * c ≤ μ0 * ∑ x ∈ S, f x := by
    calc (∑ x ∈ T, f x) * c ≤ (∑ x ∈ T, f x) * ∑ p ∈ Q', μ p :=
          mul_le_mul_of_nonneg_left hmass hT0
      _ = ∑ z ∈ T ×ˢ Q', f z.1 * μ z.2 := by
          rw [Finset.sum_mul_sum, Finset.sum_product]
      _ = ∑ z ∈ T ×ˢ Q', f (Φ z.1 z.2) * μ0 := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [Finset.mem_product] at hz
          exact hscale z.1 hz.1 z.2 hz.2
      _ = μ0 * ∑ y ∈ (T ×ˢ Q').image (fun z : X × Q => Φ z.1 z.2), f y := by
          rw [Finset.sum_image hinjOn, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ μ0 * ∑ x ∈ S, f x := by
          apply mul_le_mul_of_nonneg_left _ hμ0
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun x hx _ => hfS x hx
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith

end Erdos821.P3High
