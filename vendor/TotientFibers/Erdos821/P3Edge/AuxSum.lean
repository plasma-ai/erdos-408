import Erdos821.P3Edge.FreshBound

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

lemma mu_pos_of_V_pos (g : P.Group) (hV : 0 < P.V g) (p : P.Prime g) :
    0 < P.mu g p := by
  unfold PrimeGroups.mu
  have hp : 0 < (p.val : ℝ) := by
    have h := (P.prime g p.val p.property).pos
    exact_mod_cast h
  exact inv_pos.mpr (mul_pos hV hp)

lemma mu_sum_eq_one (g : P.Group) (hV : P.V g ≠ 0) :
    ∑ p : P.Prime g, P.mu g p = 1 := by
  have h1 : ∑ p : P.Prime g, P.mu g p
      = ∑ p ∈ P.primes g, (P.V g * (p : ℝ))⁻¹ := by
    apply Finset.sum_bij (fun p _ => p.val)
    · intro p _
      exact p.property
    · intro p _ q _ h
      exact Subtype.ext h
    · intro n hn
      exact ⟨⟨n, hn⟩, Finset.mem_univ _, rfl⟩
    · intro p _
      rfl
  rw [h1]
  simp_rw [mul_inv, ← Finset.mul_sum]
  have hV' : (∑ p ∈ P.primes g, (p : ℝ)⁻¹) ≠ 0 := by
    have : P.V g = ∑ p ∈ P.primes g, (p : ℝ)⁻¹ := rfl
    rwa [this] at hV
  exact inv_mul_cancel₀ hV'

/-- Free-label integrations collapse to one, uniformly in J. -/
lemma auxMass_sum_eq_one (ν : Pattern P J F.ell m) (hV : ∀ g, P.V g ≠ 0) :
    ∑ u : P.Aux J, ν.auxMass u = 1 := by
  classical
  simp only [Pattern.auxMass]
  -- Do it in two stages: groups outer, slots inner via fresh_sum_eq.
  have hstep : ∀ g : P.Group, ∑ w : Fin J → P.Prime g, ∏ i, P.mu g (w i)
      = (∑ p : P.Prime g, P.mu g p) ^ J := fun g =>
    fresh_sum_eq (fun p : P.Prime g => P.mu g p) J
  have h2 : (∑ u : P.Aux J, ∏ g : P.Group, ∏ i : Fin J, P.mu g (u g i))
      = ∏ g : P.Group, ∑ w : Fin J → P.Prime g, ∏ i : Fin J, P.mu g (w i) := by
    have h3 := Finset.prod_univ_sum (fun g : P.Group => (Finset.univ : Finset (Fin J → P.Prime g)))
      (fun (g : P.Group) => fun w : Fin J → P.Prime g => ∏ i : Fin J, P.mu g (w i))
    have lhs : (∏ _g : P.Group, ∑ _w : Fin J → P.Prime _, ∏ _i : Fin J, P.mu _ _) =
        ∏ g : P.Group, ∑ w : Fin J → P.Prime g, ∏ i : Fin J, P.mu g (w i) := rfl
    have rhs : (∑ x ∈ Fintype.piFinset (fun _ : P.Group => (Finset.univ : Finset (Fin J → P.Prime _))),
        ∏ g : P.Group, ∏ i : Fin J, P.mu g (x g i))
        = ∑ u : P.Aux J, ∏ g : P.Group, ∏ i : Fin J, P.mu g (u g i) := by
      rw [Fintype.piFinset_univ]
    have h3' : (∏ _g : P.Group, ∑ _w : Fin J → P.Prime _, ∏ _i : Fin J, P.mu _ _) =
        (∑ x ∈ Fintype.piFinset (fun _ : P.Group => (Finset.univ : Finset (Fin J → P.Prime _))),
          ∏ g : P.Group, ∏ i : Fin J, P.mu g (x g i)) := h3
    rw [lhs, rhs] at h3'
    exact h3'.symm
  rw [h2]
  simp_rw [hstep, mu_sum_eq_one _ (hV _), one_pow, Finset.prod_const_one]

end Erdos821.P3Edge
