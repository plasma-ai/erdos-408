module

public import Erdos408.Graph.Encoding

/-!
# Subtype labels against `ℕ`-valued lists

Upstream labels are functions `g ↦ Fin M → {p // p ∈ P g}`, and its auxiliary
labels fill every one of the first `J` slots. `GraphTransference` uses
`ℕ`-valued lists, and auxiliary labels only in the free slots `C g`, with `1`
elsewhere. Summing over upstream labels is summing over their values
(`sum_vals`). Summing over upstream auxiliary labels against their mass
`∏ μ_g` integrates out the slots outside `C g`, since `∑_p μ_g(p) = 1`
(`sum_trim`).
-/

@[expose] public section

namespace Erdos408.Graph

open Erdos821.Blueprint.Graph

variable {G : PrimeGroups}

/-- The values of upstream labels, as `ℕ`-valued lists. -/
def vals {M : ℕ} (a : G.Labels M) : Fin G.count → Fin M → ℕ :=
  fun g i => (a g i).val

/-- Upstream auxiliary labels trimmed to the slots `C g`: their values there,
and `1` elsewhere. -/
def trim {J : ℕ} (C : Fin G.count → Finset (Fin J)) (u : G.Aux J) :
    Fin G.count → Fin J → ℕ :=
  fun g i => if i ∈ C g then (u g i).val else 1

/-- Upstream's group mass is the harmonic mass. -/
lemma V_eq_harmonicMass (g : G.Group) : G.V g = harmonicMass (G.primes g) := by
  simp [PrimeGroups.V, harmonicMass]

/-- Summing over upstream labels is summing over their values. -/
lemma sum_vals {M : ℕ} {R : Type*} [AddCommMonoid R] (Φ : (Fin G.count → Fin M → ℕ) → R) :
    ∑ a : G.Labels M, Φ (vals a) =
      ∑ p ∈ Fintype.piFinset (fun g => Fintype.piFinset fun _ : Fin M => G.primes g), Φ p := by
  refine Finset.sum_bij' (fun a _ => vals a)
    (fun p hp g i => ⟨p g i, Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hp g) i⟩)
    (fun a _ => ?_) (fun _ _ => Finset.mem_univ _) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)
  simp only [Fintype.mem_piFinset]
  exact fun g i => (a g i).property

/-- The mass of the upstream auxiliary labels trimming to `w ∈ auxLabels`:
the slots outside `C g` integrate to one. -/
lemma sum_mass_trim_eq {J : ℕ} (C : Fin G.count → Finset (Fin J))
    (hV : ∀ g, G.V g ≠ 0) {w : Fin G.count → Fin J → ℕ} (hw : w ∈ auxLabels G.primes C) :
    ∑ u : G.Aux J, (if trim C u = w then ∏ g, ∏ i, G.mu g (u g i) else 0) =
      ∏ g, ∏ i ∈ C g, (harmonicMass (G.primes g) * w g i)⁻¹ := by
  have hw' : ∀ g i, w g i ∈ if i ∈ C g then G.primes g else {1} := fun g i =>
    Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hw g) i
  -- the indicator of `trim C u = w` is a product over the slots
  have hsplit : ∀ u : G.Aux J, (if trim C u = w then ∏ g, ∏ i, G.mu g (u g i) else 0) =
      ∏ g, ∏ i, (if (if i ∈ C g then (u g i).val else 1) = w g i then G.mu g (u g i)
        else 0) := by
    intro u
    by_cases h : trim C u = w
    · rw [ite_eq_left h]
      refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i _ => ?_
      exact (ite_eq_left (congrFun (congrFun h g) i)).symm
    · rw [ite_eq_right h]
      obtain ⟨g, i, hgi⟩ : ∃ g i, trim C u g i ≠ w g i := by
        simpa only [funext_iff, not_forall] using h
      exact (Finset.prod_eq_zero (Finset.mem_univ g)
        (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hgi))).symm
  simp_rw [hsplit]
  rw [← Fintype.prod_sum (fun g (y : Fin J → G.Prime g) => ∏ i,
    (if (if i ∈ C g then (y i).val else 1) = w g i then G.mu g (y i) else 0))]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [← Fintype.prod_sum (fun i (y : G.Prime g) =>
    (if (if i ∈ C g then y.val else 1) = w g i then G.mu g y else 0))]
  have hC := Finset.prod_ite_mem Finset.univ (C g)
    fun i => (harmonicMass (G.primes g) * w g i)⁻¹
  rw [Finset.univ_inter] at hC
  rw [← hC]
  · refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i ∈ C g
    · have hwi : w g i ∈ G.primes g := by simpa [hi] using hw' g i
      rw [ite_eq_left hi]
      simp only [ite_eq_left hi]
      rw [Fintype.sum_eq_single ⟨w g i, hwi⟩ fun x hx => ite_eq_right fun h => hx (Subtype.ext h)]
      simp [PrimeGroups.mu, V_eq_harmonicMass]
    · have hwi : w g i = 1 := by simpa [hi] using hw' g i
      rw [ite_eq_right hi]
      simp only [ite_eq_right hi, hwi, ite_true]
      have hsum : ∑ j : G.Prime g, G.mu g j = ∑ p ∈ G.primes g, (G.V g * p)⁻¹ :=
        Finset.sum_coe_sort (G.primes g) fun p : ℕ => (G.V g * p)⁻¹
      rw [hsum]
      simp_rw [mul_inv]
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ (hV g)

/-- Summing over upstream auxiliary labels against their mass `∏ μ_g`, for a
function of the labels in the slots `C g`, is summing over `auxLabels` against
`∏_{i ∈ C g} μ_g`. -/
lemma sum_trim {J : ℕ} (C : Fin G.count → Finset (Fin J)) (hV : ∀ g, G.V g ≠ 0)
    (Φ : (Fin G.count → Fin J → ℕ) → ℂ) :
    ∑ u : G.Aux J, Φ (trim C u) * ((∏ g, ∏ i, G.mu g (u g i) : ℝ) : ℂ) =
      ∑ w ∈ auxLabels G.primes C,
        Φ w * ((∏ g, ∏ i ∈ C g, (harmonicMass (G.primes g) * w g i)⁻¹ : ℝ) : ℂ) := by
  have hmem : ∀ u : G.Aux J, trim C u ∈ auxLabels G.primes C := by
    intro u
    simp only [auxLabels, Fintype.mem_piFinset]
    intro g i
    by_cases hi : i ∈ C g <;> simp [trim, hi]
  calc ∑ u : G.Aux J, Φ (trim C u) * ((∏ g, ∏ i, G.mu g (u g i) : ℝ) : ℂ)
      = ∑ u : G.Aux J, ∑ w ∈ auxLabels G.primes C,
          Φ w * (((if trim C u = w then ∏ g, ∏ i, G.mu g (u g i) else 0) : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp_rw [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_zero, mul_ite, mul_zero]
        rw [Finset.sum_ite_eq, ite_eq_left (hmem u)]
    _ = ∑ w ∈ auxLabels G.primes C,
          Φ w * ((∏ g, ∏ i ∈ C g, (harmonicMass (G.primes g) * w g i)⁻¹ : ℝ) : ℂ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [← Finset.mul_sum, ← Complex.ofReal_sum, sum_mass_trim_eq C hV hw]

end Erdos408.Graph
