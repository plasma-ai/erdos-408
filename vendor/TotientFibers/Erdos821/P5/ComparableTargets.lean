import Erdos821.P5.EdgePropagation

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

def comparableRoots (X : ℝ) : Finset ℤ := Finset.Ico ⌈X / 2⌉ ⌈4 * X⌉

theorem mem_comparableRoots (X : ℝ) (n : ℤ) :
    n ∈ comparableRoots X ↔ X / 2 ≤ (n : ℝ) ∧ (n : ℝ) < 4 * X := by
  simp only [comparableRoots, Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]

theorem mem_graph_dyad (X : ℝ) (n : ℤ) :
    n ∈ dyad X ↔ X ≤ (n : ℝ) ∧ (n : ℝ) < 2 * X := by
  simp only [dyad, Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]

theorem comparableRoots_eq_three_dyads (X : ℝ) (hX : 0 ≤ X) :
    comparableRoots X = (dyad (X / 2) ∪ dyad X) ∪ dyad (2 * X) := by
  unfold comparableRoots dyad
  rw [show 2 * (X / 2) = X by ring, show 2 * (2 * X) = 4 * X by ring,
    Finset.Ico_union_Ico_eq_Ico (Int.ceil_mono (by linarith : X / 2 ≤ X))
      (Int.ceil_mono (by linarith : X ≤ 2 * X)),
    Finset.Ico_union_Ico_eq_Ico (Int.ceil_mono (by linarith : X / 2 ≤ 2 * X))
      (Int.ceil_mono (by linarith : 2 * X ≤ 4 * X))]

theorem physicalKernel_eq_zero_outside_comparable {F : FixedData}
    {G : Blueprint.Graph.PrimeGroups} {J m : ℕ} (A : Model F G J m)
    (X : ℝ) (hX : 0 < X)
    (hD : ∀ v a u, |(A.k : ℝ)| * ((A.pattern v).D a u : ℝ) ≤ X / 2)
    (absolute : Bool) (n n' : ℤ) (a b : A.Labels)
    (hn : n ∈ dyad X) (hn' : n' ∉ comparableRoots X) :
    A.physicalKernel absolute (n, a) (n', b) = 0 := by
  obtain ⟨hnlo, hnhi⟩ := (mem_graph_dyad X n).mp hn
  have hout : ¬(X / 2 ≤ (n' : ℝ) ∧ (n' : ℝ) < 4 * X) :=
    fun h => hn' ((mem_comparableRoots X n').mpr h)
  apply physicalKernel_eq_zero_of_far A (X / 2) hD absolute n n' a b
  rcases not_and_or.mp hout with hlow | hhigh
  · have hlow' : (n' : ℝ) < X / 2 := lt_of_not_ge hlow
    rw [abs_of_neg (by linarith : (n' : ℝ) - n < 0)]
    linarith
  · have hhigh' : 4 * X ≤ (n' : ℝ) := le_of_not_gt hhigh
    rw [abs_of_nonneg (by linarith : 0 ≤ (n' : ℝ) - n)]
    linarith

/-- Exact target restriction by finite propagation; it applies to every
Fourier integrand without retaining the original cutoff support. -/
theorem pairing_eq_restrict_comparable {F : FixedData}
    {G : Blueprint.Graph.PrimeGroups} {J m : ℕ} (A : Model F G J m)
    (X : ℝ) (hX : 0 < X)
    (hD : ∀ v a u, |(A.k : ℝ)| * ((A.pattern v).D a u : ℝ) ≤ X / 2)
    (T : Finset ℤ) (f g : ℤ → ℂ) :
    A.pairing X (T.product Finset.univ) f (fun z => g z.1) =
      A.pairing X ((T ∩ comparableRoots X).product Finset.univ) f (fun z => g z.1) := by
  unfold Model.pairing
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro a ha
  symm
  apply Finset.sum_subset
  · intro z hz
    obtain ⟨hzt, hzu⟩ := Finset.mem_product.mp hz
    exact Finset.mem_product.mpr ⟨(Finset.mem_inter.mp hzt).1, hzu⟩
  · intro z hz hznot
    obtain ⟨hzT, hzU⟩ := Finset.mem_product.mp hz
    have hzC : z.1 ∉ comparableRoots X := by
      intro h
      exact hznot (Finset.mem_product.mpr ⟨Finset.mem_inter.mpr ⟨hzT, h⟩, hzU⟩)
    have hk := physicalKernel_eq_zero_outside_comparable A X hX hD false n z.1 a z.2 hn hzC
    simpa only [Prod.eta, mul_zero, zero_mul] using congrArg
      (fun q : ℂ => (A.stateMass (n, a) : ℂ) * star (f n) * q * g z.1) hk

theorem dyadic_cutoff_eq_restricted_pairing_integral {F : FixedData}
    {G : Blueprint.Graph.PrimeGroups} {J m : ℕ} (B : Family F G J m)
    (k : ℤ) (ζ X Z : ℝ) (T : Finset ℤ) (f g : ℤ → ℂ)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v))
    (hV : ∀ g, G.V g ≠ 0) (hX : 0 < X) (hZ : 0 < Z)
    (hD : ∀ v a u, |(k : ℝ)| * ((B.pattern v).D a u : ℝ) ≤ X / 2)
    (Ψ : ℝ → ℂ) (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α)
    (hrep : ∀ y : ℝ, 0 < y → Ψ y = ∫ ξ, α ξ * mellin y (mellinFrequency ξ)) :
    Integrable (fun ξ => α ξ * (X : ℂ)⁻¹ *
      (B.model k (ζ - mellinFrequency ξ)).pairing X
        ((T ∩ comparableRoots X).product Finset.univ)
        (mellinPairingSource X Z f (mellinFrequency ξ)) (fun z => g z.1)) ∧
    gatedFamilySum B k ζ (dyad X) T f g (harmonicCutoff Ψ Z) unused =
      ∫ ξ, α ξ * (X : ℂ)⁻¹ *
        (B.model k (ζ - mellinFrequency ξ)).pairing X
          ((T ∩ comparableRoots X).product Finset.univ)
          (mellinPairingSource X Z f (mellinFrequency ξ)) (fun z => g z.1) := by
  have h := dyadic_cutoff_eq_pairing_integral B k ζ X Z T f g unused hV hX hZ Ψ α hα hrep
  simp_rw [pairing_eq_restrict_comparable (B.model k _) X hX hD T _ g] at h
  exact h

end Erdos821.P5Core
