import Erdos821.P5.DyadicEndpointNorms

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

theorem gatedPatternTerm_rootMask {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (ν : Pattern G J F.ell m) (u : G.Aux J)
    (S T : Finset ℤ) (f g : ℤ → ℂ) (w : ℤ → ℕ → ℂ) (n : ℤ) (a b : A.Labels) :
    gatedPatternTerm A ν u T (rootMask S f) g w n a b =
      if n ∈ S then gatedPatternTerm A ν u T f g w n a b else 0 := by
  by_cases hn : n ∈ S <;> simp [rootMask, gatedPatternTerm, hn]

theorem gatedFamilySum_rootMask {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ : ℝ) (S R T : Finset ℤ)
    (f g : ℤ → ℂ) (w : ℤ → ℕ → ℂ)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v)) :
    gatedFamilySum B k ζ (S ∩ R) T f g w unused =
      gatedFamilySum B k ζ R T (rootMask S f) g w unused := by
  unfold gatedFamilySum
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  simp_rw [gatedPatternTerm_rootMask, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp [and_comm]

theorem gatedFamilySum_eq_zero_source {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ : ℝ) (S T : Finset ℤ)
    (f g : ℤ → ℂ) (w : ℤ → ℕ → ℂ)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v))
    (hf : ∀ n ∈ S, f n = 0) : gatedFamilySum B k ζ S T f g w unused = 0 := by
  unfold gatedFamilySum
  apply Finset.sum_eq_zero
  intro v hv
  apply Finset.sum_eq_zero
  intro u hu
  suffices (∑ n ∈ S, ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
      gatedPatternTerm (B.model k ζ) (B.pattern v) (assembleAux (B.pattern v) u (unused v))
        T f g w n a b) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro n hn
  simp [gatedPatternTerm, hf n hn]

end Erdos821.P5Core
