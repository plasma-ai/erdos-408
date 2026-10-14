import Erdos821.P5.ComparisonMellinAlgebra

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

def separatedComparisonTerm (G : PrimeGroups) (x Y UA UB a₁ a₂ v : ℝ)
    (E H : Endpoint) (mark₁ mark₂ : ℕ → ℂ) (w w' DA DB : ℕ) : ℂ :=
  (Y : ℂ)⁻¹ * comparisonMellinTest UA a₁ a₂ v DA *
    comparisonMellinTest UB a₁ a₂ v DB *
    star (comparisonMellinSource G x Y a₁ v E mark₁ w) *
    comparisonMellinTarget G x a₂ H mark₂ w'

theorem separatedComparisonTerm_integrable (G : PrimeGroups)
    (x Y UA UB a₁ a₂ : ℝ) (E H : Endpoint) (mark₁ mark₂ : ℕ → ℂ)
    (w w' DA DB : ℕ) (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α) :
    Integrable (fun ξ => α ξ * separatedComparisonTerm G x Y UA UB a₁ a₂
      (mellinFrequency ξ) E H mark₁ mark₂ w w' DA DB) := by
  let F := fun ξ : Fin 1 → ℝ => separatedComparisonTerm G x Y UA UB a₁ a₂
    (mellinFrequency ξ) E H mark₁ mark₂ w w' DA DB
  have hc : Continuous F := by
    unfold F separatedComparisonTerm comparisonMellinTest comparisonMellinSource
      comparisonMellinTarget mellinFrequency Blueprint.Analytic.mellin
    fun_prop
  have hn (ξ : Fin 1 → ℝ) : ‖F ξ‖ = ‖F 0‖ := by
    simp only [F, separatedComparisonTerm, norm_mul, comparisonMellinTest_norm,
      mul_one, norm_star, comparisonMellinSource_norm, comparisonMellinTarget_norm]
  exact hα.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => (hn ξ).le))

/-- Exact cutoff inversion with independent endpoint sequences. -/
theorem stripped_scalar_eq_separated_integral (G : PrimeGroups)
    (x Z UA UB a₁ a₂ : ℝ) (E H : Endpoint) (mark₁ mark₂ : ℕ → ℂ)
    (w w' DA DB : ℕ) (hZ : 0 < Z) (hUA : 0 < UA) (hUB : 0 < UB)
    (hw : 0 < w) (hw' : 0 < w') (hDA : 0 < DA) (hDB : 0 < DB)
    (Ψ : ℝ → ℂ) (α : (Fin 1 → ℝ) → ℂ)
    (hrep : ∀ y : ℝ, 0 < y → Ψ y = ∫ ξ, α ξ * mellin y (mellinFrequency ξ)) :
    strippedLiftScalar G x Z a₁ a₂ E H Ψ w w' (DA * DB) * (mark₁ w * mark₂ w') =
      ∫ ξ, α ξ * separatedComparisonTerm G x (Z * (UA * UB)) UA UB a₁ a₂
        (mellinFrequency ξ) E H mark₁ mark₂ w w' DA DB := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hDR : (0 : ℝ) < (DA * DB : ℕ) := by exact_mod_cast Nat.mul_pos hDA hDB
  let C : ℂ := (w : ℂ)⁻¹ * mellin ((w : ℝ) / (DA * DB : ℕ)) a₁ *
    mellin ((w' : ℝ) / (DA * DB : ℕ)) a₂ * star (endpoint G x E w) *
    endpoint G x H w' * (mark₁ w * mark₂ w')
  have he : strippedLiftScalar G x Z a₁ a₂ E H Ψ w w' (DA * DB) *
      (mark₁ w * mark₂ w') = Ψ ((w : ℝ) / (Z * (DA * DB : ℕ))) * C := by
    unfold strippedLiftScalar harmonicCutoff C
    simp only [Int.cast_natCast]
    ring
  rw [he, hrep _ (div_pos hwR (mul_pos hZ hDR)), ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with ξ
  have hf := comparison_mellin_scalar_factor G x Z UA UB a₁ a₂ (mellinFrequency ξ)
    E H mark₁ mark₂ w w' DA DB hZ hUA hUB hw hw' hDA hDB
  change (α ξ * mellin _ _) * C = α ξ * _
  dsimp only [separatedComparisonTerm]
  dsimp only [C]
  push_cast at hf ⊢
  linear_combination α ξ * hf

def separatedComparisonCellCorrelation {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
    (h : ℝ) (j : ℤ × ℤ) (χA χB : CharacterIndex Q)
    (x Y a₁ a₂ v : ℝ) (E H : Endpoint) (k : ℤ)
    (s : FreeDraw ν → Finset ℕ) : ℂ :=
  ∑ u : FreeDraw ν with comparisonCellPair ν block h u = j,
    (freeDrawLaw ν u : ℂ) *
      star (charValue χA (comparisonFreeProduct ν block false u)) *
      star (charValue χB (comparisonFreeProduct ν block true u)) *
      ∑ n ∈ s u, separatedComparisonTerm G x Y
        (comparisonCellScale h j.1) (comparisonCellScale h j.2) a₁ a₂ v E H
        (comparisonMarkedEndpoint ν block true h j.2 χB)
        (comparisonMarkedEndpoint ν block false h j.1 χA) n
        ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat
        (comparisonFreeProduct ν block false u) (comparisonFreeProduct ν block true u)

/-- Inversion commutes with the actual finite free laws and root sums.
Support is retained explicitly here; removing its dependence on the free
products requires the subsequent smooth size-cutoff step. -/
theorem comparisonCellCorrelation_eq_separated_integral
    {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
    (h : ℝ) (j : ℤ × ℤ) (χA χB : CharacterIndex Q)
    (x Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ)
    (s : FreeDraw ν → Finset ℕ) (z : SharedDraw ν) (hZ : 0 < Z)
    (hs : ∀ u, comparisonCellPair ν block h u = j →
      ∀ n, n ∈ s u → 0 < n ∧ 0 < (n : ℤ) + k * (freeDrawProduct ν u : ℤ))
    (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α)
    (hrep : ∀ y : ℝ, 0 < y → Ψ y = ∫ ξ, α ξ * mellin y (mellinFrequency ξ)) :
    comparisonCellCorrelation ν block h j χA χB x Z a₁ a₂ E H Ψ k s =
      ∫ ξ, α ξ * separatedComparisonCellCorrelation ν block h j χA χB
        x (Z * comparisonJointScale h j) a₁ a₂ (mellinFrequency ξ) E H k s := by
  let Y := Z * comparisonJointScale h j
  let f := fun (u : FreeDraw ν) (n : ℕ) (ξ : Fin 1 → ℝ) =>
    separatedComparisonTerm G x Y (comparisonCellScale h j.1) (comparisonCellScale h j.2)
      a₁ a₂ (mellinFrequency ξ) E H
      (comparisonMarkedEndpoint ν block true h j.2 χB)
      (comparisonMarkedEndpoint ν block false h j.1 χA) n
      ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat
      (comparisonFreeProduct ν block false u) (comparisonFreeProduct ν block true u)
  have hi (u : FreeDraw ν) (n : ℕ) : Integrable (fun ξ => α ξ * f u n ξ) :=
    separatedComparisonTerm_integrable G x Y _ _ a₁ a₂ E H _ _ n _ _ _ α hα
  have hterm (u : FreeDraw ν) (hu : comparisonCellPair ν block h u = j) (n : ℕ) (hns : n ∈ s u) :
      strippedLiftScalar G x Z a₁ a₂ E H Ψ n
        ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat (freeDrawProduct ν u) *
        (comparisonMarkedEndpoint ν block true h j.2 χB n *
          comparisonMarkedEndpoint ν block false h j.1 χA
            ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat) =
      ∫ ξ, α ξ * f u n ξ := by
    dsimp only [f, Y, comparisonJointScale]
    rw [freeDrawProduct_eq_comparisonProducts ν block u z]
    apply stripped_scalar_eq_separated_integral G x Z _ _ a₁ a₂ E H _ _ n _ _ _ hZ
      (comparisonCellScale_pos _ _) (comparisonCellScale_pos _ _) (hs u hu n hns).1
      (by have hp := (hs u hu n hns).2; rw [freeDrawProduct_eq_comparisonProducts ν block u z] at hp; omega)
      (comparisonFreeProduct_pos _ _ _ _) (comparisonFreeProduct_pos _ _ _ _) Ψ α hrep
  let c := fun u : FreeDraw ν => (freeDrawLaw ν u : ℂ) *
    star (charValue χA (comparisonFreeProduct ν block false u)) *
    star (charValue χB (comparisonFreeProduct ν block true u))
  have hrow (u : FreeDraw ν) (hu : comparisonCellPair ν block h u = j) :
      (∑ n ∈ s u, strippedLiftScalar G x Z a₁ a₂ E H Ψ n
        ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat (freeDrawProduct ν u) *
        (comparisonMarkedEndpoint ν block true h j.2 χB n *
          comparisonMarkedEndpoint ν block false h j.1 χA
            ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat)) =
      ∫ ξ, ∑ n ∈ s u, α ξ * f u n ξ := by
    rw [integral_finsetSum _ (fun n hn => hi u n)]
    apply Finset.sum_congr rfl
    intro n hn
    exact hterm u hu n hn
  have heq : comparisonCellCorrelation ν block h j χA χB x Z a₁ a₂ E H Ψ k s =
      ∑ u : FreeDraw ν with comparisonCellPair ν block h u = j,
        c u * ∫ ξ, ∑ n ∈ s u, α ξ * f u n ξ := by
    unfold comparisonCellCorrelation
    apply Finset.sum_congr rfl
    intro u hu
    rw [hrow u (Finset.mem_filter.mp hu).2]
  rw [heq]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun u hu =>
    (integrable_finsetSum (s u) (fun n hn => hi u n)).const_mul (c u))]
  apply integral_congr_ae
  filter_upwards with ξ
  unfold separatedComparisonCellCorrelation
  simp only [f, Y, c]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro n hn
  ring

end Erdos821.P5Core
