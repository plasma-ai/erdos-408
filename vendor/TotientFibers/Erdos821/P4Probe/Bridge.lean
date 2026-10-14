import Erdos821.P4Probe.CancellationTasks

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

/-- Verbatim task definition; the lead bridges by definitional equality. -/
def SymmetricProbeTask : Prop :=
  Blueprint.ComparisonEstimate → Blueprint.Graph.IdealConstruction

def analyticGeometry (F : FixedData) : Blueprint.Analytic.Geometry where
  a := F.a
  b := F.b
  c := F.c
  d := F.d
  c₀ := F.c₀
  C₀ := F.C₀
  vmin := F.vMin
  vmax := max F.vMin F.vMax
  q := F.q
  ell := F.ell
  ordered := ⟨F.a_pos, F.ab, F.bc, F.cd, by convert F.d_lt using 1 <;> norm_num⟩
  positive := ⟨F.c₀_pos, F.C₀_pos, F.vMin_pos, le_max_left ..⟩
  damping := ⟨F.q_pos, F.q_lt⟩
  marks := F.ell_pos

@[simp] lemma analyticGroups_mass (P : PrimeGroups) (g : P.Group) :
    Blueprint.Analytic.mass (analyticGroups P) g = P.V g := by
  simp [Blueprint.Analytic.mass, PrimeGroups.V, analyticGroups, one_div]

@[simp] lemma analyticGroups_big (P : PrimeGroups) :
    (analyticGroups P).big = P.bigGroups := by
  change Finset.univ \ P.smallGroups = P.bigGroups
  ext g
  simp only [PrimeGroups.smallGroups, PrimeGroups.bigGroups,
    Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [Bool.not_eq_false]

@[simp] lemma bigGroup_card (P : PrimeGroups) :
    Fintype.card P.BigGroup = P.bigGroups.card := by
  exact (Fintype.card_subtype _).trans (by
    simp only [PrimeGroups.bigGroups])

lemma admissible_analytic (F : FixedData) (P : PrimeGroups) (x : ℝ)
    (hP : P.Admissible F x) (hint : intervalBigGroups P) :
    Blueprint.Analytic.Admissible (analyticGeometry F) x (analyticGroups P) := by
  unfold Blueprint.Analytic.Admissible
  dsimp only [analyticGroups, analyticGeometry, Blueprint.Analytic.PrimeGroups.big]
  have hbig : Finset.univ \ P.smallGroups = P.bigGroups := analyticGroups_big P
  rw [hbig]
  refine ⟨⟨hP.1, hP.2.1⟩, ⟨hP.2.2.1, hP.2.2.2.1⟩, ?_, ?_, ?_⟩
  · intro g
    change F.vMin ≤ (∑ p ∈ P.primes g, 1 / (p : ℝ)) ∧
      (∑ p ∈ P.primes g, 1 / (p : ℝ)) ≤ max F.vMin F.vMax
    simp only [one_div]
    exact ⟨(hP.2.2.2.2.1 g).1,
      (hP.2.2.2.2.1 g).2.trans (le_max_right F.vMin F.vMax)⟩
  · intro g p hp
    change (if g ∈ P.smallGroups then
      Real.exp (L x ^ F.a) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L x ^ F.b)
      else Real.exp (L x ^ F.c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L x ^ F.d))
    have h := hP.2.2.2.2.2 g p hp
    have hsmall : g ∈ P.smallGroups ↔ P.big g = false := by
      exact Finset.mem_filter.trans (by simp only [Finset.mem_univ, true_and])
    simp only [hsmall]
    cases hb : P.big g <;>
      simpa only [hb, Bool.false_eq_true, Bool.true_eq_false,
        ite_true, ite_false, Blueprint.Analytic.L, L] using h
  · intro g hg
    have hb : P.big g = true := (Finset.mem_filter.mp hg).2
    exact hint ⟨g, hb⟩

lemma localComparison_of_estimate (F : FixedData) (m : ℕ) (A C₄ : ℝ)
    (hA : 0 < A) (hC₄ : 0 ≤ C₄) (hc : Blueprint.ComparisonEstimate) :
    ∃ qexp hexp ξexp : ℝ, 0 < qexp ∧ 0 < hexp ∧ 0 < ξexp ∧
      ∀ᶠ x : ℝ in Filter.atTop,
        ∀ P : PrimeGroups, P.Admissible F x → intervalBigGroups P →
          ∀ ζ : ℝ, |ζ| ≤ L x ^ C₄ →
            LocalComparison P m ⌊L x ^ qexp⌋₊ (L x ^ (-hexp))
              (L x ^ (-ξexp)) ζ (L x ^ (-A)) := by
  obtain ⟨q, h, ξ, hq, hh, hξ, he⟩ := hc (analyticGeometry F) m A C₄ hA hC₄
  refine ⟨q, h, ξ, hq, hh, hξ, ?_⟩
  filter_upwards [he] with x hx
  intro P hP hint ζ hζ a b ha hb α f g
  exact hx (analyticGroups P) (admissible_analytic F P x hP hint) a b ha hb
    α ζ f g hζ

end
end Erdos821.P4Probe
