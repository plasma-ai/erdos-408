module

public import Erdos821.P5.EndpointSupport

@[expose] public section

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T

def edgeList {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (a : G.Labels (J + ell)) (u : G.Aux J) : G.Labels J :=
  fun g i => if i ∈ ν.changed g then u g i else a g (ν.slot i)

theorem pattern_D_eq_listProduct {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (a : G.Labels (J + ell)) (u : G.Aux J) :
    ν.D a u = listProduct G (edgeList ν a u) := by
  unfold Pattern.D listProduct edgeList
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> rfl

/-- Polylogarithmic shifts times a fixed-depth edge product are subpower,
uniformly in the family, frequency, probe count and selected slots. -/
theorem eventual_edge_displacement_le (P : Geometry) (J : ℕ) (C γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ L x ∧
      ∀ (G : Blueprint.Analytic.PrimeGroups), Admissible P x G →
        ∀ (ell m : ℕ) (ν : Pattern G.graph J ell m) (a : G.graph.Labels (J + ell))
          (u : G.graph.Aux J) (k : ℤ), |(k : ℝ)| ≤ L x ^ C →
          |(k : ℝ)| * (ν.D a u : ℝ) ≤ x ^ γ := by
  filter_upwards [eventual_listProduct_le P J (γ / 2) (by linarith),
    eventual_constant_log_power_le_power (γ / 2) C 1 (by linarith)] with x hlist hlog
  refine ⟨hlog.1, hlist.1, ?_⟩
  intro G hG ell m ν a u k hk
  have hD : (ν.D a u : ℝ) ≤ x ^ (γ / 2) := by
    rw [pattern_D_eq_listProduct]
    exact hlist.2 G hG (edgeList ν a u)
  have hpow : x ^ (γ / 2) * x ^ (γ / 2) = x ^ γ := by
    rw [← Real.rpow_add (by linarith : 0 < x)]
    congr 1
    ring
  calc
    _ ≤ L x ^ C * x ^ (γ / 2) :=
      mul_le_mul hk hD (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ x ^ (γ / 2) * x ^ (γ / 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hlog.1) _)
      simpa only [one_mul] using hlog.2.2
    _ = _ := hpow

theorem physicalRaw_eq_zero_of_far {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (Δ : ℝ)
    (hD : ∀ v a u, |(A.k : ℝ)| * ((A.pattern v).D a u : ℝ) ≤ Δ)
    (absolute : Bool) (n n' : ℤ) (a b : A.Labels) (hfar : Δ < |(n' : ℝ) - n|) :
    A.physicalRaw absolute (n, a) (n', b) = 0 := by
  have hshift (v : Fin A.patternCount) (u : G.Aux J) :
      n' ≠ n + A.k * ((A.pattern v).D a u : ℤ) := by
    intro hs
    have hsR : (n' : ℝ) - n = (A.k : ℝ) * ((A.pattern v).D a u : ℝ) := by
      rw [hs]
      push_cast
      ring
    have h := hD v a u
    have habsD : |((A.pattern v).D a u : ℝ)| = ((A.pattern v).D a u : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [hsR, abs_mul, habsD] at hfar
    exact (not_lt_of_ge h) hfar
  unfold Model.physicalRaw
  by_cases hp : G.physical (J + F.ell) n a ∧ G.physical (J + F.ell) n' b
  · simp only [hp, and_self, ite_true]
    apply Finset.sum_eq_zero
    intro v hv
    apply Finset.sum_eq_zero
    intro u hu
    simp only [hshift v u, and_false, ite_false]
  · simp only [hp, ite_false]

theorem physicalKernel_eq_zero_of_far {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (Δ : ℝ)
    (hD : ∀ v a u, |(A.k : ℝ)| * ((A.pattern v).D a u : ℝ) ≤ Δ)
    (absolute : Bool) (n n' : ℤ) (a b : A.Labels) (hfar : Δ < |(n' : ℝ) - n|) :
    A.physicalKernel absolute (n, a) (n', b) = 0 := by
  unfold Model.physicalKernel
  simp_rw [physicalRaw_eq_zero_of_far A Δ hD absolute n n' _ _ hfar]
  simp

end Erdos821.P5Core
