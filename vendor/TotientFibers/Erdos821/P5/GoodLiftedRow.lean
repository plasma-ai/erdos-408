import Erdos821.P5.LiftedRootIdentity
import Erdos821.P5.MarkCountIdentity

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

def strippedMarkedRow {P : Geometry} {G : Blueprint.Analytic.PrimeGroups} {J m : ℕ}
    (ν : Pattern G.graph J P.ell m) (n n' : ℕ)
    (c : UnsharedDraw ν → UnsharedDraw ν → ℂ) : ℂ :=
  ((strippedDamping P ν n * strippedDamping P ν n' * ν.physicalTargetMass ^ 2 : ℝ) : ℂ) *
    ∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
      if UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s then c r s else 0

/-- On good shared draws the full physical lift is the stripped marked row,
for arbitrary coefficients on the two independent unshared lists. -/
theorem physicalSharedRow_good_eq_stripped {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m : ℕ} (A : Model P.graph G.graph J m) (ν : Pattern G.graph J P.ell m)
    (z : SharedDraw ν) (n n' D : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0) (hD : D ≠ 0)
    (hz : GoodSharedDraw ν n n' D z) (c : UnsharedDraw ν → UnsharedDraw ν → ℂ) :
    physicalSharedRow A ν z n n' c = strippedMarkedRow ν n n' c := by
  have hgood := (goodSharedDraw_iff ν n n' D hn hn' hD z).mp hz
  have hcop := goodSharedDraw_coprime ν n n' D hn hn' hD z hz
  unfold physicalSharedRow strippedMarkedRow
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [physical_assemble_good_iff ν z r n n' D hn hn' hD hz,
    physical_assemble_good_right_iff ν z s n n' D hn hn' hD hz]
  by_cases hp : UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s
  · simp only [hp, if_true]
    rw [damping_sq_good_shared P G J m A ν z r n n' D hn hn' hD hz,
      damping_sq_strip_of_counts P G J m A ν (sharedDrawProduct ν z) n' hcop.2.1
        (sharedProduct_counts_of_draw_injective G ν z hgood.2 r)]
    unfold strippedDamping
    push_cast
    ring
  · simp only [hp, if_false, mul_zero]

theorem strippedMarkedRow_const {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m : ℕ} (ν : Pattern G.graph J P.ell m) (n n' : ℕ) (c : ℂ) :
    strippedMarkedRow ν n n' (fun _ _ => c) =
      ((markWeight G P.q ν.t n * markWeight G P.q ν.t n' : ℝ) : ℂ) * c :=
  unshared_marked_constant_row P ν n n' c

end Erdos821.P5Core
