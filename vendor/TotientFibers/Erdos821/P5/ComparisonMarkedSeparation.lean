import Erdos821.P5.ComparisonFactors

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- A single endpoint's actual unshared marked weight. -/
def unsharedMarkedFunction {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (ν : Pattern G.graph J P.ell m) (b : UnsharedDraw ν → ℂ) (n : ℕ) : ℂ :=
  ((strippedDamping P ν n * ν.physicalTargetMass : ℝ) : ℂ) *
    ∑ r : UnsharedDraw ν, if UnsharedPhysical ν n r then b r else 0

theorem unsharedMarkedFunction_eq_weightedMarks {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (ν : Pattern G.graph J P.ell m) (b : UnsharedDraw ν → ℂ) (n : ℕ) :
    unsharedMarkedFunction ν b n =
      weightedMarks G P.q ν.t (fun z => b ((unsharedTupleEquiv ν).symm z)) n := by
  have hm : ν.physicalTargetMass = ∏ g, (mass G g)⁻¹ ^ ν.t g := by
    unfold Pattern.physicalTargetMass
    simp only [graph_mass, zpow_neg, zpow_natCast, inv_pow]
  unfold unsharedMarkedFunction strippedDamping weightedMarks
  rw [hm]
  congr 1
  rw [← (unsharedTupleEquiv ν).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro z hz
  have hp := unsharedPhysical_tuple_iff ν n ((unsharedTupleEquiv ν).symm z)
  rw [(unsharedTupleEquiv ν).apply_symm_apply] at hp
  rw [hp]

/-- Independent endpoint coefficients factor exactly, including empty
sets of physical lists at either endpoint. -/
theorem strippedMarkedRow_mul {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (ν : Pattern G.graph J P.ell m) (n n' : ℕ)
    (b c : UnsharedDraw ν → ℂ) :
    strippedMarkedRow ν n n' (fun r s => b r * c s) =
      unsharedMarkedFunction ν b n * unsharedMarkedFunction ν c n' := by
  have hs : (∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
      if UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s then b r * c s else 0) =
      (∑ r : UnsharedDraw ν, if UnsharedPhysical ν n r then b r else 0) *
        ∑ s : UnsharedDraw ν, if UnsharedPhysical ν n' s then c s else 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hp : UnsharedPhysical ν n r <;>
      by_cases hp' : UnsharedPhysical ν n' s <;> simp [hp, hp']
  unfold strippedMarkedRow unsharedMarkedFunction
  rw [hs]
  push_cast
  ring

theorem strippedMarkedRow_smul {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (ν : Pattern G.graph J P.ell m) (n n' : ℕ) (a : ℂ)
    (b : UnsharedDraw ν → UnsharedDraw ν → ℂ) :
    strippedMarkedRow ν n n' (fun r s => a * b r s) =
      a * strippedMarkedRow ν n n' b := by
  have he (r s : UnsharedDraw ν) :
      (if UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s then a * b r s else 0) =
        a * (if UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s then b r s else 0) := by
    split_ifs <;> simp
  unfold strippedMarkedRow
  simp_rw [he, ← Finset.mul_sum]
  ring

theorem strippedMarkedRow_sum {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    {ι : Type*} (ν : Pattern G.graph J P.ell m) (n n' : ℕ) (s : Finset ι)
    (b : ι → UnsharedDraw ν → UnsharedDraw ν → ℂ) :
    strippedMarkedRow ν n n' (fun r t => ∑ i ∈ s, b i r t) =
      ∑ i ∈ s, strippedMarkedRow ν n n' (b i) := by
  unfold strippedMarkedRow
  simp_rw [Finset.ite_sum_zero]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := s)]
  rw [Finset.mul_sum]

def comparisonMarkTest {G : Blueprint.Graph.PrimeGroups} {J ell m Q : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (h : ℝ) (j : ℤ) (χ : CharacterIndex Q) (r : UnsharedDraw ν) : ℂ :=
  comparisonCellCharacter h j χ (comparisonMarkProduct ν block side r)

theorem comparisonMarkTest_norm_le {G : Blueprint.Graph.PrimeGroups} {J ell m Q : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (h : ℝ) (j : ℤ) (χ : CharacterIndex Q) (r : UnsharedDraw ν) :
    ‖comparisonMarkTest ν block side h j χ r‖ ≤ 1 :=
  comparisonCellCharacter_norm_le h j χ _

theorem comparisonMarkTest_big_ext {G : Blueprint.Graph.PrimeGroups} {J ell m Q : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (h : ℝ) (j : ℤ) (χ : CharacterIndex Q) (r s : UnsharedDraw ν)
    (hrs : ∀ g : G.BigGroup, r g.val = s g.val) :
    comparisonMarkTest ν block side h j χ r = comparisonMarkTest ν block side h j χ s := by
  unfold comparisonMarkTest
  rw [comparisonMarkProduct_big_ext ν block side r s hrs]

/-- The marked endpoint sequence is fixed by its cell and character;
neither a free draw nor a shared reference draw is an argument. -/
def comparisonMarkedEndpoint {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool) (side : Bool)
    (h : ℝ) (j : ℤ) (χ : CharacterIndex Q) (n : ℕ) : ℂ :=
  unsharedMarkedFunction ν (comparisonMarkTest ν block side h j χ) n

theorem eventual_comparisonMarkedEndpoint_bound (P : Geometry) (m : ℕ) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (J Q : ℕ) (ν : Pattern G.graph J P.ell m)
        (block : G.graph.BigGroup → Bool) (side : Bool) (h : ℝ) (j : ℤ)
        (χ : CharacterIndex Q) (n : ℕ),
        Admissible P x G → ‖comparisonMarkedEndpoint ν block side h j χ n‖ ≤ L x ^ C := by
  obtain ⟨C, hC⟩ := mark_sup P (P.ell + m)
  refine ⟨C, ?_⟩
  filter_upwards [hC] with x hx
  intro G J Q ν block side h j χ n hG
  unfold comparisonMarkedEndpoint
  rw [unsharedMarkedFunction_eq_weightedMarks]
  simpa only [one_mul] using hx G hG ν.t
    (fun z => comparisonMarkTest ν block side h j χ ((unsharedTupleEquiv ν).symm z)) 1
    (fun g => by dsimp [Pattern.t]; exact Nat.add_le_add_left (ν.bound g) P.ell)
    (by norm_num) (fun z => comparisonMarkTest_norm_le ν block side h j χ _) n

end Erdos821.P5Core
