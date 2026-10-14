import Erdos821.P5.StrippedPhysicalLists
import Erdos821.Leaves.MarkSup

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

def unsharedSlotEquiv {G : PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G.graph J ell m) (g : Fin G.size) :
    {i : Fin (J + ell) // i ∈ unsharedSlots ν g} ≃ Fin (ν.t g) :=
  Finset.equivFinOfCardEq (unshared_slot_count ν g)

def unsharedTupleEquiv {G : PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G.graph J ell m) : UnsharedDraw ν ≃ Tuple G ν.t where
  toFun r g j := r g ((unsharedSlotEquiv ν g).symm j)
  invFun z g i := z g (unsharedSlotEquiv ν g i)
  left_inv r := by funext g i; simp
  right_inv z := by funext g i; simp

theorem unsharedPhysical_tuple_iff {G : PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G.graph J ell m) (n : ℕ) (r : UnsharedDraw ν) :
    admissibleMarks G ν.t n (unsharedTupleEquiv ν r) ↔ UnsharedPhysical ν n r := by
  constructor
  · intro hr g
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply (unsharedSlotEquiv ν g).injective
      apply (hr g).1
      simpa only [unsharedTupleEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using hij
    · intro i
      simpa only [unsharedTupleEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using
        (hr g).2 (unsharedSlotEquiv ν g i)
  · intro hr g
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply (unsharedSlotEquiv ν g).symm.injective
      exact (hr g).1 hij
    · intro i
      exact (hr g).2 ((unsharedSlotEquiv ν g).symm i)

def unsharedCount {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (n : ℕ) : ℝ :=
  ∑ r : UnsharedDraw ν, if UnsharedPhysical ν n r then 1 else 0

def strippedDamping {G : PrimeGroups} {J ell m : ℕ}
    (P : Geometry) (ν : Blueprint.Graph.Pattern G.graph J ell m) (n : ℕ) : ℝ :=
  P.q ^ ((omega G n : ℤ) - ∑ g, (ν.t g : ℤ))

def unsharedWeight {G : PrimeGroups} {J ell m : ℕ}
    (P : Geometry) (ν : Blueprint.Graph.Pattern G.graph J ell m) (n : ℕ) : ℝ :=
  strippedDamping P ν n * ν.physicalTargetMass * unsharedCount ν n

theorem unsharedCount_nonneg {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (n : ℕ) : 0 ≤ unsharedCount ν n := by
  apply Finset.sum_nonneg
  intro r hr
  split_ifs <;> norm_num

theorem physicalTargetMass_nonneg {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (hV : ∀ g, 0 ≤ G.V g) :
    0 ≤ ν.physicalTargetMass :=
  Finset.prod_nonneg (fun g hg => zpow_nonneg (hV g) _)

theorem unsharedWeight_nonneg {G : PrimeGroups} {J ell m : ℕ}
    (P : Geometry) (ν : Blueprint.Graph.Pattern G.graph J ell m) (n : ℕ)
    (hV : ∀ g, 0 ≤ G.graph.V g) : 0 ≤ unsharedWeight P ν n :=
  mul_nonneg (mul_nonneg (zpow_nonneg P.damping.1.le _) (physicalTargetMass_nonneg ν hV))
    (unsharedCount_nonneg ν n)

theorem unsharedWeight_eq_weightedMarks {G : PrimeGroups} {J ell m : ℕ}
    (P : Geometry) (ν : Blueprint.Graph.Pattern G.graph J ell m) (n : ℕ) :
    (unsharedWeight P ν n : ℂ) = weightedMarks G P.q ν.t (fun _ => 1) n := by
  have hm : ν.physicalTargetMass = ∏ g, (mass G g)⁻¹ ^ ν.t g := by
    unfold Blueprint.Graph.Pattern.physicalTargetMass
    simp only [graph_mass, zpow_neg, zpow_natCast, inv_pow]
  have hc : (unsharedCount ν n : ℂ) =
      ∑ z : Tuple G ν.t, if admissibleMarks G ν.t n z then (1 : ℂ) else 0 := by
    unfold unsharedCount
    rw [Complex.ofReal_sum, ← (unsharedTupleEquiv ν).symm.sum_comp]
    apply Finset.sum_congr rfl
    intro z hz
    have h := unsharedPhysical_tuple_iff ν n ((unsharedTupleEquiv ν).symm z)
    rw [(unsharedTupleEquiv ν).apply_symm_apply] at h
    by_cases hz : admissibleMarks G ν.t n z <;> simp [← h, hz]
  unfold unsharedWeight strippedDamping weightedMarks
  rw [hm, Complex.ofReal_mul, hc]

/-- The marked unshared-list weight has a fixed log-power bound. Its exponent
depends on the probe bound m and ell, and is independent of the lift depth J. -/
theorem eventual_unsharedWeight_bound (P : Geometry) (ell m : ℕ) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (J : ℕ) (ν : Blueprint.Graph.Pattern G.graph J ell m) (n : ℕ),
        Admissible P x G → unsharedWeight P ν n ≤ L x ^ C := by
  obtain ⟨C, hC⟩ := mark_sup P (ell + m)
  refine ⟨C, ?_⟩
  filter_upwards [hC] with x hx
  intro G J ν n hG
  have hV (g : Fin G.size) : 0 ≤ G.graph.V g := by
    rw [graph_mass]
    exact (P.positive.2.2.1.trans_le (hG.2.2.1 g).1).le
  have hb := hx G hG ν.t (fun _ => 1) 1
    (fun g => by dsimp [Blueprint.Graph.Pattern.t]; exact Nat.add_le_add_left (ν.bound g) ell)
    (by norm_num) (by intro z; simp) n
  rw [← unsharedWeight_eq_weightedMarks P ν n, Complex.norm_real,
    Real.norm_of_nonneg (unsharedWeight_nonneg P ν n hV)] at hb
  simpa using hb

end Erdos821.P5Core
