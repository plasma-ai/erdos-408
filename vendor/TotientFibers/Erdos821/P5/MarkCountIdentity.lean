import Erdos821.P5.UnsharedMarks

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic

abbrev DividingLabel (G : PrimeGroups) (g : Fin G.size) (n : ℕ) :=
  {p : Label G g // p.val ∣ n}

def physicalTupleEquiv (G : PrimeGroups) (t : Fin G.size → ℕ) (n : ℕ) :
    {z : Tuple G t // admissibleMarks G t n z} ≃
      ((g : Fin G.size) → Fin (t g) ↪ DividingLabel G g n) where
  toFun z g := ⟨fun i => ⟨z.val g i, (z.property g).2 i⟩, by
    intro i j hij
    exact (z.property g).1 (congrArg Subtype.val hij)⟩
  invFun z := ⟨fun g i => (z g i).val, by
    intro g
    refine ⟨?_, fun i => (z g i).property⟩
    intro i j hij
    exact (z g).injective (Subtype.ext hij)⟩
  left_inv z := rfl
  right_inv z := rfl

/-- Exact cardinality of distinct ordered prime lists dividing n. -/
theorem physicalTuple_card (G : PrimeGroups) (t : Fin G.size → ℕ) (n : ℕ) :
    Fintype.card {z : Tuple G t // admissibleMarks G t n z} =
      ∏ g, Nat.descFactorial (omegaGroup G g n) (t g) := by
  rw [Fintype.card_congr (physicalTupleEquiv G t n), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro g hg
  rw [Fintype.card_embedding_eq, Fintype.card_fin]
  rw [show Fintype.card (DividingLabel G g n) = omegaGroup G g n from
    GraphLemmas.card_div_label2 G n g]

theorem physicalTuple_count (G : PrimeGroups) (t : Fin G.size → ℕ) (n : ℕ) :
    (∑ z : Tuple G t, if admissibleMarks G t n z then (1 : ℝ) else 0) =
      ∏ g, (Nat.descFactorial (omegaGroup G g n) (t g) : ℝ) := by
  rw [← Nat.cast_prod, ← physicalTuple_card G t n]
  have hc : Fintype.card {z : Tuple G t // admissibleMarks G t n z} =
      (Finset.univ.filter (fun z : Tuple G t => admissibleMarks G t n z)).card :=
    Fintype.card_subtype _
  rw [hc, Finset.sum_boole]

theorem weightedMarks_one (G : PrimeGroups) (q : ℝ) (t : Fin G.size → ℕ) (n : ℕ) :
    weightedMarks G q t (fun _ => 1) n = (markWeight G q t n : ℂ) := by
  have hs : (∑ z : Tuple G t, if admissibleMarks G t n z then (1 : ℂ) else 0) =
      Complex.ofReal (∏ g, (Nat.descFactorial (omegaGroup G g n) (t g) : ℝ)) := by
    rw [← physicalTuple_count G t n, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro z hz
    split_ifs <;> simp
  unfold weightedMarks markWeight
  rw [hs]
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_natCast]
  rw [Finset.prod_div_distrib]
  simp only [div_eq_mul_inv, inv_pow, Finset.prod_inv_distrib, Complex.ofReal_inv,
    Complex.ofReal_pow]
  ring

theorem unsharedCount_eq_descFactorial {G : PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G.graph J ell m) (n : ℕ) :
    unsharedCount ν n = ∏ g, (Nat.descFactorial (omegaGroup G g n) (ν.t g) : ℝ) := by
  unfold unsharedCount
  rw [← (unsharedTupleEquiv ν).symm.sum_comp]
  change (∑ z : Tuple G ν.t, if UnsharedPhysical ν n ((unsharedTupleEquiv ν).symm z)
    then (1 : ℝ) else 0) = _
  have hp (z : Tuple G ν.t) : UnsharedPhysical ν n ((unsharedTupleEquiv ν).symm z) ↔
      admissibleMarks G ν.t n z := by
    have h := unsharedPhysical_tuple_iff ν n ((unsharedTupleEquiv ν).symm z)
    rw [(unsharedTupleEquiv ν).apply_symm_apply] at h
    exact h.symm
  simp_rw [hp]
  exact physicalTuple_count G ν.t n

theorem unsharedWeight_eq_markWeight {G : PrimeGroups} {J ell m : ℕ}
    (P : Geometry) (ν : Blueprint.Graph.Pattern G.graph J ell m) (n : ℕ) :
    unsharedWeight P ν n = markWeight G P.q ν.t n := by
  have h := unsharedWeight_eq_weightedMarks P ν n
  rw [weightedMarks_one] at h
  exact Complex.ofReal_injective h

/-- A constant raw-pattern coefficient yields precisely the two markWeight
factors in shiftCorrelation, including endpoints with no physical lists. -/
theorem unshared_marked_constant_row {G : PrimeGroups} {J ell m : ℕ}
    (P : Geometry) (ν : Blueprint.Graph.Pattern G.graph J ell m) (n n' : ℕ) (c : ℂ) :
    ((strippedDamping P ν n * strippedDamping P ν n' * ν.physicalTargetMass ^ 2 : ℝ) : ℂ) *
      (∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
        if UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s then c else 0) =
      ((markWeight G P.q ν.t n * markWeight G P.q ν.t n' : ℝ) : ℂ) * c := by
  have hsum : (∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
      if UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s then c else 0) =
      (unsharedCount ν n : ℂ) * (unsharedCount ν n' : ℂ) * c := by
    unfold unsharedCount
    simp_rw [Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases h : UnsharedPhysical ν n r <;> by_cases h' : UnsharedPhysical ν n' s <;> simp [h, h']
  rw [hsum, ← unsharedWeight_eq_markWeight P ν n, ← unsharedWeight_eq_markWeight P ν n']
  unfold unsharedWeight
  push_cast
  ring

end Erdos821.P5Core
