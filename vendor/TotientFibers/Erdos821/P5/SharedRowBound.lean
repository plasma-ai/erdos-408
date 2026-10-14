import Erdos821.P5.UnsharedMarks
import Erdos821.P5.ListScales

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic

def sharedDampingLoss (P : Geometry) (G : PrimeGroups) (J : ℕ) : ℝ :=
  P.q ^ (-((((J + P.ell) * G.size : ℕ) : ℤ)))

theorem omega_le_mul_right (G : PrimeGroups) (D n : ℕ) : omega G n ≤ omega G (D * n) := by
  apply Finset.sum_le_sum
  intro g hg
  apply Finset.card_le_card
  intro p hp
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
    dvd_mul_of_dvd_right (Finset.mem_filter.mp hp).2 D⟩

/-- This loss bound permits repeated or overlapping shared labels, so it
also controls all excluded draws before imposing physical distinctness. -/
theorem damping_sq_le_stripped (P : Geometry) (G : PrimeGroups) (J m : ℕ)
    (A : Blueprint.Graph.Model P.graph G.graph J m)
    (ν : Blueprint.Graph.Pattern G.graph J P.ell m) (D n : ℕ) :
    A.damping ((D * n : ℕ) : ℤ) ^ 2 ≤ sharedDampingLoss P G J * strippedDamping P ν n := by
  rw [damping_sq_int]
  unfold sharedDampingLoss strippedDamping
  rw [← zpow_add₀ P.damping.1.ne']
  apply zpow_le_zpow_right_of_le_one₀ P.damping.1 P.damping.2.le
  have hω : (omega G n : ℤ) ≤ omega G (D * n) := by exact_mod_cast omega_le_mul_right G D n
  have ht : (0 : ℤ) ≤ ∑ g, (ν.t g : ℤ) := Finset.sum_nonneg (fun g hg => Int.natCast_nonneg _)
  omega

theorem sharedDampingLoss_le_log_power (P : Geometry) (G : PrimeGroups) (J : ℕ)
    (x : ℝ) (hL : 1 ≤ L x) (hG : Admissible P x G) :
    sharedDampingLoss P G J ≤ L x ^ ((-2 * Real.log P.q) * (J + P.ell : ℕ) * P.C₀) := by
  have hLpos : 0 < L x := by linarith
  have hlogq : Real.log P.q < 0 := Real.log_neg P.damping.1 P.damping.2
  have hβ : 0 ≤ (-Real.log P.q) * (J + P.ell : ℕ) :=
    mul_nonneg (neg_nonneg.mpr hlogq.le) (Nat.cast_nonneg _)
  have hs := mul_le_mul_of_nonneg_left (admissible_count_le P G x hG) hβ
  unfold sharedDampingLoss
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos P.damping.1, Real.rpow_def_of_pos hLpos]
  apply Real.exp_le_exp.mpr
  push_cast
  change _ ≤ Real.log (L x) * _
  unfold T at hs
  convert hs using 1 <;> push_cast <;> ring

theorem unsharedPhysical_of_physical_assemble {G : PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G.graph J ell m) (z : SharedDraw ν) (r : UnsharedDraw ν)
    (n : ℕ) (ha : G.graph.physical (J + ell) ((sharedDrawProduct ν z * n : ℕ) : ℤ)
      (assembleLabels ν z r)) : UnsharedPhysical ν n r := by
  intro g
  refine ⟨?_, ?_⟩
  · intro i j hij
    apply Subtype.ext
    apply (ha g).1
    simpa only [assembleLabels_unshared] using hij
  · intro i
    have ha' : G.graph.physical (J + ell)
        ((sharedProduct ν (assembleLabels ν z r) * n : ℕ) : ℤ) (assembleLabels ν z r) := by
      simpa only [sharedProduct_assemble] using ha
    simpa only [assembleLabels_unshared] using
      unshared_label_dvd_strip ν (assembleLabels ν z r) n ha' g i.val
        ((mem_unsharedSlots ν g i.val).mp i.property)

/-- Actual physical endpoint row after removing the shared product. The
coefficient may depend on both unshared lists and on the fixed shared draw. -/
def physicalSharedRow {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (A : Blueprint.Graph.Model P.graph G.graph J m)
    (ν : Blueprint.Graph.Pattern G.graph J P.ell m) (z : SharedDraw ν) (n n' : ℕ)
    (c : UnsharedDraw ν → UnsharedDraw ν → ℂ) : ℂ :=
  ((ν.physicalTargetMass ^ 2 * A.damping ((sharedDrawProduct ν z * n : ℕ) : ℤ) ^ 2 *
    A.damping ((sharedDrawProduct ν z * n' : ℕ) : ℤ) ^ 2 : ℝ) : ℂ) *
      ∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
        if G.graph.physical (J + P.ell) ((sharedDrawProduct ν z * n : ℕ) : ℤ)
            (assembleLabels ν z r) ∧
          G.graph.physical (J + P.ell) ((sharedDrawProduct ν z * n' : ℕ) : ℤ)
            (assembleLabels ν z s) then c r s else 0

theorem physicalSharedRow_norm_le {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (A : Blueprint.Graph.Model P.graph G.graph J m)
    (ν : Blueprint.Graph.Pattern G.graph J P.ell m) (z : SharedDraw ν) (n n' : ℕ)
    (c : UnsharedDraw ν → UnsharedDraw ν → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ r s, ‖c r s‖ ≤ B) (hV : ∀ g, 0 ≤ G.graph.V g) :
    ‖physicalSharedRow A ν z n n' c‖ ≤
      B * sharedDampingLoss P G J ^ 2 * unsharedWeight P ν n * unsharedWeight P ν n' := by
  let f := fun r s =>
    if G.graph.physical (J + P.ell) ((sharedDrawProduct ν z * n : ℕ) : ℤ)
        (assembleLabels ν z r) ∧
      G.graph.physical (J + P.ell) ((sharedDrawProduct ν z * n' : ℕ) : ℤ)
        (assembleLabels ν z s) then c r s else 0
  have hpoint (r s : UnsharedDraw ν) : ‖f r s‖ ≤
      B * (if UnsharedPhysical ν n r then (1 : ℝ) else 0) *
        (if UnsharedPhysical ν n' s then (1 : ℝ) else 0) := by
    dsimp [f]
    by_cases hp : G.graph.physical (J + P.ell) ((sharedDrawProduct ν z * n : ℕ) : ℤ)
        (assembleLabels ν z r) ∧
      G.graph.physical (J + P.ell) ((sharedDrawProduct ν z * n' : ℕ) : ℤ)
        (assembleLabels ν z s)
    · have hr := unsharedPhysical_of_physical_assemble ν z r n hp.1
      have hs := unsharedPhysical_of_physical_assemble ν z s n' hp.2
      simpa only [← Nat.cast_mul, hp, hr, hs, true_and, if_true, mul_one] using hc r s
    · simp only [← Nat.cast_mul, hp, if_false, norm_zero]
      apply mul_nonneg
      · exact mul_nonneg hB (by split_ifs <;> norm_num)
      · split_ifs <;> norm_num
  have hsum : ‖∑ r, ∑ s, f r s‖ ≤ B * unsharedCount ν n * unsharedCount ν n' := by
    calc
      _ ≤ ∑ r, ∑ s, ‖f r s‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr => norm_sum_le _ _))
      _ ≤ ∑ r, ∑ s, B * (if UnsharedPhysical ν n r then (1 : ℝ) else 0) *
          (if UnsharedPhysical ν n' s then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun s hs => hpoint r s))
      _ = _ := by
        unfold unsharedCount
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hmass := physicalTargetMass_nonneg ν hV
  have hcount := unsharedCount_nonneg ν n
  have hcount' := unsharedCount_nonneg ν n'
  have hloss : 0 ≤ sharedDampingLoss P G J := zpow_nonneg P.damping.1.le _
  have hd : 0 ≤ strippedDamping P ν n := zpow_nonneg P.damping.1.le _
  have hd' : 0 ≤ strippedDamping P ν n' := zpow_nonneg P.damping.1.le _
  unfold physicalSharedRow
  change ‖((_ : ℝ) : ℂ) * (∑ r, ∑ s, f r s)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (ν.physicalTargetMass ^ 2 * A.damping ((sharedDrawProduct ν z * n : ℕ) : ℤ) ^ 2 *
        A.damping ((sharedDrawProduct ν z * n' : ℕ) : ℤ) ^ 2) *
          (B * unsharedCount ν n * unsharedCount ν n') := by gcongr
    _ ≤ (ν.physicalTargetMass ^ 2 * (sharedDampingLoss P G J * strippedDamping P ν n) *
        (sharedDampingLoss P G J * strippedDamping P ν n')) *
          (B * unsharedCount ν n * unsharedCount ν n') := by
      gcongr <;> apply damping_sq_le_stripped
    _ = _ := by unfold unsharedWeight; ring

end Erdos821.P5Core
