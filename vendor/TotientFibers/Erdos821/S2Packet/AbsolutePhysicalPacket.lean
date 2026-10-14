import Erdos821.S2.TransferenceAssemblyTask
import Erdos821.P3.PhysicalSchur

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Packet

open Erdos821.Blueprint.Graph

def absolutePhysicalRawReal {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (z z' : A.State) : ℝ :=
  if P.physical (J + F.ell) z.1 z.2 ∧ P.physical (J + F.ell) z'.1 z'.2 then
    ∑ v, ∑ u : P.Aux J,
      if (A.pattern v).compatible z.2 z'.2 ∧
          (A.pattern v).ban z.2 z'.2 u ∧
          z'.1 = z.1 + A.k * ((A.pattern v).D z.2 u : ℤ) then
        ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
          A.damping z.1 * A.damping z'.1) *
          ‖(A.pattern v).coefficient (P.restrictBig z.2) (P.restrictBig z'.2)
            (fun g => u g.val) *
            imaginaryPower ((A.pattern v).D z.2 u) A.zeta‖
      else 0
  else 0

lemma physicalRaw_true_eq_ofReal_absolutePhysicalRawReal
    {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (z z' : A.State) :
    A.physicalRaw true z z' = (absolutePhysicalRawReal A z z' : ℂ) := by
  classical
  by_cases hphys : P.physical (J + F.ell) z.1 z.2 ∧
      P.physical (J + F.ell) z'.1 z'.2
  · simp only [absolutePhysicalRawReal, Model.physicalRaw, if_pos hphys, if_true]
    simp only [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hcond : (A.pattern v).compatible z.2 z'.2 ∧
        (A.pattern v).ban z.2 z'.2 u ∧
        z'.1 = z.1 + A.k * ((A.pattern v).D z.2 u : ℤ)
    · simp [hcond, Complex.ofReal_mul]
    · simp [hcond]
  · simp [absolutePhysicalRawReal, Model.physicalRaw, hphys]

lemma absolutePhysicalRawReal_nonneg
    {F : FixedData} {P : PrimeGroups} {J m : ℕ} {x : ℝ}
    (A : Model F P J m) (z z' : A.State) (hP : P.Admissible F x) :
    0 ≤ absolutePhysicalRawReal A z z' := by
  classical
  unfold absolutePhysicalRawReal
  split_ifs with hphys
  · apply Finset.sum_nonneg
    intro v hv
    apply Finset.sum_nonneg
    intro u hu
    split_ifs with hcond
    · have haux : 0 < (A.pattern v).auxMass u :=
        Erdos821.P3Core.auxMass_pos_of_admissible (A.pattern v) u hP
      have hV : ∀ g : P.Group, 0 < P.V g :=
        fun g => Erdos821.P3Core.V_pos_of_admissible hP g
      have htarget : 0 < (A.pattern v).physicalTargetMass :=
        Erdos821.P3Core.physicalTargetMass_pos_of_admissible (A.pattern v) hV
      have hd₁ : 0 < A.damping z.1 := Erdos821.P3Core.damping_pos A z.1
      have hd₂ : 0 < A.damping z'.1 := Erdos821.P3Core.damping_pos A z'.1
      positivity
    · exact le_of_eq rfl
  · exact le_of_eq rfl

def absolutePhysicalKernelReal {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (z z' : A.State) : ℝ :=
  ((Fintype.card (P.Permutations (J + F.ell)) : ℝ) ^ 2)⁻¹ *
    ∑ π : P.Permutations (J + F.ell), ∑ τ : P.Permutations (J + F.ell),
      absolutePhysicalRawReal A (z.1, P.act π z.2) (z'.1, P.act τ z'.2)

lemma physicalKernel_true_eq_ofReal_absolutePhysicalKernelReal
    {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (z z' : A.State) :
    A.physicalKernel true z z' = (absolutePhysicalKernelReal A z z' : ℂ) := by
  classical
  simp [absolutePhysicalKernelReal, Model.physicalKernel,
    physicalRaw_true_eq_ofReal_absolutePhysicalRawReal,
    Complex.ofReal_sum, Complex.ofReal_mul]

lemma absolutePhysicalKernelReal_nonneg
    {F : FixedData} {P : PrimeGroups} {J m : ℕ} {x : ℝ}
    (A : Model F P J m) (z z' : A.State) (hP : P.Admissible F x) :
    0 ≤ absolutePhysicalKernelReal A z z' := by
  classical
  unfold absolutePhysicalKernelReal
  apply mul_nonneg
  · exact inv_nonneg.mpr (sq_nonneg _)
  · apply Finset.sum_nonneg
    intro π hπ
    apply Finset.sum_nonneg
    intro τ hτ
    exact absolutePhysicalRawReal_nonneg A _ _ hP

lemma physicalKernel_true_re_eq_absolutePhysicalKernelReal
    {F : FixedData} {P : PrimeGroups} {J m : ℕ} {x : ℝ}
    (A : Model F P J m) (z z' : A.State) (hP : P.Admissible F x) :
    (A.physicalKernel true z z').re = absolutePhysicalKernelReal A z z' := by
  rw [physicalKernel_true_eq_ofReal_absolutePhysicalKernelReal]
  simp

lemma physicalKernel_true_norm_eq_re
    {F : FixedData} {P : PrimeGroups} {J m : ℕ} {x : ℝ}
    (A : Model F P J m) (z z' : A.State) (hP : P.Admissible F x) :
    ‖A.physicalKernel true z z'‖ = (A.physicalKernel true z z').re := by
  rw [physicalKernel_true_eq_ofReal_absolutePhysicalKernelReal]
  simp [absolutePhysicalKernelReal_nonneg A z z' hP]

lemma pattern_D_le_sup_pow {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (u : P.Aux J) :
    ν.D a u ≤ P.allPrimes.sup id ^ (J * P.count) := by
  classical
  let S := P.allPrimes.sup id
  have hval (g : P.Group) (i : Fin J) :
      (if i ∈ ν.changed g then (u g i).val else (a g (ν.slot i)).val) ≤ S := by
    split_ifs with hi
    · change (u g i).val ≤ P.allPrimes.sup id
      exact Finset.le_sup (s := P.allPrimes) (f := id) (b := (u g i).val)
        (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, (u g i).property⟩)
    · change (a g (ν.slot i)).val ≤ P.allPrimes.sup id
      exact Finset.le_sup (s := P.allPrimes) (f := id) (b := (a g (ν.slot i)).val)
        (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, (a g (ν.slot i)).property⟩)
  calc
    ν.D a u = ∏ z ∈ (Finset.univ : Finset P.Group).product (Finset.univ : Finset (Fin J)),
        (if z.2 ∈ ν.changed z.1 then (u z.1 z.2).val else (a z.1 (ν.slot z.2)).val) := by
      simpa [Pattern.D] using
        (Finset.prod_product' (Finset.univ : Finset P.Group) (Finset.univ : Finset (Fin J))
          (fun g i => if i ∈ ν.changed g then (u g i).val else (a g (ν.slot i)).val)).symm
    _ ≤ S ^ ((Finset.univ : Finset P.Group).product (Finset.univ : Finset (Fin J))).card :=
      Finset.prod_le_pow_card _ _ S (by
        intro z hz
        exact hval z.1 z.2)
    _ = S ^ (J * P.count) := by simp [S, Finset.card_product, mul_comm]

lemma possiblePhysicalTargets_subset_neighbors {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (n : ℤ) :
    Erdos821.P3Core.possiblePhysicalTargets A n ⊆ A.neighbors n := by
  classical
  intro z hz
  change z ∈ Erdos821.P3Core.possiblePhysicalPositions A n ×ˢ Finset.univ at hz
  rcases Finset.mem_product.mp hz with ⟨hzpos, _⟩
  rcases Finset.mem_image.mp hzpos with ⟨w, hw, htime⟩
  rcases w with ⟨v, a, u⟩
  change n + A.k * ((A.pattern v).D a u : ℤ) = z.1 at htime
  have hD := pattern_D_le_sup_pow (A.pattern v) a u
  have hn : Int.natAbs (A.k * ((A.pattern v).D a u : ℤ)) ≤
      A.k.natAbs * (P.allPrimes.sup id) ^ (J * P.count) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ hD
  have hcast : (Int.natAbs (A.k * ((A.pattern v).D a u : ℤ)) : ℤ) ≤
      (A.stepBound : ℤ) := by
    exact_mod_cast hn
  have habs : |A.k * ((A.pattern v).D a u : ℤ)| ≤ (A.stepBound : ℤ) := by
    simpa only [Int.natCast_natAbs] using hcast
  have hdisp := abs_le.mp habs
  have hmem : n + A.k * ((A.pattern v).D a u : ℤ) ∈
      Finset.Icc (n - A.stepBound) (n + A.stepBound) := by
    simp only [Finset.mem_Icc]
    omega
  have hmem' : z.1 ∈ Finset.Icc (n - A.stepBound) (n + A.stepBound) := by
    simpa [htime] using hmem
  simpa [Model.neighbors, hmem']

lemma possiblePhysicalTargets_reverse_subset_neighbors {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (n : ℤ) :
    Erdos821.P3Core.possiblePhysicalTargets (Erdos821.P3Core.reversePhysicalModel A) n ⊆
      A.neighbors n := by
  intro z hz
  have hz' := possiblePhysicalTargets_subset_neighbors
    (Erdos821.P3Core.reversePhysicalModel A) n hz
  simpa [Model.neighbors, Model.stepBound, Erdos821.P3Core.reversePhysicalModel] using hz'

lemma physicalKernel_true_row_neighbor_norm_eq_tsum_re
    {F : FixedData} {P : PrimeGroups} {J m : ℕ} {x : ℝ}
    (A : Model F P J m) (z : A.State) (hP : P.Admissible F x) :
    (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z z'‖) =
      ∑' z', (A.physicalKernel true z z').re := by
  classical
  let S := Erdos821.P3Core.possiblePhysicalTargets A z.1
  have hsubset : S ⊆ A.neighbors z.1 := possiblePhysicalTargets_subset_neighbors A z.1
  have hsum : (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z z'‖) =
      ∑ z' ∈ S, ‖A.physicalKernel true z z'‖ := by
    exact (Finset.sum_subset hsubset (by
      intro z' hz' hzS
      simp [Erdos821.P3Core.physicalKernel_zero_outside_targets A z.1 z.2 z' hzS])).symm
  have htsum : (∑' z', (A.physicalKernel true z z').re) =
      ∑ z' ∈ S, (A.physicalKernel true z z').re := by
    apply tsum_eq_sum
    intro z' hz'
    simp [Erdos821.P3Core.physicalKernel_zero_outside_targets A z.1 z.2 z' hz']
  calc
    (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z z'‖) =
        ∑ z' ∈ S, ‖A.physicalKernel true z z'‖ := hsum
    _ = ∑ z' ∈ S, (A.physicalKernel true z z').re := by
      apply Finset.sum_congr rfl
      intro z' hz'
      exact physicalKernel_true_norm_eq_re A z z' hP
    _ = ∑' z', (A.physicalKernel true z z').re := htsum.symm

lemma physicalKernel_true_column_neighbor_norm_eq_tsum_re
    {F : FixedData} {P : PrimeGroups} {J m : ℕ} {x : ℝ}
    (A : Model F P J m) (z : A.State) (hP : P.Admissible F x) :
    (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z' z‖) =
      ∑' z', (A.physicalKernel true z' z).re := by
  classical
  let R := Erdos821.P3Core.reversePhysicalModel A
  let S := Erdos821.P3Core.possiblePhysicalTargets R z.1
  have hsubset : S ⊆ A.neighbors z.1 := by
    exact possiblePhysicalTargets_reverse_subset_neighbors A z.1
  have hzero (z' : A.State) (hz' : z' ∉ S) : A.physicalKernel true z' z = 0 := by
    rw [Erdos821.P3Core.physicalKernel_reverse_eq A z.1 z'.1 z.2 z'.2]
    exact Erdos821.P3Core.physicalKernel_zero_outside_targets R z.1 z.2 z' hz'
  have hsum : (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z' z‖) =
      ∑ z' ∈ S, ‖A.physicalKernel true z' z‖ := by
    exact (Finset.sum_subset hsubset (by
      intro z' hz' hzS
      simp [hzero z' hzS])).symm
  have htsum : (∑' z', (A.physicalKernel true z' z).re) =
      ∑ z' ∈ S, (A.physicalKernel true z' z).re := by
    apply tsum_eq_sum
    intro z' hz'
    simp [hzero z' hz']
  calc
    (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z' z‖) =
        ∑ z' ∈ S, ‖A.physicalKernel true z' z‖ := hsum
    _ = ∑ z' ∈ S, (A.physicalKernel true z' z).re := by
      apply Finset.sum_congr rfl
      intro z' hz'
      exact physicalKernel_true_norm_eq_re A z' z hP
    _ = ∑' z', (A.physicalKernel true z' z).re := htsum.symm

theorem AbsolutePhysicalPacketTask_proof :
    Erdos821.S2Core.AbsolutePhysicalPacketTask := by
  change Erdos821.Blueprint.Graph.AbsolutePhysicalBounds
  intro F m C₁
  obtain ⟨Cabs, hSchur⟩ := Erdos821.P3Core.physical_schur_proof F m C₁
  refine ⟨Cabs, ?_⟩
  intro J
  obtain ⟨x₀, hx₀⟩ := hSchur J
  filter_upwards [Filter.eventually_ge_atTop x₀] with x hge
  intro P A hP hmass
  obtain ⟨hrow, hcol⟩ := hx₀ x hge P hP A hmass
  constructor
  · intro z
    rw [physicalKernel_true_row_neighbor_norm_eq_tsum_re A z hP]
    exact hrow z
  · intro z
    rw [physicalKernel_true_column_neighbor_norm_eq_tsum_re A z hP]
    exact hcol z

example : Erdos821.S2Core.AbsolutePhysicalPacketTask :=
  AbsolutePhysicalPacketTask_proof


end Erdos821.S2Packet
