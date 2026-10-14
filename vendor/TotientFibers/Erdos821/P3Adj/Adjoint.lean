import Erdos821.P3Adj.Factor
import Erdos821.P3Adj.Single
import Erdos821.S2.MemoryGhost
import Erdos821.S2.GhostTasks

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Adj

open Erdos821.Blueprint.Graph hiding GhostChoice absoluteMemoryGhostKernel absoluteScaledMemoryGhostKernel deleteMemoryIndices ghostBirthCount ghostChoiceValid ghostChoiceWeight ghostReversalFactor memoryEntry memoryGhostKernel zeroBirthBatch zeroMemoryIndices
open Erdos821.S2Core

variable {P : PrimeGroups} {g : P.BigGroup}

/-- Fiber vanishes outside the deletion image. -/
lemma fiberA_card_eq_zero_of_not_mem (s u : P.Memory g.val)
    (h : u ∉ Finset.image (fun A : Finset (Fin s.card) => deleteMemoryIndices s A)
      (Finset.univ.filter (fun A => A ⊆ zeroMemoryIndices s))) :
    (fiberA (P := P) (g := g) s u).card = 0 := by
  by_contra hne
  have hpos : 0 < (fiberA (P := P) (g := g) s u).card :=
    Nat.pos_of_ne_zero hne
  obtain ⟨A, hA⟩ := Finset.card_pos.mp hpos
  have hmem : A ⊆ zeroMemoryIndices s ∧ deleteMemoryIndices s A = u := by
    simpa only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and] using hA
  have hA_mem : A ∈ Finset.univ.filter (fun A : Finset (Fin s.card) => A ⊆ zeroMemoryIndices s) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ A, hmem.1⟩
  have hu : deleteMemoryIndices s A ∈ Finset.image
      (fun A : Finset (Fin s.card) => deleteMemoryIndices s A)
      (Finset.univ.filter (fun A => A ⊆ zeroMemoryIndices s)) :=
    Finset.mem_image_of_mem _ hA_mem
  rw [hmem.2] at hu
  exact h hu

/-- Single-group mass-kernel reversal. -/
lemma single_mass_kernel_eq (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 : P.Memory g.val)
    (hrho : 0 < rho) (hV : 0 < P.V g.val)
    (hbase : ∀ q : P.Prime g.val, 0 < baselinePrime F n q.val)
    (hd : 0 < d)
    (hagree_st : ∀ v : P.Particle g.val, ¬ isZeroParticle v → s0.count v = t0.count v) :
    P.groupMemoryMass F n g.val s0 * singleKernel F n rho d i g s0 t0 =
      singleReversal P d g s0 t0 *
        (P.groupMemoryMass F n g.val t0 * singleKernel F n rho d i g t0 s0) := by
  have hker_s := singleKernel_eq_image_sum F n rho d i g s0 t0 hrho hV hbase
  have hker_t := singleKernel_eq_image_sum F n rho d i g t0 s0 hrho hV hbase
  rw [hker_s, hker_t]
  let Ss := Finset.image (fun A : Finset (Fin s0.card) => deleteMemoryIndices s0 A)
    (Finset.univ.filter (fun A => A ⊆ zeroMemoryIndices s0))
  let St := Finset.image (fun A : Finset (Fin t0.card) => deleteMemoryIndices t0 A)
    (Finset.univ.filter (fun A => A ⊆ zeroMemoryIndices t0))
  let S := Ss ∪ St
  have hSs_sub : Ss ⊆ S := Finset.subset_union_left
  have hSt_sub : St ⊆ S := Finset.subset_union_right
  have hsum_s : (∑ u ∈ Ss, ((fiberA (P := P) (g := g) s0 u).card : ℝ) *
      perU_term F n rho d i g s0 t0 u) =
      (∑ u ∈ S, ((fiberA (P := P) (g := g) s0 u).card : ℝ) *
        perU_term F n rho d i g s0 t0 u) := by
    apply Finset.sum_subset hSs_sub
    intro u huS huNot
    have hfib0 : (fiberA (P := P) (g := g) s0 u).card = 0 :=
      fiberA_card_eq_zero_of_not_mem s0 u huNot
    simp only [hfib0, Nat.cast_zero, zero_mul]
  have hsum_t : (∑ u ∈ St, ((fiberA (P := P) (g := g) t0 u).card : ℝ) *
      perU_term F n rho d i g t0 s0 u) =
      (∑ u ∈ S, ((fiberA (P := P) (g := g) t0 u).card : ℝ) *
        perU_term F n rho d i g t0 s0 u) := by
    apply Finset.sum_subset hSt_sub
    intro u huS huNot
    have hfib0 : (fiberA (P := P) (g := g) t0 u).card = 0 :=
      fiberA_card_eq_zero_of_not_mem t0 u huNot
    simp only [hfib0, Nat.cast_zero, zero_mul]
  rw [hsum_s, hsum_t, Finset.mul_sum, Finset.mul_sum]
  have hinner : (∑ u ∈ S, P.groupMemoryMass F n g.val s0 *
      (((fiberA (P := P) (g := g) s0 u).card : ℝ) *
        perU_term F n rho d i g s0 t0 u)) =
      (∑ u ∈ S, singleReversal P d g s0 t0 *
        (P.groupMemoryMass F n g.val t0 *
          (((fiberA (P := P) (g := g) t0 u).card : ℝ) *
            perU_term F n rho d i g t0 s0 u))) := by
    apply Finset.sum_congr rfl
    intro u _
    have hpu := perU_mass_eq F n rho d i g s0 t0 u hrho hV hbase hd hagree_st
    linear_combination hpu
  rw [hinner, ← Finset.mul_sum]

/-- Ghost adjoint identity. -/
theorem GhostAdjointTask_proof : Erdos821.S2Core.GhostAdjointTask := by
  intro F P J n r hV hbase d hd i s t
  have hd_pos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  have hrho : 0 < r.rho := r.rho_pos
  have hVbig : ∀ g : P.BigGroup, 0 < P.V g.val := fun g => hV g.val
  have hbase_big : ∀ (g : P.BigGroup) (q : P.Prime g.val), 0 < baselinePrime F n q.val :=
    fun g q => hbase g q
  by_cases hcoord : s.1 = t.1 ∧ s.2.1 = t.2.1
  · have hker_st := globalKernel_eq_prod F J n r.rho d i s t hcoord
    have hcoord_symm : t.1 = s.1 ∧ t.2.1 = s.2.1 := ⟨hcoord.1.symm, hcoord.2.symm⟩
    have hker_ts := globalKernel_eq_prod F J n r.rho d i t s hcoord_symm
    have hRevProd : ghostReversalFactor d t s =
        ∏ g : P.BigGroup, singleReversal P d g (s.2.2 g) (t.2.2 g) := rfl
    by_cases hsmall : P.smallPhysical s.1 s.2.1
    · have hsmall_t : P.smallPhysical t.1 t.2.1 := by
        rw [← hcoord.1, ← hcoord.2]
        exact hsmall
      have hmass_s : P.memoryMass F J n s =
          (Fintype.card P.SmallResidues : ℝ)⁻¹ *
            (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
            (∏ g : P.BigGroup, ∏ k, tiltedMu F P n g.val (s.2.1 g.val k)) *
            (∏ g : P.BigGroup, P.groupMemoryMass F n g.val (s.2.2 g)) := by
        unfold PrimeGroups.memoryMass
        rw [if_pos hsmall]
      have hmass_t : P.memoryMass F J n t =
          (Fintype.card P.SmallResidues : ℝ)⁻¹ *
            (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
            (∏ g : P.BigGroup, ∏ k, tiltedMu F P n g.val (s.2.1 g.val k)) *
            (∏ g : P.BigGroup, P.groupMemoryMass F n g.val (t.2.2 g)) := by
        unfold PrimeGroups.memoryMass
        rw [if_pos hsmall_t]
        rw [← hcoord.2]
      by_cases hmismatch : ∃ g : P.BigGroup, ∃ v : P.Particle g.val,
          ¬ isZeroParticle v ∧ (s.2.2 g).count v ≠ (t.2.2 g).count v
      · obtain ⟨g0, v0, hv0, hne⟩ := hmismatch
        have hmis : ∃ v : P.Particle g0.val,
            ¬ isZeroParticle v ∧ (s.2.2 g0).count v ≠ (t.2.2 g0).count v :=
          ⟨v0, hv0, hne⟩
        have hker_st0 : singleKernel F n r.rho d i g0 (s.2.2 g0) (t.2.2 g0) = 0 :=
          singleKernel_eq_zero_of_mismatch hmis F n r.rho d i
        have hmis_symm : ∃ v : P.Particle g0.val,
            ¬ isZeroParticle v ∧ (t.2.2 g0).count v ≠ (s.2.2 g0).count v :=
          ⟨v0, hv0, fun h => hne h.symm⟩
        have hker_ts0 : singleKernel F n r.rho d i g0 (t.2.2 g0) (s.2.2 g0) = 0 :=
          singleKernel_eq_zero_of_mismatch hmis_symm F n r.rho d i
        have hprod_st0 : (∏ g : P.BigGroup, singleKernel F n r.rho d i g (s.2.2 g) (t.2.2 g)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ g0) hker_st0
        have hprod_ts0 : (∏ g : P.BigGroup, singleKernel F n r.rho d i g (t.2.2 g) (s.2.2 g)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ g0) hker_ts0
        rw [hmass_s, hmass_t, hker_st, hker_ts, hprod_st0, hprod_ts0]
        ring
      · push Not at hmismatch
        have hagree_all : ∀ (g : P.BigGroup) (v : P.Particle g.val),
            ¬ isZeroParticle v → (s.2.2 g).count v = (t.2.2 g).count v := by
          intro g v hv
          by_contra hne
          exact hne (hmismatch g v hv)
        have hPerGroup : ∀ g : P.BigGroup,
            P.groupMemoryMass F n g.val (s.2.2 g) *
              singleKernel F n r.rho d i g (s.2.2 g) (t.2.2 g) =
              singleReversal P d g (s.2.2 g) (t.2.2 g) *
                (P.groupMemoryMass F n g.val (t.2.2 g) *
                  singleKernel F n r.rho d i g (t.2.2 g) (s.2.2 g)) := by
          intro g
          exact single_mass_kernel_eq F n r.rho d i g (s.2.2 g) (t.2.2 g)
            hrho (hVbig g) (hbase_big g) hd_pos (hagree_all g)
        have hProd : (∏ g : P.BigGroup,
            (P.groupMemoryMass F n g.val (s.2.2 g) *
              singleKernel F n r.rho d i g (s.2.2 g) (t.2.2 g))) =
            (∏ g : P.BigGroup,
              (singleReversal P d g (s.2.2 g) (t.2.2 g) *
                (P.groupMemoryMass F n g.val (t.2.2 g) *
                  singleKernel F n r.rho d i g (t.2.2 g) (s.2.2 g)))) := by
          apply Finset.prod_congr rfl
          intro g _
          exact hPerGroup g
        have hL : (∏ g : P.BigGroup,
            (P.groupMemoryMass F n g.val (s.2.2 g) *
              singleKernel F n r.rho d i g (s.2.2 g) (t.2.2 g))) =
            (∏ g : P.BigGroup, P.groupMemoryMass F n g.val (s.2.2 g)) *
              (∏ g : P.BigGroup, singleKernel F n r.rho d i g (s.2.2 g) (t.2.2 g)) := by
          rw [Finset.prod_mul_distrib]
        have hR1 : (∏ g : P.BigGroup,
            (singleReversal P d g (s.2.2 g) (t.2.2 g) *
              (P.groupMemoryMass F n g.val (t.2.2 g) *
                singleKernel F n r.rho d i g (t.2.2 g) (s.2.2 g)))) =
            (∏ g : P.BigGroup, singleReversal P d g (s.2.2 g) (t.2.2 g)) *
              (∏ g : P.BigGroup, (P.groupMemoryMass F n g.val (t.2.2 g) *
                singleKernel F n r.rho d i g (t.2.2 g) (s.2.2 g))) := by
          rw [Finset.prod_mul_distrib]
        have hR2 : (∏ g : P.BigGroup, (P.groupMemoryMass F n g.val (t.2.2 g) *
            singleKernel F n r.rho d i g (t.2.2 g) (s.2.2 g))) =
            (∏ g : P.BigGroup, P.groupMemoryMass F n g.val (t.2.2 g)) *
              (∏ g : P.BigGroup, singleKernel F n r.rho d i g (t.2.2 g) (s.2.2 g)) := by
          rw [Finset.prod_mul_distrib]
        rw [hL, hR1, hR2] at hProd
        rw [hmass_s, hmass_t, hker_st, hker_ts, hRevProd]
        have hC : (Fintype.card P.SmallResidues : ℝ)⁻¹ *
            (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
            (∏ g : P.BigGroup, ∏ k, tiltedMu F P n g.val (s.2.1 g.val k)) =
            (Fintype.card P.SmallResidues : ℝ)⁻¹ *
            (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
            (∏ g : P.BigGroup, ∏ k, tiltedMu F P n g.val (s.2.1 g.val k)) := rfl
        linear_combination
          ((Fintype.card P.SmallResidues : ℝ)⁻¹ *
            (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
            (∏ g : P.BigGroup, ∏ k, tiltedMu F P n g.val (s.2.1 g.val k))) * hProd
    · have hsmall_t : ¬ P.smallPhysical t.1 t.2.1 := by
        rw [← hcoord.1, ← hcoord.2]
        exact hsmall
      have hmass_s0 : P.memoryMass F J n s = 0 := by
        unfold PrimeGroups.memoryMass
        rw [if_neg hsmall]
      have hmass_t0 : P.memoryMass F J n t = 0 := by
        unfold PrimeGroups.memoryMass
        rw [if_neg hsmall_t]
      rw [hmass_s0, hmass_t0]
      ring
  · have hcoord_symm : ¬ (t.1 = s.1 ∧ t.2.1 = s.2.1) := by
      rintro ⟨h1, h2⟩
      exact hcoord ⟨h1.symm, h2.symm⟩
    have hker_st0 : absoluteScaledMemoryGhostKernel F J n r.rho d i s t = 0 := by
      unfold absoluteScaledMemoryGhostKernel
      rw [if_neg hcoord]
    have hker_ts0 : absoluteScaledMemoryGhostKernel F J n r.rho d i t s = 0 := by
      unfold absoluteScaledMemoryGhostKernel
      rw [if_neg hcoord_symm]
    rw [hker_st0, hker_ts0]
    ring


end Erdos821.P3Adj

theorem Erdos821.S2Core.GhostAdjointTask_proof : Erdos821.S2Core.GhostAdjointTask :=
  Erdos821.P3Adj.GhostAdjointTask_proof



