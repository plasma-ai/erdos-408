import Erdos821.P4Probe.RowBridge
import Erdos821.P4Probe.Anova
import Erdos821.P4Probe.CountingTasks
import Erdos821.P4Probe.InvarianceTasks
import Erdos821.P4Count.ProbeCounting

set_option autoImplicit false
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Proj
open Erdos821.P4Probe

noncomputable section

variable {s M : ℕ} {α : Fin s → Type} [∀ g, Fintype (α g)]

local instance rowSiteDecidableEq' (s M : ℕ) : DecidableEq (RowSite s M) :=
  Classical.decEq _

/-- Pushforward action of a row permutation on flat samples. -/
def rowPush (π : Fin s → Equiv.Perm (Fin M))
    (y : ProductSample (FlatAlphabet α M)) : ProductSample (FlatAlphabet α M) :=
  fun z => y ((rowPermutation s M π).symm z)

/-- The pushforward action is bijective. -/
def rowSampleEquiv (π : Fin s → Equiv.Perm (Fin M)) :
    ProductSample (FlatAlphabet α M) ≃ ProductSample (FlatAlphabet α M) where
  toFun y := rowPush (s := s) (M := M) (α := α) π y
  invFun y := fun z => y ((rowPermutation s M π) z)
  left_inv y := by
    funext ⟨g, i⟩
    show y (g, (π g).symm ((π g) i)) = y (g, i)
    rw [Equiv.symm_apply_apply]
  right_inv y := by
    funext ⟨g, i⟩
    show y (g, (π g) ((π g).symm i)) = y (g, i)
    rw [Equiv.apply_symm_apply]

/-- Flat weights are constant along row permutations. -/
lemma flatWeight_pushforward (w : ∀ g, α g → ℝ)
    (π : Fin s → Equiv.Perm (Fin M)) (y : ProductSample (FlatAlphabet α M)) :
    productWeight (flatWeight w) (rowPush (s := s) (M := M) (α := α) π y) =
      productWeight (flatWeight w) y := by
  exact Equiv.prod_comp (rowPermutation s M π).symm
    (fun j => (flatWeight w) j (y j))

/-- A symmetric source stays invariant under row-permutation pushforward. -/
lemma symmetric_pushforward_invariant
    (f : ProbeSample α M → ℂ)
    (hsym : ∀ (π : Fin s → Equiv.Perm (Fin M)) x,
      f (fun g i => x g (π g i)) = f x)
    (π : Fin s → Equiv.Perm (Fin M)) (y : ProductSample (FlatAlphabet α M)) :
    (fun y => f (flattenRows.symm y)) (rowPush (s := s) (M := M) (α := α) π y) =
      (fun y => f (flattenRows.symm y)) y := by
  show f (flattenRows.symm (rowPush (s := s) (M := M) (α := α) π y)) =
    f (flattenRows.symm y)
  have hx : flattenRows.symm (rowPush (s := s) (M := M) (α := α) π y) =
      fun g i => (flattenRows.symm y) g ((π g).symm i) := by
    funext g i
    rfl
  rw [hx]
  exact hsym (fun g => (π g).symm) _

/-- Membership in a row-permuted Finset unfolds through the inverse. -/
lemma mem_map_rowPerm (π : Fin s → Equiv.Perm (Fin M))
    (S : Finset (RowSite s M)) (z : RowSite s M) :
    z ∈ S.map (rowPermutation s M π).toEmbedding ↔
      (rowPermutation s M π).symm z ∈ S := by
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨a, ha, heq⟩
    have hba : a = (rowPermutation s M π).symm z := by
      rw [← heq]
      exact (Equiv.symm_apply_apply _ _).symm
    rw [hba] at ha
    exact ha
  · intro h
    exact Finset.mem_map.mpr
      ⟨_, h, Equiv.apply_symm_apply _ _⟩

/-- Mixing commutes with row-permutation pushforward over mapped sets. -/
lemma mix_pushforward (π : Fin s → Equiv.Perm (Fin M))
    (S : Finset (RowSite s M))
    (x y : ProductSample (FlatAlphabet α M)) :
    mixCoords (S.map (rowPermutation s M π).toEmbedding)
        (rowPush (s := s) (M := M) (α := α) π x)
        (rowPush (s := s) (M := M) (α := α) π y) =
      rowPush (s := s) (M := M) (α := α) π (mixCoords S x y) := by
  funext ⟨g, i⟩
  have hiff : ((g, i) ∈ S.map (rowPermutation s M π).toEmbedding) ↔
      ((rowPermutation s M π).symm (g, i) ∈ S) :=
    mem_map_rowPerm π S (g, i)
  by_cases hz : (g, i) ∈ S.map (rowPermutation s M π).toEmbedding
  · have hS : (rowPermutation s M π).symm (g, i) ∈ S := hiff.mp hz
    have h1 : mixCoords (S.map (rowPermutation s M π).toEmbedding)
        (rowPush (s := s) (M := M) (α := α) π x)
        (rowPush (s := s) (M := M) (α := α) π y) (g, i) =
        (rowPush (s := s) (M := M) (α := α) π y) (g, i) := by
      simp only [mixCoords]
      exact if_pos hz
    have h2 : (mixCoords S x y) ((rowPermutation s M π).symm (g, i)) =
        y ((rowPermutation s M π).symm (g, i)) := by
      simp only [mixCoords]
      exact if_pos hS
    have h3 : (rowPush (s := s) (M := M) (α := α) π (mixCoords S x y)) (g, i) =
        (mixCoords S x y) ((rowPermutation s M π).symm (g, i)) := rfl
    have h4 : (rowPush (s := s) (M := M) (α := α) π y) (g, i) =
        y ((rowPermutation s M π).symm (g, i)) := rfl
    rw [h1, h3, h2, ← h4]
  · have hS : (rowPermutation s M π).symm (g, i) ∉ S :=
      fun h => hz (hiff.mpr h)
    have h1 : mixCoords (S.map (rowPermutation s M π).toEmbedding)
        (rowPush (s := s) (M := M) (α := α) π x)
        (rowPush (s := s) (M := M) (α := α) π y) (g, i) =
        (rowPush (s := s) (M := M) (α := α) π x) (g, i) := by
      simp only [mixCoords]
      exact if_neg hz
    have h2 : (mixCoords S x y) ((rowPermutation s M π).symm (g, i)) =
        x ((rowPermutation s M π).symm (g, i)) := by
      simp only [mixCoords]
      exact if_neg hS
    have h3 : (rowPush (s := s) (M := M) (α := α) π (mixCoords S x y)) (g, i) =
        (mixCoords S x y) ((rowPermutation s M π).symm (g, i)) := rfl
    have h4 : (rowPush (s := s) (M := M) (α := α) π x) (g, i) =
        x ((rowPermutation s M π).symm (g, i)) := rfl
    rw [h1, h3, h2, ← h4]

/-- Averaging over a mapped set pulls back through row permutations. -/
lemma avg_pullback (w : ∀ g, α g → ℝ)
    (π : Fin s → Equiv.Perm (Fin M))
    (U : Finset (RowSite s M)) (G : ProductSample (FlatAlphabet α M) → ℂ)
    (x : ProductSample (FlatAlphabet α M)) :
    productAverage (flatWeight w) (U.map (rowPermutation s M π).toEmbedding) G
        (rowPush (s := s) (M := M) (α := α) π x) =
      productAverage (flatWeight w) U
        (fun z => G (rowPush (s := s) (M := M) (α := α) π z)) x := by
  unfold productAverage
  symm
  apply Fintype.sum_equiv (rowSampleEquiv (s := s) (M := M) (α := α) π)
  intro y'
  show (productWeight (flatWeight w) y' : ℂ) *
      (fun z => G (rowPush (s := s) (M := M) (α := α) π z))
        (mixCoords U x y') =
    (productWeight (flatWeight w)
        (rowPush (s := s) (M := M) (α := α) π y') : ℂ) *
      G (mixCoords (U.map (rowPermutation s M π).toEmbedding)
        (rowPush (s := s) (M := M) (α := α) π x)
        (rowPush (s := s) (M := M) (α := α) π y'))
  rw [flatWeight_pushforward, mix_pushforward]

/-- Mapping by `σ.symm` then `σ` is the identity on finsets. -/
lemma map_symm_map (π : Fin s → Equiv.Perm (Fin M))
    (S : Finset (RowSite s M)) :
    (S.map (rowPermutation s M π).symm.toEmbedding).map
      (rowPermutation s M π).toEmbedding = S := by
  ext a
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨b, hb_mem, hb_eq⟩
    rcases Finset.mem_map.mp hb_mem with ⟨c, hc, hc_eq⟩
    have hb_eq' : (rowPermutation s M π) b = a := hb_eq
    have hc_eq' : (rowPermutation s M π).symm c = b := hc_eq
    rw [← hc_eq'] at hb_eq'
    have h0 : (rowPermutation s M π)
        ((rowPermutation s M π).symm c) = c :=
      Equiv.apply_symm_apply _ _
    have hca : c = a := h0.symm.trans hb_eq'
    rwa [hca] at hc
  · intro ha
    exact Finset.mem_map.mpr ⟨(rowPermutation s M π).symm a,
      Finset.mem_map.mpr ⟨a, ha, rfl⟩, Equiv.apply_symm_apply _ _⟩

/-- Mapping by `σ` then `σ.symm` is the identity on finsets. -/
lemma map_map_symm (π : Fin s → Equiv.Perm (Fin M))
    (S : Finset (RowSite s M)) :
    (S.map (rowPermutation s M π).toEmbedding).map
      (rowPermutation s M π).symm.toEmbedding = S := by
  ext a
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨b, hb_mem, hb_eq⟩
    rcases Finset.mem_map.mp hb_mem with ⟨c, hc, hc_eq⟩
    have hb_eq' : (rowPermutation s M π).symm b = a := hb_eq
    have hc_eq' : (rowPermutation s M π) c = b := hc_eq
    rw [← hc_eq'] at hb_eq'
    have h0 : (rowPermutation s M π).symm
        ((rowPermutation s M π) c) = c :=
      Equiv.symm_apply_apply _ _
    have hca : c = a := h0.symm.trans hb_eq'
    rwa [hca] at hc
  · intro ha
    exact Finset.mem_map.mpr ⟨(rowPermutation s M π) a,
      Finset.mem_map.mpr ⟨a, ha, rfl⟩, Equiv.symm_apply_apply _ _⟩

/-- Full projection pulls back through row permutations. -/
lemma full_pullback (w : ∀ g, α g → ℝ)
    (π : Fin s → Equiv.Perm (Fin M))
    (I : Finset (RowSite s M)) (G : ProductSample (FlatAlphabet α M) → ℂ)
    (x : ProductSample (FlatAlphabet α M)) :
    productFull (flatWeight w) (I.map (rowPermutation s M π).toEmbedding) G
        (rowPush (s := s) (M := M) (α := α) π x) =
      productFull (flatWeight w) I
        (fun z => G (rowPush (s := s) (M := M) (α := α) π z)) x := by
  unfold productFull
  symm
  refine Finset.sum_bij (fun V _ => V.map (rowPermutation s M π).toEmbedding)
    ?_ ?_ ?_ ?_
  · intro V hV
    simp only [Finset.mem_powerset] at hV ⊢
    exact Finset.map_subset_map.mpr hV
  · intro V₁ _ V₂ _ hEq
    have hsub12 : V₁.map (rowPermutation s M π).toEmbedding ⊆
        V₂.map (rowPermutation s M π).toEmbedding := by
      rw [hEq]
    have h12 : V₁ ⊆ V₂ :=
      Finset.map_subset_map.mp hsub12
    have hsub21 : V₂.map (rowPermutation s M π).toEmbedding ⊆
        V₁.map (rowPermutation s M π).toEmbedding := by
      rw [← hEq]
    have h21 : V₂ ⊆ V₁ :=
      Finset.map_subset_map.mp hsub21
    exact Finset.Subset.antisymm h12 h21
  · intro U hU
    simp only [Finset.mem_powerset] at hU
    refine ⟨U.map (rowPermutation s M π).symm.toEmbedding, ?_, ?_⟩
    · simp only [Finset.mem_powerset]
      have hsub : U.map (rowPermutation s M π).symm.toEmbedding ⊆
          (I.map (rowPermutation s M π).toEmbedding).map
            (rowPermutation s M π).symm.toEmbedding :=
        Finset.map_subset_map.mpr hU
      rwa [map_map_symm] at hsub
    · exact map_symm_map π U
  · intro V hV
    have hcard : (V.map (rowPermutation s M π).toEmbedding).card = V.card :=
      Finset.card_map _
    rw [hcard]
    congr 1
    exact (avg_pullback w π V G x).symm

/-- Complement of a mapped set is the mapped complement (relative to `univ`). -/
lemma univ_sdiff_map (π : Fin s → Equiv.Perm (Fin M))
    (S : Finset (RowSite s M)) :
    (Finset.univ \ S.map (rowPermutation s M π).toEmbedding) =
      (Finset.univ \ S).map (rowPermutation s M π).toEmbedding := by
  ext z
  have h1 : z ∈ Finset.univ \ S.map (rowPermutation s M π).toEmbedding ↔
      z ∉ S.map (rowPermutation s M π).toEmbedding := by
    simp
  have h2 : z ∈ (Finset.univ \ S).map (rowPermutation s M π).toEmbedding ↔
      (rowPermutation s M π).symm z ∉ S := by
    rw [mem_map_rowPerm]
    simp
  exact h1.trans ((mem_map_rowPerm π S z).not.trans h2.symm)

/-- ANOVA components pull back through row permutations. -/
lemma anova_pullback (w : ∀ g, α g → ℝ)
    (π : Fin s → Equiv.Perm (Fin M))
    (S : Finset (RowSite s M)) (G : ProductSample (FlatAlphabet α M) → ℂ)
    (x : ProductSample (FlatAlphabet α M)) :
    productAnova (flatWeight w) Finset.univ
        (S.map (rowPermutation s M π).toEmbedding) G
        (rowPush (s := s) (M := M) (α := α) π x) =
      productAnova (flatWeight w) Finset.univ S
        (fun z => G (rowPush (s := s) (M := M) (α := α) π z)) x := by
  unfold productAnova
  have hcompl : (Finset.univ \ S.map (rowPermutation s M π).toEmbedding) =
      (Finset.univ \ S).map (rowPermutation s M π).toEmbedding :=
    univ_sdiff_map π S
  rw [hcompl]
  have hcomp : (fun z => productAverage (flatWeight w)
      ((Finset.univ \ S).map (rowPermutation s M π).toEmbedding) G
      (rowPush (s := s) (M := M) (α := α) π z)) =
      productAverage (flatWeight w) (Finset.univ \ S)
        (fun z => G (rowPush (s := s) (M := M) (α := α) π z)) := by
    funext y
    exact avg_pullback w π (Finset.univ \ S) G y
  calc productFull (flatWeight w) (S.map (rowPermutation s M π).toEmbedding)
        (productAverage (flatWeight w)
          ((Finset.univ \ S).map (rowPermutation s M π).toEmbedding) G)
        (rowPush (s := s) (M := M) (α := α) π x)
      = productFull (flatWeight w) S
        (fun z => productAverage (flatWeight w)
          ((Finset.univ \ S).map (rowPermutation s M π).toEmbedding) G
          (rowPush (s := s) (M := M) (α := α) π z))
        x := full_pullback w π S _ _
    _ = productFull (flatWeight w) S
        (productAverage (flatWeight w) (Finset.univ \ S)
          (fun z => G (rowPush (s := s) (M := M) (α := α) π z))) x := by
        rw [hcomp]

/-- Symmetric ANOVA energies are invariant under row permutations. -/
lemma anova_energy_invariant (w : ∀ g, α g → ℝ)
    (f : ProbeSample α M → ℂ)
    (hsym : ∀ (π : Fin s → Equiv.Perm (Fin M)) x,
      f (fun g i => x g (π g i)) = f x)
    (π : Fin s → Equiv.Perm (Fin M)) (S : Finset (RowSite s M)) :
    productSqNorm (flatWeight w)
        (productAnova (flatWeight w) Finset.univ
          (S.map (rowPermutation s M π).toEmbedding)
          (fun y => f (flattenRows.symm y))) =
      productSqNorm (flatWeight w)
        (productAnova (flatWeight w) Finset.univ S
          (fun y => f (flattenRows.symm y))) := by
  let G : ProductSample (FlatAlphabet α M) → ℂ :=
    fun y => f (flattenRows.symm y)
  have hG : (fun z => G (rowPush (s := s) (M := M) (α := α) π z)) = G := by
    funext y
    exact symmetric_pushforward_invariant f hsym π y
  have hpoint : ∀ y, productAnova (flatWeight w) Finset.univ
      (S.map (rowPermutation s M π).toEmbedding) G
      (rowPush (s := s) (M := M) (α := α) π y) =
      productAnova (flatWeight w) Finset.univ S G y := by
    intro y
    have h := anova_pullback (s := s) (M := M) (α := α) w π S G y
    rwa [hG] at h
  unfold productSqNorm
  symm
  apply Fintype.sum_equiv (rowSampleEquiv (s := s) (M := M) (α := α) π)
  intro y
  show productWeight (flatWeight w) y *
      ‖productAnova (flatWeight w) Finset.univ S G y‖ ^ 2 =
    productWeight (flatWeight w) (rowPush (s := s) (M := M) (α := α) π y) *
      ‖productAnova (flatWeight w) Finset.univ
        (S.map (rowPermutation s M π).toEmbedding) G
        (rowPush (s := s) (M := M) (α := α) π y)‖ ^ 2
  rw [flatWeight_pushforward, hpoint]

end
end Erdos821.P4Proj

/-- The exclusive row-symmetry fact: ANOVA energies are invariant. -/
theorem Erdos821.P4Probe.RowAnovaInvariantTask_proof :
    Erdos821.P4Probe.RowAnovaInvariantTask := by
  intro s M α _ w f hsym π S
  exact Erdos821.P4Proj.anova_energy_invariant w f hsym π S

/-- The full symmetric component task follows from counting + invariance. -/
theorem Erdos821.P4Probe.SymmetricFullComponentTask_proof :
    Erdos821.P4Probe.SymmetricFullComponentTask :=
  Erdos821.P4Probe.symmetricFullComponentTask_of_counting
    Erdos821.P4Probe.ProbeCountingTask_proof
    Erdos821.P4Probe.RowAnovaInvariantTask_proof
