import Erdos821.P3High.GhostRelabel

/-! The initial boundary with prescribed initial big labels: each prescribed slot replaces
its total tilted mass by a point mass. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3High

open Erdos821.Blueprint.Graph hiding BirthAddress EdgeChoice GhostChoice MemoryHistory
  TransferChoice TransferMode absoluteMemoryEdgeKernel absoluteMemoryGhostKernel
  absoluteScaledMemoryGhostKernel deleteMemoryIndices distinctMemoryExpression
  edgeChoiceCoefficient edgeChoiceValid edgeDelta edgeForward edgeSymmetryFactor freshBigFactor
  ghostBirthCount ghostChoiceValid ghostChoiceWeight ghostReversalFactor memoryEdgeKernel
  memoryEntry memoryGhostKernel permuteActive rawEdgeValid rawEdgeWeight retrievedIndices
  smallDamping smallOmega smallTargetFactor storedMemory transferModeAccept translateMemory
  translateParticle translateSmallResidues zeroBirthBatch zeroMemoryIndices
open Erdos821.S2Core Erdos821.P3Lowrank

attribute [local instance] bmsFintype

variable {F : FixedData} {P : PrimeGroups}

theorem smallPhysical_relabel {M : ℕ} (y : P.SmallResidues) (a : P.Labels M) (g : P.BigGroup)
    (h : Fin M) (p : P.Prime g.val) :
    P.smallPhysical y (relabelLabels a g h p) ↔ P.smallPhysical y a := by
  unfold PrimeGroups.smallPhysical
  apply forall_congr'
  intro g'
  have hne : g'.val ≠ g.val := by
    intro he
    have h1' := g'.property
    have h2' := g.property
    rw [he] at h1'
    rw [h1'] at h2'
    exact Bool.false_ne_true h2'
  rw [relabelLabels_ne_group a g h p g'.val hne]

theorem tilted_prod_relabel_all (F : FixedData) (n : ℕ) {M : ℕ} (a : P.Labels M)
    (g : P.BigGroup) (h : Fin M) (p : P.Prime g.val) :
    (∏ g' : P.BigGroup, ∏ i : Fin M, tiltedMu F P n g'.val (relabelLabels a g h p g'.val i)) *
      tiltedMu F P n g.val (a g.val h) =
    (∏ g' : P.BigGroup, ∏ i : Fin M, tiltedMu F P n g'.val (a g'.val i)) *
      tiltedMu F P n g.val p := by
  let f : P.BigGroup × Fin M → ℝ := fun x => tiltedMu F P n x.1.val (a x.1.val x.2)
  have hpt : (fun x : P.BigGroup × Fin M =>
      tiltedMu F P n x.1.val (relabelLabels a g h p x.1.val x.2)) =
      Function.update f (g, h) (tiltedMu F P n g.val p) := by
    funext x
    by_cases hx : x = (g, h)
    · subst hx
      simp only [Function.update_self, relabelLabels_self]
    · rw [Function.update_of_ne hx]
      rcases x with ⟨g', i⟩
      simp only [f]
      rw [relabelLabels_of_ne a g h p g' i hx]
  have key := prod_update_mul f (g, h) (tiltedMu F P n g.val p)
  rw [← hpt] at key
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type] at key
  exact key

theorem memoryMass_relabel (F : FixedData) (J n : ℕ) (z : P.MemoryState (J + F.ell))
    (g : P.BigGroup) (h : Fin (J + F.ell)) (p : P.Prime g.val) :
    P.memoryMass F J n (relabelState g h p z) * tiltedMu F P n g.val (z.2.1 g.val h) =
      P.memoryMass F J n z * tiltedMu F P n g.val p := by
  have hiff : P.smallPhysical (relabelState g h p z).1 (relabelState g h p z).2.1 ↔
      P.smallPhysical z.1 z.2.1 := smallPhysical_relabel z.1 z.2.1 g h p
  unfold PrimeGroups.memoryMass
  split_ifs with h1 h2 h2
  · simp only [relabelState]
    have key := tilted_prod_relabel_all F n z.2.1 g h p
    calc (Fintype.card P.SmallResidues : ℝ)⁻¹ *
          (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
          (∏ g' : P.BigGroup, ∏ i, tiltedMu F P n g'.val (relabelLabels z.2.1 g h p g'.val i)) *
          (∏ g : P.BigGroup, P.groupMemoryMass F n g.val (z.2.2 g)) *
          tiltedMu F P n g.val (z.2.1 g.val h)
        = ((∏ g' : P.BigGroup, ∏ i, tiltedMu F P n g'.val (relabelLabels z.2.1 g h p g'.val i)) *
            tiltedMu F P n g.val (z.2.1 g.val h)) *
          ((Fintype.card P.SmallResidues : ℝ)⁻¹ *
            (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
            (∏ g : P.BigGroup, P.groupMemoryMass F n g.val (z.2.2 g))) := by ring
      _ = _ := by rw [key]; ring
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rw [zero_mul, zero_mul]

/-- Initial boundary term: empty memory and absolute mass. -/
def initTerm (F : FixedData) (J n : ℕ) (z : P.MemoryState (J + F.ell)) : ℝ :=
  if ∀ g, z.2.2 g = 0 then |P.memoryMass F J n z| else 0

theorem initTerm_nonneg (F : FixedData) (J n : ℕ) (z : P.MemoryState (J + F.ell)) :
    0 ≤ initTerm F J n z := by
  unfold initTerm
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

theorem init_single (F : FixedData) (J n B : ℕ)
    (hμ : ∀ (g : P.BigGroup) (p : P.Prime g.val), 0 < tiltedMu F P n g.val p)
    (hmass1 : ∀ g : P.BigGroup, 1 ≤ ∑ p : P.Prime g.val, tiltedMu F P n g.val p)
    (Q : P.MemoryState (J + F.ell) → Prop) (x : P.BigGroup × Fin (J + F.ell))
    (hQ : ∀ p z, Q (relabelState x.1 x.2 p z) ↔ Q z) (vx : ℕ) :
    ∑ z : BoundedMemoryState P (J + F.ell) B,
        (if Q z.val ∧ (z.val.2.1 x.1.val x.2).val = vx then initTerm F J n z.val else 0) ≤
      muHat F P n x.1 vx * ∑ z : BoundedMemoryState P (J + F.ell) B,
        (if Q z.val then initTerm F J n z.val else 0) := by
  rcases x with ⟨g, h⟩
  dsimp only at hQ ⊢
  have hf0 : ∀ z : BoundedMemoryState P (J + F.ell) B, 0 ≤ initTerm F J n z.val :=
    fun z => initTerm_nonneg F J n z.val
  have hR0 : 0 ≤ ∑ z : BoundedMemoryState P (J + F.ell) B,
      (if Q z.val then initTerm F J n z.val else 0) :=
    Finset.sum_nonneg fun z _ => by
      split_ifs
      · exact hf0 z
      · exact le_rfl
  have hRHS0 := mul_nonneg (muHat_nonneg F P n hμ g vx) hR0
  by_cases hvx : vx ∈ P.primes g.val
  swap
  · have hz : ∀ z : BoundedMemoryState P (J + F.ell) B,
        ¬ (Q z.val ∧ (z.val.2.1 g.val h).val = vx) := by
      rintro z ⟨-, he⟩
      exact hvx (he ▸ (z.val.2.1 g.val h).property)
    rw [Finset.sum_eq_zero fun z _ => if_neg (hz z)]
    exact hRHS0
  let α : P.Prime g.val := ⟨vx, hvx⟩
  have hmu : muHat F P n g vx = tiltedMu F P n g.val α := muHat_of_mem F P n g α
  let T := Finset.univ.filter (fun z : BoundedMemoryState P (J + F.ell) B =>
    Q z.val ∧ z.val.2.1 g.val h = α)
  let S := Finset.univ.filter (fun z : BoundedMemoryState P (J + F.ell) B => Q z.val)
  have hLHS : (∑ z : BoundedMemoryState P (J + F.ell) B,
      (if Q z.val ∧ (z.val.2.1 g.val h).val = vx then initTerm F J n z.val else 0)) =
      ∑ z ∈ T, initTerm F J n z.val := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hc : Q z.val ∧ z.val.2.1 g.val h = α
    · rw [if_pos ⟨hc.1, congrArg Subtype.val hc.2⟩, if_pos hc]
    · rw [if_neg (fun h' => hc ⟨h'.1, Subtype.ext h'.2⟩), if_neg hc]
  have hS : (∑ z : BoundedMemoryState P (J + F.ell) B,
      (if Q z.val then initTerm F J n z.val else 0)) = ∑ z ∈ S, initTerm F J n z.val :=
    (Finset.sum_filter _ _).symm
  have key := relabel_sum_le (fun z : BoundedMemoryState P (J + F.ell) B => initTerm F J n z.val)
    T S Finset.univ (fun z p => relabelB g h p z) (tiltedMu F P n g.val)
    (tiltedMu F P n g.val α) 1
    (fun z _ => hf0 z) (fun z _ => hf0 z) (hμ _ _).le one_pos (hmass1 g)
    (by
      intro z hz p _
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨Finset.mem_univ _, (hQ p z.val).mpr hz.2.1⟩)
    (by
      intro z1 hz1 p1 _ z2 hz2 p2 _ he
      have he' : relabelState g h p1 z1.val = relabelState g h p2 z2.val :=
        congrArg Subtype.val he
      have hp : p1 = p2 := by
        have h3 := congrArg (fun z : P.MemoryState (J + F.ell) => z.2.1 g.val h) he'
        change relabelLabels z1.val.2.1 g h p1 g.val h =
          relabelLabels z2.val.2.1 g h p2 g.val h at h3
        rwa [relabelLabels_self, relabelLabels_self] at h3
      refine ⟨?_, hp⟩
      apply Subtype.ext
      have h1 : z1.val.2.1 g.val h = α := (Finset.mem_filter.1 hz1).2.2
      have h2 : z2.val.2.1 g.val h = α := (Finset.mem_filter.1 hz2).2.2
      calc z1.val = relabelState g h α (relabelState g h p1 z1.val) := by
            rw [relabelState_relabel, ← h1, relabelState_eq_self]
        _ = relabelState g h α (relabelState g h p2 z2.val) := by rw [he']
        _ = z2.val := by rw [relabelState_relabel, ← h2, relabelState_eq_self])
    (by
      intro z hz p _
      have hlab : z.val.2.1 g.val h = α := (Finset.mem_filter.1 hz).2.2
      change initTerm F J n z.val * tiltedMu F P n g.val p =
        initTerm F J n (relabelState g h p z.val) * tiltedMu F P n g.val α
      unfold initTerm
      by_cases hem : ∀ g', z.val.2.2 g' = 0
      · have hem' : ∀ g', (relabelState g h p z.val).2.2 g' = 0 := hem
        rw [if_pos hem, if_pos hem']
        have hM := congrArg abs (memoryMass_relabel F J n z.val g h p)
        rw [abs_mul, abs_mul, abs_of_pos (hμ _ _), abs_of_pos (hμ _ _), hlab] at hM
        exact hM.symm
      · have hem' : ¬ ∀ g', (relabelState g h p z.val).2.2 g' = 0 := hem
        rw [if_neg hem, if_neg hem', zero_mul, zero_mul])
  rw [hLHS, hS, hmu]
  calc _ ≤ tiltedMu F P n g.val α / 1 * ∑ z ∈ S, initTerm F J n z.val := key
    _ = _ := by ring

theorem init_slots (F : FixedData) (J n B : ℕ)
    (hμ : ∀ (g : P.BigGroup) (p : P.Prime g.val), 0 < tiltedMu F P n g.val p)
    (hmass1 : ∀ g : P.BigGroup, 1 ≤ ∑ p : P.Prime g.val, tiltedMu F P n g.val p)
    (vals : P.BigGroup × Fin (J + F.ell) → ℕ) :
    ∀ Sl : Finset (P.BigGroup × Fin (J + F.ell)),
    ∑ z : BoundedMemoryState P (J + F.ell) B,
        (if ∀ x ∈ Sl, (z.val.2.1 x.1.val x.2).val = vals x then initTerm F J n z.val else 0) ≤
      (∏ x ∈ Sl, muHat F P n x.1 (vals x)) *
        ∑ z : BoundedMemoryState P (J + F.ell) B, initTerm F J n z.val := by
  intro Sl
  induction Sl using Finset.induction_on with
  | empty => simp
  | insert y S hy ih =>
      have hrw : ∀ z : BoundedMemoryState P (J + F.ell) B,
          (if ∀ x ∈ insert y S, (z.val.2.1 x.1.val x.2).val = vals x
            then initTerm F J n z.val else 0) =
          (if (∀ x ∈ S, (z.val.2.1 x.1.val x.2).val = vals x) ∧
              (z.val.2.1 y.1.val y.2).val = vals y
            then initTerm F J n z.val else 0) := by
        intro z
        by_cases h1 : ∀ x ∈ insert y S, (z.val.2.1 x.1.val x.2).val = vals x
        · rw [if_pos h1, if_pos ⟨fun x hx => h1 x (Finset.mem_insert_of_mem hx),
            h1 y (Finset.mem_insert_self y S)⟩]
        · rw [if_neg h1, if_neg]
          rintro ⟨h2, h3⟩
          apply h1
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact h3
          · exact h2 x hx
      rw [Finset.sum_congr rfl (fun z _ => hrw z)]
      have hQ : ∀ (p : P.Prime y.1.val) (z : P.MemoryState (J + F.ell)),
          (∀ x ∈ S, ((relabelState y.1 y.2 p z).2.1 x.1.val x.2).val = vals x) ↔
            (∀ x ∈ S, (z.2.1 x.1.val x.2).val = vals x) := by
        intro p z
        have hx : ∀ x ∈ S, ((relabelState y.1 y.2 p z).2.1 x.1.val x.2).val = vals x ↔
            (z.2.1 x.1.val x.2).val = vals x := by
          intro x hxS
          have hne : (x.1, x.2) ≠ (y.1, y.2) := by
            rw [Prod.mk.eta, Prod.mk.eta]
            rintro rfl
            exact hy hxS
          change (relabelLabels z.2.1 y.1 y.2 p x.1.val x.2).val = vals x ↔ _
          rw [relabelLabels_of_ne _ y.1 y.2 p x.1 x.2 hne]
        exact ⟨fun h x hxS => (hx x hxS).mp (h x hxS), fun h x hxS => (hx x hxS).mpr (h x hxS)⟩
      have hstep := init_single F J n B hμ hmass1
        (fun z => ∀ x ∈ S, (z.2.1 x.1.val x.2).val = vals x) y hQ (vals y)
      have hm0 : 0 ≤ muHat F P n y.1 (vals y) := muHat_nonneg F P n hμ _ _
      calc _ ≤ muHat F P n y.1 (vals y) * ∑ z : BoundedMemoryState P (J + F.ell) B,
              (if ∀ x ∈ S, (z.val.2.1 x.1.val x.2).val = vals x
                then initTerm F J n z.val else 0) := by
            convert hstep
        _ ≤ muHat F P n y.1 (vals y) * ((∏ x ∈ S, muHat F P n x.1 (vals x)) *
              ∑ z : BoundedMemoryState P (J + F.ell) B, initTerm F J n z.val) :=
            mul_le_mul_of_nonneg_left ih hm0
        _ = _ := by rw [Finset.prod_insert hy]; ring

theorem initTerm_sum_le {J m : ℕ} (A : Model F P J m) (n B : ℕ) :
    ∑ z : BoundedMemoryState P (J + F.ell) B, initTerm F J n z.val ≤
      initialMemoryBoundaryMass A n := by
  let T := (Finset.univ.filter (fun s : BoundedMemoryState P (J + F.ell) B =>
    ∀ g, s.val.2.2 g = 0)).map (Function.Embedding.subtype _)
  calc ∑ z : BoundedMemoryState P (J + F.ell) B, initTerm F J n z.val
      = ∑ s ∈ Finset.univ.filter (fun s : BoundedMemoryState P (J + F.ell) B =>
          ∀ g, s.val.2.2 g = 0), |P.memoryMass F J n s.val| := by
        rw [Finset.sum_filter]
        rfl
    _ = ∑ x ∈ T, |P.memoryMass F J n x| := by
        simp only [T, Finset.sum_map, Function.Embedding.coe_subtype]
    _ ≤ _ := by
        apply Erdos821.P3Tail.start_sum_le A n T
        intro x hx
        simp only [T, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coe_subtype] at hx
        obtain ⟨s, hs, rfl⟩ := hx
        exact hs

end Erdos821.P3High
