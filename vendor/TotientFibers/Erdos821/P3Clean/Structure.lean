import Erdos821.S2.EdgeTasks

/-! The literal clean mask and the diagonal memory translation. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {P : PrimeGroups} {F : FixedData} {J m : ℕ}

def emptyTransfer {M : ℕ} (s : P.MemoryState M) : TransferChoice s :=
  ⟨fun _ => ∅, ⟨fun _ => ∅,
    fun _ (i : {i : Fin M // i ∈ (∅ : Finset (Fin M))}) =>
      False.elim (Finset.notMem_empty i.val i.property)⟩⟩

theorem clean_transfer_iff {M : ℕ} {s : P.MemoryState M} (c : TransferChoice s) :
    transferModeAccept .clean c ↔ c = emptyTransfer s := by
  constructor
  · intro h
    rcases c with ⟨B, A, f⟩
    have hB : B = fun _ => ∅ := funext (fun g => (h g).1)
    have hA : A = fun _ => ∅ := funext (fun g => (h g).2)
    subst B A
    congr 2
    funext g i
    exact False.elim (Finset.notMem_empty i.val i.property)
  · rintro rfl
    exact fun _ => ⟨rfl, rfl⟩

theorem sum_clean_transfer {M : ℕ} (s : P.MemoryState M)
    (h : TransferChoice s → Prop) (f : TransferChoice s → ℂ) :
    (∑ c : TransferChoice s, if h c ∧ transferModeAccept .clean c then f c else 0) =
      if h (emptyTransfer s) then f (emptyTransfer s) else 0 := by
  classical
  simp_rw [clean_transfer_iff]
  rw [Finset.sum_eq_single (emptyTransfer s)]
  · simp
  · intro c _ hc
    simp [hc]
  · simp

def cleanEdgeKernel (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) : ℂ :=
  (edgeSymmetryFactor P (J + F.ell) : ℂ) *
    ∑ π : P.Permutations (J + F.ell), ∑ τ : P.Permutations (J + F.ell),
      ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
        if rawEdgeValid A (A.pattern v) (edgeForward i) u
            (permuteActive π s) (permuteActive τ t) (emptyTransfer s) then
          edgeChoiceCoefficient A n rho theta i s t ⟨π, τ, v, u, emptyTransfer s⟩
        else 0

theorem memoryEdgeKernel_clean (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (i : Fin n) (s t : P.MemoryState (J + F.ell)) :
    memoryEdgeKernel A n rho theta i .clean (fun _ _ _ => 1) s t =
      cleanEdgeKernel A n rho theta i s t := by
  classical
  unfold memoryEdgeKernel cleanEdgeKernel
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro π _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  simp only [edgeChoiceValid, mul_one]
  exact sum_clean_transfer s _ _

theorem deleteMemoryIndices_empty {g : P.Group} (z : P.Memory g) :
    deleteMemoryIndices z ∅ = z := by
  classical
  simp only [deleteMemoryIndices, Finset.sdiff_empty]
  rw [← Multiset.map_coe, Finset.coe_toList, Fin.univ_val_map]
  unfold memoryEntry
  have h (l : List (P.Particle g)) (n : ℕ) (hn : l.length = n) :
      List.ofFn (fun i : Fin n => l.get ⟨i.val, by omega⟩) = l := by
    subst n
    exact List.ofFn_get l
  rw [h z.toList z.card (Multiset.length_toList z), Multiset.coe_toList]

theorem retrievedIndices_empty {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup) :
    retrievedIndices (emptyTransfer s) g = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨j, _, _⟩ := Finset.mem_image.mp hi
  exact False.elim (Finset.notMem_empty j.val j.property)

theorem storedMemory_empty {M : ℕ} {g : P.Group} (a : Fin M → P.Prime g) :
    storedMemory a ∅ = 0 := by simp [storedMemory]

theorem rawEdgeValid_empty (A : Model F P J m) (ν : Pattern P J F.ell m)
    (forward : Bool) (u : P.Aux J) (s t : P.MemoryState (J + F.ell)) :
    rawEdgeValid A ν forward u s t (emptyTransfer s) ↔
      P.smallPhysical s.1 s.2.1 ∧ P.smallPhysical t.1 t.2.1 ∧
      ν.compatible s.2.1 t.2.1 ∧ ν.ban s.2.1 t.2.1 u ∧
      t.1 = translateSmallResidues (edgeDelta A ν forward s.2.1 u) s.1 ∧
      ∀ g : P.BigGroup,
        t.2.2 g = translateMemory (edgeDelta A ν forward s.2.1 u) (s.2.2 g) := by
  classical
  unfold rawEdgeValid
  have hr (g : P.BigGroup) : retrievedIndices (emptyTransfer s) g = ∅ :=
    retrievedIndices_empty s g
  simp only [hr]
  simp [emptyTransfer, storedMemory_empty, deleteMemoryIndices_empty, Function.Injective]

theorem clean_memory_card (A : Model F P J m) (ν : Pattern P J F.ell m)
    (forward : Bool) (u : P.Aux J) (s t : P.MemoryState (J + F.ell))
    (c : TransferChoice s) (hv : rawEdgeValid A ν forward u s t c)
    (hc : transferModeAccept .clean c) (g : P.BigGroup) :
    (t.2.2 g).card = (s.2.2 g).card := by
  rw [rawEdgeValid_memory_card A ν forward u s t c hv g, (hc g).1, (hc g).2]
  simp

theorem clean_memory_size (A : Model F P J m) (n : ℕ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s)
    (hc : edgeChoiceValid A .clean i s t c) : P.memorySize t = P.memorySize s := by
  apply Finset.sum_congr rfl
  intro g _
  exact clean_memory_card A _ _ _ (permuteActive c.1 s) (permuteActive c.2.1 t)
    c.2.2.2.2 hc.1 hc.2 g

theorem clean_kernel_eq_zero_of_memory_size_ne (A : Model F P J m)
    (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (s t : P.MemoryState (J + F.ell)) (h : P.memorySize t ≠ P.memorySize s) :
    memoryEdgeKernel A n rho theta i .clean phi s t = 0 := by
  classical
  unfold memoryEdgeKernel
  have hzero : (∑ c : EdgeChoice A s,
      if edgeChoiceValid A .clean i s t c then
        edgeChoiceCoefficient A n rho theta i s t c * phi s t c else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    exact if_neg (fun hc => h (clean_memory_size A n i s t c hc))
  rw [hzero, mul_zero]

def particleTranslation (delta : ℤ) (g : P.Group) : P.Particle g ≃ P.Particle g where
  toFun := translateParticle delta
  invFun := translateParticle (-delta)
  left_inv := by
    intro z
    rcases z with ⟨p, r⟩
    simp only [translateParticle]
    congr 1
    change r + (delta : ZMod p.val) + ((-delta : ℤ) : ZMod p.val) = r
    simp
  right_inv := by
    intro z
    rcases z with ⟨p, r⟩
    simp only [translateParticle]
    congr 1
    change r + ((-delta : ℤ) : ZMod p.val) + (delta : ZMod p.val) = r
    simp

theorem translateMemory_groupMass (F : FixedData) (n : ℕ) (delta : ℤ)
    (g : P.Group) (z : P.Memory g) :
    P.groupMemoryMass F n g (translateMemory delta z) = P.groupMemoryMass F n g z := by
  classical
  have hinj : Function.Injective (translateParticle (P := P) delta (g := g)) :=
    (particleTranslation delta g).injective
  unfold PrimeGroups.groupMemoryMass translateMemory
  simp only [Multiset.map_map]
  congr 1
  rw [Multiset.toFinset_map, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro u _
    rw [Multiset.count_map_eq_count' _ _ hinj]
  · intro a _ b _ h
    exact hinj h


end Erdos821.P3Clean
