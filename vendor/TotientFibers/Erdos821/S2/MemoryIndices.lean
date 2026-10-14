import Erdos821.S2.HistorySizes

/-! Index multiplicities and zero counts used for local damping cancellation. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

theorem memoryEntry_enumeration {g : P.Group} (z : P.Memory g) :
    (Finset.univ : Finset (Fin z.card)).val.map (memoryEntry z) = z := by
  let v : List.Vector (P.Particle g) z.card := ⟨z.toList, Multiset.length_toList z⟩
  have he : memoryEntry z = v.get := by funext i; rfl
  have hl : List.ofFn (memoryEntry z) = z.toList := by
    rw [he, ← List.Vector.toList_ofFn, List.Vector.ofFn_get]
    rfl
  rw [Finset.val_univ_fin, Multiset.map_coe, ← List.ofFn_eq_map, hl, Multiset.coe_toList]

theorem deleteMemoryIndices_eq_map {g : P.Group} (z : P.Memory g)
    (B : Finset (Fin z.card)) :
    deleteMemoryIndices z B = (Finset.univ \ B).val.map (memoryEntry z) := by
  simp only [deleteMemoryIndices, ← Multiset.map_coe, Finset.coe_toList]

theorem zeroMemoryIndices_card {g : P.Group} (z : P.Memory g) :
    (zeroMemoryIndices z).card = (z.filter (fun u => u.2 = 0)).card := by
  calc
    _ = (((Finset.univ : Finset (Fin z.card)).val.map (memoryEntry z)).filter
        (fun u => u.2 = 0)).card := by
      simp only [Multiset.filter_map, Multiset.card_map]
      rfl
    _ = _ := by rw [memoryEntry_enumeration]

theorem zeroMemoryIndices_delete_card {g : P.Group} (z : P.Memory g)
    (B : Finset (Fin z.card)) (hB : B ⊆ zeroMemoryIndices z) :
    (zeroMemoryIndices (deleteMemoryIndices z B)).card =
      (zeroMemoryIndices z).card - B.card := by
  rw [zeroMemoryIndices_card, deleteMemoryIndices_eq_map,
    Multiset.filter_map, Multiset.card_map]
  have he : (Finset.univ \ B).filter (fun i => (memoryEntry z i).2 = 0) =
      zeroMemoryIndices z \ B := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, zeroMemoryIndices]
    tauto
  change ((Finset.univ \ B).filter (fun i => (memoryEntry z i).2 = 0)).card = _
  rw [he, Finset.card_sdiff_of_subset hB]

theorem zeroMemoryIndices_add_card {g : P.Group} (z w : P.Memory g) :
    (zeroMemoryIndices (z + w)).card = (zeroMemoryIndices z).card + (zeroMemoryIndices w).card := by
  simp only [zeroMemoryIndices_card, Multiset.filter_add, Multiset.card_add]

theorem zeroMemoryIndices_birth_card {g : P.Group} {b : ℕ} (p : Fin b → P.Prime g) :
    (zeroMemoryIndices (zeroBirthBatch p)).card = b := by
  rw [zeroMemoryIndices_card]
  have he : (zeroBirthBatch p).filter (fun u => u.2 = 0) = zeroBirthBatch p := by
    apply Multiset.filter_eq_self.mpr
    intro u hu
    unfold zeroBirthBatch at hu
    simp only [Multiset.mem_coe, List.mem_ofFn] at hu
    obtain ⟨i, rfl⟩ := hu
    rfl
  rw [he, zeroBirthBatch_card]

theorem ghostChoiceValid_zero_card {M : ℕ} {s t : P.MemoryState M}
    (c : GhostChoice s t) (hc : ghostChoiceValid c) (g : P.BigGroup) :
    (zeroMemoryIndices (t.2.2 g)).card =
      (zeroMemoryIndices (s.2.2 g)).card - (c.1 g).card + (c.2.1 g).val := by
  have he := congrArg (fun z => (zeroMemoryIndices z).card) (hc g).2
  simpa only [zeroMemoryIndices_add_card,
    zeroMemoryIndices_delete_card _ _ (hc g).1, zeroMemoryIndices_birth_card] using he.symm

/-- Local rho factors cancel exactly, including old zero multiplicities. -/
theorem local_rho_cancellation (rho q eta V : ℝ) (hρ : rho ≠ 0)
    (Z t b : ℕ) (ht : t ≤ Z) :
    rho ^ Z * (-eta / rho) ^ t * (q / rho ^ (2 : ℕ)) ^ (Z - t) *
      (-eta * V / rho) ^ b * rho ^ (Z - t + b) =
      (-eta) ^ t * q ^ (Z - t) * (-eta * V) ^ b := by
  have hZ : Z = (Z - t) + t := (Nat.sub_add_cancel ht).symm
  rw [show rho ^ Z = rho ^ (Z - t) * rho ^ t by rw [← pow_add, ← hZ]]
  simp only [div_pow, pow_mul, pow_add]
  field_simp [hρ]
  ring

/-- The incoming and outgoing edge damping cancels the ghost normalization. -/
theorem ghostChoiceWeight_rho_cancel (F : FixedData) (n : ℕ) (rho : ℝ) (hρ : rho ≠ 0)
    (i : Fin (n + 1)) {M : ℕ} {s t : P.MemoryState M} (c : GhostChoice s t)
    (hc : ghostChoiceValid c) :
    rho ^ (∑ g : P.BigGroup, (zeroMemoryIndices (s.2.2 g)).card) *
      ghostChoiceWeight F n rho i c *
      rho ^ (∑ g : P.BigGroup, (zeroMemoryIndices (t.2.2 g)).card) =
        ghostChoiceWeight F n 1 i c := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  simp only [ghostChoiceWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  have hn := congrArg (fun Z => rho ^ Z) (ghostChoiceValid_zero_card c hc g)
  have ht : (c.1 g).card ≤ (zeroMemoryIndices (s.2.2 g)).card := Finset.card_le_card (hc g).1
  simp only [div_one, one_pow]
  calc
    _ = (rho ^ (zeroMemoryIndices (s.2.2 g)).card * (-eta F n i / rho) ^ (c.1 g).card *
        (visitQ F.q n i / rho ^ (2 : ℕ)) ^ ((zeroMemoryIndices (s.2.2 g)).card - (c.1 g).card) *
        (-eta F n i * P.V g.val / rho) ^ (c.2.1 g).val *
        rho ^ ((zeroMemoryIndices (t.2.2 g)).card)) *
        (((c.2.1 g).val.factorial : ℝ)⁻¹ *
          ∏ h : Fin (c.2.1 g).val, tiltedMu F P n g.val (c.2.2 g h)) := by ring
    _ = _ := by
      rw [hn, local_rho_cancellation rho (visitQ F.q n i) (eta F n i) (P.V g.val) hρ _ _ _ ht]
      ring


end Erdos821.S2Core
