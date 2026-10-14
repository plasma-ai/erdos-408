import Erdos821.P3Edge.SmallFibres
import Erdos821.P3Edge.PromoBound
import Erdos821.P3Edge.LargeX
import Erdos821.S2.MemoryIndices

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- Translated-zero indices in one big group (source memory with `+delta = 0`). -/
def transZeroSet {g : P.BigGroup} (z : P.Memory g.val) (delta : ℤ) :
    Finset (Fin z.card) :=
  Finset.univ.filter (fun i => (memoryEntry z i).2 + (delta : ZMod (memoryEntry z i).1.val) = 0)

/-- Deleting a subset `R` of indices and adding `w` leaves at least
`(transZeroSet z delta).card - R.card` zero-residue particles after translation by `delta`. -/
lemma zeroMemoryIndices_translate_delete_add_ge {g : P.BigGroup}
    (z : P.Memory g.val) (delta : ℤ) (R : Finset (Fin z.card)) (w : P.Memory g.val) :
    (transZeroSet z delta).card - R.card ≤
      (zeroMemoryIndices (translateMemory delta (deleteMemoryIndices z R + w))).card := by
  classical
  have hmap_add : translateMemory delta (deleteMemoryIndices z R + w) =
      translateMemory delta (deleteMemoryIndices z R) + translateMemory delta w := by
    unfold translateMemory
    exact Multiset.map_add _ _ _
  rw [hmap_add, zeroMemoryIndices_add_card]
  have hdel : (zeroMemoryIndices (translateMemory delta (deleteMemoryIndices z R))).card =
      ((transZeroSet z delta) \ R).card := by
    rw [zeroMemoryIndices_card]
    unfold translateMemory
    rw [deleteMemoryIndices_eq_map, Multiset.map_map, Multiset.filter_map, Multiset.card_map]
    have hfilt : (Finset.univ \ R).filter
        (fun i : Fin z.card => (translateParticle delta (memoryEntry z i)).2 = 0) =
        (transZeroSet z delta) \ R := by
      ext i
      unfold transZeroSet translateParticle
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    change ((Finset.univ \ R).filter
      (fun i : Fin z.card => (translateParticle delta (memoryEntry z i)).2 = 0)).card = _
    rw [hfilt]
  have hsdiff : (transZeroSet z delta).card - R.card ≤ ((transZeroSet z delta) \ R).card :=
    Finset.le_card_sdiff R (transZeroSet z delta)
  omega

/-- Target zero-memory damping is bounded by `rho ^ ((transZeroSet z delta).card - A_g.card)`
for any retrieval map `f_g : {idx // idx ∈ A_g} → Fin z.card`. -/
lemma target_rho_pow_le {g : P.BigGroup} (r : MemoryParameters F)
    (z : P.Memory g.val) (delta : ℤ) (A_g : Finset (Fin (J + F.ell)))
    (f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z.card) (w : P.Memory g.val) :
    r.rho ^ (zeroMemoryIndices (translateMemory delta
      (deleteMemoryIndices z (Finset.univ.image f_g) + w))).card ≤
      r.rho ^ ((transZeroSet z delta).card - A_g.card) := by
  have hcard_img : (Finset.univ.image f_g).card ≤ A_g.card := by
    calc (Finset.univ.image f_g).card
        ≤ (Finset.univ : Finset {idx : Fin (J + F.ell) // idx ∈ A_g}).card :=
          Finset.card_image_le
      _ = A_g.card := by simp
  have hge : (transZeroSet z delta).card - A_g.card ≤
      (zeroMemoryIndices (translateMemory delta
        (deleteMemoryIndices z (Finset.univ.image f_g) + w))).card := by
    have h1 := zeroMemoryIndices_translate_delete_add_ge z delta (Finset.univ.image f_g) w
    omega
  exact pow_le_pow_of_le_one r.rho_pos.le r.rho_lt.le hge

/-- Fresh sums over arbitrary finite index. -/
lemma fresh_sum_eq_card {α : Type*} [Fintype α] [DecidableEq α]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (w : α → ℝ) :
    ∑ a : ι → α, ∏ i, w (a i) = (∑ a, w a) ^ (Fintype.card ι) := by
  classical
  have h1 := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset α))
    (fun _ : ι => fun a : α => w a)
  have lhs : (∏ _i : ι, ∑ _j : α, w _j) = (∑ a, w a) ^ (Fintype.card ι) := by
    rw [Finset.prod_const, Finset.card_univ]
  have rhs : (∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset α)), ∏ i, w (x i))
      = ∑ a : ι → α, ∏ i, w (a i) := by
    rw [Fintype.piFinset_univ]
  have h1' : (∏ _i : ι, ∑ _j : α, w _j)
      = (∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset α)), ∏ i, w (x i)) := h1
  rw [lhs, rhs] at h1'
  exact h1'.symm

/-- Summing a product over functions `b : ι → α` constrained to equal `b₀` on `{i | P i}`
and weighted by `w (b i)` on `{i | ¬ P i}` yields `(∑ a, w a) ^ card {i // ¬ P i}`. -/
lemma sum_fixed_outside_eq {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (Q : ι → Prop) [DecidablePred Q] (b₀ : ι → α) (w : α → ℝ) :
    (∑ b : ι → α, if (∀ i, Q i → b i = b₀ i) then (∏ i : ι, if Q i then 1 else w (b i)) else 0) =
      (∑ a : α, w a) ^ (Fintype.card {i : ι // ¬ Q i}) := by
  classical
  rw [← fresh_sum_eq_card {i : ι // ¬ Q i} w, ← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun (φ : {i : ι // ¬ Q i} → α) _ =>
    fun i : ι => if h : Q i then b₀ i else φ ⟨i, h⟩)
  · intro φ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    exact dif_pos hi
  · intro φ₁ _ φ₂ _ h
    funext j
    have hj := congrArg (fun f : ι → α => f j.val) h
    simpa [dif_neg j.property] using hj
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨fun j => b j.val, Finset.mem_univ _, ?_⟩
    funext i
    by_cases hi : Q i
    · rw [dif_pos hi, hb i hi]
    · rw [dif_neg hi]
  · intro φ _
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
    apply Finset.prod_bij (fun (j : {i : ι // ¬ Q i}) _ => j.val)
    · intro j _
      simp [j.property]
    · intro j₁ _ j₂ _ h
      exact Subtype.ext h
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
    · intro j _
      simp [dif_neg j.property]

/-- Row per-entry weight ratio from Schur weights (big groups only). -/
lemma weight_ratio_le (r : MemoryParameters F)
    (a b : ℕ) (_ha : a ≤ F.ell + m) (hb : b ≤ F.ell + m) :
    (r.v ^ b / r.v ^ a) ≤ r.v ^ (F.ell + m) := by
  have hv : 1 < r.v := r.v_gt
  have hpos : 0 < r.v ^ a := pow_pos (lt_trans zero_lt_one hv) _
  calc r.v ^ b / r.v ^ a ≤ r.v ^ b := by
        rw [div_le_iff₀ hpos]
        have h1 : r.v ^ b ≤ r.v ^ b * r.v ^ a := by
          have ha1 : 1 ≤ r.v ^ a := one_le_pow₀ hv.le
          calc r.v ^ b = r.v ^ b * 1 := (mul_one _).symm
            _ ≤ r.v ^ b * r.v ^ a :=
              mul_le_mul_of_nonneg_left ha1 (pow_nonneg (le_of_lt (lt_trans zero_lt_one hv)) _)
        linarith [h1]
    _ ≤ r.v ^ (F.ell + m) := pow_le_pow_right₀ hv.le hb

/-- Per-big-group constant (≥1, J-independent) combining transfer counts,
promo sup, V powers, Schur weight, fresh mass. -/
def bigGroupConst (F : FixedData) (r : MemoryParameters F) (m : ℕ)
    (Cprom : ℝ) : ℝ :=
  max 1 ((4 : ℝ) ^ (F.ell + m) * max 1 Cprom *
    max 1 (max ((F.vMax) ^ (F.ell + m)) ((F.vMin⁻¹) ^ (F.ell + m))) *
    (r.v ^ (F.ell + m)) * ((2 : ℝ) ^ (F.ell + m)))

lemma bigGroupConst_ge_one (F : FixedData) (r : MemoryParameters F) (m : ℕ)
    (Cprom : ℝ) : 1 ≤ bigGroupConst F r m Cprom := le_max_left _ _

lemma bigGroupConst_pos (F : FixedData) (r : MemoryParameters F) (m : ℕ)
    (Cprom : ℝ) : 0 < bigGroupConst F r m Cprom :=
  lt_of_lt_of_le zero_lt_one (bigGroupConst_ge_one F r m Cprom)

/-- Relaxed per-big-group validity predicate for row summation. -/
def bigGroupValid (ν : Pattern P J F.ell m) (delta : ℤ) (g : P.BigGroup)
    (a_g : Fin (J + F.ell) → P.Prime g.val) (z_g : P.Memory g.val)
    (B_g A_g : Finset (Fin (J + F.ell)))
    (f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card)
    (b_g : Fin (J + F.ell) → P.Prime g.val) : Prop :=
  (∀ idx ∈ B_g, ¬ ν.shared g.val idx) ∧
  (∀ idx ∈ A_g, ¬ ν.shared g.val idx) ∧
  (∀ j : Fin J, j ∉ ν.changed g.val → b_g (ν.slot j) = a_g (ν.slot j)) ∧
  (∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g},
    (memoryEntry z_g (f_g idx)).1 = b_g idx.val ∧
    (memoryEntry z_g (f_g idx)).2 + (delta : ZMod (memoryEntry z_g (f_g idx)).1.val) = 0)

/-- Per-big-group weight factor in the row sum. -/
def bigGroupWeight (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (ν : Pattern P J F.ell m) (delta : ℤ) (g : P.BigGroup)
    (a_g : Fin (J + F.ell) → P.Prime g.val) (z_g : P.Memory g.val)
    (B_g A_g : Finset (Fin (J + F.ell)))
    (f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card)
    (b_g : Fin (J + F.ell) → P.Prime g.val) : ℝ :=
  (∏ idx : Fin (J + F.ell),
    if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx)) *
  (P.V g.val) ^ (-(A_g.card : ℤ)) *
  r.rho ^ (zeroMemoryIndices (translateMemory delta
    (deleteMemoryIndices z_g (Finset.univ.image f_g) + storedMemory a_g B_g))).card *
  (r.v ^ B_g.card / r.v ^ A_g.card)

lemma bigGroupWeight_nonneg (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (ν : Pattern P J F.ell m) (delta : ℤ) (g : P.BigGroup)
    (hV : 0 < P.V g.val) (htilted : ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (a_g : Fin (J + F.ell) → P.Prime g.val) (z_g : P.Memory g.val)
    (B_g A_g : Finset (Fin (J + F.ell)))
    (f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card)
    (b_g : Fin (J + F.ell) → P.Prime g.val) :
    0 ≤ bigGroupWeight F r n ν delta g a_g z_g B_g A_g f_g b_g := by
  unfold bigGroupWeight
  have hvpos : 0 < r.v := lt_trans zero_lt_one r.v_gt
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · apply Finset.prod_nonneg
        intro idx _
        split_ifs
        · exact zero_le_one
        · exact htilted _
      · exact zpow_nonneg hV.le _
    · exact pow_nonneg r.rho_pos.le _
  · exact div_nonneg (pow_nonneg hvpos.le _) (pow_nonneg hvpos.le _)

/-- Sum of `freshBigFactor` over target labels `b_g` for fixed `(B_g, A_g, f_g)` is at most
`2 ^ (F.ell + m)`. -/
lemma bigGroup_label_sum_le (F : FixedData) (n : ℕ)
    (ν : Pattern P J F.ell m) (delta : ℤ) (g : P.BigGroup)
    (htilted_nn : ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (htilted_sum : ∑ p : P.Prime g.val, tiltedMu F P n g.val p ≤ 2)
    (a_g : Fin (J + F.ell) → P.Prime g.val) (z_g : P.Memory g.val)
    (B_g A_g : Finset (Fin (J + F.ell)))
    (f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card) :
    (∑ b_g : Fin (J + F.ell) → P.Prime g.val,
      if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
        (∏ idx : Fin (J + F.ell),
          if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx))
      else 0) ≤
    if (∀ idx ∈ B_g, ¬ ν.shared g.val idx) ∧
       (∀ idx ∈ A_g, ¬ ν.shared g.val idx) ∧
       (∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g}, f_g idx ∈ transZeroSet z_g delta)
    then (2 : ℝ) ^ (F.ell + m) else 0 := by
  classical
  by_cases hcond : (∀ idx ∈ B_g, ¬ ν.shared g.val idx) ∧
      (∀ idx ∈ A_g, ¬ ν.shared g.val idx) ∧
      (∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g}, f_g idx ∈ transZeroSet z_g delta)
  · rw [if_pos hcond]
    obtain ⟨hB, hA, hzero⟩ := hcond
    let Q : Fin (J + F.ell) → Prop := fun idx => ν.shared g.val idx ∨ idx ∈ A_g
    let b₀ : Fin (J + F.ell) → P.Prime g.val :=
      fun idx => if h : idx ∈ A_g then (memoryEntry z_g (f_g ⟨idx, h⟩)).1 else a_g idx
    have hle : (∑ b_g : Fin (J + F.ell) → P.Prime g.val,
        if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
          (∏ idx : Fin (J + F.ell),
            if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx))
        else 0) ≤
        ∑ b_g : Fin (J + F.ell) → P.Prime g.val,
          if (∀ idx, Q idx → b_g idx = b₀ idx) then
            (∏ idx : Fin (J + F.ell),
              if Q idx then 1 else tiltedMu F P n g.val (b_g idx))
          else 0 := by
      apply Finset.sum_le_sum
      intro b_g _
      by_cases hval : bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g
      · have hfix : ∀ idx, Q idx → b_g idx = b₀ idx := by
          intro idx hQ
          rcases hQ with hsh | hmem
          · have hnotA : idx ∉ A_g := fun hm => hA idx hm hsh
            simp only [b₀, dif_neg hnotA]
            obtain ⟨j, rfl, hj⟩ := hsh
            exact hval.2.2.1 j hj
          · simp only [b₀, dif_pos hmem]
            exact (hval.2.2.2 ⟨idx, hmem⟩).1.symm
        rw [if_pos hval, if_pos hfix]
      · rw [if_neg hval]
        split_ifs
        · apply Finset.prod_nonneg
          intro idx _
          split_ifs
          · exact zero_le_one
          · exact htilted_nn _
        · exact le_refl 0
    have heq := sum_fixed_outside_eq Q b₀ (fun p => tiltedMu F P n g.val p)
    have hcard_le : Fintype.card {idx : Fin (J + F.ell) // ¬ Q idx} ≤ F.ell + m := by
      have hsub : Finset.univ.filter (fun idx : Fin (J + F.ell) => ¬ Q idx) ⊆
          Finset.univ.filter (fun idx : Fin (J + F.ell) => ¬ ν.shared g.val idx) := by
        intro idx hidx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Q, not_or] at hidx ⊢
        exact hidx.1
      have h1 : Fintype.card {idx : Fin (J + F.ell) // ¬ Q idx} =
          (Finset.univ.filter (fun idx : Fin (J + F.ell) => ¬ Q idx)).card :=
        Fintype.card_subtype _
      have h2 := Finset.card_le_card hsub
      have h3 := nonshared_card_le ν g.val
      have h4 : (ν.changed g.val).card ≤ m := ν.bound g.val
      unfold Pattern.t at h3
      omega
    have hsum_nn : 0 ≤ ∑ p : P.Prime g.val, tiltedMu F P n g.val p :=
      Finset.sum_nonneg (fun p _ => htilted_nn p)
    calc (∑ b_g : Fin (J + F.ell) → P.Prime g.val,
          if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
            (∏ idx : Fin (J + F.ell),
              if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx))
          else 0)
        ≤ (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ^
            (Fintype.card {idx : Fin (J + F.ell) // ¬ Q idx}) := by
          rw [← heq]
          convert hle using 3
      _ ≤ (2 : ℝ) ^ (Fintype.card {idx : Fin (J + F.ell) // ¬ Q idx}) :=
          pow_le_pow_left₀ hsum_nn htilted_sum _
      _ ≤ (2 : ℝ) ^ (F.ell + m) :=
          pow_le_pow_right₀ (by norm_num) hcard_le
  · rw [if_neg hcond]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro b_g _
    rw [if_neg]
    intro hval
    apply hcond
    refine ⟨hval.1, hval.2.1, fun idx => ?_⟩
    simp only [transZeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hval.2.2.2 idx).2

/-- Sum over retrieval maps `f_g` of the target zero-damping is bounded by `max 1 Cprom`. -/
lemma bigGroup_retrieval_sum_le (r : MemoryParameters F) (m : ℕ)
    (Cprom : ℝ) (hCprom : ∀ Z' a : ℕ, a ≤ F.ell + m → (Z' : ℝ) ^ a * r.rho ^ (Z' - a) ≤ Cprom)
    (ν : Pattern P J F.ell m) (delta : ℤ) (g : P.BigGroup)
    (a_g : Fin (J + F.ell) → P.Prime g.val) (z_g : P.Memory g.val)
    (B_g A_g : Finset (Fin (J + F.ell))) (hA : ∀ idx ∈ A_g, ¬ ν.shared g.val idx) :
    (∑ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card,
      if (∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g}, f_g idx ∈ transZeroSet z_g delta) then
        r.rho ^ (zeroMemoryIndices (translateMemory delta
          (deleteMemoryIndices z_g (Finset.univ.image f_g) + storedMemory a_g B_g))).card
      else 0) ≤ max 1 Cprom := by
  classical
  set Z' := (transZeroSet z_g delta).card
  have hle_const : (∑ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card,
      if (∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g}, f_g idx ∈ transZeroSet z_g delta) then
        r.rho ^ (zeroMemoryIndices (translateMemory delta
          (deleteMemoryIndices z_g (Finset.univ.image f_g) + storedMemory a_g B_g))).card
      else 0) ≤
      ∑ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card,
        if f_g ∈ Fintype.piFinset (fun _ : {idx : Fin (J + F.ell) // idx ∈ A_g} =>
            transZeroSet z_g delta) then
          r.rho ^ (Z' - A_g.card)
        else 0 := by
    apply Finset.sum_le_sum
    intro f_g _
    have hmem_iff : (∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g},
        f_g idx ∈ transZeroSet z_g delta) ↔
        f_g ∈ Fintype.piFinset (fun _ : {idx : Fin (J + F.ell) // idx ∈ A_g} =>
          transZeroSet z_g delta) := by
      rw [Fintype.mem_piFinset]
    by_cases hf : ∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g}, f_g idx ∈ transZeroSet z_g delta
    · rw [if_pos hf, if_pos (hmem_iff.mp hf)]
      exact target_rho_pow_le r z_g delta A_g f_g (storedMemory a_g B_g)
    · rw [if_neg hf, if_neg (mt hmem_iff.mpr hf)]
  have hpi_card : (Fintype.piFinset (fun _ : {idx : Fin (J + F.ell) // idx ∈ A_g} =>
      transZeroSet z_g delta)).card = Z' ^ A_g.card := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have hsum_const : (∑ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card,
      if f_g ∈ Fintype.piFinset (fun _ : {idx : Fin (J + F.ell) // idx ∈ A_g} =>
          transZeroSet z_g delta) then
        r.rho ^ (Z' - A_g.card)
      else 0) = (Z' : ℝ) ^ A_g.card * r.rho ^ (Z' - A_g.card) := by
    rw [← Finset.sum_filter, Finset.filter_univ_mem, Finset.sum_const, hpi_card, nsmul_eq_mul]
    push_cast
    rfl
  have hA_card : A_g.card ≤ F.ell + m := prom_card_le ν g A_g hA
  calc (∑ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card,
        if (∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g}, f_g idx ∈ transZeroSet z_g delta) then
          r.rho ^ (zeroMemoryIndices (translateMemory delta
            (deleteMemoryIndices z_g (Finset.univ.image f_g) + storedMemory a_g B_g))).card
        else 0)
      ≤ (Z' : ℝ) ^ A_g.card * r.rho ^ (Z' - A_g.card) := by
        rw [← hsum_const]
        exact hle_const
    _ ≤ Cprom := hCprom Z' A_g.card hA_card
    _ ≤ max 1 Cprom := le_max_right _ _

/-- Full single-big-group sum bound over `(B_g, A_g, f_g, b_g)`. -/
lemma bigGroup_sum_le (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (Cprom : ℝ) (hCprom : ∀ Z' a : ℕ, a ≤ F.ell + m → (Z' : ℝ) ^ a * r.rho ^ (Z' - a) ≤ Cprom)
    (ν : Pattern P J F.ell m) (delta : ℤ) (g : P.BigGroup)
    (hVlo : F.vMin ≤ P.V g.val)
    (htilted_nn : ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (htilted_sum : ∑ p : P.Prime g.val, tiltedMu F P n g.val p ≤ 2)
    (a_g : Fin (J + F.ell) → P.Prime g.val) (z_g : P.Memory g.val) :
    (∑ B_g : Finset (Fin (J + F.ell)),
      ∑ A_g : Finset (Fin (J + F.ell)),
        ∑ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card,
          ∑ b_g : Fin (J + F.ell) → P.Prime g.val,
            if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
              bigGroupWeight F r n ν delta g a_g z_g B_g A_g f_g b_g
            else 0) ≤
      bigGroupConst F r m Cprom := by
  classical
  have hVpos : 0 < P.V g.val := lt_of_lt_of_le F.vMin_pos hVlo
  have hvpos : 0 < r.v := lt_trans zero_lt_one r.v_gt
  let CV : ℝ := max 1 (max ((F.vMax) ^ (F.ell + m)) ((F.vMin⁻¹) ^ (F.ell + m)))
  have hCV_pos : 0 < CV := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  -- Step 1: For fixed B_g, A_g, bound the inner sum over f_g and b_g.
  have hinner_BA : ∀ B_g A_g : Finset (Fin (J + F.ell)),
      (∑ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card,
        ∑ b_g : Fin (J + F.ell) → P.Prime g.val,
          if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
            bigGroupWeight F r n ν delta g a_g z_g B_g A_g f_g b_g
          else 0) ≤
      if (∀ idx ∈ B_g, ¬ ν.shared g.val idx) ∧ (∀ idx ∈ A_g, ¬ ν.shared g.val idx) then
        max 1 Cprom * CV * (r.v ^ (F.ell + m)) * ((2 : ℝ) ^ (F.ell + m))
      else 0 := by
    intro B_g A_g
    by_cases hBA : (∀ idx ∈ B_g, ¬ ν.shared g.val idx) ∧ (∀ idx ∈ A_g, ¬ ν.shared g.val idx)
    · rw [if_pos hBA]
      obtain ⟨hB, hA⟩ := hBA
      have hB_card : B_g.card ≤ F.ell + m := prom_card_le ν g B_g hB
      have hA_card : A_g.card ≤ F.ell + m := prom_card_le ν g A_g hA
      have hV_le : (P.V g.val) ^ (-(A_g.card : ℤ)) ≤ CV := by
        calc (P.V g.val) ^ (-(A_g.card : ℤ))
            ≤ max 1 ((F.vMin⁻¹) ^ (F.ell + m)) :=
              Vinv_pow_le F.vMin_pos (P.V g.val) hVlo A_g.card hA_card
          _ ≤ CV := by
              apply max_le (le_max_left _ _)
              exact le_max_of_le_right (le_max_right _ _)
      have hw_le : (r.v ^ B_g.card / r.v ^ A_g.card) ≤ r.v ^ (F.ell + m) :=
        weight_ratio_le r A_g.card B_g.card hA_card hB_card
      have hf_step : ∀ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card,
          (∑ b_g : Fin (J + F.ell) → P.Prime g.val,
            if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
              bigGroupWeight F r n ν delta g a_g z_g B_g A_g f_g b_g
            else 0) ≤
          (if (∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g}, f_g idx ∈ transZeroSet z_g delta) then
            r.rho ^ (zeroMemoryIndices (translateMemory delta
              (deleteMemoryIndices z_g (Finset.univ.image f_g) + storedMemory a_g B_g))).card
          else 0) * (CV * (r.v ^ (F.ell + m)) * ((2 : ℝ) ^ (F.ell + m))) := by
        intro f_g
        have hpull : (∑ b_g : Fin (J + F.ell) → P.Prime g.val,
            if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
              bigGroupWeight F r n ν delta g a_g z_g B_g A_g f_g b_g
            else 0) =
            (∑ b_g : Fin (J + F.ell) → P.Prime g.val,
              if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
                (∏ idx : Fin (J + F.ell),
                  if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx))
              else 0) *
            ((P.V g.val) ^ (-(A_g.card : ℤ)) *
              r.rho ^ (zeroMemoryIndices (translateMemory delta
                (deleteMemoryIndices z_g (Finset.univ.image f_g) + storedMemory a_g B_g))).card *
              (r.v ^ B_g.card / r.v ^ A_g.card)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro b_g _
          split_ifs
          · unfold bigGroupWeight
            ring
          · ring
        rw [hpull]
        have hbl := bigGroup_label_sum_le F n ν delta g htilted_nn htilted_sum a_g z_g B_g A_g f_g
        by_cases hf : ∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g}, f_g idx ∈ transZeroSet z_g delta
        · have hcond_pos : (∀ idx ∈ B_g, ¬ ν.shared g.val idx) ∧
              (∀ idx ∈ A_g, ¬ ν.shared g.val idx) ∧
              (∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g}, f_g idx ∈ transZeroSet z_g delta) :=
            ⟨hB, hA, hf⟩
          rw [if_pos hcond_pos] at hbl
          rw [if_pos hf]
          have hrho_nn : 0 ≤ r.rho ^ (zeroMemoryIndices (translateMemory delta
              (deleteMemoryIndices z_g (Finset.univ.image f_g) + storedMemory a_g B_g))).card :=
            pow_nonneg r.rho_pos.le _
          have hV_nn : 0 ≤ (P.V g.val) ^ (-(A_g.card : ℤ)) := zpow_nonneg hVpos.le _
          have hw_nn : 0 ≤ r.v ^ B_g.card / r.v ^ A_g.card :=
            div_nonneg (pow_nonneg hvpos.le _) (pow_nonneg hvpos.le _)
          calc (∑ b_g : Fin (J + F.ell) → P.Prime g.val,
                if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
                  (∏ idx : Fin (J + F.ell),
                    if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx))
                else 0) *
              ((P.V g.val) ^ (-(A_g.card : ℤ)) *
                r.rho ^ (zeroMemoryIndices (translateMemory delta
                  (deleteMemoryIndices z_g (Finset.univ.image f_g) + storedMemory a_g B_g))).card *
                (r.v ^ B_g.card / r.v ^ A_g.card))
              ≤ ((2 : ℝ) ^ (F.ell + m)) *
                (CV *
                  r.rho ^ (zeroMemoryIndices (translateMemory delta
                    (deleteMemoryIndices z_g (Finset.univ.image f_g) + storedMemory a_g B_g))).card *
                  (r.v ^ (F.ell + m))) := by
                apply mul_le_mul hbl
                · apply mul_le_mul
                  · exact mul_le_mul_of_nonneg_right hV_le hrho_nn
                  · exact hw_le
                  · exact hw_nn
                  · exact mul_nonneg hCV_pos.le hrho_nn
                · exact mul_nonneg (mul_nonneg hV_nn hrho_nn) hw_nn
                · positivity
            _ = r.rho ^ (zeroMemoryIndices (translateMemory delta
                  (deleteMemoryIndices z_g (Finset.univ.image f_g) + storedMemory a_g B_g))).card *
                (CV * (r.v ^ (F.ell + m)) * ((2 : ℝ) ^ (F.ell + m))) := by ring
        · have hcond_neg : ¬ ((∀ idx ∈ B_g, ¬ ν.shared g.val idx) ∧
              (∀ idx ∈ A_g, ¬ ν.shared g.val idx) ∧
              (∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g}, f_g idx ∈ transZeroSet z_g delta)) :=
            fun hc => hf hc.2.2
          rw [if_neg hcond_neg] at hbl
          rw [if_neg hf, zero_mul]
          have hsum_nn : 0 ≤ ∑ b_g : Fin (J + F.ell) → P.Prime g.val,
              if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
                (∏ idx : Fin (J + F.ell),
                  if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx))
              else 0 := by
            apply Finset.sum_nonneg
            intro b_g _
            split_ifs
            · apply Finset.prod_nonneg
              intro idx _
              split_ifs
              · exact zero_le_one
              · exact htilted_nn _
            · exact le_refl 0
          have hsum_zero : (∑ b_g : Fin (J + F.ell) → P.Prime g.val,
              if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
                (∏ idx : Fin (J + F.ell),
                  if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx))
              else 0) = 0 := le_antisymm hbl hsum_nn
          rw [hsum_zero, zero_mul]
      calc (∑ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card,
            ∑ b_g : Fin (J + F.ell) → P.Prime g.val,
              if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
                bigGroupWeight F r n ν delta g a_g z_g B_g A_g f_g b_g
              else 0)
          ≤ ∑ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card,
              (if (∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g}, f_g idx ∈ transZeroSet z_g delta) then
                r.rho ^ (zeroMemoryIndices (translateMemory delta
                  (deleteMemoryIndices z_g (Finset.univ.image f_g) + storedMemory a_g B_g))).card
              else 0) * (CV * (r.v ^ (F.ell + m)) * ((2 : ℝ) ^ (F.ell + m))) :=
            Finset.sum_le_sum (fun f_g _ => hf_step f_g)
        _ = (∑ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card,
              if (∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g}, f_g idx ∈ transZeroSet z_g delta) then
                r.rho ^ (zeroMemoryIndices (translateMemory delta
                  (deleteMemoryIndices z_g (Finset.univ.image f_g) + storedMemory a_g B_g))).card
              else 0) * (CV * (r.v ^ (F.ell + m)) * ((2 : ℝ) ^ (F.ell + m))) := by
            rw [← Finset.sum_mul]
        _ ≤ max 1 Cprom * (CV * (r.v ^ (F.ell + m)) * ((2 : ℝ) ^ (F.ell + m))) := by
            apply mul_le_mul_of_nonneg_right
              (bigGroup_retrieval_sum_le r m Cprom hCprom ν delta g a_g z_g B_g A_g hA)
            exact mul_nonneg (mul_nonneg hCV_pos.le (pow_nonneg hvpos.le _)) (by positivity)
        _ = max 1 Cprom * CV * (r.v ^ (F.ell + m)) * ((2 : ℝ) ^ (F.ell + m)) := by ring
    · rw [if_neg hBA]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro f_g _
      apply Finset.sum_eq_zero
      intro b_g _
      rw [if_neg]
      intro hval
      exact hBA ⟨hval.1, hval.2.1⟩
  -- Step 2: Sum over B_g and A_g.
  let S_non := (Finset.univ.filter (fun idx : Fin (J + F.ell) => ¬ ν.shared g.val idx)).powerset
  let C_inner := max 1 Cprom * CV * (r.v ^ (F.ell + m)) * ((2 : ℝ) ^ (F.ell + m))
  have hC_inner_nn : 0 ≤ C_inner := by
    dsimp [C_inner]
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hCV_pos.le)
      (pow_nonneg hvpos.le _)) (by positivity)
  have hBA_sum : (∑ B_g : Finset (Fin (J + F.ell)),
      ∑ A_g : Finset (Fin (J + F.ell)),
        if (∀ idx ∈ B_g, ¬ ν.shared g.val idx) ∧ (∀ idx ∈ A_g, ¬ ν.shared g.val idx) then
          C_inner
        else 0) = ((S_non ×ˢ S_non).card : ℝ) * C_inner := by
    rw [← Finset.sum_product']
    have hfilt : (Finset.univ ×ˢ Finset.univ).filter
        (fun p : Finset (Fin (J + F.ell)) × Finset (Fin (J + F.ell)) =>
          (∀ idx ∈ p.1, ¬ ν.shared g.val idx) ∧ (∀ idx ∈ p.2, ¬ ν.shared g.val idx)) =
        S_non ×ˢ S_non := by
      ext ⟨B_g, A_g⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
        S_non, Finset.mem_powerset, Finset.subset_iff]
    rw [← Finset.sum_filter, hfilt, Finset.sum_const, nsmul_eq_mul]
  have hcard_4 : ((S_non ×ˢ S_non).card : ℝ) ≤ (4 : ℝ) ^ (F.ell + m) := by
    have h := transfer_pairs_card_le ν g
    exact_mod_cast h
  calc (∑ B_g : Finset (Fin (J + F.ell)),
        ∑ A_g : Finset (Fin (J + F.ell)),
          ∑ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin z_g.card,
            ∑ b_g : Fin (J + F.ell) → P.Prime g.val,
              if bigGroupValid ν delta g a_g z_g B_g A_g f_g b_g then
                bigGroupWeight F r n ν delta g a_g z_g B_g A_g f_g b_g
              else 0)
      ≤ ∑ B_g : Finset (Fin (J + F.ell)),
          ∑ A_g : Finset (Fin (J + F.ell)),
            if (∀ idx ∈ B_g, ¬ ν.shared g.val idx) ∧ (∀ idx ∈ A_g, ¬ ν.shared g.val idx) then
              C_inner
            else 0 :=
        Finset.sum_le_sum (fun B_g _ => Finset.sum_le_sum (fun A_g _ => hinner_BA B_g A_g))
    _ = ((S_non ×ˢ S_non).card : ℝ) * C_inner := hBA_sum
    _ ≤ (4 : ℝ) ^ (F.ell + m) * C_inner :=
        mul_le_mul_of_nonneg_right hcard_4 hC_inner_nn
    _ = (4 : ℝ) ^ (F.ell + m) * max 1 Cprom * CV *
          (r.v ^ (F.ell + m)) * ((2 : ℝ) ^ (F.ell + m)) := by
        dsimp [C_inner]
        ring
    _ ≤ bigGroupConst F r m Cprom := le_max_right _ _

end Erdos821.P3Edge
