import Erdos821.S2.Births

/-! Distinctness on performed addresses as a signed permutation sum. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2

/-- A permutation supported on performed addresses and preserving their values
has total sign sum one precisely when those values are distinct. -/
theorem performed_value_preserving_sign_sum {α : Type*} [Fintype α] [DecidableEq α]
    (performed : Finset α) (value : α → ℕ) :
    (if Set.InjOn value performed then (1 : ℤ) else 0) =
      ∑ σ : Equiv.Perm α,
        if σ.support ⊆ performed ∧ ∀ i, value (σ i) = value i
          then (Equiv.Perm.sign σ : ℤ) else 0 := by
  classical
  let M : Matrix α α ℤ := fun r c =>
    if c ∈ performed then (if r ∈ performed ∧ value r = value c then 1 else 0)
    else if r = c then 1 else 0
  have hdet : (if Set.InjOn value performed then (1 : ℤ) else 0) = M.det := by
    by_cases hv : Set.InjOn value performed
    · have hM : M = 1 := by
        ext r c
        by_cases hc : c ∈ performed
        · have he : (r ∈ performed ∧ value r = value c) ↔ r = c := by
            constructor
            · rintro ⟨hr, he⟩
              exact hv hr hc he
            · rintro rfl
              exact ⟨hc, rfl⟩
          simp only [M, if_pos hc, he, Matrix.one_apply]
        · simp only [M, if_neg hc, Matrix.one_apply]
      simp [hv, hM]
    · change ¬ (∀ r ∈ performed, ∀ c ∈ performed, value r = value c → r = c) at hv
      push_neg at hv
      obtain ⟨r, hr, c, hc, he, hrc⟩ := hv
      have hrows : M r = M c := by
        funext k
        by_cases hk : k ∈ performed
        · simp [M, hk, hr, hc, he]
        · have hrk : r ≠ k := by rintro rfl; exact hk hr
          have hck : c ≠ k := by rintro rfl; exact hk hc
          simp [M, hk, hrk, hck]
      simp only [show ¬ Set.InjOn value performed from by
        intro h; exact hrc (h hr hc he), ↓reduceIte]
      exact (Matrix.det_zero_of_row_eq hrc hrows).symm
  let cond (σ : Equiv.Perm α) (i : α) : Prop :=
    if i ∈ performed then σ i ∈ performed ∧ value (σ i) = value i else σ i = i
  have hcond (σ : Equiv.Perm α) : (∀ i, cond σ i) ↔
      σ.support ⊆ performed ∧ ∀ i, value (σ i) = value i := by
    constructor
    · intro h
      constructor
      · intro i hi
        by_contra hn
        have hfix : σ i = i := by simpa only [cond, if_neg hn] using h i
        exact Equiv.Perm.mem_support.mp hi hfix
      · intro i
        by_cases hi : i ∈ performed
        · exact (show σ i ∈ performed ∧ value (σ i) = value i from by
            simpa only [cond, if_pos hi] using h i).2
        · have hfix : σ i = i := by simpa only [cond, if_neg hi] using h i
          rw [hfix]
    · rintro ⟨hs, hv⟩ i
      by_cases hi : i ∈ performed
      · have ho : σ i ∈ performed := by
          by_cases hfix : σ i = i
          · simpa only [hfix] using hi
          · exact hs (Equiv.Perm.apply_mem_support.mpr (Equiv.Perm.mem_support.mpr hfix))
        exact (show cond σ i from by simpa only [cond, if_pos hi] using And.intro ho (hv i))
      · have hfix : σ i = i := Equiv.Perm.notMem_support.mp (fun h => hi (hs h))
        simpa only [cond, if_neg hi] using hfix
  have hentry (σ : Equiv.Perm α) (i : α) :
      M (σ i) i = if cond σ i then (1 : ℤ) else 0 := by
    by_cases hi : i ∈ performed <;> simp only [M, cond, hi, ↓reduceIte]
  have hprod (σ : Equiv.Perm α) :
      (∏ i, M (σ i) i) =
        if σ.support ⊆ performed ∧ ∀ i, value (σ i) = value i then (1 : ℤ) else 0 := by
    by_cases he : σ.support ⊆ performed ∧ ∀ i, value (σ i) = value i
    · have hc := (hcond σ).mpr he
      rw [if_pos he]
      apply Finset.prod_eq_one
      intro i _
      rw [hentry]
      exact if_pos (hc i)
    · have hc : ¬ ∀ i, cond σ i := fun h => he ((hcond σ).mp h)
      obtain ⟨i, hi⟩ := not_forall.mp hc
      rw [if_neg he]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hentry]
      exact if_neg hi

  calc
    _ = M.det := hdet
    _ = _ := by
      rw [Matrix.det_apply']
      apply Finset.sum_congr rfl
      intro σ _
      rw [hprod]
      split_ifs <;> simp


end Erdos821.S2
