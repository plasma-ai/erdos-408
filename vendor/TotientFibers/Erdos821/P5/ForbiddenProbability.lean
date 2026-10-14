import Erdos821.P5.ProductProbability

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core

theorem weighted_forbidden_values {α : Type*} [Fintype α] (w : α → ℝ)
    (value : α → ℕ) (hv : Function.Injective value) (F : Finset ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (hw : ∀ a, w a ≤ ε) :
    (∑ a, if value a ∈ F then w a else 0) ≤ (F.card : ℝ) * ε := by
  let s := Finset.univ.filter (fun a => value a ∈ F)
  have hsub : s.image value ⊆ F := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    exact (Finset.mem_filter.mp ha).2
  have hcard : s.card ≤ F.card := by
    rw [← Finset.card_image_of_injective s hv]
    exact Finset.card_le_card hsub
  have hcardR : (s.card : ℝ) ≤ F.card := by exact_mod_cast hcard
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ a ∈ s, ε := Finset.sum_le_sum (fun a ha => hw a)
    _ = (s.card : ℝ) * ε := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcardR hε

/-- The forbidden values for a coordinate may be chosen from all the other
draws. A bound on their cardinality still gives the usual atom union bound. -/
theorem productLaw_forbidden_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (w : ∀ i, α i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hs : ∀ i, (∑ a, w i a) = 1) (i : ι) (value : α i → ℕ)
    (hv : Function.Injective value)
    (F : (∀ j : {j : ι // j ≠ i}, α j.val) → Finset ℕ) (N : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (hatom : ∀ a, w i a ≤ ε) (hN : ∀ r, (F r).card ≤ N) :
    (∑ z : ∀ i, α i,
      if value (z i) ∈ F (fun j => z j.val) then productLaw w z else 0) ≤ (N : ℝ) * ε := by
  let f : (∀ i, α i) → ℝ := fun z => if value (z i) ∈ F (fun j => z j.val) then 1 else 0
  have hb (r : ∀ j : {j : ι // j ≠ i}, α j.val) :
      (∑ a : α i, w i a * f ((Equiv.piSplitAt i α).symm (a, r))) ≤ (N : ℝ) * ε := by
    have hterm (a : α i) : w i a * f ((Equiv.piSplitAt i α).symm (a, r)) =
        if value a ∈ F r then w i a else 0 := by
      have heq : (((Equiv.piSplitAt i α).symm (a, r)) i,
          fun j : {j : ι // j ≠ i} => ((Equiv.piSplitAt i α).symm (a, r)) j.val) = (a, r) :=
        (Equiv.piSplitAt i α).apply_symm_apply (a, r)
      have hown : ((Equiv.piSplitAt i α).symm (a, r)) i = a := congrArg Prod.fst heq
      have hrest : (fun j : {j : ι // j ≠ i} =>
          ((Equiv.piSplitAt i α).symm (a, r)) j.val) = r := congrArg Prod.snd heq
      simp only [f, hown, hrest, mul_ite, mul_one, mul_zero]
    simp_rw [hterm]
    exact (weighted_forbidden_values (w i) value hv (F r) ε hε hatom).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hN r) hε)
  simpa only [f, mul_ite, mul_one, mul_zero] using
    productLaw_conditional_bound w hw hs i f ((N : ℝ) * ε) hb

theorem productLaw_union_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (w : ∀ i, α i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (event : κ → (∀ i, α i) → Prop) (B : κ → ℝ)
    (hb : ∀ k, (∑ z, if event k z then productLaw w z else 0) ≤ B k) :
    (∑ z, if ∃ k, event k z then productLaw w z else 0) ≤ ∑ k, B k := by
  have hpoint (z : ∀ i, α i) :
      (if ∃ k, event k z then productLaw w z else 0) ≤
        ∑ k, if event k z then productLaw w z else 0 := by
    by_cases hz : ∃ k, event k z
    · rw [if_pos hz]
      obtain ⟨k, hk⟩ := hz
      have h := Finset.single_le_sum
        (f := fun k => if event k z then productLaw w z else 0)
        (fun k hk => by split_ifs <;> first | exact productLaw_nonneg w hw z | exact le_rfl)
        (Finset.mem_univ k)
      simpa only [if_pos hk] using h
    · have hnone : ∀ k, ¬event k z := not_exists.mp hz
      rw [if_neg hz]
      simp only [hnone, if_false, Finset.sum_const_zero, le_refl]
  calc
    _ ≤ ∑ z : ∀ i, α i, ∑ k, if event k z then productLaw w z else 0 :=
      Finset.sum_le_sum (fun z hz => hpoint z)
    _ = ∑ k, ∑ z : ∀ i, α i, if event k z then productLaw w z else 0 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun k hk => hb k)

theorem productLaw_any_forbidden {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (w : ∀ i, α i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hs : ∀ i, (∑ a, w i a) = 1) (value : ∀ i, α i → ℕ)
    (hv : ∀ i, Function.Injective (value i))
    (F : ∀ i, (∀ j : {j : ι // j ≠ i}, α j.val) → Finset ℕ)
    (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hatom : ∀ i a, w i a ≤ ε)
    (hN : ∀ i r, (F i r).card ≤ N) :
    (∑ z : ∀ i, α i,
      if ∃ i, value i (z i) ∈ F i (fun j => z j.val) then productLaw w z else 0) ≤
        (Fintype.card ι : ℝ) * N * ε := by
  have h := productLaw_union_bound w hw
    (fun i z => value i (z i) ∈ F i (fun j => z j.val))
    (fun _ => (N : ℝ) * ε) (fun i => by
      have hi := productLaw_forbidden_coordinate w hw hs i (value i) (hv i) (F i) N ε hε
        (hatom i) (hN i)
      convert hi using 1
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hp : value i (z i) ∈ F i (fun j => z j.val) <;> simp only [hp, if_true, if_false])
  have h' : (∑ z : ∀ i, α i,
      if ∃ i, value i (z i) ∈ F i (fun j => z j.val) then productLaw w z else 0) ≤
        ∑ i : ι, (N : ℝ) * ε := by
    convert h using 1
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hp : ∃ i, value i (z i) ∈ F i (fun j => z j.val) <;> simp only [hp, if_true, if_false]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using h'

end Erdos821.P5Core
