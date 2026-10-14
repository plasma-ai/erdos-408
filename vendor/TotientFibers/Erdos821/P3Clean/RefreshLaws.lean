import Erdos821.P3Clean.Baseline

/-! Product laws with deterministic shared coordinates and fresh unshared coordinates. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

def productMass {I : Type*} [Fintype I] {α : I → Type*} (mu : ∀ i, α i → ℝ)
    (a : ∀ i, α i) : ℝ := ∏ i, mu i (a i)

def refreshMatches {I : Type*} {α : I → Type*} (shared : I → Prop) (a b : ∀ i, α i) : Prop :=
  ∀ i, shared i → a i = b i

def refreshMass {I : Type*} [Fintype I] {α : I → Type*} (shared : I → Prop)
    (mu : ∀ i, α i → ℝ) (b : ∀ i, α i) : ℝ :=
  ∏ i, if shared i then 1 else mu i (b i)

def refreshKernel {I : Type*} [Fintype I] {α : I → Type*} (shared : I → Prop)
    (mu : ∀ i, α i → ℝ) (a b : ∀ i, α i) : ℝ :=
  if refreshMatches shared a b then refreshMass shared mu b else 0

theorem refreshKernel_eq_prod {I : Type*} [Fintype I] {α : I → Type*}
    (shared : I → Prop) (mu : ∀ i, α i → ℝ) (a b : ∀ i, α i) :
    refreshKernel shared mu a b =
      ∏ i, if shared i then (if a i = b i then 1 else 0) else mu i (b i) := by
  classical
  by_cases h : refreshMatches shared a b
  · simp only [refreshKernel, if_pos h, refreshMass]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : shared i
    · simp only [if_pos hi, if_pos (h i hi)]
    · simp only [if_neg hi]
  · rw [refreshKernel, if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    have hs : shared i := by by_contra hh; exact hi (fun hp => False.elim (hh hp))
    have hab : a i ≠ b i := fun hh => hi (fun _ => hh)
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [if_pos hs, if_neg hab]

theorem refreshKernel_row_sum {I : Type*} [Fintype I] [DecidableEq I] {α : I → Type*} [∀ i, Fintype (α i)]
    (shared : I → Prop) (mu : ∀ i, α i → ℝ) (hmu : ∀ i, (∑ x, mu i x) = 1)
    (a : ∀ i, α i) : (∑ b, refreshKernel shared mu a b) = 1 := by
  classical
  simp only [refreshKernel_eq_prod]
  rw [← Fintype.prod_sum (fun i x => if shared i then (if a i = x then 1 else 0) else mu i x)]
  apply Finset.prod_eq_one
  intro i _
  by_cases hi : shared i
  · simp [hi]
  · simp only [if_neg hi, hmu i]

theorem refreshMass_reversal {I : Type*} [Fintype I] {α : I → Type*}
    (shared : I → Prop) (mu : ∀ i, α i → ℝ) (a b : ∀ i, α i)
    (h : refreshMatches shared a b) :
    productMass mu a * refreshMass shared mu b = productMass mu b * refreshMass shared mu a := by
  simp only [productMass, refreshMass, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : shared i
  · simp only [if_pos hi, h i hi]
  · simp only [if_neg hi]
    ring

theorem refreshKernel_reversal {I : Type*} [Fintype I] {α : I → Type*}
    (shared : I → Prop) (mu : ∀ i, α i → ℝ) (a b : ∀ i, α i) :
    productMass mu a * refreshKernel shared mu a b =
      productMass mu b * refreshKernel shared mu b a := by
  classical
  have hs : refreshMatches shared a b ↔ refreshMatches shared b a := by
    unfold refreshMatches
    exact forall_congr' (fun _ => imp_congr_right (fun _ => eq_comm))
  by_cases h : refreshMatches shared a b
  · simp only [refreshKernel, if_pos h, if_pos (hs.mp h)]
    exact refreshMass_reversal shared mu a b h
  · simp only [refreshKernel, if_neg h, if_neg (fun hh => h (hs.mpr hh)), mul_zero]


end Erdos821.P3Clean
