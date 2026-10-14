import Mathlib
import Erdos821.Blueprint.Graph
import Erdos821.Blueprint.Analytic

open scoped BigOperators
open Filter

attribute [local instance] Classical.propDecidable

namespace Erdos821.GraphLemmas

theorem sum_powerset_neg_one {ι : Type*} [DecidableEq ι] (U : Finset ι) :
    ∑ A ∈ U.powerset, (-1 : ℤ) ^ A.card = if U = ∅ then 1 else 0 := by
  induction U using Finset.induction with
  | empty => simp
  | insert a s has =>
    rw [Finset.powerset_insert]
    have hdisj : Disjoint (s.powerset) (s.powerset.image (insert a)) := by
      rw [Finset.disjoint_left]
      intro A hA himg
      have hAsub : A ⊆ s := Finset.mem_powerset.mp hA
      obtain ⟨B, _, hB⟩ := Finset.mem_image.mp himg
      have haA : a ∈ A := by rw [← hB]; exact Finset.mem_insert_self a B
      exact has (hAsub haA)
    rw [Finset.sum_union hdisj]
    have himg : ∑ A ∈ s.powerset.image (insert a), (-1 : ℤ) ^ A.card
        = - ∑ A ∈ s.powerset, (-1 : ℤ) ^ A.card := by
      rw [Finset.sum_image]
      · rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro A hA
        have hAsub : A ⊆ s := Finset.mem_powerset.mp hA
        have haA : a ∉ A := fun h => has (hAsub h)
        rw [Finset.card_insert_of_notMem haA, pow_succ]
        ring
      · intro A hA B hB hab
        have hAsub : A ⊆ s := Finset.mem_powerset.mp hA
        have hBsub : B ⊆ s := Finset.mem_powerset.mp hB
        have haA : a ∉ A := fun h => has (hAsub h)
        have haB : a ∉ B := fun h => has (hBsub h)
        have hcon : Finset.erase (insert a A) a = Finset.erase (insert a B) a :=
          congrArg (·.erase a) hab
        simp [Finset.erase_insert haA, Finset.erase_insert haB] at hcon
        exact hcon
    rw [himg, add_neg_cancel]
    simp

end Erdos821.GraphLemmas

namespace Erdos821.Blueprint.Analytic

/-- §3 alternating nonempty free subsets cancel: sum = -1. -/
theorem inclusion_exclusion {ι : Type*} [DecidableEq ι] (U : Finset ι)
    (hU : U.Nonempty) :
    ∑ A ∈ U.powerset.erase ∅, (-1 : ℤ) ^ A.card = -1 := by
  have hne : U ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hU
  have hsum : ∑ A ∈ U.powerset, (-1 : ℤ) ^ A.card = 0 := by
    rw [Erdos821.GraphLemmas.sum_powerset_neg_one]
    simp [hne]
  have hmem : (∅ : Finset ι) ∈ U.powerset := Finset.empty_mem_powerset U
  have hadd := Finset.add_sum_erase (s := U.powerset)
    (f := fun A => (-1 : ℤ) ^ A.card) hmem
  have h0 : (-1 : ℤ) ^ (∅ : Finset ι).card = 1 := by simp
  have hadd2 : (1 : ℤ) + ∑ A ∈ U.powerset.erase ∅, (-1 : ℤ) ^ A.card
      = ∑ A ∈ U.powerset, (-1 : ℤ) ^ A.card := by
    rw [← h0]
    exact hadd
  linarith

example : @Erdos821.Blueprint.Analytic.inclusion_exclusion =
    @Erdos821.Blueprint.Analytic.inclusion_exclusion := rfl

end Erdos821.Blueprint.Analytic

namespace Erdos821.Blueprint.Graph

/-- §2 omission injection: at most one U per pending index (field argument). -/
theorem omission_congruence_unique (p : ℕ) (hp : Nat.Prime p)
    (r A : ZMod p) (hA : A ≠ 0) (U₁ U₂ : ℕ)
    (h₁ : 0 < U₁) (h₁p : U₁ < p) (h₂ : 0 < U₂) (h₂p : U₂ < p)
    (hc₁ : r * (U₁ : ZMod p) + A = 0) (hc₂ : r * (U₂ : ZMod p) + A = 0) :
    U₁ = U₂ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have _h₁ : 0 < U₁ := h₁
  have _h₂ : 0 < U₂ := h₂
  have hr : r ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_add] at hc₁
    exact hA hc₁
  have e1 : r * (U₁ : ZMod p) = -A := eq_neg_of_add_eq_zero_left hc₁
  have e2 : r * (U₂ : ZMod p) = -A := eq_neg_of_add_eq_zero_left hc₂
  have hmul : r * (U₁ : ZMod p) = r * (U₂ : ZMod p) := by rw [e1, e2]
  have hcast : (U₁ : ZMod p) = (U₂ : ZMod p) := mul_left_cancel₀ hr hmul
  have hv1 : ((U₁ : ZMod p).val) = U₁ := ZMod.val_natCast_of_lt h₁p
  have hv2 : ((U₂ : ZMod p).val) = U₂ := ZMod.val_natCast_of_lt h₂p
  have hval : ((U₁ : ZMod p).val) = ((U₂ : ZMod p).val) := congrArg ZMod.val hcast
  rw [hv1, hv2] at hval
  exact hval

example : @Erdos821.Blueprint.Graph.omission_congruence_unique =
    @Erdos821.Blueprint.Graph.omission_congruence_unique := rfl

/-- §2 large-J gain needs ell > 0: log choose → ∞. -/
theorem omission_number_grows (ell : ℕ) (h : 0 < ell) :
    Tendsto (fun J : ℕ => Real.log (Nat.choose (J + ell) ell)) atTop atTop := by
  have h1ell : 1 ≤ ell := h
  have hbound : ∀ J : ℕ, J + 1 ≤ Nat.choose (J + ell) ell := by
    intro J
    have hle : J + 1 ≤ J + ell := Nat.add_le_add_left h1ell J
    have hmono : (J + 1).choose J ≤ (J + ell).choose J :=
      Nat.choose_le_choose J hle
    have hsucc : (J + 1).choose J = J + 1 := Nat.choose_succ_self_right J
    have hsymm : (J + ell).choose J = (J + ell).choose ell := Nat.choose_symm_add
    omega
  have hboundR : ∀ J : ℕ, ((J + 1 : ℕ) : ℝ) ≤ ((Nat.choose (J + ell) ell : ℕ) : ℝ) := by
    intro J
    exact Nat.cast_le.mpr (hbound J)
  have hcast : Tendsto (fun J : ℕ => ((J : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hplus1 : Tendsto (fun J : ℕ => ((J : ℕ) : ℝ) + 1) atTop atTop := by
    apply Filter.tendsto_atTop_mono (fun J => le_add_of_nonneg_right zero_le_one)
    exact hcast
  have hchoose : Tendsto (fun J : ℕ => ((Nat.choose (J + ell) ell : ℕ) : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono _ hplus1
    intro J
    simpa using hboundR J
  exact Real.tendsto_log_atTop.comp hchoose

example : @Erdos821.Blueprint.Graph.omission_number_grows =
    @Erdos821.Blueprint.Graph.omission_number_grows := rfl

end Erdos821.Blueprint.Graph
