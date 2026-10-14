import Erdos821.S2.MemoryGhost
import Erdos821.S2.GhostTasks
import Erdos821.Blueprint.Graph

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Adj

open Erdos821.Blueprint.Graph hiding GhostChoice absoluteMemoryGhostKernel absoluteScaledMemoryGhostKernel deleteMemoryIndices ghostBirthCount ghostChoiceValid ghostChoiceWeight ghostReversalFactor memoryEntry memoryGhostKernel zeroBirthBatch zeroMemoryIndices
open Erdos821.S2Core

def singleWeight {P : PrimeGroups} (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 : P.Memory g.val)
    (A : Finset (Fin s0.card)) (b : Fin (t0.card + 1))
    (p : Fin b.val → P.Prime g.val) : ℝ :=
  (-eta F n i / rho) ^ A.card *
  (visitQ F.q n i / rho ^ (2 : ℕ)) ^
    ((zeroMemoryIndices s0).card - A.card) *
  ((b.val.factorial : ℝ)⁻¹) *
  (-eta F n i * P.V g.val / rho) ^ b.val *
  ∏ h : Fin b.val, tiltedMu F P n g.val (p h)

def singleValid {P : PrimeGroups} (g : P.BigGroup) (s0 t0 : P.Memory g.val)
    (A : Finset (Fin s0.card)) (b : Fin (t0.card + 1))
    (p : Fin b.val → P.Prime g.val) : Prop :=
  A ⊆ zeroMemoryIndices s0 ∧
    deleteMemoryIndices s0 A + zeroBirthBatch p = t0

def singleKernel {P : PrimeGroups} (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 : P.Memory g.val) : ℝ :=
  ∑ A : Finset (Fin s0.card), ∑ b : Fin (t0.card + 1),
    ∑ p : Fin b.val → P.Prime g.val,
      if singleValid g s0 t0 A b p then
        |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
      else 0

variable {P : PrimeGroups} (F : FixedData) (J n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
  (s t : P.MemoryState (J + F.ell))

lemma globalSummand_eq_prod (c : GhostChoice s t) :
    (if ghostChoiceValid c then |ghostChoiceWeight F n rho i c| * d ^ ghostBirthCount c else 0) =
    ∏ g : P.BigGroup,
      (if singleValid g (s.2.2 g) (t.2.2 g) (c.1 g) (c.2.1 g) (c.2.2 g) then
        |singleWeight F n rho i g (s.2.2 g) (t.2.2 g) (c.1 g) (c.2.1 g) (c.2.2 g)| *
          d ^ (c.2.1 g).val
      else 0) := by
  by_cases hvalid : ghostChoiceValid c
  · rw [if_pos hvalid]
    have hsingle : ∀ g, singleValid g (s.2.2 g) (t.2.2 g) (c.1 g) (c.2.1 g) (c.2.2 g) := fun g => hvalid g
    rw [Finset.prod_congr rfl (fun g _ => if_pos (hsingle g))]
    have hweight : ghostChoiceWeight F n rho i c =
        ∏ g, singleWeight F n rho i g (s.2.2 g) (t.2.2 g) (c.1 g) (c.2.1 g) (c.2.2 g) := rfl
    rw [hweight, Finset.abs_prod]
    have hbirth : ghostBirthCount c = ∑ g : P.BigGroup, (c.2.1 g).val := rfl
    rw [hbirth, ← Finset.prod_pow_eq_pow_sum]
    rw [Finset.prod_mul_distrib]
  · rw [if_neg hvalid]
    have hneg : ∃ g0 : P.BigGroup, ¬ singleValid g0 (s.2.2 g0) (t.2.2 g0) (c.1 g0) (c.2.1 g0) (c.2.2 g0) := by
      by_contra hcon
      push_neg at hcon
      apply hvalid
      intro g
      exact hcon g
    obtain ⟨g0, hg0⟩ := hneg
    have hzero : (∏ g : P.BigGroup,
      (if singleValid g (s.2.2 g) (t.2.2 g) (c.1 g) (c.2.1 g) (c.2.2 g) then
        |singleWeight F n rho i g (s.2.2 g) (t.2.2 g) (c.1 g) (c.2.1 g) (c.2.2 g)| *
          d ^ (c.2.1 g).val
      else 0)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ g0)
      rw [if_neg hg0]
    rw [hzero]

lemma globalSum_split :
    (∑ c : GhostChoice s t,
      (if ghostChoiceValid c then |ghostChoiceWeight F n rho i c| * d ^ ghostBirthCount c else 0)) =
    ∑ A : ((g : P.BigGroup) → Finset (Fin (s.2.2 g).card)),
    ∑ b : ((g : P.BigGroup) → Fin ((t.2.2 g).card + 1)),
    ∑ p : ((g : P.BigGroup) → Fin (b g).val → P.Prime g.val),
      (∏ g : P.BigGroup,
        (if singleValid g (s.2.2 g) (t.2.2 g) (A g) (b g) (p g) then
          |singleWeight F n rho i g (s.2.2 g) (t.2.2 g) (A g) (b g) (p g)| *
            d ^ (b g).val
        else 0)) := by
  have hsplit : ∀ f : GhostChoice s t → ℝ,
    ∑ c, f c = ∑ A, ∑ b, ∑ p : ((g : P.BigGroup) → Fin (b g).val → P.Prime g.val), f (A, ⟨b, p⟩) := by
    intro f
    simp only [GhostChoice]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro A _
    rw [Fintype.sum_sigma]
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  rw [globalSummand_eq_prod F J n rho d i s t (A, ⟨b, p⟩)]

lemma interchange_p (A : (g : P.BigGroup) → Finset (Fin (s.2.2 g).card))
    (b : (g : P.BigGroup) → Fin ((t.2.2 g).card + 1)) :
    (∑ p : ((g : P.BigGroup) → Fin (b g).val → P.Prime g.val),
      ∏ g : P.BigGroup,
        (if singleValid g (s.2.2 g) (t.2.2 g) (A g) (b g) (p g) then
          |singleWeight F n rho i g (s.2.2 g) (t.2.2 g) (A g) (b g) (p g)| *
            d ^ (b g).val
        else 0)) =
    ∏ g : P.BigGroup, ∑ p_g : Fin (b g).val → P.Prime g.val,
      (if singleValid g (s.2.2 g) (t.2.2 g) (A g) (b g) p_g then
        |singleWeight F n rho i g (s.2.2 g) (t.2.2 g) (A g) (b g) p_g| * d ^ (b g).val
      else 0) := by
  have h := Finset.prod_univ_sum
    (t := fun g : P.BigGroup => (Finset.univ : Finset (Fin (b g).val → P.Prime g.val)))
    (f := fun g : P.BigGroup => fun p_g : Fin (b g).val → P.Prime g.val =>
      (if singleValid g (s.2.2 g) (t.2.2 g) (A g) (b g) p_g then
        |singleWeight F n rho i g (s.2.2 g) (t.2.2 g) (A g) (b g) p_g| * d ^ (b g).val
      else 0))
  rw [Fintype.piFinset_univ] at h
  exact h.symm

lemma interchange_b (A : (g : P.BigGroup) → Finset (Fin (s.2.2 g).card))
    (G : ∀ g : P.BigGroup, Fin ((t.2.2 g).card + 1) → ℝ) :
    (∑ b : ((g : P.BigGroup) → Fin ((t.2.2 g).card + 1)), ∏ g, G g (b g)) =
    ∏ g, ∑ b_g : Fin ((t.2.2 g).card + 1), G g b_g := by
  have h := Finset.prod_univ_sum
    (t := fun g : P.BigGroup => (Finset.univ : Finset (Fin ((t.2.2 g).card + 1))))
    (f := fun g : P.BigGroup => fun b_g : Fin ((t.2.2 g).card + 1) => G g b_g)
  rw [Fintype.piFinset_univ] at h
  exact h.symm

lemma interchange_A (G : ∀ g : P.BigGroup, Finset (Fin (s.2.2 g).card) → ℝ) :
    (∑ A : ((g : P.BigGroup) → Finset (Fin (s.2.2 g).card)), ∏ g, G g (A g)) =
    ∏ g, ∑ A_g : Finset (Fin (s.2.2 g).card), G g A_g := by
  have h := Finset.prod_univ_sum
    (t := fun g : P.BigGroup => (Finset.univ : Finset (Finset (Fin (s.2.2 g).card))))
    (f := fun g : P.BigGroup => fun A_g : Finset (Fin (s.2.2 g).card) => G g A_g)
  rw [Fintype.piFinset_univ] at h
  exact h.symm

lemma globalKernel_eq_prod (hcoord : s.1 = t.1 ∧ s.2.1 = t.2.1) :
    absoluteScaledMemoryGhostKernel F J n rho d i s t =
    ∏ g : P.BigGroup, singleKernel F n rho d i g (s.2.2 g) (t.2.2 g) := by
  unfold absoluteScaledMemoryGhostKernel singleKernel
  rw [if_pos hcoord]
  rw [globalSum_split F J n rho d i s t]
  calc
    (∑ A : ((g : P.BigGroup) → Finset (Fin (s.2.2 g).card)),
      ∑ b : ((g : P.BigGroup) → Fin ((t.2.2 g).card + 1)),
      ∑ p : ((g : P.BigGroup) → Fin (b g).val → P.Prime g.val),
        ∏ g, (if singleValid g (s.2.2 g) (t.2.2 g) (A g) (b g) (p g) then
          |singleWeight F n rho i g (s.2.2 g) (t.2.2 g) (A g) (b g) (p g)| * d ^ (b g).val else 0))
      = ∑ A : ((g : P.BigGroup) → Finset (Fin (s.2.2 g).card)),
        ∑ b : ((g : P.BigGroup) → Fin ((t.2.2 g).card + 1)),
        ∏ g : P.BigGroup, ∑ p_g : Fin (b g).val → P.Prime g.val,
          (if singleValid g (s.2.2 g) (t.2.2 g) (A g) (b g) p_g then
            |singleWeight F n rho i g (s.2.2 g) (t.2.2 g) (A g) (b g) p_g| * d ^ (b g).val else 0) := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro b _
        exact interchange_p F J n rho d i s t A b
    _ = ∑ A : ((g : P.BigGroup) → Finset (Fin (s.2.2 g).card)),
        ∏ g : P.BigGroup, ∑ b_g : Fin ((t.2.2 g).card + 1),
          ∑ p_g : Fin b_g.val → P.Prime g.val,
            (if singleValid g (s.2.2 g) (t.2.2 g) (A g) b_g p_g then
              |singleWeight F n rho i g (s.2.2 g) (t.2.2 g) (A g) b_g p_g| * d ^ b_g.val else 0) := by
        apply Finset.sum_congr rfl
        intro A _
        exact interchange_b F J s t A
          (fun g b_g => ∑ p_g : Fin b_g.val → P.Prime g.val,
            (if singleValid g (s.2.2 g) (t.2.2 g) (A g) b_g p_g then
              |singleWeight F n rho i g (s.2.2 g) (t.2.2 g) (A g) b_g p_g| * d ^ b_g.val else 0))
    _ = ∏ g : P.BigGroup, ∑ A_g : Finset (Fin (s.2.2 g).card),
        ∑ b_g : Fin ((t.2.2 g).card + 1),
        ∑ p_g : Fin b_g.val → P.Prime g.val,
          (if singleValid g (s.2.2 g) (t.2.2 g) A_g b_g p_g then
            |singleWeight F n rho i g (s.2.2 g) (t.2.2 g) A_g b_g p_g| * d ^ b_g.val else 0) := by
        exact interchange_A F J s
          (fun g A_g => ∑ b_g : Fin ((t.2.2 g).card + 1),
            ∑ p_g : Fin b_g.val → P.Prime g.val,
              (if singleValid g (s.2.2 g) (t.2.2 g) A_g b_g p_g then
                |singleWeight F n rho i g (s.2.2 g) (t.2.2 g) A_g b_g p_g| * d ^ b_g.val else 0))


end Erdos821.P3Adj
