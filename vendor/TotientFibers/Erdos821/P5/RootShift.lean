import Erdos821.P5.CompressedPairing

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

def patternTarget {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (u : P.Aux J)
    (n : ℤ) (a : A.Labels) : ℤ := n + A.k * (ν.D a u : ℤ)

theorem physicalPatternBody_zero_off_shift {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (u : P.Aux J)
    (n n' : ℤ) (a b : A.Labels) (h : n' ≠ patternTarget A ν u n a) :
    physicalPatternBody A ν u n n' a b = 0 := by
  simp only [physicalPatternBody, patternTarget] at *
  simp [h]

/-- The displacement gate eliminates the target-root sum, keeping its exact
finite support as a gate on the signed shifted root. -/
theorem sum_target_pattern {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (u : P.Aux J)
    (T : Finset ℤ) (g : ℤ → ℂ) (n : ℤ) (a b : A.Labels) :
    (∑ n' ∈ T, g n' * physicalPatternBody A ν u n n' a b) =
      if patternTarget A ν u n a ∈ T then
        g (patternTarget A ν u n a) *
          physicalPatternBody A ν u n (patternTarget A ν u n a) a b else 0 := by
  classical
  by_cases ht : patternTarget A ν u n a ∈ T
  · rw [if_pos ht]
    apply Finset.sum_eq_single_of_mem _ ht
    intro n' hn' hne
    rw [physicalPatternBody_zero_off_shift A ν u n n' a b hne, mul_zero]
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro n' hn'
    rw [physicalPatternBody_zero_off_shift A ν u n n' a b (fun h => ht (h ▸ hn')),
      mul_zero]

/-- Actual root-only graph pairing with the target root removed. Free laws,
physical lists, the ban and the signed displacement are all unchanged. -/
theorem pairing_shift_expansion {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (hV : ∀ g, P.V g ≠ 0)
    (X : ℝ) (T : Finset ℤ) (f g : ℤ → ℂ) :
    A.pairing X (T.product Finset.univ) f (fun z => g z.1) =
      ∑ n ∈ dyad X, ∑ v : Fin A.patternCount, ∑ u : FreeDraw (A.pattern v),
        ∑ a : A.Labels, ∑ b : A.Labels,
          (freeDrawLaw (A.pattern v) u : ℂ) * star (f n) *
            (P.markMass (J + F.ell) : ℂ) *
              (if patternTarget A (A.pattern v)
                (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV)) n a ∈ T
              then g (patternTarget A (A.pattern v)
                  (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV)) n a) *
                physicalPatternBody A (A.pattern v)
                  (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV)) n
                  (patternTarget A (A.pattern v)
                    (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV)) n a) a b
              else 0) := by
  rw [pairing_free_expansion A hV X T f g]
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← sum_target_pattern A (A.pattern v)
    (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV)) T g n a b,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n' hn'
  ring

end Erdos821.P5Core
