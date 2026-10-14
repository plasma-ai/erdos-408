import Erdos821.P5.PatternPairing

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

theorem sharedDraw_nonempty {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (hV : ∀ g, P.V g ≠ 0) : Nonempty (SharedDraw ν) := by
  have hsum := sharedDrawLaw_sum ν hV
  have hs : (Finset.univ : Finset (SharedDraw ν)).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty] at hsum
    norm_num at hsum
  obtain ⟨z, hz⟩ := hs
  exact ⟨z⟩

def unusedAuxDraw {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (hV : ∀ g, P.V g ≠ 0) : SharedDraw ν :=
  Classical.choice (sharedDraw_nonempty ν hV)

theorem physicalPatternBody_restrict {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (u : P.Aux J) (unused : SharedDraw ν)
    (n n' : ℤ) (a b : A.Labels) :
    physicalPatternBody A ν u n n' a b =
      physicalPatternBody A ν (assembleAux ν (freeRestriction ν u) unused) n n' a b := by
  apply physicalPatternBody_aux_ext
  intro g i hi
  rw [assembleAux_free ν (freeRestriction ν u) unused g ⟨i, hi⟩]
  rfl

theorem sum_pattern_aux_free {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (hV : ∀ g, P.V g ≠ 0)
    (unused : SharedDraw ν) (n n' : ℤ) (a b : A.Labels) :
    (∑ u : P.Aux J, (ν.auxMass u : ℂ) * physicalPatternBody A ν u n n' a b) =
      ∑ u : FreeDraw ν, (freeDrawLaw ν u : ℂ) *
        physicalPatternBody A ν (assembleAux ν u unused) n n' a b := by
  calc
    _ = ∑ u : P.Aux J, (ν.auxMass u : ℂ) *
        physicalPatternBody A ν (assembleAux ν (freeRestriction ν u) unused) n n' a b :=
      Finset.sum_congr rfl (fun u hu => congrArg (fun c => (ν.auxMass u : ℂ) * c)
        (physicalPatternBody_restrict A ν u unused n n' a b))
    _ = _ := sum_auxMass_free ν hV
      (fun u => physicalPatternBody A ν (assembleAux ν u unused) n n' a b)

theorem sum_pattern_labels_aux_free {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (hV : ∀ g, P.V g ≠ 0)
    (unused : SharedDraw ν) (n n' : ℤ) :
    (∑ u : P.Aux J, ∑ a : A.Labels, ∑ b : A.Labels,
      (ν.auxMass u : ℂ) * physicalPatternBody A ν u n n' a b) =
      ∑ u : FreeDraw ν, ∑ a : A.Labels, ∑ b : A.Labels,
        (freeDrawLaw ν u : ℂ) * physicalPatternBody A ν (assembleAux ν u unused) n n' a b := by
  calc
    _ = ∑ a : A.Labels, ∑ b : A.Labels, ∑ u : P.Aux J,
        (ν.auxMass u : ℂ) * physicalPatternBody A ν u n n' a b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ a : A.Labels, ∑ b : A.Labels, ∑ u : FreeDraw ν,
        (freeDrawLaw ν u : ℂ) * physicalPatternBody A ν (assembleAux ν u unused) n n' a b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact sum_pattern_aux_free A ν hV unused n n' a b
    _ = _ := by
      symm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]

/-- Exact raw graph pairing with only the designated free-label harmonic
laws. Its ban and signed displacement are preserved by the compression. -/
theorem pairing_free_expansion {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (hV : ∀ g, P.V g ≠ 0)
    (X : ℝ) (T : Finset ℤ) (f g : ℤ → ℂ) :
    A.pairing X (T.product Finset.univ) f (fun z => g z.1) =
      ∑ n ∈ dyad X, ∑ n' ∈ T,
        star (f n) * g n' * (P.markMass (J + F.ell) : ℂ) *
          ∑ v : Fin A.patternCount, ∑ u : FreeDraw (A.pattern v), ∑ a : A.Labels, ∑ b : A.Labels,
            (freeDrawLaw (A.pattern v) u : ℂ) *
              physicalPatternBody A (A.pattern v)
                (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV)) n n' a b := by
  rw [pairing_pattern_expansion]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro n' hn'
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  exact sum_pattern_labels_aux_free A (A.pattern v) hV
    (unusedAuxDraw (A.pattern v) hV) n n'

end Erdos821.P5Core
