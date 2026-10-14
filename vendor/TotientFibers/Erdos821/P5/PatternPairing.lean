module

public import Erdos821.P5.RootPairing
public import Erdos821.P5.FreeDraws

@[expose] public section

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

def physicalPatternBody {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (u : P.Aux J)
    (n n' : ℤ) (a b : A.Labels) : ℂ :=
  if (P.physical (J + F.ell) n a ∧ P.physical (J + F.ell) n' b) ∧
      ν.compatible a b ∧ ν.ban a b u ∧ n' = n + A.k * (ν.D a u : ℤ) then
    ((ν.physicalTargetMass * A.damping n * A.damping n' : ℝ) : ℂ) *
      ν.coefficient (P.restrictBig a) (P.restrictBig b) (fun g => u g.val) *
      imaginaryPower (ν.D a u) A.zeta
  else 0

theorem physicalRaw_false_eq_patterns {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n n' : ℤ) (a b : A.Labels) :
    A.physicalRaw false (n, a) (n', b) =
      ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
        ((A.pattern v).auxMass u : ℂ) * physicalPatternBody A (A.pattern v) u n n' a b := by
  by_cases hp : P.physical (J + F.ell) n a ∧ P.physical (J + F.ell) n' b
  · simp only [Model.physicalRaw, hp, and_self, if_true, Bool.false_eq_true, if_false]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    unfold physicalPatternBody
    simp only [hp, true_and]
    split_ifs <;> simp only [mul_zero, Complex.ofReal_mul] <;> ring
  · simp only [Model.physicalRaw, hp, if_false, physicalPatternBody, false_and,
      mul_zero, Finset.sum_const_zero]

/-- The actual symmetrized graph pairing is an exact sum of its physical
patterns and auxiliary harmonic laws when both endpoints depend only on roots. -/
theorem pairing_pattern_expansion {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (X : ℝ) (T : Finset ℤ) (f g : ℤ → ℂ) :
    A.pairing X (T.product Finset.univ) f (fun z => g z.1) =
      ∑ n ∈ dyad X, ∑ n' ∈ T,
        star (f n) * g n' * (P.markMass (J + F.ell) : ℂ) *
          ∑ v : Fin A.patternCount, ∑ u : P.Aux J, ∑ a : A.Labels, ∑ b : A.Labels,
            ((A.pattern v).auxMass u : ℂ) * physicalPatternBody A (A.pattern v) u n n' a b := by
  rw [pairing_root_raw]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro n' hn'
  simp_rw [physicalRaw_false_eq_patterns]
  rw [sum_four_swap_blocks]

theorem freeProduct_aux_ext {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (u v : P.Aux J)
    (hu : ∀ g i, i ∈ ν.changed g → u g i = v g i) : freeProduct ν u = freeProduct ν v := by
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  rw [hu g i hi]

theorem pattern_D_aux_ext {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (u v : P.Aux J)
    (hu : ∀ g i, i ∈ ν.changed g → u g i = v g i) : ν.D a u = ν.D a v := by
  rw [pattern_D_split, pattern_D_split, freeProduct_aux_ext ν u v hu]

theorem pattern_ban_aux_ext {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a b : P.Labels (J + ell)) (u v : P.Aux J)
    (hu : ∀ g i, i ∈ ν.changed g → u g i = v g i) : ν.ban a b u ↔ ν.ban a b v := by
  unfold Pattern.ban
  constructor <;> intro h g i hi j
  · rw [← hu g i hi]
    exact h g i hi j
  · rw [hu g i hi]
    exact h g i hi j

theorem physicalPatternBody_aux_ext {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (u v : P.Aux J)
    (n n' : ℤ) (a b : A.Labels) (hu : ∀ g i, i ∈ ν.changed g → u g i = v g i) :
    physicalPatternBody A ν u n n' a b = physicalPatternBody A ν v n n' a b := by
  have hc := ν.coefficient_aux_ext (P.restrictBig a) (P.restrictBig b)
    (fun g => u g.val) (fun g => v g.val) (fun g i hi => hu g.val i hi)
  simp only [physicalPatternBody, pattern_ban_aux_ext ν a b u v hu,
    pattern_D_aux_ext ν a u v hu, hc]

end Erdos821.P5Core
