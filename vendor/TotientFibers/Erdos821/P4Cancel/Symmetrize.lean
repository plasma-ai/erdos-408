import Erdos821.P4Probe.RawAssembly

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Cancel
open Blueprint.Graph P4Probe

noncomputable section

variable {P : PrimeGroups} {M : ℕ}

lemma actBig_inv_actBig (π : P.BigPermutations M) (a : P.BigLabels M) :
    P.actBig π⁻¹ (P.actBig π a) = a := by
  funext g i
  simp [PrimeGroups.actBig]

lemma actBig_actBig_inv (π : P.BigPermutations M) (a : P.BigLabels M) :
    P.actBig π (P.actBig π⁻¹ a) = a := by
  funext g i
  simp [PrimeGroups.actBig]

lemma actBig_actBig (π ρ : P.BigPermutations M) (a : P.BigLabels M) :
    P.actBig π (P.actBig ρ a) = P.actBig (ρ * π) a := by
  funext g i
  simp [PrimeGroups.actBig]

/-- The action of one permutation tuple, as an equivalence of label tuples. -/
def actEquiv (π : P.BigPermutations M) : P.BigLabels M ≃ P.BigLabels M where
  toFun := P.actBig π
  invFun := P.actBig π⁻¹
  left_inv a := actBig_inv_actBig π a
  right_inv a := actBig_actBig_inv π a

/-- Permutation average of a test. -/
def symTest (P : PrimeGroups) (M : ℕ) (f : P.BigLabels M → ℂ) (a : P.BigLabels M) : ℂ :=
  ((Fintype.card (P.BigPermutations M) : ℂ))⁻¹ * ∑ π : P.BigPermutations M, f (P.actBig π a)

lemma symTest_invariant (f : P.BigLabels M → ℂ) (ρ : P.BigPermutations M)
    (a : P.BigLabels M) : symTest P M f (P.actBig ρ a) = symTest P M f a := by
  unfold symTest
  congr 1
  simp_rw [actBig_actBig]
  exact Fintype.sum_equiv (Equiv.mulLeft ρ) _ _ (fun π => rfl)

lemma pair_transport (K : P.BigLabels M → P.BigLabels M → ℂ)
    (f g : P.BigLabels M → ℂ) (π τ : P.BigPermutations M) :
    (∑ a, ∑ b, (P.idealMass a : ℂ) * star (f a) * K (P.actBig π a) (P.actBig τ b) * g b) =
      ∑ a, ∑ b, (P.idealMass a : ℂ) * star (f (P.actBig π⁻¹ a)) * K a b *
        g (P.actBig τ⁻¹ b) := by
  apply Fintype.sum_equiv (actEquiv π)
  intro a
  apply Fintype.sum_equiv (actEquiv τ)
  intro b
  simp only [actEquiv, Equiv.coe_fn_mk, idealMass_act, actBig_inv_actBig]

lemma sum4_swap {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (φ : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ x, ∑ y, φ a b x y) = ∑ x, ∑ y, ∑ a, ∑ b, φ a b x y := by
  calc
    _ = ∑ a, ∑ x, ∑ b, ∑ y, φ a b x y :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ x, ∑ a, ∑ b, ∑ y, φ a b x y := Finset.sum_comm
    _ = ∑ x, ∑ a, ∑ y, ∑ b, φ a b x y :=
      Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
    _ = _ := Finset.sum_congr rfl (fun x _ => Finset.sum_comm)

lemma star_symTest (f : P.BigLabels M → ℂ) (a : P.BigLabels M) :
    star (symTest P M f a) =
      ((Fintype.card (P.BigPermutations M) : ℂ))⁻¹ *
        ∑ π : P.BigPermutations M, star (f (P.actBig π a)) := by
  unfold symTest
  rw [star_mul, star_sum, mul_comm]
  congr 1
  simp

lemma symmetrized_pair (K : P.BigLabels M → P.BigLabels M → ℂ)
    (f g : P.BigLabels M → ℂ) :
    idealFullPair (fun a b => ((Fintype.card (P.BigPermutations M) : ℂ) ^ 2)⁻¹ *
        ∑ π : P.BigPermutations M, ∑ τ : P.BigPermutations M,
          K (P.actBig π a) (P.actBig τ b)) f g =
      idealFullPair K (symTest P M f) (symTest P M g) := by
  have hc2 : ((Fintype.card (P.BigPermutations M) : ℂ) ^ 2)⁻¹ =
      ((Fintype.card (P.BigPermutations M) : ℂ))⁻¹ *
        ((Fintype.card (P.BigPermutations M) : ℂ))⁻¹ := by
    rw [sq, mul_inv]
  set c : ℂ := ((Fintype.card (P.BigPermutations M) : ℂ))⁻¹ with hc
  have hL : idealFullPair (fun a b => ((Fintype.card (P.BigPermutations M) : ℂ) ^ 2)⁻¹ *
        ∑ π : P.BigPermutations M, ∑ τ : P.BigPermutations M,
          K (P.actBig π a) (P.actBig τ b)) f g =
      ∑ a, ∑ b, ∑ π : P.BigPermutations M, ∑ τ : P.BigPermutations M,
        c * c * ((P.idealMass a : ℂ) * star (f a) * K (P.actBig π a) (P.actBig τ b) * g b) := by
    unfold idealFullPair
    rw [hc2]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro π _
    apply Finset.sum_congr rfl; intro τ _
    ring
  have hR : idealFullPair K (symTest P M f) (symTest P M g) =
      ∑ a, ∑ b, ∑ π : P.BigPermutations M, ∑ τ : P.BigPermutations M,
        c * c * ((P.idealMass a : ℂ) * star (f (P.actBig π a)) * K a b *
          g (P.actBig τ b)) := by
    unfold idealFullPair
    simp only [star_symTest]
    unfold symTest
    rw [← hc]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro π _
    apply Finset.sum_congr rfl; intro τ _
    ring
  rw [hL, hR]
  conv_lhs => rw [sum4_swap]
  conv_rhs => rw [sum4_swap]
  have hX : ∀ π τ : P.BigPermutations M,
      (∑ a, ∑ b, c * c * ((P.idealMass a : ℂ) * star (f a) *
        K (P.actBig π a) (P.actBig τ b) * g b)) =
      ∑ a, ∑ b, c * c * ((P.idealMass a : ℂ) * star (f (P.actBig π⁻¹ a)) * K a b *
          g (P.actBig τ⁻¹ b)) := by
    intro π τ
    have h := congrArg (fun z => c * c * z) (pair_transport K f g π τ)
    simpa only [Finset.mul_sum] using h
  refine (Finset.sum_congr rfl (fun π _ => Finset.sum_congr rfl (fun τ _ => hX π τ))).trans ?_
  apply Fintype.sum_equiv (Equiv.inv (P.BigPermutations M))
  intro π
  apply Fintype.sum_equiv (Equiv.inv (P.BigPermutations M))
  intro τ
  rfl

lemma symTest_sqNorm_le (hV : ∀ g, 0 < P.V g) (f : P.BigLabels M → ℂ) :
    (∑ a, P.idealMass a * ‖symTest P M f a‖ ^ 2) ≤ ∑ a, P.idealMass a * ‖f a‖ ^ 2 := by
  set N : ℕ := Fintype.card (P.BigPermutations M) with hN
  have hNpos : (0 : ℝ) < N := by
    rw [hN]; exact_mod_cast Fintype.card_pos
  have hpt : ∀ a, ‖symTest P M f a‖ ^ 2 ≤
      (N : ℝ)⁻¹ * ∑ π : P.BigPermutations M, ‖f (P.actBig π a)‖ ^ 2 := by
    intro a
    have h1 : ‖symTest P M f a‖ ≤ (N : ℝ)⁻¹ * ∑ π : P.BigPermutations M, ‖f (P.actBig π a)‖ := by
      unfold symTest
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    have h2 : (∑ π : P.BigPermutations M, ‖f (P.actBig π a)‖) ^ 2 ≤
        (N : ℝ) * ∑ π : P.BigPermutations M, ‖f (P.actBig π a)‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (P.BigPermutations M)))
        (f := fun π => ‖f (P.actBig π a)‖)
      simpa [hN] using this
    calc ‖symTest P M f a‖ ^ 2
        ≤ ((N : ℝ)⁻¹ * ∑ π : P.BigPermutations M, ‖f (P.actBig π a)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = (N : ℝ)⁻¹ ^ 2 * (∑ π : P.BigPermutations M, ‖f (P.actBig π a)‖) ^ 2 := by ring
      _ ≤ (N : ℝ)⁻¹ ^ 2 * ((N : ℝ) * ∑ π : P.BigPermutations M, ‖f (P.actBig π a)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by field_simp
  have hmass : ∀ a, 0 ≤ P.idealMass a := fun a => (idealMass_pos P M hV a).le
  calc (∑ a, P.idealMass a * ‖symTest P M f a‖ ^ 2)
      ≤ ∑ a, P.idealMass a * ((N : ℝ)⁻¹ * ∑ π : P.BigPermutations M, ‖f (P.actBig π a)‖ ^ 2) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hpt a) (hmass a))
    _ = (N : ℝ)⁻¹ * ∑ π : P.BigPermutations M, ∑ a, P.idealMass a * ‖f (P.actBig π a)‖ ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro π _
        apply Finset.sum_congr rfl; intro a _
        ring
    _ = (N : ℝ)⁻¹ * ∑ _π : P.BigPermutations M, ∑ a, P.idealMass a * ‖f a‖ ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl; intro π _
        apply Fintype.sum_equiv (actEquiv π)
        intro a
        simp only [actEquiv, Equiv.coe_fn_mk, idealMass_act]
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]
        field_simp

lemma symTest_norm_le (hV : ∀ g, 0 < P.V g) (f : P.BigLabels M → ℂ) :
    idealVectorNorm P M (symTest P M f) ≤ idealVectorNorm P M f :=
  Real.sqrt_le_sqrt (symTest_sqNorm_le hV f)

end
end Erdos821.P4Cancel
