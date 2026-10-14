import Erdos821.P5.LabelActions

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

def physicalRootBlock {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (absolute : Bool) (n n' : ℤ) : ℂ :=
  ∑ a : A.Labels, ∑ b : A.Labels,
    (A.stateMass (n, a) : ℂ) * A.physicalKernel absolute (n, a) (n', b)

def rawRootBlock {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (absolute : Bool) (n n' : ℤ) : ℂ :=
  ∑ a : A.Labels, ∑ b : A.Labels,
    (A.stateMass (n, a) : ℂ) * A.physicalRaw absolute (n, a) (n', b)

theorem rawRootBlock_act {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (absolute : Bool) (n n' : ℤ)
    (π τ : P.Permutations (J + F.ell)) :
    (∑ a : A.Labels, ∑ b : A.Labels, (A.stateMass (n, a) : ℂ) *
      A.physicalRaw absolute (n, P.act π a) (n', P.act τ b)) =
        rawRootBlock A absolute n n' := by
  calc
    _ = ∑ a : A.Labels, ∑ b : A.Labels, (A.stateMass (n, P.act π a) : ℂ) *
        A.physicalRaw absolute (n, P.act π a) (n', P.act τ b) := by
      simp_rw [stateMass_act]
    _ = ∑ a : A.Labels, ∑ b : A.Labels, (A.stateMass (n, a) : ℂ) *
        A.physicalRaw absolute (n, a) (n', P.act τ b) :=
      sum_labels_act P π (fun a : A.Labels => ∑ b : A.Labels,
        (A.stateMass (n, a) : ℂ) * A.physicalRaw absolute (n, a) (n', P.act τ b))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      exact sum_labels_act P τ (fun b : A.Labels =>
        (A.stateMass (n, a) : ℂ) * A.physicalRaw absolute (n, a) (n', b))

/-- Summing every endpoint list removes the two independent permutation
projections, with their exact normalization. -/
theorem physicalRootBlock_eq_raw {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (absolute : Bool) (n n' : ℤ) :
    physicalRootBlock A absolute n n' = rawRootBlock A absolute n n' := by
  let N : ℂ := Fintype.card (P.Permutations (J + F.ell))
  have hN : N ≠ 0 := by
    have hcard : 0 < Fintype.card (P.Permutations (J + F.ell)) :=
      Fintype.card_pos_iff.mpr ⟨fun g => Equiv.refl _⟩
    dsimp [N]
    exact_mod_cast Nat.ne_of_gt hcard
  have hexpand : physicalRootBlock A absolute n n' = (N ^ 2)⁻¹ *
      ∑ a : A.Labels, ∑ b : A.Labels,
        ∑ π : P.Permutations (J + F.ell), ∑ τ : P.Permutations (J + F.ell),
          (A.stateMass (n, a) : ℂ) * A.physicalRaw absolute (n, P.act π a) (n', P.act τ b) := by
    unfold physicalRootBlock Model.physicalKernel
    change (∑ a : A.Labels, ∑ b : A.Labels, (A.stateMass (n, a) : ℂ) *
      ((N ^ 2)⁻¹ * ∑ π, ∑ τ, A.physicalRaw absolute (n, P.act π a) (n', P.act τ b))) = _
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro π hπ
    apply Finset.sum_congr rfl
    intro τ hτ
    ring
  rw [hexpand, sum_four_swap_blocks]
  simp_rw [rawRootBlock_act]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change (N ^ 2)⁻¹ * (N * (N * rawRootBlock A absolute n n')) = _
  field_simp [hN] <;> ring

theorem rawRootBlock_eq_markMass {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (absolute : Bool) (n n' : ℤ) :
    rawRootBlock A absolute n n' = (P.markMass (J + F.ell) : ℂ) *
      ∑ a : A.Labels, ∑ b : A.Labels, A.physicalRaw absolute (n, a) (n', b) := by
  unfold rawRootBlock
  simp_rw [stateMass_mul_physicalRaw, ← Finset.mul_sum]

/-- Exact finite pairing expansion for endpoint vectors depending only on
the integer root, before any transference or analytic estimate. -/
theorem pairing_root_raw {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (X : ℝ) (T : Finset ℤ) (f g : ℤ → ℂ) :
    A.pairing X (T.product Finset.univ) f (fun z => g z.1) =
      ∑ n ∈ dyad X, ∑ n' ∈ T,
        star (f n) * g n' * (P.markMass (J + F.ell) : ℂ) *
          ∑ a : A.Labels, ∑ b : A.Labels, A.physicalRaw false (n, a) (n', b) := by
  unfold Model.pairing
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  change (∑ z ∈ T.product (Finset.univ : Finset A.Labels), ∑ a : A.Labels,
    (A.stateMass (n, a) : ℂ) * star (f n) * A.physicalKernel false (n, a) z * g z.1) = _
  simp only [Finset.product_eq_sprod]
  rw [Finset.sum_product T (Finset.univ : Finset A.Labels)
    (fun z : A.State => ∑ a : A.Labels,
      (A.stateMass (n, a) : ℂ) * star (f n) * A.physicalKernel false (n, a) z * g z.1)]
  apply Finset.sum_congr rfl
  intro n' hn'
  rw [Finset.sum_comm]
  have hblock : (∑ a : A.Labels, ∑ b : A.Labels,
      (A.stateMass (n, a) : ℂ) * star (f n) * A.physicalKernel false (n, a) (n', b) * g n') =
        (star (f n) * g n') * physicalRootBlock A false n n' := by
    unfold physicalRootBlock
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hblock, physicalRootBlock_eq_raw, rawRootBlock_eq_markMass]
  ring

end Erdos821.P5Core
