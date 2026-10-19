module

public import Erdos408.Graph.Pattern
public import Erdos821.Blueprint.Transference
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

/-!
# Upstream's pairing for endpoints of the position alone

Upstream's `Model.pairing X t f g` pairs a function `f` of the position on the
dyad `[X, 2X)` with a function `g` of the state on `t`, through the
symmetrized kernel `physicalKernel`. For `f` the extension by zero of a
function on `S ⊆ [X, 2X)` (`extend`), `t = S' × (all labels)` (`targets`) and
`g` a function of the position:

* the average over slot permutations drops out, since the state mass is
  permutation invariant and both label sums are complete (`sum_physicalKernel`);
* so the pairing is the sum over patterns of `rawPairing` (`pairing_eq_sum`);
* and upstream's norms are the physical norms (`normOn_extend`,
  `normOn_targets`).
-/

@[expose] public section

namespace Erdos408.Graph

open Erdos821.Blueprint.Graph
open scoped Classical

variable {G : PrimeGroups}

/-- The extension of `f` from `S ⊆ ℕ` to `ℤ` by zero. -/
noncomputable def extend (S : Finset ℕ) (f : ℕ → ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n ∧ n.toNat ∈ S then f n.toNat else 0

/-- The states at the positions of `S'`, with all labels. -/
noncomputable def targets {F : FixedData} {J m : ℕ} (A : Model F G J m) (S' : Finset ℕ) :
    Finset A.State :=
  (S'.map Nat.castEmbedding) ×ˢ Finset.univ

/-! ### Permutations of the slots -/

/-- Permuting the slots of each group, as an equivalence of labels. -/
def actEquiv {M : ℕ} (π : G.Permutations M) : G.Labels M ≃ G.Labels M where
  toFun := G.act π
  invFun := G.act fun g => (π g)⁻¹
  left_inv a := by funext g i; simp [PrimeGroups.act]
  right_inv a := by funext g i; simp [PrimeGroups.act]

/-- Physical states are invariant under slot permutations. -/
lemma physical_act {M : ℕ} (π : G.Permutations M) (n : ℤ) (a : G.Labels M) :
    G.physical M n (G.act π a) ↔ G.physical M n a :=
  forall_congr' fun g => and_congr (EquivLike.injective_comp (π g) (a g))
    ((π g).surjective.forall (p := fun i => ((a g i).val : ℤ) ∣ n)).symm

/-- The state mass is invariant under slot permutations. -/
lemma stateMass_act {F : FixedData} {J m : ℕ} (A : Model F G J m)
    (π : G.Permutations (J + F.ell)) (n : ℤ) (a : G.Labels (J + F.ell)) :
    A.stateMass (n, G.act π a) = A.stateMass (n, a) := by
  simp only [Model.stateMass, physical_act]

/-- Against the state mass and complete label sums, the symmetrized kernel
pairs as the raw kernel. -/
lemma sum_physicalKernel {F : FixedData} {J m : ℕ} (A : Model F G J m) (n n' : ℤ) (s t : ℂ) :
    ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
        (A.stateMass (n, a) : ℂ) * s * A.physicalKernel false (n, a) (n', b) * t =
      ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
        (A.stateMass (n, a) : ℂ) * s * A.physicalRaw false (n, a) (n', b) * t := by
  -- each pair of permutations contributes the unpermuted sum
  have hperm : ∀ π τ : G.Permutations (J + F.ell),
      ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
          (A.stateMass (n, a) : ℂ) * s * A.physicalRaw false (n, G.act π a) (n', G.act τ b) * t =
        ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
          (A.stateMass (n, a) : ℂ) * s * A.physicalRaw false (n, a) (n', b) * t := by
    intro π τ
    calc _ = ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
          (A.stateMass (n, G.act π a) : ℂ) * s *
            A.physicalRaw false (n, G.act π a) (n', G.act τ b) * t := by
          simp only [stateMass_act]
      _ = ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
          (A.stateMass (n, a) : ℂ) * s * A.physicalRaw false (n, a) (n', G.act τ b) * t :=
          Equiv.sum_comp (actEquiv π) fun a => ∑ b : G.Labels (J + F.ell),
            (A.stateMass (n, a) : ℂ) * s * A.physicalRaw false (n, a) (n', G.act τ b) * t
      _ = _ := Finset.sum_congr rfl fun a _ => Equiv.sum_comp (actEquiv τ) fun b =>
          (A.stateMass (n, a) : ℂ) * s * A.physicalRaw false (n, a) (n', b) * t
  have hcard : ((Fintype.card (G.Permutations (J + F.ell)) : ℂ) ^ 2) ≠ 0 :=
    pow_ne_zero 2 (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  calc _ = ∑ ab : G.Labels (J + F.ell) × G.Labels (J + F.ell),
          ∑ πτ : G.Permutations (J + F.ell) × G.Permutations (J + F.ell),
            ((Fintype.card (G.Permutations (J + F.ell)) : ℂ) ^ 2)⁻¹ *
              ((A.stateMass (n, ab.1) : ℂ) * s *
                A.physicalRaw false (n, G.act πτ.1 ab.1) (n', G.act πτ.2 ab.2) * t) := by
        rw [← Fintype.sum_prod_type']
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [Model.physicalKernel, ← Fintype.sum_prod_type', Finset.mul_sum, Finset.mul_sum,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun πτ _ => ?_
        ring
    _ = ∑ πτ : G.Permutations (J + F.ell) × G.Permutations (J + F.ell),
          ((Fintype.card (G.Permutations (J + F.ell)) : ℂ) ^ 2)⁻¹ *
            ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
              (A.stateMass (n, a) : ℂ) * s *
                A.physicalRaw false (n, G.act πτ.1 a) (n', G.act πτ.2 b) * t := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun πτ _ => ?_
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        simp_rw [Finset.mul_sum]
    _ = _ := by
        simp_rw [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
          ← mul_assoc]
        rw [Nat.cast_mul, ← pow_two, mul_inv_cancel₀ hcard, one_mul]

/-! ### The pairing -/

/-- Upstream's pairing of `extend S f` with a function `g` of the position on
`targets S'` is the sum of the pattern pairings. -/
theorem pairing_eq_sum {F : FixedData} {J m : ℕ} (A : Model F G J m) (X : ℝ)
    (S S' : Finset ℕ) (f g : ℕ → ℂ) (hS : ∀ n ∈ S, X ≤ n ∧ (n : ℝ) < 2 * X) :
    A.pairing X (targets A S') (extend S f) (fun z => g z.1.toNat) =
      ∑ v, rawPairing A v S S' f g := by
  unfold Model.pairing
  -- the positions of the dyad outside `S` do not contribute
  rw [← Finset.sum_subset (M := ℂ) (s₁ := S.map Nat.castEmbedding)]
  rotate_left
  · intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hn
    obtain ⟨h₁, h₂⟩ := hS k hk
    rw [Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]
    exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
  · intro n _ hn
    have : extend S f n = 0 := by
      refine ite_eq_right fun h => hn (Finset.mem_map.mpr ⟨n.toNat, h.2, ?_⟩)
      simp [Int.toNat_of_nonneg h.1]
    simp [this]
  rw [Finset.sum_map]
  calc _ = ∑ n ∈ S, ∑ n' ∈ S', ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
        (A.stateMass ((n : ℤ), a) : ℂ) * star (f n) *
          A.physicalKernel false ((n : ℤ), a) ((n' : ℤ), b) * g n' := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hf : extend S f (Nat.castEmbedding n) = f n := by
          simp [extend, hn]
        rw [hf]
        unfold targets
        simp_rw [Finset.sum_product, Finset.sum_map]
        exact Finset.sum_comm
    _ = ∑ n ∈ S, ∑ n' ∈ S', ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
        (A.stateMass ((n : ℤ), a) : ℂ) * star (f n) *
          A.physicalRaw false ((n : ℤ), a) ((n' : ℤ), b) * g n' :=
        Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ =>
          sum_physicalKernel A n n' _ _
    _ = ∑ n ∈ S, ∑ a : G.Labels (J + F.ell), ∑ n' ∈ S', ∑ b : G.Labels (J + F.ell), ∑ v,
        (A.stateMass ((n : ℤ), a) : ℂ) * star (f n) *
          patternRaw A v ((n : ℤ), a) ((n' : ℤ), b) * g n' := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_comm]
        simp_rw [physicalRaw_eq_sum, Finset.mul_sum, Finset.sum_mul]
    _ = _ := by
        symm
        unfold rawPairing
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n' _ => ?_
        rw [Finset.sum_comm]

/-! ### Norms -/

/-- The state mass at a position, summed over labels, is the number of
physical lists times `∏ V_g^{-M}`. -/
lemma sum_stateMass {F : FixedData} {J m : ℕ} (A : Model F G J m) (n : ℕ) :
    ∑ a : G.Labels (J + F.ell), A.stateMass ((n : ℤ), a) =
      (physicalLists G.primes (J + F.ell) n).card *
        ∏ g, (harmonicMass (G.primes g))⁻¹ ^ (J + F.ell) := by
  simp only [Model.stateMass, physical_iff]
  rw [sum_vals (fun p => if ∀ g, Function.Injective (p g) ∧ ∀ i, p g i ∣ n then
    G.markMass (J + F.ell) else 0), markMass_eq, physicalLists, Finset.card_filter,
    Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

/-- Upstream's norm of `extend S f` on the dyad is the physical norm. -/
lemma normOn_extend {F : FixedData} {J m : ℕ} (A : Model F G J m) (X : ℝ)
    (S : Finset ℕ) (f : ℕ → ℂ) (hS : ∀ n ∈ S, X ≤ n ∧ (n : ℝ) < 2 * X) :
    A.normOn ((Finset.Ico ⌈X⌉ ⌈2 * X⌉).product Finset.univ) (fun z => extend S f z.1) =
      Real.sqrt (physicalNormSq G.primes (J + F.ell) S f) := by
  unfold Model.normOn
  congr 1
  rw [Finset.product_eq_sprod, Finset.sum_product,
    ← Finset.sum_subset (M := ℝ) (s₁ := S.map Nat.castEmbedding)]
  rotate_left
  · intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hn
    obtain ⟨h₁, h₂⟩ := hS k hk
    rw [Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]
    exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
  · intro n _ hn
    have : extend S f n = 0 := by
      refine ite_eq_right fun h => hn (Finset.mem_map.mpr ⟨n.toNat, h.2, ?_⟩)
      simp [Int.toNat_of_nonneg h.1]
    simp [this]
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hf : extend S f (Nat.castEmbedding n) = f n := by
    simp [extend, hn]
  simp only [hf, ← Finset.sum_mul]
  rw [show (Nat.castEmbedding n : ℤ) = (n : ℤ) from rfl, sum_stateMass]
  ring

/-- Upstream's norm of a function of the position on `targets S'` is the
physical norm. -/
lemma normOn_targets {F : FixedData} {J m : ℕ} (A : Model F G J m) (S' : Finset ℕ)
    (g : ℕ → ℂ) :
    A.normOn (targets A S') (fun z => g z.1.toNat) =
      Real.sqrt (physicalNormSq G.primes (J + F.ell) S' g) := by
  unfold Model.normOn targets
  congr 1
  rw [Finset.sum_product, Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [show (Nat.castEmbedding n : ℤ) = (n : ℤ) from rfl, Int.toNat_natCast,
    ← Finset.sum_mul]
  rw [sum_stateMass]
  ring

end Erdos408.Graph
