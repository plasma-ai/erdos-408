import Erdos821.S34.MajorRetained
import Erdos821.S34.FiniteComparison
import Erdos821.S34.DiscardedCells
import Erdos821.S34.ProductLaws

set_option autoImplicit false
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

def occupiedProductCells (G : PrimeGroups) (k : Fin G.size → ℕ) (h : ℝ) : ℕ :=
  (Finset.univ.image (fun z : Tuple G k => cell h (product G k z))).card

theorem discarded_tuple_mass_bound (G : PrimeGroups) (k : Fin G.size → ℕ)
    (h ξ : ℝ) (hξ : 0 ≤ ξ) :
    (∑ z, if cellMass G k h (cell h (product G k z)) < ξ then tupleWeight G k z else 0) ≤
      (occupiedProductCells G k h : ℝ) * ξ := by
  exact discarded_cell_mass (tupleWeight G k) (fun z => cell h (product G k z)) ξ hξ

theorem comparisonScalar_zero_discarded (G : PrimeGroups) (a b : Fin G.size → ℕ)
    (Q : ℕ) (h ξ θ ζ : ℝ) (X : Tuple G a) (Y : Tuple G b)
    (hdisc : cellMass G a h (cell h (product G a X)) < ξ ∨
      cellMass G b h (cell h (product G b Y)) < ξ) :
    comparisonScalar G a b Q h ξ θ ζ X Y = 0 := by
  rcases hdisc with ha | hb
  · have hnot := not_le_of_gt ha
    simp [comparisonScalar, cellKernel, expect, hnot]
  · have hnot := not_le_of_gt hb
    simp [comparisonScalar, cellKernel, expect, hnot]

theorem comparison_error_scalar_pairing (G : PrimeGroups) (a b : Fin G.size → ℕ)
    (Q : ℕ) (h ξ θ ζ : ℝ) (f : Tuple G b → ℂ) (g : Tuple G a → ℂ) :
    comparisonError G a b Q h ξ θ ζ f g =
      ∑ X, ∑ Y, (tupleWeight G a X : ℂ) * (tupleWeight G b Y : ℂ) * star (f Y) * g X *
        (tuplePhase G a b θ ζ X Y - comparisonScalar G a b Q h ξ θ ζ X Y) := by
  simp only [comparisonError, comparisonScalar, tuplePhase, expect, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro X _
  apply Finset.sum_congr rfl
  intro Y _
  ring

theorem dyadic_major_comparison (hfourier : RationalFourierTask) (hind : PrimitiveInductionTask)
    (G : PrimeGroups) (a b : Fin G.size → ℕ) (Q r : ℕ) (u : ℤ)
    (h ξ U V S θ β ζ δ : ℝ) (hr : 1 ≤ r) (hrQ : r ≤ Q)
    (hh : 0 < h) (hh2 : h ≤ Real.log 2) (hξ : 0 < ξ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hS : 0 ≤ S)
    (hθ : θ = (u : ℝ) / r + β) (hβ : |β| * (U * V) ≤ 2 * S)
    (hδ : 0 ≤ δ) (hε1 : (Q : ℝ) ^ 2 * δ / ξ ≤ 1)
    (hMass : ∀ g, 0 < mass G g)
    (hPrimeA : ∀ g, 0 < a g → ∀ p ∈ G.primes g, Q < p)
    (hPrimeB : ∀ g, 0 < b g → ∀ p ∈ G.primes g, Q < p)
    (hGramA : ∀ j χ ψ, χ ∈ primitiveCharacters Q → ψ ∈ primitiveCharacters Q → χ ≠ ψ →
      ‖expect G a (fun z => if cell h (product G a z) = j then
        star (charValue χ (product G a z)) * charValue ψ (product G a z) else 0)‖ ≤ δ)
    (hGramB : ∀ j χ ψ, χ ∈ primitiveCharacters Q → ψ ∈ primitiveCharacters Q → χ ≠ ψ →
      ‖expect G b (fun z => if cell h (product G b z) = j then
        star (charValue χ (product G b z)) * charValue ψ (product G b z) else 0)‖ ≤ δ)
    (f : Tuple G b → ℂ) (g : Tuple G a → ℂ)
    (hg : ∀ X, g X ≠ 0 → U ≤ (product G a X : ℝ) ∧ (product G a X : ℝ) ≤ 2 * U)
    (hf : ∀ Y, f Y ≠ 0 → V ≤ (product G b Y : ℝ) ∧ (product G b Y : ℝ) ≤ 2 * V) :
    ‖comparisonError G a b Q h ξ θ ζ f g‖ ≤
      (Real.sqrt (((occupiedProductCells G a h : ℝ) + occupiedProductCells G b h) * ξ) +
        (Q : ℝ) ^ 4 * (2 * h * (|ζ| + 64 * Real.pi * S)) +
        3 * ((Q : ℝ) ^ 2 * δ / ξ) * Real.sqrt (Q : ℝ)) * tupleNorm G b f * tupleNorm G a g := by
  let EA := fun X : Tuple G a => cellMass G a h (cell h (product G a X)) < ξ
  let EB := fun Y : Tuple G b => cellMass G b h (cell h (product G b Y)) < ξ
  let valid := fun X : Tuple G a => fun Y : Tuple G b =>
    (U ≤ (product G a X : ℝ) ∧ (product G a X : ℝ) ≤ 2 * U) ∧
    (V ≤ (product G b Y : ℝ) ∧ (product G b Y : ℝ) ≤ 2 * V)
  let raw := fun X Y => if valid X Y then tuplePhase G a b θ ζ X Y else 0
  let comp := fun X Y => if valid X Y then comparisonScalar G a b Q h ξ θ ζ X Y else 0
  let ε := (Q : ℝ) ^ 2 * δ / ξ
  let E := (Q : ℝ) ^ 4 * (2 * h * (|ζ| + 64 * Real.pi * S)) + 3 * ε * Real.sqrt (Q : ℝ)
  have hε : 0 ≤ ε := div_nonneg (mul_nonneg (sq_nonneg _) hδ) hξ.le
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have cop (k : Fin G.size → ℕ) (hp : ∀ g, 0 < k g → ∀ p ∈ G.primes g, Q < p)
      (s : ℕ) (hs : 1 ≤ s) (hsQ : s ≤ Q) (z : Tuple G k) : Nat.Coprime (product G k z) s := by
    apply tuple_product_coprime G k s (by omega) _ z
    intro g hg p hpg
    exact lt_of_le_of_lt hsQ (hp g hg p hpg)
  have repA (X : Tuple G a) (hX : ¬ EA X) (χ : CharacterIndex Q) (hχ : χ ∈ primitiveCharacters Q) :
      ‖cellApply G a Q h ξ (fun D => charValue χ (product G a D)) X - charValue χ (product G a X)‖ ≤ ε := by
    apply cell_character_reproduction G a Q h ξ δ hξ hδ χ hχ
    · intro D
      have hl := χ.1.isLt
      exact cop a hPrimeA (χ.1.val + 1) (by omega) (by omega) D
    · intro j _ ψ hψ hne
      exact hGramA j ψ χ hψ hχ hne
    · exact le_of_not_gt hX
  have repB (Y : Tuple G b) (hY : ¬ EB Y) (χ : CharacterIndex Q) (hχ : χ ∈ primitiveCharacters Q) :
      ‖cellApply G b Q h ξ (fun D => charValue χ (product G b D)) Y - charValue χ (product G b Y)‖ ≤ ε := by
    apply cell_character_reproduction G b Q h ξ δ hξ hδ χ hχ
    · intro D
      have hl := χ.1.isLt
      exact cop b hPrimeB (χ.1.val + 1) (by omega) (by omega) D
    · intro j _ ψ hψ hne
      exact hGramB j ψ χ hψ hχ hne
    · exact le_of_not_gt hY
  have hraw (X : Tuple G a) (Y : Tuple G b) : ‖raw X Y‖ ≤ 1 := by
    dsimp [raw]
    split_ifs
    · simp only [tuplePhase, norm_mul, Erdos821.P5Core.norm_mellin, norm_e, one_mul, le_refl]
    · simp
  have hzero (X : Tuple G a) (Y : Tuple G b) (hd : EA X ∨ EB Y) : comp X Y = 0 := by
    dsimp [comp]
    split_ifs
    · exact comparisonScalar_zero_discarded G a b Q h ξ θ ζ X Y hd
    · rfl
  have hpoint (X : Tuple G a) (Y : Tuple G b) (hX : ¬ EA X) (hY : ¬ EB Y) : ‖raw X Y - comp X Y‖ ≤ E := by
    by_cases hv : valid X Y
    · simp only [raw, comp, if_pos hv]
      have ht := major_retained_comparison hfourier hind G a b Q r u h ξ U V S θ β ζ ε hr hrQ
        hh hh2 hξ (by linarith) (by linarith) hS hθ hβ hε hε1 X Y hv.1 hv.2
        (cop a hPrimeA r hr hrQ) (cop b hPrimeB r hr hrQ) (repA X hX) (repB Y hY)
      apply ht.trans
      have htot : (r.totient : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (Nat.totient_le r).trans hrQ
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htot) (by positivity))
    · simp only [raw, comp, if_neg hv, sub_self, norm_zero]
      exact hE
  have hprobA : (∑ X, tupleWeight G a X) = 1 := tuple_law_sum (coreGroups G) a hMass
  have hprobB : (∑ Y, tupleWeight G b Y) = 1 := tuple_law_sum (coreGroups G) b hMass
  have hwA := Erdos821.S34.Proofs.tupleWeight_nonneg (coreGroups G) a
  have hwB := Erdos821.S34.Proofs.tupleWeight_nonneg (coreGroups G) b
  have ht := finite_comparison_of_pointwise (tupleWeight G a) (tupleWeight G b) hwA hwB hprobA hprobB
    EA EB raw comp E hE hraw hzero hpoint f g
  have heq : comparisonError G a b Q h ξ θ ζ f g =
      ∑ X, ∑ Y, (tupleWeight G a X : ℂ) * (tupleWeight G b Y : ℂ) * star (f Y) * g X * (raw X Y - comp X Y) := by
    rw [comparison_error_scalar_pairing]
    apply Finset.sum_congr rfl
    intro X _
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hx : U ≤ (product G a X : ℝ) ∧ (product G a X : ℝ) ≤ 2 * U
    · by_cases hy : V ≤ (product G b Y : ℝ) ∧ (product G b Y : ℝ) ≤ 2 * V
      · simp [raw, comp, valid, hx, hy]
      · have hz : f Y = 0 := by by_contra hn; exact hy (hf Y hn)
        simp [hz]
    · have hz : g X = 0 := by by_contra hn; exact hx (hg X hn)
      simp [hz]
  rw [← heq] at ht
  change ‖comparisonError G a b Q h ξ θ ζ f g‖ ≤
    (Real.sqrt ((∑ X, if EA X then tupleWeight G a X else 0) + (∑ Y, if EB Y then tupleWeight G b Y else 0)) + E) *
      tupleNorm G a g * tupleNorm G b f at ht
  have hmass := add_le_add (discarded_tuple_mass_bound G a h ξ hξ.le) (discarded_tuple_mass_bound G b h ξ hξ.le)
  have hmass' : ((∑ X, if EA X then tupleWeight G a X else 0) + (∑ Y, if EB Y then tupleWeight G b Y else 0)) ≤
      ((occupiedProductCells G a h : ℝ) + occupiedProductCells G b h) * ξ := by
    convert hmass using 1 <;> ring
  have hn := ht.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (add_le_add (Real.sqrt_le_sqrt hmass') (le_refl E)) (tuple_norm_nonneg G a g))
    (tuple_norm_nonneg G b f))
  convert hn using 1 <;> dsimp [E, ε] <;> ring

end
end Erdos821.S34Core
