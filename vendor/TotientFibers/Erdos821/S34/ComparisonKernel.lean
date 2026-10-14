import Erdos821.S34.AtomProof
import Erdos821.S34.CharacterCellBridge
import Erdos821.S34.RationalCharacterBridge
import Erdos821.S34.ComparisonGeometry
import Erdos821.S34.MajorPrecision
import Erdos821.S34.MinorDyadic
import Erdos821.S34.DyadicPartition
import Erdos821.S34.DirichletApproximation

set_option autoImplicit false
open scoped BigOperators Classical
open Filter

namespace Erdos821.Blueprint.Analytic
noncomputable section
open Erdos821.S34Core

theorem comparison_kernel_proof : Erdos821.Blueprint.Analytic.comparison_kernel_statement := by
  intro P m A C₄ hA hC₄
  have hd : 0 < P.d := by rcases P.ordered with ⟨ha, hab, hbc, hcd, hd⟩; linarith
  let κ := atomExponent P m
  let B := A + 2 * (P.d + 1) + 20
  let q := comparisonPowerQ B κ P.d
  let hExp := comparisonPowerH B q C₄
  let ξExp := comparisonPowerXi B P.d hExp
  let DExp := comparisonPowerD B q ξExp
  have hκ : 0 ≤ κ := atomExponent_nonneg P m
  have hB : 0 < B := by dsimp [B]; linarith
  have hq1 : 1 ≤ q := by dsimp [q, comparisonPowerQ]; linarith
  have hq : 0 < q := by linarith
  have hhExp : 0 < hExp := by dsimp [hExp, comparisonPowerH]; linarith
  have hξExp : 0 < ξExp := by dsimp [ξExp, comparisonPowerXi]; linarith
  have hDExp : 0 < DExp := by dsimp [DExp, comparisonPowerD]; linarith
  obtain ⟨K, hK, hCharacter⟩ := characterCellTask_proof Blueprint.classical_inputs.harmonic P m q DExp hq hDExp
  let threshold := 3 + 60 * integerBilinearConstant + 3 * K + 2 * (1 + 64 * Real.pi)
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  refine ⟨q, hExp, ξExp, hq, hhExp, hξExp, ?_⟩
  filter_upwards [product_atom_bound_proof P m,
    cell_operator_norm_eventual P m q ξExp hq hξExp, hCharacter,
    eventually_product_cell_count P m hExp hhExp,
    eventually_product_dyad_count P m, eventually_product_dyad_scale P m q,
    eventually_dyad_denominator_log P m, eventually_big_prime_power P q,
    eventually_cell_width hExp hhExp, hL.eventually_ge_atTop threshold]
    with x hAtom hFrame hGram hCells hDyads hScales hLog hPrimes hWidth hx
  have hL3 : 3 ≤ L x := by dsimp [threshold] at hx; linarith [integerBilinearConstant_pos, Real.pi_pos]
  have hL1 : 1 ≤ L x := by linarith
  have hLp : 0 < L x := by linarith
  have hIntK : 60 * integerBilinearConstant ≤ L x := by dsimp [threshold] at hx; linarith [Real.pi_pos]
  have hCharK : 3 * K ≤ L x := by dsimp [threshold] at hx; linarith [integerBilinearConstant_pos, Real.pi_pos]
  have hπ : 2 * (1 + 64 * Real.pi) ≤ L x := by dsimp [threshold] at hx; linarith [integerBilinearConstant_pos]
  intro G hG a b ha hb θ ζ f g hζ
  let Q := ⌊L x ^ q⌋₊
  let h := L x ^ (-hExp)
  let ξ := L x ^ (-ξExp)
  let S := L x ^ q
  let δ := K * L x ^ (-DExp)
  have hQ : (Q : ℝ) ≤ L x ^ q := Nat.floor_le (Real.rpow_nonneg hLp.le _)
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hLp _
  have hδ : 0 ≤ δ := mul_nonneg hK.le (Real.rpow_nonneg hLp.le _)
  have hS : 0 < S := Real.rpow_pos_of_pos hLp _
  have hS1 : 1 ≤ S := Real.one_le_rpow hL1 hq.le
  have hρa (n : ℕ) (hn : 0 < n) : rho G a n ≤ L x ^ κ / n := hAtom G hG a ha n hn
  have hρb (n : ℕ) (hn : 0 < n) : rho G b n ≤ L x ^ κ / n := hAtom G hG b hb n hn
  have hMass (j : Fin G.size) : 0 < mass G j := P.positive.2.2.1.trans_le (hG.2.2.1 j).1
  have primeCap (k : Fin G.size → ℕ) (hk : bigSlots G k m) (j : Fin G.size)
      (hj : 0 < k j) (p : ℕ) (hp : p ∈ G.primes j) : Q < p := by
    have hs : j ∉ G.small := by intro hs; have hz := (hk.2 j).2 hs; omega
    have hjB : j ∈ G.big := by simp [PrimeGroups.big, hs]
    exact_mod_cast hQ.trans_lt (hPrimes G hG j hjB p hp)
  have Gram (k : Fin G.size → ℕ) (hk : bigSlots G k m) (j : ℤ) (χ ψ : CharacterIndex Q)
      (hχ : χ ∈ primitiveCharacters Q) (hψ : ψ ∈ primitiveCharacters Q) (hne : χ ≠ ψ) :
      ‖expect G k (fun z => if cell h (product G k z) = j then
        star (charValue χ (product G k z)) * charValue ψ (product G k z) else 0)‖ ≤ δ :=
    hGram G hG k hk Q h j χ ψ hQ hWidth.1 hχ hψ hne
  have hCA : (occupiedProductCells G a h : ℝ) ≤ L x ^ (P.d + 1 + hExp) := hCells G hG a ha
  have hCB : (occupiedProductCells G b h : ℝ) ≤ L x ^ (P.d + 1 + hExp) := hCells G hG b hb
  have hmajorPower := major_power_precision (L x) K B q P.d C₄ hExp ξExp DExp ζ
    (occupiedProductCells G a h) (occupiedProductCells G b h) Q
    hL3 hK hCharK hπ hB.le hq.le hd.le hC₄ rfl rfl rfl hQ hζ hCA hCB
  have hE : 0 ≤ L x ^ (-B) := Real.rpow_nonneg hLp.le _
  have hdyadic : ∀ j ∈ occupiedDyads G a, ∀ k ∈ occupiedDyads G b,
      ‖comparisonError G a b Q h ξ θ ζ (dyadRestriction G b k f) (dyadRestriction G a j g)‖ ≤
        L x ^ (-B) * tupleNorm G b (dyadRestriction G b k f) * tupleNorm G a (dyadRestriction G a j g) := by
    intro j hj k hk
    obtain ⟨X, _, hX⟩ := Finset.mem_image.mp hj
    obtain ⟨Y, _, hY⟩ := Finset.mem_image.mp hk
    let U := dyadScale j
    let V := dyadScale k
    have hU : L x ^ q ≤ U := by simpa only [hX, U] using hScales G hG a ha X
    have hV : L x ^ q ≤ V := by simpa only [hY, V] using hScales G hG b hb Y
    have hU1 : 1 ≤ U := hS1.trans hU
    have hV1 : 1 ≤ V := hS1.trans hV
    have hUp : 0 < U := hS.trans_le hU
    have hVp : 0 < V := hS.trans_le hV
    have hUV : 0 < U * V := mul_pos hUp hVp
    have hZS : 1 ≤ U * V / S := by
      apply (le_div_iff₀ hS).mpr
      have hm := mul_le_mul hU hV hS.le hUp.le
      nlinarith
    obtain ⟨u, r, β, hr, hcop, hrS, hθ, hβ, hβZ⟩ := scaled_dirichlet_approximation θ (U * V) S hUV hS hZS
    have hrR : 1 ≤ (r : ℝ) := by exact_mod_cast hr
    have hrp : 0 < (r : ℝ) := by linarith
    have hf := dyadRestriction_support G b k f
    have hg := dyadRestriction_support G a j g
    by_cases hrQ : r ≤ Q
    · have hβZ' : |β| * (U * V) ≤ 2 * S := by
        apply hβZ.trans
        exact (div_le_iff₀ hrp).mpr (by nlinarith)
      have hm := dyadic_major_comparison rationalFourierTask_proof primitiveInductionTask_proof
        G a b Q r u h ξ U V S θ β ζ δ hr hrQ hWidth.1 hWidth.2 hξ
        hU1 hV1 hS.le hθ hβZ' hδ hmajorPower.1 hMass
        (primeCap a ha) (primeCap b hb) (Gram a ha) (Gram b hb)
        (dyadRestriction G b k f) (dyadRestriction G a j g) hg hf
      exact hm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmajorPower.2 (tuple_norm_nonneg G b (dyadRestriction G b k f)))
        (tuple_norm_nonneg G a (dyadRestriction G a j g)))
    · have hrQ' : (Q : ℝ) < r := by exact_mod_cast (Nat.lt_of_not_ge hrQ)
      have hrUV : (r : ℝ) ≤ U * V := hrS.trans (div_le_self hUV.le hS1)
      have hlog : Real.log (2 * r) ≤ L x ^ (P.d + 1) := by
        have ht := hLog G hG a b ha hb X Y r hrR
        apply ht
        simpa only [hX, hY, U, V] using hrUV
      have hm := dyadic_comparison_bilinear G a b Q h ξ U V (L x ^ κ) θ β ζ u r
        (dyadRestriction G b k f) (dyadRestriction G a j g)
        hU1 hV1 (Real.rpow_nonneg hLp.le _) hr hcop hθ hβ hWidth.1 hWidth.2 hg hf hρa hρb
        (fun F => (hFrame G hG a ha Q h hQ hWidth.1 F).2)
        (fun F => (hFrame G hG b hb Q h hQ hWidth.1 F).2)
      have hcost := minor_power_precision (L x) integerBilinearConstant B κ P.d U V r
        (by linarith) integerBilinearConstant_pos hIntK hB.le hκ hd.le hU hV hrR hrQ' hrS hlog
      have hcost' : 20 * integerBilinearConstant * L x ^ κ * Real.sqrt (bilinearDecay U V r) ≤ L x ^ (-B) :=
        hcost.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
      exact hm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcost' (tuple_norm_nonneg G b (dyadRestriction G b k f)))
        (tuple_norm_nonneg G a (dyadRestriction G a j g)))
  have hbound := comparison_bound_from_dyads G a b Q h ξ θ ζ (L x ^ (-B)) f g hE hdyadic
  have hNA : ((occupiedDyads G a).card : ℝ) ≤ L x ^ (P.d + 1) := hDyads G hG a ha
  have hNB : ((occupiedDyads G b).card : ℝ) ≤ L x ^ (P.d + 1) := hDyads G hG b hb
  have hcard := mul_le_mul hNA hNB (Nat.cast_nonneg _) (Real.rpow_nonneg hLp.le _)
  have hcost : ((occupiedDyads G a).card : ℝ) * (occupiedDyads G b).card * L x ^ (-B) ≤ L x ^ (-A) := by
    calc
      _ ≤ (L x ^ (P.d + 1) * L x ^ (P.d + 1)) * L x ^ (-B) := mul_le_mul_of_nonneg_right hcard hE
      _ = L x ^ (2 * (P.d + 1) - B) := by
        rw [← Real.rpow_add hLp, ← Real.rpow_add hLp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [B]; linarith)
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost (tuple_norm_nonneg G b f)) (tuple_norm_nonneg G a g))

example : Erdos821.Blueprint.Analytic.comparison_kernel_statement := @comparison_kernel_proof

end
end Erdos821.Blueprint.Analytic
