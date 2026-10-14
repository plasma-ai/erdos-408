import Erdos408.TwoSided.Comparison.ArcsCore
import Erdos408.TwoSided.Comparison.Multiplier
import Erdos408.TwoSided.Comparison.Separation

/-!
# Parseval, the arcs and the local Mellin energy

S8–S10 of `blueprint/two_sided_correlation.md` §§5.3–5.4 (PD (6.22)–(6.24) and Lemma 6.4;
WD §§5.3, 5.5). Write `𝔅_m = ∫₀¹ star(Û_m) V̂ 𝔪` (shift identity), split `[0, 1]` into the
minor arcs (C2) and the arcs of radius `Δ = L^{C_arc}/H'` around `u/r`, `r ≤ L^{C_arc}`; on
each arc, the local Mellin energy (PD Lemma 6.4) turns `∫_{arc} |Û_m|²` into the mean square
(6.24) of interface E with `h = u`, `k = r`, plus a tail over `|t| > T₀` and an additive term.
The result, `exists_norm_comparisonBilinear_le_arcs`, bounds `|Y_m⁻¹ 𝔅_m|` by
`K (L^{-A_m} + L^{C_cost} (√Ξ₀ + L^{-A_e}))` whenever (6.24) is at most `Ξ₀` at every centre.

The pieces live in `Comparison/ArcsFourier.lean` (shift identity, Parseval, the arc energy),
`Comparison/ArcsBound.lean` (S8–S10 for abstract data), `Comparison/ArcsLabels.lean` (the free
labels, the four boxes) and `Comparison/ArcsCore.lean` (energies, minor arcs, the count); the
crude U7 and U9 are in `Setup.lean`.
-/

namespace Erdos408.TwoSided

open Filter MeasureTheory

/-- **One bilinear form from the mean square (S6–S10).** For `m₀`, the derivative bounds
`M₁` of the pieces and every minor-arc saving `A_m` there are `C_arc` (the arc exponent of
C2 at `(max(C₇, 1), 0.38, A_m')`, `A_m' = |A_m| + |C_A| + |C_V| + 1`) and
`C_cost = 2C_arc + C_V/2` such that for every `C_m ≥ C_arc` and every `A_e` there is `K`
with: eventually, for groups as in (6.1), all admissible data, every comparison pattern,
piece `ψ₁` of the class, `y₀ ∈ [(4κ)⁻¹, 2κe²]` and twist `σ`, if the mean square (6.24) of
`𝒰 = endpointCoeff … (A ∪ B) (ψ' ∘ X_B) ψ₁ Y σ` over `|t| ≤ T₀ = x L^{C_m + 2}` is at most
`Ξ₀` at every centre `h/k`, `k ≤ L^{C_m}` (when `Y` is in the range of interface E), then
`|Y⁻¹ 𝔅| ≤ K (L^{-A_m} + L^{C_cost} (√Ξ₀ + L^{-A_e}))`, with `Y = y₀ x U U'`.

If no label has `φ(D_A) φ'(D_B) ≠ 0`, then `𝔅 = 0`; otherwise the scales (6.17) put `Y` in
range. Then `exists_norm_sum_shift_le` applies with `ε = 4K' L^{-A_m'}` (C1, C2 on four
boxes), the energies `A ≤ Y L^{C_A}`, `B ≤ Y L^{C_V}` (6.19, `C_A = 2C_W + 3`,
`C_V = 2B₀ + 2C_W + 1`) and the arcs `H = UU'/L^{C_arc}`, `R = ⌊L^{C_arc}⌋`; with `j` chosen
from `A_e`, the arc energy is `≤ K_j Y (Ξ₀ + 2L^{-2A_e})` (`energy_le`). -/
theorem exists_norm_comparisonBilinear_le_arcs (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ)
    (CN c : ℝ) (d : ℕ) (B₀ κ : ℝ) (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1)
    (hvlo : 0 < vlo) (halo : 1 / 10 < alo) (hc : 0 < c) (hκ : 1 < κ) (m₀ : ℕ) (M₁ : ℕ → ℝ)
    (Am : ℝ) :
    ∃ Carc Ccost : ℝ, ∀ Cm : ℝ, Carc ≤ Cm → ∀ A₀ : ℝ, ∃ K : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ)
          (G : ℕ → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v →
          (∀ Q, |Bc Q| ≤ 1) → CoreAdmissible B₀ x P G →
        ∀ (J : ℕ) (A B : ι → Finset (Fin J)) (φ φ' ψ ψ' : ℕ → ℂ) (U U' : ℝ),
          ComparisonPattern m₀ big A B φ φ' ψ ψ' U U' →
        ∀ ψ₁ : ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁ →
          (∀ z, ψ₁ z ≠ 0 → 1 ≤ z ∧ z ≤ 2) →
          (∀ (j : ℕ) (z : ℝ), ‖iteratedDeriv j ψ₁ z‖ ≤ M₁ j) →
        ∀ (y₀ σ Ξ₀ : ℝ), (4 * κ)⁻¹ ≤ y₀ → y₀ ≤ 2 * κ * Real.exp 2 →
          (x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ y₀ * (x * U * U') →
            y₀ * (x * U * U') ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ)) →
            ∀ (k : ℕ) (h : ℤ), 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm →
              ∫ t in -(x * Real.log x ^ (Cm + 2))..(x * Real.log x ^ (Cm + 2)),
                  ‖twistedPoly (y₀ * (x * U * U'))
                      (endpointCoeff x q q₀ a u v Bc P (fun g => A g ∪ B g)
                        (fun p => ψ' (slotProduct B fun g i => p g i.castSucc)) ψ₁
                        (y₀ * (x * U * U')) σ) h k t‖ ^ 2 ≤ Ξ₀) →
          ‖(((y₀ * (x * U * U')) : ℝ) : ℂ)⁻¹ *
              comparisonBilinear x q q₀ a u v Bc P A B φ φ' ψ ψ' G ψ₁ (y₀ * (x * U * U')) σ‖ ≤
            K * (Real.log x ^ (-Am) +
              Real.log x ^ Ccost * (Real.sqrt Ξ₀ + Real.log x ^ (-A₀))) := by
  obtain ⟨C₇, hC1⟩ := eventually_sum_auxLabels_eq_le c₀ C₀ vlo vhi hvlo m₀
  obtain ⟨CW, hU9⟩ := exists_norm_markedListWeight_le_rpow q₀ c₀ C₀ vlo vhi hq₀ hq₀₁ hvlo m₀
  -- the energy exponents `A ≤ Y L^{CA}`, `B ≤ Y L^{CB}` and the minor-arc saving
  set CA : ℝ := 2 * CW + 3 with hCA
  set CB : ℝ := 2 * B₀ + 2 * CW + 1 with hCB
  set Am' : ℝ := |Am| + |CA| + |CB| + 1 with hAm'
  obtain ⟨Carc, Kmin, hCarc, hKmin, hC2⟩ := exists_minorArc_bound (max C₇ 1) 0.38 Am'
    (by positivity) (by norm_num) (by positivity)
  refine ⟨Carc, 2 * Carc + CB / 2, fun Cm hCm A₀ => ?_⟩
  -- the decay order of the local Mellin energy
  set j : ℕ := ⌈|CA| + 2 * |A₀| + 6⌉₊ + 4 with hj
  obtain ⟨K₃, hK₃, hshift⟩ := Arcs.exists_norm_sum_shift_le j (by omega)
  refine ⟨4 * Kmin + 8 * Real.sqrt K₃, ?_⟩
  set M0 := M₁ 0 with hM0
  have hlogκ := Real.tendsto_log_atTop
  filter_upwards [hC1, hU9,
    eventually_abs_centeredCore_le_log q alo ahi K₀ CN c d hq hq₁ halo hc, hC2,
    Arcs.eventually_slotProduct_le c₀ C₀ vlo vhi m₀,
    hlogκ.eventually (Arcs.eventually_add_le_rpow 1 1 (by norm_num : (0 : ℝ) ≤ 0.38)
      (by norm_num : (0.38 : ℝ) < 0.39)),
    hlogκ.eventually (Arcs.eventually_add_le_rpow (1 / 2) ((Real.log (4 * κ) + 2) / 2)
      (by norm_num : (0 : ℝ) ≤ 0.38) (by norm_num : (0.38 : ℝ) < 0.39)),
    hlogκ.eventually (Arcs.eventually_add_le_rpow (|Carc| / 2) 1
      (by norm_num : (0 : ℝ) ≤ 0.38) (by norm_num : (0.38 : ℝ) < 0.39)),
    hlogκ.eventually ((isLittleO_log_rpow_atTop (show (0 : ℝ) < 0.38 by norm_num)).bound
      one_pos),
    hlogκ.eventually (Arcs.eventually_add_le_rpow 2 (Real.log (2 * κ * Real.exp 2))
      (by norm_num : (0 : ℝ) ≤ 0.465) (by norm_num : (0.465 : ℝ) < 0.47)),
    hlogκ.eventually (Arcs.eventually_add_le_rpow 2 (Real.log 4)
      (by norm_num : (0 : ℝ) ≤ 0.465) (by norm_num : (0.465 : ℝ) < 1)),
    hlogκ.eventually_ge_atTop (7 + 4 * κ * Real.exp 2 + 3 * M0 ^ 2),
    eventually_ge_atTop (40 * κ + 4 * κ * Real.exp 2 + 16 * κ ^ 2 + 10),
    eventually_log_rpow_le_self (CA + 2 * A₀)]
    with x hC1x hU9x hU7x hC2x hscale hF1 hF2 hF3 hF3' hF4 hF5 hF6 hF7 hF8
  intro ι _ _ P big hadm r a u v Bc G hin hsl hBc hco J A B φ φ' ψ ψ' U U' hpat ψ₁ hψ₁
    hψ₁s hψ₁M y₀ σ Ξ₀ hy₀ hy₀' hΞ
  clear hC1 hU9 hC2 hlogκ
  set L := Real.log x with hLdef
  set Y := y₀ * (x * U * U') with hYdef
  have hκ0 : 0 < κ := by linarith only [hκ]
  have he2 : 0 < Real.exp 2 := Real.exp_pos 2
  have hM0sq : 0 ≤ M0 ^ 2 := sq_nonneg _
  have hκe : 0 ≤ 4 * κ * Real.exp 2 := by positivity
  have hκ2 : 0 ≤ 16 * κ ^ 2 := by positivity
  have hL7 : 7 ≤ L := by linarith only [hF6, hκe, hM0sq]
  have hL0 : 0 < L := by linarith only [hL7]
  have hL1 : 1 ≤ L := by linarith only [hL7]
  have hx10 : 10 ≤ x := by linarith only [hF7, hκ0, hκe, hκ2]
  have hx0 : 0 < x := by linarith only [hx10]
  have hy₀0 : 0 < y₀ := lt_of_lt_of_le (by positivity) hy₀
  have he1 : Real.exp 1 ≤ 4 := (Real.exp_one_lt_d9).le.trans (by norm_num)
  have he1' : 0 < Real.exp 1 := Real.exp_pos 1
  -- the coefficients of the bilinear form
  set 𝒰 : ℕ → ℂ := endpointCoeff x q q₀ a u v Bc P (fun g => A g ∪ B g)
    (fun p => ψ' (slotProduct B fun g i => p g i.castSucc)) ψ₁ Y σ with h𝒰
  set 𝒱 : ℕ → ℂ := fun w => (G w : ℂ) * markedListWeight P q₀ (unsharedSlots fun g => A g ∪ B g)
    (fun p => ψ (slotProduct A fun g i => p g i.castSucc)) w with h𝒱
  set b₁ : ℕ → ℂ := fun n => φ n * (n : ℂ) ^ (-((σ : ℂ) * Complex.I)) with hb₁
  set b₂ : ℕ → ℂ := fun n => φ' n * (n : ℂ) ^ (-((σ : ℂ) * Complex.I)) with hb₂
  set cl : (ι → Fin J → ℕ) → ℂ := fun l =>
    (labelMass P (fun g => A g ∪ B g) l : ℂ) * b₁ (slotProduct A l) *
      b₂ (slotProduct B l) with hcl
  set D : (ι → Fin J → ℕ) → ℕ := fun l => slotProduct (fun g => A g ∪ B g) l with hD
  have h𝔅 : comparisonBilinear x q q₀ a u v Bc P A B φ φ' ψ ψ' G ψ₁ Y σ =
      ∑ l ∈ auxLabels P (fun g => A g ∪ B g),
        cl l * ∑ w ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, 𝒰 w * 𝒱 (w + D l) := rfl
  have hK0 : 0 ≤ 4 * Kmin + 8 * Real.sqrt K₃ := by positivity
  have hRHS0 : 0 ≤ (4 * Kmin + 8 * Real.sqrt K₃) * (L ^ (-Am) +
      L ^ (2 * Carc + CB / 2) * (Real.sqrt Ξ₀ + L ^ (-A₀))) := by positivity
  -- if no label has `φ(D_A) φ'(D_B) ≠ 0`, then `𝔅 = 0`
  by_cases hex : ∃ l ∈ auxLabels P (fun g => A g ∪ B g),
    φ (slotProduct A l) ≠ 0 ∧ φ' (slotProduct B l) ≠ 0
  swap
  · push Not at hex
    have h0 : comparisonBilinear x q q₀ a u v Bc P A B φ φ' ψ ψ' G ψ₁ Y σ = 0 := by
      rw [h𝔅]
      refine Finset.sum_eq_zero fun l hl => ?_
      by_cases hφ : φ (slotProduct A l) = 0
      · simp [hcl, hb₁, hφ]
      · simp [hcl, hb₂, hex l hl hφ]
    rw [h0, mul_zero, norm_zero]
    exact hRHS0
  obtain ⟨l₀, hl₀, hφ₀, hφ₀'⟩ := hex
  -- the scales (6.17)
  have hAB : ∀ g, Disjoint (A g) (B g) := fun g => (hpat.1 g).1
  have hAm : ∀ g, (A g).card ≤ m₀ := fun g =>
    (Finset.card_le_card Finset.subset_union_left).trans (hpat.1 g).2
  have hBm : ∀ g, (B g).card ≤ m₀ := fun g =>
    (Finset.card_le_card Finset.subset_union_right).trans (hpat.1 g).2
  have hCbig : ∀ g ∉ big, A g ∪ B g = ∅ := fun g hg => by
    rw [(hpat.2.1 g hg).1, (hpat.2.1 g hg).2, Finset.empty_union]
  obtain ⟨gA, iA, hiA⟩ : ∃ g, ∃ i, i ∈ A g := by
    obtain ⟨g, hg⟩ := hpat.2.2.1.1
    exact ⟨g, hg⟩
  obtain ⟨gB, iB, hiB⟩ : ∃ g, ∃ i, i ∈ B g := by
    obtain ⟨g, hg⟩ := hpat.2.2.1.2
    exact ⟨g, hg⟩
  have hDA_lo := Arcs.le_slotProduct hadm hCbig (fun g => Finset.subset_union_left) hl₀ hiA
  have hDB_lo := Arcs.le_slotProduct hadm hCbig (fun g => Finset.subset_union_right) hl₀ hiB
  have hDA_hi := hscale P big hadm J (fun g => A g ∪ B g) A (fun g hg => (hpat.2.1 g hg).1) hAm
    (fun g => Finset.subset_union_left) l₀ hl₀
  have hDB_hi := hscale P big hadm J (fun g => A g ∪ B g) B (fun g hg => (hpat.2.1 g hg).2) hBm
    (fun g => Finset.subset_union_right) l₀ hl₀
  have hUA := hpat.2.2.2.2.1 _ hφ₀
  have hUB := hpat.2.2.2.2.2 _ hφ₀'
  have hU_lo : Real.exp (L ^ (0.39 : ℝ) - 1) ≤ U := by
    rw [Real.exp_sub, div_le_iff₀ he1', mul_comm]
    exact hDA_lo.trans hUA.2
  have hU'_lo : Real.exp (L ^ (0.39 : ℝ) - 1) ≤ U' := by
    rw [Real.exp_sub, div_le_iff₀ he1', mul_comm]
    exact hDB_lo.trans hUB.2
  have hU_hi : U ≤ Real.exp (L ^ (0.465 : ℝ)) := hUA.1.trans hDA_hi
  have hU'_hi : U' ≤ Real.exp (L ^ (0.465 : ℝ)) := hUB.1.trans hDB_hi
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hU_lo
  have hU'0 : 0 < U' := lt_of_lt_of_le (Real.exp_pos _) hU'_lo
  have hUU_lo : Real.exp (2 * L ^ (0.39 : ℝ) - 2) ≤ U * U' := by
    rw [show 2 * L ^ (0.39 : ℝ) - 2 = (L ^ (0.39 : ℝ) - 1) + (L ^ (0.39 : ℝ) - 1) by ring,
      Real.exp_add]
    exact mul_le_mul hU_lo hU'_lo (Real.exp_pos _).le hU0.le
  have hUU_hi : U * U' ≤ Real.exp (2 * L ^ (0.465 : ℝ)) := by
    rw [two_mul, Real.exp_add]
    exact mul_le_mul hU_hi hU'_hi hU'0.le (Real.exp_pos _).le
  have hUU0 : 0 < U * U' := mul_pos hU0 hU'0
  -- `exp(L^{0.38}) ≤ U, U'`
  have h38 : Real.exp (L ^ (0.38 : ℝ)) ≤ Real.exp (L ^ (0.39 : ℝ) - 1) :=
    Real.exp_le_exp.2 (by linarith only [hF1])
  -- `Y` lies in the range of interface E
  have hY_lo : x * Real.exp (L ^ (0.38 : ℝ)) ≤ Y := by
    have h₁ : 4 * κ * Real.exp (L ^ (0.38 : ℝ)) ≤ U * U' := by
      refine le_trans ?_ hUU_lo
      rw [← Real.exp_log (show 0 < 4 * κ by positivity), ← Real.exp_add, Real.exp_le_exp]
      linarith only [hF2]
    have h₂ : Real.exp (L ^ (0.38 : ℝ)) ≤ y₀ * (U * U') := by
      calc Real.exp (L ^ (0.38 : ℝ)) = (4 * κ)⁻¹ * (4 * κ * Real.exp (L ^ (0.38 : ℝ))) := by
            rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
        _ ≤ y₀ * (U * U') := mul_le_mul hy₀ h₁ (by positivity) hy₀0.le
    calc x * Real.exp (L ^ (0.38 : ℝ)) ≤ x * (y₀ * (U * U')) :=
          mul_le_mul_of_nonneg_left h₂ hx0.le
      _ = Y := by rw [hYdef]; ring
  have hY_hi : Y ≤ x * Real.exp (L ^ (0.47 : ℝ)) := by
    have h₁ : y₀ * (U * U') ≤ Real.exp (L ^ (0.47 : ℝ)) := by
      calc y₀ * (U * U') ≤ 2 * κ * Real.exp 2 * Real.exp (2 * L ^ (0.465 : ℝ)) :=
            mul_le_mul hy₀' hUU_hi hUU0.le (by positivity)
        _ = Real.exp (Real.log (2 * κ * Real.exp 2) + 2 * L ^ (0.465 : ℝ)) := by
            rw [Real.exp_add, Real.exp_log (by positivity)]
        _ ≤ Real.exp (L ^ (0.47 : ℝ)) := Real.exp_le_exp.2 (by linarith only [hF4])
    calc Y = x * (y₀ * (U * U')) := by rw [hYdef]; ring
      _ ≤ x * Real.exp (L ^ (0.47 : ℝ)) := mul_le_mul_of_nonneg_left h₁ hx0.le
  have hΞall := hΞ hY_lo hY_hi
  -- the arc parameters: `H = UU'/L^{C_arc}`, `T₀ = x L^{C_m + 2}`, `R = ⌊L^{C_arc}⌋`
  have hLCarc1 : 1 ≤ L ^ Carc := Real.one_le_rpow hL1 hCarc.le
  have hLCarc : L ^ Carc ≤ U * U' := by
    refine le_trans ?_ hUU_lo
    rw [Real.rpow_def_of_pos hL0, Real.exp_le_exp]
    have h₁ : Real.log L ≤ L ^ (0.38 : ℝ) := by
      have := hF3'
      rwa [Real.norm_of_nonneg (Real.log_nonneg hL1), Real.norm_of_nonneg (by positivity),
        one_mul] at this
    have h₂ : Real.log L * Carc ≤ |Carc| * L ^ (0.38 : ℝ) := by
      calc Real.log L * Carc ≤ Real.log L * |Carc| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (Real.log_nonneg hL1)
        _ ≤ L ^ (0.38 : ℝ) * |Carc| := mul_le_mul_of_nonneg_right h₁ (abs_nonneg _)
        _ = |Carc| * L ^ (0.38 : ℝ) := mul_comm _ _
    linarith only [h₂, hF3]
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = U * U' / L ^ Carc := ⟨_, rfl⟩
  have hH1 : 1 ≤ H := by rw [hHdef, le_div_iff₀ (by positivity), one_mul]; exact hLCarc
  have hHle : H ≤ U * U' := by rw [hHdef]; exact div_le_self hUU0.le hLCarc1
  have hxy : 10 ≤ y₀ * x := by
    have : (4 * κ)⁻¹ * (40 * κ) ≤ y₀ * x :=
      mul_le_mul hy₀ (by linarith only [hF7, hκe, hκ2]) (by positivity) hy₀0.le
    rwa [show (4 * κ)⁻¹ * (40 * κ) = 10 by
      rw [inv_mul_eq_div, div_eq_iff (by positivity)]; ring] at this
  have hY0 : 0 < Y := by rw [hYdef]; positivity
  have hY10 : 10 ≤ Y :=
    hx10.trans (le_trans (le_mul_of_one_le_right hx0.le (Real.one_le_exp (by positivity)))
      hY_lo)
  have hHY : H ≤ Y / 10 := by
    refine hHle.trans ?_
    rw [le_div_iff₀ (by norm_num), hYdef]
    calc U * U' * 10 ≤ U * U' * (y₀ * x) := mul_le_mul_of_nonneg_left hxy hUU0.le
      _ = y₀ * (x * U * U') := by ring
  obtain ⟨T₀, hT₀def⟩ : ∃ T₀ : ℝ, T₀ = x * L ^ (Cm + 2) := ⟨_, rfl⟩
  have hratio : L ^ 2 * L ^ Carc ≤ L ^ (Cm + 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by push_cast; linarith only [hCm])
  have hT₀H : 2 * Y * L ≤ T₀ * H := by
    have h₁ : 2 * y₀ ≤ L := by linarith only [hy₀', hF6, hM0sq]
    calc 2 * Y * L = (2 * y₀) * L * (x * (U * U')) := by rw [hYdef]; ring
      _ ≤ L * L * (x * (U * U')) := by gcongr
      _ = x * (L ^ 2 * L ^ Carc) * (U * U') / L ^ Carc := by
          rw [eq_div_iff (by positivity)]; ring
      _ ≤ x * L ^ (Cm + 2) * (U * U') / L ^ Carc := by gcongr
      _ = T₀ * H := by rw [hT₀def, hHdef]; ring
  have hT₀H' : 2 * Y ≤ T₀ * H := le_trans (le_mul_of_one_le_right (by positivity) hL1) hT₀H
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ, R = ⌊L ^ Carc⌋₊ := ⟨_, rfl⟩
  have hRL : (R : ℝ) ≤ L ^ Carc := by rw [hRdef]; exact Nat.floor_le (by positivity)
  have hLCm : L ^ Carc ≤ L ^ Cm := Real.rpow_le_rpow_of_exponent_le hL1 hCm
  -- the mean square at the centres, and `Ξ₀ ≥ 0`
  have hΞR : ∀ (r : ℕ) (u : ℤ), 1 ≤ r → r ≤ R →
      ∫ t in (-T₀)..T₀, ‖twistedPoly Y 𝒰 (-u) r t‖ ^ 2 ≤ Ξ₀ := by
    intro r u' hr₁ hr₂
    rw [hT₀def]
    refine hΞall r (-u') hr₁ ?_
    have : (r : ℝ) ≤ R := by exact_mod_cast hr₂
    linarith only [this, hRL, hLCm]
  have hΞ0 : 0 ≤ Ξ₀ := by
    refine le_trans ?_ (hΞall 1 0 le_rfl (by simpa using hLCarc1.trans hLCm))
    exact intervalIntegral.integral_nonneg (neg_le_self (by positivity)) fun t _ => by positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 4 * (Kmin * L ^ (-Am')) := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  -- the shifts land in `[0, 3Y]`: `D_C ≤ e² UU' ≤ Y`
  have hxe : Real.exp 2 ≤ y₀ * x := by
    have : (4 * κ)⁻¹ * (4 * κ * Real.exp 2) ≤ y₀ * x :=
      mul_le_mul hy₀ (by linarith only [hF7, hκ2, hκ0]) (by positivity) hy₀0.le
    rwa [show (4 * κ)⁻¹ * (4 * κ * Real.exp 2) = Real.exp 2 by
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]] at this
  have hsupp : ∀ l ∈ auxLabels P (fun g => A g ∪ B g), cl l ≠ 0 →
      ∀ n ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, n + D l ∈ Finset.Icc 0 ⌊3 * Y⌋₊ := by
    intro l _ hcl0 n hn
    have hφl : φ (slotProduct A l) ≠ 0 := fun h => hcl0 (by simp [hcl, hb₁, h])
    have hφl' : φ' (slotProduct B l) ≠ 0 := fun h => hcl0 (by simp [hcl, hb₂, h])
    have h₁ := (hpat.2.2.2.2.1 _ hφl).2
    have h₂ := (hpat.2.2.2.2.2 _ hφl').2
    have hDl : (D l : ℝ) ≤ Real.exp 2 * (U * U') := by
      have : (D l : ℝ) = (slotProduct A l : ℝ) * (slotProduct B l : ℝ) := by
        rw [hD]
        simp only
        rw [slotProduct_union hAB]
        push_cast
        rfl
      rw [this, show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      calc (slotProduct A l : ℝ) * (slotProduct B l : ℝ)
          ≤ (Real.exp 1 * U) * (Real.exp 1 * U') :=
            mul_le_mul h₁ h₂ (Nat.cast_nonneg _) (by positivity)
        _ = Real.exp 1 * Real.exp 1 * (U * U') := by ring
    have hDY : Real.exp 2 * (U * U') ≤ Y := by
      rw [hYdef]
      calc Real.exp 2 * (U * U') ≤ (y₀ * x) * (U * U') :=
            mul_le_mul_of_nonneg_right hxe hUU0.le
        _ = y₀ * (x * U * U') := by ring
    have hn2 : (n : ℝ) ≤ 2 * Y := (Nat.le_floor_iff (by positivity)).1 (Finset.mem_Icc.1 hn).2
    refine Finset.mem_Icc.2 ⟨Nat.zero_le _, Nat.le_floor ?_⟩
    push_cast
    linarith only [hn2, hDl, hDY]
  -- the energies (6.19)
  have hexpx : Real.exp (L ^ (0.47 : ℝ)) ≤ x := by
    calc Real.exp (L ^ (0.47 : ℝ)) ≤ Real.exp L := by
          refine Real.exp_le_exp.2 ?_
          simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (0.47 : ℝ) ≤ 1 by norm_num)
      _ = x := Real.exp_log hx0
  have hYx : Y ≤ x * x := hY_hi.trans (mul_le_mul_of_nonneg_left hexpx hx0.le)
  have hYx3 : 2 * Y ≤ x ^ 3 :=
    calc 2 * Y ≤ 2 * (x * x) := by linarith only [hYx]
      _ ≤ x * (x * x) := mul_le_mul_of_nonneg_right (by linarith only [hx10]) (by positivity)
      _ = x ^ 3 := by ring
  have hcardS : ∀ g, (unsharedSlots (fun g => A g ∪ B g) g).card ≤ m₀ + 1 := by
    intro g
    refine (Finset.card_insert_le _ _).trans ?_
    rw [Finset.card_map]
    exact Nat.add_le_add_right (hpat.1 g).2 1
  have hAen := Arcs.sum_norm_endpointCoeff_sq_le a u v Bc P (fun g => A g ∪ B g)
    (fun p => ψ' (slotProduct B fun g i => p g i.castSucc)) ψ₁ (Y := Y) (σ := σ) (M0 := M0) hL0
    (by linarith only [hY10]) hYx3 (by linarith only [hF6, hκe]) (fun z => by simpa using hψ₁M 0 z)
    (hU7x r a u v Bc hin hsl hBc)
    (hU9x P big hadm (J + 1) _ _ hcardS fun p => (hpat.2.2.2.1 _).2.2.2)
  have hBen := Arcs.sum_norm_second_sq_le (L := L) (B₀ := B₀) (CW := CW) (Y := Y)
    (by linarith only [hL7]) (by linarith only [hY10]) G _ hco.2
    (hU9x P big hadm (J + 1) _ (fun p => ψ (slotProduct A fun g i => p g i.castSucc)) hcardS
      fun p => (hpat.2.2.2.1 _).2.2.1)
  -- the multiplier: mass `1`, and the minor arcs
  have hV : ∀ g, harmonicMass (P g) ≠ 0 := fun g =>
    (lt_of_lt_of_le hvlo (hadm.2.2.2.2.2.1 g).1).ne'
  have hM1 : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖∑ l ∈ auxLabels P (fun g => A g ∪ B g),
      cl l * Erdos821.Blueprint.Analytic.e (-θ * D l)‖ ≤ 1 := by
    intro θ _
    refine (norm_sum_le _ _).trans ?_
    rw [← sum_labelMass hV (fun g => A g ∪ B g)]
    refine Finset.sum_le_sum fun l _ => ?_
    have hμ : 0 ≤ labelMass P (fun g => A g ∪ B g) l := labelMass_nonneg P _ l
    have hb : ∀ (f : ℕ → ℂ) (n : ℕ), ‖f n‖ ≤ 1 →
        ‖f n * (n : ℂ) ^ (-((σ : ℂ) * Complex.I))‖ ≤ 1 := fun f n h => by
      rw [norm_mul]
      exact (mul_le_mul h (Arcs.norm_natCast_cpow_neg_le_one n σ) (norm_nonneg _)
        zero_le_one).trans (by norm_num)
    rw [norm_mul, Arcs.norm_e, mul_one, hcl]
    simp only
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ]
    calc labelMass P (fun g => A g ∪ B g) l * ‖b₁ (slotProduct A l)‖ *
          ‖b₂ (slotProduct B l)‖ ≤ labelMass P (fun g => A g ∪ B g) l * 1 * 1 := by
          gcongr
          · exact hb φ _ (hpat.2.2.2.1 _).1
          · exact hb φ' _ (hpat.2.2.2.1 _).2.1
      _ = labelMass P (fun g => A g ∪ B g) l := by ring
  have hUUx : 4 * (U * U') ≤ x ^ 2 := by
    have hx2 : x ^ 2 = Real.exp (2 * L) := by
      rw [show 2 * L = L + L by ring, Real.exp_add, Real.exp_log hx0]
      ring
    rw [hx2]
    calc 4 * (U * U') ≤ 4 * Real.exp (2 * L ^ (0.465 : ℝ)) := by gcongr
      _ = Real.exp (Real.log 4 + 2 * L ^ (0.465 : ℝ)) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (2 * L) := by
          refine Real.exp_le_exp.2 ?_
          have h₁ : 2 * L ^ (0.465 : ℝ) + Real.log 4 ≤ L := by simpa using hF5
          calc Real.log 4 + 2 * L ^ (0.465 : ℝ) = 2 * L ^ (0.465 : ℝ) + Real.log 4 := add_comm _ _
            _ ≤ L := h₁
            _ ≤ 2 * L := by linarith only [hL0]
  have hMε : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      (∀ (r : ℕ) (u : ℤ), 1 ≤ r → r ≤ R → -(R : ℤ) ≤ u → u ≤ 2 * R → 1 / H < |θ - u / r|) →
      ‖∑ l ∈ auxLabels P (fun g => A g ∪ B g),
        cl l * Erdos821.Blueprint.Analytic.e (-θ * D l)‖ ≤ ε := by
    intro θ hθ harc
    rw [hεdef]
    have harc' : ∀ (r : ℕ) (u : ℤ), 1 ≤ r → r ≤ R → -(R : ℤ) ≤ u → u ≤ 2 * R →
        L ^ Carc / (U * U') < |θ - u / r| := fun r u hr₁ hr₂ hu₁ hu₂ => by
      have := harc r u hr₁ hr₂ hu₁ hu₂
      rwa [hHdef, one_div_div] at this
    exact Arcs.norm_multiplier_le hadm hvlo hAB φ φ' σ U U' θ C₇ (max C₇ 1) Carc Am' Kmin R
      (fun n => (hpat.2.2.2.1 n).1) (fun n => (hpat.2.2.2.1 n).2.1) hpat.2.2.2.2.1
      hpat.2.2.2.2.2 (hC1x P big hadm J A hAm) (hC1x P big hadm J B hBm) hC2x
      (h38.trans hU_lo) (h38.trans hU'_lo) hUUx hL1
      (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
      (Real.one_le_rpow hL1 (le_trans zero_le_one (le_max_right _ _)))
      (fun r hr => hRdef ▸ Nat.le_floor hr) hLCarc hθ harc'
  -- S8–S10
  have hmain := hshift Y H T₀ ε (Y * L ^ CA) (Y * L ^ CB) Ξ₀ R
    (auxLabels P (fun g => A g ∪ B g)) cl D (Finset.Icc 0 ⌊3 * Y⌋₊) 𝒰 𝒱 hY10 hH1 hHY hT₀H'
    hε0 hΞ0 hsupp hAen hBen hM1 hMε hΞR
  rw [← h𝔅, hεdef] at hmain
  -- the arc energy: `E ≤ K₃ Y (Ξ₀ + 2L^{-2A_e})`
  have hm : CA + 2 * A₀ + 2 ≤ ((j - 4 : ℕ) : ℝ) := by
    rw [hj, Nat.add_sub_cancel]
    have := Nat.le_ceil (|CA| + 2 * |A₀| + 6)
    linarith only [this, le_abs_self CA, le_abs_self A₀]
  have hHY4 : H / Y ≤ 4 * κ / x := by
    rw [div_le_div_iff₀ hY0 hx0, hYdef]
    have h₁ : 1 ≤ 4 * κ * y₀ := by
      have := mul_le_mul_of_nonneg_left hy₀ (show 0 ≤ 4 * κ by positivity)
      rwa [mul_inv_cancel₀ (by positivity)] at this
    calc H * x ≤ U * U' * x := mul_le_mul_of_nonneg_right hHle hx0.le
      _ ≤ (4 * κ * y₀) * (U * U' * x) := le_mul_of_one_le_left (by positivity) h₁
      _ = 4 * κ * (y₀ * (x * U * U')) := by ring
  have hE := Arcs.energy_le (K₃ := K₃) (Ξ₀ := Ξ₀) hx0 hLdef.symm hL7
    (by linarith only [hY10]) hY_hi hH1 hT₀H hm hHY4 (by linarith only [hF7, hκ0, hκe]) hF8 hK₃.le
  -- the count
  have hAm : -Am' + (CA + CB) / 2 ≤ -Am := by
    rw [hAm']
    linarith only [le_abs_self Am, le_abs_self CA, le_abs_self CB, abs_nonneg CA, abs_nonneg CB]
  have hfin := Arcs.div_le_of_arcs hY0 hL1 hKmin.le hK₃.le hΞ0 hmain hE hRL hAm
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hY0.le, inv_mul_eq_div]
  exact hfin

end Erdos408.TwoSided
