module

public import Erdos408.TwoSided.Comparison
public import Erdos408.TwoSided.Graph

/-!
# The two-sided correlation from the graph transference

A proof of `TwoSidedCorrelation` (PD Theorem 6.1, extended) from `GraphTransference` (PD
Propositions 6.2 and 6.3), following PD §6 as restated in
`blueprint/two_sided_correlation.md` (§3.4).

* `eventually_raw_add_comparison_le` (interface G, `TwoSided/Graph.lean`): the raw correlation
  plus the signed stripped comparison correlations of `GraphTransference`'s family is
  `O(L^{-A})`, with `∑ |β| ≤ L^{C₁}`.
* `exists_comparison_bound` (interface C, `TwoSided/Comparison.lean`): under the premises,
  each stripped comparison correlation is `O(L^{-A''})`, `A'' = A + max(C₁, 0)`. It rests on
  the endpoint mean square (interface E, `TwoSided/Endpoint.lean`).

The groups of `TwoSidedCorrelation` are reindexed once (R1) by `ι = ↥(Sg ∪ Bg)`, with
`P = Subtype.val` and `big = univ.filter (·.1 ∈ Bg)`. The bound `d ≤ 2` is not used.

The step numbers S0–S19 and the lemma names G1–G5, C1–C3, E1–E10 in the docstrings of
`Erdos408/TwoSided/` are those of the blueprint.
-/

@[expose] public section

namespace Erdos408

open Filter TwoSided

/-- The extended two-sided marked correlation follows from the graph transference input. -/
theorem twoSidedCorrelation_of_graphTransference (hG : GraphTransference) :
    TwoSidedCorrelation := by
  intro q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d B₀ κ CΨ M A hq hq₁ hq₀ hq₀₁ hc₀ hvlo halo hal
    hahi hc _hd hκ
  obtain ⟨m₀, J, C₁, CG, hGx⟩ := eventually_raw_add_comparison_le hG q q₀ c₀ C₀ vlo vhi alo ahi
    K₀ CN c d B₀ κ CΨ M A hq hq₁ hq₀ hq₀₁ hc₀ hvlo halo hal hahi hc hκ
  obtain ⟨A', Cm, hC⟩ := exists_comparison_bound q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d B₀ κ CΨ M
    hq hq₁ hq₀ hq₀₁ hc₀ hvlo halo hal hahi hc hκ m₀ (A + max C₁ 0)
  refine ⟨A', Cm, fun E κ' => ?_⟩
  obtain ⟨CC, hCx⟩ := hC E κ'
  refine ⟨|CG| + |CC|, ?_⟩
  filter_upwards [hGx, hCx, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hGx hCx hL
  intro h₁ h₂ Sg Bg r a u v Bc G Ψ hdisj hpw hS₁ hS₂ hB₁ hB₂ hV hSr hBr hBi hr ha hab hu hv
    hBc hG₁ hG₂ hΨ₁ hΨ₂ hΨ₃
  -- R1: reindex the groups by `ι = ↥(Sg ∪ Bg)`
  have hadm := groupAdmissible_coe_sort hdisj hpw hS₁ hS₂ hB₁ hB₂ hV hSr hBr hBi
  obtain ⟨N, Aν, Bν, β, φ, φ', ψ, ψ', U, U', hpat, hβ, hbd⟩ := hGx _ _ hadm
  have hin : InertAdmissible K₀ CN alo ahi x a := ⟨hr, ha, hab⟩
  have hsl : AdmissibleSlots c x u v := ⟨hu, hv⟩
  have hco : CoreAdmissible B₀ x (Subtype.val : ↥(Sg ∪ Bg) → Finset ℕ) G :=
    ⟨fun n => by rw [hG₁ n, biUnion_coe_sort], hG₂⟩
  have hcu : CutoffAdmissible κ CΨ M x Ψ := ⟨hΨ₁, hΨ₂, hΨ₃⟩
  have hraw := hbd r a u v Bc G Ψ hin hsl hBc hco hcu
  have hcmp := fun ν => hCx h₁ h₂ _ _ hadm r a u v Bc G Ψ hin hsl hBc hco hcu J (Aν ν) (Bν ν)
    (φ ν) (φ' ν) (ψ ν) (ψ' ν) (U ν) (U' ν) (hpat ν)
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  -- the comparisons: `∑ |β| |S_ν| ≤ L^{C₁} |C_C| L^{-A''} ≤ |C_C| L^{-A}`
  have hcmp' : ‖∑ ν, β ν * strippedComparison x q₀ Subtype.val (Aν ν) (Bν ν) (φ ν) (φ' ν)
      (ψ ν) (ψ' ν) (centeredCore x q a u v Bc) G Ψ‖ ≤ |CC| * L ^ (-A) := by
    refine (norm_sum_le _ _).trans ?_
    have hLA : L ^ C₁ * L ^ (-(A + max C₁ 0)) ≤ L ^ (-A) := by
      rw [← Real.rpow_add hL0]
      exact Real.rpow_le_rpow_of_exponent_le hL (by linarith [le_max_left C₁ 0])
    calc ∑ ν, ‖β ν * strippedComparison x q₀ Subtype.val (Aν ν) (Bν ν) (φ ν) (φ' ν) (ψ ν)
          (ψ' ν) (centeredCore x q a u v Bc) G Ψ‖
        ≤ ∑ ν, ‖β ν‖ * (|CC| * L ^ (-(A + max C₁ 0))) := by
          refine Finset.sum_le_sum fun ν _ => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ((hcmp ν).trans ?_) (norm_nonneg _)
          gcongr
          exact le_abs_self _
      _ = (∑ ν, ‖β ν‖) * (|CC| * L ^ (-(A + max C₁ 0))) := by rw [Finset.sum_mul]
      _ ≤ L ^ C₁ * (|CC| * L ^ (-(A + max C₁ 0))) := by gcongr
      _ = |CC| * (L ^ C₁ * L ^ (-(A + max C₁ 0))) := by ring
      _ ≤ |CC| * L ^ (-A) := by gcongr
  -- `TwoSidedCorrelation`'s sum is `twoSidedSum` for `ι = ↥(Sg ∪ Bg)`
  have key : |TwoSided.twoSidedSum x q q₀ κ a u v Bc (Subtype.val : ↥(Sg ∪ Bg) → Finset ℕ) G Ψ| ≤
      (|CG| + |CC|) * L ^ (-A) := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    calc ‖(TwoSided.twoSidedSum x q q₀ κ a u v Bc (Subtype.val : ↥(Sg ∪ Bg) → Finset ℕ) G Ψ : ℂ)‖
        = ‖((TwoSided.twoSidedSum x q q₀ κ a u v Bc Subtype.val G Ψ : ℂ) +
              ∑ ν, β ν * strippedComparison x q₀ Subtype.val (Aν ν) (Bν ν) (φ ν) (φ' ν) (ψ ν)
                (ψ' ν) (centeredCore x q a u v Bc) G Ψ) -
            ∑ ν, β ν * strippedComparison x q₀ Subtype.val (Aν ν) (Bν ν) (φ ν) (φ' ν) (ψ ν)
              (ψ' ν) (centeredCore x q a u v Bc) G Ψ‖ := by rw [add_sub_cancel_right]
      _ ≤ CG * L ^ (-A) + |CC| * L ^ (-A) := (norm_sub_le _ _).trans (add_le_add hraw hcmp')
      _ ≤ (|CG| + |CC|) * L ^ (-A) := by
          rw [add_mul]
          gcongr
          exact le_abs_self _
  simpa only [TwoSided.twoSidedSum, centeredCore, slotCount, slotMean, markedWeight_coe_sort]
    using key

end Erdos408
