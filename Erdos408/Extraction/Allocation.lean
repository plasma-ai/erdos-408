module

public import Erdos408.Analytic.IntegerKernel
public import Erdos408.Analytic.PrimeTwist
public import Erdos408.Extraction.Allocation.Assembly
public import Erdos408.Extraction.Defs

/-!
# The proxy sum is small

Steps E6–E8 of the blueprint: `Prox_j = O(x L^{-1-c'})`.

* E6. Toss independent coins in the candidate groups with success
  probability
  `s_g = c₁ [q₀^{ω_g(u)-1} ω_g(u)/V_g] [q₀^{ω_g(v)-1} ω_g(v)/V_g]`, where
  `v = ∏ m_i` and `u = v - 1`. Outcomes with fewer than `c₂ T` successes in
  either family have mass `(x/L) L^{-c + o(1)}`, by the exact residue law
  `μ_p(0) = t/(p - 1 + t)`, `μ_p(a) = 1/(p - 1 + t)` (`t = 1/j`), a
  quantitative multigroup CRT at Bonferroni depth `O(T)`, and Chernoff.
  Discard them before the signed expansion (the paper, §6.4).
* E7. Expand the failure factors (`3^{|𝒞|} = L^{O(1)}` terms). Discard the
  candidate-square multiples (`x exp(-c L^{0.28})`). Each candidate prime of
  `v` then has `j` allocations with equal stripped coefficient, so
  `j^ω t^ω = 1`. This turns the coefficient into the core
  `G_j(v) = ∑_{e₁⋯e_j = v̄} ∏ [P⁻(e_i) > Y] [e_i > x^γ] / (D_j log e_i)`, which
  is invariant under every candidate prime (the paper, §6.3).
* E8. Clip `G_j` at a fixed power `L^{B_core}`, paying
  `L^{-B_core} ∑ G_j² ≤ x L^{-B_core-1-c_P+o(1)}` (the core moment bound of
  the paper, §6.3) in the raw sum. Apply `TwoSidedCorrelation`, with
  premises from `eventually_primeTwistBound` and
  `eventually_integerKernelBound`, to each term with the endpoint
  `𝒲 (f_𝔟 - C_𝔟)` for each inert monomial.

The argument at one scale is `abs_proxySum_le_at` (`Allocation/Assembly`): the
allocation identity (`Allocation/Coefficients`), the coin and inert-polynomial
expansions (`Allocation/Expansion`, `Allocation/MainTerm`), the admissibility of
the groups and bands for `TwoSidedCorrelation` (`Allocation/Groups`,
`Allocation/TwoSided`), and the mean square of the core (`Allocation/CoreMoment`).
The failure mass of E6 is `exists_failure_mass_le` (`Allocation/Analytic`).

See `blueprint/rectangle_input.md` §4 (E6–E8) and §§6.3–6.4 of the paper
*The normal order of the number of iterations of Euler's function* (Plasma AI,
2026).
-/

@[expose] public section

namespace Erdos408

open Filter Real

/-- E6–E8: the proxy sum is `O(x L^{-1-c'})`, uniformly in `2 ≤ j ≤ J_c`, the
admissible slots, coefficients `0 ≤ 𝔟 ≤ 1`, and cutoffs in the class. -/
theorem eventually_abs_proxySum_le (h₂ : TwoSidedCorrelation) (q cw : ℝ) (hq : 0 < q)
    (hq₁ : q < 1) (hcw : 0 < cw) (hcw₁ : cw ≤ (1 - q) ^ 2 / 3) :
    ∀ (K : ℕ) (CN c Ch Cj κ CΦ : ℝ) (M : ℕ → ℝ), 1 ≤ K → 0 < c → 1 < κ →
      ∃ C c' : ℝ, 0 < c' ∧ ∀ᶠ x : ℝ in atTop,
        ∀ k ≤ 2, ∀ (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) (Φ : ℝ → ℝ) (j : ℕ),
          AdmissibleSlots c x u v → (∀ Q, 0 ≤ B Q ∧ B Q ≤ 1) → IsCutoff κ CΦ M x Φ →
          2 ≤ j → j ≤ compositeCutoff Cj x →
          |proxySum q cw K CN x (presieveExponent c Ch x) κ j Φ u v B| ≤
            C * (x / Real.log x) * Real.log x ^ (-c') := by
  intro K CN c Ch Cj κ CΦ M hK hc hκ
  obtain ⟨c₁, c₂, c₃, C₃, hc₁, hc₁', hc₂, hc₃, hfail⟩ := exists_failure_mass_le c Ch Cj κ hc hκ
  obtain ⟨C₅, hcore⟩ := exists_sum_proxyCore_sq_le c Ch Cj κ hc hκ
  set c' := c₃ / 2 with hc'
  have hc'0 : 0 < c' := by positivity
  have hc₃' : c₃ = 2 * c' := by rw [hc']; ring
  -- the two-sided estimate for each number `d ≤ 2` of weighted slots
  have hbody : ∀ d : Fin 3, ∃ Cs : ℝ, ∀ᶠ x : ℝ in atTop,
      TwoSidedBody q (1 / 2) c₂ 1 (1 / 2) 3 (11 / 100) (39 / 200) K (max CN 0) c d
        (C₅ + 1 + 2 * c') κ (max CΦ 0) (fun r => κ * M r + r * M (r - 1)) (5 + c') Cs x :=
    fun d => exists_twoSidedBody h₂ q (1 / 2) c₂ 1 (1 / 2) 3 (11 / 100) (39 / 200) K (max CN 0) c
      d (C₅ + 1 + 2 * c') κ (max CΦ 0) _ (5 + c') hq hq₁ (by norm_num) (by norm_num) hc₂
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc (by omega) hκ
  choose Cs hCs using hbody
  refine ⟨|Cs 0| + |Cs 1| + |Cs 2| + |C₃| + 2, c', hc'0, ?_⟩
  filter_upwards [Filter.eventually_all.2 hCs, hfail, hcore, eventually_candidateGroups,
    eventually_inertBands hK CN, eventually_harmonicMass_band, eventually_sum_primesIoc_le hc,
    Filter.eventually_gt_atTop 1, Filter.eventually_ge_atTop κ, eventually_le_logLog 1,
    eventually_endpoint_budget |M 0| hc hc'0, eventually_terms_budget K CN,
    eventually_squares_budget κ (2 + 4 * c' + C₅)]
    with x hCsx hfailx hcorex hgroups hbands hmassband hH hx hxκ hT hBd hterms hsq
  intro k hk u v B Φ j hadm hB hΦ hj hjJ
  have hfailx' := hfailx j hj hjJ
  rw [hc₃'] at hfailx'
  have hbound := abs_proxySum_le_at hq hq₁ hcw hcw₁ hκ hc hc₁ hc₁'
    (hCsx ⟨k, by omega⟩) hgroups hbands hmassband hH hx hxκ hT
    hBd hterms hsq hfailx' (hcorex j hj hjJ) hk hadm hB hΦ hj
  refine hbound.trans ?_
  have hL : 0 < Real.log x := Real.log_pos hx
  have hpos : 0 ≤ x / Real.log x * Real.log x ^ (-c') := by
    have := rpow_pos_of_pos hL (-c')
    have : 0 < x := by linarith
    positivity
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hpos
  have hk' : |Cs ⟨k, by omega⟩| ≤ |Cs 0| + |Cs 1| + |Cs 2| := by
    interval_cases k
    · exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg le_rfl (abs_nonneg _)) (abs_nonneg _)
    · exact le_add_of_le_of_nonneg (le_add_of_nonneg_left (abs_nonneg _)) (abs_nonneg _)
    · exact le_add_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _))
  linarith

end Erdos408
