import Erdos408.Extraction.Allocation.CoreMoment
import Erdos408.Extraction.Allocation.Expansion
import Erdos408.Extraction.Allocation.Failure.Main

/-!
# The analytic inputs of E6 and E8

The two estimates that E6–E8 (`blueprint/rectangle_input.md` §4) use beyond
`TwoSidedCorrelation`, stated for the proxy coefficient `A_j(w + 1)` and the
core `G_j(w + 1)` on `w ≤ κ x`, uniformly in `2 ≤ j ≤ J_c`.

* `exists_failure_mass_le` (E6): with `c₁ = 1/4`, `c₂ = a/4` and
  `a = (1 - e⁻¹)/4500`, the proxy mass of the outcomes with fewer than `c₂ T`
  successes in either family is at most `20 κ (x/L) L^{-a/2}`; see
  `Erdos408.Extraction.Allocation.Failure.Main`. In the proof, `A_j ≤ G_j`
  since the allocation factor lies in `[0, 1]`; Chernoff bounds the failure
  probability by
  `e^{c₂ T} ∏_g (1 - θ s_g)`; the depth-two bound `ω 2^{1-ω} ≥ ω - C(ω, 2)`
  expands the `u`-side of each coin into residue conditions on at most two
  primes per group; one free core factor carries the residue law, by Bonferroni
  at depth `⌈6 T⌉` over the primes up to `Y` and partial summation;
  the `v`-side model factors exactly over the groups through the candidate part
  `v_P`, whose Euler product cancels the normalization `κ_j^j` of the proxy;
  and the `j - 1` other factors cost `exp(O(s²)) = L^{o(1)}`.
* `exists_sum_proxyCore_sq_le` (E8, the core moment bound at `r = 2`): the
  core has mean square at most `x L^{15}`; see
  `Erdos408.Extraction.Allocation.CoreMoment`.
-/

namespace Erdos408

open Filter

/-- E6: few successes have small proxy mass. -/
theorem exists_failure_mass_le (c Ch Cj κ : ℝ) (hc : 0 < c) (hκ : 1 < κ) :
    ∃ c₁ c₂ c₃ C : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 4 ∧ 0 < c₂ ∧ 0 < c₃ ∧ ∀ᶠ x : ℝ in atTop,
      ∀ j : ℕ, 2 ≤ j → j ≤ compositeCutoff Cj x →
        ∑ w ∈ Finset.Icc 1 ⌊κ * x⌋₊ with x / κ ≤ ((w : ℕ) : ℝ),
            proxyCoeff x (presieveExponent c Ch x) j (w + 1) * failureProb c₁ c₂ x w ≤
          C * (x / Real.log x) * Real.log x ^ (-c₃) := by
  refine ⟨1 / 4, failureDecay / 4, failureDecay / 2, 20 * κ, by norm_num, le_rfl,
    by have := failureDecay_pos; positivity, by have := failureDecay_pos; positivity, ?_⟩
  filter_upwards [eventually_freeFactorSum_le hc Ch Cj κ hκ, eventually_candidateGroups,
    eventually_presieveExponent hc Ch, eventually_gt_atTop 1, eventually_le_log 1,
    eventually_le_logLog 1] with x hfree hgroups hγ hx hlog hT j hj hjJ
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hγx : 1 ≤ x ^ presieveExponent c Ch x := Real.one_le_rpow hx.le hγ.1.le
  have hred := sum_proxyCoeff_mul_failureProb_le (c₁ := 1 / 4) (c₂ := failureDecay / 4)
    (κ := κ) (by norm_num) (by norm_num) hγx (fun g hg => (hgroups.1 g hg).1) j'
  refine hred.trans ?_
  have h1 := hfree j' hjJ (smallGroups x) (by simp)
  have h2 := hfree j' hjJ (bigGroups x) (by simp)
  have hX : ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * κ * x := by
    push_cast
    have := Nat.floor_le (show 0 ≤ κ * x by positivity)
    nlinarith
  exact final_le failureDecay_pos failureDecay_le_one (by linarith)
    (exp_logLog (by linarith)) (Nat.cast_nonneg _) hX h1 h2

/-- E8: the core has a fixed-log-power mean square. -/
theorem exists_sum_proxyCore_sq_le (c Ch Cj κ : ℝ) (hc : 0 < c) (hκ : 1 < κ) :
    ∃ C₅ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ j : ℕ, 2 ≤ j → j ≤ compositeCutoff Cj x →
      ∑ w ∈ Finset.Icc 1 ⌊κ * x⌋₊, proxyCore x (presieveExponent c Ch x) j (w + 1) ^ 2 ≤
        x * Real.log x ^ C₅ :=
  ⟨15, eventually_sum_proxyCore_sq_le hc Ch Cj κ hκ⟩

end Erdos408
