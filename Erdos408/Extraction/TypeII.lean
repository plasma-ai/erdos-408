import Erdos408.Analytic.IntegerKernel
import Erdos408.Analytic.ProxyTwist
import Erdos408.Extraction.TypeII.Eventually

/-!
# Replacing primes by the damped proxy

Steps E4–E5 of the blueprint. In the composite sum `Comp_j`, replace the
`j` primes one at a time by the unstripped damped proxy (E4), then strip
the candidate primes (E5), arriving at the proxy sum `Prox_j`.

* E4. Telescope one factor `m` at a time. Aggregate the other `j - 1`
  factors, with their `> x^γ` cutoffs, into one companion coefficient
  `β(n)`, and split only `(m, n)` into dyads (`O(L²)` boxes, independent of
  `j`). The companion's mean square is `≤ H L^{-1+o(1)}` (the paper, §6.3);
  clip it at a fixed power `L^{B_comp}`. Replace `Φ((mn - 1)/x)` by `Φ(mn/x)`
  and separate `m, n` by Fourier inversion in `log(mn/x)`. Expand the inert
  polynomial into monomials (coefficient mass `2^N = L^{o(1)}`). In each
  monomial, take one band per cluster as the distinguished bands of
  `OneSidedTypeII`, and put the other band weights and `f_𝔟 - C_𝔟`, clipped
  and normalized, into the invariant endpoint `F`. The coefficient
  `α_m = m^{iv}([m prime, m > x^γ] - a_j^0(m))` satisfies P1–P4 by
  `eventually_proxyTwist`, and the kernel premise holds by
  `eventually_kernel_premise`.
* E5. `a_j^0 → a_j`. The weighted count of `log(m / m̄)` on a dyad is
  `≪ H D_j L^{0.45} / j`. The threshold strips and the denominator change
  cost `(x/L) L^{-c + o(1)}`, using full `j`-factor boxes, at most
  `(j + O(1)) (C L)^{j-1}` of them, each with proxy mass `≤ x / (γ L)^j`.

See `blueprint/rectangle_input.md` §4 (E4–E5) and §6.3 of the paper
*The normal order of the number of iterations of Euler's function* (Plasma AI,
2026).
-/

namespace Erdos408

open Filter Real

/-- E4–E5: the composite sum and the proxy sum differ by `O(x L^{-1-c'})`,
uniformly in `2 ≤ j ≤ J_c`, the admissible slots, coefficients `0 ≤ 𝔟 ≤ 1`,
and cutoffs in the class. -/
theorem eventually_compositeSum_sub_proxySum (h₁ : OneSidedTypeII) (q cw : ℝ) (hq : 0 < q)
    (hq₁ : q < 1) (hcw : 0 < cw) (hcw₁ : cw ≤ (1 - q) ^ 2 / 3) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ (CN c Ch Cj κ CΦ : ℝ) (M : ℕ → ℝ), 0 < c → 1 < κ →
      ∃ C c' : ℝ, 0 < c' ∧ ∀ᶠ x : ℝ in atTop,
        ∀ k ≤ 2, ∀ (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) (Φ : ℝ → ℝ) (j : ℕ),
          AdmissibleSlots c x u v → (∀ Q, 0 ≤ B Q ∧ B Q ≤ 1) → IsCutoff κ CΦ M x Φ →
          2 ≤ j → j ≤ compositeCutoff Cj x →
          |compositeSum q cw K CN x (presieveExponent c Ch x) κ j Φ u v B -
              proxySum q cw K CN x (presieveExponent c Ch x) κ j Φ u v B| ≤
            C * (x / Real.log x) * Real.log x ^ (-c') := by
  have hcw1 : cw ≤ 1 := by nlinarith
  obtain ⟨K₀, hK₀⟩ := TypeII.typeII_box h₁ hq hq₁ fun CX B => eventually_kernel_premise CX B
  refine ⟨max K₀ 1, fun K hK CN c Ch Cj κ CΦ M hc hκ => ?_⟩
  obtain ⟨C₂, hC₂, hbox⟩ := hK₀ K (le_of_max_le_left hK) c Ch Cj κ hc hκ
    fun A Cm Kan => eventually_proxyTwist c Ch Cj A Cm Kan hc
  obtain ⟨c₃, hc₃, hmert⟩ := TypeII.mertens_third_lower
  obtain ⟨A₁, C₁r, hA₁, hG⟩ := TypeII.sum_dampedWeight_le
  obtain ⟨E₂, hE₂0, hE₂⟩ := TypeII.sum_inv_primes_le
  obtain ⟨L₀, hL₀⟩ := TypeII.harmonicMass_band_ge
  obtain ⟨EM1, hEM10, hEM1⟩ := mertens_first
  obtain ⟨EM2, -, hEM2⟩ := mertens_second
  refine ⟨2 * κ * M 0 + 25 * M 0 * C₂ * κ + 56 * κ ^ 2 * M 1 +
    2 * κ * M 0 * (A₁ / c₃ + 1) * (6 * (A₁ / c₃ + 1) + 4 / c₃), 1 / 20, by norm_num, ?_⟩
  filter_upwards [TypeII.eventually_largeX (CN := CN) (CΦ := CΦ) (C₁r := C₁r) (E₂ := E₂)
    (L₀ := L₀) (EM1 := EM1) (EM2 := EM2) hc hκ hc₃ hbox] with x hX
  exact TypeII.final_at hq hq₁ hcw.le hcw1 (le_of_max_le_right hK) hc hκ hC₂ hc₃ hmert hA₁ hG
    hE₂0 hE₂ hL₀ hEM10 hEM1 hEM2 hX

end Erdos408
