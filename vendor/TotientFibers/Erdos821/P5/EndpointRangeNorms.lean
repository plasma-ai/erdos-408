import Erdos821.P5.PhysicalNormTheorem

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- The physical endpoint norm exponent is chosen before J and the probe bound. -/
theorem eventual_physical_endpoint_norm_any_power (P : Geometry) (C : ℝ) :
    ∃ C₃ : ℝ, ∀ (J m : ℕ) (γ r : ℝ), 0 < γ → 0 ≤ r →
      ∀ᶠ x : ℝ in atTop, ∀ (G : PrimeGroups)
        (A : Blueprint.Graph.Model P.graph G.graph J m) (X τ η : ℝ) (E : Endpoint)
        (f : A.State → ℂ),
        Admissible P x G → EndpointBound x C τ η E →
        x ^ γ ≤ X → X ≤ x ^ r →
        (∀ n ∈ Blueprint.Graph.dyad X, ∀ a : A.Labels,
          G.graph.physical (J + P.ell) n a → ‖f (n, a)‖ ≤ ‖endpoint G x E n.toNat‖) →
        A.normOn ((Blueprint.Graph.dyad X).product Finset.univ) f ≤
          Real.sqrt X * L x ^ C₃ := by
  obtain ⟨c, K, hc, hK, hm⟩ := physical_endpoint_square_sum
  refine ⟨2 * C + c / 2 + 1, ?_⟩
  intro J m γ r hγ hr
  let R := Real.log 4 + r
  have hR : 0 < R := by
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    dsimp [R]
    linarith
  let K₀ := K * R ^ c
  have hK₀ : 0 < K₀ := mul_pos hK (Real.rpow_pos_of_pos hR c)
  filter_upwards [eventual_listProduct_le P (J + P.ell) γ hγ,
    eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop K₀] with x hx hxx hKx
  intro G A X τ η E f hG hE hXlo hXhi hf
  have hL : 0 < L x := by linarith [hx.1]
  have hxpos : 0 < x := by linarith
  have hX : 1 ≤ X := (Real.one_le_rpow hxx hγ.le).trans hXlo
  have hXpos : 0 < X := by linarith
  have hsum := hm G x C τ η X E hx.1 hE hX
    (fun g => lt_of_lt_of_le P.positive.2.2.1 (hG.2.2.1 g).1)
    P.graph J m A (fun a => (hx.2 G hG a).trans hXlo)
  have hdom : (∑ z ∈ (Blueprint.Graph.dyad X).product Finset.univ,
      A.stateMass z * ‖f z‖ ^ 2) ≤
      ∑ z ∈ (Blueprint.Graph.dyad X).product Finset.univ,
        A.stateMass z * ‖endpoint G x E z.1.toNat‖ ^ 2 := by
    apply Finset.sum_le_sum
    rintro ⟨n, a⟩ hz
    have hn := (Finset.mem_product.mp hz).1
    by_cases hp : G.graph.physical (J + P.ell) n a
    · apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hf n hn a hp) 2)
      simpa only [Blueprint.Graph.Model.stateMass, if_pos hp] using
        markMass_nonneg G.graph (J + P.ell)
          (fun g => by rw [graph_mass]; exact lt_of_lt_of_le P.positive.2.2.1 (hG.2.2.1 g).1)
    · simp only [Blueprint.Graph.Model.stateMass, if_neg hp, zero_mul, le_refl]
  have hlogX : Real.log X ≤ r * L x := by
    apply (Real.log_le_log hXpos hXhi).trans
    rw [Real.log_rpow hxpos]
    simp only [L, mul_comm, le_refl]
  have hlog : Real.log (4 * X) ≤ R * L x := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hXpos.ne']
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h := mul_le_mul_of_nonneg_left hx.1 hlog4
    dsimp [R]
    nlinarith
  have hlogpow : Real.log (4 * X) ^ c ≤ R ^ c * L x ^ c := by
    calc
      _ ≤ (R * L x) ^ c := Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog hc
      _ = _ := Real.mul_rpow hR.le hL.le
  have hKpow : K₀ ≤ L x ^ (2 : ℕ) := by
    have hKx' : K₀ ≤ L x := hKx
    nlinarith [hx.1, hKx']
  have hmain : K * X * L x ^ (4 * C) * Real.log (4 * X) ^ c ≤
      X * L x ^ (4 * C + c + 2) := by
    calc
      _ ≤ K * X * L x ^ (4 * C) * (R ^ c * L x ^ c) :=
        mul_le_mul_of_nonneg_left hlogpow (by positivity)
      _ = K₀ * X * L x ^ (4 * C + c) := by
        rw [Real.rpow_add hL]; dsimp [K₀]; ring
      _ ≤ L x ^ (2 : ℕ) * X * L x ^ (4 * C + c) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKpow hXpos.le) (by positivity)
      _ = _ := by rw [Real.rpow_add hL (4 * C + c) 2, Real.rpow_two]; ring
  change Real.sqrt _ ≤ _
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hexp : (2 * C + c / 2 + 1) * (2 : ℝ) = 4 * C + c + 2 := by ring
  rw [mul_pow, Real.sq_sqrt hXpos.le,
    ← Real.rpow_mul_natCast hL.le (2 * C + c / 2 + 1) 2]
  simp only [Nat.cast_ofNat]
  rw [hexp]
  exact hdom.trans (hsum.trans hmain)

end Erdos821.P5Core
