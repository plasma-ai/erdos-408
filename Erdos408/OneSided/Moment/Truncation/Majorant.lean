import Erdos408.OneSided.Moment.Phased.Edge
import Erdos408.OneSided.Moment.Phased.Rows
import Erdos408.OneSided.Moment.Truncation.Cap

/-!
# The absolute majorant of the truncation error

The second step of M3 (`eventually_distinctSum_truncation` in `Moment/Memory.lean`, PD
`mem:truncation-error`). By `distinctSum_sub_eq`, the difference of the distinct-birth history
sums with caps `B ≤ B'` runs over histories that leave the memories of size at most `B`. From
an empty memory such a history has more than `B - K N` ghost births
(`lt_of_not_staysBelow`). Inserting a factor `2` at every ghost birth therefore gains
`2^{-(B + 1 - KN)}` on these histories, and the inserted majorant is bounded over *all*
histories by a weighted row iteration (`sum_history_le_of_rows`), with no use of distinctness.

* `dblGhostCoef`: the ghost coefficient with the creation coefficient doubled. Its modulus is
  `2^{|batch|}` times the modulus of the ghost coefficient (`norm_dblGhostCoef`), so
  `‖w(s, h)‖ 2^{ghost births} = ∏ ‖dblGhost‖ ∏ ‖edge‖` (`norm_chainWeight_mul_two_pow`).
* `sum_dblGhostCoef_le`: the doubled ghost has weighted row sums at most
  `exp(v₀ · 4K/ρ)` against `v₀^{size}`, with `v₀ = 1/(ρ(1 - ρ²))` (`ghost_row`).
* `sum_chainEdgeCoef_weight_le`: an edge stores at most `K` particles, so a row bound for the
  edge gives a row bound against `v₀^{size}` at the cost of `v₀^K`.
* `norm_distinctSum_sub_mul_le`: if the doubled ghosts and the edges have weighted row sums at
  most `R_G` and `R_E`, then
  `‖distinctSum(B') - distinctSum(B)‖ 2^{B+1} ≤ 2^{KN} R_G^{N+1} R_E^N ∑_s μ(s) |𝐛(s)|`.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

section Majorant

variable (q x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

open scoped Classical in
/-- The doubled ghost coefficient: `chainGhostCoef` with the creation coefficient
`cre(p, ℓ) = -η'_j V(p)/ρ` replaced by `2 cre(p, ℓ)`. -/
def dblGhostCoef (N j : ℕ) (s : ChainState x d Y d₀ u v r B)
    (c : (Particle x d → ℕ) × (Particle x d → ℕ)) : ℂ :=
  ghostCoef (HitsAt x d s.1.1) (fun xp : Particle x d => primeWeight q x d N xp.1.1)
      (-dampDefect q N j / pendingWeight q) ((1 - dampDefect q N j) / pendingWeight q ^ 2)
    (fun xp : Particle x d => 2 * (-dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q))
    B s.2.2 c

/-- The weight `v₀ = 1/(ρ(1 - ρ²))` of the ghost row bound. -/
def truncV : ℝ := 1 / (pendingWeight q * (1 - pendingWeight q ^ 2))

variable {q x d Y d₀ u v r B}

/-- Doubling the creation coefficient multiplies the modulus by `2^{|batch|}`. -/
theorem norm_dblGhostCoef (N j : ℕ) (s : ChainState x d Y d₀ u v r B) (c : GhostChoice x d) :
    ‖dblGhostCoef q x d Y d₀ u v r B N j s c‖ =
      2 ^ memSize c.2 * ‖chainGhostCoef q x d Y d₀ u v r B N j s c‖ := by
  by_cases hv : GhostValid (HitsAt x d s.1.1) B s.2.2.1 c
  · rw [dblGhostCoef, chainGhostCoef, ghostCoef, ghostCoef, ite_eq_left hv, ite_eq_left hv,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [show (∏ xp : Particle x d, ghostFactor (fun xp : Particle x d => primeWeight q x d N xp.1.1)
        (-dampDefect q N j / pendingWeight q) ((1 - dampDefect q N j) / pendingWeight q ^ 2)
        (fun xp : Particle x d => 2 * (-dampDefect q N j * primeMass x d xp.1.1 /
          pendingWeight q)) xp (hitPart (HitsAt x d s.1.1) s.2.2.1 xp) (c.1 xp) (c.2 xp)) =
        (2 : ℝ) ^ memSize c.2 * ∏ xp : Particle x d, ghostFactor
          (fun xp : Particle x d => primeWeight q x d N xp.1.1)
          (-dampDefect q N j / pendingWeight q) ((1 - dampDefect q N j) / pendingWeight q ^ 2)
          (fun xp : Particle x d => -dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q)
          xp (hitPart (HitsAt x d s.1.1) s.2.2.1 xp) (c.1 xp) (c.2 xp) by
      rw [memSize, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
      refine prod_congr rfl fun xp _ => ?_
      simp only [ghostFactor, mul_pow]
      ring, abs_mul, abs_of_nonneg (pow_nonneg zero_le_two _)]
  · rw [dblGhostCoef, chainGhostCoef, ghostCoef, ghostCoef, ite_eq_right hv, ite_eq_right hv,
      norm_zero, mul_zero]

/-- **The inserted factors**: `‖w(s, h)‖ 2^{ghost births} = ∏_j ‖dblGhost_j‖ ∏_j ‖edge_j‖`. -/
theorem norm_chainWeight_mul_two_pow {A₀ : ℝ} {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (h : History x d Y d₀ u v r N) :
    ‖chainWeight q A₀ s h‖ * 2 ^ ghostBirths x d Y d₀ u v r h =
      (∏ j : Fin (N + 1), ‖dblGhostCoef q x d Y d₀ u v r B N j (chainVisit s h j) (h.1 j)‖) *
        ∏ j : Fin N, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N
          (chainGhostOut x d Y d₀ u v r B (chainVisit s h j.castSucc) (h.1 j.castSucc))
            (h.2 j)‖ := by
  simp only [chainWeight, ghostBirths, norm_mul, norm_prod, norm_dblGhostCoef,
    prod_mul_distrib, prod_pow_eq_pow_sum]
  ring

/-! ### Band facts -/

/-- A particle's prime is a band prime. -/
private theorem fst_mem_bandPrimes' (xp : Particle x d) : xp.1.1 ∈ bandPrimes x d := by
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.1 xp.2
  obtain ⟨ℓ, -, hℓ⟩ := mem_image.1 hxp
  rw [← hℓ]
  exact hp

/-- The hitting particles have one line per band prime, so a sum over them of a nonnegative
function of the prime is at most the sum over the band primes. -/
private theorem sum_hits_le_sum_bandPrimes' (z : ℤ × ℤ) {f : ℕ → ℝ} (hf : ∀ p, 0 ≤ f p) :
    ∑ xp with HitsAt x d z xp, f xp.1.1 ≤ ∑ p ∈ bandPrimes x d, f p := by
  rw [← sum_image (f := f) (g := fun xp : Particle x d => xp.1.1)]
  · exact sum_le_sum_of_subset_of_nonneg
      (image_subset_iff.2 fun xp _ => fst_mem_bandPrimes' xp) fun p _ _ => hf p
  · intro xp hxp yp hyp h
    have hxp' : lineOf xp.1.1 z = xp.1.2 := (mem_filter.1 (mem_coe.1 hxp)).2
    have hyp' : lineOf yp.1.1 z = yp.1.2 := (mem_filter.1 (mem_coe.1 hyp)).2
    refine Subtype.ext (Prod.ext h ?_)
    rw [← hxp', ← hyp']
    exact congrArg (lineOf · z) h

/-- With band masses at most `1`, `∑_{p band prime} 1/p ≤ ∑_i V_i ≤ K`. -/
private theorem sum_one_div_bandPrimes_le' (hV : ∀ i, harmonicMass (band x (d.a i)) ≤ 1) :
    ∑ p ∈ bandPrimes x d, (1 : ℝ) / p ≤ K :=
  calc ∑ p ∈ bandPrimes x d, (1 : ℝ) / p
      ≤ ∑ p ∈ bandPrimes x d, ∑ i, if p ∈ band x (d.a i) then (1 : ℝ) / p else 0 := by
        refine sum_le_sum fun p hp => ?_
        obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
        calc (1 : ℝ) / p = if p ∈ band x (d.a i) then (1 : ℝ) / p else 0 :=
              (ite_eq_left hpi).symm
          _ ≤ ∑ i, if p ∈ band x (d.a i) then (1 : ℝ) / p else 0 :=
              single_le_sum (f := fun i => if p ∈ band x (d.a i) then (1 : ℝ) / p else 0)
                (fun j _ => by split_ifs <;> positivity) (mem_univ i)
    _ = ∑ i, ∑ p ∈ bandPrimes x d, if p ∈ band x (d.a i) then (1 : ℝ) / p else 0 := sum_comm
    _ = ∑ i, harmonicMass (band x (d.a i)) := by
        refine sum_congr rfl fun i _ => ?_
        rw [sum_ite_mem, inter_eq_right.2
          (show band x (d.a i) ⊆ bandPrimes x d from fun p hp => mem_biUnion.2 ⟨i, mem_univ i, hp⟩)]
        rfl
    _ ≤ ∑ _i : Fin K, (1 : ℝ) := sum_le_sum fun i _ => hV i
    _ = K := by simp

/-- The harmonic mass `V(p)` of the bands containing `p` is nonnegative. -/
private theorem primeMass_nonneg'' (p : ℕ) : 0 ≤ primeMass x d p :=
  sum_nonneg fun i _ => by
    split_ifs
    · exact sum_nonneg fun p _ => by positivity
    · exact le_rfl

/-- `ρ⁴ = √q`. -/
private theorem pendingWeight_pow_four' (hq : 0 < q) : pendingWeight q ^ 4 = Real.sqrt q := by
  unfold pendingWeight
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, Real.sqrt_eq_rpow]
  norm_num

/-- The damping defects are in `[0, 1]`. -/
private theorem dampDefect_mem_Icc' (hq : 0 < q) (hq₁ : q < 1) (N j : ℕ) :
    0 ≤ dampDefect q N j ∧ dampDefect q N j ≤ 1 := by
  have hs : Real.sqrt q ≤ 1 := Real.sqrt_le_one.2 hq₁.le
  unfold dampDefect
  split_ifs <;> constructor <;> linarith [Real.sqrt_nonneg q]

/-- `v₀ ≥ 1`. -/
theorem one_le_truncV (hq : 0 < q) (hq₁ : q < 1) : 1 ≤ truncV q := by
  have hρ0 : 0 < pendingWeight q := Real.rpow_pos_of_pos hq _
  have hρ1 : pendingWeight q < 1 := Real.rpow_lt_one hq.le hq₁ (by norm_num)
  have hρ2 : pendingWeight q ^ 2 < 1 := pow_lt_one₀ hρ0.le hρ1 (by norm_num)
  have hw : pendingWeight q * (1 - pendingWeight q ^ 2) ≤ 1 :=
    calc pendingWeight q * (1 - pendingWeight q ^ 2) ≤ 1 * 1 :=
          mul_le_mul hρ1.le (by nlinarith) (by linarith) zero_le_one
      _ = 1 := one_mul 1
  rw [truncV, le_div_iff₀ (mul_pos hρ0 (by linarith)), one_mul]
  exact hw

/-! ### The row bounds -/

/-- **The doubled ghost row bound**: against `v₀^{size}` with `v₀ = 1/(ρ(1 - ρ²))`, the doubled
ghost has row sums at most `exp(v₀ · 4K/ρ)`. The hitting particles carry
`∑ |2 cre| ν ≤ (4/ρ) ∑_p 1/p ≤ 4K/ρ`, since `V(p) ν(p) ≤ 2/p`. -/
theorem sum_dblGhostCoef_le (hq : 0 < q) (hq₁ : q < 1) {N : ℕ}
    (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hVν : ∀ p ∈ bandPrimes x d, primeMass x d p * primeWeight q x d N p ≤ 2 * (1 / p))
    (hV₁ : ∀ i, harmonicMass (band x (d.a i)) ≤ 1) (j : ℕ) (t : ChainState x d Y d₀ u v r B) :
    ∑ c ∈ multBox B ×ˢ multBox B, ‖dblGhostCoef q x d Y d₀ u v r B N j t c‖ *
        truncV q ^ memSize (chainGhostOut x d Y d₀ u v r B t c).2.2.1 ≤
      Real.exp (truncV q * (4 * K / pendingWeight q)) * truncV q ^ memSize t.2.2.1 := by
  set ρ := pendingWeight q with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hq _
  have hρ1 : ρ < 1 := Real.rpow_lt_one hq.le hq₁ (by norm_num)
  have hρ2 : ρ ^ 2 < 1 := pow_lt_one₀ hρ0.le hρ1 (by norm_num)
  have hv₀ : 0 < truncV q := lt_of_lt_of_le zero_lt_one (one_le_truncV hq hq₁)
  obtain ⟨hη0, hη1⟩ := dampDefect_mem_Icc' hq hq₁ N j
  -- `0 ≤ surv ≤ ρ²`, since `q_j ≤ √q = ρ⁴`
  have hsurv0 : 0 ≤ (1 - dampDefect q N j) / ρ ^ 2 := div_nonneg (by linarith) (by positivity)
  have hsurv1 : (1 - dampDefect q N j) / ρ ^ 2 ≤ ρ ^ 2 := by
    have hqs : q ≤ Real.sqrt q := by
      have h₁ := Real.mul_self_sqrt hq.le
      have h₂ : Real.sqrt q ≤ 1 := Real.sqrt_le_one.2 hq₁.le
      calc q = Real.sqrt q * Real.sqrt q := h₁.symm
        _ ≤ Real.sqrt q * 1 := mul_le_mul_of_nonneg_left h₂ (Real.sqrt_nonneg q)
        _ = Real.sqrt q := mul_one _
    have hqj : 1 - dampDefect q N j ≤ ρ ^ 4 := by
      rw [hρ, pendingWeight_pow_four' hq]
      unfold dampDefect
      split_ifs <;> linarith
    rw [div_le_iff₀ (by positivity)]
    calc 1 - dampDefect q N j ≤ ρ ^ 4 := hqj
      _ = ρ ^ 2 * ρ ^ 2 := by ring
  -- `surv + |del|/v₀ ≤ ρ² + (1/ρ) ρ (1 - ρ²) = 1`
  have hdel : (1 - dampDefect q N j) / ρ ^ 2 + |-dampDefect q N j / ρ| / truncV q ≤ 1 := by
    have h₁ : |-dampDefect q N j / ρ| ≤ 1 / ρ := by
      rw [abs_div, abs_neg, abs_of_nonneg hη0, abs_of_pos hρ0]
      exact div_le_div_of_nonneg_right hη1 hρ0.le
    have h₂ : 1 / ρ / truncV q = 1 - ρ ^ 2 := by
      rw [truncV, ← hρ]
      field_simp
    calc (1 - dampDefect q N j) / ρ ^ 2 + |-dampDefect q N j / ρ| / truncV q
        ≤ ρ ^ 2 + 1 / ρ / truncV q :=
          add_le_add hsurv1 (div_le_div_of_nonneg_right h₁ hv₀.le)
      _ = 1 := by rw [h₂]; ring
  -- the creation mass of the hitting particles
  have hcre : ∑ xp with HitsAt x d t.1.1 xp,
      |2 * (-dampDefect q N j * primeMass x d xp.1.1 / ρ)| * primeWeight q x d N xp.1.1 ≤
        4 * K / ρ :=
    calc ∑ xp with HitsAt x d t.1.1 xp,
          |2 * (-dampDefect q N j * primeMass x d xp.1.1 / ρ)| * primeWeight q x d N xp.1.1
        ≤ ∑ xp with HitsAt x d t.1.1 xp, 4 / ρ * (1 / (xp.1.1 : ℝ)) := by
          refine sum_le_sum fun xp _ => ?_
          have h := hVν _ (fst_mem_bandPrimes' xp)
          rw [abs_mul, abs_div, abs_mul, abs_neg, abs_of_nonneg hη0,
            abs_of_nonneg (primeMass_nonneg'' _), abs_of_pos hρ0, abs_two]
          calc 2 * (dampDefect q N j * primeMass x d xp.1.1 / ρ) * primeWeight q x d N xp.1.1
              = 2 * dampDefect q N j / ρ *
                  (primeMass x d xp.1.1 * primeWeight q x d N xp.1.1) := by ring
            _ ≤ 2 * 1 / ρ * (2 * (1 / (xp.1.1 : ℝ))) :=
                mul_le_mul (div_le_div_of_nonneg_right (by linarith) hρ0.le) h
                  (mul_nonneg (primeMass_nonneg'' _) (hν _)) (by positivity)
            _ = 4 / ρ * (1 / (xp.1.1 : ℝ)) := by ring
      _ ≤ ∑ p ∈ bandPrimes x d, 4 / ρ * (1 / (p : ℝ)) :=
          sum_hits_le_sum_bandPrimes' t.1.1 (f := fun p => 4 / ρ * (1 / (p : ℝ)))
            fun p => by positivity
      _ = 4 / ρ * ∑ p ∈ bandPrimes x d, (1 : ℝ) / p := (mul_sum _ _ _).symm
      _ ≤ 4 / ρ * K := mul_le_mul_of_nonneg_left (sum_one_div_bandPrimes_le' hV₁) (by positivity)
      _ = 4 * K / ρ := by ring
  calc ∑ c ∈ multBox B ×ˢ multBox B, ‖dblGhostCoef q x d Y d₀ u v r B N j t c‖ *
        truncV q ^ memSize (chainGhostOut x d Y d₀ u v r B t c).2.2.1
      ≤ Real.exp (truncV q * ∑ xp with HitsAt x d t.1.1 xp,
          |2 * (-dampDefect q N j * primeMass x d xp.1.1 / ρ)| * primeWeight q x d N xp.1.1) *
          truncV q ^ memSize t.2.2.1 :=
        ghost_row (fun xp => hν _) hsurv0 hv₀ hdel t.2.2
    _ ≤ Real.exp (truncV q * (4 * K / ρ)) * truncV q ^ memSize t.2.2.1 :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hcre hv₀.le)) (pow_nonneg hv₀.le _)

/-- **The weighted edge row bound**: an edge stores at most `K` particles, so for `v₀ ≥ 1` a
bound `R` on its absolute row sums gives the bound `v₀^K R` against `v₀^{size}`. -/
theorem sum_chainEdgeCoef_weight_le {A₀ v₀ R : ℝ} {N : ℕ} (hv₀ : 1 ≤ v₀)
    (t : ChainState x d Y d₀ u v r B)
    (hR : ∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N t c‖ ≤ R) :
    ∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N t c‖ *
        v₀ ^ memSize (chainEdgeOut x d Y d₀ u v r B t c).2.2.1 ≤
      v₀ ^ K * R * v₀ ^ memSize t.2.2.1 :=
  calc ∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N t c‖ *
        v₀ ^ memSize (chainEdgeOut x d Y d₀ u v r B t c).2.2.1
      ≤ ∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N t c‖ *
          (v₀ ^ K * v₀ ^ memSize t.2.2.1) := by
        refine sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [← pow_add, add_comm K]
        exact pow_le_pow_right₀ hv₀ (memSize_chainEdgeOut_le_add t c)
    _ = (∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N t c‖) *
          (v₀ ^ K * v₀ ^ memSize t.2.2.1) := (sum_mul _ _ _).symm
    _ ≤ R * (v₀ ^ K * v₀ ^ memSize t.2.2.1) :=
        mul_le_mul_of_nonneg_right hR (by positivity)
    _ = v₀ ^ K * R * v₀ ^ memSize t.2.2.1 := by ring

/-! ### The majorant -/

open scoped Classical in
/-- **The truncation majorant**: for caps `B ≤ B'`, if the doubled ghosts and the edges of the
cap-`B'` chain have row sums at most `R_G` and `R_E` against `v₀^{size}` with `v₀ ≥ 1`, then
`‖distinctSum(B') - distinctSum(B)‖ 2^{B+1} ≤ 2^{KN} R_G^{N+1} R_E^N ∑_s μ(s) |𝐛(s)|`. -/
theorem norm_distinctSum_sub_mul_le {A₀ v₀ RG RE : ℝ} {B' N : ℕ} (hB : B ≤ B') (hv₀ : 1 ≤ v₀)
    (hRG : 0 ≤ RG) (hRE : 0 ≤ RE) (hμ : ∀ s, 0 ≤ chainMeasure q x d Y d₀ u v r B' N s)
    (hG : ∀ (j : ℕ) (t : ChainState x d Y d₀ u v r B'),
      ∑ c ∈ multBox B' ×ˢ multBox B', ‖dblGhostCoef q x d Y d₀ u v r B' N j t c‖ *
          v₀ ^ memSize (chainGhostOut x d Y d₀ u v r B' t c).2.2.1 ≤
        RG * v₀ ^ memSize t.2.2.1)
    (hE : ∀ t : ChainState x d Y d₀ u v r B',
      ∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B' N t c‖ *
          v₀ ^ memSize (chainEdgeOut x d Y d₀ u v r B' t c).2.2.1 ≤
        RE * v₀ ^ memSize t.2.2.1) :
    ‖distinctSum q A₀ x d Y d₀ u v r B' N - distinctSum q A₀ x d Y d₀ u v r B N‖ *
        2 ^ (B + 1) ≤
      2 ^ (K * N) * RG ^ (N + 1) * RE ^ N *
        ∑ s, chainMeasure q x d Y d₀ u v r B' N s * ‖chainInit x d Y d₀ u v r B' s‖ := by
  set C := (2 : ℝ) ^ (K * N) * RG ^ (N + 1) * RE ^ N with hC
  have hC0 : 0 ≤ C := by positivity
  -- the majorant of the histories from one state
  have hrow : ∀ s : ChainState x d Y d₀ u v r B',
      ∑ h ∈ histories x d Y d₀ u v r B' N,
        (∏ j : Fin (N + 1), ‖dblGhostCoef q x d Y d₀ u v r B' N j (chainVisit s h j) (h.1 j)‖) *
          (∏ j : Fin N, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B' N
            (chainGhostOut x d Y d₀ u v r B' (chainVisit s h j.castSucc) (h.1 j.castSucc))
              (h.2 j)‖) * 1 ≤
        RG ^ (N + 1) * RE ^ N * v₀ ^ memSize s.2.2.1 := by
    intro s
    have := sum_history_le_of_rows (h := fun t => v₀ ^ memSize t.2.2.1) (f := fun _ => 1)
      (fun t => one_le_pow₀ hv₀) N
      (fun j t c => ‖dblGhostCoef q x d Y d₀ u v r B' N j t c‖)
      (fun _ t e => ‖chainEdgeCoef q A₀ x d Y d₀ u v r B' N t e‖) (fun _ => RG) (fun _ => RE)
      (fun _ _ _ => norm_nonneg _) (fun _ _ _ => norm_nonneg _) (fun _ => hRG) (fun _ => hRE)
      (fun j t => hG j t) (fun _ t => hE t) s
    simpa only [prod_const, card_univ, Fintype.card_fin] using this
  -- one state
  have hpt : ∀ s : ChainState x d Y d₀ u v r B',
      ‖(chainMeasure q x d Y d₀ u v r B' N s : ℂ) * chainInit x d Y d₀ u v r B' s *
          ∑ h ∈ ((histories x d Y d₀ u v r B' N).filter
              (fun h => BirthsDistinct (births s h))).filter (fun h => ¬ StaysBelow B s h),
            chainWeight q A₀ s h * chainInit x d Y d₀ u v r B' (chainEnd s h)‖ * 2 ^ (B + 1) ≤
        C * (chainMeasure q x d Y d₀ u v r B' N s * ‖chainInit x d Y d₀ u v r B' s‖) := by
    intro s
    by_cases h0 : chainInit x d Y d₀ u v r B' s = 0
    · simp [h0]
    have hs : memSize s.2.2.1 = 0 := by
      by_contra hs
      exact h0 (by rw [chainInit]; exact ite_eq_right fun h => hs h.2)
    set H := ((histories x d Y d₀ u v r B' N).filter
      (fun h => BirthsDistinct (births s h))).filter (fun h => ¬ StaysBelow B s h) with hH
    set P : History x d Y d₀ u v r N → ℝ := fun h =>
      (∏ j : Fin (N + 1), ‖dblGhostCoef q x d Y d₀ u v r B' N j (chainVisit s h j) (h.1 j)‖) *
        ∏ j : Fin N, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B' N
          (chainGhostOut x d Y d₀ u v r B' (chainVisit s h j.castSucc) (h.1 j.castSucc))
            (h.2 j)‖ with hP
    have hP0 : ∀ h, 0 ≤ P h := fun h =>
      mul_nonneg (prod_nonneg fun _ _ => norm_nonneg _) (prod_nonneg fun _ _ => norm_nonneg _)
    -- each history leaving the low memories gains `2^{-(B + 1 - KN)}`
    have hh : ∀ h ∈ H, ‖chainWeight q A₀ s h * chainInit x d Y d₀ u v r B' (chainEnd s h)‖ *
        2 ^ (B + 1) ≤ 2 ^ (K * N) * P h := by
      intro h hh
      have hlt := lt_of_not_staysBelow hs (mem_filter.1 hh).2
      have hb : ‖chainInit x d Y d₀ u v r B' (chainEnd s h)‖ ≤ 1 := by
        unfold chainInit
        split_ifs <;> simp
      have h2 : (2 : ℝ) ^ (B + 1) ≤ 2 ^ (K * N) * 2 ^ ghostBirths x d Y d₀ u v r h := by
        rw [← pow_add]
        exact pow_le_pow_right₀ one_le_two (by omega)
      calc ‖chainWeight q A₀ s h * chainInit x d Y d₀ u v r B' (chainEnd s h)‖ * 2 ^ (B + 1)
          ≤ ‖chainWeight q A₀ s h‖ * 1 * (2 ^ (K * N) * 2 ^ ghostBirths x d Y d₀ u v r h) := by
            rw [norm_mul]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) h2 (by positivity)
              (by positivity)
        _ = 2 ^ (K * N) * P h := by
            rw [mul_one, mul_left_comm, norm_chainWeight_mul_two_pow]
    have hX : ‖∑ h ∈ H, chainWeight q A₀ s h * chainInit x d Y d₀ u v r B' (chainEnd s h)‖ *
        2 ^ (B + 1) ≤ C :=
      calc ‖∑ h ∈ H, chainWeight q A₀ s h * chainInit x d Y d₀ u v r B' (chainEnd s h)‖ *
            2 ^ (B + 1)
          ≤ (∑ h ∈ H, ‖chainWeight q A₀ s h * chainInit x d Y d₀ u v r B' (chainEnd s h)‖) *
              2 ^ (B + 1) :=
            mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
        _ ≤ ∑ h ∈ H, 2 ^ (K * N) * P h := by
            rw [sum_mul]
            exact sum_le_sum hh
        _ ≤ ∑ h ∈ histories x d Y d₀ u v r B' N, 2 ^ (K * N) * P h :=
            sum_le_sum_of_subset_of_nonneg
              ((filter_subset _ _).trans (filter_subset _ _))
              fun h _ _ => mul_nonneg (by positivity) (hP0 h)
        _ = 2 ^ (K * N) * ∑ h ∈ histories x d Y d₀ u v r B' N, P h * 1 := by
            rw [mul_sum]
            simp only [mul_one]
        _ ≤ 2 ^ (K * N) * (RG ^ (N + 1) * RE ^ N * v₀ ^ memSize s.2.2.1) :=
            mul_le_mul_of_nonneg_left (hrow s) (by positivity)
        _ = C := by rw [hs, pow_zero, mul_one, hC]; ring
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ s)]
    calc chainMeasure q x d Y d₀ u v r B' N s * ‖chainInit x d Y d₀ u v r B' s‖ *
          ‖∑ h ∈ H, chainWeight q A₀ s h * chainInit x d Y d₀ u v r B' (chainEnd s h)‖ *
          2 ^ (B + 1)
        = chainMeasure q x d Y d₀ u v r B' N s * ‖chainInit x d Y d₀ u v r B' s‖ *
            (‖∑ h ∈ H, chainWeight q A₀ s h * chainInit x d Y d₀ u v r B' (chainEnd s h)‖ *
              2 ^ (B + 1)) := by ring
      _ ≤ chainMeasure q x d Y d₀ u v r B' N s * ‖chainInit x d Y d₀ u v r B' s‖ * C :=
          mul_le_mul_of_nonneg_left hX (mul_nonneg (hμ s) (norm_nonneg _))
      _ = C * (chainMeasure q x d Y d₀ u v r B' N s * ‖chainInit x d Y d₀ u v r B' s‖) := by
          ring
  rw [distinctSum_sub_eq hB N]
  calc ‖∑ s, (chainMeasure q x d Y d₀ u v r B' N s : ℂ) * chainInit x d Y d₀ u v r B' s *
          ∑ h ∈ ((histories x d Y d₀ u v r B' N).filter
              (fun h => BirthsDistinct (births s h))).filter (fun h => ¬ StaysBelow B s h),
            chainWeight q A₀ s h * chainInit x d Y d₀ u v r B' (chainEnd s h)‖ * 2 ^ (B + 1)
      ≤ (∑ s, ‖(chainMeasure q x d Y d₀ u v r B' N s : ℂ) * chainInit x d Y d₀ u v r B' s *
          ∑ h ∈ ((histories x d Y d₀ u v r B' N).filter
              (fun h => BirthsDistinct (births s h))).filter (fun h => ¬ StaysBelow B s h),
            chainWeight q A₀ s h * chainInit x d Y d₀ u v r B' (chainEnd s h)‖) * 2 ^ (B + 1) :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ ≤ ∑ s, C * (chainMeasure q x d Y d₀ u v r B' N s * ‖chainInit x d Y d₀ u v r B' s‖) := by
        rw [sum_mul]
        exact sum_le_sum fun s _ => hpt s
    _ = C * ∑ s, chainMeasure q x d Y d₀ u v r B' N s * ‖chainInit x d Y d₀ u v r B' s‖ :=
        (mul_sum _ _ _).symm

end Majorant

end Erdos408.OneSided
