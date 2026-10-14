import Erdos408.OneSided.Moment.Chain
import Erdos408.OneSided.Bands

/-!
# The ghost bound on the chain states

The ingredients of M4 for the ghost (`exists_phasedGhost_normLe` in `Moment/Phased.lean`,
PD `mem:ghost-norm`).

* `normLe_ghostChoiceOp`: a choice operator on the chain states with the ghost output and
  coefficients bounded by the ghost coefficients has norm at most `√(R C)`, where `R` and `C`
  bound the row and column factors `exp(v₀ ∑_{hits} |cre| ν)` and `exp(v₀ |del| ∑_{hits} ν)` of
  `ghostOp_normLe` at every position. The ghost acts fiberwise in the position and the lists,
  and the factor `∏ ν(act)` of the chain measure is common to both sides.
* `eventually_harmonicMass_band` (`Bands.lean`), `eventually_two_mul_add_one_le` and
  `half_le_baseline`: eventually every band has harmonic mass in `[1/2, 1]`, and every band
  prime is at least `2N + 1`, so has baseline `b'_p ≥ 1/2`, for `N = 2R`.
* `sum_hits_le_sum_bandPrimes` and `sum_one_div_bandPrimes_le`: the hitting particles have at
  most one line per band prime, and `∑_{p band prime} 1/p ≤ ∑_i V_i ≤ K`.
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

section Ghost

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B : ℕ}

/-- **The fiberwise ghost bound**: a choice operator with the ghost output, whose coefficients
are bounded by the ghost coefficients, has norm at most `√(R C)` for the chain measure, once
`v₀` makes both bases of `ghostOp_normLe` at most one and `R`, `C` bound its row and column
factors at every position. -/
theorem normLe_ghostChoiceOp {N j : ℕ} {a : ChainState x d Y d₀ u v r B → GhostChoice x d → ℂ}
    (ha : ∀ s c, ‖a s c‖ ≤ ‖chainGhostCoef q x d Y d₀ u v r B N j s c‖)
    (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hsurv : 0 ≤ (1 - dampDefect q N j) / pendingWeight q ^ 2) {v₀ R C : ℝ} (hv₀ : 0 < v₀)
    (hdel : (1 - dampDefect q N j) / pendingWeight q ^ 2 +
      |-dampDefect q N j / pendingWeight q| / v₀ ≤ 1)
    (hcre : ∀ xp : Particle x d, (1 - dampDefect q N j) / pendingWeight q ^ 2 +
      |-dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q| / v₀ ≤ 1)
    (hR : ∀ z : ℤ × ℤ, Real.exp (v₀ * ∑ xp with HitsAt x d z xp,
      |-dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q| *
        primeWeight q x d N xp.1.1) ≤ R)
    (hC : ∀ z : ℤ × ℤ, Real.exp (v₀ * |-dampDefect q N j / pendingWeight q| *
      ∑ xp with HitsAt x d z xp, primeWeight q x d N xp.1.1) ≤ C) :
    NormLe (fun s => chainMeasure q x d Y d₀ u v r B N s)
      (fun s => chainMeasure q x d Y d₀ u v r B N s)
      (choiceOp (multBox B ×ˢ multBox B) a (chainGhostOut x d Y d₀ u v r B))
      (Real.sqrt (R * C)) := by
  classical
  have hν' : ∀ xp : Particle x d, 0 ≤ primeWeight q x d N xp.1.1 := fun xp => hν _
  refine normLe_choiceOp (h := fun s => v₀ ^ memSize s.2.2.1)
    (h' := fun s => v₀ ^ memSize s.2.2.1) ((Real.exp_pos _).le.trans (hR 0))
    ((Real.exp_pos _).le.trans (hC 0))
    (fun s => mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg hν' _))
    (fun s => pow_pos hv₀ _) (fun s => ?_) (fun T => ?_)
  · -- the row sum is the row sum of the ghost at the position of `s`
    calc ∑ c ∈ multBox B ×ˢ multBox B,
          ‖a s c‖ * v₀ ^ memSize (chainGhostOut x d Y d₀ u v r B s c).2.2.1
        ≤ ∑ c ∈ multBox B ×ˢ multBox B,
          ‖chainGhostCoef q x d Y d₀ u v r B N j s c‖ *
            v₀ ^ memSize (chainGhostOut x d Y d₀ u v r B s c).2.2.1 :=
          sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (ha s c) (pow_nonneg hv₀.le _)
      _ ≤ Real.exp (v₀ * ∑ xp with HitsAt x d s.1.1 xp,
            |-dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q| *
              primeWeight q x d N xp.1.1) * v₀ ^ memSize s.2.2.1 :=
          ghost_row hν' hsurv hv₀ hdel s.2.2
      _ ≤ R * v₀ ^ memSize s.2.2.1 := mul_le_mul_of_nonneg_right (hR _) (pow_nonneg hv₀.le _)
  · -- only inputs at the position and lists of `T` reach `T`
    have hpos : ∀ (z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r))
        (y : ↥(lists x d (padCount x)) × MemState (Particle x d) B) (c : GhostChoice x d),
        chainGhostOut x d Y d₀ u v r B (z, y) c = T → z = T.1 :=
      fun z y c h => congrArg Prod.fst h
    have hlist : ∀ (l : ↥(lists x d (padCount x))) (S : MemState (Particle x d) B)
        (c : GhostChoice x d), chainGhostOut x d Y d₀ u v r B (T.1, l, S) c = T → l = T.2.1 :=
      fun l S c h => congrArg (fun t => t.2.1) h
    have hmem : ∀ (S : MemState (Particle x d) B) (c : GhostChoice x d),
        chainGhostOut x d Y d₀ u v r B (T.1, T.2.1, S) c = T ↔
          ghostOut (HitsAt x d T.1.1) B S c = T.2.2 := by
      intro S c
      refine ⟨fun h => congrArg (fun t => t.2.2) h, fun h => ?_⟩
      change (T.1, T.2.1, ghostOut (HitsAt x d T.1.1) B S c) = T
      rw [h]
    set P := ∏ i, ∏ h, primeWeight q x d N (T.2.1.1 i h) with hP
    have hP0 : 0 ≤ P := prod_nonneg fun i _ => prod_nonneg fun h _ => hν _
    calc ∑ s, ∑ c ∈ multBox B ×ˢ multBox B with chainGhostOut x d Y d₀ u v r B s c = T,
          chainMeasure q x d Y d₀ u v r B N s * ‖a s c‖ * v₀ ^ memSize s.2.2.1
        ≤ ∑ s, ∑ c ∈ multBox B ×ˢ multBox B with chainGhostOut x d Y d₀ u v r B s c = T,
          chainMeasure q x d Y d₀ u v r B N s * ‖chainGhostCoef q x d Y d₀ u v r B N j s c‖ *
            v₀ ^ memSize s.2.2.1 := by
          refine sum_le_sum fun s _ => sum_le_sum fun c _ => ?_
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha s c) ?_)
            (pow_nonneg hv₀.le _)
          exact mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
            (memWeight_nonneg hν' _)
      _ = P * ∑ S : MemState (Particle x d) B,
          ∑ c ∈ multBox B ×ˢ multBox B with ghostOut (HitsAt x d T.1.1) B S c = T.2.2,
            memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) S.1 *
              ‖ghostCoef (HitsAt x d T.1.1)
                (fun xp : Particle x d => primeWeight q x d N xp.1.1)
                (-dampDefect q N j / pendingWeight q)
                ((1 - dampDefect q N j) / pendingWeight q ^ 2)
                (fun xp : Particle x d => -dampDefect q N j * primeMass x d xp.1.1 /
                  pendingWeight q) B S c‖ * v₀ ^ memSize S.1 := by
          rw [Fintype.sum_prod_type, sum_eq_single T.1, Fintype.sum_prod_type,
            sum_eq_single T.2.1, mul_sum]
          · refine sum_congr rfl fun S _ => ?_
            rw [filter_congr fun c _ => hmem S c, mul_sum]
            refine sum_congr rfl fun c _ => ?_
            simp only [chainMeasure, chainGhostCoef, hP]
            ring
          · intro l _ hl
            refine sum_eq_zero fun S _ => sum_eq_zero fun c hc => ?_
            exact absurd (hlist l S c (mem_filter.1 hc).2) hl
          · intro h
            exact absurd (mem_univ _) h
          · intro z _ hz
            refine sum_eq_zero fun y _ => sum_eq_zero fun c hc => ?_
            exact absurd (hpos z y c (mem_filter.1 hc).2) hz
          · intro h
            exact absurd (mem_univ _) h
      _ ≤ P * (Real.exp (v₀ * |-dampDefect q N j / pendingWeight q| *
            ∑ xp with HitsAt x d T.1.1 xp, primeWeight q x d N xp.1.1) *
          (memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) T.2.2.1 *
            v₀ ^ memSize T.2.2.1)) :=
          mul_le_mul_of_nonneg_left (ghost_col hν' hsurv hv₀ hcre T.2.2) hP0
      _ ≤ P * (C * (memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) T.2.2.1 *
            v₀ ^ memSize T.2.2.1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hC _)
            (mul_nonneg (memWeight_nonneg hν' _) (pow_nonneg hv₀.le _))) hP0
      _ = C * (chainMeasure q x d Y d₀ u v r B N T * v₀ ^ memSize T.2.2.1) := by
          simp only [chainMeasure, hP]
          ring

/-! ### The band facts -/

/-- The damping defects are in `[0, 1]`. -/
private theorem dampDefect_mem_Icc {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) (N j : ℕ) :
    0 ≤ dampDefect q N j ∧ dampDefect q N j ≤ 1 := by
  have hs : Real.sqrt q ≤ 1 := Real.sqrt_le_one.2 hq₁.le
  unfold dampDefect
  split_ifs <;> constructor <;> linarith [Real.sqrt_nonneg q]

/-- For primes `p ≥ 2N + 1`, the baseline is `b'_p ≥ 1/2`: each of the `N + 1` defects is at
most `1`, and `p + 1 ≥ 2(N + 1)`. -/
private theorem half_le_baseline {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) {N p : ℕ}
    (hp : 2 * N + 1 ≤ p) : 1 / 2 ≤ baseline q N p := by
  have hp1 : (0 : ℝ) < p + 1 := by positivity
  have hNp : 2 * ((N : ℝ) + 1) ≤ p + 1 := by exact_mod_cast (show 2 * (N + 1) ≤ p + 1 by omega)
  -- `∑_{j ≤ N} η'_j ≤ N + 1`
  have hsum : ∑ j ∈ range (N + 1), dampDefect q N j ≤ (N : ℝ) + 1 :=
    calc ∑ j ∈ range (N + 1), dampDefect q N j ≤ ∑ _j ∈ range (N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => (dampDefect_mem_Icc hq hq₁ N j).2
      _ = (N : ℝ) + 1 := by simp
  have h₁ : ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), dampDefect q N j ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ hp1]
    linarith
  unfold baseline
  linarith

/-- Eventually every band prime is at least `2N + 1` for `N = 2R`: band primes exceed `L`, and
`2N + 1 ≤ 2 L^{1/2} + 5 ≤ L`. -/
private theorem eventually_two_mul_add_one_le {C CX alo ahi g : ℝ} (halo : 1 / 10 < alo) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ p ∈ bandPrimes x d, 2 * (2 * momentPower x) + 1 ≤ p := by
  have hL := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp Real.tendsto_log_atTop
  filter_upwards [eventually_rpow_lt_of_mem_band (by linarith : 0 < alo) 1,
    hL.eventually_ge_atTop 8, Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with x hbig hs8 hL0 d hd p hp
  obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
  have hLp := hbig (d.a i) (hd.window i).1 p hpi
  rw [Real.rpow_one] at hLp
  set s := Real.log x ^ (1 / 2 : ℝ) with hs
  have hs8' : 8 ≤ s := hs8
  -- `s² = L` and `R < s/2 + 1`
  have hss : s * s = Real.log x := by
    rw [hs, ← Real.rpow_add hL0]
    norm_num
  have hR : (momentPower x : ℝ) < s / 2 + 1 := by
    unfold momentPower
    exact Nat.ceil_lt_add_one (by linarith)
  have h8 : 8 * s ≤ s * s := mul_le_mul_of_nonneg_right hs8' (by linarith)
  have : ((2 * (2 * momentPower x) + 1 : ℕ) : ℝ) < p := by
    push_cast
    linarith
  exact_mod_cast this.le

/-- The harmonic mass is nonnegative. -/
private theorem harmonicMass_nonneg (S : Finset ℕ) : 0 ≤ harmonicMass S :=
  sum_nonneg fun p _ => by positivity

/-- A particle's prime is a band prime. -/
private theorem fst_mem_bandPrimes (xp : Particle x d) : xp.1.1 ∈ bandPrimes x d := by
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.1 xp.2
  obtain ⟨ℓ, -, hℓ⟩ := mem_image.1 hxp
  rw [← hℓ]
  exact hp

/-- The harmonic mass `V(p)` of the bands containing `p` is nonnegative. -/
private theorem primeMass_nonneg (p : ℕ) : 0 ≤ primeMass x d p :=
  sum_nonneg fun i _ => by
    split_ifs
    · exact harmonicMass_nonneg _
    · exact le_rfl

/-- With band masses at least `1/2`, a band prime has `V(p) ≥ 1/2`. -/
private theorem half_le_primeMass (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i))) {p : ℕ}
    (hp : p ∈ bandPrimes x d) : 1 / 2 ≤ primeMass x d p := by
  obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
  calc 1 / 2 ≤ harmonicMass (band x (d.a i)) := hV i
    _ = if p ∈ band x (d.a i) then harmonicMass (band x (d.a i)) else 0 := (ite_eq_left hpi).symm
    _ ≤ primeMass x d p :=
        single_le_sum (f := fun i => if p ∈ band x (d.a i) then harmonicMass (band x (d.a i))
          else 0) (fun j _ => by split_ifs; exact harmonicMass_nonneg _; exact le_rfl)
          (mem_univ i)

/-- With band masses at most `1`, `V(p) ≤ K`. -/
private theorem primeMass_le (hV : ∀ i, harmonicMass (band x (d.a i)) ≤ 1) (p : ℕ) :
    primeMass x d p ≤ K :=
  calc primeMass x d p ≤ ∑ _i : Fin K, (1 : ℝ) :=
        sum_le_sum fun i _ => by
          split_ifs
          · exact hV i
          · norm_num
    _ = K := by simp

/-- With baselines at least `1/2` at the band primes, the birth weights are nonnegative. -/
private theorem primeWeight_nonneg {N : ℕ} (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p)
    (p : ℕ) : 0 ≤ primeWeight q x d N p := by
  unfold primeWeight
  by_cases hp : p ∈ bandPrimes x d
  · have := hb p hp
    exact one_div_nonneg.2 (mul_nonneg (mul_nonneg (primeMass_nonneg p) (by positivity))
      (by linarith))
  · have h0 : primeMass x d p = 0 :=
      sum_eq_zero fun i _ => ite_eq_right fun hpi => hp (mem_biUnion.2 ⟨i, mem_univ i, hpi⟩)
    rw [h0]
    simp

/-- At a band prime, `ν(p) ≤ 4/p` and `V(p) ν(p) ≤ 2/p`. -/
private theorem primeWeight_le {N : ℕ} (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) {p : ℕ} (hp : p ∈ bandPrimes x d) :
    primeWeight q x d N p ≤ 4 * (1 / p) ∧
      primeMass x d p * primeWeight q x d N p ≤ 2 * (1 / p) := by
  have hV₁ := half_le_primeMass hV hp
  have hb₁ := hb p hp
  have hp0 : (0 : ℝ) < p := by
    obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
    exact_mod_cast (TypeII.band_prime hpi).pos
  unfold primeWeight
  constructor
  · calc 1 / (primeMass x d p * ((p : ℝ) + 1) * baseline q N p)
        ≤ 1 / (1 / 2 * p * (1 / 2)) :=
          one_div_le_one_div_of_le (by positivity)
            (mul_le_mul (mul_le_mul hV₁ (by linarith) hp0.le (by linarith)) hb₁ (by norm_num)
              (mul_nonneg (by linarith) (by linarith)))
      _ = 4 * (1 / p) := by field_simp; norm_num
  · have hV0 : primeMass x d p ≠ 0 := by linarith
    have hb0 : baseline q N p ≠ 0 := by linarith
    calc primeMass x d p * (1 / (primeMass x d p * ((p : ℝ) + 1) * baseline q N p))
        = 1 / (((p : ℝ) + 1) * baseline q N p) := by field_simp
      _ ≤ 1 / (p * (1 / 2)) :=
          one_div_le_one_div_of_le (by positivity)
            (mul_le_mul (by linarith) hb₁ (by norm_num) (by linarith))
      _ = 2 * (1 / p) := by field_simp

/-- The hitting particles have one line per band prime, so a sum over them of a nonnegative
function of the prime is at most the sum over the band primes. -/
private theorem sum_hits_le_sum_bandPrimes (z : ℤ × ℤ) {f : ℕ → ℝ} (hf : ∀ p, 0 ≤ f p) :
    ∑ xp with HitsAt x d z xp, f xp.1.1 ≤ ∑ p ∈ bandPrimes x d, f p := by
  rw [← sum_image (f := f) (g := fun xp : Particle x d => xp.1.1)]
  · exact sum_le_sum_of_subset_of_nonneg
      (image_subset_iff.2 fun xp _ => fst_mem_bandPrimes xp) fun p _ _ => hf p
  · intro xp hxp yp hyp h
    have hxp' : lineOf xp.1.1 z = xp.1.2 := (mem_filter.1 (mem_coe.1 hxp)).2
    have hyp' : lineOf yp.1.1 z = yp.1.2 := (mem_filter.1 (mem_coe.1 hyp)).2
    refine Subtype.ext (Prod.ext h ?_)
    rw [← hxp', ← hyp']
    exact congrArg (lineOf · z) h

/-- With band masses at most `1`, `∑_{p band prime} 1/p ≤ ∑_i V_i ≤ K`. -/
private theorem sum_one_div_bandPrimes_le (hV : ∀ i, harmonicMass (band x (d.a i)) ≤ 1) :
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

/-! ### The ghost bound -/

/-- `ρ⁴ = √q`. -/
private theorem pendingWeight_pow_four {q : ℝ} (hq : 0 < q) :
    pendingWeight q ^ 4 = Real.sqrt q := by
  unfold pendingWeight
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, Real.sqrt_eq_rpow]
  norm_num

/-- **The ghost bound on the chain states** (PD `mem:ghost-norm`): there is a `C₀`, depending
only on `q` and `K`, such that eventually every choice operator with the ghost output and
coefficients bounded by those of a ghost `𝒢_j` with `N = 2R` has norm at most `C₀` for the
chain measure. Here `v₀ = (K + 1)/(ρ (1 - ρ²))`, the hitting particles carry
`∑ |cre| ν ≤ 2K/ρ` and `∑ ν ≤ 4K`, and `|del| ≤ 1/ρ`. -/
theorem exists_ghostChoiceOp_normLe {q C CX alo ahi g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ (Y d₀ u v r : ℝ) (B j : ℕ) (a : ChainState x d Y d₀ u v r B → GhostChoice x d → ℂ),
        (∀ s c, ‖a s c‖ ≤ ‖chainGhostCoef q x d Y d₀ u v r B (2 * momentPower x) j s c‖) →
        NormLe (fun s => chainMeasure q x d Y d₀ u v r B (2 * momentPower x) s)
          (fun s => chainMeasure q x d Y d₀ u v r B (2 * momentPower x) s)
          (choiceOp (multBox B ×ˢ multBox B) a (chainGhostOut x d Y d₀ u v r B)) C₀ := by
  set ρ := pendingWeight q with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hq _
  have hρ1 : ρ < 1 := Real.rpow_lt_one hq.le hq₁ (by norm_num)
  have hρ2 : ρ ^ 2 < 1 := pow_lt_one₀ hρ0.le hρ1 (by norm_num)
  set w := 1 - ρ ^ 2 with hw
  have hw0 : 0 < w := by linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  set v₀ := ((K : ℝ) + 1) / (ρ * w) with hv
  have hv₀ : 0 < v₀ := by positivity
  -- `M/ρ/v₀ ≤ w` for `M ≤ K + 1`
  have hdiv : ∀ M : ℝ, 0 ≤ M → M ≤ K + 1 → M / ρ / v₀ ≤ w := by
    intro M hM0 hM
    rw [div_div, show ρ * v₀ = ((K : ℝ) + 1) / w by rw [hv]; field_simp, div_div_eq_mul_div,
      div_le_iff₀ (by positivity)]
    calc M * w ≤ ((K : ℝ) + 1) * w := mul_le_mul_of_nonneg_right hM hw0.le
      _ = w * ((K : ℝ) + 1) := mul_comm _ _
  refine ⟨Real.sqrt (Real.exp (v₀ * (2 * K / ρ)) * Real.exp (v₀ * (1 / ρ) * (4 * K))), ?_⟩
  filter_upwards [eventually_harmonicMass_band halo.le, eventually_two_mul_add_one_le halo]
    with x hV hbig d hd Y d₀ u v r B j a ha
  set N := 2 * momentPower x with hN
  have hV₀ : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) := fun i => (hV _ (hd.window i).1).1
  have hV₁ : ∀ i, harmonicMass (band x (d.a i)) ≤ 1 := fun i => (hV _ (hd.window i).1).2
  have hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p :=
    fun p hp => half_le_baseline hq hq₁ (hbig d hd p hp)
  have hν := primeWeight_nonneg hb
  obtain ⟨hη0, hη1⟩ := dampDefect_mem_Icc hq hq₁ N j
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
      rw [hρ, pendingWeight_pow_four hq]
      unfold dampDefect
      split_ifs <;> linarith
    rw [div_le_iff₀ (by positivity)]
    calc 1 - dampDefect q N j ≤ ρ ^ 4 := hqj
      _ = ρ ^ 2 * ρ ^ 2 := by ring
  -- `|del| ≤ 1/ρ`, and `|cre| ν ≤ (2/ρ)(1/p)`, `|cre| ≤ K/ρ` at the band primes
  have hdel : |-dampDefect q N j / ρ| ≤ 1 / ρ := by
    rw [abs_div, abs_neg, abs_of_nonneg hη0, abs_of_pos hρ0]
    exact div_le_div_of_nonneg_right hη1 hρ0.le
  have hcre : ∀ p, |-dampDefect q N j * primeMass x d p / ρ| =
      dampDefect q N j / ρ * primeMass x d p := by
    intro p
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg hη0, abs_of_nonneg (primeMass_nonneg p),
      abs_of_pos hρ0]
    ring
  have hη : dampDefect q N j / ρ ≤ 1 / ρ := div_le_div_of_nonneg_right hη1 hρ0.le
  have hη' : 0 ≤ dampDefect q N j / ρ := div_nonneg hη0 hρ0.le
  refine normLe_ghostChoiceOp ha hν hsurv0 hv₀ ?_ (fun xp => ?_) (fun z => ?_) (fun z => ?_)
  · calc (1 - dampDefect q N j) / ρ ^ 2 + |-dampDefect q N j / ρ| / v₀
        ≤ ρ ^ 2 + 1 / ρ / v₀ := add_le_add hsurv1 (div_le_div_of_nonneg_right hdel hv₀.le)
      _ ≤ ρ ^ 2 + w := add_le_add le_rfl (hdiv 1 zero_le_one (by linarith))
      _ = 1 := by rw [hw]; ring
  · have hcreK : |-dampDefect q N j * primeMass x d xp.1.1 / ρ| ≤ K / ρ := by
      rw [hcre]
      calc dampDefect q N j / ρ * primeMass x d xp.1.1 ≤ 1 / ρ * K :=
            mul_le_mul hη (primeMass_le hV₁ _) (primeMass_nonneg _) (by positivity)
        _ = K / ρ := by ring
    calc (1 - dampDefect q N j) / ρ ^ 2 + |-dampDefect q N j * primeMass x d xp.1.1 / ρ| / v₀
        ≤ ρ ^ 2 + K / ρ / v₀ := add_le_add hsurv1 (div_le_div_of_nonneg_right hcreK hv₀.le)
      _ ≤ ρ ^ 2 + w := add_le_add le_rfl (hdiv K hK0 (by linarith))
      _ = 1 := by rw [hw]; ring
  · refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hv₀.le)
    calc ∑ xp with HitsAt x d z xp,
          |-dampDefect q N j * primeMass x d xp.1.1 / ρ| * primeWeight q x d N xp.1.1
        ≤ ∑ xp with HitsAt x d z xp, 2 / ρ * (1 / (xp.1.1 : ℝ)) := by
          refine sum_le_sum fun xp _ => ?_
          have h := (primeWeight_le hV₀ hb (fst_mem_bandPrimes xp)).2
          rw [hcre]
          calc dampDefect q N j / ρ * primeMass x d xp.1.1 * primeWeight q x d N xp.1.1
              = dampDefect q N j / ρ * (primeMass x d xp.1.1 * primeWeight q x d N xp.1.1) :=
                mul_assoc _ _ _
            _ ≤ 1 / ρ * (2 * (1 / (xp.1.1 : ℝ))) :=
                mul_le_mul hη h (mul_nonneg (primeMass_nonneg _) (hν _)) (by positivity)
            _ = 2 / ρ * (1 / (xp.1.1 : ℝ)) := by ring
      _ ≤ ∑ p ∈ bandPrimes x d, 2 / ρ * (1 / (p : ℝ)) :=
          sum_hits_le_sum_bandPrimes z (f := fun p => 2 / ρ * (1 / (p : ℝ))) fun p => by positivity
      _ = 2 / ρ * ∑ p ∈ bandPrimes x d, (1 : ℝ) / p := (mul_sum _ _ _).symm
      _ ≤ 2 / ρ * K := mul_le_mul_of_nonneg_left (sum_one_div_bandPrimes_le hV₁) (by positivity)
      _ = 2 * K / ρ := by ring
  · refine Real.exp_le_exp.2 (mul_le_mul (mul_le_mul_of_nonneg_left hdel hv₀.le) ?_
      (sum_nonneg fun xp _ => hν _) (by positivity))
    calc ∑ xp with HitsAt x d z xp, primeWeight q x d N xp.1.1
        ≤ ∑ xp with HitsAt x d z xp, 4 * (1 / (xp.1.1 : ℝ)) :=
          sum_le_sum fun xp _ => (primeWeight_le hV₀ hb (fst_mem_bandPrimes xp)).1
      _ ≤ ∑ p ∈ bandPrimes x d, 4 * (1 / (p : ℝ)) :=
          sum_hits_le_sum_bandPrimes z (f := fun p => 4 * (1 / (p : ℝ))) fun p => by positivity
      _ = 4 * ∑ p ∈ bandPrimes x d, (1 : ℝ) / p := (mul_sum _ _ _).symm
      _ ≤ 4 * K := mul_le_mul_of_nonneg_left (sum_one_div_bandPrimes_le hV₁) (by norm_num)

end Ghost

end Erdos408.OneSided
