import Erdos408.OneSided.Moment.Phased.Edge
import Erdos408.OneSided.Moment.Edge.LineCount

/-!
# The dirty comparison edges

M8 of `blueprint/one_sided_type_ii.md` §16 (PD §4 "Dirty comparison edges",
`mem:comparison-small`). The comparison part of the edge piece with stored groups `S` and
promoted groups `I` has the coefficient `-w ∫_𝔐 e(θ(t - b + a))` (`compCoef`, which unfolds to
`edgeComp` of `Moment/Edge.lean`). For `(S, I) ≠ (∅, ∅)` its norm is at most `L^{-G - 1}`, by
the weighted Schur test with weight `1`:

* `norm_compCoef_le`: the coefficient is at most `M!^{-2K} ∏_i w_i · 4 L^{3A₀}/Y`, and zero
  unless `det = D t` with `|t| ≤ ⌈5Y⌉` (`mem:major-absolute`);
* `norm_compCoef_le_crude`: it is the difference of two edge coefficients, at `A₀` and at an
  arc parameter with no arcs, so both Schur sides are at most `L^{C}` (`mem:edge-crude`);
* `sum_norm_compCoef_le_of_mem`: for a promoted group, the row sum is at most
  `2^K (2B + 4)^K Λ` with `Λ = 4 L^{3A₀}/Y · 2^13 (Y/P + Y^{0.8})`, where `P` bounds the primes
  of that group from below. The promoted particle `(p, ℓ)` prescribes the line of the target,
  and the line count (`card_filter_line_le`) applies, since `p ∤ D` by the cross-edge ban;
* `sum_col_compCoef_le_of_mem`: for a stored group, the column sum is at most
  `3^K (B + 4)^K B Λ μ(s')`, by the same count at the source;
* `eventually_compOp_normLe`: eventually, for `B ≤ L³`, both products of a small and a crude
  side are at most `L^{-2G - 2}`. If `4Y ≤ L^E` the piece vanishes, since a label product
  exceeds every band prime.
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-! ### The comparison coefficient -/

section Coef

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

/-- The edge choices with stored groups `S` and promoted groups `I` (`edgePartChoices`). -/
def compChoices (S I : Finset (Fin K)) : Finset (EdgeChoice x d Y d₀ u v r) :=
  (edgeChoices x d Y d₀ u v r).filter fun c =>
    c.2.1 = S ∧ univ.filter (fun i => (c.2.2.2.1 i).2 = true) = I

open scoped Classical in
/-- The comparison coefficient `-w ∫_𝔐 e(θ(t - b + a))`: the coefficient of `edgeComp`, with
the amplitude `edgeAmp` and the shift `edgeShift` unfolded. -/
def compCoef (N : ℕ) (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℂ :=
  -(((if EdgeValid x d Y d₀ u v r B s c then
    ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
      pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
      pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
      (∏ i, if (c.2.2.2.1 i).2 then
        (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0) /
          primeMass x d (c.2.2.2.1 i).1
      else primeWeight q x d N (c.2.2.2.1 i).1) *
      (d₀ / edgePad s c) * dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y) *
      dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y) * plateau ((edgeDet s c / edgePad s c : ℤ) / Y))
  else 0 : ℝ) : ℂ) *
    arcIntegral A₀ x Y
      (edgeDet s c / edgePad s c - (∏ i, edgeSrc s c i (Fin.last _) : ℕ) +
        (∏ i, (c.2.2.2.1 i).1 : ℕ)))

/-- The comparison part of the edge piece `(S, I)`. -/
def compOp (N : ℕ) (S I : Finset (Fin K)) :
    (ChainState x d Y d₀ u v r B → ℂ) → ChainState x d Y d₀ u v r B → ℂ :=
  choiceOp (compChoices x d Y d₀ u v r S I) (compCoef q A₀ x d Y d₀ u v r B N)
    (chainEdgeOut x d Y d₀ u v r B)

end Coef

section Bounds

variable {q A₀ x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- The coefficient vanishes off the admissible choices. -/
theorem compCoef_eq_zero {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hv : ¬ EdgeValid x d Y d₀ u v r B s c) : compCoef q A₀ x d Y d₀ u v r B N s c = 0 := by
  classical
  unfold compCoef
  rw [ite_eq_right fun h => absurd h hv]
  simp

/-- `η(y) ≠ 0` only for `y < 4`. -/
theorem lt_four_of_dyadicBump_ne_zero {y : ℝ} (h : dyadicBump y ≠ 0) : y < 4 := by
  by_contra hy
  push Not at hy
  apply h
  unfold dyadicBump
  rw [smoothTransition.one_of_one_le (by linarith), smoothTransition.one_of_one_le (by linarith),
    sub_self]

/-- `|η| ≤ 1`. -/
private theorem abs_dyadicBump_le' (y : ℝ) : |dyadicBump y| ≤ 1 := by
  unfold dyadicBump
  have h₁ := smoothTransition.nonneg (y - 1)
  have h₂ := smoothTransition.le_one (y - 1)
  have h₃ := smoothTransition.nonneg (y / 2 - 1)
  have h₄ := smoothTransition.le_one (y / 2 - 1)
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- A product of a number at most one and a number in `[0, 1]` is at most one. -/
private theorem mul_le_one_of_le' {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) :
    a * b ≤ 1 :=
  (mul_le_mul_of_nonneg_right ha hb0).trans (by rw [one_mul]; exact hb)

/-- A nonzero admissible coefficient has label product `a < 4Y`. -/
theorem labelProd_lt_of_compCoef_ne_zero {s : ChainState x d Y d₀ u v r B}
    {c : EdgeChoice x d Y d₀ u v r} (hY : 0 < Y)
    (h : compCoef q A₀ x d Y d₀ u v r B N s c ≠ 0) :
    ((∏ i, (c.2.2.2.1 i).1 : ℕ) : ℝ) < 4 * Y := by
  classical
  by_cases hv : EdgeValid x d Y d₀ u v r B s c
  · have hη : dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y) ≠ 0 := by
      intro h0
      apply h
      unfold compCoef
      rw [ite_eq_left hv, h0]
      simp
    have := lt_four_of_dyadicBump_ne_zero hη
    rwa [div_lt_iff₀ hY] at this
  · exact absurd (compCoef_eq_zero hv) h

/-- With `L^{A} < 1` there are no arcs: `∫_𝔐 = 0`. -/
theorem arcIntegral_eq_zero_of_lt_one {A x Y : ℝ} (h : Real.log x ^ A < 1) (n : ℤ) :
    arcIntegral A x Y n = 0 := by
  unfold arcIntegral
  rw [Nat.floor_eq_zero.2 h]
  simp

/-- **The comparison coefficient is a difference of edge coefficients**: at an arc parameter
`A₁` with no arcs, `-w ∫_𝔐 = ℰ_{A₀} - ℰ_{A₁}`, since `ℰ_A = w ([t - b + a = 0] - ∫_{𝔐_A})`. -/
theorem compCoef_eq_sub {A₁ : ℝ} (h0 : ∀ n, arcIntegral A₁ x Y n = 0)
    (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    compCoef q A₀ x d Y d₀ u v r B N s c =
      chainEdgeCoef q A₀ x d Y d₀ u v r B N s c - chainEdgeCoef q A₁ x d Y d₀ u v r B N s c := by
  classical
  unfold compCoef chainEdgeCoef
  by_cases hv : EdgeValid x d Y d₀ u v r B s c
  · simp only [hv, ↓reduceIte, h0]
    ring
  · simp [hv]

/-- **The crude coefficient bound**: `|-w ∫_𝔐| ≤ |ℰ_{A₀}| + |ℰ_{A₁}|` for an arc parameter
`A₁` with no arcs. -/
theorem norm_compCoef_le_crude {A₁ : ℝ} (h0 : ∀ n, arcIntegral A₁ x Y n = 0)
    (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ ≤
      ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ +
        ‖chainEdgeCoef q A₁ x d Y d₀ u v r B N s c‖ := by
  rw [compCoef_eq_sub h0]
  exact norm_sub_le _ _

open scoped Classical in
/-- **The coefficient bound** (`mem:major-absolute`): an admissible comparison coefficient is at
most `M!^{-2K} ∏_i w_i · 4 L^{3A₀}/Y`, and it vanishes unless `det = D t` with `|t| ≤ ⌈5Y⌉`. -/
theorem norm_compCoef_le (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀) (hY : 0 < Y)
    (hL : 0 < Real.log x) (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hv : EdgeValid x d Y d₀ u v r B s c) :
    ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ ≤
      (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 * crudeWeight q x d Y d₀ u v r B N s c *
        ((if ∃ t ∈ Icc (-(⌈5 * Y⌉₊ : ℤ)) ⌈5 * Y⌉₊, edgeDet s c = edgePad s c * t then 1 else 0) *
          (4 * Real.log x ^ (3 * A₀) / Y)) := by
  classical
  have hW := crudeWeight_nonneg hν s c
  have hρ0 : 0 ≤ pendingWeight q := (Real.rpow_pos_of_pos hq _).le
  have hρ1 : pendingWeight q ≤ 1 := Real.rpow_le_one hq.le hq₁.le (by norm_num)
  have hv' := hv
  obtain ⟨-, -, hD₀, -, hdvd, -⟩ := hv
  have hD : 0 < (edgePad s c : ℝ) := hd₀.trans_le hD₀
  set r₀ := (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hr₀
  set ψ := plateau ((edgeDet s c / edgePad s c : ℤ) / Y) with hψ
  set Ω := 4 * Real.log x ^ (3 * A₀) / Y with hΩ
  have hr0 : 0 ≤ r₀ := by positivity
  have hΩ0 : 0 ≤ Ω := by positivity
  have hψ0 : 0 ≤ ψ := smoothTransition.nonneg _
  have hψ1 : ψ ≤ 1 := smoothTransition.le_one _
  -- `ψ ≤ [det = D t, |t| ≤ ⌈5Y⌉]`
  have hψI : ψ ≤ if ∃ t ∈ Icc (-(⌈5 * Y⌉₊ : ℤ)) ⌈5 * Y⌉₊, edgeDet s c = edgePad s c * t
      then 1 else 0 := by
    split_ifs with ht
    · exact hψ1
    · by_contra hlt
      push Not at hlt
      apply ht
      refine ⟨edgeDet s c / edgePad s c, ?_, (Int.mul_ediv_cancel' hdvd).symm⟩
      have h5 := abs_lt_of_plateau_ne_zero (ne_of_gt hlt)
      rw [abs_div, abs_of_pos hY, div_lt_iff₀ hY] at h5
      have hle : |((edgeDet s c / edgePad s c : ℤ) : ℝ)| ≤ ⌈5 * Y⌉₊ := h5.le.trans (Nat.le_ceil _)
      rw [abs_le] at hle
      exact mem_Icc.2 ⟨by exact_mod_cast hle.1, by exact_mod_cast hle.2⟩
  -- `|w| ≤ r₀ W ψ`
  have hamp : |r₀ * pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
      pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
      crudeWeight q x d Y d₀ u v r B N s c * (d₀ / edgePad s c) *
      dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y) *
      dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y) * ψ| ≤
        r₀ * crudeWeight q x d Y d₀ u v r B N s c * ψ := by
    have hdD0 : 0 ≤ d₀ / (edgePad s c : ℝ) := div_nonneg hd₀.le hD.le
    have hdD1 : d₀ / (edgePad s c : ℝ) ≤ 1 := (div_le_one hD).2 hD₀
    simp only [abs_mul, abs_of_nonneg hr0, abs_of_nonneg hW, abs_of_nonneg hψ0,
      abs_of_nonneg hdD0, abs_of_nonneg (pow_nonneg hρ0 _)]
    have hη₁ := abs_dyadicBump_le' ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y)
    have hη₂ := abs_dyadicBump_le' ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y)
    have hp₁ := pow_le_one₀ (n := pendingHits x d s.1.1 s.2.2.1) hρ0 hρ1
    have hp₂ := pow_le_one₀ (n := pendingHits x d c.2.2.1.1 (edgeMem s c)) hρ0 hρ1
    have hfac : pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
        pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) * (d₀ / (edgePad s c : ℝ)) *
          |dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y)| *
            |dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y)| ≤ 1 := by
      exact mul_le_one_of_le' (mul_le_one_of_le' (mul_le_one_of_le' (mul_le_one_of_le' hp₁
        (pow_nonneg hρ0 _) hp₂) hdD0 hdD1) (abs_nonneg _) hη₁) (abs_nonneg _) hη₂
    calc _ = r₀ * crudeWeight q x d Y d₀ u v r B N s c * ψ *
          (pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
            pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) * (d₀ / (edgePad s c : ℝ)) *
              |dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y)| *
                |dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y)|) := by ring
      _ ≤ r₀ * crudeWeight q x d Y d₀ u v r B N s c * ψ * 1 :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = _ := mul_one _
  have harc := norm_arcIntegral_le A₀ hL hY
    (edgeDet s c / edgePad s c - (∏ i, edgeSrc s c i (Fin.last _) : ℕ) +
      (∏ i, (c.2.2.2.1 i).1 : ℕ))
  unfold compCoef
  rw [ite_eq_left hv', norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine (mul_le_mul hamp harc (norm_nonneg _) (by positivity)).trans ?_
  calc r₀ * crudeWeight q x d Y d₀ u v r B N s c * ψ * Ω
      = r₀ * crudeWeight q x d Y d₀ u v r B N s c * (ψ * Ω) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hψI hΩ0) (mul_nonneg hr0 hW)

/-- The coefficient bound without the support condition: `|-w ∫_𝔐| ≤ M!^{-2K} ∏_i w_i ·
4 L^{3A₀}/Y` at an admissible choice. -/
theorem norm_compCoef_le' (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀) (hY : 0 < Y)
    (hL : 0 < Real.log x) (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hv : EdgeValid x d Y d₀ u v r B s c) :
    ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ ≤
      (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 * crudeWeight q x d Y d₀ u v r B N s c *
        (4 * Real.log x ^ (3 * A₀) / Y) := by
  classical
  refine (norm_compCoef_le hq hq₁ hd₀ hY hL hν hv).trans (mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (by positivity) (crudeWeight_nonneg hν s c)))
  have hΩ : 0 ≤ 4 * Real.log x ^ (3 * A₀) / Y := by positivity
  calc _ ≤ 1 * (4 * Real.log x ^ (3 * A₀) / Y) :=
        mul_le_mul_of_nonneg_right (by split_ifs <;> norm_num) hΩ
    _ = _ := one_mul _

/-- The support of the comparison coefficient: it vanishes unless `det = D t` with
`|t| ≤ ⌈5Y⌉`. -/
theorem exists_det_of_compCoef_ne_zero (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀) (hY : 0 < Y)
    (hL : 0 < Real.log x) (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h : compCoef q A₀ x d Y d₀ u v r B N s c ≠ 0) :
    ∃ t ∈ Icc (-(⌈5 * Y⌉₊ : ℤ)) ⌈5 * Y⌉₊, edgeDet s c = edgePad s c * t := by
  classical
  by_contra ht
  have hv : EdgeValid x d Y d₀ u v r B s c := by
    by_contra hv
    exact h (compCoef_eq_zero hv)
  have := norm_compCoef_le (A₀ := A₀) hq hq₁ hd₀ hY hL hν hv
  rw [ite_eq_right ht, zero_mul, mul_zero] at this
  exact h (norm_le_zero_iff.1 this)

/-! ### Lists and products -/

/-- A prime different from every factor of a product of primes does not divide it. -/
theorem not_dvd_prod_of_ne {M : ℕ} {p : ℕ} (hp : p.Prime) (f : Fin K → Fin M → ℕ)
    (hf : ∀ i h, (f i h).Prime) (hne : ∀ i h, p ≠ f i h) : ¬ p ∣ ∏ i, ∏ h, f i h :=
  Prime.not_dvd_finsetProd hp.prime fun i _ => Prime.not_dvd_finsetProd hp.prime fun h _ hd =>
    hne i h ((Nat.prime_dvd_prime_iff_eq hp (hf i h)).1 hd)

/-- The omission product at the last slots of a symmetrization is the product over the other
slots. -/
theorem omitProd_last {M : ℕ} (p : Lists K M) (σ : Fin K → Equiv.Perm (Fin (M + 1)))
    (hpos : ∀ i h, 0 < p i h) :
    omitProd p (fun i => σ i (Fin.last M)) = ∏ i, ∏ h : Fin M, p i (σ i h.castSucc) := by
  unfold omitProd
  refine prod_congr rfl fun i _ => ?_
  have h₁ : ∏ h, p i h = (∏ h : Fin M, p i (σ i h.castSucc)) * p i (σ i (Fin.last M)) := by
    rw [← Fin.prod_univ_castSucc (fun h => p i (σ i h))]
    exact (Equiv.prod_comp (σ i) (p i)).symm
  have h₂ : ∏ h, p i h = p i (σ i (Fin.last M)) * ∏ h ∈ univ.erase (σ i (Fin.last M)), p i h :=
    (mul_prod_erase _ _ (mem_univ _)).symm
  rw [h₂, mul_comm] at h₁
  exact mul_right_cancel₀ (hpos i _).ne' h₁

/-! ### The row sums of a promoted group -/

open scoped Classical in
/-- **The small row bound** (PD `mem:comparison-small`): if the group `i₀` is promoted and its
primes are at least `P`, then for every source the absolute comparison coefficients sum to at
most `2^K (2B + 4)^K Λ` with `Λ = 4 L^{3A₀}/Y · 2^13 (Y/P + Y^{0.8})`. The promoted particle
`(p, ℓ)` of `i₀` prescribes `[z']_p = ℓ` with `p ∤ D` (the cross-edge ban), so the targets are
counted by `card_filter_line_le` at the good source; the other groups are bounded as in the
crude row bound. -/
theorem sum_norm_compCoef_le_of_mem (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀) (hY : 1 ≤ Y)
    (hU : 0 < d₀ * Y * d.Hm) (hL : 0 < Real.log x) (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνi : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4)
    (hV : ∀ i, ∀ p ∈ band x (d.a i), 1 / 2 ≤ primeMass x d p)
    {S I : Finset (Fin K)} {i₀ : Fin K} (hi₀ : i₀ ∈ I) {P : ℝ} (hP : 0 < P)
    (hPi : ∀ p ∈ band x (d.a i₀), P ≤ p) (s : ChainState x d Y d₀ u v r B) :
    ∑ c ∈ compChoices x d Y d₀ u v r S I, ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ ≤
      2 ^ K * (2 * B + 4) ^ K *
        (4 * Real.log x ^ (3 * A₀) / Y * (2 ^ 13 * (Y / P + Y ^ (4 / 5 : ℝ)))) := by
  set M := padCount x with hM
  set Ω := 4 * Real.log x ^ (3 * A₀) / Y with hΩ
  set Λ := Ω * (2 ^ 13 * (Y / P + Y ^ (4 / 5 : ℝ))) with hΛ
  have hY0 : 0 < Y := by linarith
  have hΩ0 : 0 ≤ Ω := by positivity
  have hΛ0 : 0 ≤ Λ := by positivity
  have hRHS : 0 ≤ 2 ^ K * (2 * (B : ℝ) + 4) ^ K * Λ := by positivity
  -- a bad source has no admissible choice
  by_cases hg : GoodFirst Y d₀ (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1
  swap
  · refine le_trans (le_of_eq (sum_eq_zero fun c _ => ?_)) hRHS
    rw [compCoef_eq_zero fun hv => hg hv.2.2.2.2.2.1.1, norm_zero]
  set r₀ := (((M + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hr₀
  set T := ⌈5 * Y⌉₊ with hT
  set ω : ℕ × Bool → ℝ := fun pf =>
    if pf.2 then 2 * primeMult x d s.2.2.1 pf.1 else primeWeight q x d N pf.1 with hω
  set Dσ : (Fin K → Equiv.Perm (Fin (M + 1))) → ℕ :=
    fun σ => ∏ i, ∏ h : Fin M, s.2.1.1 i (σ i h.castSucc) with hDσ
  set kern : (Fin K → Equiv.Perm (Fin (M + 1))) →
      ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) → ℝ := fun σ z' =>
    if d₀ ≤ (Dσ σ : ℝ) ∧ (Dσ σ : ℝ) < 2 * d₀ ∧
        ∃ t ∈ Icc (-(T : ℤ)) T, s.1.1.1 * z'.1.2 - s.1.1.2 * z'.1.1 = Dσ σ * t
      then Ω else 0 with hkern
  set Ψ : (Fin K → Equiv.Perm (Fin (M + 1))) →
      ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) → ℕ × Bool → ℝ := fun σ z' pf =>
    if pf.2 ∧ ¬ pf.1 ∣ Dσ σ then
      2 * ∑ xp : Particle x d, if xp.1 = (pf.1, lineOf pf.1 z'.1) then (s.2.2.1 xp : ℝ) else 0
    else 0 with hΨ
  set g : (Fin K → Equiv.Perm (Fin (M + 1))) →
      ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) → Fin K → ℕ × Bool → ℝ :=
    fun σ z' i pf => if i = i₀ then Ψ σ z' pf else ω pf with hg'
  set F : (Fin K → Equiv.Perm (Fin (M + 1))) → ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) →
      (Fin K → ℕ × Bool) → ℝ := fun σ z' lab =>
    r₀ * (∏ i, g σ z' i (lab i)) * kern σ z' with hF
  have hr0 : 0 ≤ r₀ := by positivity
  have hω0 : ∀ pf, 0 ≤ ω pf := fun pf => by
    simp only [hω]
    split_ifs
    exacts [mul_nonneg (by norm_num) (primeMult_nonneg _ _), hν _]
  have hΨ0 : ∀ σ z' pf, 0 ≤ Ψ σ z' pf := fun σ z' pf => by
    simp only [hΨ]
    split_ifs
    · exact mul_nonneg (by norm_num) (sum_nonneg fun xp _ => by split_ifs <;> positivity)
    · exact le_rfl
  have hg0 : ∀ σ z' i pf, 0 ≤ g σ z' i pf := fun σ z' i pf => by
    simp only [hg']
    split_ifs
    exacts [hΨ0 _ _ _, hω0 _]
  have hkern0 : ∀ σ z', 0 ≤ kern σ z' := fun σ z' => by
    simp only [hkern]
    split_ifs
    exacts [hΩ0, le_rfl]
  have hF0 : ∀ σ z' lab, 0 ≤ F σ z' lab := fun σ z' lab =>
    mul_nonneg (mul_nonneg hr0 (prod_nonneg fun i _ => hg0 _ _ _ _)) (hkern0 _ _)
  -- the pointwise bound
  have hpt : ∀ c ∈ compChoices x d Y d₀ u v r S I,
      ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ ≤ F c.1 c.2.2.1 c.2.2.2.1 := by
    intro c hc
    obtain ⟨hc, hcS, hcI⟩ := mem_filter.1 hc
    by_cases hv : EdgeValid x d Y d₀ u v r B s c
    swap
    · rw [compCoef_eq_zero hv, norm_zero]
      exact hF0 _ _ _
    refine (norm_compCoef_le hq hq₁ hd₀ hY0 hL hν hv).trans ?_
    have hprom : (c.2.2.2.1 i₀).2 = true := by
      have := hcI ▸ hi₀
      exact (mem_filter.1 this).2
    have hban : ¬ (c.2.2.2.1 i₀).1 ∣ Dσ c.1 :=
      not_dvd_prod_of_ne (TypeII.band_prime (mem_band_of_mem_edgeChoices hc i₀)) _
        (fun i h => TypeII.band_prime (mem_band_of_mem_lists s.2.1.2 i _))
        (fun i h => hv.2.1 i₀ i _)
    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ hr0) ?_ (by positivity)
      (mul_nonneg hr0 (prod_nonneg fun i _ => hg0 _ _ _ _))
    · -- the weights
      refine prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
      · split_ifs
        · exact div_nonneg (sum_nonneg fun xp _ => by split_ifs <;> positivity)
            (le_trans (by norm_num) (hV i _ (mem_band_of_mem_edgeChoices hc i)))
        · exact hν _
      · have hVi := hV i _ (mem_band_of_mem_edgeChoices hc i)
        have hnum0 : 0 ≤ ∑ xp : Particle x d,
            if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0 :=
          sum_nonneg fun xp _ => by split_ifs <;> positivity
        by_cases hi : i = i₀
        · subst hi
          simp only [hg', hΨ, ↓reduceIte, hprom, hban, not_false_eq_true, and_self]
          rw [div_le_iff₀ (by linarith)]
          have : (∑ xp : Particle x d,
              if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0) =
                ∑ xp : Particle x d, if xp.1 = ((c.2.2.2.1 i).1, lineOf (c.2.2.2.1 i).1 c.2.2.1.1)
                  then (s.2.2.1 xp : ℝ) else 0 := rfl
          rw [← this]
          nlinarith
        · simp only [hg', hi, ↓reduceIte, hω]
          split_ifs with hf
          · have hnum : (∑ xp : Particle x d,
                if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0) ≤
                  primeMult x d s.2.2.1 (c.2.2.2.1 i).1 := by
              refine sum_le_sum fun xp _ => ?_
              split_ifs with h₁ h₂ h₂
              · exact le_rfl
              · exact absurd (congrArg Prod.fst h₁) h₂
              · positivity
              · exact le_rfl
            rw [div_le_iff₀ (by linarith)]
            nlinarith [primeMult_nonneg s.2.2.1 (c.2.2.2.1 i).1]
          · exact le_rfl
    · -- the kernel
      by_cases ht : ∃ t ∈ Icc (-(T : ℤ)) T, edgeDet s c = edgePad s c * t
      · rw [ite_eq_left ht, one_mul]
        have hk : kern c.1 c.2.2.1 = Ω := ite_eq_left ⟨hv.2.2.1, hv.2.2.2.1, ht⟩
        rw [hk]
      · rw [ite_eq_right ht, zero_mul]
        exact hkern0 _ _
  -- the targets on the prescribed line
  have hT6 : (T : ℝ) ≤ 6 * Y := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 5 * Y by linarith)
    rw [← hT] at this
    linarith
  set Φ : ℕ × Bool → ℝ := fun pf =>
    if pf.2 then 2 * primeMult x d s.2.2.1 pf.1 * Λ else 0 with hΦ
  have hΦ0 : ∀ pf, 0 ≤ Φ pf := fun pf => by
    simp only [hΦ]
    split_ifs
    · exact mul_nonneg (mul_nonneg (by norm_num) (primeMult_nonneg _ _)) hΛ0
    · exact le_rfl
  have hkey : ∀ σ, ∀ pf ∈ band x (d.a i₀) ×ˢ (univ : Finset Bool),
      ∑ z', Ψ σ z' pf * kern σ z' ≤ Φ pf := by
    intro σ pf hpf
    have hpb := (mem_product.1 hpf).1
    have hp := TypeII.band_prime hpb
    have hPp := hPi _ hpb
    by_cases hΨc : pf.2 ∧ ¬ pf.1 ∣ Dσ σ
    swap
    · rw [sum_eq_zero fun z' _ => by simp only [hΨ, ite_eq_right hΨc, zero_mul]]
      exact hΦ0 pf
    by_cases hDr : d₀ ≤ (Dσ σ : ℝ) ∧ (Dσ σ : ℝ) < 2 * d₀
    swap
    · rw [sum_eq_zero fun z' _ => by
        simp only [hkern]
        rw [ite_eq_right fun h => hDr ⟨h.1, h.2.1⟩, mul_zero]]
      exact hΦ0 pf
    -- test (i) at the omission product `D_σ`
    have hom := omitProd_last s.2.1.1 σ
      (fun i h => (TypeII.band_prime (mem_band_of_mem_lists s.2.1.2 i h)).pos)
    have hgoodD : ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (1 / 5 : ℝ) →
        Y ^ (-(7 / 10 : ℝ)) <
          circleDist (l * (Dσ σ : ℕ) * (tau r (complement s.1.1) / tau r s.1.1)) := by
      intro l hl hlY
      have := hg (fun i => σ i (Fin.last M)) (by rw [hom]; exact hDr.1) (by rw [hom]; exact hDr.2)
        l hl hlY
      rwa [hom] at this
    -- each particle sees at most `Λ` of kernel mass on its line
    have hinner : ∀ xp : Particle x d,
        ∑ z', (if xp.1 = (pf.1, lineOf pf.1 z'.1) then (1 : ℝ) else 0) * kern σ z' ≤
          if xp.1.1 = pf.1 then Λ else 0 := by
      intro xp
      by_cases hxp : xp.1.1 = pf.1
      · rw [ite_eq_left hxp]
        set cond : ℤ × ℤ → Prop := fun z =>
          (∃ t ∈ Icc (-(T : ℤ)) T, s.1.1.1 * z.2 - s.1.1.2 * z.1 = Dσ σ * t) ∧
            lineOf pf.1 z = xp.1.2 with hcond
        have hterm : ∀ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
            (if xp.1 = (pf.1, lineOf pf.1 z'.1) then (1 : ℝ) else 0) * kern σ z' ≤
              if cond z'.1 then Ω else 0 := by
          intro z'
          by_cases h1 : xp.1 = (pf.1, lineOf pf.1 z'.1)
          · rw [ite_eq_left h1, one_mul]
            by_cases ht : ∃ t ∈ Icc (-(T : ℤ)) T, s.1.1.1 * z'.1.2 - s.1.1.2 * z'.1.1 = Dσ σ * t
            · have hc : cond z'.1 := ⟨ht, (congrArg Prod.snd h1).symm⟩
              rw [ite_eq_left hc]
              simp only [hkern]
              split_ifs
              exacts [le_rfl, hΩ0]
            · have hk : kern σ z' = 0 := ite_eq_right fun h => ht h.2.2
              rw [hk]
              split_ifs
              exacts [hΩ0, le_rfl]
          · rw [ite_eq_right h1, zero_mul]
            split_ifs
            exacts [hΩ0, le_rfl]
        have hcard := card_filter_line_le hU hY s.1.2 hgoodD hp hΨc.2 xp.1.2 hT6
        calc ∑ z', (if xp.1 = (pf.1, lineOf pf.1 z'.1) then (1 : ℝ) else 0) * kern σ z'
            ≤ ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
                if cond z'.1 then Ω else 0 := sum_le_sum fun z' _ => hterm z'
          _ = ∑ z ∈ rootPositions (d₀ * Y * d.Hm) d.Hn u v r, if cond z then Ω else 0 :=
              sum_coe_sort (rootPositions (d₀ * Y * d.Hm) d.Hn u v r)
                (fun z => if cond z then Ω else 0)
          _ = (((rootPositions (d₀ * Y * d.Hm) d.Hn u v r).filter cond).card : ℝ) * Ω := by
              rw [← sum_filter, sum_const, nsmul_eq_mul]
          _ ≤ (2 ^ 13 * (Y / pf.1 + Y ^ (4 / 5 : ℝ))) * Ω :=
              mul_le_mul_of_nonneg_right hcard hΩ0
          _ ≤ (2 ^ 13 * (Y / P + Y ^ (4 / 5 : ℝ))) * Ω := by
              gcongr
          _ = Λ := by rw [hΛ]; ring
      · rw [ite_eq_right hxp]
        refine le_of_eq (sum_eq_zero fun z' _ => ?_)
        rw [ite_eq_right fun h => hxp (congrArg Prod.fst h), zero_mul]
    -- sum over the particles
    have hexp : ∀ z', Ψ σ z' pf * kern σ z' = 2 * ∑ xp : Particle x d, (s.2.2.1 xp : ℝ) *
        ((if xp.1 = (pf.1, lineOf pf.1 z'.1) then (1 : ℝ) else 0) * kern σ z') := by
      intro z'
      simp only [hΨ, ite_eq_left hΨc, mul_assoc, sum_mul]
      congr 1
      refine sum_congr rfl fun xp _ => ?_
      split_ifs <;> ring
    calc ∑ z', Ψ σ z' pf * kern σ z'
        = 2 * ∑ xp : Particle x d, (s.2.2.1 xp : ℝ) *
            ∑ z', (if xp.1 = (pf.1, lineOf pf.1 z'.1) then (1 : ℝ) else 0) * kern σ z' := by
          simp only [hexp, ← mul_sum]
          rw [sum_comm]
          simp only [mul_sum]
      _ ≤ 2 * ∑ xp : Particle x d, (s.2.2.1 xp : ℝ) * (if xp.1.1 = pf.1 then Λ else 0) := by
          gcongr with xp
          exact hinner xp
      _ = Φ pf := by
          simp only [hΦ, ite_eq_left hΨc.1, primeMult, mul_ite, mul_zero, mul_sum, sum_mul]
          refine sum_congr rfl fun xp _ => ?_
          split_ifs <;> ring
  -- the group sums
  have hlab : ∀ i, ∑ pf ∈ band x (d.a i) ×ˢ (univ : Finset Bool), ω pf ≤ 2 * B + 4 := by
    intro i
    rw [sum_product]
    simp only [Fintype.sum_bool, hω, ite_true, Bool.false_eq_true, ite_false, sum_add_distrib,
      ← mul_sum]
    have h₁ := sum_primeMult_le s.2.2.1 (band x (d.a i))
    have h₂ : (memSize s.2.2.1 : ℝ) ≤ B := by exact_mod_cast mem_memStates.1 s.2.2.2
    linarith [hνi i]
  have hlab₀ : ∑ pf ∈ band x (d.a i₀) ×ˢ (univ : Finset Bool), Φ pf ≤ (2 * B + 4) * Λ := by
    rw [sum_product]
    simp only [Fintype.sum_bool, hΦ, ite_true, Bool.false_eq_true, ite_false, add_zero,
      ← sum_mul, ← mul_sum]
    have h₁ := sum_primeMult_le s.2.2.1 (band x (d.a i₀))
    have h₂ : (memSize s.2.2.1 : ℝ) ≤ B := by exact_mod_cast mem_memStates.1 s.2.2.2
    have : 2 * ∑ p ∈ band x (d.a i₀), primeMult x d s.2.2.1 p ≤ 2 * B + 4 := by linarith
    exact mul_le_mul_of_nonneg_right this hΛ0
  set h : Fin K → ℕ × Bool → ℝ := fun i pf => if i = i₀ then Φ pf else ω pf with hh
  have hh0 : ∀ i pf, 0 ≤ h i pf := fun i pf => by
    simp only [hh]
    split_ifs
    exacts [hΦ0 _, hω0 _]
  -- the inner sum over the labels and the target
  have hinner : ∀ σ, ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
      ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), F σ z' lab ≤
        r₀ * ((2 * B + 4) ^ K * Λ) := by
    intro σ
    calc ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
          ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), F σ z' lab
        ≤ ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
            r₀ * ∏ i, h i (lab i) := by
          refine sum_le_sum fun lab hlab' => ?_
          have hlab₀' : lab i₀ ∈ band x (d.a i₀) ×ˢ (univ : Finset Bool) :=
            Fintype.mem_piFinset.1 hlab' i₀
          have hsplit : ∀ z', ∏ i, g σ z' i (lab i) =
              Ψ σ z' (lab i₀) * ∏ i ∈ univ.erase i₀, ω (lab i) := by
            intro z'
            rw [← mul_prod_erase univ _ (mem_univ i₀)]
            simp only [hg', ↓reduceIte]
            congr 1
            exact prod_congr rfl fun i hi => ite_eq_right (ne_of_mem_erase hi)
          have hsplit' : ∏ i, h i (lab i) = Φ (lab i₀) * ∏ i ∈ univ.erase i₀, ω (lab i) := by
            rw [← mul_prod_erase univ _ (mem_univ i₀)]
            simp only [hh, ↓reduceIte]
            congr 1
            exact prod_congr rfl fun i hi => ite_eq_right (ne_of_mem_erase hi)
          have hω' : 0 ≤ ∏ i ∈ univ.erase i₀, ω (lab i) := prod_nonneg fun i _ => hω0 _
          calc ∑ z', F σ z' lab
              = r₀ * (∏ i ∈ univ.erase i₀, ω (lab i)) * ∑ z', Ψ σ z' (lab i₀) * kern σ z' := by
                simp only [hF, hsplit, mul_sum]
                exact sum_congr rfl fun z' _ => by ring
            _ ≤ r₀ * (∏ i ∈ univ.erase i₀, ω (lab i)) * Φ (lab i₀) :=
                mul_le_mul_of_nonneg_left (hkey σ _ hlab₀') (mul_nonneg hr0 hω')
            _ = r₀ * ∏ i, h i (lab i) := by rw [hsplit']; ring
      _ = r₀ * ∏ i, ∑ pf ∈ band x (d.a i) ×ˢ (univ : Finset Bool), h i pf := by
          rw [prod_univ_sum, mul_sum]
      _ ≤ r₀ * ∏ i : Fin K, ((2 * (B : ℝ) + 4) * if i = i₀ then Λ else 1) := by
          refine mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun i _ => sum_nonneg fun pf _ =>
            hh0 _ _) fun i _ => ?_) hr0
          by_cases hi : i = i₀
          · subst hi
            simp only [hh, ↓reduceIte]
            exact hlab₀
          · simp only [hh, hi, ↓reduceIte, mul_one]
            exact hlab i
      _ = r₀ * ((2 * B + 4) ^ K * Λ) := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_ite_eq']
          simp
  -- assemble
  have hcard : (Fintype.card (Fin K → Equiv.Perm (Fin (M + 1))) : ℝ) =
      (((M + 1).factorial ^ K : ℕ) : ℝ) := by
    simp [Fintype.card_perm]
  have hf : (((M + 1).factorial ^ K : ℕ) : ℝ) ≠ 0 := by positivity
  calc ∑ c ∈ compChoices x d Y d₀ u v r S I, ‖compCoef q A₀ x d Y d₀ u v r B N s c‖
      ≤ ∑ c ∈ compChoices x d Y d₀ u v r S I, F c.1 c.2.2.1 c.2.2.2.1 := sum_le_sum hpt
    _ ≤ ∑ c ∈ edgeChoices x d Y d₀ u v r, F c.1 c.2.2.1 c.2.2.2.1 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun c _ _ => hF0 _ _ _
    _ = ∑ σ : Fin K → Equiv.Perm (Fin (M + 1)), ∑ _st : Finset (Fin K),
          ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
            ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
              ∑ _σ' : Fin K → Equiv.Perm (Fin (M + 1)), F σ z' lab := by
        simp only [edgeChoices, sum_product]
        rfl
    _ = ∑ σ : Fin K → Equiv.Perm (Fin (M + 1)), ∑ _st : Finset (Fin K),
          (((M + 1).factorial ^ K : ℕ) : ℝ) *
            ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
              ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), F σ z' lab := by
        refine sum_congr rfl fun σ _ => sum_congr rfl fun _ _ => ?_
        simp only [sum_const, card_univ, nsmul_eq_mul, hcard]
        rw [sum_comm]
        simp only [mul_sum]
    _ ≤ ∑ _σ : Fin K → Equiv.Perm (Fin (M + 1)), ∑ _st : Finset (Fin K),
          (((M + 1).factorial ^ K : ℕ) : ℝ) * (r₀ * ((2 * B + 4) ^ K * Λ)) :=
        sum_le_sum fun σ _ => sum_le_sum fun _ _ =>
          mul_le_mul_of_nonneg_left (hinner σ) (by positivity)
    _ = 2 ^ K * (2 * B + 4) ^ K * Λ := by
        simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_finset, Fintype.card_fin, hcard,
          hr₀]
        field_simp
        push_cast
        ring

/-! ### The column sums of a stored group -/

open scoped Classical in
/-- **The small column bound** (PD `mem:comparison-small` for the adjoint): if the group `i₀` is
stored and its primes are at least `P`, then for every output `s'` the measure-weighted absolute
comparison coefficients reaching `s'` sum to at most `3^K (B + 4)^K B Λ μ(s')`, with
`Λ = 4 L^{3A₀}/Y · 2^13 (Y/P + Y^{0.8})`. The stored particle `(b, [z]_b)` lies in the output
memory, which prescribes the line of the source; `b ∤ D` since the source lists are lists, so
the sources are counted by `card_filter_line_le` at the good target. The other groups are
bounded as in the crude column bound, through the adjoint calculation `crudeWeight_le_col`. -/
theorem sum_col_compCoef_le_of_mem (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀) (hY : 1 ≤ Y)
    (hU : 0 < d₀ * Y * d.Hm) (hL : 0 < Real.log x)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, ∀ p ∈ band x (d.a i), 1 / 2 ≤ primeMass x d p)
    (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p)
    (hνi : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4)
    {S I : Finset (Fin K)} {i₀ : Fin K} (hi₀ : i₀ ∈ S) {P : ℝ} (hP : 0 < P)
    (hPi : ∀ p ∈ band x (d.a i₀), P ≤ p) (s' : ChainState x d Y d₀ u v r B) :
    ∑ s, ∑ c ∈ compChoices x d Y d₀ u v r S I with chainEdgeOut x d Y d₀ u v r B s c = s',
        chainMeasure q x d Y d₀ u v r B N s * ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ ≤
      3 ^ K * (B + 4) ^ K *
        (B * (4 * Real.log x ^ (3 * A₀) / Y * (2 ^ 13 * (Y / P + Y ^ (4 / 5 : ℝ))))) *
        chainMeasure q x d Y d₀ u v r B N s' := by
  set M := padCount x with hM
  set Ω := 4 * Real.log x ^ (3 * A₀) / Y with hΩ
  set Λ := Ω * (2 ^ 13 * (Y / P + Y ^ (4 / 5 : ℝ))) with hΛ
  set r₀ := (((M + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hr₀
  set T := ⌈5 * Y⌉₊ with hT
  have hY0 : 0 < Y := by linarith
  have hΩ0 : 0 ≤ Ω := by positivity
  have hΛ0 : 0 ≤ Λ := by positivity
  have hr0 : 0 ≤ r₀ := by positivity
  have hμ0 : ∀ s : ChainState x d Y d₀ u v r B, 0 ≤ chainMeasure q x d Y d₀ u v r B N s :=
    fun s => mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg (fun xp => hν _) _)
  have hRHS : 0 ≤ 3 ^ K * ((B : ℝ) + 4) ^ K * (B * Λ) * chainMeasure q x d Y d₀ u v r B N s' := by
    have := hμ0 s'
    positivity
  -- an admissible choice reaching `s'`
  set A := ((univ ×ˢ compChoices x d Y d₀ u v r S I).filter fun p =>
      chainEdgeOut x d Y d₀ u v r B p.1 p.2 = s').filter fun p =>
    EdgeValid x d Y d₀ u v r B p.1 p.2 with hA
  have hfacts : ∀ p ∈ A, p.2 ∈ edgeChoices x d Y d₀ u v r ∧ p.2.2.1 = S ∧
      EdgeValid x d Y d₀ u v r B p.1 p.2 ∧
      s'.1 = p.2.2.2.1 ∧ s'.2.1.1 = edgeTgt p.1 p.2 ∧ s'.2.2.1 = edgeMem p.1 p.2 := by
    intro p hp
    simp only [hA, mem_filter, mem_product, mem_univ, true_and] at hp
    obtain ⟨⟨hc, hout⟩, hv⟩ := hp
    obtain ⟨hc, hcS, -⟩ := mem_filter.1 hc
    have he := hout.symm.trans (chainEdgeOut_of_valid hv)
    exact ⟨hc, hcS, hv, congrArg (fun t => t.1) he, congrArg (fun t => t.2.1.1) he,
      congrArg (fun t => t.2.2.1) he⟩
  -- the sum over the admissible choices
  have hsumA : ∑ s, ∑ c ∈ compChoices x d Y d₀ u v r S I with
      chainEdgeOut x d Y d₀ u v r B s c = s',
      chainMeasure q x d Y d₀ u v r B N s * ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ =
        ∑ p ∈ A, chainMeasure q x d Y d₀ u v r B N p.1 *
          ‖compCoef q A₀ x d Y d₀ u v r B N p.1 p.2‖ := by
    have hne : ∀ p ∈ (univ ×ˢ compChoices x d Y d₀ u v r S I).filter
        (fun p => chainEdgeOut x d Y d₀ u v r B p.1 p.2 = s'),
        chainMeasure q x d Y d₀ u v r B N p.1 *
          ‖compCoef q A₀ x d Y d₀ u v r B N p.1 p.2‖ ≠ 0 →
        EdgeValid x d Y d₀ u v r B p.1 p.2 := by
      intro p _ h
      by_contra hnv
      apply h
      rw [compCoef_eq_zero hnv, norm_zero, mul_zero]
    rw [hA, sum_filter_of_ne hne, sum_filter, sum_product]
    simp only [sum_filter]
    congr! 3
  -- a bad target is reached by no admissible choice
  by_cases hg : GoodFirst Y d₀ (tau r (complement s'.1.1) / tau r s'.1.1) s'.2.1.1
  swap
  · rw [hsumA]
    refine le_trans (le_of_eq (sum_eq_zero fun p hp => ?_)) hRHS
    obtain ⟨-, -, hv, hz, htgt, -⟩ := hfacts p hp
    exact absurd (by rw [hz, htgt]; exact hv.2.2.2.2.2.2.1.1) hg
  -- the parameters: `σ`, `σ'`, (stored, promoted, `b_i`) per group, and the source position
  set Dp : (Fin K → Equiv.Perm (Fin (M + 1))) → ℕ :=
    fun σ' => ∏ i, ∏ h : Fin M, s'.2.1.1 i ((σ' i).symm h.castSucc) with hDp
  set kern : (Fin K → Equiv.Perm (Fin (M + 1))) →
      ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) → ℝ := fun σ' z =>
    if d₀ ≤ (Dp σ' : ℝ) ∧ (Dp σ' : ℝ) < 2 * d₀ ∧
        ∃ t ∈ Icc (-(T : ℤ)) T, z.1.1 * s'.1.1.2 - z.1.2 * s'.1.1.1 = Dp σ' * t
      then Ω else 0 with hkern
  set Ξ : (Fin K → Equiv.Perm (Fin (M + 1))) → ℕ →
      ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) → ℝ := fun σ' b z =>
    if ¬ b ∣ Dp σ' then
      ∑ xp : Particle x d, if xp.1 = (b, lineOf b z.1) then (s'.2.2.1 xp : ℝ) else 0
    else 0 with hΞ
  set F : (Fin K → Equiv.Perm (Fin (M + 1))) × (Fin K → Equiv.Perm (Fin (M + 1))) ×
      (Fin K → Bool × Bool × ℕ) × ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) → ℝ := fun y =>
    chainMeasure q x d Y d₀ u v r B N s' * r₀ *
      (∏ i, colFactor q x d N s'.2.2.1 (y.2.2.1 i).1 (y.2.2.1 i).2.1 (y.2.2.1 i).2.2) *
      (Ξ y.2.1 (y.2.2.1 i₀).2.2 y.2.2.2 * kern y.2.1 y.2.2.2) with hF
  set φ : ChainState x d Y d₀ u v r B × EdgeChoice x d Y d₀ u v r →
      (Fin K → Equiv.Perm (Fin (M + 1))) × (Fin K → Equiv.Perm (Fin (M + 1))) ×
        (Fin K → Bool × Bool × ℕ) × ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) := fun p =>
    (p.2.1, p.2.2.2.2.2, fun i => (decide (i ∈ p.2.2.1), (p.2.2.2.2.1 i).2,
      edgeSrc p.1 p.2 i (Fin.last _)), p.1.1) with hφ
  set Params := (univ : Finset (Fin K → Equiv.Perm (Fin (M + 1)))) ×ˢ
    (univ : Finset (Fin K → Equiv.Perm (Fin (M + 1)))) ×ˢ
      Fintype.piFinset (fun i => (univ : Finset Bool) ×ˢ (univ : Finset Bool) ×ˢ
        band x (d.a i)) ×ˢ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r))
    with hParams
  have hcolF0 : ∀ st f b, 0 ≤ colFactor q x d N s'.2.2.1 st f b := fun st f b =>
    mul_nonneg (by split_ifs; exacts [primeMult_nonneg _ _, hν _]) (by split_ifs <;> norm_num)
  have hΞ0 : ∀ σ' b z, 0 ≤ Ξ σ' b z := fun σ' b z => by
    simp only [hΞ]
    split_ifs
    · exact le_rfl
    · exact sum_nonneg fun xp _ => by split_ifs <;> positivity
  have hkern0 : ∀ σ' z, 0 ≤ kern σ' z := fun σ' z => by
    simp only [hkern]
    split_ifs
    exacts [hΩ0, le_rfl]
  have hF0 : ∀ y, 0 ≤ F y := fun y =>
    mul_nonneg (mul_nonneg (mul_nonneg (hμ0 s') hr0) (prod_nonneg fun i _ => hcolF0 _ _ _))
      (mul_nonneg (hΞ0 _ _ _) (hkern0 _ _))
  -- the parameters determine the choice
  have hinj : Set.InjOn φ A := by
    rintro ⟨s₁, c₁⟩ hp₁ ⟨s₂, c₂⟩ hp₂ h
    obtain ⟨hc₁, -, hv₁, hz₁, htgt₁, hmem₁⟩ := hfacts _ hp₁
    obtain ⟨-, -, hv₂, hz₂, htgt₂, hmem₂⟩ := hfacts _ hp₂
    dsimp only at hc₁ hv₁ hz₁ htgt₁ hmem₁ hv₂ hz₂ htgt₂ hmem₂
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨hσ, hσ', htr, hz⟩ := h
    have htr' := fun i => congrFun htr i
    simp only [Prod.mk.injEq] at htr'
    have hst : c₁.2.1 = c₂.2.1 := Finset.ext fun i => by simpa using (htr' i).1
    have hb : ∀ i, edgeSrc s₁ c₁ i (Fin.last _) = edgeSrc s₂ c₂ i (Fin.last _) :=
      fun i => (htr' i).2.2
    have htgt : edgeTgt s₁ c₁ = edgeTgt s₂ c₂ := htgt₁.symm.trans htgt₂
    have hlab : c₁.2.2.2.1 = c₂.2.2.2.1 := funext fun i => Prod.ext
      (by rw [label_eq_tgt s₁ c₁, label_eq_tgt s₂ c₂, htgt, hσ']) (htr' i).2.1
    have hc : c₁ = c₂ :=
      Prod.ext hσ (Prod.ext hst (Prod.ext (hz₁.symm.trans hz₂) (Prod.ext hlab hσ')))
    subst hc
    -- the source lists: the pads are target labels and the last slots are the `b_i`
    have hact : s₁.2.1.1 = s₂.2.1.1 := by
      funext i h
      have key : ∀ s : ChainState x d Y d₀ u v r B,
          s.2.1.1 i h = edgeSrc s c₁ i ((c₁.1 i).symm h) := fun s => by
        simp only [edgeSrc, Equiv.apply_symm_apply]
      rw [key s₁, key s₂]
      by_cases hl : (c₁.1 i).symm h = Fin.last _
      · rw [hl]
        exact hb i
      · rw [edgeSrc_eq_tgt s₁ c₁ i hl, edgeSrc_eq_tgt s₂ c₁ i hl, htgt]
    -- the memories: the same particles are promoted and stored
    have hS : ∀ xp, s₁.2.2.1 xp = s₂.2.2.1 xp := by
      intro xp
      have h₁ := congrFun (hmem₁.symm.trans hmem₂) xp
      have hQ : (c₁.2.1.filter fun i => edgeStored s₁ c₁ i = xp.1) =
          (c₁.2.1.filter fun i => edgeStored s₂ c₁ i = xp.1) :=
        filter_congr fun i _ => by simp only [edgeStored, hb i, hz]
      simp only [edgeMem, hQ] at h₁
      have hP₁ := card_promoted_le hdisj hc₁ hv₁ xp
      have hP₂ := card_promoted_le hdisj hc₁ hv₂ xp
      omega
    exact Prod.ext (Prod.ext hz (Prod.ext (Subtype.ext hact) (Subtype.ext (funext hS)))) rfl
  -- the pointwise bound
  have hpt : ∀ p ∈ A, chainMeasure q x d Y d₀ u v r B N p.1 *
      ‖compCoef q A₀ x d Y d₀ u v r B N p.1 p.2‖ ≤ F (φ p) := by
    rintro ⟨s, c⟩ hp
    obtain ⟨hc, hcS, hv, hz, htgt, hmem⟩ := hfacts _ hp
    dsimp only at hc hcS hv hz htgt hmem
    have hi₀c : i₀ ∈ c.2.1 := hcS ▸ hi₀
    have hD : edgePad s c = Dp c.2.2.2.2 := by
      rw [edgePad_eq_tgt]
      simp only [hDp, htgt]
      rfl
    have hdet : edgeDet s c = s.1.1.1 * s'.1.1.2 - s.1.1.2 * s'.1.1.1 := by
      rw [hz]
      rfl
    have hμ' : chainMeasure q x d Y d₀ u v r B N s' =
        (∏ i, ∏ h, primeWeight q x d N (edgeTgt s c i h)) *
          memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) (edgeMem s c) := by
      rw [chainMeasure, htgt, hmem]
    have hw := crudeWeight_le_col hdisj hV hν hνpos hc hv
    rw [← hμ', ← hmem] at hw
    -- the stored particle lies in the output memory, so `Ξ ≥ 1`
    have hban : ¬ edgeSrc s c i₀ (Fin.last _) ∣ Dp c.2.2.2.2 := by
      rw [← hD]
      refine not_dvd_prod_of_ne (TypeII.band_prime (mem_band_edgeSrc s c i₀ _)) _
        (fun i h => TypeII.band_prime (mem_band_edgeSrc s c i _)) fun i h heq => ?_
      by_cases hi : i = i₀
      · subst hi
        have h1 := injective_of_mem_lists s.2.1.2 i
          (show s.2.1.1 i (c.1 i (Fin.last _)) = s.2.1.1 i (c.1 i h.castSucc) from heq)
        exact Fin.castSucc_ne_last h ((c.1 i).injective h1).symm
      · have hm : edgeSrc s c i₀ (Fin.last _) ∈ band x (d.a i) := by
          rw [heq]
          exact mem_band_edgeSrc s c i _
        exact disjoint_left.1 (hdisj i₀ i (Ne.symm hi)) (mem_band_edgeSrc s c i₀ _) hm
    have hΞ1 : 1 ≤ Ξ c.2.2.2.2 (edgeSrc s c i₀ (Fin.last _)) s.1 := by
      set xs : Particle x d := ⟨edgeStored s c i₀, hv.2.2.2.2.2.2.2.2.1 i₀ hi₀c⟩ with hxs
      have hQ : 1 ≤ (c.2.1.filter fun i => edgeStored s c i = xs.1).card :=
        card_pos.2 ⟨i₀, mem_filter.2 ⟨hi₀c, rfl⟩⟩
      have hS1 : (1 : ℝ) ≤ (s'.2.2.1 xs : ℝ) := by
        rw [hmem]
        have : 1 ≤ edgeMem s c xs := by
          unfold edgeMem
          omega
        exact_mod_cast this
      simp only [hΞ, hban, not_false_eq_true, ite_true]
      calc (1 : ℝ) ≤ (s'.2.2.1 xs : ℝ) := hS1
        _ = if xs.1 = (edgeSrc s c i₀ (Fin.last _), lineOf (edgeSrc s c i₀ (Fin.last _)) s.1.1)
              then (s'.2.2.1 xs : ℝ) else 0 := (ite_eq_left rfl).symm
        _ ≤ _ := single_le_sum (f := fun xp : Particle x d =>
              if xp.1 = (edgeSrc s c i₀ (Fin.last _), lineOf (edgeSrc s c i₀ (Fin.last _)) s.1.1)
                then (s'.2.2.1 xp : ℝ) else 0)
              (fun xp _ => by split_ifs <;> positivity) (mem_univ xs)
    -- the kernel
    by_cases ht : ∃ t ∈ Icc (-(T : ℤ)) T, edgeDet s c = edgePad s c * t
    swap
    · have h0 : compCoef q A₀ x d Y d₀ u v r B N s c = 0 := by
        by_contra h0
        exact ht (exists_det_of_compCoef_ne_zero hq hq₁ hd₀ hY0 hL hν h0)
      rw [h0, norm_zero, mul_zero]
      exact hF0 _
    have hk : kern c.2.2.2.2 s.1 = Ω := by
      refine ite_eq_left ⟨hD ▸ hv.2.2.1, hD ▸ hv.2.2.2.1, ?_⟩
      rw [← hdet, ← hD]
      exact ht
    have hker : Ω ≤ Ξ c.2.2.2.2 (edgeSrc s c i₀ (Fin.last _)) s.1 * kern c.2.2.2.2 s.1 := by
      rw [hk]
      calc Ω = 1 * Ω := (one_mul Ω).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hΞ1 hΩ0
    calc chainMeasure q x d Y d₀ u v r B N s * ‖compCoef q A₀ x d Y d₀ u v r B N s c‖
        ≤ chainMeasure q x d Y d₀ u v r B N s *
            (r₀ * crudeWeight q x d Y d₀ u v r B N s c * Ω) :=
          mul_le_mul_of_nonneg_left (norm_compCoef_le' hq hq₁ hd₀ hY0 hL hν hv) (hμ0 s)
      _ = r₀ * (chainMeasure q x d Y d₀ u v r B N s * crudeWeight q x d Y d₀ u v r B N s c) *
            Ω := by ring
      _ ≤ r₀ * (chainMeasure q x d Y d₀ u v r B N s' *
            ∏ i, colFactor q x d N s'.2.2.1 (decide (i ∈ c.2.1)) (c.2.2.2.1 i).2
              (edgeSrc s c i (Fin.last _))) *
            (Ξ c.2.2.2.2 (edgeSrc s c i₀ (Fin.last _)) s.1 * kern c.2.2.2.2 s.1) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw hr0) hker hΩ0
            (mul_nonneg hr0 (mul_nonneg (hμ0 s') (prod_nonneg fun i _ => hcolF0 _ _ _)))
      _ = F (φ (s, c)) := by
          simp only [hF, hφ]
          ring
  -- the image of the parameters
  have himage : A.image φ ⊆ Params := by
    intro y hy
    obtain ⟨⟨s, c⟩, -, rfl⟩ := mem_image.1 hy
    simp only [hParams, hφ, mem_product, mem_univ, true_and, and_true, Fintype.mem_piFinset]
    exact fun i => mem_band_edgeSrc s c i (Fin.last _)
  -- the sources on the prescribed line
  have hT6 : (T : ℝ) ≤ 6 * Y := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 5 * Y by linarith)
    rw [← hT] at this
    linarith
  have hkey : ∀ σ', ∀ b ∈ band x (d.a i₀),
      ∑ z, Ξ σ' b z * kern σ' z ≤ primeMult x d s'.2.2.1 b * Λ := by
    intro σ' b hb
    have hp := TypeII.band_prime hb
    have hPp := hPi _ hb
    have hR0 : 0 ≤ primeMult x d s'.2.2.1 b * Λ := mul_nonneg (primeMult_nonneg _ _) hΛ0
    by_cases hbD : ¬ b ∣ Dp σ'
    swap
    · rw [sum_eq_zero fun z _ => by simp only [hΞ, ite_eq_right hbD, zero_mul]]
      exact hR0
    by_cases hDr : d₀ ≤ (Dp σ' : ℝ) ∧ (Dp σ' : ℝ) < 2 * d₀
    swap
    · rw [sum_eq_zero fun z _ => by
        simp only [hkern]
        rw [ite_eq_right fun h => hDr ⟨h.1, h.2.1⟩, mul_zero]]
      exact hR0
    -- test (i) at the target, at the omission product `D_{σ'}`
    have hom := omitProd_last s'.2.1.1 (fun i => (σ' i).symm)
      (fun i h => (TypeII.band_prime (mem_band_of_mem_lists s'.2.1.2 i h)).pos)
    have hgoodD : ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (1 / 5 : ℝ) →
        Y ^ (-(7 / 10 : ℝ)) <
          circleDist (l * (Dp σ' : ℕ) * (tau r (complement s'.1.1) / tau r s'.1.1)) := by
      intro l hl hlY
      have := hg (fun i => (σ' i).symm (Fin.last M)) (by rw [hom]; exact hDr.1)
        (by rw [hom]; exact hDr.2) l hl hlY
      rwa [hom] at this
    -- each particle sees at most `Λ` of kernel mass on its line
    have hinner : ∀ xp : Particle x d,
        ∑ z, (if xp.1 = (b, lineOf b z.1) then (1 : ℝ) else 0) * kern σ' z ≤
          if xp.1.1 = b then Λ else 0 := by
      intro xp
      by_cases hxp : xp.1.1 = b
      · rw [ite_eq_left hxp]
        set cond : ℤ × ℤ → Prop := fun z =>
          (∃ t ∈ Icc (-(T : ℤ)) T, s'.1.1.1 * z.2 - s'.1.1.2 * z.1 = Dp σ' * t) ∧
            lineOf b z = xp.1.2 with hcond
        have hterm : ∀ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
            (if xp.1 = (b, lineOf b z.1) then (1 : ℝ) else 0) * kern σ' z ≤
              if cond z.1 then Ω else 0 := by
          intro z
          by_cases h1 : xp.1 = (b, lineOf b z.1)
          · rw [ite_eq_left h1, one_mul]
            by_cases ht : ∃ t ∈ Icc (-(T : ℤ)) T, z.1.1 * s'.1.1.2 - z.1.2 * s'.1.1.1 = Dp σ' * t
            · obtain ⟨t, htI, ht⟩ := ht
              have hc : cond z.1 := by
                refine ⟨⟨-t, ?_, by linear_combination -ht⟩, (congrArg Prod.snd h1).symm⟩
                obtain ⟨h₁, h₂⟩ := mem_Icc.1 htI
                exact mem_Icc.2 ⟨by omega, by omega⟩
              rw [ite_eq_left hc]
              simp only [hkern]
              split_ifs
              exacts [le_rfl, hΩ0]
            · have hk : kern σ' z = 0 := ite_eq_right fun h => ht h.2.2
              rw [hk]
              split_ifs
              exacts [hΩ0, le_rfl]
          · rw [ite_eq_right h1, zero_mul]
            split_ifs
            exacts [hΩ0, le_rfl]
        have hcard := card_filter_line_le hU hY s'.1.2 hgoodD hp hbD xp.1.2 hT6
        calc ∑ z, (if xp.1 = (b, lineOf b z.1) then (1 : ℝ) else 0) * kern σ' z
            ≤ ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
                if cond z.1 then Ω else 0 := sum_le_sum fun z _ => hterm z
          _ = ∑ z ∈ rootPositions (d₀ * Y * d.Hm) d.Hn u v r, if cond z then Ω else 0 :=
              sum_coe_sort (rootPositions (d₀ * Y * d.Hm) d.Hn u v r)
                (fun z => if cond z then Ω else 0)
          _ = (((rootPositions (d₀ * Y * d.Hm) d.Hn u v r).filter cond).card : ℝ) * Ω := by
              rw [← sum_filter, sum_const, nsmul_eq_mul]
          _ ≤ (2 ^ 13 * (Y / b + Y ^ (4 / 5 : ℝ))) * Ω :=
              mul_le_mul_of_nonneg_right hcard hΩ0
          _ ≤ (2 ^ 13 * (Y / P + Y ^ (4 / 5 : ℝ))) * Ω := by
              gcongr
          _ = Λ := by rw [hΛ]; ring
      · rw [ite_eq_right hxp]
        refine le_of_eq (sum_eq_zero fun z _ => ?_)
        rw [ite_eq_right fun h => hxp (congrArg Prod.fst h), zero_mul]
    have hexp : ∀ z, Ξ σ' b z * kern σ' z = ∑ xp : Particle x d, (s'.2.2.1 xp : ℝ) *
        ((if xp.1 = (b, lineOf b z.1) then (1 : ℝ) else 0) * kern σ' z) := by
      intro z
      simp only [hΞ, ite_eq_left hbD, sum_mul]
      refine sum_congr rfl fun xp _ => ?_
      split_ifs <;> ring
    calc ∑ z, Ξ σ' b z * kern σ' z
        = ∑ xp : Particle x d, (s'.2.2.1 xp : ℝ) *
            ∑ z, (if xp.1 = (b, lineOf b z.1) then (1 : ℝ) else 0) * kern σ' z := by
          simp only [hexp]
          rw [sum_comm]
          simp only [mul_sum]
      _ ≤ ∑ xp : Particle x d, (s'.2.2.1 xp : ℝ) * (if xp.1.1 = b then Λ else 0) := by
          gcongr with xp
          exact hinner xp
      _ = primeMult x d s'.2.2.1 b * Λ := by
          simp only [primeMult, mul_ite, mul_zero, sum_mul]
          refine sum_congr rfl fun xp _ => ?_
          split_ifs <;> ring
  -- the group sums
  have hgroup : ∀ i, ∑ t ∈ (univ : Finset Bool) ×ˢ (univ : Finset Bool) ×ˢ band x (d.a i),
      colFactor q x d N s'.2.2.1 t.1 t.2.1 t.2.2 ≤ 3 * (B + 4) := by
    intro i
    have h₁ := sum_primeMult_le s'.2.2.1 (band x (d.a i))
    have h₂ : (memSize s'.2.2.1 : ℝ) ≤ B := by exact_mod_cast mem_memStates.1 s'.2.2.2
    have h₃ := hνi i
    rw [sum_product, Fintype.sum_bool, sum_product, sum_product, Fintype.sum_bool,
      Fintype.sum_bool]
    simp only [colFactor, ↓reduceIte, Bool.false_eq_true, ← sum_mul]
    linarith
  have hB' : ∀ b, primeMult x d s'.2.2.1 b ≤ B := fun b => by
    have h₁ := sum_primeMult_le s'.2.2.1 {b}
    rw [sum_singleton] at h₁
    have h₂ : (memSize s'.2.2.1 : ℝ) ≤ B := by exact_mod_cast mem_memStates.1 s'.2.2.2
    linarith
  set hh : Fin K → Bool × Bool × ℕ → ℝ := fun i t =>
    if i = i₀ then colFactor q x d N s'.2.2.1 t.1 t.2.1 t.2.2 * (B * Λ)
    else colFactor q x d N s'.2.2.1 t.1 t.2.1 t.2.2 with hhh
  have hhh0 : ∀ i t, 0 ≤ hh i t := fun i t => by
    simp only [hhh]
    split_ifs
    · exact mul_nonneg (hcolF0 _ _ _) (by positivity)
    · exact hcolF0 _ _ _
  have hinnerσ : ∀ σ σ', ∑ tr ∈ Fintype.piFinset (fun i => (univ : Finset Bool) ×ˢ
      (univ : Finset Bool) ×ˢ band x (d.a i)),
      ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), F (σ, σ', tr, z) ≤
        chainMeasure q x d Y d₀ u v r B N s' * r₀ * ((3 * (B + 4)) ^ K * (B * Λ)) := by
    intro σ σ'
    have hμr : 0 ≤ chainMeasure q x d Y d₀ u v r B N s' * r₀ := mul_nonneg (hμ0 s') hr0
    calc ∑ tr ∈ Fintype.piFinset (fun i => (univ : Finset Bool) ×ˢ
          (univ : Finset Bool) ×ˢ band x (d.a i)),
          ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), F (σ, σ', tr, z)
        ≤ ∑ tr ∈ Fintype.piFinset (fun i => (univ : Finset Bool) ×ˢ
            (univ : Finset Bool) ×ˢ band x (d.a i)),
            chainMeasure q x d Y d₀ u v r B N s' * r₀ * ∏ i, hh i (tr i) := by
          refine sum_le_sum fun tr htr => ?_
          have hb₀ : (tr i₀).2.2 ∈ band x (d.a i₀) :=
            (mem_product.1 (mem_product.1 (Fintype.mem_piFinset.1 htr i₀)).2).2
          have hsplit : ∏ i, colFactor q x d N s'.2.2.1 (tr i).1 (tr i).2.1 (tr i).2.2 =
              colFactor q x d N s'.2.2.1 (tr i₀).1 (tr i₀).2.1 (tr i₀).2.2 *
                ∏ i ∈ univ.erase i₀, colFactor q x d N s'.2.2.1 (tr i).1 (tr i).2.1 (tr i).2.2 :=
            (mul_prod_erase univ _ (mem_univ i₀)).symm
          have hsplit' : ∏ i, hh i (tr i) =
              colFactor q x d N s'.2.2.1 (tr i₀).1 (tr i₀).2.1 (tr i₀).2.2 * (B * Λ) *
                ∏ i ∈ univ.erase i₀, colFactor q x d N s'.2.2.1 (tr i).1 (tr i).2.1 (tr i).2.2 := by
            rw [← mul_prod_erase univ _ (mem_univ i₀)]
            simp only [hhh, ↓reduceIte]
            congr 1
            exact prod_congr rfl fun i hi => ite_eq_right (ne_of_mem_erase hi)
          have hP0 : 0 ≤ ∏ i, colFactor q x d N s'.2.2.1 (tr i).1 (tr i).2.1 (tr i).2.2 :=
            prod_nonneg fun i _ => hcolF0 _ _ _
          calc ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), F (σ, σ', tr, z)
              = chainMeasure q x d Y d₀ u v r B N s' * r₀ *
                  (∏ i, colFactor q x d N s'.2.2.1 (tr i).1 (tr i).2.1 (tr i).2.2) *
                  ∑ z, Ξ σ' (tr i₀).2.2 z * kern σ' z := by
                simp only [hF, mul_sum]
            _ ≤ chainMeasure q x d Y d₀ u v r B N s' * r₀ *
                  (∏ i, colFactor q x d N s'.2.2.1 (tr i).1 (tr i).2.1 (tr i).2.2) *
                  (primeMult x d s'.2.2.1 (tr i₀).2.2 * Λ) :=
                mul_le_mul_of_nonneg_left (hkey σ' _ hb₀) (mul_nonneg hμr hP0)
            _ ≤ chainMeasure q x d Y d₀ u v r B N s' * r₀ *
                  (∏ i, colFactor q x d N s'.2.2.1 (tr i).1 (tr i).2.1 (tr i).2.2) * (B * Λ) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hB' _) hΛ0)
                  (mul_nonneg hμr hP0)
            _ = chainMeasure q x d Y d₀ u v r B N s' * r₀ * ∏ i, hh i (tr i) := by
                rw [hsplit', hsplit]
                ring
      _ = chainMeasure q x d Y d₀ u v r B N s' * r₀ *
            ∏ i, ∑ t ∈ (univ : Finset Bool) ×ˢ (univ : Finset Bool) ×ˢ band x (d.a i), hh i t := by
          rw [prod_univ_sum, mul_sum]
      _ ≤ chainMeasure q x d Y d₀ u v r B N s' * r₀ *
            ∏ i : Fin K, (3 * ((B : ℝ) + 4) * if i = i₀ then B * Λ else 1) := by
          refine mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun i _ => sum_nonneg fun t _ =>
            hhh0 _ _) fun i _ => ?_) hμr
          by_cases hi : i = i₀
          · subst hi
            simp only [hhh, ↓reduceIte, ← sum_mul]
            exact mul_le_mul_of_nonneg_right (hgroup i) (by positivity)
          · simp only [hhh, hi, ↓reduceIte, mul_one]
            exact hgroup i
      _ = chainMeasure q x d Y d₀ u v r B N s' * r₀ * ((3 * (B + 4)) ^ K * (B * Λ)) := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_ite_eq']
          simp
  have hcard : (Fintype.card (Fin K → Equiv.Perm (Fin (M + 1))) : ℝ) =
      (((M + 1).factorial ^ K : ℕ) : ℝ) := by
    simp [Fintype.card_perm]
  have hf : (((M + 1).factorial ^ K : ℕ) : ℝ) ≠ 0 := by positivity
  have hparams : ∑ y ∈ Params, F y ≤
      3 ^ K * (B + 4) ^ K * (B * Λ) * chainMeasure q x d Y d₀ u v r B N s' := by
    calc ∑ y ∈ Params, F y
        = ∑ σ : Fin K → Equiv.Perm (Fin (M + 1)),
            ∑ σ' : Fin K → Equiv.Perm (Fin (M + 1)),
              ∑ tr ∈ Fintype.piFinset (fun i => (univ : Finset Bool) ×ˢ
                (univ : Finset Bool) ×ˢ band x (d.a i)),
                ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), F (σ, σ', tr, z) := by
          simp only [hParams, sum_product]
      _ ≤ ∑ _σ : Fin K → Equiv.Perm (Fin (M + 1)),
            ∑ _σ' : Fin K → Equiv.Perm (Fin (M + 1)),
              chainMeasure q x d Y d₀ u v r B N s' * r₀ * ((3 * (B + 4)) ^ K * (B * Λ)) :=
          sum_le_sum fun σ _ => sum_le_sum fun σ' _ => hinnerσ σ σ'
      _ = 3 ^ K * (B + 4) ^ K * (B * Λ) * chainMeasure q x d Y d₀ u v r B N s' := by
          simp only [sum_const, card_univ, nsmul_eq_mul, hcard, hr₀, mul_pow]
          field_simp
  calc ∑ s, ∑ c ∈ compChoices x d Y d₀ u v r S I with chainEdgeOut x d Y d₀ u v r B s c = s',
        chainMeasure q x d Y d₀ u v r B N s * ‖compCoef q A₀ x d Y d₀ u v r B N s c‖
      = ∑ p ∈ A, chainMeasure q x d Y d₀ u v r B N p.1 *
          ‖compCoef q A₀ x d Y d₀ u v r B N p.1 p.2‖ := hsumA
    _ ≤ ∑ p ∈ A, F (φ p) := sum_le_sum hpt
    _ = ∑ y ∈ A.image φ, F y := (sum_image hinj).symm
    _ ≤ ∑ y ∈ Params, F y := sum_le_sum_of_subset_of_nonneg himage fun y _ _ => hF0 y
    _ ≤ _ := hparams

end Bounds

/-! ### Band facts -/

section Facts

variable {q x : ℝ} {d : Data K} {N : ℕ}

/-- A band prime is a band prime of the data. -/
private theorem mem_bandPrimes_of_mem_band {i : Fin K} {p : ℕ} (hp : p ∈ band x (d.a i)) :
    p ∈ bandPrimes x d :=
  mem_biUnion.2 ⟨i, mem_univ i, hp⟩

/-- `V(p) ≥ 0`. -/
private theorem primeMass_nonneg (p : ℕ) : 0 ≤ primeMass x d p :=
  sum_nonneg fun i _ => by
    split_ifs
    · exact sum_nonneg fun p _ => by positivity
    · exact le_rfl

/-- With band masses at least `1/2`, a prime of a band has `V(p) ≥ 1/2`. -/
private theorem half_le_primeMass (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i))) {i : Fin K}
    {p : ℕ} (hp : p ∈ band x (d.a i)) : 1 / 2 ≤ primeMass x d p :=
  calc 1 / 2 ≤ harmonicMass (band x (d.a i)) := hV i
    _ = if p ∈ band x (d.a i) then harmonicMass (band x (d.a i)) else 0 := (ite_eq_left hp).symm
    _ ≤ primeMass x d p :=
        single_le_sum (f := fun i => if p ∈ band x (d.a i) then harmonicMass (band x (d.a i))
          else 0) (fun j _ => by
            split_ifs
            · exact sum_nonneg fun p _ => by positivity
            · exact le_rfl) (mem_univ i)

/-- With baselines at least `1/2` at the band primes, the birth weights are nonnegative. -/
private theorem primeWeight_nonneg (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (p : ℕ) :
    0 ≤ primeWeight q x d N p := by
  unfold primeWeight
  by_cases hp : p ∈ bandPrimes x d
  · have := hb p hp
    exact one_div_nonneg.2 (mul_nonneg (mul_nonneg (primeMass_nonneg p) (by positivity))
      (by linarith))
  · have h0 : primeMass x d p = 0 :=
      sum_eq_zero fun i _ => ite_eq_right fun hpi => hp (mem_bandPrimes_of_mem_band hpi)
    rw [h0]
    simp

/-- At a prime of a band, `0 < ν(p) ≤ 4/p`. -/
private theorem primeWeight_pos_le (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) {i : Fin K} {p : ℕ}
    (hp : p ∈ band x (d.a i)) :
    0 < primeWeight q x d N p ∧ primeWeight q x d N p ≤ 4 * (1 / p) := by
  have hV₁ := half_le_primeMass hV hp
  have hb₁ := hb p (mem_bandPrimes_of_mem_band hp)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (TypeII.band_prime hp).pos
  unfold primeWeight
  refine ⟨one_div_pos.2 (mul_pos (mul_pos (by linarith) (by positivity)) (by linarith)), ?_⟩
  calc 1 / (primeMass x d p * ((p : ℝ) + 1) * baseline q N p)
      ≤ 1 / (1 / 2 * p * (1 / 2)) :=
        one_div_le_one_div_of_le (by positivity)
          (mul_le_mul (mul_le_mul hV₁ (by linarith) hp0.le (by linarith)) hb₁ (by norm_num)
            (mul_nonneg (by linarith) (by linarith)))
    _ = 4 * (1 / p) := by field_simp; norm_num

/-- With band masses in `[1/2, 1]`, the birth weights of a band sum to at most `4`. -/
private theorem sum_primeWeight_band_le (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hV₁ : ∀ i, harmonicMass (band x (d.a i)) ≤ 1)
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (i : Fin K) :
    ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4 :=
  calc ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ ∑ p ∈ band x (d.a i), 4 * (1 / (p : ℝ)) :=
        sum_le_sum fun p hp => (primeWeight_pos_le hV hb hp).2
    _ = 4 * harmonicMass (band x (d.a i)) := (mul_sum _ _ _).symm
    _ ≤ 4 * 1 := mul_le_mul_of_nonneg_left (hV₁ i) (by norm_num)
    _ = 4 := mul_one 4

/-- The damping defects are in `[0, 1]`. -/
private theorem dampDefect_mem_Icc (hq : 0 < q) (hq₁ : q < 1) (N j : ℕ) :
    0 ≤ dampDefect q N j ∧ dampDefect q N j ≤ 1 := by
  have hs : Real.sqrt q ≤ 1 := Real.sqrt_le_one.2 hq₁.le
  unfold dampDefect
  split_ifs <;> constructor <;> linarith [Real.sqrt_nonneg q]

/-- For primes `p ≥ 2N + 1`, the baseline is `b'_p ≥ 1/2`. -/
private theorem half_le_baseline (hq : 0 < q) (hq₁ : q < 1) {N p : ℕ}
    (hp : 2 * N + 1 ≤ p) : 1 / 2 ≤ baseline q N p := by
  have hp1 : (0 : ℝ) < p + 1 := by positivity
  have hNp : 2 * ((N : ℝ) + 1) ≤ p + 1 := by exact_mod_cast (show 2 * (N + 1) ≤ p + 1 by omega)
  have hsum : ∑ j ∈ range (N + 1), dampDefect q N j ≤ (N : ℝ) + 1 :=
    calc ∑ j ∈ range (N + 1), dampDefect q N j ≤ ∑ _j ∈ range (N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => (dampDefect_mem_Icc hq hq₁ N j).2
      _ = (N : ℝ) + 1 := by simp
  have h₁ : ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), dampDefect q N j ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ hp1]
    linarith
  unfold baseline
  linarith

end Facts

/-- Eventually every band prime is at least `2N + 1` for `N = 2R`. -/
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

/-! ### The norm bound -/

/-- A piece whose coefficients all vanish has norm at most any `c`, for a nonnegative input
measure. -/
private theorem normLe_choiceOp_of_eq_zero {ι κ γ : Type*} [Fintype ι] [Fintype κ]
    {μ : ι → ℝ} {ν : κ → ℝ} (hν : ∀ j, 0 ≤ ν j) {cs : Finset γ} {a : ι → γ → ℂ}
    {out : ι → γ → κ} (ha : ∀ i, ∀ c ∈ cs, a i c = 0) (c : ℝ) :
    NormLe μ ν (choiceOp cs a out) c := by
  intro f
  have h0 : choiceOp cs a out f = 0 := funext fun i => sum_eq_zero fun c hc => by
    rw [ha i c hc, zero_mul]
  rw [h0]
  simp only [wnormSq, Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, sum_const_zero]
  exact mul_nonneg (sq_nonneg _) (sum_nonneg fun j _ => mul_nonneg (hν j) (sq_nonneg _))

/-- The final comparison: for `c₁ ≤ L` and `e = 6K + 6A + 3`,
`c₁ L^{6K + 6A + 3} L^{-(e + 2|G| + 3)} ≤ (L^{-(G + 1)})²`. -/
private theorem final_le {L c₁ A G : ℝ} (hL : 1 ≤ L) (hc : c₁ ≤ L) (K : ℕ) :
    c₁ * (L ^ 3) ^ K * (L ^ 3) ^ K * L ^ (3 * A) * L ^ (3 * A) * L ^ 3 *
        L ^ (-(6 * (K : ℝ) + 6 * A + 3 + 2 * |G| + 3)) ≤
      (L ^ (-(G + 1))) ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hpow : (L ^ 3) ^ K * (L ^ 3) ^ K * L ^ (3 * A) * L ^ (3 * A) * L ^ 3 *
      L ^ (-(6 * (K : ℝ) + 6 * A + 3 + 2 * |G| + 3)) = L ^ (-(2 * |G| + 3)) := by
    rw [← pow_mul, ← pow_add, ← Real.rpow_natCast, ← Real.rpow_add hL0, ← Real.rpow_natCast,
      ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    push_cast
    ring
  have hsq : (L ^ (-(G + 1))) ^ 2 = L ^ (-(2 * G + 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    push_cast
    ring
  calc c₁ * (L ^ 3) ^ K * (L ^ 3) ^ K * L ^ (3 * A) * L ^ (3 * A) * L ^ 3 *
        L ^ (-(6 * (K : ℝ) + 6 * A + 3 + 2 * |G| + 3))
      = c₁ * L ^ (-(2 * |G| + 3)) := by rw [← hpow]; ring
    _ ≤ L * L ^ (-(2 * |G| + 3)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = L ^ (-(2 * |G| + 2)) := by
        rw [show L * L ^ (-(2 * |G| + 3)) = L ^ (1 : ℝ) * L ^ (-(2 * |G| + 3)) by
          rw [Real.rpow_one], ← Real.rpow_add hL0]
        congr 1
        ring
    _ ≤ L ^ (-(2 * G + 2)) :=
        Real.rpow_le_rpow_of_exponent_le hL (by linarith [le_abs_self G])
    _ = _ := hsq.symm

/-- **M8, the dirty comparison parts** (PD `mem:comparison-small`): eventually, for `B ≤ L³`,
`Y ≥ 1`, `d₀ > 0` and `(S, I) ≠ (∅, ∅)`, the comparison part has norm at most `L^{-G - 1}`
for the chain measure, uniformly in the root box. If a group is promoted, the row side is
small and the column side crude; otherwise a group is stored, and the column side is small.
The small side carries `1/P + Y^{-0.2}` with `P = L^E`; if `4Y ≤ L^E` the piece vanishes. -/
theorem eventually_compOp_normLe {q C CX alo ahi g A₀ G : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ (Y d₀ u v r : ℝ) (B : ℕ), 1 ≤ Y → 0 < d₀ → (B : ℝ) ≤ Real.log x ^ 3 →
      ∀ S I : Finset (Fin K), (S, I) ≠ (∅, ∅) →
        NormLe (fun s => chainMeasure q x d Y d₀ u v r B (2 * momentPower x) s)
          (fun s => chainMeasure q x d Y d₀ u v r B (2 * momentPower x) s)
          (compOp q A₀ x d Y d₀ u v r B (2 * momentPower x) S I)
          (Real.log x ^ (-(G + 1))) := by
  classical
  set Am := max A₀ 0 with hAm
  set E : ℝ := 5 * (6 * (K : ℝ) + 6 * Am + 3 + 2 * |G| + 3) with hE
  set c₁ : ℝ := 180 ^ K * 2 ^ 28 with hc₁
  have hc₁1 : 1 ≤ c₁ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (by norm_num)
  have hAm0 : 0 ≤ Am := le_max_right _ _
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  filter_upwards [eventually_harmonicMass_band halo.le, eventually_band_disjoint hg,
    eventually_two_mul_add_one_le halo, eventually_rpow_lt_of_mem_band (by linarith : 0 < alo) E,
    Real.tendsto_log_atTop.eventually_ge_atTop (max c₁ 2), eventually_gt_atTop 0]
    with x hV hdisj hbig hbandE hLc hx d hd Y d₀ u v r B hY hd₀ hB S I hSI
  set N := 2 * momentPower x with hN
  set L := Real.log x with hLdef
  have hL2 : 2 ≤ L := le_of_max_le_right hLc
  have hLc₁ : c₁ ≤ L := le_of_max_le_left hLc
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hY0 : 0 < Y := by linarith
  -- the band facts
  have hV₀ : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) := fun i => (hV _ (hd.window i).1).1
  have hV₁ : ∀ i, harmonicMass (band x (d.a i)) ≤ 1 := fun i => (hV _ (hd.window i).1).2
  have hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p :=
    fun p hp => half_le_baseline hq hq₁ (hbig d hd p hp)
  have hdisj' : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hdisj _ _ (hd.gap i j h)
    · exact (hdisj _ _ (hd.gap j i h)).symm
  have hHm : 0 < d.Hm := (Real.rpow_pos_of_pos hx _).trans_le hd.Hm_ge
  have hU : 0 < d₀ * Y * d.Hm := by positivity
  have hν := primeWeight_nonneg (q := q) (x := x) (d := d) (N := N) hb
  have hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p :=
    fun i p hp => (primeWeight_pos_le hV₀ hb hp).1
  have hνi := sum_primeWeight_band_le (q := q) (N := N) hV₀ hV₁ hb
  have hVp : ∀ i, ∀ p ∈ band x (d.a i), 1 / 2 ≤ primeMass x d p :=
    fun i p hp => half_le_primeMass hV₀ hp
  have hμ0 : ∀ s : ChainState x d Y d₀ u v r B, 0 ≤ chainMeasure q x d Y d₀ u v r B N s :=
    fun s => mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg (fun xp => hν _) _)
  -- a stored or promoted group
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin K, i₀ ∈ S ∨ i₀ ∈ I := by
    by_contra h
    push Not at h
    exact hSI (Prod.ext (eq_empty_of_forall_notMem fun i hi => (h i).1 hi)
      (eq_empty_of_forall_notMem fun i hi => (h i).2 hi))
  -- for `4Y ≤ L^E` the piece vanishes: the label product exceeds a band prime
  by_cases hYs : 4 * Y ≤ L ^ E
  · refine normLe_choiceOp_of_eq_zero hμ0 (fun s c hc => ?_) _
    by_contra hne
    have hlt := labelProd_lt_of_compCoef_ne_zero hY0 hne
    have hcE := (mem_filter.1 hc).1
    have hbig' := hbandE (d.a i₀) (hd.window i₀).1 _ (mem_band_of_mem_edgeChoices hcE i₀)
    have hle : ((c.2.2.2.1 i₀).1 : ℝ) ≤ ((∏ i, (c.2.2.2.1 i).1 : ℕ) : ℝ) := by
      exact_mod_cast Finset.single_le_prod
        (fun i _ => (TypeII.band_prime (mem_band_of_mem_edgeChoices hcE i)).one_lt.le)
        (mem_univ i₀)
    linarith
  push Not at hYs
  -- the decay `Λ ≤ 2^17 L^{3A} L^{-E/5}`
  set δ := L ^ (-(E / 5)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hLE5 : 0 < L ^ (E / 5) := by positivity
  have hδinv : δ = 1 / L ^ (E / 5) := by rw [hδ, Real.rpow_neg hL0.le, one_div]
  have hPi : ∀ i, ∀ p ∈ band x (d.a i), L ^ E ≤ p :=
    fun i p hp => (hbandE _ (hd.window i).1 p hp).le
  have hY5 : 0 < Y ^ (1 / 5 : ℝ) := by positivity
  have hYY : Y ^ (4 / 5 : ℝ) = Y * (1 / Y ^ (1 / 5 : ℝ)) := by
    rw [mul_one_div, eq_div_iff hY5.ne', ← Real.rpow_add hY0]
    norm_num
  -- `L^{E/5} ≤ 2 Y^{1/5}`, from `L^E < 4Y`
  have hE5 : L ^ (E / 5) ≤ 2 * Y ^ (1 / 5 : ℝ) := by
    have h5 : (L ^ (E / 5)) ^ 5 ≤ (2 * Y ^ (1 / 5 : ℝ)) ^ 5 := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ (E / 5)), ← Real.rpow_natCast (Y ^ (1 / 5 : ℝ)),
        ← Real.rpow_mul hL0.le, ← Real.rpow_mul hY0.le]
      norm_num
      linarith
    exact (pow_le_pow_iff_left₀ hLE5.le (by positivity) (by norm_num)).1 h5
  have hdecay : 1 / L ^ E + 1 / Y ^ (1 / 5 : ℝ) ≤ 3 * δ := by
    have h₁ : 1 / L ^ E ≤ δ := by
      rw [hδinv]
      exact one_div_le_one_div_of_le hLE5
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
    have h₂ : 1 / Y ^ (1 / 5 : ℝ) ≤ 2 * δ := by
      rw [hδinv, div_le_iff₀ hY5]
      rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ hLE5]
      linarith
    linarith
  set Λ := 4 * L ^ (3 * A₀) / Y * (2 ^ 13 * (Y / L ^ E + Y ^ (4 / 5 : ℝ))) with hΛ
  have hLA : L ^ (3 * A₀) ≤ L ^ (3 * Am) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hAm]; linarith [le_max_left A₀ 0])
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛle : Λ ≤ 2 ^ 17 * L ^ (3 * Am) * δ := by
    have hsplit : Λ = 2 ^ 15 * L ^ (3 * A₀) * (1 / L ^ E + 1 / Y ^ (1 / 5 : ℝ)) := by
      rw [hΛ, hYY]
      field_simp
      norm_num
    rw [hsplit]
    calc 2 ^ 15 * L ^ (3 * A₀) * (1 / L ^ E + 1 / Y ^ (1 / 5 : ℝ))
        ≤ 2 ^ 15 * L ^ (3 * Am) * (3 * δ) := by gcongr
      _ ≤ 2 ^ 17 * L ^ (3 * Am) * δ := by nlinarith [Real.rpow_nonneg hL0.le (3 * Am)]
  -- the crude sides, at `A₀` and at the arc parameter `-1`, which has no arcs
  have hno : ∀ n, arcIntegral (-1) x Y n = 0 := arcIntegral_eq_zero_of_lt_one (by
    rw [Real.rpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by linarith))
  set κ : ℝ := 16 * (1 + 52 * L ^ (3 * A₀)) + 16 * (1 + 52 * L ^ (3 * (-1 : ℝ))) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκle : κ ≤ 1696 * L ^ (3 * Am) := by
    have h1 : L ^ (3 * (-1 : ℝ)) ≤ L ^ (3 * Am) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have h2 : 1 ≤ L ^ (3 * Am) := Real.one_le_rpow hL1 (by linarith)
    linarith
  have hrowc : ∀ s, ∑ c ∈ compChoices x d Y d₀ u v r S I,
      ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ ≤ 2 ^ K * (2 * B + 4) ^ K * κ := by
    intro s
    calc ∑ c ∈ compChoices x d Y d₀ u v r S I, ‖compCoef q A₀ x d Y d₀ u v r B N s c‖
        ≤ ∑ c ∈ edgeChoices x d Y d₀ u v r, (‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ +
            ‖chainEdgeCoef q (-1) x d Y d₀ u v r B N s c‖) :=
          (sum_le_sum fun c _ => norm_compCoef_le_crude hno s c).trans
            (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun c _ _ => by positivity)
      _ ≤ 2 ^ K * (2 * B + 4) ^ K * (16 * (1 + 52 * L ^ (3 * A₀))) +
            2 ^ K * (2 * B + 4) ^ K * (16 * (1 + 52 * L ^ (3 * (-1 : ℝ)))) := by
          rw [sum_add_distrib]
          exact add_le_add (sum_norm_chainEdgeCoef_le hq hq₁ hd₀ hY hU hL0 hν hνi hVp s)
            (sum_norm_chainEdgeCoef_le hq hq₁ hd₀ hY hU hL0 hν hνi hVp s)
      _ = 2 ^ K * (2 * B + 4) ^ K * κ := by rw [hκ]; ring
  have hcolc : ∀ s', ∑ s, ∑ c ∈ compChoices x d Y d₀ u v r S I with
      chainEdgeOut x d Y d₀ u v r B s c = s',
        chainMeasure q x d Y d₀ u v r B N s * ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ ≤
      3 ^ K * (B + 4) ^ K * κ * chainMeasure q x d Y d₀ u v r B N s' := by
    intro s'
    calc ∑ s, ∑ c ∈ compChoices x d Y d₀ u v r S I with chainEdgeOut x d Y d₀ u v r B s c = s',
          chainMeasure q x d Y d₀ u v r B N s * ‖compCoef q A₀ x d Y d₀ u v r B N s c‖
        ≤ ∑ s, ∑ c ∈ edgeChoices x d Y d₀ u v r with chainEdgeOut x d Y d₀ u v r B s c = s',
            (chainMeasure q x d Y d₀ u v r B N s * ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ +
              chainMeasure q x d Y d₀ u v r B N s *
                ‖chainEdgeCoef q (-1) x d Y d₀ u v r B N s c‖) := by
          refine sum_le_sum fun s _ => ?_
          refine (sum_le_sum fun c _ => ?_).trans (sum_le_sum_of_subset_of_nonneg
            (filter_subset_filter _ (filter_subset _ _)) fun c _ _ => by
              have := hμ0 s
              positivity)
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (norm_compCoef_le_crude hno s c) (hμ0 s)
      _ ≤ 3 ^ K * (B + 4) ^ K * (16 * (1 + 52 * L ^ (3 * A₀))) *
            chainMeasure q x d Y d₀ u v r B N s' +
          3 ^ K * (B + 4) ^ K * (16 * (1 + 52 * L ^ (3 * (-1 : ℝ)))) *
            chainMeasure q x d Y d₀ u v r B N s' := by
          simp only [sum_add_distrib]
          exact add_le_add
            (sum_col_chainEdgeCoef_le hq hq₁ hd₀ hY hU hL0 hdisj' hVp hν hνpos hνi s')
            (sum_col_chainEdgeCoef_le hq hq₁ hd₀ hY hU hL0 hdisj' hVp hν hνpos hνi s')
      _ = 3 ^ K * (B + 4) ^ K * κ * chainMeasure q x d Y d₀ u v r B N s' := by rw [hκ]; ring
  -- the weighted Schur test with weight one, and the final comparison
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have h2B : 2 * (B : ℝ) + 4 ≤ 6 * L ^ 3 := by linarith
  have hB4 : (B : ℝ) + 4 ≤ 5 * L ^ 3 := by linarith
  have hfin : ∀ R C' : ℝ, 0 ≤ R → 0 ≤ C' →
      R * C' ≤ c₁ * (L ^ 3) ^ K * (L ^ 3) ^ K * L ^ (3 * Am) * L ^ (3 * Am) * L ^ 3 * δ →
      (∀ s, ∑ c ∈ compChoices x d Y d₀ u v r S I,
        ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ * 1 ≤ R * 1) →
      (∀ s', ∑ s, ∑ c ∈ compChoices x d Y d₀ u v r S I with
        chainEdgeOut x d Y d₀ u v r B s c = s',
          chainMeasure q x d Y d₀ u v r B N s * ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ * 1 ≤
        C' * (chainMeasure q x d Y d₀ u v r B N s' * 1)) →
      NormLe (fun s => chainMeasure q x d Y d₀ u v r B N s)
        (fun s => chainMeasure q x d Y d₀ u v r B N s)
        (compOp q A₀ x d Y d₀ u v r B N S I) (L ^ (-(G + 1))) := by
    intro R C' hR hC' hRC hrow hcol f
    have hnorm := normLe_choiceOp (h := fun _ => (1 : ℝ)) (h' := fun _ => (1 : ℝ)) hR hC' hμ0
      (fun _ => one_pos) hrow hcol f
    refine hnorm.trans (mul_le_mul_of_nonneg_right ?_
      (sum_nonneg fun s _ => mul_nonneg (hμ0 s) (sq_nonneg _)))
    rw [Real.sq_sqrt (mul_nonneg hR hC')]
    refine hRC.trans ?_
    rw [hδ, hE, show 5 * (6 * (K : ℝ) + 6 * Am + 3 + 2 * |G| + 3) / 5 =
      6 * (K : ℝ) + 6 * Am + 3 + 2 * |G| + 3 by ring]
    exact final_le hL1 hLc₁ K
  have hR0 : ∀ R : ℝ, 0 ≤ R → (∀ s, ∑ c ∈ compChoices x d Y d₀ u v r S I,
      ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ ≤ R) → ∀ s, ∑ c ∈ compChoices x d Y d₀ u v r S I,
        ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ * 1 ≤ R * 1 := fun R _ h s => by
    simp only [mul_one]
    exact h s
  have hC0 : ∀ C' : ℝ, (∀ s', ∑ s, ∑ c ∈ compChoices x d Y d₀ u v r S I with
      chainEdgeOut x d Y d₀ u v r B s c = s',
        chainMeasure q x d Y d₀ u v r B N s * ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ ≤
      C' * chainMeasure q x d Y d₀ u v r B N s') → ∀ s', ∑ s, ∑ c ∈ compChoices x d Y d₀ u v r S I
        with chainEdgeOut x d Y d₀ u v r B s c = s',
          chainMeasure q x d Y d₀ u v r B N s * ‖compCoef q A₀ x d Y d₀ u v r B N s c‖ * 1 ≤
        C' * (chainMeasure q x d Y d₀ u v r B N s' * 1) := fun C' h s' => by
    simp only [mul_one]
    exact h s'
  by_cases hI : i₀ ∈ I
  · -- a promoted group: the rows are small
    refine hfin (2 ^ K * (2 * B + 4) ^ K * Λ) (3 ^ K * (B + 4) ^ K * κ) (by positivity)
      (by positivity) ?_ (hR0 _ (by positivity) fun s =>
        sum_norm_compCoef_le_of_mem hq hq₁ hd₀ hY hU hL0 hν hνi hVp hI (by positivity)
          (hPi i₀) s) (hC0 _ hcolc)
    calc 2 ^ K * (2 * (B : ℝ) + 4) ^ K * Λ * (3 ^ K * ((B : ℝ) + 4) ^ K * κ)
        ≤ 2 ^ K * (6 * L ^ 3) ^ K * (2 ^ 17 * L ^ (3 * Am) * δ) *
            (3 ^ K * (5 * L ^ 3) ^ K * (1696 * L ^ (3 * Am))) := by
          gcongr
      _ = (180 ^ K * (2 ^ 17 * 1696)) * (L ^ 3) ^ K * (L ^ 3) ^ K * L ^ (3 * Am) *
            L ^ (3 * Am) * δ := by
          rw [show (180 : ℝ) = 2 * 6 * 3 * 5 by norm_num, mul_pow, mul_pow, mul_pow, mul_pow,
            mul_pow]
          ring
      _ ≤ c₁ * (L ^ 3) ^ K * (L ^ 3) ^ K * L ^ (3 * Am) * L ^ (3 * Am) * L ^ 3 * δ := by
          rw [hc₁]
          have h1 : (0 : ℝ) ≤ (L ^ 3) ^ K * (L ^ 3) ^ K * L ^ (3 * Am) * L ^ (3 * Am) * δ := by
            positivity
          have h2 : (180 : ℝ) ^ K * (2 ^ 17 * 1696) ≤ 180 ^ K * 2 ^ 28 :=
            mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
          calc (180 ^ K * (2 ^ 17 * 1696)) * (L ^ 3) ^ K * (L ^ 3) ^ K * L ^ (3 * Am) *
                L ^ (3 * Am) * δ
              = (180 ^ K * (2 ^ 17 * 1696)) *
                  ((L ^ 3) ^ K * (L ^ 3) ^ K * L ^ (3 * Am) * L ^ (3 * Am) * δ) := by ring
            _ ≤ (180 ^ K * 2 ^ 28) *
                  ((L ^ 3) ^ K * (L ^ 3) ^ K * L ^ (3 * Am) * L ^ (3 * Am) * δ * L ^ 3) :=
                mul_le_mul h2 (le_mul_of_one_le_right h1 hL3) h1 (by positivity)
            _ = _ := by ring
  · -- a stored group: the columns are small
    have hS : i₀ ∈ S := hi₀.resolve_right hI
    refine hfin (2 ^ K * (2 * B + 4) ^ K * κ) (3 ^ K * (B + 4) ^ K * (B * Λ)) (by positivity)
      (by positivity) ?_ (hR0 _ (by positivity) hrowc) (hC0 _ fun s' =>
        sum_col_compCoef_le_of_mem hq hq₁ hd₀ hY hU hL0 hdisj' hVp hν hνpos hνi hS
          (by positivity) (hPi i₀) s')
    have hBL : (B : ℝ) ≤ L ^ 3 := hB
    calc 2 ^ K * (2 * (B : ℝ) + 4) ^ K * κ * (3 ^ K * ((B : ℝ) + 4) ^ K * (B * Λ))
        ≤ 2 ^ K * (6 * L ^ 3) ^ K * (1696 * L ^ (3 * Am)) *
            (3 ^ K * (5 * L ^ 3) ^ K * (L ^ 3 * (2 ^ 17 * L ^ (3 * Am) * δ))) := by
          gcongr
      _ = (180 ^ K * (2 ^ 17 * 1696)) * (L ^ 3) ^ K * (L ^ 3) ^ K * L ^ (3 * Am) *
            L ^ (3 * Am) * L ^ 3 * δ := by
          rw [show (180 : ℝ) = 2 * 6 * 3 * 5 by norm_num, mul_pow, mul_pow, mul_pow, mul_pow,
            mul_pow]
          ring
      _ ≤ c₁ * (L ^ 3) ^ K * (L ^ 3) ^ K * L ^ (3 * Am) * L ^ (3 * Am) * L ^ 3 * δ := by
          rw [hc₁]
          gcongr
          norm_num

end Erdos408.OneSided
