import Erdos408.OneSided.Major.Energy.Average
import Erdos408.OneSided.Major.Energy.Isolated
import Erdos408.OneSided.Major.Energy.Mean
import Erdos408.OneSided.Major.Mellin
import Mathlib.Data.Fin.Tuple.Finset

/-!
# The energy of the separated major term

`blueprint/one_sided_type_ii.md` §6.3 steps 5–7 and §6.4. After the Mellin separation, the
major term at one arc and one character tuple is controlled by the energy
`∫_{|τ| ≤ XL^B} |B_λ M_α N_β|²` of three polynomials:

* `labelPoly`: `B_λ(τ) = Y⁻¹ ∑_{p} η(a/Y) e(-λ a/Y) ∏V_i⁻¹ χ(a) a^{iτ}` over label tuples,
  `a = ∏ p_i`;
* `markedPoly`: `M_α(τ) = H_m⁻¹ ∑_m α_m χ(m) m^{iτ}` (the sum of P4);
* `unmarkedPoly`: `N_β(τ)` (from `Major/Sparse.lean`).

`eventually_energy_le` gives energy at most `C₀ L^{-A'}`, `A' = energyExp`. The proof:

* Split the first band into `O(L)` dyads `[P, 2P)`, `P = exp(L^{a₀}) 2^r`, and use
  Cauchy–Schwarz over the dyads.
* In one dyad write `a = p b'`. Only `b' ≤ 4Y/P` occurs. Mellin-separate `η(a/Y) e(-λ a/Y)`
  (`exists_bumpTwist_mellin`, `∫ |g| ≪ L^{2A₀}`). The sum then factors as
  `Y^{-iξ} P_s (P Q)`, with `|P Q| ≤ 8` by B3 (`norm_dyadPoly_le`).
* Pass from the average over `ξ` to the energy by weighted Cauchy–Schwarz and Fubini
  (`integral_sq_le_of_le_integral`, in place of Minkowski).
* The isolated energy `∫ |P_s M_α N_β|²` (`eventually_integral_isolated_le`): on
  `{|P_s| ≤ L^{-A_s}}` use the mean value of `M_α N_β` (`maj:product-mean`,
  `integral_norm_markedPoly_mul_sq_le`). On the sparse family use P4,
  `|M_α| ≤ c₄ L^{-A}` for `|τ| ≤ 2XL^B`, together with `sum_norm_sq_le_of_sparse`.

With no bands the only label product is `1`, below every dyad, and `B_λ = 0`.
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real MeasureTheory

variable {K : ℕ}

/-- `B_λ(τ) = Y⁻¹ ∑_p η(a/Y) e(-λ a/Y) ∏ V_i⁻¹ χ(a) a^{iτ}`, `a = ∏ p_i`. -/
def labelPoly (x : ℝ) (d : Data K) (Y lam : ℝ) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (τ : ℝ) : ℂ :=
  (Y : ℂ)⁻¹ * ∑ p ∈ d.labels x,
    ((dyadicBump ((∏ i, p i : ℕ) / Y) * (d.bandMass x)⁻¹ : ℝ) : ℂ) *
      Complex.exp (-(2 * π * Complex.I * ((lam * (∏ i, p i : ℕ) / Y : ℝ) : ℂ))) *
      χ (∏ i, p i : ℕ) * ((∏ i, p i : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I)

/-- `M_α(τ) = H_m⁻¹ ∑_m α_m χ(m) m^{iτ}`. -/
def markedPoly (d : Data K) {k : ℕ} (χ : DirichletCharacter ℂ k) (τ : ℝ) : ℂ :=
  (d.Hm : ℂ)⁻¹ * ∑ m ∈ d.mRange, d.α m * χ m * (m : ℂ) ^ ((τ : ℂ) * Complex.I)

/-! ### Unimodular phases -/

/-- `n^{iτ} (n/Y)^{iξ} = e^{-iξ log Y} n^{i(τ + ξ)}` for `n ≠ 0` and `Y > 0`. -/
private theorem natCast_cpow_mul_ofReal_div_cpow {n : ℕ} (hn : n ≠ 0) {Y : ℝ} (hY : 0 < Y)
    (τ ξ : ℝ) :
    (n : ℂ) ^ ((τ : ℂ) * Complex.I) * (((n : ℝ) / Y : ℝ) : ℂ) ^ ((ξ : ℂ) * Complex.I) =
      Complex.exp (((-(ξ * Real.log Y) : ℝ) : ℂ) * Complex.I) *
        (n : ℂ) ^ (((τ + ξ : ℝ) : ℂ) * Complex.I) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnY : 0 < (n : ℝ) / Y := div_pos hn' hY
  rw [natCast_cpow_mul_I hn, natCast_cpow_mul_I hn,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hnY.ne'), ← Complex.ofReal_log hnY.le,
    Real.log_div hn'.ne' hY.ne', ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `|y^{iξ}| = 1` for `y > 0`. -/
private theorem norm_ofReal_cpow_mul_I {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    ‖(y : ℂ) ^ ((ξ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

/-- `ξ ↦ g(ξ) y^{iξ}` is integrable for `g` integrable and `y > 0`. -/
private theorem integrable_mul_ofReal_cpow {g : ℝ → ℂ} (hg : Integrable g) {y : ℝ} (hy : 0 < y) :
    Integrable fun ξ : ℝ => g ξ * (y : ℂ) ^ ((ξ : ℂ) * Complex.I) := by
  refine hg.mul_bdd (c := 1) ?_ (Eventually.of_forall fun ξ => (norm_ofReal_cpow_mul_I hy ξ).le)
  exact (Continuous.const_cpow (by fun_prop)
    (Or.inl (Complex.ofReal_ne_zero.2 hy.ne'))).aestronglyMeasurable

/-- `|∑_{n ∈ I} c_n n^{it}| ≤ ∑_{n ∈ I} |c_n|` when `0 ∉ I`. -/
private theorem norm_sum_mul_natCast_cpow_le {I : Finset ℕ} (hI : ∀ n ∈ I, n ≠ 0) (c : ℕ → ℂ)
    (t : ℝ) : ‖∑ n ∈ I, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ ∑ n ∈ I, ‖c n‖ := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
  rw [norm_mul, natCast_cpow_mul_I (hI n hn),
    show (Real.log n : ℂ) * Complex.I * t = ((Real.log n * t : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]

/-! ### The label polynomial by dyads of the first band -/

/-- The summand of `B_λ` at a label product `a`: `η(a/Y) V⁻¹ e(-λ a/Y) χ(a) a^{iτ}`. -/
private def labelTerm (x : ℝ) (d : Data K) (Y lam : ℝ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (τ : ℝ) (a : ℕ) : ℂ :=
  ((dyadicBump (a / Y) * (d.bandMass x)⁻¹ : ℝ) : ℂ) *
    Complex.exp (-(2 * π * Complex.I * ((lam * a / Y : ℝ) : ℂ))) *
    χ a * (a : ℂ) ^ ((τ : ℂ) * Complex.I)

/-- The tuples of primes from the bands after the first. -/
private def tailLabels (x : ℝ) (d : Data (K + 1)) : Finset (Fin K → ℕ) :=
  Fintype.piFinset fun i : Fin K => band x (d.a i.succ)

/-- The part of `B_λ` whose prime from the first band lies in `PS`. -/
private def dyadPoly (x : ℝ) (d : Data (K + 1)) (Y lam : ℝ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (PS : Finset ℕ) (τ : ℝ) : ℂ :=
  (Y : ℂ)⁻¹ * ∑ q ∈ PS, ∑ r ∈ tailLabels x d, labelTerm x d Y lam χ τ (q * ∏ i, r i)

/-- Splitting off the first coordinate of a label tuple:
`∑_p F(∏ p_i) = ∑_{q ∈ 𝒫₀} ∑_r F(q ∏ r_i)`, with `r` running over the later bands. -/
private theorem sum_labels_succ (x : ℝ) (d : Data (K + 1)) (F : ℕ → ℂ) :
    ∑ p ∈ d.labels x, F (∏ i, p i) =
      ∑ q ∈ band x (d.a 0), ∑ r ∈ tailLabels x d, F (q * ∏ i, r i) := by
  have h := Finset.filter_piFinset_eq_map_consEquiv (fun i => band x (d.a i))
    (fun _ : Fin K → ℕ => True)
  simp only [Finset.filter_true] at h
  unfold Data.labels tailLabels
  rw [h, sum_map, sum_product]
  refine sum_congr rfl fun q _ => sum_congr rfl fun r _ => ?_
  simp [Fin.prod_univ_succ]

/-- `B_λ` is continuous in `τ`, dyad by dyad. -/
private theorem continuous_dyadPoly (x : ℝ) (d : Data (K + 1)) (Y lam : ℝ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) {PS : Finset ℕ} (hPS : ∀ q ∈ PS, q ≠ 0) :
    Continuous (dyadPoly x d Y lam χ PS) := by
  unfold dyadPoly
  refine continuous_const.mul (continuous_finsetSum _ fun q hq =>
    continuous_finsetSum _ fun r hr => ?_)
  have hr0 : ∏ i, r i ≠ 0 := prod_ne_zero_iff.2 fun i _ =>
    (TypeII.band_prime ((Fintype.mem_piFinset.1 hr) i)).ne_zero
  have h := continuous_natCast_cpow_mul_I (Nat.mul_ne_zero (hPS q hq) hr0)
  unfold labelTerm
  exact continuous_const.mul h

/-- The Mellin form of one label term: if `η(y) e(-λy) = ∫ g(ξ) y^{iξ}` for `y > 0`, then the
term at `a ≥ 1` is `V⁻¹ χ(a) a^{iτ} ∫ g(ξ) (a/Y)^{iξ}`. -/
private theorem labelTerm_eq_integral {x Y lam : ℝ} {d : Data K} (hY : 0 < Y) {g : ℝ → ℂ}
    (hgm : ∀ y : ℝ, 0 < y →
      (dyadicBump y : ℂ) * Complex.exp (-(2 * π * Complex.I * ((lam * y : ℝ) : ℂ))) =
        ∫ ξ, g ξ * (y : ℂ) ^ ((ξ : ℂ) * Complex.I))
    {k : ℕ} (χ : DirichletCharacter ℂ k) (τ : ℝ) {a : ℕ} (ha : 0 < a) :
    labelTerm x d Y lam χ τ a = ((d.bandMass x)⁻¹ : ℂ) * χ a * (a : ℂ) ^ ((τ : ℂ) * Complex.I) *
      ∫ ξ, g ξ * (((a : ℝ) / Y : ℝ) : ℂ) ^ ((ξ : ℂ) * Complex.I) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [← hgm _ (div_pos ha' hY)]
  unfold labelTerm
  rw [show lam * (a : ℝ) / Y = lam * ((a : ℝ) / Y) from mul_div_assoc _ _ _]
  push_cast
  ring

/-- PD §5, the dyad contribution: for primes `PS ⊆ [P, 2P)` from the first band,
`|B_λ^{PS}(τ)| ≤ 8 ∫ |g(ξ)| |P_s(τ; ξ)| dξ`. Only label products `a = q b' ≤ 4Y` occur, so
`b' ≤ 4Y/P`. After Mellin inversion of `η(a/Y) e(-λa/Y)` the sum over `a = q b'` factors as
`Y^{-iξ} (P P_s) Q`, where `Q = Y⁻¹ V⁻¹ ∑_{b' ≤ 4Y/P} χ(b') b'^{i(τ + ξ)}` has
`|Q| ≤ (4/P) V⁻¹ ∑_{b'} 1/b' = 4 / (P V₀) ≤ 8 / P`. -/
private theorem norm_dyadPoly_le {x Y lam P : ℝ} {d : Data (K + 1)} (hY : 0 < Y) (hP : 1 ≤ P)
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i))) {PS : Finset ℕ}
    (hPS : ∀ q ∈ PS, q.Prime ∧ P ≤ q ∧ (q : ℝ) < 2 * P) {g : ℝ → ℂ} (hg : Integrable g)
    (hgm : ∀ y : ℝ, 0 < y →
      (dyadicBump y : ℂ) * Complex.exp (-(2 * π * Complex.I * ((lam * y : ℝ) : ℂ))) =
        ∫ ξ, g ξ * (y : ℂ) ^ ((ξ : ℂ) * Complex.I))
    {k : ℕ} (χ : DirichletCharacter ℂ k) (τ : ℝ) :
    ‖dyadPoly x d Y lam χ PS τ‖ ≤ 8 * ∫ ξ, ‖g ξ‖ * ‖primePoly P PS χ ξ τ‖ := by
  set V := d.bandMass x
  set T' := tailLabels x d
  have hP0 : 0 < P := by linarith
  have hq : ∀ q ∈ PS, 0 < q := fun q hq => (hPS q hq).1.pos
  have hr : ∀ r ∈ T', 0 < ∏ i, r i := fun r hr =>
    prod_pos fun i _ => (TypeII.band_prime ((Fintype.mem_piFinset.1 hr) i)).pos
  -- the masses: `V = V₀ ∏_{i ≥ 1} V_i` and `∑_{b'} 1/b' = ∏_{i ≥ 1} V_i`
  have hVi : ∀ i, 0 < harmonicMass (band x (d.a i)) := fun i => by linarith [hV i]
  set V' := ∏ i : Fin K, harmonicMass (band x (d.a i.succ))
  have hV' : 0 < V' := prod_pos fun i _ => hVi _
  have hVeq : V = harmonicMass (band x (d.a 0)) * V' := Fin.prod_univ_succ _
  have hV0 : 0 < V := by rw [hVeq]; exact mul_pos (hVi 0) hV'
  have hsum : ∑ r ∈ T', ((∏ i, r i : ℕ) : ℝ)⁻¹ = V' := by
    simp only [V', harmonicMass, T', tailLabels]
    rw [prod_univ_sum]
    refine sum_congr rfl fun r _ => ?_
    push_cast
    rw [← prod_inv_distrib]
    simp [one_div]
  -- the indicator `[P b' ≤ 4Y]`
  set ind : (Fin K → ℕ) → ℂ := fun r => if P * (∏ i, r i : ℕ) ≤ 4 * Y then 1 else 0
  -- only `P b' ≤ 4Y` contributes
  have hind : ∀ q ∈ PS, ∀ r : Fin K → ℕ,
      labelTerm x d Y lam χ τ (q * ∏ i, r i) = ind r * labelTerm x d Y lam χ τ (q * ∏ i, r i) := by
    intro q hq' r
    by_cases h : P * (∏ i, r i : ℕ) ≤ 4 * Y
    · simp only [ind, h, ↓reduceIte, one_mul]
    · simp only [ind, h, ↓reduceIte, zero_mul]
      have hη : dyadicBump (((q * ∏ i, r i : ℕ) : ℝ) / Y) = 0 := by
        by_contra hne
        have h₁ := (lt_of_dyadicBump_ne_zero hne).2
        rw [div_lt_iff₀ hY] at h₁
        have h₂ : P * (∏ i, r i : ℕ) ≤ ((q * ∏ i, r i : ℕ) : ℝ) := by
          rw [Nat.cast_mul]
          exact mul_le_mul_of_nonneg_right (hPS q hq').2.1 (Nat.cast_nonneg _)
        exact h (by linarith)
      unfold labelTerm
      rw [hη, zero_mul, Complex.ofReal_zero, zero_mul, zero_mul, zero_mul]
  -- the inner polynomial after Mellin inversion
  set c : ℕ → (Fin K → ℕ) → ℂ := fun q r => (V : ℂ)⁻¹ * χ (q * ∏ i, r i : ℕ) *
    ((q * ∏ i, r i : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I)
  set y : ℕ → (Fin K → ℕ) → ℝ := fun q r => ((q * ∏ i, r i : ℕ) : ℝ) / Y
  have hy : ∀ q ∈ PS, ∀ r ∈ T', 0 < y q r := fun q hq' r hr' =>
    div_pos (by exact_mod_cast Nat.mul_pos (hq q hq') (hr r hr')) hY
  set W : ℝ → ℂ := fun ξ => (Y : ℂ)⁻¹ * ∑ q ∈ PS, ∑ r ∈ T',
    ind r * (c q r * ((y q r : ℝ) : ℂ) ^ ((ξ : ℂ) * Complex.I))
  have hW : dyadPoly x d Y lam χ PS τ = ∫ ξ, g ξ * W ξ := by
    have hint : ∀ q ∈ PS, ∀ r ∈ T', Integrable fun ξ : ℝ =>
        (Y : ℂ)⁻¹ * ind r * c q r * (g ξ * ((y q r : ℝ) : ℂ) ^ ((ξ : ℂ) * Complex.I)) :=
      fun q hq' r hr' => (integrable_mul_ofReal_cpow hg (hy q hq' r hr')).const_mul _
    calc dyadPoly x d Y lam χ PS τ
        = ∑ q ∈ PS, ∑ r ∈ T', (Y : ℂ)⁻¹ * ind r * c q r *
            ∫ ξ, g ξ * ((y q r : ℝ) : ℂ) ^ ((ξ : ℂ) * Complex.I) := by
          unfold dyadPoly
          rw [mul_sum]
          refine sum_congr rfl fun q hq' => ?_
          rw [mul_sum]
          refine sum_congr rfl fun r hr' => ?_
          rw [hind q hq' r, labelTerm_eq_integral hY hgm χ τ (Nat.mul_pos (hq q hq') (hr r hr'))]
          simp only [c, y]
          ring
      _ = ∑ q ∈ PS, ∑ r ∈ T', ∫ ξ, (Y : ℂ)⁻¹ * ind r * c q r *
            (g ξ * ((y q r : ℝ) : ℂ) ^ ((ξ : ℂ) * Complex.I)) := by
          simp_rw [integral_const_mul]
      _ = ∫ ξ, ∑ q ∈ PS, ∑ r ∈ T', (Y : ℂ)⁻¹ * ind r * c q r *
            (g ξ * ((y q r : ℝ) : ℂ) ^ ((ξ : ℂ) * Complex.I)) := by
          rw [integral_finsetSum _ fun q hq' =>
            integrable_finsetSum _ fun r hr' => hint q hq' r hr']
          refine sum_congr rfl fun q hq' => ?_
          rw [integral_finsetSum _ fun r hr' => hint q hq' r hr']
      _ = ∫ ξ, g ξ * W ξ := by
          congr 1
          ext ξ
          simp only [W, mul_sum]
          refine sum_congr rfl fun q _ => sum_congr rfl fun r _ => ?_
          ring
  -- the inner polynomial factors, and is at most `8 |P_s|`
  have hWle : ∀ ξ, ‖W ξ‖ ≤ 8 * ‖primePoly P PS χ ξ τ‖ := by
    intro ξ
    set e := Complex.exp (((-(ξ * Real.log Y) : ℝ) : ℂ) * Complex.I)
    set A : ℕ → ℂ := fun q => χ q * (q : ℂ) ^ (((τ + ξ : ℝ) : ℂ) * Complex.I)
    set Bt : (Fin K → ℕ) → ℂ := fun r =>
      ind r * (χ (∏ i, r i : ℕ) * ((∏ i, r i : ℕ) : ℂ) ^ (((τ + ξ : ℝ) : ℂ) * Complex.I))
    have hfac : W ξ = e * ((Y : ℂ)⁻¹ * (V : ℂ)⁻¹) * ((∑ q ∈ PS, A q) * ∑ r ∈ T', Bt r) := by
      rw [sum_mul_sum]
      simp only [W, mul_sum]
      refine sum_congr rfl fun q hq' => sum_congr rfl fun r hr' => ?_
      show (Y : ℂ)⁻¹ * (ind r * (c q r * ((y q r : ℝ) : ℂ) ^ ((ξ : ℂ) * Complex.I))) =
        e * ((Y : ℂ)⁻¹ * (V : ℂ)⁻¹) * (A q * Bt r)
      have hqr : q * ∏ i, r i ≠ 0 := (Nat.mul_pos (hq q hq') (hr r hr')).ne'
      simp only [c, y, A, Bt, e]
      rw [mul_assoc ((V : ℂ)⁻¹ * χ _), natCast_cpow_mul_ofReal_div_cpow hqr hY,
        Nat.cast_mul (α := ZMod k), map_mul, Nat.cast_mul (α := ℂ),
        Complex.natCast_mul_natCast_cpow]
      ring
    -- `∑_q A_q = P P_s`
    have hA : ∑ q ∈ PS, A q = (P : ℂ) * primePoly P PS χ ξ τ := by
      unfold primePoly
      rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hP0.ne'), one_mul]
    -- `|∑_r B_r| ≤ (4Y/P) V'`
    have hB : ‖∑ r ∈ T', Bt r‖ ≤ 4 * Y / P * V' := by
      refine (norm_sum_le _ _).trans ?_
      rw [← hsum, mul_sum]
      refine sum_le_sum fun r hr' => ?_
      have hb : (0 : ℝ) < (∏ i, r i : ℕ) := by exact_mod_cast hr r hr'
      simp only [Bt, ind]
      rw [norm_mul, norm_mul, natCast_cpow_mul_I (hr r hr').ne',
        show (Real.log (∏ i, r i : ℕ) : ℂ) * Complex.I * ((τ + ξ : ℝ) : ℂ) =
          ((Real.log (∏ i, r i : ℕ) * (τ + ξ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      by_cases h : P * (∏ i, r i : ℕ) ≤ 4 * Y
      · rw [ite_eq_left h, norm_one, one_mul]
        refine (DirichletCharacter.norm_le_one χ _).trans ?_
        rw [div_mul_eq_mul_div, le_div_iff₀ hP0, ← div_eq_mul_inv, one_mul,
          le_div_iff₀ hb]
        linarith
      · rw [ite_eq_right h, norm_zero, zero_mul]
        positivity
    have he : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    rw [hfac, hA]
    simp only [norm_mul, norm_inv, Complex.norm_real, he, Real.norm_of_nonneg hY.le,
      Real.norm_of_nonneg hV0.le, Real.norm_of_nonneg hP0.le]
    have hPs := norm_nonneg (primePoly P PS χ ξ τ)
    calc _ ≤ 1 * (Y⁻¹ * V⁻¹) * (P * ‖primePoly P PS χ ξ τ‖ * (4 * Y / P * V')) := by gcongr
      _ = 4 * ‖primePoly P PS χ ξ τ‖ * (V' / V) := by
          field_simp
      _ = 4 * ‖primePoly P PS χ ξ τ‖ * (harmonicMass (band x (d.a 0)))⁻¹ := by
          rw [hVeq, div_mul_cancel_right₀ hV'.ne']
      _ ≤ 4 * ‖primePoly P PS χ ξ τ‖ * 2 := by
          gcongr
          rw [inv_le_comm₀ (hVi 0) two_pos]
          linarith [hV 0]
      _ = 8 * ‖primePoly P PS χ ξ τ‖ := by ring
  -- integrate against `|g|`
  have hbd : Integrable fun ξ => 8 * (‖g ξ‖ * ‖primePoly P PS χ ξ τ‖) := by
    have hc : Continuous fun ξ => primePoly P PS χ ξ τ := by
      have h := (continuous_primePoly (P := P) (fun q hq' => (hq q hq').ne') χ).comp
        (continuous_id.prodMk (continuous_const (y := τ)))
      exact h
    exact (hg.norm.mul_bdd (c := 2) hc.norm.aestronglyMeasurable (Eventually.of_forall fun ξ => by
      rw [norm_norm]; exact norm_primePoly_le_two hP hPS χ ξ τ)).const_mul 8
  rw [hW, ← integral_const_mul]
  refine norm_integral_le_of_norm_le hbd (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul]
  calc ‖g ξ‖ * ‖W ξ‖ ≤ ‖g ξ‖ * (8 * ‖primePoly P PS χ ξ τ‖) := by gcongr; exact hWle ξ
    _ = 8 * (‖g ξ‖ * ‖primePoly P PS χ ξ τ‖) := by ring

/-! ### The mean value of `M_α N_β` -/

/-- PD `maj:product-mean` on `[-T, T]` with `T = X L^B`: `∫_{-T}^T |M_α N_β|² ≤ 10584 L^{C₄ + B}`,
once `log 4X ≤ 2L`. The coefficients of `M_α N_β` are `X⁻¹ ∑_{mn = l} α_m χ(m) β_n ψ(n)`, of
length `N ≤ 4X`, and `maj:product-mean` (`integral_norm_sum_mul_sum_sq_le`) gives
`X⁻² (2T + 8N(1 + log N)) L^{4C} N (1 + log N)³ ≤ X⁻² (98 X L^{B + 1}) L^{4C} (108 X L³)`. -/
private theorem integral_norm_markedPoly_mul_sq_le {C CX alo ahi g x B : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d) (hx : 1 ≤ x) (hL : 1 ≤ Real.log x) (hB : 0 ≤ B)
    (hlog : Real.log (4 * d.X) ≤ 2 * Real.log x) {k : ℕ} (χ₂ χ₃ : DirichletCharacter ℂ k) :
    ∫ τ in (-(d.X * Real.log x ^ B))..(d.X * Real.log x ^ B),
        ‖markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ‖ ^ 2 ≤
      10584 * Real.log x ^ (meanExp C + B) := by
  set L := Real.log x
  set T := d.X * L ^ B
  have hL0 : 0 < L := by linarith
  have hγ : 0 ≤ d.γ := (Real.rpow_nonneg hL0.le _).trans hd.γ_ge
  have hHm : 1 ≤ d.Hm := (Real.one_le_rpow hx hγ).trans hd.Hm_ge
  have hHn : 1 ≤ d.Hn := (Real.one_le_rpow hx hγ).trans hd.Hn_ge
  have hX : 0 < d.X := mul_pos (by linarith) (by linarith)
  have hT : 0 ≤ T := by positivity
  -- the coefficients are at most `L^C`
  have hLC : 0 ≤ L ^ C := Real.rpow_nonneg hL0.le _
  have hu : ∀ m ∈ d.mRange, ‖d.α m * χ₂ m‖ ≤ L ^ C := by
    intro m _
    rw [norm_mul]
    by_cases h : d.α m = 0
    · rw [h, norm_zero, zero_mul]
      exact hLC
    · calc ‖d.α m‖ * ‖χ₂ m‖ ≤ L ^ C * 1 := mul_le_mul (hd.α_supp m h).2.2.2
            (DirichletCharacter.norm_le_one χ₂ _) (norm_nonneg _) hLC
        _ = L ^ C := mul_one _
  have hv : ∀ n ∈ d.nRange, ‖d.β n * χ₃ n‖ ≤ L ^ C := by
    intro n _
    rw [norm_mul]
    by_cases h : d.β n = 0
    · rw [h, norm_zero, zero_mul]
      exact hLC
    · calc ‖d.β n‖ * ‖χ₃ n‖ ≤ L ^ C * 1 := mul_le_mul (hd.β_supp n h).2.2.2
            (DirichletCharacter.norm_le_one χ₃ _) (norm_nonneg _) hLC
        _ = L ^ C := mul_one _
  -- the ranges lie in `[1, ⌊2H_m⌋]` and `[1, ⌊2H_n⌋]`
  set N₁ := ⌊2 * d.Hm⌋₊
  set N₂ := ⌊2 * d.Hn⌋₊
  have hI₁ : ∀ m ∈ d.mRange, 1 ≤ m ∧ m ≤ N₁ := fun m hm => by
    rw [Data.mRange, mem_Icc] at hm
    exact ⟨(Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne').trans hm.1, hm.2⟩
  have hI₂ : ∀ n ∈ d.nRange, 1 ≤ n ∧ n ≤ N₂ := fun n hn => by
    rw [Data.nRange, mem_Icc] at hn
    exact ⟨(Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne').trans hn.1, hn.2⟩
  have hmean := integral_norm_sum_mul_sum_sq_le hI₁ hI₂ hLC hLC hu hv
    (a := -T) (b := T) (by linarith)
  -- `M_α N_β = X⁻¹ (∑_m α_m χ(m) m^{iτ}) (∑_n β_n ψ(n) n^{iτ})`
  have hprod : ∀ τ : ℝ, ‖markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ‖ ^ 2 = d.X⁻¹ ^ 2 *
      ‖(∑ m ∈ d.mRange, d.α m * χ₂ m * (m : ℂ) ^ ((τ : ℂ) * Complex.I)) *
        (∑ n ∈ d.nRange, d.β n * χ₃ n * (n : ℂ) ^ ((τ : ℂ) * Complex.I))‖ ^ 2 := by
    intro τ
    unfold markedPoly unmarkedPoly Data.X
    rw [mul_mul_mul_comm, norm_mul, mul_pow, ← mul_inv, ← Complex.ofReal_mul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp_rw [hprod]
  rw [intervalIntegral.integral_const_mul]
  -- the length `N = N₁ N₂` has `1 ≤ N ≤ 4X` and `1 + log N ≤ 3L`
  have hN₁ : (N₁ : ℝ) ≤ 2 * d.Hm := Nat.floor_le (by linarith)
  have hN₂ : (N₂ : ℝ) ≤ 2 * d.Hn := Nat.floor_le (by linarith)
  have hN₁' : 1 ≤ N₁ := Nat.le_floor (by push_cast; linarith)
  have hN₂' : 1 ≤ N₂ := Nat.le_floor (by push_cast; linarith)
  have hN : ((N₁ * N₂ : ℕ) : ℝ) ≤ 4 * d.X := by
    push_cast
    unfold Data.X
    calc (N₁ : ℝ) * N₂ ≤ (2 * d.Hm) * (2 * d.Hn) :=
          mul_le_mul hN₁ hN₂ (Nat.cast_nonneg _) (by linarith)
      _ = 4 * (d.Hm * d.Hn) := by ring
  have hN1 : (1 : ℝ) ≤ ((N₁ * N₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hlogN0 : 0 ≤ Real.log ((N₁ * N₂ : ℕ) : ℝ) := Real.log_nonneg hN1
  have hlogN : 1 + Real.log ((N₁ * N₂ : ℕ) : ℝ) ≤ 3 * L := by
    have := Real.log_le_log (by linarith) hN
    linarith
  -- `L^B, L ≤ L^{B + 1}`
  have hLB : L ^ B ≤ L ^ (B + 1) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hL1 : L ≤ L ^ (B + 1) := by
    conv_lhs => rw [← Real.rpow_one L]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h₁ : T - -T + 8 * ((N₁ * N₂ : ℕ) : ℝ) * (1 + Real.log ((N₁ * N₂ : ℕ) : ℝ)) ≤
      98 * d.X * L ^ (B + 1) := by
    have h : 8 * ((N₁ * N₂ : ℕ) : ℝ) * (1 + Real.log ((N₁ * N₂ : ℕ) : ℝ)) ≤
        8 * (4 * d.X) * (3 * L) := by gcongr
    have h' : d.X * L ^ B ≤ d.X * L ^ (B + 1) := mul_le_mul_of_nonneg_left hLB hX.le
    have h'' : d.X * L ≤ d.X * L ^ (B + 1) := mul_le_mul_of_nonneg_left hL1 hX.le
    simp only [T] at h' ⊢
    linarith
  have h₂ : (L ^ C) ^ 2 * (L ^ C) ^ 2 *
      (((N₁ * N₂ : ℕ) : ℝ) * (1 + Real.log ((N₁ * N₂ : ℕ) : ℝ)) ^ 3) ≤
      L ^ (4 * C) * (108 * d.X * L ^ 3) := by
    have e : (L ^ C) ^ 2 * (L ^ C) ^ 2 = L ^ (4 * C) := by
      rw [← pow_add, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      norm_num
      ring_nf
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ((N₁ * N₂ : ℕ) : ℝ) * (1 + Real.log ((N₁ * N₂ : ℕ) : ℝ)) ^ 3
        ≤ (4 * d.X) * (3 * L) ^ 3 := by gcongr
      _ = 108 * d.X * L ^ 3 := by ring
  calc d.X⁻¹ ^ 2 * ∫ τ in -T..T, ‖(∑ m ∈ d.mRange, d.α m * χ₂ m *
          (m : ℂ) ^ ((τ : ℂ) * Complex.I)) *
        (∑ n ∈ d.nRange, d.β n * χ₃ n * (n : ℂ) ^ ((τ : ℂ) * Complex.I))‖ ^ 2
      ≤ d.X⁻¹ ^ 2 * ((98 * d.X * L ^ (B + 1)) * (L ^ (4 * C) * (108 * d.X * L ^ 3))) := by
        gcongr
        refine hmean.trans ?_
        exact mul_le_mul h₁ h₂ (by positivity) (by positivity)
    _ = 10584 * (L ^ (B + 1) * L ^ (4 * C) * L ^ (3 : ℝ)) := by
        rw [show (L ^ 3 : ℝ) = L ^ (3 : ℝ) by norm_cast]
        field_simp
        ring
    _ = 10584 * L ^ (meanExp C + B) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, meanExp]
        ring_nf

/-- `M_α` is continuous in `τ`. -/
theorem continuous_markedPoly {d : Data K} (hHm : 0 < d.Hm) {k : ℕ}
    (χ : DirichletCharacter ℂ k) : Continuous (markedPoly d χ) := by
  unfold markedPoly
  refine continuous_const.mul (continuous_finsetSum _ fun m hm => ?_)
  have h : 0 < m := lt_of_lt_of_le (Nat.ceil_pos.2 hHm) (mem_Icc.1 hm).1
  exact continuous_const.mul (continuous_natCast_cpow_mul_I h.ne')

/-! ### The energy -/

/-- `eventually_energy_le` with at least one band. Split the first band into the dyads
`[P₀ 2^r, P₀ 2^{r + 1})`, `P₀ = exp(L^{a₀})`, `r ≤ R = ⌊L^{a₀} / log 2⌋`, so
`|B_λ M_α N_β|² ≤ (R + 1) ∑_r |B_λ^{(r)} M_α N_β|²`. For each dyad,
`|B_λ^{(r)}| ≤ 8 ∫ |g(ξ)| |P_s(·; ξ)| dξ` (`norm_dyadPoly_le`), so by
`integral_sq_le_of_le_integral` its energy is at most `64 (∫ |g|)² sup_ξ ∫ |P_s M_α N_β|²`,
and the isolated energy is `O(L^{-A''})`. With `R + 1 ≤ 3L` and `∫ |g| ≤ 9 |C_g| L^{2A₀}`,
the total is `O(L^{2 + 4A₀ - A''}) = O(L^{-A' - 2})`. -/
private theorem eventually_energy_le_succ {C CX alo ahi Dstar g c₄ cG : ℝ} (hC : 0 < C)
    (hD : 0 < Dstar) (hCX : 1 ≤ CX) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data (K + 1), Admissible C CX alo ahi g x d →
      TwistBound (arcExp Dstar C) (freqExp Dstar C) (twistExp Dstar C) c₄ x d →
      KernelBound (freqExp Dstar C) cG x d →
      ∀ (j : ℕ) (lam : ℝ), |lam| ≤ 2 * Real.log x ^ arcExp Dstar C →
      ∀ (k : ℕ), 1 ≤ k → (k : ℝ) ≤ Real.log x ^ arcExp Dstar C →
      ∀ χ₁ χ₂ χ₃ : DirichletCharacter ℂ k,
        ∫ τ in (-(d.X * Real.log x ^ freqExp Dstar C))..(d.X * Real.log x ^ freqExp Dstar C),
            ‖labelPoly x d (2 ^ j) lam χ₁ τ * markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ‖ ^ 2 ≤
          C₀ * Real.log x ^ (-energyExp Dstar C) := by
  obtain ⟨Cg, hCg⟩ := exists_bumpTwist_mellin
  obtain ⟨Ci, hCi⟩ := eventually_integral_isolated_le (K := K + 1) (C := C) (CX := CX)
    (g := g) (B := freqExp Dstar C) (As := sparseExp Dstar C) (cG := cG) halo hahi
  refine ⟨46656 * Cg ^ 2 * (10584 + 4 * c₄ ^ 2 * |Ci|), ?_⟩
  filter_upwards [hCi, eventually_harmonicMass_band halo.le,
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (Real.log (4 * CX))),
    eventually_ge_atTop 1] with x hCi hV hLx hx d hd hP4 hG j lam hlam k hk1 hkL χ₁ χ₂ χ₃
  set L := Real.log x
  set A₀ := arcExp Dstar C
  set B := freqExp Dstar C
  set T := d.X * L ^ B
  set Y : ℝ := 2 ^ j
  set M := markedPoly d χ₂
  set N := unmarkedPoly d χ₃
  have hL : 1 ≤ L := le_of_max_le_left hLx
  have hL0 : 0 < L := by linarith
  have hY : 0 < Y := by positivity
  -- the exponents are nonnegative
  have hA₀ : 0 ≤ A₀ := by
    simp only [A₀, arcExp, edgePrec, momentPrec, squarePrec]
    linarith
  have hB : 0 ≤ B := by
    simp only [B, freqExp, majorPrec, meanExp, squarePrec, arcExp, edgePrec, momentPrec]
    linarith
  -- the scales
  have hγ : 0 ≤ d.γ := (Real.rpow_nonneg hL0.le _).trans hd.γ_ge
  have hHm : 1 ≤ d.Hm := (Real.one_le_rpow hx hγ).trans hd.Hm_ge
  have hHn : 1 ≤ d.Hn := (Real.one_le_rpow hx hγ).trans hd.Hn_ge
  have hX : 0 < d.X := mul_pos (by linarith) (by linarith)
  have hT : 0 ≤ T := by positivity
  have hT2 : T ≤ 2 * d.X * L ^ B := by
    have h : 0 ≤ d.X * L ^ B := hT
    rw [mul_assoc]
    linarith
  have hlog : Real.log (4 * d.X) ≤ 2 * L := by
    have h₁ : 4 * d.X ≤ (4 * CX) * x := by
      have := hd.X_le
      unfold Data.X
      linarith
    have h₂ := Real.log_le_log (by positivity) h₁
    rw [Real.log_mul (x := 4 * CX) (y := x) (by positivity) (by linarith)] at h₂
    linarith [le_of_max_le_right hLx]
  have hV' : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) := fun i =>
    (hV (d.a i) (hd.window i).1).1
  -- `M_α` and `N_β`: continuity, the bound P4, a crude bound and the mean value
  have hMc : Continuous M := continuous_markedPoly (by linarith) χ₂
  have hNc : Continuous N := continuous_unmarkedPoly (by linarith) χ₃
  have hMε : ∀ τ, |τ| ≤ T → ‖M τ‖ ≤ c₄ * L ^ (-twistExp Dstar C) := fun τ hτ =>
    hP4 k hk1 hkL χ₂ τ (hτ.trans hT2)
  set Mb := ‖((d.Hm : ℂ))⁻¹‖ * (∑ m ∈ d.mRange, ‖d.α m * χ₂ m‖) *
    (‖((d.Hn : ℂ))⁻¹‖ * ∑ n ∈ d.nRange, ‖d.β n * χ₃ n‖)
  have hMb : ∀ τ, ‖M τ * N τ‖ ≤ Mb := by
    intro τ
    have hm : ∀ m ∈ d.mRange, m ≠ 0 := fun m hm =>
      (lt_of_lt_of_le (Nat.ceil_pos.2 (by linarith)) (mem_Icc.1 hm).1).ne'
    have hn : ∀ n ∈ d.nRange, n ≠ 0 := fun n hn =>
      (lt_of_lt_of_le (Nat.ceil_pos.2 (by linarith)) (mem_Icc.1 hn).1).ne'
    simp only [M, N, markedPoly, unmarkedPoly, norm_mul (_ * _), norm_mul ((d.Hm : ℂ)⁻¹),
      norm_mul ((d.Hn : ℂ)⁻¹)]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (norm_sum_mul_natCast_cpow_le hm _ τ) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (norm_sum_mul_natCast_cpow_le hn _ τ) (norm_nonneg _))
      (by positivity) (by positivity)
  have hmean := integral_norm_markedPoly_mul_sq_le hd hx hL hB hlog χ₂ χ₃
  -- the Mellin transform of `η(y) e(-λ y)`: `∫ |g| ≤ 9 |C_g| L^{2A₀}`
  obtain ⟨gm, hgi, hgn, hgm⟩ := hCg lam
  set Wg := ∫ ξ, ‖gm ξ‖
  have hWg0 : 0 ≤ Wg := integral_nonneg fun _ => norm_nonneg _
  have hWg : Wg ≤ |Cg| * (9 * L ^ (2 * A₀)) := by
    have hLA : 1 ≤ L ^ A₀ := Real.one_le_rpow hL hA₀
    have h₁ : (1 + |lam|) ^ 2 ≤ 9 * L ^ (2 * A₀) := by
      have e : L ^ (2 * A₀) = (L ^ A₀) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
        ring_nf
      rw [e]
      calc (1 + |lam|) ^ 2 ≤ (3 * L ^ A₀) ^ 2 := by
            gcongr
            linarith
        _ = 9 * (L ^ A₀) ^ 2 := by ring
    calc Wg ≤ Cg * (1 + |lam|) ^ 2 := hgn
      _ ≤ |Cg| * (1 + |lam|) ^ 2 := by gcongr; exact le_abs_self Cg
      _ ≤ |Cg| * (9 * L ^ (2 * A₀)) := by gcongr
  -- the dyads `[P₀ 2^r, P₀ 2^{r + 1})` of the first band
  set a₀ := d.a 0
  set P₀ := Real.exp (L ^ a₀)
  set R := ⌊L ^ a₀ / Real.log 2⌋₊
  set ρ : ℕ → ℕ := fun q => ⌊Real.logb 2 (q / P₀)⌋₊
  set PS : ℕ → Finset ℕ := fun r => (band x a₀).filter fun q => ρ q = r
  have ha₀ : alo ≤ a₀ ∧ a₀ ≤ ahi := hd.window 0
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hP₀ : 0 < P₀ := Real.exp_pos _
  have hLa : 0 ≤ L ^ a₀ := Real.rpow_nonneg hL0.le _
  have hR : (R : ℝ) * Real.log 2 ≤ L ^ a₀ :=
    (le_div_iff₀ hlog2).1 (Nat.floor_le (div_nonneg hLa hlog2.le))
  have hPS : ∀ r, ∀ q ∈ PS r, q.Prime ∧ P₀ * 2 ^ r ≤ q ∧ (q : ℝ) < 2 * (P₀ * 2 ^ r) := by
    intro r q hq
    simp only [PS, mem_filter] at hq
    obtain ⟨hqb, hqr⟩ := hq
    have hq₁ : P₀ ≤ q := exp_le_of_mem_band hqb
    have hqP : 1 ≤ (q : ℝ) / P₀ := (one_le_div hP₀).2 hq₁
    have hqP0 : 0 < (q : ℝ) / P₀ := by linarith
    have hl0 : 0 ≤ Real.logb 2 ((q : ℝ) / P₀) := Real.logb_nonneg one_lt_two hqP
    have h₁ : (r : ℝ) ≤ Real.logb 2 ((q : ℝ) / P₀) := by
      rw [← hqr]
      exact Nat.floor_le hl0
    have h₂ : Real.logb 2 ((q : ℝ) / P₀) < r + 1 := by
      rw [← hqr]
      exact Nat.lt_floor_add_one _
    rw [Real.le_logb_iff_rpow_le one_lt_two hqP0, Real.rpow_natCast, le_div_iff₀ hP₀] at h₁
    rw [Real.logb_lt_iff_lt_rpow one_lt_two hqP0, div_lt_iff₀ hP₀, Real.rpow_add two_pos,
      Real.rpow_natCast, Real.rpow_one] at h₂
    exact ⟨TypeII.band_prime hqb, by linarith, by linarith⟩
  have hmaps : ∀ q ∈ band x a₀, ρ q ∈ range (R + 1) := by
    intro q hq
    rw [mem_range, Nat.lt_succ_iff]
    have hq₁ : P₀ ≤ q := exp_le_of_mem_band hq
    have hq₂ : (q : ℝ) ≤ Real.exp (2 * L ^ a₀) := le_exp_of_mem_band hq
    have hqP0 : 0 < (q : ℝ) / P₀ := div_pos (by linarith) hP₀
    have h : (q : ℝ) / P₀ ≤ Real.exp (L ^ a₀) := by
      rw [div_le_iff₀ hP₀, ← Real.exp_add]
      convert hq₂ using 2
      ring
    refine Nat.floor_le_floor ?_
    rw [Real.logb]
    refine div_le_div_of_nonneg_right ?_ hlog2.le
    calc Real.log ((q : ℝ) / P₀) ≤ Real.log (Real.exp (L ^ a₀)) := Real.log_le_log hqP0 h
      _ = L ^ a₀ := Real.log_exp _
  have hPr₁ : ∀ r : ℕ, Real.exp (L ^ alo) ≤ P₀ * 2 ^ r := fun r =>
    (Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL ha₀.1)).trans
      (le_mul_of_one_le_right hP₀.le (one_le_pow₀ one_le_two))
  have hPr₂ : ∀ r ∈ range (R + 1), P₀ * 2 ^ r ≤ Real.exp (2 * L ^ ahi) := by
    intro r hr
    have hr' : r ≤ R := Nat.lt_succ_iff.1 (mem_range.1 hr)
    have h₁ : (2 : ℝ) ^ r ≤ Real.exp (L ^ a₀) :=
      calc (2 : ℝ) ^ r ≤ 2 ^ R := pow_le_pow_right₀ one_le_two hr'
        _ = Real.exp (R * Real.log 2) := by rw [Real.exp_nat_mul, Real.exp_log two_pos]
        _ ≤ Real.exp (L ^ a₀) := Real.exp_le_exp.2 hR
    have h₂ : L ^ a₀ ≤ L ^ ahi := Real.rpow_le_rpow_of_exponent_le hL ha₀.2
    calc P₀ * 2 ^ r ≤ P₀ * Real.exp (L ^ a₀) := mul_le_mul_of_nonneg_left h₁ hP₀.le
      _ = Real.exp (2 * L ^ a₀) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (2 * L ^ ahi) := Real.exp_le_exp.2 (by linarith)
  have hR3 : (R : ℝ) + 1 ≤ 3 * L := by
    have h₁ : L ^ a₀ ≤ L := by
      conv_rhs => rw [← Real.rpow_one L]
      exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    have h₂ : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h₃ : (R : ℝ) * (1 / 2) ≤ R * Real.log 2 :=
      mul_le_mul_of_nonneg_left h₂.le (Nat.cast_nonneg _)
    linarith
  -- `B_λ` is the sum of its dyad pieces
  have hdecomp : ∀ τ, labelPoly x d Y lam χ₁ τ =
      ∑ r ∈ range (R + 1), dyadPoly x d Y lam χ₁ (PS r) τ := by
    intro τ
    have h : labelPoly x d Y lam χ₁ τ =
        (Y : ℂ)⁻¹ * ∑ p ∈ d.labels x, labelTerm x d Y lam χ₁ τ (∏ i, p i) := rfl
    rw [h, sum_labels_succ, ← sum_fiberwise_of_maps_to hmaps, mul_sum]
    rfl
  -- the isolated energy is at most `E = (10584 + 4 c₄² |C_i|) L^{-A''}`
  set Eiso := (10584 + 4 * c₄ ^ 2 * |Ci|) * L ^ (-isolatedExp Dstar C)
  have hiso : ∀ r ∈ range (R + 1), ∀ ξ, ∫ τ in (-T)..T,
      (‖primePoly (P₀ * 2 ^ r) (PS r) χ₁ ξ τ‖ * ‖M τ * N τ‖) ^ 2 ≤ Eiso := by
    intro r hr ξ
    refine (hCi d hd hG (P₀ * 2 ^ r) (hPr₁ r) (hPr₂ r hr) (PS r) (hPS r) k χ₁ χ₃ ξ M hMc T
      (c₄ * L ^ (-twistExp Dstar C)) (10584 * L ^ (meanExp C + B)) hT hT2 hMε hmean).trans ?_
    have e₁ : L ^ (-(2 * sparseExp Dstar C)) * L ^ (meanExp C + B) =
        L ^ (-isolatedExp Dstar C - 2) := by
      rw [← Real.rpow_add hL0]
      congr 1
      simp only [sparseExp, B]
      ring
    have e₂ : (L ^ (-twistExp Dstar C)) ^ 2 * L ^ (2 * C + 1) =
        L ^ (-isolatedExp Dstar C - 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
      congr 1
      simp only [twistExp]
      push_cast
      ring
    have h₂ : L ^ (-isolatedExp Dstar C - 2) ≤ L ^ (-isolatedExp Dstar C) :=
      Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    have h₃ : L ^ (-isolatedExp Dstar C - 3) ≤ L ^ (-isolatedExp Dstar C) :=
      Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    have h₄ : 0 ≤ L ^ (-isolatedExp Dstar C - 3) := Real.rpow_nonneg hL0.le _
    calc L ^ (-(2 * sparseExp Dstar C)) * (10584 * L ^ (meanExp C + B)) +
          4 * (c₄ * L ^ (-twistExp Dstar C)) ^ 2 * (Ci * L ^ (2 * C + 1))
        = 10584 * (L ^ (-(2 * sparseExp Dstar C)) * L ^ (meanExp C + B)) +
            4 * c₄ ^ 2 * (Ci * ((L ^ (-twistExp Dstar C)) ^ 2 * L ^ (2 * C + 1))) := by ring
      _ = 10584 * L ^ (-isolatedExp Dstar C - 2) +
            4 * c₄ ^ 2 * (Ci * L ^ (-isolatedExp Dstar C - 3)) := by rw [e₁, e₂]
      _ ≤ 10584 * L ^ (-isolatedExp Dstar C) +
            4 * c₄ ^ 2 * (|Ci| * L ^ (-isolatedExp Dstar C)) :=
          add_le_add (mul_le_mul_of_nonneg_left h₂ (by norm_num))
            (mul_le_mul_of_nonneg_left (mul_le_mul (le_abs_self Ci) h₃ h₄ (abs_nonneg _))
              (by positivity))
      _ = Eiso := by ring
  -- the energy of one dyad is at most `64 (∫ |g|)² E`
  have hdyad : ∀ r ∈ range (R + 1), ∫ τ in (-T)..T,
      (‖dyadPoly x d Y lam χ₁ (PS r) τ‖ * ‖M τ * N τ‖) ^ 2 ≤ 8 ^ 2 * Wg ^ 2 * Eiso := by
    intro r hr
    have hP : 1 ≤ P₀ * 2 ^ r :=
      (Real.one_le_exp hLa).trans (le_mul_of_one_le_right hP₀.le (one_le_pow₀ one_le_two))
    have hPS0 : ∀ q ∈ PS r, q ≠ 0 := fun q hq => (hPS r q hq).1.ne_zero
    have hcont : Continuous (Function.uncurry fun ξ τ =>
        ‖primePoly (P₀ * 2 ^ r) (PS r) χ₁ ξ τ‖ * ‖M τ * N τ‖) := by
      have h₁ := continuous_primePoly (P := P₀ * 2 ^ r) hPS0 χ₁
      have h₂ : Continuous fun z : ℝ × ℝ => M z.2 * N z.2 :=
        (hMc.comp continuous_snd).mul (hNc.comp continuous_snd)
      have h₃ := h₁.norm.mul h₂.norm
      exact h₃
    refine integral_sq_le_of_le_integral (by linarith) hgi.norm (fun ξ => norm_nonneg _) hcont
      (fun ξ τ => by positivity) (M := 2 * Mb) (fun ξ τ => ?_) (hiso r hr)
      (fun τ => by positivity) (fun τ => ?_)
    · exact mul_le_mul (norm_primePoly_le_two hP (hPS r) χ₁ ξ τ) (hMb τ) (norm_nonneg _)
        zero_le_two
    · have h := norm_dyadPoly_le hY hP hV' (hPS r) hgi hgm χ₁ τ
      calc ‖dyadPoly x d Y lam χ₁ (PS r) τ‖ * ‖M τ * N τ‖
          ≤ (8 * ∫ ξ, ‖gm ξ‖ * ‖primePoly (P₀ * 2 ^ r) (PS r) χ₁ ξ τ‖) * ‖M τ * N τ‖ :=
            mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ = 8 * ∫ ξ, ‖gm ξ‖ * (‖primePoly (P₀ * 2 ^ r) (PS r) χ₁ ξ τ‖ * ‖M τ * N τ‖) := by
            rw [mul_assoc, ← integral_mul_const]
            congr 2
            ext ξ
            ring
  -- sum over the dyads
  have hDc : ∀ r ∈ range (R + 1), Continuous (dyadPoly x d Y lam χ₁ (PS r)) := fun r _ =>
    continuous_dyadPoly x d Y lam χ₁ fun q hq => (hPS r q hq).1.ne_zero
  have hMNc : Continuous fun τ => ‖M τ * N τ‖ := (hMc.mul hNc).norm
  have hpt : ∀ τ, ‖labelPoly x d Y lam χ₁ τ * M τ * N τ‖ ^ 2 ≤ (R + 1) *
      ∑ r ∈ range (R + 1), (‖dyadPoly x d Y lam χ₁ (PS r) τ‖ * ‖M τ * N τ‖) ^ 2 := by
    intro τ
    rw [mul_assoc, norm_mul, hdecomp τ]
    calc (‖∑ r ∈ range (R + 1), dyadPoly x d Y lam χ₁ (PS r) τ‖ * ‖M τ * N τ‖) ^ 2
        ≤ (∑ r ∈ range (R + 1), ‖dyadPoly x d Y lam χ₁ (PS r) τ‖ * ‖M τ * N τ‖) ^ 2 := by
          rw [← sum_mul]
          gcongr
          exact norm_sum_le _ _
      _ ≤ #(range (R + 1)) * ∑ r ∈ range (R + 1),
            (‖dyadPoly x d Y lam χ₁ (PS r) τ‖ * ‖M τ * N τ‖) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = (R + 1) * ∑ r ∈ range (R + 1),
            (‖dyadPoly x d Y lam χ₁ (PS r) τ‖ * ‖M τ * N τ‖) ^ 2 := by
          rw [card_range]
          push_cast
          ring
  have hLHS : Continuous fun τ => ‖labelPoly x d Y lam χ₁ τ * M τ * N τ‖ ^ 2 := by
    have e : (fun τ => labelPoly x d Y lam χ₁ τ) =
        fun τ => ∑ r ∈ range (R + 1), dyadPoly x d Y lam χ₁ (PS r) τ := funext hdecomp
    have h : Continuous fun τ => labelPoly x d Y lam χ₁ τ := by
      rw [e]
      exact continuous_finsetSum _ hDc
    exact ((h.mul hMc).mul hNc).norm.pow 2
  have hterm : ∀ r ∈ range (R + 1), Continuous fun τ =>
      (‖dyadPoly x d Y lam χ₁ (PS r) τ‖ * ‖M τ * N τ‖) ^ 2 := fun r hr =>
    ((hDc r hr).norm.mul hMNc).pow 2
  have hRHS : Continuous fun τ => ((R : ℝ) + 1) *
      ∑ r ∈ range (R + 1), (‖dyadPoly x d Y lam χ₁ (PS r) τ‖ * ‖M τ * N τ‖) ^ 2 :=
    continuous_const.mul (continuous_finsetSum _ hterm)
  have hpow : L ^ 2 * (L ^ (2 * A₀)) ^ 2 * L ^ (-isolatedExp Dstar C) ≤
      L ^ (-energyExp Dstar C) := by
    rw [← Real.rpow_natCast (L ^ (2 * A₀)) 2, ← Real.rpow_mul hL0.le, ← Real.rpow_natCast L 2,
      ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    apply Real.rpow_le_rpow_of_exponent_le hL
    simp only [isolatedExp, A₀]
    push_cast
    linarith
  calc ∫ τ in (-T)..T, ‖labelPoly x d Y lam χ₁ τ * M τ * N τ‖ ^ 2
      ≤ ∫ τ in (-T)..T, ((R : ℝ) + 1) *
          ∑ r ∈ range (R + 1), (‖dyadPoly x d Y lam χ₁ (PS r) τ‖ * ‖M τ * N τ‖) ^ 2 :=
        intervalIntegral.integral_mono_on (by linarith) (hLHS.intervalIntegrable _ _)
          (hRHS.intervalIntegrable _ _) fun τ _ => hpt τ
    _ = ((R : ℝ) + 1) * ∑ r ∈ range (R + 1), ∫ τ in (-T)..T,
          (‖dyadPoly x d Y lam χ₁ (PS r) τ‖ * ‖M τ * N τ‖) ^ 2 := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
          fun r hr => (hterm r hr).intervalIntegrable _ _]
    _ ≤ ((R : ℝ) + 1) * ∑ r ∈ range (R + 1), 8 ^ 2 * Wg ^ 2 * Eiso := by
        gcongr with r hr
        exact hdyad r hr
    _ = ((R : ℝ) + 1) ^ 2 * (64 * Wg ^ 2 * Eiso) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (3 * L) ^ 2 * (64 * (|Cg| * (9 * L ^ (2 * A₀))) ^ 2 * Eiso) := by gcongr
    _ = 46656 * Cg ^ 2 * (10584 + 4 * c₄ ^ 2 * |Ci|) *
          (L ^ 2 * (L ^ (2 * A₀)) ^ 2 * L ^ (-isolatedExp Dstar C)) := by
        rw [mul_pow |Cg|, sq_abs]
        ring
    _ ≤ 46656 * Cg ^ 2 * (10584 + 4 * c₄ ^ 2 * |Ci|) * L ^ (-energyExp Dstar C) := by
        gcongr

/-- The energy bound: under P4 and (G), for `|λ| ≤ 2L^{A₀}` and characters of modulus at most
`L^{A₀}`, `∫_{|τ| ≤ XL^B} |B_λ M_α N_β|² ≤ C₀ L^{-A'}`. -/
theorem eventually_energy_le {C CX alo ahi Dstar g c₄ cG : ℝ} (hC : 0 < C) (hD : 0 < Dstar)
    (hCX : 1 ≤ CX) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      TwistBound (arcExp Dstar C) (freqExp Dstar C) (twistExp Dstar C) c₄ x d →
      KernelBound (freqExp Dstar C) cG x d →
      ∀ (j : ℕ) (lam : ℝ), |lam| ≤ 2 * Real.log x ^ arcExp Dstar C →
      ∀ (k : ℕ), 1 ≤ k → (k : ℝ) ≤ Real.log x ^ arcExp Dstar C →
      ∀ χ₁ χ₂ χ₃ : DirichletCharacter ℂ k,
        ∫ τ in (-(d.X * Real.log x ^ freqExp Dstar C))..(d.X * Real.log x ^ freqExp Dstar C),
            ‖labelPoly x d (2 ^ j) lam χ₁ τ * markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ‖ ^ 2 ≤
          C₀ * Real.log x ^ (-energyExp Dstar C) := by
  cases K with
  | zero =>
    -- with no bands the only label product is `1 ≤ Y`, where `η` vanishes
    refine ⟨0, Eventually.of_forall fun x d _ _ _ j lam _ k _ _ χ₁ χ₂ χ₃ => ?_⟩
    have hη : dyadicBump (1 / (2 : ℝ) ^ j) = 0 := by
      have h : (1 : ℝ) / 2 ^ j ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ one_le_two) (by positivity)
      unfold dyadicBump
      rw [smoothTransition.zero_of_nonpos (by linarith),
        smoothTransition.zero_of_nonpos (by linarith), sub_zero]
    have h : ∀ τ, labelPoly x d (2 ^ j) lam χ₁ τ = 0 := by
      intro τ
      unfold labelPoly
      rw [sum_eq_zero fun p _ => ?_, mul_zero]
      simp only [Fin.prod_univ_zero, Nat.cast_one, hη, zero_mul, Complex.ofReal_zero]
    simp [h]
  | succ K => exact eventually_energy_le_succ hC hD hCX halo hahi

end Erdos408.OneSided
