module

public import Erdos408.OneSided.Major.Characters
public import Erdos408.OneSided.Major.Energy
public import Erdos408.OneSided.Major.Mellin

/-!
# The major sum arc by arc

`blueprint/one_sided_type_ii.md` §6.3 steps 1–2 and §6.4. Write the major sum over pairs of
sides `u = (p', m, n)` and `v = (p, r, s)`. A side has the label product `a_u = ∏ p'_i`, the
product `N_u = a_u m n` and the coefficient `c_u = η(a_u/Y) ∏ V_i⁻¹ α_m β_n`.

* `majorSquare_eq_sum_arcs`: interchange the arcs `h/k + θ` with the sums, so that `Q_Y^maj`
  is `∑_{k, h} ∫_{|θ| ≤ 2L^{A₀}/Y}` of
  `∑_{v, u} c_u \bar c_v ψ((N_u - N_v)/Y) e((h/k + θ)(N_u - N_v - a_u + a_v))`.
* `arcTerm_eq_integral`: at `θ = λ/Y` the phase is
  `ψ_λ(X(w_u - w_v)) φ_u \bar φ_v / (c_u \bar c_v)`, where `w_u = N_u/(XY) ∈ [1, 16]` and
  `φ_u = c_u e(-λ a_u/Y) e(h(N_u - a_u)/k)`. Separating `ψ_λ` with the kernel `K` of
  `exists_plateauTwist_separation` gives `∫ K(q) G(q₁) \bar G(-q₂) dq` with
  `G(τ) = ∑_u φ_u w_u^{iτ}`.
* `norm_sidePoly_le`: the phase `e(h(a m n - a)/k)` is a function of the units `a, m, n`
  modulo `k`, so it expands into products of three characters with coefficients of modulus at
  most one. Hence `|G(τ)| ≤ XY ∑_χ |B_λ^{χ₁} M^{χ₂} N^{χ₃}(τ)|`.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open MeasureTheory Finset Real

variable {K : ℕ}

/-! ### Sides and arcs -/

/-- The sides `(p, m, n)` of the major sum: a label tuple and a pair in the ranges. -/
def sideSet (x : ℝ) (d : Data K) : Finset ((Fin K → ℕ) × ℕ × ℕ) :=
  d.labels x ×ˢ (d.mRange ×ˢ d.nRange)

/-- The label product `∏ p_i` of a side. -/
def sideLabel (u : (Fin K → ℕ) × ℕ × ℕ) : ℕ := ∏ i, u.1 i

/-- The product `(∏ p_i) m n` of a side. -/
def sideProd (u : (Fin K → ℕ) × ℕ × ℕ) : ℕ := sideLabel u * u.2.1 * u.2.2

/-- The coefficient `η(a/Y) ∏ V_i⁻¹ α_m β_n` of a side, `a = ∏ p_i`. -/
def sideCoeff (x : ℝ) (d : Data K) (Y : ℝ) (u : (Fin K → ℕ) × ℕ × ℕ) : ℂ :=
  ((dyadicBump (sideLabel u / Y) * (d.bandMass x)⁻¹ : ℝ) : ℂ) * d.α u.2.1 * d.β u.2.2

/-- The arcs `h/k`: `1 ≤ k ≤ L^{A₀}`, `0 ≤ h < k` and `(h, k) = 1`. -/
def arcSet (A₀ x : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (Icc 1 ⌊Real.log x ^ A₀⌋₊).sigma fun k => (range k).filter fun h => Nat.Coprime h k

/-- The integrand of the major sum at the arc `h/k` and the shift `θ`:
`∑_{v, u} c_u \bar c_v ψ((N_u - N_v)/Y) e((h/k + θ)(N_u - N_v - a_u + a_v))`. -/
def arcTerm (x : ℝ) (d : Data K) (Y : ℝ) (k h : ℕ) (θ : ℝ) : ℂ :=
  ∑ v ∈ sideSet x d, ∑ u ∈ sideSet x d, sideCoeff x d Y u * star (sideCoeff x d Y v) *
    ((plateau ((((sideProd u : ℤ) - sideProd v : ℤ) : ℝ) / Y) : ℂ) *
      Complex.exp (2 * π * Complex.I * ((((h : ℝ) / k + θ) *
        ((((sideProd u : ℤ) - sideProd v) - sideLabel u + sideLabel v : ℤ) : ℝ) : ℝ) : ℂ)))

/-- The phase `e(h(abc - a)/k)` on `(ℤ/k)³`. -/
def arcPhase (k h : ℕ) [NeZero k] (A B C : ZMod k) : ℂ :=
  (ZMod.toCircle ((h : ZMod k) * (A * B * C - A)) : ℂ)

/-- The separated coefficient `φ_u = c_u e(-λ a/Y) e(h(a m n - a)/k)` of a side. -/
def sidePhase (x : ℝ) (d : Data K) (Y lam : ℝ) (k h : ℕ) [NeZero k]
    (u : (Fin K → ℕ) × ℕ × ℕ) : ℂ :=
  sideCoeff x d Y u * Complex.exp (-(2 * π * Complex.I * ((lam * sideLabel u / Y : ℝ) : ℂ))) *
    arcPhase k h (sideLabel u) u.2.1 u.2.2

/-- The separated polynomial `G(τ) = ∑_u φ_u (N_u/(XY))^{iτ}`. -/
def sidePoly (x : ℝ) (d : Data K) (Y lam : ℝ) (k h : ℕ) [NeZero k] (τ : ℝ) : ℂ :=
  ∑ u ∈ sideSet x d, sidePhase x d Y lam k h u *
    ((sideProd u / (d.X * Y) : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)

/-! ### The major sum as a sum over arcs -/

/-- The major sum over pairs of sides, the `v` side outside. -/
theorem majorSquare_eq_sum_side (A₀ x : ℝ) (d : Data K) (Y : ℝ) :
    majorSquare A₀ x d Y = ∑ v ∈ sideSet x d, ∑ u ∈ sideSet x d,
      sideCoeff x d Y u * star (sideCoeff x d Y v) *
        majorWeight A₀ x Y ((sideProd u : ℤ) - sideProd v) (sideLabel v) (sideLabel u) := by
  unfold majorSquare
  rw [Finset.mul_sum, sideSet, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  -- bring the `u` side outside the pair `(r, s)` of the `v` side
  conv_rhs => rw [Finset.sum_comm]
  simp only [Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun m _ =>
    Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun s _ => ?_
  simp only [sideCoeff, sideProd, sideLabel, star_mul', Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- Finite sums commute with the arcs and the integral over `θ`. -/
private theorem sum_sum_mul_sum_integral {ι κ : Type*} (S : Finset ι) (P : Finset κ)
    (c : ι → ι → ℂ) (f : ι → ι → κ → ℝ → ℂ) (hf : ∀ u v kh, Continuous (f u v kh)) (a b : ℝ) :
    ∑ v ∈ S, ∑ u ∈ S, c u v * ∑ kh ∈ P, ∫ θ in a..b, f u v kh θ =
      ∑ kh ∈ P, ∫ θ in a..b, ∑ v ∈ S, ∑ u ∈ S, c u v * f u v kh θ := by
  calc ∑ v ∈ S, ∑ u ∈ S, c u v * ∑ kh ∈ P, ∫ θ in a..b, f u v kh θ
      = ∑ v ∈ S, ∑ u ∈ S, ∑ kh ∈ P, ∫ θ in a..b, c u v * f u v kh θ := by
        simp_rw [Finset.mul_sum, intervalIntegral.integral_const_mul]
    _ = ∑ kh ∈ P, ∑ v ∈ S, ∑ u ∈ S, ∫ θ in a..b, c u v * f u v kh θ := by
        rw [Finset.sum_congr rfl fun v _ => Finset.sum_comm, Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun kh _ => ?_
        rw [intervalIntegral.integral_finsetSum fun v _ =>
          (continuous_finsetSum _ fun u _ => (hf u v kh).const_mul _).intervalIntegrable _ _]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [intervalIntegral.integral_finsetSum fun u _ =>
          ((hf u v kh).const_mul _).intervalIntegrable _ _]

/-- The major sum is `∑_{k, h} ∫_{|θ| ≤ 2L^{A₀}/Y}` of the arc term. -/
theorem majorSquare_eq_sum_arcs (A₀ x : ℝ) (d : Data K) (Y : ℝ) :
    majorSquare A₀ x d Y = ∑ kh ∈ arcSet A₀ x,
      ∫ θ in (-(2 * Real.log x ^ A₀ / Y))..(2 * Real.log x ^ A₀ / Y),
        arcTerm x d Y kh.1 kh.2 θ := by
  -- the major-arc kernel as a sum over arcs
  have hW : ∀ t a b : ℤ, majorWeight A₀ x Y t a b = ∑ kh ∈ arcSet A₀ x,
      ∫ θ in (-(2 * Real.log x ^ A₀ / Y))..(2 * Real.log x ^ A₀ / Y),
        (plateau (t / Y) : ℂ) * Complex.exp (2 * π * Complex.I *
          ((((kh.2 : ℝ) / kh.1 + θ) * ((t - b + a : ℤ) : ℝ) : ℝ) : ℂ)) := by
    intro t a b
    rw [majorWeight, arcIntegral, arcSet, Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← intervalIntegral.integral_const_mul]
  rw [majorSquare_eq_sum_side]
  simp only [hW]
  exact sum_sum_mul_sum_integral _ _ _ _ (fun u v kh => by fun_prop) _ _

/-! ### Separation of one arc term -/

/-- `|w^{iτ}| = 1` for `w > 0`. -/
private theorem norm_ofReal_cpow_mul_I {w : ℝ} (hw : 0 < w) (τ : ℝ) :
    ‖(w : ℂ) ^ ((τ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hw]
  simp

/-- `\overline{w^{-iτ}} = w^{iτ}` for `w > 0`. -/
private theorem star_ofReal_cpow_neg_mul_I {w : ℝ} (hw : 0 < w) (τ : ℝ) :
    star ((w : ℂ) ^ (((-τ : ℝ) : ℂ) * Complex.I)) = (w : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  have hw' : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
  rw [Complex.cpow_def_of_ne_zero hw', Complex.cpow_def_of_ne_zero hw', Complex.star_def,
    ← Complex.exp_conj, ← Complex.ofReal_log hw.le]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `t ↦ w^{iτ}` is continuous for `w > 0`. -/
private theorem continuous_ofReal_cpow_mul_I {w : ℝ} (hw : 0 < w) :
    Continuous fun τ : ℝ => (w : ℂ) ^ ((τ : ℂ) * Complex.I) :=
  (Complex.continuous_ofReal.mul continuous_const).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.2 hw.ne'))

/-- The phase at natural numbers: `e(h(a m n - a)/k)`. -/
private theorem arcPhase_natCast (k h : ℕ) [NeZero k] {a m n N : ℕ} (hN : a * m * n = N) :
    arcPhase k h a m n = Complex.exp (2 * π * Complex.I * ((h * ((N : ℤ) - a) : ℤ) : ℂ) / k) := by
  rw [arcPhase, ← ZMod.toCircle_intCast, ← hN]
  push_cast
  rfl

/-- The phase identity of one pair of sides: `φ_u \bar φ_v ψ_λ(X(w_u - w_v))` is
`c_u \bar c_v ψ((N_u - N_v)/Y) e((h/k + λ/Y)(N_u - N_v - a_u + a_v))`. -/
private theorem sidePhase_mul_star_mul_plateauTwist (x : ℝ) (d : Data K) {Y : ℝ} (hY : Y ≠ 0)
    (hX : d.X ≠ 0) (lam : ℝ) (k h : ℕ) [NeZero k] (u v : (Fin K → ℕ) × ℕ × ℕ) :
    sidePhase x d Y lam k h u * star (sidePhase x d Y lam k h v) *
        plateauTwist lam (d.X * ((sideProd u : ℝ) / (d.X * Y) - (sideProd v : ℝ) / (d.X * Y))) =
      sideCoeff x d Y u * star (sideCoeff x d Y v) *
        ((plateau ((((sideProd u : ℤ) - sideProd v : ℤ) : ℝ) / Y) : ℂ) *
          Complex.exp (2 * π * Complex.I * ((((h : ℝ) / k + lam / Y) *
            ((((sideProd u : ℤ) - sideProd v) - sideLabel u + sideLabel v : ℤ) : ℝ) : ℝ) :
              ℂ))) := by
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne k)
  have hY' : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hY
  have hy : d.X * ((sideProd u : ℝ) / (d.X * Y) - (sideProd v : ℝ) / (d.X * Y)) =
      (((sideProd u : ℤ) - sideProd v : ℤ) : ℝ) / Y := by
    push_cast
    field_simp
  unfold sidePhase plateauTwist
  rw [hy, arcPhase_natCast k h (N := sideProd u) rfl, arcPhase_natCast k h (N := sideProd v) rfl]
  -- the exponentials combine
  have key : Complex.exp (-(2 * π * Complex.I * ((lam * sideLabel u / Y : ℝ) : ℂ))) *
      star (Complex.exp (-(2 * π * Complex.I * ((lam * sideLabel v / Y : ℝ) : ℂ)))) *
      Complex.exp (2 * π * Complex.I * ((h * ((sideProd u : ℤ) - sideLabel u) : ℤ) : ℂ) / k) *
      star (Complex.exp (2 * π * Complex.I *
        ((h * ((sideProd v : ℤ) - sideLabel v) : ℤ) : ℂ) / k)) *
      Complex.exp (2 * π * Complex.I *
        ((lam * ((((sideProd u : ℤ) - sideProd v : ℤ) : ℝ) / Y) : ℝ) : ℂ)) =
      Complex.exp (2 * π * Complex.I * ((((h : ℝ) / k + lam / Y) *
        ((((sideProd u : ℤ) - sideProd v) - sideLabel u + sideLabel v : ℤ) : ℝ) : ℝ) : ℂ)) := by
    simp only [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_neg, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
      map_intCast, map_natCast]
    push_cast
    field_simp
    ring
  rw [star_mul', star_mul', ← key]
  ring

/-- One arc term, separated: at `θ = λ/Y` it is `∫ K(q) G(q₁) \bar G(-q₂) dq`, for any kernel
`K` separating `ψ_λ(X(w - w'))` on `[1, 16]²`. -/
theorem arcTerm_eq_integral {x Y : ℝ} {d : Data K} (hY : 0 < Y) (hX : 0 < d.X) (k h : ℕ)
    [NeZero k] (lam : ℝ) {Kf : ℝ × ℝ → ℂ} (hKi : Integrable Kf)
    (hK : ∀ w w' : ℝ, 1 ≤ w → w ≤ 16 → 1 ≤ w' → w' ≤ 16 →
      plateauTwist lam (d.X * (w - w')) =
        ∫ q : ℝ × ℝ, Kf q * (w : ℂ) ^ ((q.1 : ℂ) * Complex.I) *
          (w' : ℂ) ^ ((q.2 : ℂ) * Complex.I))
    (hsupp : ∀ u ∈ sideSet x d, sideCoeff x d Y u ≠ 0 →
      1 ≤ (sideProd u : ℝ) / (d.X * Y) ∧ (sideProd u : ℝ) / (d.X * Y) ≤ 16)
    (hpos : ∀ u ∈ sideSet x d, 0 < sideProd u) :
    arcTerm x d Y k h (lam / Y) =
      ∫ q : ℝ × ℝ, Kf q * (sidePoly x d Y lam k h q.1 * star (sidePoly x d Y lam k h (-q.2))) := by
  set w : (Fin K → ℕ) × ℕ × ℕ → ℝ := fun u => (sideProd u : ℝ) / (d.X * Y) with hw
  have hw0 : ∀ u ∈ sideSet x d, 0 < w u := fun u hu =>
    div_pos (Nat.cast_pos.2 (hpos u hu)) (mul_pos hX hY)
  set φ := sidePhase x d Y lam k h with hφ
  -- the integrand is a double sum over pairs of sides
  set F : (Fin K → ℕ) × ℕ × ℕ → (Fin K → ℕ) × ℕ × ℕ → ℝ × ℝ → ℂ := fun u v q =>
    Kf q * (φ u * (w u : ℂ) ^ ((q.1 : ℂ) * Complex.I) *
      (star (φ v) * (w v : ℂ) ^ ((q.2 : ℂ) * Complex.I))) with hF
  have hexp : ∀ q : ℝ × ℝ,
      Kf q * (sidePoly x d Y lam k h q.1 * star (sidePoly x d Y lam k h (-q.2))) =
        ∑ v ∈ sideSet x d, ∑ u ∈ sideSet x d, F u v q := by
    intro q
    simp only [sidePoly, star_sum, star_mul']
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [star_ofReal_cpow_neg_mul_I (w := (sideProd v : ℝ) / (d.X * Y)) (hw0 v hv)]
  have hFi : ∀ u ∈ sideSet x d, ∀ v ∈ sideSet x d, Integrable (F u v) := by
    intro u hu v hv
    refine hKi.mul_bdd (c := ‖φ u‖ * ‖φ v‖) ?_ (Filter.Eventually.of_forall fun q => ?_)
    · exact ((continuous_const.mul ((continuous_ofReal_cpow_mul_I (hw0 u hu)).comp
        continuous_fst)).mul (continuous_const.mul ((continuous_ofReal_cpow_mul_I
          (hw0 v hv)).comp continuous_snd))).aestronglyMeasurable
    · rw [norm_mul, norm_mul, norm_mul, norm_ofReal_cpow_mul_I (hw0 u hu),
        norm_ofReal_cpow_mul_I (hw0 v hv), norm_star, mul_one, mul_one]
  rw [show (fun q : ℝ × ℝ => Kf q * (sidePoly x d Y lam k h q.1 *
      star (sidePoly x d Y lam k h (-q.2)))) = fun q => ∑ v ∈ sideSet x d,
        ∑ u ∈ sideSet x d, F u v q from funext hexp,
    integral_finsetSum _ fun v hv => integrable_finsetSum _ fun u hu => hFi u hu v hv]
  unfold arcTerm
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [integral_finsetSum _ fun u hu => hFi u hu v hv]
  refine Finset.sum_congr rfl fun u hu => ?_
  -- pull out the coefficients, then separate `ψ_λ`
  have hFc : ∀ q, F u v q = φ u * star (φ v) *
      (Kf q * (w u : ℂ) ^ ((q.1 : ℂ) * Complex.I) * (w v : ℂ) ^ ((q.2 : ℂ) * Complex.I)) :=
    fun q => by simp only [hF]; ring
  simp only [hFc]
  rw [integral_const_mul]
  by_cases hc : sideCoeff x d Y u = 0 ∨ sideCoeff x d Y v = 0
  · have hφ0 : φ u * star (φ v) = 0 := by
      rcases hc with hc | hc
      · simp [hφ, sidePhase, hc]
      · simp [hφ, sidePhase, hc]
    have hc0 : sideCoeff x d Y u * star (sideCoeff x d Y v) = 0 := by
      rcases hc with hc | hc <;> simp [hc]
    rw [hφ0, hc0, zero_mul, zero_mul]
  · push Not at hc
    obtain ⟨hu₁, hu₂⟩ := hsupp u hu hc.1
    obtain ⟨hv₁, hv₂⟩ := hsupp v hv hc.2
    rw [← hK _ _ hu₁ hu₂ hv₁ hv₂, hφ,
      sidePhase_mul_star_mul_plateauTwist x d hY.ne' hX.ne' lam k h u v]

/-! ### The separated polynomial and characters -/

/-- `(a/b)^{iτ} = a^{iτ} (b^{iτ})⁻¹` for `a, b > 0`. -/
private theorem ofReal_div_cpow_mul_I {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (τ : ℝ) :
    ((a / b : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) =
      (a : ℂ) ^ ((τ : ℂ) * Complex.I) * ((b : ℂ) ^ ((τ : ℂ) * Complex.I))⁻¹ := by
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le (inv_nonneg.2 hb.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hb.le]; exact Real.pi_pos.ne)]

/-- With the characters in place of the phase, the sum over sides factors as
`(Y B_λ^{χ₁}) (H_m M^{χ₂}) (H_n N^{χ₃})`. -/
private theorem sum_side_eq_mul (x : ℝ) (d : Data K) {Y : ℝ} (hY : Y ≠ 0) (hHm : d.Hm ≠ 0)
    (hHn : d.Hn ≠ 0) (lam : ℝ) {k : ℕ} (χ₁ χ₂ χ₃ : DirichletCharacter ℂ k) (τ : ℝ) :
    ∑ u ∈ sideSet x d, sideCoeff x d Y u *
        Complex.exp (-(2 * π * Complex.I * ((lam * sideLabel u / Y : ℝ) : ℂ))) *
        (χ₁ (sideLabel u) * χ₂ u.2.1 * χ₃ u.2.2) *
        ((sideProd u : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I) =
      (Y : ℂ) * labelPoly x d Y lam χ₁ τ * ((d.Hm : ℂ) * markedPoly d χ₂ τ) *
        ((d.Hn : ℂ) * unmarkedPoly d χ₃ τ) := by
  simp only [labelPoly, markedPoly, unmarkedPoly]
  rw [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 hY),
    mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 hHm),
    mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 hHn), Finset.sum_mul_sum, Finset.sum_mul,
    sideSet, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  -- `(a m n)^{iτ} = a^{iτ} m^{iτ} n^{iτ}`
  simp only [sideCoeff, sideLabel, sideProd]
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  ring

/-- The separated polynomial is at most `XY ∑_χ |B_λ^{χ₁} M^{χ₂} N^{χ₃}|`, when the variables
of every side with `c_u ≠ 0` are units modulo `k`. -/
theorem norm_sidePoly_le {x Y : ℝ} {d : Data K} (hY : 0 < Y) (hHm : 0 < d.Hm) (hHn : 0 < d.Hn)
    (k h : ℕ) [NeZero k] (lam : ℝ)
    (hunit : ∀ u ∈ sideSet x d, sideCoeff x d Y u ≠ 0 →
      IsUnit (sideLabel u : ZMod k) ∧ IsUnit (u.2.1 : ZMod k) ∧ IsUnit (u.2.2 : ZMod k))
    (hpos : ∀ u ∈ sideSet x d, 0 < sideProd u) (τ : ℝ) :
    ‖sidePoly x d Y lam k h τ‖ ≤ d.X * Y *
      ∑ χ : DirichletCharacter ℂ k × DirichletCharacter ℂ k × DirichletCharacter ℂ k,
        ‖labelPoly x d Y lam χ.1 τ * markedPoly d χ.2.1 τ * unmarkedPoly d χ.2.2 τ‖ := by
  have hXY : 0 < d.X * Y := mul_pos (mul_pos hHm hHn) hY
  obtain ⟨c, hc, hexp⟩ := exists_dirichletCharacter_expansion (arcPhase k h)
    fun a b c' => by rw [arcPhase, Circle.norm_coe]
  set z : ℂ := (τ : ℂ) * Complex.I with hz
  -- factor out `(XY)^{-iτ}`
  have h₁ : sidePoly x d Y lam k h τ = (((d.X * Y : ℝ) : ℂ) ^ z)⁻¹ *
      ∑ u ∈ sideSet x d, sidePhase x d Y lam k h u * ((sideProd u : ℕ) : ℂ) ^ z := by
    rw [sidePoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [ofReal_div_cpow_mul_I (Nat.cast_pos.2 (hpos u hu)) hXY, Complex.ofReal_natCast]
    ring
  -- expand the phase into characters
  have h₂ : ∑ u ∈ sideSet x d, sidePhase x d Y lam k h u * ((sideProd u : ℕ) : ℂ) ^ z =
      ∑ χ : DirichletCharacter ℂ k × DirichletCharacter ℂ k × DirichletCharacter ℂ k,
        c χ.1 χ.2.1 χ.2.2 * ((Y : ℂ) * labelPoly x d Y lam χ.1 τ *
          ((d.Hm : ℂ) * markedPoly d χ.2.1 τ) * ((d.Hn : ℂ) * unmarkedPoly d χ.2.2 τ)) := by
    simp only [← sum_side_eq_mul x d hY.ne' hHm.ne' hHn.ne' lam, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [Fintype.sum_prod_type]
    by_cases hcu : sideCoeff x d Y u = 0
    · simp [sidePhase, hcu]
    obtain ⟨hu₁, hu₂, hu₃⟩ := hunit u hu hcu
    rw [sidePhase, hexp _ _ _ hu₁ hu₂ hu₃]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ₁ _ => Finset.sum_congr rfl fun χ₂ _ =>
      Finset.sum_congr rfl fun χ₃ _ => ?_
    ring
  rw [h₁, h₂, norm_mul, norm_inv, hz, norm_ofReal_cpow_mul_I hXY, inv_one, one_mul,
    Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
  -- `|c| ≤ 1` and `Y H_m H_n = XY`
  have hprod : (Y : ℂ) * labelPoly x d Y lam χ.1 τ * ((d.Hm : ℂ) * markedPoly d χ.2.1 τ) *
      ((d.Hn : ℂ) * unmarkedPoly d χ.2.2 τ) = ((d.X * Y : ℝ) : ℂ) *
        (labelPoly x d Y lam χ.1 τ * markedPoly d χ.2.1 τ * unmarkedPoly d χ.2.2 τ) := by
    unfold Data.X
    push_cast
    ring
  rw [norm_mul, hprod, norm_mul, Complex.norm_real, Real.norm_of_nonneg hXY.le]
  exact mul_le_of_le_one_left (by positivity) (hc _ _ _)

end Erdos408.OneSided
