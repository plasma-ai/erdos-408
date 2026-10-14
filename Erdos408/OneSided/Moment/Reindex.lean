module

public import Erdos408.OneSided.Moment.Lines
public import Erdos408.OneSided.RootResidue

/-!
# Reindexing the moment by integer roots

RR1 of `blueprint/one_sided_type_ii.md` §15. A physical position `P₀ = (u, v)` has the integer
root `g = (u c; v d)`, with `c = rootC u v` and `u d - v c = 1`, so `g(ϱ)` at the real root
`ϱ = (u, v, c/u)` is `g`. The map `z ↦ g z` identifies the root model at `ϱ` with lines
`ℓ_p = [(c, -u)]_p`, the kernel line of the first row modulo `p`, with the physical model:
`p ∣ (g z)₁ = u z₁ + c z₂` exactly when `[z]_p = ℓ_p`, and the ratios agree modulo `ℤ`. Hence
the determinant moment is the sum of the root moments at the integer roots.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

/-- The lines of the integer root of `P₀ = (u, v)`: `ℓ_p = [(c, -u)]_p`, `c = rootC u v`. -/
def rootLines (P₀ : ℕ × ℕ) (p : ℕ) : ℕ :=
  lineOf p ((rootC P₀.1 P₀.2 : ℤ), -(P₀.1 : ℤ))

namespace Reindex

open RootResidue

/-! ### The integer root -/

/-- `g z` for the integer root `g = (u c; v d)` of `P₀ = (u, v)`. -/
def rootMap (P₀ : ℕ × ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  (P₀.1 * z.1 + rootC P₀.1 P₀.2 * z.2, P₀.2 * z.1 + rootD P₀.1 P₀.2 * z.2)

/-- `g⁻¹ w = (d w₁ - c w₂, -v w₁ + u w₂)`. -/
def rootMapInv (P₀ : ℕ × ℕ) (w : ℤ × ℤ) : ℤ × ℤ :=
  (rootD P₀.1 P₀.2 * w.1 - rootC P₀.1 P₀.2 * w.2, -(P₀.2 : ℤ) * w.1 + P₀.1 * w.2)

variable {P₀ : ℕ × ℕ}

/-- `u d - v c = 1`. -/
theorem root_det (hu : 0 < P₀.1) (hco : P₀.1.Coprime P₀.2) :
    (P₀.1 : ℤ) * rootD P₀.1 P₀.2 - P₀.2 * rootC P₀.1 P₀.2 = 1 := by
  have h : ((P₀.1 * rootD P₀.1 P₀.2 : ℕ) : ℤ) = (1 + P₀.2 * rootC P₀.1 P₀.2 : ℕ) := by
    rw [mul_rootD hu hco]
  push_cast at h
  linarith

/-- `g⁻¹ g z = z`. -/
theorem rootMapInv_rootMap (hu : 0 < P₀.1) (hco : P₀.1.Coprime P₀.2) (z : ℤ × ℤ) :
    rootMapInv P₀ (rootMap P₀ z) = z := by
  have h := root_det hu hco
  refine Prod.ext ?_ ?_ <;> simp only [rootMapInv, rootMap]
  · linear_combination z.1 * h
  · linear_combination z.2 * h

/-- `g g⁻¹ w = w`. -/
theorem rootMap_rootMapInv (hu : 0 < P₀.1) (hco : P₀.1.Coprime P₀.2) (w : ℤ × ℤ) :
    rootMap P₀ (rootMapInv P₀ w) = w := by
  have h := root_det hu hco
  refine Prod.ext ?_ ?_ <;> simp only [rootMapInv, rootMap]
  · linear_combination w.1 * h
  · linear_combination w.2 * h

/-- `g` maps primitive vectors to primitive vectors. -/
theorem isCoprime_rootMap (hu : 0 < P₀.1) (hco : P₀.1.Coprime P₀.2) {z : ℤ × ℤ}
    (hz : IsCoprime z.1 z.2) : IsCoprime (rootMap P₀ z).1 (rootMap P₀ z).2 := by
  obtain ⟨x, y, h⟩ := hz
  refine ⟨x * rootD P₀.1 P₀.2 - y * P₀.2, -x * rootC P₀.1 P₀.2 + y * P₀.1, ?_⟩
  simp only [rootMap]
  linear_combination h + (x * z.1 + y * z.2) * root_det hu hco

/-- `g⁻¹` maps primitive vectors to primitive vectors. -/
theorem isCoprime_rootMapInv (hu : 0 < P₀.1) (hco : P₀.1.Coprime P₀.2) {w : ℤ × ℤ}
    (hw : IsCoprime w.1 w.2) : IsCoprime (rootMapInv P₀ w).1 (rootMapInv P₀ w).2 := by
  obtain ⟨x, y, h⟩ := hw
  refine ⟨x * P₀.1 + y * P₀.2, x * rootC P₀.1 P₀.2 + y * rootD P₀.1 P₀.2, ?_⟩
  simp only [rootMapInv]
  linear_combination h + (x * w.1 + y * w.2) * root_det hu hco

/-- `det(g z, g z') = det(z, z')`. -/
theorem det_rootMap (hu : 0 < P₀.1) (hco : P₀.1.Coprime P₀.2) (z z' : ℤ × ℤ) :
    (rootMap P₀ z).1 * (rootMap P₀ z').2 - (rootMap P₀ z).2 * (rootMap P₀ z').1 =
      z.1 * z'.2 - z.2 * z'.1 := by
  simp only [rootMap]
  linear_combination (z.1 * z'.2 - z.2 * z'.1) * root_det hu hco

/-- `u τ(z) = (g z)₁` at the ratio `r = c/u`. -/
theorem mul_tau (hu : 0 < P₀.1) (z : ℤ × ℤ) :
    (P₀.1 : ℝ) * tau ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) z = (rootMap P₀ z).1 := by
  have hu' : (P₀.1 : ℝ) ≠ 0 := by positivity
  simp only [tau, rootMap]
  push_cast
  field_simp

/-- `v τ(z) + z₂/u = (g z)₂` at the ratio `r = c/u`. -/
theorem mul_tau_add_div (hu : 0 < P₀.1) (hco : P₀.1.Coprime P₀.2) (z : ℤ × ℤ) :
    (P₀.2 : ℝ) * tau ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) z + z.2 / P₀.1 = (rootMap P₀ z).2 := by
  have hu' : (P₀.1 : ℝ) ≠ 0 := by positivity
  have h : (P₀.1 * rootD P₀.1 P₀.2 : ℝ) = 1 + P₀.2 * rootC P₀.1 P₀.2 := by
    exact_mod_cast mul_rootD hu hco
  simp only [tau, rootMap]
  push_cast
  field_simp
  linear_combination (-(z.2 : ℝ)) * h

/-! ### Divisibility and lines -/

/-- For a prime `p`, a primitive `z` and a primitive row `(a, b)`: `p ∣ a z₁ + b z₂` exactly
when `[z]_p` is the kernel line `[(b, -a)]_p`. -/
theorem dvd_iff_lineOf_eq {p : ℕ} (hp : p.Prime) {a b : ℤ} (hab : IsCoprime a b) {z : ℤ × ℤ}
    (hz : IsCoprime z.1 z.2) : (p : ℤ) ∣ a * z.1 + b * z.2 ↔ lineOf p z = lineOf p (b, -a) := by
  have : Fact p.Prime := ⟨hp⟩
  -- a primitive vector is nonzero modulo `p`
  have hne {x y : ℤ} (h : IsCoprime x y) : ¬((x : ZMod p) = 0 ∧ (y : ZMod p) = 0) := by
    rintro ⟨hx, hy⟩
    obtain ⟨s, t, h⟩ := h
    have h' := congrArg (Int.cast : ℤ → ZMod p) h
    push_cast at h'
    rw [hx, hy] at h'
    simp at h'
  have hval (w : ZMod p) : w.val ≠ p := (ZMod.val_lt w).ne
  have hz' := hne hz
  have hab' := hne hab
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [lineOf]
  push_cast
  by_cases h1 : (z.1 : ZMod p) = 0 <;> by_cases h2 : (b : ZMod p) = 0
  · simp [h1, h2]
  · have h3 : (z.2 : ZMod p) ≠ 0 := fun h3 => hz' ⟨h1, h3⟩
    simp [h1, h2, h3, (hval _).symm]
  · have h3 : (a : ZMod p) ≠ 0 := fun h3 => hab' ⟨h3, h2⟩
    simp [h1, h2, h3, hval]
  · simp only [h1, h2, ite_false, (ZMod.val_injective p).eq_iff]
    constructor
    · intro h
      field_simp
      linear_combination h
    · intro h
      field_simp at h
      linear_combination h

/-! ### Ratios -/

/-- If `n Q₂ - m Q₁ = 1`, then `r_{(n, m)} ≡ Q₁ / n (mod ℤ)`. -/
theorem rootRatio_sub_div {n m : ℕ} (hn : 0 < n) {Q₁ Q₂ : ℤ} (h : n * Q₂ - m * Q₁ = 1) :
    ∃ k : ℤ, rootRatio (n, m) - Q₁ / n = k := by
  have : NeZero n := ⟨hn.ne'⟩
  -- `-m⁻¹ = Q₁` modulo `n`
  have hm : (m : ZMod n) * (-Q₁ : ℤ) = 1 := by
    have h' := congrArg (Int.cast : ℤ → ZMod n) h
    push_cast at h'
    rw [ZMod.natCast_self] at h'
    push_cast
    linear_combination h'
  have hQ : ((((-(m : ZMod n)⁻¹ : ZMod n).val : ℤ) - Q₁ : ℤ) : ZMod n) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.inv_eq_of_mul_eq_one _ _ _ hm]
    push_cast
    ring
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hQ
  refine ⟨k, ?_⟩
  have hk' : ((-(m : ZMod n)⁻¹ : ZMod n).val : ℝ) - Q₁ = n * k := by exact_mod_cast hk
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [rootRatio]
  field_simp
  linear_combination hk'

/-! ### The boxes -/

variable {d : Data K} {Y d₀ : ℝ}

/-- For `U > 0` and `V ≥ 0`, `P ∈ positions` exactly when `P` is primitive and
`P ∈ [U, 16U] × [V, 2V]`. -/
theorem mem_positions_iff (hU : 0 < d₀ * Y * d.Hm) (hV : 0 ≤ d.Hn) {P : ℕ × ℕ} :
    P ∈ positions d Y d₀ ↔ P.1.Coprime P.2 ∧ d₀ * Y * d.Hm ≤ P.1 ∧
      (P.1 : ℝ) ≤ 16 * (d₀ * Y * d.Hm) ∧ d.Hn ≤ P.2 ∧ (P.2 : ℝ) ≤ 2 * d.Hn := by
  simp only [positions, mem_filter, mem_product, mem_Icc, Nat.ceil_le,
    Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 16 * (d₀ * Y * d.Hm)),
    Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 2 * d.Hn)]
  tauto

/-- `z ∈ rootPositions` at the integer root of `P₀` exactly when `z` is primitive, lies in the
square `|z₁|, |z₂| ≤ rootBound`, and `g z ∈ [U, 16U] × [V, 2V]`. -/
theorem mem_rootPositions_iff {U V : ℝ} (hu : 0 < P₀.1) (hco : P₀.1.Coprime P₀.2)
    {z : ℤ × ℤ} :
    z ∈ rootPositions U V P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) ↔
      z ∈ Icc (-(rootBound U V : ℤ)) (rootBound U V) ×ˢ
          Icc (-(rootBound U V : ℤ)) (rootBound U V) ∧
        Int.gcd z.1 z.2 = 1 ∧ U ≤ (rootMap P₀ z).1 ∧ ((rootMap P₀ z).1 : ℝ) ≤ 16 * U ∧
          V ≤ (rootMap P₀ z).2 ∧ ((rootMap P₀ z).2 : ℝ) ≤ 2 * V := by
  rw [rootPositions, mem_filter, mul_tau hu, mul_tau_add_div hu hco]

/-- `((n.toNat : ℕ) : ℝ) = n` for `n ≥ 0`. -/
theorem natCast_toNat {n : ℤ} (hn : 0 ≤ n) : ((n.toNat : ℕ) : ℝ) = n := by
  exact_mod_cast Int.toNat_of_nonneg hn

/-- At a root position, `g z` has positive first and nonnegative second coordinate. -/
theorem rootMap_pos (hU : 0 < d₀ * Y * d.Hm) (hV : 0 ≤ d.Hn) (hu : 0 < P₀.1)
    (hco : P₀.1.Coprime P₀.2) {z : ℤ × ℤ}
    (hz : z ∈ rootPositions (d₀ * Y * d.Hm) d.Hn P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1)) :
    0 < (rootMap P₀ z).1 ∧ 0 ≤ (rootMap P₀ z).2 := by
  obtain ⟨-, -, h₁, -, h₂, -⟩ := (mem_rootPositions_iff hu hco).1 hz
  constructor
  · exact_mod_cast hU.trans_le h₁
  · exact_mod_cast hV.trans h₂

/-- `g` maps the root positions into the physical positions. -/
theorem toNat_rootMap_mem (hU : 0 < d₀ * Y * d.Hm) (hV : 0 ≤ d.Hn) (hu : 0 < P₀.1)
    (hco : P₀.1.Coprime P₀.2) {z : ℤ × ℤ}
    (hz : z ∈ rootPositions (d₀ * Y * d.Hm) d.Hn P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1)) :
    ((rootMap P₀ z).1.toNat, (rootMap P₀ z).2.toNat) ∈ positions d Y d₀ := by
  obtain ⟨-, hg, h₁, h₂, h₃, h₄⟩ := (mem_rootPositions_iff hu hco).1 hz
  obtain ⟨hp₁, hp₂⟩ := rootMap_pos hU hV hu hco hz
  have hc := isCoprime_rootMap hu hco (Int.isCoprime_iff_gcd_eq_one.2 hg)
  rw [← Int.toNat_of_nonneg hp₁.le, ← Int.toNat_of_nonneg hp₂] at hc
  rw [mem_positions_iff hU hV, natCast_toNat hp₁.le, natCast_toNat hp₂]
  exact ⟨Nat.isCoprime_iff_coprime.1 hc, h₁, h₂, h₃, h₄⟩

/-- `g⁻¹` maps the physical positions into the square `|z₁|, |z₂| ≤ rootBound`. -/
theorem rootMapInv_mem_square (hU : 0 < d₀ * Y * d.Hm) (hV : 0 ≤ d.Hn)
    (hP₀ : P₀ ∈ positions d Y d₀) {P : ℕ × ℕ} (hP : P ∈ positions d Y d₀) :
    rootMapInv P₀ (P.1, P.2) ∈
      Icc (-(rootBound (d₀ * Y * d.Hm) d.Hn : ℤ)) (rootBound (d₀ * Y * d.Hm) d.Hn) ×ˢ
        Icc (-(rootBound (d₀ * Y * d.Hm) d.Hn : ℤ)) (rootBound (d₀ * Y * d.Hm) d.Hn) := by
  set U := d₀ * Y * d.Hm
  set V := d.Hn
  obtain ⟨hco, hu₁, hu₂, -, hv₂⟩ := (mem_positions_iff hU hV).1 hP₀
  obtain ⟨-, hP₁, hP₁', hP₂, hP₂'⟩ := (mem_positions_iff hU hV).1 hP
  have hu : 0 < P₀.1 := by exact_mod_cast hU.trans_le hu₁
  -- `c < u` and `d ≤ 1 + v`
  have hc : (rootC P₀.1 P₀.2 : ℝ) ≤ P₀.1 := by exact_mod_cast (rootC_lt hu P₀.2).le
  have hd : (rootD P₀.1 P₀.2 : ℝ) ≤ 1 + P₀.2 := by
    have h : P₀.1 * rootD P₀.1 P₀.2 ≤ P₀.1 * (1 + P₀.2) := by
      rw [mul_rootD hu hco]
      nlinarith [rootC_lt hu P₀.2]
    exact_mod_cast Nat.le_of_mul_le_mul_left h hu
  have hB : 2 * (16 * U + 2 * V + 1) ^ 2 ≤ (rootBound U V : ℝ) := Nat.le_ceil _
  have hP₁0 : (0 : ℝ) ≤ P.1 := by positivity
  have hP₂0 : (0 : ℝ) ≤ P.2 := by positivity
  have hc0 : (0 : ℝ) ≤ rootC P₀.1 P₀.2 := by positivity
  have hd0 : (0 : ℝ) ≤ rootD P₀.1 P₀.2 := by positivity
  have hv0 : (0 : ℝ) ≤ P₀.2 := by positivity
  have h₁ : (rootD P₀.1 P₀.2 : ℝ) * P.1 ≤ (1 + 2 * V) * (16 * U) :=
    mul_le_mul (by linarith) hP₁' hP₁0 (by linarith)
  have h₂ : (rootC P₀.1 P₀.2 : ℝ) * P.2 ≤ (16 * U) * (2 * V) :=
    mul_le_mul (by linarith) hP₂' hP₂0 (by linarith)
  have h₃ : (P₀.2 : ℝ) * P.1 ≤ (2 * V) * (16 * U) := mul_le_mul hv₂ hP₁' hP₁0 (by linarith)
  have h₄ : (P₀.1 : ℝ) * P.2 ≤ (16 * U) * (2 * V) := mul_le_mul hu₂ hP₂' hP₂0 (by linarith)
  have h₅ : 0 ≤ (rootD P₀.1 P₀.2 : ℝ) * P.1 := by positivity
  have h₆ : 0 ≤ (rootC P₀.1 P₀.2 : ℝ) * P.2 := by positivity
  have h₇ : 0 ≤ (P₀.2 : ℝ) * P.1 := by positivity
  have h₈ : 0 ≤ (P₀.1 : ℝ) * P.2 := by positivity
  have hUV : 0 ≤ U * V := by positivity
  simp only [rootMapInv, mem_product, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  all_goals
    rw [← Int.cast_le (R := ℝ)]
    push_cast
    nlinarith

/-- `g⁻¹` maps the physical positions into the root positions. -/
theorem rootMapInv_mem (hU : 0 < d₀ * Y * d.Hm) (hV : 0 ≤ d.Hn) (hP₀ : P₀ ∈ positions d Y d₀)
    {P : ℕ × ℕ} (hP : P ∈ positions d Y d₀) :
    rootMapInv P₀ (P.1, P.2) ∈
      rootPositions (d₀ * Y * d.Hm) d.Hn P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) := by
  obtain ⟨hco, hu₁, -⟩ := (mem_positions_iff hU hV).1 hP₀
  have hu : 0 < P₀.1 := by exact_mod_cast hU.trans_le hu₁
  obtain ⟨hPc, hP₁, hP₁', hP₂, hP₂'⟩ := (mem_positions_iff hU hV).1 hP
  have hc := isCoprime_rootMapInv hu hco (w := ((P.1 : ℤ), (P.2 : ℤ)))
    (Nat.isCoprime_iff_coprime.2 hPc)
  rw [mem_rootPositions_iff hu hco, rootMap_rootMapInv hu hco]
  exact ⟨rootMapInv_mem_square hU hV hP₀ hP, Int.isCoprime_iff_gcd_eq_one.1 hc,
    by exact_mod_cast hP₁, by exact_mod_cast hP₁', by exact_mod_cast hP₂,
    by exact_mod_cast hP₂'⟩

/-! ### The isomorphism -/

/-- A physical position has `u > 0`. -/
theorem pos_of_mem (hU : 0 < d₀ * Y * d.Hm) (hV : 0 ≤ d.Hn) (hP₀ : P₀ ∈ positions d Y d₀) :
    0 < P₀.1 := by
  exact_mod_cast hU.trans_le ((mem_positions_iff hU hV).1 hP₀).2.1

/-- A physical position is primitive. -/
theorem coprime_of_mem (hP₀ : P₀ ∈ positions d Y d₀) : P₀.1.Coprime P₀.2 :=
  (mem_filter.1 hP₀).2

/-- `g⁻¹ P₀ = e₁`. -/
theorem rootMapInv_self (hu : 0 < P₀.1) (hco : P₀.1.Coprime P₀.2) :
    rootMapInv P₀ (P₀.1, P₀.2) = (1, 0) := by
  refine Prod.ext ?_ ?_ <;> simp only [rootMapInv]
  · linear_combination root_det hu hco
  · ring

/-- `z ↦ g z` from the root positions at the integer root of `P₀` to the physical
positions. -/
def rootEquiv (hU : 0 < d₀ * Y * d.Hm) (hV : 0 ≤ d.Hn) (hP₀ : P₀ ∈ positions d Y d₀) :
    ↥(rootPositions (d₀ * Y * d.Hm) d.Hn P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1)) ≃
      ↥(positions d Y d₀) where
  toFun z := ⟨_, toNat_rootMap_mem hU hV (pos_of_mem hU hV hP₀) (coprime_of_mem hP₀) z.2⟩
  invFun P := ⟨_, rootMapInv_mem hU hV hP₀ P.2⟩
  left_inv z := by
    obtain ⟨h₁, h₂⟩ := rootMap_pos hU hV (pos_of_mem hU hV hP₀) (coprime_of_mem hP₀) z.2
    refine Subtype.ext ?_
    simp only [Int.toNat_of_nonneg h₁.le, Int.toNat_of_nonneg h₂]
    exact rootMapInv_rootMap (pos_of_mem hU hV hP₀) (coprime_of_mem hP₀) z.1
  right_inv P := by
    refine Subtype.ext ?_
    simp only [rootMap_rootMapInv (pos_of_mem hU hV hP₀) (coprime_of_mem hP₀), Int.toNat_natCast]

/-- `z ↦ g z` is an isomorphism from the root model at the integer root of `P₀`, with lines
`ℓ(P₀)`, onto the physical model. -/
def rootIso (hU : 0 < d₀ * Y * d.Hm) (hV : 0 ≤ d.Hn) (hP₀ : P₀ ∈ positions d Y d₀) :
    (rootModel d Y d₀ P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) (rootLines P₀)).Iso
      (physModel d Y d₀) where
  toEquiv := rootEquiv hU hV hP₀
  det_eq := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩
    have hu := pos_of_mem hU hV hP₀
    have hco := coprime_of_mem hP₀
    obtain ⟨h₁, h₂⟩ := rootMap_pos hU hV hu hco hz
    obtain ⟨h₁', h₂'⟩ := rootMap_pos hU hV hu hco hz'
    show ((rootMap P₀ z).1.toNat : ℤ) * ((rootMap P₀ z').2.toNat : ℤ) -
      ((rootMap P₀ z).2.toNat : ℤ) * ((rootMap P₀ z').1.toNat : ℤ) = z.1 * z'.2 - z.2 * z'.1
    rw [Int.toNat_of_nonneg h₁.le, Int.toNat_of_nonneg h₂, Int.toNat_of_nonneg h₁'.le,
      Int.toNat_of_nonneg h₂']
    exact det_rootMap hu hco z z'
  firstDvd_iff := by
    rintro p hp ⟨z, hz⟩
    have hu := pos_of_mem hU hV hP₀
    have hco := coprime_of_mem hP₀
    obtain ⟨h₁, -⟩ := rootMap_pos hU hV hu hco hz
    obtain ⟨-, hg, -⟩ := (mem_rootPositions_iff hu hco).1 hz
    show p ∣ (rootMap P₀ z).1.toNat ↔ lineOf p z = rootLines P₀ p
    rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg h₁.le, rootLines]
    exact dvd_iff_lineOf_eq hp ⟨rootD P₀.1 P₀.2, -(P₀.2 : ℤ), by linear_combination root_det hu hco⟩
      (Int.isCoprime_iff_gcd_eq_one.2 hg)
  ratio_sub := by
    rintro ⟨z, hz⟩
    have hu := pos_of_mem hU hV hP₀
    have hco := coprime_of_mem hP₀
    have hu' : (P₀.1 : ℝ) ≠ 0 := by positivity
    obtain ⟨h₁, h₂⟩ := rootMap_pos hU hV hu hco hz
    obtain ⟨-, hg, -⟩ := (mem_rootPositions_iff hu hco).1 hz
    show ∃ k : ℤ, rootRatio ((rootMap P₀ z).1.toNat, (rootMap P₀ z).2.toNat) -
      tau ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) (complement z) /
        tau ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) z = k
    rw [← mul_div_mul_left _ _ hu', mul_tau hu, mul_tau hu, ← natCast_toNat h₁.le]
    refine rootRatio_sub_div (Q₂ := (rootMap P₀ (complement z)).2) (by omega) ?_
    rw [Int.toNat_of_nonneg h₁.le, Int.toNat_of_nonneg h₂, det_rootMap hu hco]
    -- `det(z, w_z) = gcd(z₁, z₂) = 1`
    have h := Int.gcd_eq_gcd_ab z.1 z.2
    rw [hg, Nat.cast_one] at h
    simp only [complement]
    linear_combination -h

end Reindex

/-- **RR1**: the determinant moment is the sum over physical positions of the root moments at
their integer roots. -/
theorem detMoment_eq_sum_rootMoment (q A₀ x : ℝ) {d : Data K} {Y d₀ : ℝ}
    (hU : 0 < d₀ * Y * d.Hm) (hV : 0 ≤ d.Hn) :
    detMoment q A₀ x d Y d₀ =
      ∑ P₀ ∈ positions d Y d₀, rootMoment q A₀ x d Y d₀ P₀.1 P₀.2
        ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) (rootLines P₀) := by
  rw [detMoment_eq_sum_moment, ← sum_coe_sort (positions d Y d₀)]
  refine Fintype.sum_congr _ _ fun P₀ => ?_
  have hu := Reindex.pos_of_mem hU hV P₀.2
  have hco := Reindex.coprime_of_mem P₀.2
  -- `e₁ = g⁻¹ P₀` is a root position
  have h : ((1 : ℤ), (0 : ℤ)) ∈
      rootPositions (d₀ * Y * d.Hm) d.Hn P₀.1.1 P₀.1.2 ((rootC P₀.1.1 P₀.1.2 : ℝ) / P₀.1.1) := by
    have h := Reindex.rootMapInv_mem hU hV P₀.2 P₀.2
    rwa [Reindex.rootMapInv_self hu hco] at h
  rw [rootMoment, dite_eq_left_of_eq_true (eq_true h)]
  refine Eq.trans ?_ ((Reindex.rootIso hU hV P₀.2).moment_eq q A₀ x d Y d₀ _)
  congr 1
  -- `g e₁ = P₀`
  refine Subtype.ext ?_
  show P₀.1 = ((Reindex.rootMap P₀.1 (1, 0)).1.toNat, (Reindex.rootMap P₀.1 (1, 0)).2.toNat)
  simp [Reindex.rootMap]

end Erdos408.OneSided
