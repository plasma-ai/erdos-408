import Erdos408.OneSided.Cauchy
import Erdos408.OneSided.Lift

/-!
# Slope cells and the support of the lift

The geometric part of PD §3.3 (`blueprint/one_sided_type_ii.md` §5.1).

* `slopeCell κ P = ⌊κ P₂ / P₁⌋` cuts the slopes into intervals of length `1/κ`; with
  `κ = U²/H` these are the intervals of length `H/U²` of PD.
* Positions with `|det(P, Q)| ≤ 10H` and first coordinates at least `U` lie in cells at
  distance at most `10`.
* A cell holds at most `17 (512H + 1)` primitive positions with `P₁ ∈ [U, 16U]`: against a
  pivot `P₀`, the map `P ↦ (det(P₀, P), ⌊P₁/P₀₁⌋)` is injective.
* An entry of `𝒜 = 𝒢 𝒮 𝒯 𝒮 𝒢` is nonzero only if an entry of `𝒯` between the same
  positions is. A nonzero entry of `𝒯` has `|det(P, Q)| < 10 d₀ Y` and `d₀ Y` below its
  list product.
-/

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-! ### Slope cells -/

/-- The slope cell `⌊κ P₂ / P₁⌋`. -/
noncomputable def slopeCell (κ : ℝ) (P : ℕ × ℕ) : ℤ := ⌊(P.2 : ℝ) / P.1 * κ⌋

/-- The slopes of `P` and `Q`, scaled by `U²/H`, differ by `|det(P, Q)| U² / (H P₁ Q₁)`. -/
theorem slope_sub_slope {U H : ℝ} (hH : 0 < H) {P Q : ℕ × ℕ} (hP : 0 < (P.1 : ℝ))
    (hQ : 0 < (Q.1 : ℝ)) :
    (Q.2 : ℝ) / Q.1 * (U ^ 2 / H) - (P.2 : ℝ) / P.1 * (U ^ 2 / H) =
      (det P Q : ℝ) * U ^ 2 / (H * (P.1 * Q.1)) := by
  unfold det
  push_cast
  field_simp

/-- Positions with `|det(P, Q)| ≤ 10H` and `P₁, Q₁ ≥ U` lie in cells at distance at most
`10`. -/
theorem abs_slopeCell_sub_le {U H : ℝ} (hU : 0 < U) (hH : 0 < H) {P Q : ℕ × ℕ}
    (hP : U ≤ P.1) (hQ : U ≤ Q.1) (hdet : |(det P Q : ℝ)| ≤ 10 * H) :
    |slopeCell (U ^ 2 / H) P - slopeCell (U ^ 2 / H) Q| ≤ 10 := by
  have hP₀ : 0 < (P.1 : ℝ) := hU.trans_le hP
  have hQ₀ : 0 < (Q.1 : ℝ) := hU.trans_le hQ
  set a := (P.2 : ℝ) / P.1 * (U ^ 2 / H)
  set b := (Q.2 : ℝ) / Q.1 * (U ^ 2 / H)
  -- the scaled slopes differ by at most `10`
  have hab : |b - a| ≤ 10 := by
    rw [slope_sub_slope hH hP₀ hQ₀, abs_div, abs_mul, abs_of_pos (by positivity : 0 < U ^ 2),
      abs_of_pos (by positivity : 0 < H * (P.1 * Q.1)), div_le_iff₀ (by positivity)]
    have hUU : U ^ 2 ≤ P.1 * Q.1 := by nlinarith
    nlinarith [abs_nonneg (det P Q : ℝ)]
  have ha₁ := Int.floor_le a
  have ha₂ := Int.lt_floor_add_one a
  have hb₁ := Int.floor_le b
  have hb₂ := Int.lt_floor_add_one b
  have hab' := abs_le.1 hab
  have h₁ : ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) < 11 := by push_cast; linarith
  have h₂ : (-11 : ℝ) < ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) := by push_cast; linarith
  have h₁' : ⌊a⌋ - ⌊b⌋ < 11 := by exact_mod_cast h₁
  have h₂' : -11 < ⌊a⌋ - ⌊b⌋ := by exact_mod_cast h₂
  show |⌊a⌋ - ⌊b⌋| ≤ 10
  rw [abs_le]
  constructor <;> omega

/-- A slope cell holds at most `17 (512H + 1)` primitive positions with `P₁ ∈ [U, 16U]`. -/
theorem card_slopeCell_le {U H : ℝ} (hU : 0 < U) (hH : 0 < H) (S : Finset (ℕ × ℕ))
    (hS : ∀ P ∈ S, U ≤ P.1 ∧ (P.1 : ℝ) ≤ 16 * U ∧ Nat.Coprime P.1 P.2) (j : ℤ) :
    ((S.filter fun P => slopeCell (U ^ 2 / H) P = j).card : ℝ) ≤ 17 * (512 * H + 1) := by
  set T := S.filter fun P => slopeCell (U ^ 2 / H) P = j with hT
  rcases T.eq_empty_or_nonempty with hT₀ | ⟨P₀, hP₀⟩
  · rw [hT₀, card_empty, Nat.cast_zero]
    positivity
  set n := ⌊256 * H⌋₊
  obtain ⟨hP₀S, hP₀j⟩ := mem_filter.1 hP₀
  obtain ⟨hP₀U, -, hP₀cop⟩ := hS P₀ hP₀S
  have hP₀pos : 0 < (P₀.1 : ℝ) := hU.trans_le hP₀U
  -- the scaled slopes in the cell lie in `[j, j + 1)`
  have hslope : ∀ P ∈ T, (j : ℝ) ≤ (P.2 : ℝ) / P.1 * (U ^ 2 / H) ∧
      (P.2 : ℝ) / P.1 * (U ^ 2 / H) < j + 1 := by
    intro P hP
    have h := (mem_filter.1 hP).2
    unfold slopeCell at h
    rw [← h]
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  -- the determinant with the pivot is at most `256H`
  have hdet : ∀ P ∈ T, |det P₀ P| ≤ n := by
    intro P hP
    obtain ⟨hPU, hP16, -⟩ := hS P (mem_filter.1 hP).1
    have hPpos : 0 < (P.1 : ℝ) := hU.trans_le hPU
    have hs := hslope P hP
    have hs₀ := hslope P₀ hP₀
    have h := slope_sub_slope (U := U) hH hP₀pos hPpos
    have hlt : |(det P₀ P : ℝ) * U ^ 2 / (H * (P₀.1 * P.1))| < 1 := by
      rw [← h, abs_sub_lt_iff]
      constructor <;> linarith
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < U ^ 2),
      abs_of_pos (by positivity : 0 < H * (P₀.1 * P.1)), div_lt_one (by positivity)] at hlt
    have hP₀16 := (hS P₀ hP₀S).2.1
    have hle : |(det P₀ P : ℝ)| ≤ 256 * H := by
      by_contra hcon
      push Not at hcon
      have : 256 * H * U ^ 2 ≥ H * (P₀.1 * P.1) := by
        have : (P₀.1 : ℝ) * P.1 ≤ 16 * U * (16 * U) :=
          mul_le_mul hP₀16 hP16 hPpos.le (by positivity)
        nlinarith
      nlinarith [abs_nonneg (det P₀ P : ℝ), sq_nonneg U]
    have h' : |det P₀ P| ≤ ⌊256 * H⌋ := Int.le_floor.2 (by rw [Int.cast_abs]; exact hle)
    rwa [← Int.natCast_floor_eq_floor (by positivity)] at h'
  -- `P ↦ (det(P₀, P), ⌊P₁ / P₀₁⌋)` maps the cell into a box
  have hmaps : ∀ P ∈ T, (det P₀ P, P.1 / P₀.1) ∈ (Icc (-(n : ℤ)) n) ×ˢ range 17 := by
    intro P hP
    obtain ⟨-, hP16, -⟩ := hS P (mem_filter.1 hP).1
    have hd := abs_le.1 (hdet P hP)
    have h16 : P.1 < 17 * P₀.1 := by
      have : (P.1 : ℝ) < 17 * P₀.1 := by linarith
      exact_mod_cast this
    rw [mem_product, mem_Icc, mem_range]
    exact ⟨hd, Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩
  -- and is injective: equal determinants differ by multiples of the primitive pivot
  have hinj : Set.InjOn (fun P : ℕ × ℕ => (det P₀ P, P.1 / P₀.1)) T := by
    intro P _ P' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hd, hq⟩ := h
    have hP₀ne : (P₀.1 : ℤ) ≠ 0 := by
      have : P₀.1 ≠ 0 := by
        intro h0
        rw [h0, Nat.cast_zero] at hP₀pos
        exact lt_irrefl _ hP₀pos
      exact_mod_cast this
    have hlin : (P₀.1 : ℤ) * (P.2 - P'.2) = (P.1 - P'.1) * P₀.2 := by
      unfold det at hd
      linarith
    have hdvd : (P₀.1 : ℤ) ∣ P.1 - P'.1 :=
      (Nat.isCoprime_iff_coprime.2 hP₀cop).dvd_of_dvd_mul_right ⟨P.2 - P'.2, hlin.symm⟩
    have hmod : P'.1 % P₀.1 = P.1 % P₀.1 := Nat.modEq_iff_dvd.2 hdvd
    have h1 : P.1 = P'.1 :=
      calc P.1 = P₀.1 * (P.1 / P₀.1) + P.1 % P₀.1 := (Nat.div_add_mod _ _).symm
        _ = P₀.1 * (P'.1 / P₀.1) + P'.1 % P₀.1 := by rw [hq, hmod]
        _ = P'.1 := Nat.div_add_mod _ _
    have h2 : P.2 = P'.2 := by
      rw [h1, sub_self, zero_mul] at hlin
      have := (mul_eq_zero.1 hlin).resolve_left hP₀ne
      omega
    exact Prod.ext h1 h2
  have hcard := card_le_card_of_injOn _ (fun P hP => hmaps P hP) hinj
  rw [card_product, Int.card_Icc, card_range,
    show (n + 1 - -(n : ℤ)).toNat = 2 * n + 1 by omega] at hcard
  have hn : (n : ℝ) ≤ 256 * H := Nat.floor_le (by positivity)
  calc (T.card : ℝ) ≤ ((2 * n + 1) * 17 : ℕ) := by exact_mod_cast hcard
    _ ≤ 17 * (512 * H + 1) := by push_cast; linarith

/-! ### Support of the operators -/

/-- A nonzero entry of a product comes from nonzero entries of the factors. -/
private theorem exists_ne_zero_of_mul_apply_ne_zero {ι : Type*} [Fintype ι]
    {M N : Matrix ι ι ℂ} {a c : ι} (h : (M * N) a c ≠ 0) : ∃ b, M a b ≠ 0 ∧ N b c ≠ 0 := by
  rw [Matrix.mul_apply] at h
  obtain ⟨b, -, hb⟩ := exists_ne_zero_of_sum_ne_zero h
  exact ⟨b, left_ne_zero_of_mul hb, right_ne_zero_of_mul hb⟩

variable {q A₀ x : ℝ} {d : Data K} {Y d₀ : ℝ}

/-- `𝒢` is diagonal. -/
private theorem eq_of_goodOp_ne_zero {s t : State x d Y d₀} (h : goodOp x d Y d₀ s t ≠ 0) :
    s = t := by
  by_contra hst
  exact h (Matrix.diagonal_apply_ne _ hst)

/-- `𝒮` preserves positions. -/
private theorem pos_eq_of_symOp_ne_zero {s t : State x d Y d₀} (h : symOp x d Y d₀ s t ≠ 0) :
    s.1.1 = t.1.1 := by
  unfold symOp at h
  by_contra hst
  exact h (ite_eq_right fun hc => hst hc.1)

/-- A nonzero entry of `𝒜` comes from a nonzero entry of `𝒯` between the same positions. -/
theorem exists_rowOp_ne_zero {s s' : State x d Y d₀} (h : edgeOp q A₀ x d Y d₀ s s' ≠ 0) :
    ∃ t t', t.1.1 = s.1.1 ∧ t'.1.1 = s'.1.1 ∧ rowOp q A₀ x d Y d₀ t t' ≠ 0 := by
  unfold edgeOp at h
  obtain ⟨b₄, h₄, hg₄⟩ := exists_ne_zero_of_mul_apply_ne_zero h
  obtain ⟨b₃, h₃, hs₃⟩ := exists_ne_zero_of_mul_apply_ne_zero h₄
  obtain ⟨b₂, h₂, hr⟩ := exists_ne_zero_of_mul_apply_ne_zero h₃
  obtain ⟨b₁, hg₁, hs₁⟩ := exists_ne_zero_of_mul_apply_ne_zero h₂
  refine ⟨b₂, b₃, ?_, ?_, hr⟩
  · rw [← pos_eq_of_symOp_ne_zero hs₁, eq_of_goodOp_ne_zero hg₁]
  · rw [pos_eq_of_symOp_ne_zero hs₃, eq_of_goodOp_ne_zero hg₄]

/-- The conditions and cutoffs of a nonzero entry of `𝒯`. -/
theorem rowOp_ne_zero {t t' : State x d Y d₀} (h : rowOp q A₀ x d Y d₀ t t' ≠ 0) :
    d₀ ≤ (padProd t.1.2 : ℝ) ∧ (padProd t.1.2 : ℝ) < 2 * d₀ ∧
      (padProd t.1.2 : ℤ) ∣ det t.1.1 t'.1.1 ∧ dyadicBump (lastProd t.1.2 / Y) ≠ 0 ∧
      plateau ((det t.1.1 t'.1.1 / padProd t.1.2 : ℤ) / Y) ≠ 0 := by
  unfold rowOp at h
  rw [ne_eq, ite_eq_right_iff, not_imp] at h
  obtain ⟨hc, h⟩ := h
  have h₁ := Complex.ofReal_ne_zero.1 (left_ne_zero_of_mul h)
  exact ⟨hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2,
    right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h₁))),
    right_ne_zero_of_mul (left_ne_zero_of_mul h₁)⟩

/-- A nonzero entry of `𝒯` has `|det(P, Q)| < 10 d₀ Y`: the plateau gives `|t| < 5Y` for
`t = det(P, Q) / D`, and `D < 2 d₀`. -/
theorem abs_det_lt_of_rowOp_ne_zero (hY : 0 < Y) {t t' : State x d Y d₀}
    (h : rowOp q A₀ x d Y d₀ t t' ≠ 0) : |(det t.1.1 t'.1.1 : ℝ)| < 10 * (d₀ * Y) := by
  obtain ⟨-, hD₂, hdvd, -, hψ⟩ := rowOp_ne_zero h
  set D := padProd t.1.2
  set τ := det t.1.1 t'.1.1 / D
  -- the plateau vanishes outside `[-5, 5]`
  have hτ : |(τ : ℝ)| < 5 * Y := by
    have h₁ : |(τ : ℝ) / Y| < 5 := by
      by_contra hcon
      push Not at hcon
      exact hψ (smoothTransition.zero_of_nonpos (by linarith))
    rwa [abs_div, abs_of_pos hY, div_lt_iff₀ hY] at h₁
  have hdet : (det t.1.1 t'.1.1 : ℝ) = D * τ := by
    exact_mod_cast (Int.mul_ediv_cancel' hdvd).symm
  rw [hdet, abs_mul, Nat.abs_cast]
  have hD₀ : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  nlinarith [abs_nonneg (τ : ℝ)]

/-- The list product is the pad product times the product of the last slots. -/
theorem listProd_eq_padProd_mul_lastProd {J : ℕ} (p : Lists K J) :
    listProd p = padProd p * lastProd p := by
  unfold listProd padProd lastProd
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun i _ => Fin.prod_univ_castSucc _

/-- A nonzero entry of `𝒯` has `d₀ Y` below the list product of its source: `D ≥ d₀` and
`η(b/Y) ≠ 0` gives `b > Y`. -/
theorem le_listProd_of_rowOp_ne_zero (hY : 0 < Y) {t t' : State x d Y d₀}
    (h : rowOp q A₀ x d Y d₀ t t' ≠ 0) : d₀ * Y ≤ listProd t.1.2 := by
  obtain ⟨hD₁, -, -, hη, -⟩ := rowOp_ne_zero h
  have hb : Y < lastProd t.1.2 := by
    have h₁ := (lt_of_dyadicBump_ne_zero hη).1
    rwa [one_lt_div hY] at h₁
  rw [listProd_eq_padProd_mul_lastProd, Nat.cast_mul]
  exact mul_le_mul hD₁ hb.le hY.le (Nat.cast_nonneg _)

end Erdos408.OneSided
