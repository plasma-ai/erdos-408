module

public import Erdos408.OneSided.Moment.RootReplacement.Config

/-!
# The tube

PD `det:tube` ((3.30), §3.5), for the configurations of `Config.lean`. A configuration with
`c(ω) ≠ 0` starts at `e₁`, its consecutive determinants are below `10 H`, `H = d₀ Y`, since
the pad product `D ∈ [d₀, 2d₀)` divides `det(z, z')` and the plateau forces
`|det(z, z')/D| < 5Y`, and `d₀, Y` are below the product of the labels, since `D ≥ d₀` and the
bump `η(b/Y)` forces `b > Y`.

If moreover the configuration is live, all its visits are positions at one root `ϱ` of the
box. Then `g z_j ∈ Ω` and `det(g z, g z') = det(z, z')`, so consecutive slopes of `g z_j`
differ by at most `10 H / U²`, and `z_{j,2} = det(g e₁, g z_j)` is at most `2560 N H`
(`tube_of_live`). Since `τ(z_j) ∈ [1/16, 16]`, also `|z_{j,1}| ≤ 2560 N H + 16`.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-! ### Nonzero entries of the operators -/

/-- The dyadic bump vanishes at `y ≤ 1`. -/
theorem one_lt_of_dyadicBump_ne_zero {y : ℝ} (h : dyadicBump y ≠ 0) : 1 < y := by
  by_contra hy
  push Not at hy
  exact h (by
    rw [dyadicBump, Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero])

/-- The plateau vanishes at `|t| ≥ 5`. -/
theorem abs_lt_of_plateau_ne_zero {t : ℝ} (h : plateau t ≠ 0) : |t| < 5 := by
  by_contra ht
  push Not at ht
  exact h (Real.smoothTransition.zero_of_nonpos (by linarith))

/-- The product of all labels is the pad product times the last-slot product. -/
theorem listProd_eq_padProd_mul_lastProd {J : ℕ} (p : Lists K J) :
    listProd p = padProd p * lastProd p := by
  simp only [listProd, padProd, lastProd, ← prod_mul_distrib, Fin.prod_univ_castSucc]

/-- The product of all labels is invariant under reordering each group. -/
theorem listProd_comp_perm {J : ℕ} (p p' : Lists K J) (σ : Fin K → Equiv.Perm (Fin (J + 1)))
    (h : ∀ i, p' i = p i ∘ σ i) : listProd p' = listProd p := by
  refine prod_congr rfl fun i _ => ?_
  rw [h i]
  exact Equiv.prod_comp (σ i) (p i)

/-- A nonzero entry of the slot symmetrization keeps the position and reorders the lists. -/
theorem PosModel.symOp_ne_zero_imp (M : PosModel) {x : ℝ} {d : Data K} {s s' : M.State x d}
    (h : M.symOp x d s s' ≠ 0) :
    s.1.1 = s'.1.1 ∧
      ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, s'.1.2 i = s.1.2 i ∘ σ i := by
  unfold PosModel.symOp at h
  exact (ite_ne_right_iff.1 h).1

/-- A nonzero entry of the row operation has pad product `D ≥ d₀`, determinant below
`10 d₀ Y` (as `D < 2 d₀` divides it and the plateau forces `|det / D| < 5 Y`), and last-slot
product above `Y` (by the bump). -/
theorem PosModel.rowOp_ne_zero_imp (M : PosModel) {q A₀ x : ℝ} {d : Data K} {Y d₀ : ℝ}
    (hY : 0 < Y) (hd₀ : 0 < d₀) {s s' : M.State x d} (h : M.rowOp q A₀ x d Y d₀ s s' ≠ 0) :
    d₀ ≤ (padProd s.1.2 : ℝ) ∧ |(M.det s.1.1 s'.1.1 : ℝ)| < 10 * d₀ * Y ∧
      Y < lastProd s.1.2 := by
  unfold PosModel.rowOp at h
  obtain ⟨⟨-, -, hD₀, hD₁, hdvd⟩, h⟩ := ite_ne_right_iff.1 h
  have hA := Complex.ofReal_ne_zero.1 (left_ne_zero_of_mul h)
  have hpl := right_ne_zero_of_mul (left_ne_zero_of_mul hA)
  have hb := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul
    (left_ne_zero_of_mul hA)))
  -- step: the bump forces `b > Y`
  have hlast := one_lt_of_dyadicBump_ne_zero hb
  rw [one_lt_div hY] at hlast
  -- step: the plateau forces `|det / D| < 5 Y`
  have hk := abs_lt_of_plateau_ne_zero hpl
  rw [abs_div, abs_of_pos hY, div_lt_iff₀ hY] at hk
  set D := padProd s.1.2
  have hDpos : (0 : ℝ) < D := hd₀.trans_le hD₀
  obtain ⟨k, hkD⟩ := hdvd
  have hk' : M.det s.1.1 s'.1.1 / (D : ℤ) = k := by
    rw [hkD, Int.mul_ediv_cancel_left _ (by exact_mod_cast hDpos.ne')]
  rw [hk'] at hk
  refine ⟨hD₀, ?_, hlast⟩
  rw [hkD, Int.cast_mul, abs_mul, Int.cast_natCast, abs_of_pos hDpos]
  calc (D : ℝ) * |(k : ℝ)| ≤ D * (5 * Y) := by gcongr
    _ < 2 * d₀ * (5 * Y) := by gcongr
    _ = 10 * d₀ * Y := by ring

/-- A nonzero entry of `𝒮 𝒯 𝒮` passes through a nonzero entry of each factor. -/
theorem exists_of_confKernel_ne_zero {A₀ x : ℝ} {d : Data K} {Y d₀ : ℝ}
    {s s' : (squareModel d Y d₀).State x d} (h : confKernel A₀ x d Y d₀ s s' ≠ 0) :
    ∃ t t', (squareModel d Y d₀).symOp x d s t ≠ 0 ∧
      (squareModel d Y d₀).rowOp 1 A₀ x d Y d₀ t t' ≠ 0 ∧
      (squareModel d Y d₀).symOp x d t' s' ≠ 0 := by
  unfold confKernel at h
  rw [Matrix.mul_apply] at h
  obtain ⟨t', -, ht'⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨hST, hS'⟩ := mul_ne_zero_iff.1 ht'
  rw [Matrix.mul_apply] at hST
  obtain ⟨t, -, ht⟩ := exists_ne_zero_of_sum_ne_zero hST
  obtain ⟨hS, hT⟩ := mul_ne_zero_iff.1 ht
  exact ⟨t, t', hS, hT, hS'⟩

/-! ### Slopes in the box -/

/-- Points `P_j = (A_j, B_j)`, `j ≤ N`, with `A_j ∈ [U, 16U]` and consecutive determinants at
most `10 H` have `|det(P₀, P_j)| ≤ 2560 N H`: consecutive slopes differ by at most
`10 H / U²`, and `det(P₀, P_j) = A₀ A_j (B_j / A_j - B₀ / A₀)`. -/
theorem abs_det_le_of_consecutive {N : ℕ} {U H : ℝ} (hU : 0 < U) (hH : 0 ≤ H)
    (A B : Fin (N + 1) → ℝ) (hA : ∀ j, U ≤ A j ∧ A j ≤ 16 * U)
    (hdet : ∀ j : Fin N, |A j.castSucc * B j.succ - B j.castSucc * A j.succ| ≤ 10 * H)
    (j : Fin (N + 1)) : |A 0 * B j - B 0 * A j| ≤ 2560 * N * H := by
  have hApos : ∀ j, 0 < A j := fun j => hU.trans_le (hA j).1
  -- step: the slopes move by at most `10 H / U²` per edge
  have hslope : ∀ n (hn : n < N + 1),
      |B ⟨n, hn⟩ / A ⟨n, hn⟩ - B 0 / A 0| ≤ n * (10 * H / U ^ 2) := by
    intro n
    induction n with
    | zero => intro hn; simp
    | succ n ih =>
      intro hn
      have ha := hApos ⟨n, by omega⟩
      have hb := hApos ⟨n + 1, hn⟩
      have hstep : |B ⟨n + 1, hn⟩ / A ⟨n + 1, hn⟩ - B ⟨n, by omega⟩ / A ⟨n, by omega⟩| ≤
          10 * H / U ^ 2 := by
        have hd : |A ⟨n, by omega⟩ * B ⟨n + 1, hn⟩ - B ⟨n, by omega⟩ * A ⟨n + 1, hn⟩| ≤
            10 * H := hdet ⟨n, by omega⟩
        have hUU : U ^ 2 ≤ A ⟨n + 1, hn⟩ * A ⟨n, by omega⟩ := by
          rw [sq]
          exact mul_le_mul (hA _).1 (hA _).1 hU.le hb.le
        rw [div_sub_div _ _ hb.ne' ha.ne', abs_div, abs_of_pos (mul_pos hb ha),
          div_le_div_iff₀ (mul_pos hb ha) (by positivity)]
        calc |B ⟨n + 1, hn⟩ * A ⟨n, by omega⟩ - A ⟨n + 1, hn⟩ * B ⟨n, by omega⟩| * U ^ 2
            ≤ 10 * H * U ^ 2 := by
              gcongr
              calc |B ⟨n + 1, hn⟩ * A ⟨n, by omega⟩ - A ⟨n + 1, hn⟩ * B ⟨n, by omega⟩|
                  = |A ⟨n, by omega⟩ * B ⟨n + 1, hn⟩ - B ⟨n, by omega⟩ * A ⟨n + 1, hn⟩| := by
                    congr 1
                    ring
                _ ≤ 10 * H := hd
          _ ≤ 10 * H * (A ⟨n + 1, hn⟩ * A ⟨n, by omega⟩) := by gcongr
      calc |B ⟨n + 1, hn⟩ / A ⟨n + 1, hn⟩ - B 0 / A 0|
          ≤ |B ⟨n + 1, hn⟩ / A ⟨n + 1, hn⟩ - B ⟨n, by omega⟩ / A ⟨n, by omega⟩| +
            |B ⟨n, by omega⟩ / A ⟨n, by omega⟩ - B 0 / A 0| := abs_sub_le _ _ _
        _ ≤ 10 * H / U ^ 2 + n * (10 * H / U ^ 2) := add_le_add hstep (ih (by omega))
        _ = ((n + 1 : ℕ) : ℝ) * (10 * H / U ^ 2) := by push_cast; ring
  -- step: `det(P₀, P_j) = A₀ A_j (s_j - s₀)`
  have hj : (j : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
  have h0 := hApos 0
  have hjpos := hApos j
  have hid : A 0 * B j - B 0 * A j = A 0 * A j * (B j / A j - B 0 / A 0) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos (mul_pos h0 hjpos)]
  have hs := hslope j j.isLt
  have hs₀ : 0 ≤ (j : ℝ) * (10 * H / U ^ 2) := by positivity
  calc A 0 * A j * |B j / A j - B 0 / A 0| ≤ (16 * U) * (16 * U) * (j * (10 * H / U ^ 2)) :=
        mul_le_mul (mul_le_mul (hA 0).2 (hA j).2 hjpos.le (by linarith)) hs (abs_nonneg _)
          (by positivity)
    _ = 2560 * j * H := by field_simp; ring
    _ ≤ 2560 * N * H := by gcongr

/-- `c(ω) ≠ 0` forces the start `z₀ = e₁`, consecutive determinants below `10 d₀ Y`, and
`d₀ ≤ ∏ labels`, `Y < ∏ labels` for the labels of the first state. -/
theorem confCoeff_ne_zero_imp {A₀ x : ℝ} {d : Data K} {Y d₀ : ℝ} (hY : 0 < Y) (hd₀ : 0 < d₀)
    (hR : 0 < momentPower x) {ω : Conf x d Y d₀} (hc : confCoeff A₀ x d Y d₀ ω ≠ 0) :
    (ω 0).1.1.1 = (1, 0) ∧
      (∀ j : Fin (2 * momentPower x),
        |(((ω j.castSucc).1.1.1.1 * (ω j.succ).1.1.1.2 -
            (ω j.castSucc).1.1.1.2 * (ω j.succ).1.1.1.1 : ℤ) : ℝ)| < 10 * d₀ * Y) ∧
      d₀ ≤ listProd (ω 0).1.2 ∧ Y < listProd (ω 0).1.2 := by
  unfold confCoeff at hc
  obtain ⟨hc', hker⟩ := mul_ne_zero_iff.1 hc
  have hend := (ite_ne_right_iff.1 (right_ne_zero_of_mul hc')).1
  rw [prod_ne_zero_iff] at hker
  -- step: each edge passes through a nonzero entry of `𝒯`
  have hedge : ∀ j : Fin (2 * momentPower x), ∃ t t' : (squareModel d Y d₀).State x d,
      (ω j.castSucc).1.1 = t.1.1 ∧ listProd t.1.2 = listProd (ω j.castSucc).1.2 ∧
      t'.1.1 = (ω j.succ).1.1 ∧ (squareModel d Y d₀).rowOp 1 A₀ x d Y d₀ t t' ≠ 0 := by
    intro j
    obtain ⟨t, t', hS, hT, hS'⟩ := exists_of_confKernel_ne_zero (hker j (mem_univ _))
    obtain ⟨hpos, σ, hσ⟩ := (squareModel d Y d₀).symOp_ne_zero_imp hS
    exact ⟨t, t', hpos, listProd_comp_perm _ _ σ hσ,
      ((squareModel d Y d₀).symOp_ne_zero_imp hS').1, hT⟩
  refine ⟨hend.1, fun j => ?_, ?_⟩
  · obtain ⟨t, t', hpos, -, hpos', hT⟩ := hedge j
    have h := ((squareModel d Y d₀).rowOp_ne_zero_imp hY hd₀ hT).2.1
    rw [← hpos, hpos'] at h
    exact_mod_cast h
  · -- step: the first edge bounds `d₀` and `Y` by the labels of the first state
    obtain ⟨t, t', -, hprod, -, hT⟩ := hedge ⟨0, by omega⟩
    obtain ⟨hD, -, hb⟩ := (squareModel d Y d₀).rowOp_ne_zero_imp hY hd₀ hT
    have hlp := listProd_eq_padProd_mul_lastProd t.1.2
    have hcast : (Fin.castSucc ⟨0, by omega⟩ : Fin (2 * momentPower x + 1)) = 0 := rfl
    rw [hcast] at hprod
    rw [← hprod, hlp, Nat.cast_mul]
    have hD₁ : (1 : ℝ) ≤ padProd t.1.2 := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
        rintro h0; rw [h0, Nat.cast_zero] at hD; linarith)
    have hb₁ : (1 : ℝ) ≤ lastProd t.1.2 := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
        rintro h0; rw [h0, Nat.cast_zero] at hb; linarith)
    constructor <;> nlinarith

/-- **The tube** (`det:tube`): a live configuration with `c(ω) ≠ 0` has
`|z_{j,2}| ≤ 2560 N H` and `|z_{j,1}| ≤ 2560 N H + 16` at every visit, `H = d₀ Y`. -/
theorem tube_of_live {A₀ x : ℝ} {d : Data K} {Y d₀ : ℝ} (hY : 0 < Y) (hd₀ : 0 < d₀)
    (hHm : 0 < d.Hm) (hR : 0 < momentPower x) {ω : Conf x d Y d₀}
    (hc : confCoeff A₀ x d Y d₀ ω ≠ 0) (hω : ConfLive ω) (j : Fin (2 * momentPower x + 1)) :
    |((ω j).1.1.1.2 : ℝ)| ≤ 2560 * (2 * momentPower x) * (d₀ * Y) ∧
      |((ω j).1.1.1.1 : ℝ)| ≤ 2560 * (2 * momentPower x) * (d₀ * Y) + 16 := by
  classical
  obtain ⟨hz₀, hdet, -⟩ := confCoeff_ne_zero_imp hY hd₀ hR hc
  obtain ⟨u, v, r, hu₁, hu₂, -, -, hr₀, hr₁, hind⟩ := hω
  have hU : 0 < d₀ * Y * d.Hm := by positivity
  have hu : 0 < u := hU.trans_le hu₁
  -- step: every visit is a position at the root `(u, v, r)`
  have hvis : ∀ i, d₀ * Y * d.Hm ≤ u * tau r (ω i).1.1.1 ∧
      u * tau r (ω i).1.1.1 ≤ 16 * (d₀ * Y * d.Hm) := by
    intro i
    have hi := (prod_ne_zero_iff.1 hind) i (mem_univ _)
    unfold visitInd at hi
    obtain ⟨-, h₁, h₂, -⟩ := (mem_filter.1 (ite_ne_right_iff.1 hi).1.1).2
    exact ⟨h₁, h₂⟩
  -- step: `g z ∈ Ω` and `det(g z, g z') = det(z, z')`
  set A : Fin (2 * momentPower x + 1) → ℝ := fun i => u * tau r (ω i).1.1.1
  set B : Fin (2 * momentPower x + 1) → ℝ :=
    fun i => v * tau r (ω i).1.1.1 + ((ω i).1.1.1.2 : ℝ) / u
  have hid : ∀ i k, A i * B k - B i * A k =
      ((ω i).1.1.1.1 : ℝ) * (ω k).1.1.1.2 - ((ω i).1.1.1.2 : ℝ) * (ω k).1.1.1.1 := by
    intro i k
    simp only [A, B, tau]
    field_simp
    ring
  have h₂ := abs_det_le_of_consecutive hU (by positivity : 0 ≤ d₀ * Y) A B
    (fun i => ⟨(hvis i).1, by linarith [(hvis i).2]⟩) (fun i => by
      rw [hid]
      have := hdet i
      push_cast at this
      linarith) j
  rw [hid, hz₀] at h₂
  simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, sub_zero] at h₂
  have h₂' : |((ω j).1.1.1.2 : ℝ)| ≤ 2560 * (2 * momentPower x) * (d₀ * Y) := by
    push_cast at h₂
    linarith
  refine ⟨h₂', ?_⟩
  -- step: `τ(z_j) ∈ (0, 16]`, and `z_{j,1} = τ(z_j) - r z_{j,2}`
  have hτ₀ : 0 < tau r (ω j).1.1.1 := pos_of_mul_pos_right (hU.trans_le (hvis j).1) hu.le
  have hτ₁ : tau r (ω j).1.1.1 ≤ 16 := by
    by_contra h
    push Not at h
    have := (hvis j).2
    nlinarith
  have hrz : |r * ((ω j).1.1.1.2 : ℝ)| ≤ |((ω j).1.1.1.2 : ℝ)| := by
    rw [abs_mul, abs_of_nonneg hr₀]
    exact mul_le_of_le_one_left (abs_nonneg _) hr₁
  have heq : ((ω j).1.1.1.1 : ℝ) = tau r (ω j).1.1.1 - r * (ω j).1.1.1.2 := by
    simp only [tau]
    ring
  rw [heq]
  calc |tau r (ω j).1.1.1 - r * ((ω j).1.1.1.2 : ℝ)|
      ≤ |tau r (ω j).1.1.1| + |r * ((ω j).1.1.1.2 : ℝ)| := abs_sub _ _
    _ ≤ 16 + 2560 * (2 * momentPower x) * (d₀ * Y) := by
        rw [abs_of_pos hτ₀]
        linarith
    _ = 2560 * (2 * momentPower x) * (d₀ * Y) + 16 := by ring

end Erdos408.OneSided
