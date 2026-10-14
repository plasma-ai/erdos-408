import Erdos408.TwoSided.Endpoint.Constant.Glue
import Erdos408.TwoSided.Endpoint.Constant.Kernel

/-!
# Boxes of the constant part

The factorization step E6 of `blueprint/two_sided_correlation.md` §6.3 for the constant part
`𝒰_con(w) = ψ₁(w/Y) w^{iσ} κ ∑_{p ∈ Ps, p ∣ w} H(w/p)`, with an elementary separation in place
of the Mellin cutoff: split `p` and `n = w/p` along the geometric grid
`⌊e^{iδ}⌋`, `i < I`, and in the box `(j, i)` replace `ψ₁(pn/Y)` by its value at the corner
`r = e^{(j + i)δ}`, at a cost `|ψ₁(pn/Y) - ψ₁(r/Y)| ≤ 12 δ M₁(1)`. In the box the corner term
factors over the classes `n ≡ β (mod k)` as `W ∑_β A_β(t) B_β(t)`, with the small-prime
polynomial `A_β(t) = e^{-jδ} ∑_{p} e(hpβ/k) p^{iσ} p^{it}` and the residual
`B_β(t) = e^{-iδ} ∑_{n ≡ β} H(n) n^{iσ} n^{it}`, split by a divisor model as `B⁰ + B¹`.
-/

namespace Erdos408.TwoSided.ConstHigh

open Finset

/-- The geometric grid `⌊e^{iδ}⌋`. -/
noncomputable def grid (δ : ℝ) (i : ℕ) : ℕ :=
  ⌊Real.exp (i * δ)⌋₊

/-- The grid interval `(⌊e^{iδ}⌋, ⌊e^{(i + 1)δ}⌋]`. -/
noncomputable def gridPiece (δ : ℝ) (i : ℕ) : Finset ℕ :=
  Ioc (grid δ i) (grid δ (i + 1))

/-- The additive twist `e(hm/k)`. -/
noncomputable def twist (h : ℤ) (k m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (h * m / k : ℝ))

section Boxes

variable (Y σ δ : ℝ) (h : ℤ) (k : ℕ) (Ps : Finset ℕ) (κ : ℂ) (H : ℕ → ℂ) (ψ : ℝ → ℂ)

/-- The primes of `Ps` in the grid interval `j`. -/
noncomputable def boxPrimes (j : ℕ) : Finset ℕ :=
  (gridPiece δ j).filter (· ∈ Ps)

/-- The box `(j, i)` of the constant part:
`T_{ji}(t) = κ Y⁻¹ ∑_{p, n} ψ(pn/Y) e(hpn/k) (pn)^{iσ} H(n) (pn)^{it}`. -/
noncomputable def boxSum (j i : ℕ) (t : ℝ) : ℂ :=
  κ * (Y : ℂ)⁻¹ * ∑ p ∈ boxPrimes δ Ps j, ∑ n ∈ gridPiece δ i,
    ψ (((p * n : ℕ) : ℝ) / Y) * twist h k (p * n) * ((p * n : ℕ) : ℂ) ^ ((σ : ℂ) * Complex.I) *
      H n * ((p * n : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I)

/-- The corner error of the box: `ψ(pn/Y)` replaced by `ψ(pn/Y) - ψ(r/Y)`, `r = e^{(j + i)δ}`. -/
noncomputable def boxErr (j i : ℕ) (t : ℝ) : ℂ :=
  κ * (Y : ℂ)⁻¹ * ∑ p ∈ boxPrimes δ Ps j, ∑ n ∈ gridPiece δ i,
    (ψ (((p * n : ℕ) : ℝ) / Y) - ψ (Real.exp (j * δ) * Real.exp (i * δ) / Y)) *
      twist h k (p * n) * ((p * n : ℕ) : ℂ) ^ ((σ : ℂ) * Complex.I) * H n *
      ((p * n : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I)

/-- The corner weight `W = κ Y⁻¹ ψ(r/Y) r` of the box. -/
noncomputable def boxWeight (j i : ℕ) : ℂ :=
  κ * (Y : ℂ)⁻¹ * ψ (Real.exp (j * δ) * Real.exp (i * δ) / Y) *
    ((Real.exp (j * δ) * Real.exp (i * δ) : ℝ) : ℂ)

/-- The small-prime polynomial `A_β(t) = e^{-jδ} ∑_{p} e(hpβ/k) p^{iσ} p^{it}` of the box. -/
noncomputable def boxSmall (j β : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ boxPrimes δ Ps j,
    (((Real.exp (j * δ))⁻¹ : ℝ) : ℂ) * twist h k (p * β) * (p : ℂ) ^ ((σ : ℂ) * Complex.I) *
      (p : ℂ) ^ ((t : ℂ) * Complex.I)

/-- The residual `e^{-iδ} ∑_{n ≡ β} G(n) n^{iσ} n^{it}` of the box, for `G = H` and for the
model part and the model error. -/
noncomputable def boxResidual (G : ℕ → ℂ) (i β : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ (gridPiece δ i).filter (· ≡ β [MOD k]),
    (((Real.exp (i * δ))⁻¹ : ℝ) : ℂ) * G n * (n : ℂ) ^ ((σ : ℂ) * Complex.I) *
      (n : ℂ) ^ ((t : ℂ) * Complex.I)

end Boxes

/-! ### The grid -/

/-- The grid starts at `⌊e⁰⌋ = 1`. -/
theorem grid_zero (δ : ℝ) : grid δ 0 = 1 := by
  simp [grid]

/-- The grid is monotone for `δ ≥ 0`. -/
theorem grid_mono {δ : ℝ} (hδ : 0 ≤ δ) : Monotone (grid δ) := fun i j hij =>
  Nat.floor_mono (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hδ))

/-- Every grid point is at least `1`. -/
theorem one_le_grid {δ : ℝ} (hδ : 0 ≤ δ) (i : ℕ) : 1 ≤ grid δ i := by
  rw [← grid_zero δ]
  exact grid_mono hδ (Nat.zero_le i)

/-- A point `m` of the grid interval `i` has `e^{iδ} < m ≤ e^{(i + 1)δ}`. -/
theorem mem_gridPiece {δ : ℝ} {i m : ℕ} (hm : m ∈ gridPiece δ i) :
    Real.exp (i * δ) < m ∧ (m : ℝ) ≤ Real.exp ((i + 1 : ℕ) * δ) := by
  rw [gridPiece, mem_Ioc, grid, grid] at hm
  exact ⟨(Nat.floor_lt (Real.exp_pos _).le).1 hm.1,
    (Nat.le_floor_iff (Real.exp_pos _).le).1 hm.2⟩

/-- The points of a grid interval are positive. -/
theorem gridPiece_pos {δ : ℝ} {i m : ℕ} (hm : m ∈ gridPiece δ i) : m ≠ 0 := by
  have := (mem_gridPiece hm).1
  intro h0
  rw [h0, Nat.cast_zero] at this
  linarith [Real.exp_pos (i * δ)]

/-- The grid interval `i` lies in `[1, ⌊e^{(i+1)δ}⌋]`. -/
theorem gridPiece_subset_Icc (δ : ℝ) (i : ℕ) : gridPiece δ i ⊆ Icc 1 (grid δ (i + 1)) := by
  intro m hm
  have h0 := gridPiece_pos hm
  rw [gridPiece, mem_Ioc] at hm
  exact mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 h0, hm.2⟩

/-- `e^δ - 1 ≤ 2δ` for `0 ≤ δ ≤ 1`. -/
theorem exp_sub_one_le_two_mul {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) :
    Real.exp δ - 1 ≤ 2 * δ := by
  have := Real.abs_exp_sub_one_le (x := δ) (by rw [abs_of_nonneg hδ0]; exact hδ)
  rw [abs_of_nonneg hδ0, abs_of_nonneg (by linarith [Real.add_one_le_exp δ])] at this
  exact this

/-- `e^{(i+1)δ} = e^δ e^{iδ}`. -/
theorem exp_succ_mul (δ : ℝ) (i : ℕ) :
    Real.exp ((i + 1 : ℕ) * δ) = Real.exp δ * Real.exp (i * δ) := by
  rw [← Real.exp_add]
  push_cast
  ring_nf

/-- `⌊e^{iδ}⌋ ≤ e^{iδ}`. -/
theorem grid_le (δ : ℝ) (i : ℕ) : (grid δ i : ℝ) ≤ Real.exp (i * δ) :=
  Nat.floor_le (Real.exp_pos _).le

/-- `⌊e^{(i+1)δ}⌋ ≤ 2e^{iδ}` for `0 ≤ δ ≤ 1/2`. -/
theorem grid_succ_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (i : ℕ) :
    (grid δ (i + 1) : ℝ) ≤ 2 * Real.exp (i * δ) := by
  refine (grid_le δ (i + 1)).trans ?_
  rw [exp_succ_mul]
  have := exp_sub_one_le_two_mul hδ0 (by linarith)
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- The grid interval `i` has at most `3δ e^{iδ}` points once `δ e^{iδ} ≥ 1`. -/
theorem card_gridPiece_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) {i : ℕ}
    (h1 : 1 ≤ δ * Real.exp (i * δ)) : ((gridPiece δ i).card : ℝ) ≤ 3 * δ * Real.exp (i * δ) := by
  rw [gridPiece, Nat.card_Ioc, Nat.cast_sub (grid_mono hδ0 (Nat.le_succ i))]
  have hlo : Real.exp (i * δ) < grid δ i + 1 := Nat.lt_floor_add_one _
  have hhi := grid_le δ (i + 1)
  rw [exp_succ_mul] at hhi
  have := exp_sub_one_le_two_mul hδ0 (by linarith)
  have h2 : (Real.exp δ - 1) * Real.exp (i * δ) ≤ 2 * δ * Real.exp (i * δ) :=
    mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  nlinarith

/-! ### The decomposition into boxes -/

section Decomposition

variable {Y σ δ : ℝ} {h : ℤ} {k : ℕ} {Ps : Finset ℕ} {κ : ℂ} {H : ℕ → ℂ} {ψ : ℝ → ℂ}

/-- The constant part is the sum of its boxes: for `ψ` supported in `[1, 2]`, primes
`p ∈ Ps` with `2p ≤ Y` and a grid reaching `2Y`,
`Y⁻¹ ∑_{w ∈ [Y, 2Y]} 𝒰_con(w) e(hw/k) w^{it} = ∑_{j, i < I} T_{ji}(t)`. -/
theorem twistedPoly_eq_sum_boxSum (hδ : 0 ≤ δ) (hψ : ∀ y, ψ y ≠ 0 → 1 ≤ y ∧ y ≤ 2)
    (hPs : ∀ p ∈ Ps, 2 ≤ p ∧ 2 * (p : ℝ) ≤ Y) {I : ℕ} (hI : 2 * Y ≤ grid δ I) (t : ℝ) :
    twistedPoly Y (fun w => ψ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * κ *
        ∑ p ∈ Ps.filter (· ∣ w), H (w / p)) h k t =
      ∑ j ∈ range I, ∑ i ∈ range I, boxSum Y σ δ h k Ps κ H ψ j i t := by
  set F : ℕ → ℕ → ℂ := fun p n =>
    ψ (((p * n : ℕ) : ℝ) / Y) * twist h k (p * n) * ((p * n : ℕ) : ℂ) ^ ((σ : ℂ) * Complex.I) *
      H n * ((p * n : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) with hF
  set F' : ℕ → ℕ → ℂ := fun w p =>
    ψ ((w : ℝ) / Y) * twist h k w * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * H (w / p) *
      (w : ℂ) ^ ((t : ℂ) * Complex.I) with hF'
  set G := grid δ I with hG
  have hgrid : ∀ g : ℕ → ℂ, ∑ m ∈ Ioc 1 G, g m = ∑ i ∈ range I, ∑ m ∈ gridPiece δ i, g m := by
    intro g
    rw [hG, ← grid_zero δ]
    exact sum_Ioc_eq_sum_range (grid δ) (grid_mono hδ) g I
  have hPsI : Ps ⊆ Ioc 1 G := by
    intro p hp
    obtain ⟨hp2, hpY⟩ := hPs p hp
    refine mem_Ioc.2 ⟨by omega, ?_⟩
    have : (p : ℝ) ≤ G := by nlinarith [show (2 : ℝ) ≤ p by exact_mod_cast hp2]
    exact_mod_cast this
  -- the boxes add up to `κ Y⁻¹ ∑_{p ∈ Ps} ∑_{n ∈ (1, G]} F p n`
  have hR : ∑ j ∈ range I, ∑ i ∈ range I, boxSum Y σ δ h k Ps κ H ψ j i t =
      κ * (Y : ℂ)⁻¹ * ∑ p ∈ Ps, ∑ n ∈ Ioc 1 G, F p n := by
    simp only [boxSum, ← mul_sum]
    congr 1
    show ∑ j ∈ range I, ∑ i ∈ range I, ∑ p ∈ boxPrimes δ Ps j, ∑ n ∈ gridPiece δ i, F p n =
      ∑ p ∈ Ps, ∑ n ∈ Ioc 1 G, F p n
    have h1 : ∀ j, ∑ i ∈ range I, ∑ p ∈ boxPrimes δ Ps j, ∑ n ∈ gridPiece δ i, F p n =
        ∑ p ∈ gridPiece δ j, if p ∈ Ps then ∑ n ∈ Ioc 1 G, F p n else 0 := by
      intro j
      rw [sum_comm, boxPrimes, sum_filter]
      refine sum_congr rfl fun p _ => ?_
      rw [hgrid]
    simp_rw [h1]
    rw [← hgrid fun p => if p ∈ Ps then ∑ n ∈ Ioc 1 G, F p n else 0, sum_ite_mem,
      inter_eq_right.2 hPsI]
  rw [hR, twistedPoly]
  -- the left side, as `κ Y⁻¹ ∑_{p ∈ Ps} ∑_{w ∈ [Y, 2Y], p ∣ w} F' w p`
  have hL : ∑ w ∈ Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, ψ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * κ *
        (∑ p ∈ Ps.filter (· ∣ w), H (w / p)) *
        Complex.exp (2 * Real.pi * Complex.I * (h * w / k : ℝ)) *
        (w : ℂ) ^ ((t : ℂ) * Complex.I) =
      κ * ∑ p ∈ Ps, ∑ w ∈ (Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).filter (p ∣ ·), F' w p := by
    have e1 : ∀ w ∈ Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, ψ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * κ *
          (∑ p ∈ Ps.filter (· ∣ w), H (w / p)) *
          Complex.exp (2 * Real.pi * Complex.I * (h * w / k : ℝ)) *
          (w : ℂ) ^ ((t : ℂ) * Complex.I) = ∑ p ∈ Ps.filter (· ∣ w), κ * F' w p := by
      intro w _
      rw [mul_sum, sum_mul, sum_mul]
      refine sum_congr rfl fun p _ => ?_
      simp only [hF', twist]
      ring
    rw [sum_congr rfl e1, mul_sum]
    simp_rw [mul_sum]
    refine sum_comm' fun w p => ?_
    simp only [mem_filter]
    tauto
  rw [hL, ← mul_assoc, mul_comm ((Y : ℂ)⁻¹) κ]
  congr 1
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨hp2, hpY⟩ := hPs p hp
  have hp0 : 0 < p := by omega
  symm
  have hY0 : 0 < Y := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  refine sum_bij_ne_zero (fun n _ _ => p * n) ?_ ?_ ?_ ?_
  · intro n hn hF0
    have h0 : ψ (((p * n : ℕ) : ℝ) / Y) ≠ 0 := fun h0 => hF0 (by
      show ψ (((p * n : ℕ) : ℝ) / Y) * _ * _ * _ * _ = 0
      rw [h0]
      simp)
    obtain ⟨h1, h2⟩ := hψ _ h0
    rw [le_div_iff₀ hY0, one_mul] at h1
    rw [div_le_iff₀ hY0] at h2
    exact mem_filter.2 ⟨mem_Icc.2 ⟨Nat.ceil_le.2 h1, Nat.le_floor (by linarith)⟩,
      dvd_mul_right p n⟩
  · intro n₁ _ _ n₂ _ _ h12
    exact Nat.eq_of_mul_eq_mul_left hp0 h12
  · intro w hw hF0
    obtain ⟨hwI, hpw⟩ := mem_filter.1 hw
    obtain ⟨hw1, hw2⟩ := mem_Icc.1 hwI
    have hFw : F p (w / p) = F' w p := by simp only [hF, hF', Nat.mul_div_cancel' hpw]
    refine ⟨w / p, mem_Ioc.2 ⟨?_, ?_⟩, by rwa [hFw], Nat.mul_div_cancel' hpw⟩
    · have h2p : 2 * p ≤ w := by
        have : ((2 * p : ℕ) : ℝ) ≤ w := by
          push_cast
          exact hpY.trans ((Nat.le_ceil Y).trans (by exact_mod_cast hw1))
        exact_mod_cast this
      have : 2 ≤ w / p := (Nat.le_div_iff_mul_le hp0).2 (by linarith)
      omega
    · have hwG : w ≤ G := by
        have : (w : ℝ) ≤ G :=
          (show (w : ℝ) ≤ ⌊2 * Y⌋₊ by exact_mod_cast hw2).trans
            ((Nat.floor_le (by linarith)).trans hI)
        exact_mod_cast this
      exact (Nat.div_le_self w p).trans hwG
  · intro n _ _
    simp only [hF, hF', Nat.mul_div_cancel_left n hp0]

/-- The residual is linear in its coefficients. -/
theorem boxResidual_add (G₁ G₂ : ℕ → ℂ) (i β : ℕ) (t : ℝ) :
    boxResidual σ δ k (fun n => G₁ n + G₂ n) i β t =
      boxResidual σ δ k G₁ i β t + boxResidual σ δ k G₂ i β t := by
  simp only [boxResidual, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  ring

/-- One box splits into its corner term over the classes `n ≡ β (mod k)` and the corner
error: `T_{ji} = W ∑_{β < k} A_β B_β + E_{ji}`. -/
theorem boxSum_eq (hk : k ≠ 0) (j i : ℕ) (t : ℝ) :
    boxSum Y σ δ h k Ps κ H ψ j i t =
      boxWeight Y δ κ ψ j i * ∑ β ∈ range k,
          boxSmall σ δ h k Ps j β t * boxResidual σ δ k H i β t +
        boxErr Y σ δ h k Ps κ H ψ j i t := by
  set r := Real.exp (j * δ) * Real.exp (i * δ) with hr
  set X : ℕ → ℕ → ℂ := fun p β => twist h k (p * β) * (p : ℂ) ^ ((σ : ℂ) * Complex.I) *
    (p : ℂ) ^ ((t : ℂ) * Complex.I) with hX
  set Z : ℕ → ℂ := fun β => ∑ n ∈ (gridPiece δ i).filter (· ≡ β [MOD k]),
    H n * (n : ℂ) ^ ((σ : ℂ) * Complex.I) * (n : ℂ) ^ ((t : ℂ) * Complex.I) with hZ
  -- the corner term
  have hmain : boxSum Y σ δ h k Ps κ H ψ j i t - boxErr Y σ δ h k Ps κ H ψ j i t =
      κ * (Y : ℂ)⁻¹ * ψ (r / Y) * ∑ p ∈ boxPrimes δ Ps j, ∑ n ∈ gridPiece δ i,
        twist h k (p * n) * ((p * n : ℕ) : ℂ) ^ ((σ : ℂ) * Complex.I) * H n *
          ((p * n : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
    simp only [boxSum, boxErr, ← mul_sub, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun n _ => ?_
    ring
  -- the classes `n ≡ β`
  have hsplit : ∀ p, ∑ n ∈ gridPiece δ i, twist h k (p * n) *
      ((p * n : ℕ) : ℂ) ^ ((σ : ℂ) * Complex.I) * H n *
        ((p * n : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) = ∑ β ∈ range k, X p β * Z β := by
    intro p
    rw [← sum_fiberwise_of_maps_to (g := (· % k)) (t := range k)
      (fun n _ => mem_range.2 (Nat.mod_lt n (Nat.pos_of_ne_zero hk)))]
    refine sum_congr rfl fun β hβ => ?_
    have hfilt : (gridPiece δ i).filter (fun n => n % k = β) =
        (gridPiece δ i).filter (· ≡ β [MOD k]) := by
      refine filter_congr fun n _ => ?_
      rw [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.1 hβ)]
    rw [hfilt]
    simp only [hZ, hX, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hnβ : n ≡ β [MOD k] := (mem_filter.1 hn).2
    have htw : twist h k (p * n) = twist h k (p * β) :=
      exp_twist_eq_of_modEq h hk (hnβ.mul_left p)
    rw [htw, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Complex.natCast_mul_natCast_cpow]
    ring
  have hcorner : ∑ p ∈ boxPrimes δ Ps j, ∑ n ∈ gridPiece δ i,
      twist h k (p * n) * ((p * n : ℕ) : ℂ) ^ ((σ : ℂ) * Complex.I) * H n *
        ((p * n : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) =
      ∑ β ∈ range k, (∑ p ∈ boxPrimes δ Ps j, X p β) * Z β := by
    simp_rw [hsplit, sum_mul]
    exact sum_comm
  have hsmall : ∀ β, boxSmall σ δ h k Ps j β t =
      (((Real.exp (j * δ))⁻¹ : ℝ) : ℂ) * ∑ p ∈ boxPrimes δ Ps j, X p β := by
    intro β
    simp only [boxSmall, hX, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    ring
  have hres : ∀ β, boxResidual σ δ k H i β t = (((Real.exp (i * δ))⁻¹ : ℝ) : ℂ) * Z β := by
    intro β
    simp only [boxResidual, hZ, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    ring
  have hone : ((r : ℝ) : ℂ) * (((Real.exp (j * δ))⁻¹ : ℝ) : ℂ) *
      (((Real.exp (i * δ))⁻¹ : ℝ) : ℂ) = 1 := by
    rw [hr]
    push_cast
    have h1 : (Real.exp (j * δ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    have h2 : (Real.exp (i * δ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    field_simp
  rw [← sub_eq_iff_eq_add, hmain, hcorner, boxWeight, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [hsmall, hres, ← hr]
  linear_combination (κ * (Y : ℂ)⁻¹ * ψ (r / Y) * ((∑ p ∈ boxPrimes δ Ps j, X p β) * Z β)) *
    hone.symm

/-! ### Norms and continuity -/

/-- The twist has modulus one. -/
theorem norm_twist (h : ℤ) (k m : ℕ) : ‖twist h k m‖ = 1 := by
  rw [twist, show 2 * (Real.pi : ℂ) * Complex.I * ((h * m / k : ℝ) : ℂ) =
    ((2 * Real.pi * (h * m / k) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `t ↦ m^{it}` is continuous for `m ≠ 0`. -/
theorem continuous_natCast_cpow {m : ℕ} (hm : m ≠ 0) :
    Continuous fun t : ℝ => (m : ℂ) ^ ((t : ℂ) * Complex.I) :=
  Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hm))

/-- The small-prime polynomial of a box is continuous. -/
theorem continuous_boxSmall (j β : ℕ) : Continuous (boxSmall σ δ h k Ps j β) :=
  continuous_finsetSum _ fun _ hp => continuous_const.mul
    (continuous_natCast_cpow (gridPiece_pos (mem_filter.1 hp).1))

/-- The residual of a box is continuous. -/
theorem continuous_boxResidual (G : ℕ → ℂ) (i β : ℕ) :
    Continuous (boxResidual σ δ k G i β) :=
  continuous_finsetSum _ fun _ hn => continuous_const.mul
    (continuous_natCast_cpow (gridPiece_pos (mem_filter.1 hn).1))

/-- A box is continuous in `t`. -/
theorem continuous_boxSum (j i : ℕ) : Continuous (boxSum Y σ δ h k Ps κ H ψ j i) := by
  refine continuous_const.mul (continuous_finsetSum _ fun p hp =>
    continuous_finsetSum _ fun n hn => continuous_const.mul (continuous_natCast_cpow ?_))
  exact Nat.mul_ne_zero (gridPiece_pos (mem_filter.1 hp).1) (gridPiece_pos hn)

/-- The corner error of a box is continuous in `t`. -/
theorem continuous_boxErr (j i : ℕ) : Continuous (boxErr Y σ δ h k Ps κ H ψ j i) := by
  refine continuous_const.mul (continuous_finsetSum _ fun p hp =>
    continuous_finsetSum _ fun n hn => continuous_const.mul (continuous_natCast_cpow ?_))
  exact Nat.mul_ne_zero (gridPiece_pos (mem_filter.1 hp).1) (gridPiece_pos hn)

/-- `|A_β(t)| ≤ #𝒫_j e^{-jδ}`. -/
theorem norm_boxSmall_le (j β : ℕ) (t : ℝ) :
    ‖boxSmall σ δ h k Ps j β t‖ ≤ (boxPrimes δ Ps j).card * (Real.exp (j * δ))⁻¹ := by
  rw [boxSmall]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p ∈ boxPrimes δ Ps j, ‖(((Real.exp (j * δ))⁻¹ : ℝ) : ℂ) * twist h k (p * β) *
        (p : ℂ) ^ ((σ : ℂ) * Complex.I) * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖
      ≤ ∑ p ∈ boxPrimes δ Ps j, (Real.exp (j * δ))⁻¹ := by
        refine sum_le_sum fun p _ => ?_
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, norm_twist, mul_one,
          Real.norm_of_nonneg (by positivity)]
        have h1 := IntegerKernel.norm_natCast_cpow_I_mul_le σ p
        have h2 := IntegerKernel.norm_natCast_cpow_I_mul_le t p
        have h3 : 0 ≤ (Real.exp (j * δ))⁻¹ := by positivity
        calc (Real.exp (j * δ))⁻¹ * ‖(p : ℂ) ^ ((σ : ℂ) * Complex.I)‖ *
              ‖(p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ (Real.exp (j * δ))⁻¹ * 1 * 1 := by gcongr
          _ = (Real.exp (j * δ))⁻¹ := by ring
    _ = (boxPrimes δ Ps j).card * (Real.exp (j * δ))⁻¹ := by rw [sum_const, nsmul_eq_mul]

/-- In the box `(j, i)`, `r < pn ≤ e^{2δ} r` for the corner `r = e^{jδ} e^{iδ}`. -/
theorem corner_lt_mul {p n j i : ℕ} (hp : p ∈ gridPiece δ j) (hn : n ∈ gridPiece δ i) :
    Real.exp (j * δ) * Real.exp (i * δ) < (p * n : ℕ) ∧
      ((p * n : ℕ) : ℝ) ≤ Real.exp (2 * δ) * (Real.exp (j * δ) * Real.exp (i * δ)) := by
  obtain ⟨hp1, hp2⟩ := mem_gridPiece hp
  obtain ⟨hn1, hn2⟩ := mem_gridPiece hn
  push_cast
  refine ⟨mul_lt_mul'' hp1 hn1 (Real.exp_pos _).le (Real.exp_pos _).le, ?_⟩
  calc (p : ℝ) * n ≤ Real.exp ((j + 1 : ℕ) * δ) * Real.exp ((i + 1 : ℕ) * δ) :=
        mul_le_mul hp2 hn2 (by positivity) (by positivity)
    _ = Real.exp (2 * δ) * (Real.exp (j * δ) * Real.exp (i * δ)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        push_cast
        ring_nf

/-- The boxes away from the corner range `Y/4 ≤ r ≤ 2Y`, or without primes, vanish. -/
theorem boxSum_eq_zero (hY : 0 < Y) (hδ : δ ≤ 1 / 2) (hψ : ∀ y, ψ y ≠ 0 → 1 ≤ y ∧ y ≤ 2)
    {j i : ℕ} (hji : boxPrimes δ Ps j = ∅ ∨ Real.exp (j * δ) * Real.exp (i * δ) < Y / 4 ∨
      2 * Y < Real.exp (j * δ) * Real.exp (i * δ)) (t : ℝ) :
    boxSum Y σ δ h k Ps κ H ψ j i t = 0 := by
  rw [boxSum]
  rcases hji with h0 | hji
  · rw [h0, sum_empty, mul_zero]
  refine mul_eq_zero_of_right _ (sum_eq_zero fun p hp => sum_eq_zero fun n hn => ?_)
  obtain ⟨h1, h2⟩ := corner_lt_mul (mem_filter.1 hp).1 hn
  have he : Real.exp (2 * δ) ≤ 3 := by
    have := Real.exp_one_lt_d9
    have : Real.exp (2 * δ) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
    linarith
  have hψ0 : ψ (((p * n : ℕ) : ℝ) / Y) = 0 := by
    by_contra h0
    obtain ⟨h3, h4⟩ := hψ _ h0
    rw [le_div_iff₀ hY, one_mul] at h3
    rw [div_le_iff₀ hY] at h4
    rcases hji with hji | hji
    · have : Real.exp (2 * δ) * (Real.exp (j * δ) * Real.exp (i * δ)) ≤
          3 * (Real.exp (j * δ) * Real.exp (i * δ)) :=
        mul_le_mul_of_nonneg_right he (by positivity)
      linarith
    · linarith
  rw [hψ0]
  ring

/-- The corner error of one term: `|ψ(pn/Y) - ψ(r/Y)| ≤ 12 δ M₁(1)`. -/
theorem norm_corner_sub_le (hY : 0 < Y) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hψ : ∀ y, ψ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) (hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) {M : ℝ}
    (hM : ∀ y, ‖iteratedDeriv 1 ψ y‖ ≤ M) {j i p n : ℕ} (hp : p ∈ gridPiece δ j)
    (hn : n ∈ gridPiece δ i) :
    ‖ψ (((p * n : ℕ) : ℝ) / Y) - ψ (Real.exp (j * δ) * Real.exp (i * δ) / Y)‖ ≤ 12 * δ * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set r := Real.exp (j * δ) * Real.exp (i * δ) with hr
  obtain ⟨h1, h2⟩ := corner_lt_mul hp hn
  rw [← hr] at h1 h2
  have hr0 : 0 < r := by positivity
  by_cases hz : ψ (((p * n : ℕ) : ℝ) / Y) = 0 ∧ ψ (r / Y) = 0
  · rw [hz.1, hz.2, sub_zero, norm_zero]
    positivity
  -- one of the two values is nonzero, so `r ≤ 2Y`
  have hr2 : r ≤ 2 * Y := by
    rcases not_and_or.1 hz with h0 | h0
    · have := (hψ _ h0).2
      rw [div_le_iff₀ hY] at this
      linarith
    · have := (hψ _ h0).2
      rwa [div_le_iff₀ hY] at this
  have hexp : Real.exp (2 * δ) - 1 ≤ 4 * δ := by
    have := Real.abs_exp_sub_one_le (x := 2 * δ) (by rw [abs_of_nonneg (by linarith)]; linarith)
    rw [abs_of_nonneg (show 0 ≤ 2 * δ by linarith),
      abs_of_nonneg (show 0 ≤ Real.exp (2 * δ) - 1 by linarith [Real.add_one_le_exp (2 * δ)])]
      at this
    linarith
  refine (norm_sub_le_of_iteratedDeriv_one hψd hM _ _).trans ?_
  rw [← sub_div, abs_div, abs_of_pos hY, abs_of_pos (by linarith)]
  calc M * ((((p * n : ℕ) : ℝ) - r) / Y) ≤ M * ((Real.exp (2 * δ) - 1) * r / Y) := by
        gcongr
        linarith
    _ ≤ M * (4 * δ * (2 * Y) / Y) := by
        gcongr
    _ = 8 * δ * M := by field_simp; ring
    _ ≤ 12 * δ * M := by nlinarith

/-- **The corner error of a box (E6 separation).**
`∫_a^b |E_{ji}|² ≤ #𝒫_j² (b - a + 8N(1 + log N)) #(n-interval) (‖κ‖ Y⁻¹ 12δM₁(1) H_max)²`
with `N = ⌊e^{(i+1)δ}⌋`, by Cauchy–Schwarz over `p` and the mean value theorem in `n`. -/
theorem integral_boxErr_le {a b : ℝ} (hab : a ≤ b) (hY : 0 < Y) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hψ : ∀ y, ψ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) (hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) {M : ℝ}
    (hM : ∀ y, ‖iteratedDeriv 1 ψ y‖ ≤ M) {Kc Hc : ℝ} (hκ : ‖κ‖ ≤ Kc) (hH : ∀ n, ‖H n‖ ≤ Hc)
    (j i : ℕ) :
    ∫ t in a..b, ‖boxErr Y σ δ h k Ps κ H ψ j i t‖ ^ 2 ≤
      ((boxPrimes δ Ps j).card : ℝ) ^ 2 * ((b - a + 8 * grid δ (i + 1) *
        (1 + Real.log (grid δ (i + 1)))) * ((gridPiece δ i).card *
          (Kc * Y⁻¹ * (12 * δ * M) * Hc) ^ 2)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hKc : 0 ≤ Kc := (norm_nonneg _).trans hκ
  have hHc : 0 ≤ Hc := (norm_nonneg _).trans (hH 0)
  set s := boxPrimes δ Ps j with hs
  set N := grid δ (i + 1) with hN
  set c : ℕ → ℕ → ℂ := fun p n => κ * (Y : ℂ)⁻¹ *
    (ψ (((p * n : ℕ) : ℝ) / Y) - ψ (Real.exp (j * δ) * Real.exp (i * δ) / Y)) *
      twist h k (p * n) * ((p * n : ℕ) : ℂ) ^ ((σ : ℂ) * Complex.I) * H n with hc
  set c₀ := Kc * Y⁻¹ * (12 * δ * M) * Hc with hc₀
  have hrepr : ∀ t, boxErr Y σ δ h k Ps κ H ψ j i t = ∑ p ∈ s, (p : ℂ) ^ ((t : ℂ) * Complex.I) *
      ∑ n ∈ gridPiece δ i, c p n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
    intro t
    simp only [boxErr, hs, mul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun n _ => ?_
    have hcp : ((p * n : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) =
        (p : ℂ) ^ ((t : ℂ) * Complex.I) * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
      rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    rw [hcp, hc]
    ring
  have hcn : ∀ p ∈ s, ∀ n ∈ gridPiece δ i, ‖c p n‖ ≤ c₀ := by
    intro p hp n hn
    have hD := norm_corner_sub_le hY hδ0 hδ hψ hψd hM (mem_filter.1 hp).1 hn
    simp only [hc, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hY.le, norm_twist,
      mul_one]
    have hcp : ‖((p * n : ℕ) : ℂ) ^ ((σ : ℂ) * Complex.I)‖ ≤ 1 :=
      IntegerKernel.norm_natCast_cpow_I_mul_le σ (p * n)
    calc ‖κ‖ * Y⁻¹ * ‖ψ (((p * n : ℕ) : ℝ) / Y) - ψ (Real.exp (j * δ) * Real.exp (i * δ) / Y)‖ *
          ‖((p * n : ℕ) : ℂ) ^ ((σ : ℂ) * Complex.I)‖ * ‖H n‖
        ≤ Kc * Y⁻¹ * (12 * δ * M) * 1 * Hc := by
          gcongr
          · exact hH n
      _ = c₀ := by rw [hc₀, mul_one]
  have hS : gridPiece δ i ⊆ Icc 1 N := gridPiece_subset_Icc δ i
  have hN0 : 0 ≤ b - a + 8 * N * (1 + Real.log N) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast one_le_grid hδ0 (i + 1)
    have := Real.log_nonneg this
    nlinarith
  simp_rw [hrepr]
  have hcont : ∀ p ∈ s, Continuous fun t : ℝ => (p : ℂ) ^ ((t : ℂ) * Complex.I) *
      ∑ n ∈ gridPiece δ i, c p n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := fun p hp =>
    (continuous_natCast_cpow (gridPiece_pos (mem_filter.1 hp).1)).mul
      (continuous_sum_cpow (fun n hn => gridPiece_pos hn) _)
  have hCS := integral_norm_sum_sq_le s (fun _ => 1) (fun _ _ => norm_one.le) _ hcont hab
  simp only [one_mul] at hCS
  refine hCS.trans ?_
  have hper : ∀ p ∈ s, ∫ t in a..b, ‖(p : ℂ) ^ ((t : ℂ) * Complex.I) *
      ∑ n ∈ gridPiece δ i, c p n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      (b - a + 8 * N * (1 + Real.log N)) * ((gridPiece δ i).card * c₀ ^ 2) := by
    intro p hp
    have hQ := integral_norm_sum_cpow_sq_le N (gridPiece δ i) hS (c p) a b
    refine le_trans (intervalIntegral.integral_mono_on hab ((hcont p hp).norm.pow 2
      |>.intervalIntegrable a b) ((continuous_sum_cpow (fun n hn => gridPiece_pos hn) _).norm.pow
        2 |>.intervalIntegrable a b) fun t _ => ?_) (hQ.trans ?_)
    · simp only [Pi.pow_apply]
      rw [norm_mul, mul_pow]
      have := IntegerKernel.norm_natCast_cpow_I_mul_le t p
      have h1 : ‖(p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg ((p : ℂ) ^ ((t : ℂ) * Complex.I))]
      have h0 := sq_nonneg ‖∑ n ∈ gridPiece δ i, c p n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖
      nlinarith
    · gcongr
      calc ∑ n ∈ gridPiece δ i, ‖c p n‖ ^ 2 ≤ ∑ n ∈ gridPiece δ i, c₀ ^ 2 :=
            sum_le_sum fun n hn => pow_le_pow_left₀ (norm_nonneg _) (hcn p hp n hn) 2
        _ = (gridPiece δ i).card * c₀ ^ 2 := by rw [sum_const, nsmul_eq_mul]
  calc (s.card : ℝ) * ∑ p ∈ s, ∫ t in a..b, ‖(p : ℂ) ^ ((t : ℂ) * Complex.I) *
        ∑ n ∈ gridPiece δ i, c p n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2
      ≤ s.card * ∑ p ∈ s, (b - a + 8 * N * (1 + Real.log N)) *
          ((gridPiece δ i).card * c₀ ^ 2) := by
        gcongr with p hp
        exact hper p hp
    _ = (s.card : ℝ) ^ 2 * ((b - a + 8 * N * (1 + Real.log N)) *
          ((gridPiece δ i).card * c₀ ^ 2)) := by
        rw [sum_const, nsmul_eq_mul]
        ring

/-- **The corner term of a box.** `∫_a^b |W ∑_{β < k} A_β B_β|² ≤ |W|² k ∑_β ∫_a^b |A_β B_β|²`. -/
theorem integral_corner_le {a b : ℝ} (hab : a ≤ b) (W : ℂ) (A B : ℕ → ℝ → ℂ)
    (hA : ∀ β, Continuous (A β)) (hB : ∀ β, Continuous (B β)) :
    ∫ t in a..b, ‖W * ∑ β ∈ range k, A β t * B β t‖ ^ 2 ≤
      ‖W‖ ^ 2 * (k * ∑ β ∈ range k, ∫ t in a..b, ‖A β t * B β t‖ ^ 2) := by
  have hW : ∀ t, ‖W * ∑ β ∈ range k, A β t * B β t‖ ^ 2 =
      ‖W‖ ^ 2 * ‖∑ β ∈ range k, A β t * B β t‖ ^ 2 := fun t => by rw [norm_mul, mul_pow]
  simp_rw [hW]
  rw [intervalIntegral.integral_const_mul]
  gcongr
  have := integral_norm_sum_sq_le (range k) (fun _ => 1) (fun _ _ => norm_one.le)
    (fun β t => A β t * B β t) (fun β _ => (hA β).mul (hB β)) hab
  simpa only [one_mul, card_range] using this

end Decomposition

end Erdos408.TwoSided.ConstHigh
