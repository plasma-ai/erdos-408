import Erdos408.OneSided.Pairing.Endpoint
import Erdos408.OneSided.Pairing.Geometry

/-!
# From the moment to the pairing

PD §3.3 (`blueprint/one_sided_type_ii.md` §5.1). A bound on the determinant moment
`∑_P ⟨u_P, (𝒜𝒜^*)^R u_P⟩ ≤ UV L^{-EN}` gives `|⟨f, 𝒜 f⟩| ≪ UV L^{4C - E}`.

* Partition the positions into intervals of slope `P₂/P₁` of length `H/U²`, `H = d₀ Y`. A
  nonzero edge has `|det(P, Q)| ≪ H`, so only a bounded number of neighbouring intervals
  interact. Each interval holds `O(H)` primitive positions (pivot argument).
* Compression: the Gram matrix `⟨u_P, B^R u_Q⟩`, `B = 𝒜𝒜^*`, is positive semidefinite, so
  `⟨f_j, B^R f_j⟩ ≤ (trace) ∑_P |f(P)|² ≪ H sup|f|² d_j`.
* Spectral Hölder: `‖𝒜^* f‖² = ⟨f, B f⟩ ≤ ‖f‖^{2 - 2/R} ⟨f, B^R f⟩^{1/R}`.
* Hölder in the intervals with exponents `(2, 2R/(R-1), 2R)`, and `H^{1/(2R)} = O(1)` since
  `log H = O(L^{0.21})` and `R ≍ L^{1/2}`.
* The endpoint bounds `‖f‖² ≪ UV L^{4C}`, `sup|f| ≤ L^{2C}` (PD (3.18)).
-/

namespace Erdos408.OneSided

open Filter Finset Real
open scoped Matrix

variable {K : ℕ}

/-- The bounds of a position: `U ≤ P₁ ≤ 16U` and `P` is primitive. -/
theorem mem_positions_bounds {d : Data K} {Y d₀ : ℝ} (hU : 0 ≤ d₀ * Y * d.Hm) {P : ℕ × ℕ}
    (hP : P ∈ positions d Y d₀) :
    d₀ * Y * d.Hm ≤ P.1 ∧ (P.1 : ℝ) ≤ 16 * (d₀ * Y * d.Hm) ∧ Nat.Coprime P.1 P.2 := by
  unfold positions at hP
  rw [mem_filter, mem_product, mem_Icc] at hP
  exact ⟨Nat.ceil_le.1 hP.1.1.1, (Nat.le_floor_iff (by positivity)).1 hP.1.1.2, hP.2⟩

/-- The labels of a state have product at most `exp(4K L^{1/2})`: there are `K (J + 1)`
labels, each at most `exp(2 L^{a_hi})`, and `(J + 1) L^{a_hi} ≤ 2 L^{0.01 + a_hi}`. -/
theorem listProd_le_exp {C CX alo ahi g x : ℝ} {d : Data K} {Y d₀ : ℝ}
    (hd : Admissible C CX alo ahi g x d) (hahi : ahi < 1 / 5) (hL : 1 ≤ Real.log x)
    (t : State x d Y d₀) :
    (listProd t.1.2 : ℝ) ≤ Real.exp (4 * K * Real.log x ^ (1 / 2 : ℝ)) := by
  obtain ⟨-, hband, -, -⟩ := state_props t
  set L := Real.log x
  set J := padCount x
  -- each label is at most `exp(2 L^{a_hi})`
  have hlabel : ∀ i h, (t.1.2 i h : ℝ) ≤ Real.exp (2 * L ^ ahi) := by
    intro i h
    have h₁ := Real.rpow_le_rpow_of_exponent_le hL (hd.window i).2
    exact (le_exp_of_mem_band (hband i h)).trans (Real.exp_le_exp.2 (by linarith))
  -- `(J + 1) L^{a_hi} ≤ 2 L^{1/2}`
  have hJ : (J : ℝ) + 1 ≤ 2 * L ^ (1 / 100 : ℝ) := by
    have h₁ : (J : ℝ) ≤ L ^ (1 / 100 : ℝ) := Nat.floor_le (by positivity)
    have h₂ : 1 ≤ L ^ (1 / 100 : ℝ) := Real.one_le_rpow hL (by norm_num)
    linarith
  have hexp : L ^ (1 / 100 : ℝ) * L ^ ahi ≤ L ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hLa : 0 ≤ L ^ ahi := by positivity
  have hJa : ((J : ℝ) + 1) * L ^ ahi ≤ 2 * L ^ (1 / 2 : ℝ) := by nlinarith
  unfold listProd
  push_cast
  calc ∏ i, ∏ h, (t.1.2 i h : ℝ) ≤ ∏ _i : Fin K, ∏ _h : Fin (J + 1), Real.exp (2 * L ^ ahi) :=
        prod_le_prod₀ (fun i _ => prod_nonneg fun h _ => Nat.cast_nonneg _) fun i _ =>
          prod_le_prod₀ (fun h _ => Nat.cast_nonneg _) fun h _ => hlabel i h
    _ = Real.exp (K * ((J + 1 : ℕ) * (2 * L ^ ahi))) := by
        rw [prod_const, prod_const, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin,
          ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    _ ≤ Real.exp (4 * K * L ^ (1 / 2 : ℝ)) := by
        refine Real.exp_le_exp.2 ?_
        have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
        push_cast
        nlinarith

/-- PD (3.20): a moment bound with precision `E` bounds the pairing by `UV L^{4C - E}`. -/
theorem eventually_pairing_of_moment {q C CX alo ahi g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (hahi : ahi < 1 / 5) (hg : 0 < g) (A₀ E : ℝ) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ‖detMoment q A₀ x d (2 ^ j) (2 ^ k)‖ ≤
          2 ^ k * 2 ^ j * d.X * Real.log x ^ (-(E * (2 * momentPower x : ℕ))) →
        ‖pairing q A₀ x d (2 ^ j) (2 ^ k)‖ ≤
          C₀ * (2 ^ k * 2 ^ j * d.X) * Real.log x ^ (4 * C - E) := by
  refine ⟨21 * 64 * 8721 * Real.exp (4 * K), ?_⟩
  filter_upwards [eventually_band_disjoint hg, eventually_not_dvd_of_isRough hahi,
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 1]
    with x hE1 hE2 hL hx1 d hd j k hmom
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  -- band facts and the scales
  have hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hE1 _ _ (hd.gap i j h)
    · exact (hE1 _ _ (hd.gap j i h)).symm
  have hrough : ∀ i, ∀ p ∈ band x (d.a i), ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ p ∣ m :=
    fun i => hE2 (d.a i) (hd.window i).2
  have hγ : 0 < d.γ := (Real.rpow_pos_of_pos hL0 _).trans_le hd.γ_ge
  have hHm : 1 ≤ d.Hm := (Real.one_le_rpow hx1 hγ.le).trans hd.Hm_ge
  have hHn : 1 ≤ d.Hn := (Real.one_le_rpow hx1 hγ.le).trans hd.Hn_ge
  set Y : ℝ := 2 ^ j with hY
  set d₀ : ℝ := 2 ^ k with hd₀
  have hY0 : 0 < Y := by positivity
  have hd₀0 : 0 < d₀ := by positivity
  set H := d₀ * Y with hH
  have hH1 : 1 ≤ H := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two)
    (one_le_pow₀ one_le_two)
  set U := d₀ * Y * d.Hm with hU
  have hU0 : 0 < U := by positivity
  set Z : ℝ := 2 ^ k * 2 ^ j * d.X with hZ
  have hZU : Z = d₀ * Y * d.Hm * d.Hn := by
    rw [hZ, Data.X]
    ring
  have hZ0 : 0 < Z := by
    rw [hZU]
    positivity
  set C₀ := 21 * 64 * 8721 * Real.exp (4 * K) with hC₀
  -- `R = M - 1` and `L^{1/2} ≤ 2M`
  obtain ⟨R, hR⟩ : ∃ R, momentPower x = R + 1 := by
    have : 0 < momentPower x := Nat.ceil_pos.2 (by positivity)
    exact ⟨momentPower x - 1, by omega⟩
  have hLR : L ^ (1 / 2 : ℝ) ≤ 2 * (R + 1) := by
    have h₁ : L ^ (1 / 2 : ℝ) / 2 ≤ (momentPower x : ℝ) := Nat.le_ceil _
    rw [hR] at h₁
    push_cast at h₁
    linarith
  -- the pairing vanishes unless `𝒯 ≠ 0`
  by_cases hT : ∃ t t' : State x d Y d₀, rowOp q A₀ x d Y d₀ t t' ≠ 0
  swap
  · have hA : edgeOp q A₀ x d Y d₀ = 0 := by
      ext s s'
      by_contra h
      obtain ⟨t, t', -, -, h'⟩ := exists_rowOp_ne_zero h
      exact hT ⟨t, t', h'⟩
    rw [pairing, hA, Matrix.zero_mulVec]
    simp only [stateInner, Pi.zero_apply, mul_zero, sum_const_zero, norm_zero]
    positivity
  obtain ⟨t, t', ht⟩ := hT
  -- `H ≤ exp(8 K M)`
  have hHexp : H ≤ Real.exp (8 * K * (R + 1)) := by
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    calc H ≤ listProd t.1.2 := le_listProd_of_rowOp_ne_zero hY0 ht
      _ ≤ Real.exp (4 * K * L ^ (1 / 2 : ℝ)) := listProd_le_exp hd hahi hL t
      _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)
  -- the hypotheses of the cell bound
  set N := ⌊17 * (512 * H + 1)⌋₊ with hN
  set σ := L ^ (4 * C) with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hpos : ∀ s : State x d Y d₀, U ≤ s.1.1.1 := fun s =>
    (mem_positions_bounds hU0.le (state_props s).1).1
  have hA : ∀ s s', edgeOp q A₀ x d Y d₀ s s' ≠ 0 →
      |slopeCell (U ^ 2 / H) s.1.1 - slopeCell (U ^ 2 / H) s'.1.1| ≤ ((10 : ℕ) : ℤ) := by
    intro s s' h
    obtain ⟨u, u', hu, hu', h'⟩ := exists_rowOp_ne_zero h
    have hdet := abs_det_lt_of_rowOp_ne_zero hY0 h'
    rw [hu, hu'] at hdet
    exact_mod_cast abs_slopeCell_sub_le hU0 (by positivity) (hpos s) (hpos s') hdet.le
  have hcellN : ∀ c, ((univ.image fun s : State x d Y d₀ => s.1.1).filter
      fun P => slopeCell (U ^ 2 / H) P = c).card ≤ N := by
    intro c
    refine (card_le_card (filter_subset_filter _ fun P hP => ?_)).trans
      (Nat.le_floor (card_slopeCell_le hU0 (by positivity) (positions d Y d₀)
        (fun P hP => mem_positions_bounds hU0.le hP) c))
    obtain ⟨s, -, rfl⟩ := mem_image.1 hP
    exact (state_props s).1
  have hcells := norm_pow_le_of_cells (edgeOp q A₀ x d Y d₀) (fun s => s.1.1)
    (slopeCell (U ^ 2 / H)) (endVec x d Y d₀) hσ0 R hA
    (fun s s' h => endVec_eq_of_pos_eq hd hdisj hrough (by linarith) h) hcellN
    (fun s => norm_endVec_sq_le hd hL0 s)
  -- the pairing and the moment through the unnormalized forms
  set m := stateMass x d with hm
  have hm0 : 0 ≤ m := stateMass_nonneg x d
  set P := ‖star (endVec x d Y d₀) ⬝ᵥ (edgeOp q A₀ x d Y d₀ *ᵥ endVec x d Y d₀)‖ with hP
  set S := sqNorm (endVec x d Y d₀) with hS
  set ρ := ∑ s : State x d Y d₀, ∑ s' : State x d Y d₀, if s.1.1 = s'.1.1 then
    ((edgeOp q A₀ x d Y d₀ * (edgeOp q A₀ x d Y d₀)ᴴ) ^ (R + 1)) s s' else 0 with hρ
  have hpair : ‖pairing q A₀ x d Y d₀‖ = m * P := by
    rw [hP, ← Real.norm_of_nonneg hm0, ← Complex.norm_real, ← norm_mul]
    rfl
  have hmoment : ‖detMoment q A₀ x d Y d₀‖ = m * ‖ρ‖ := by
    have h₁ : detMoment q A₀ x d Y d₀ = (m : ℂ) * ρ := by
      unfold detMoment
      rw [hR]
    rw [h₁, norm_mul, Complex.norm_real, Real.norm_of_nonneg hm0]
  set n := 2 * (R + 1) with hn
  have hn0 : n ≠ 0 := by omega
  have hmom' : m * ‖ρ‖ ≤ Z * L ^ (-(E * (n : ℝ))) := by
    rw [← hmoment]
    rw [hR] at hmom
    exact hmom
  have hS' : m * S ≤ 64 * σ * Z := by
    rw [hZU]
    exact stateMass_mul_sqNorm_endVec_le hd hdisj hHm hHn (by positivity) hσ0
      fun s => norm_endVec_sq_le hd hL0 s
  have hNH : (N : ℝ) ≤ 8721 * Real.exp (8 * K * (R + 1)) := by
    have h₁ : (N : ℝ) ≤ 17 * (512 * H + 1) := Nat.floor_le (by positivity)
    linarith
  -- `σ^{2M} L^{-2ME} = (L^{4C - E})^{2M}`
  have hrpow : σ ^ n * L ^ (-(E * (n : ℝ))) = (L ^ (4 * C - E)) ^ n := by
    rw [hσ, ← Real.rpow_mul_natCast hL0.le, ← Real.rpow_mul_natCast hL0.le,
      ← Real.rpow_add hL0]
    congr 1
    ring
  -- `21^M 64^{2M - 1} N ≤ C₀^{2M}`, using `N ≪ H ≤ exp(8 K M)`
  have hnum : (21 : ℝ) ^ (R + 1) * 64 ^ (2 * R + 1) * N ≤ C₀ ^ n := by
    have h₁ : (21 : ℝ) ^ (R + 1) ≤ 21 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    have h₂ : (64 : ℝ) ^ (2 * R + 1) ≤ 64 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    have h₃ : (N : ℝ) ≤ 8721 ^ n * Real.exp (4 * K) ^ n := by
      have h₄ : (8721 : ℝ) ≤ 8721 ^ n := le_self_pow₀ (by norm_num) hn0
      have h₅ : Real.exp (8 * K * (R + 1)) = Real.exp (4 * K) ^ n := by
        rw [← Real.exp_nat_mul, hn]
        push_cast
        ring_nf
      rw [← h₅]
      exact hNH.trans (mul_le_mul_of_nonneg_right h₄ (Real.exp_pos _).le)
    rw [hC₀, mul_pow, mul_pow, mul_pow]
    calc (21 : ℝ) ^ (R + 1) * 64 ^ (2 * R + 1) * N
        ≤ 21 ^ n * 64 ^ n * (8721 ^ n * Real.exp (4 * K) ^ n) :=
          mul_le_mul (mul_le_mul h₁ h₂ (by positivity) (by positivity)) h₃ (Nat.cast_nonneg _)
            (by positivity)
      _ = _ := by ring
  have hP0 : 0 ≤ P := norm_nonneg _
  have hS0 : 0 ≤ S := sqNorm_nonneg _
  have hρ0 : 0 ≤ ‖ρ‖ := norm_nonneg _
  have hNσ : 0 ≤ (N : ℝ) * σ := mul_nonneg (Nat.cast_nonneg _) hσ0
  have hσZ : 0 ≤ 64 * σ * Z := mul_nonneg (mul_nonneg (by norm_num) hσ0) hZ0.le
  rw [hpair]
  refine le_of_pow_le_pow_left₀ hn0
    (mul_nonneg (mul_nonneg (by positivity) hZ0.le) (by positivity)) ?_
  calc (m * P) ^ n = m ^ n * P ^ n := mul_pow _ _ _
    _ ≤ m ^ n * ((2 * ((10 : ℕ) : ℝ) + 1) ^ (R + 1) * S ^ (2 * R + 1) * (N * σ) * ‖ρ‖) :=
        mul_le_mul_of_nonneg_left hcells (pow_nonneg hm0 _)
    _ = 21 ^ (R + 1) * (m * S) ^ (2 * R + 1) * (N * σ) * (m * ‖ρ‖) := by
        rw [hn]
        push_cast
        ring
    _ ≤ 21 ^ (R + 1) * (64 * σ * Z) ^ (2 * R + 1) * (N * σ) * (Z * L ^ (-(E * (n : ℝ)))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg hm0 hS0) hS' _) (by positivity)) hNσ) hmom'
          (mul_nonneg hm0 hρ0) (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hσZ _)) hNσ)
    _ = (21 ^ (R + 1) * 64 ^ (2 * R + 1) * N) * (σ ^ n * L ^ (-(E * (n : ℝ)))) * Z ^ n := by
        rw [hn]
        ring
    _ ≤ C₀ ^ n * (σ ^ n * L ^ (-(E * (n : ℝ)))) * Z ^ n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnum
          (mul_nonneg (pow_nonneg hσ0 _) (by positivity))) (pow_nonneg hZ0.le _)
    _ = (C₀ * Z * L ^ (4 * C - E)) ^ n := by
        rw [hrpow]
        ring

end Erdos408.OneSided
