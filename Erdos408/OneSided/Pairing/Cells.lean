module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Cells, compression and spectral Hölder

The finite-dimensional part of PD §3.3 (`blueprint/one_sided_type_ii.md` §5.1), for an
arbitrary complex matrix `A` on a finite index type, with the unnormalized inner product
`⟨u, v⟩ = ∑ ū v` and `B = A A^*`.

* `halfPow A R` is the alternating product `⋯ A A^* A A^*` of `R` factors, so that
  `(halfPow A R)^* halfPow A R = B^R`.
* Spectral Hölder: the moments `m_k = ∑_c ‖halfPow A k v_c‖²` of a family of vectors are
  log-convex, so `m_1^R ≤ m_0^{R - 1} m_R`. Summing over a family is Hölder in the family.
* Compression: for `v = ∑_P F(P) u_P`, `‖W v‖² ≤ (∑_P |F(P)|²) ∑_P ‖W u_P‖²`.
* `norm_pow_le_of_cells`: if the indices carry positions `π`, the positions carry cells,
  `A` joins only cells at distance at most `w`, and `f` is constant on positions, then
  `|⟨f, A f⟩|^{2R} ≤ (2w + 1)^R ‖f‖^{2(2R - 1)} N sup|f|² ∑_P ⟨u_P, B^R u_P⟩`, where `N`
  bounds the number of positions in a cell.
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset
open scoped Matrix

variable {ι : Type*} [Fintype ι]

/-! ### Vectors -/

/-- The squared norm `‖v‖² = ∑ |v_i|²`. -/
noncomputable def sqNorm (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- `‖v‖² ≥ 0`. -/
theorem sqNorm_nonneg (v : ι → ℂ) : 0 ≤ sqNorm v :=
  sum_nonneg fun _ _ => sq_nonneg _

/-- `⟨v, v⟩ = ‖v‖²`. -/
theorem star_dotProduct_self (v : ι → ℂ) : star v ⬝ᵥ v = (sqNorm v : ℂ) := by
  simp only [dotProduct, sqNorm, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  exact sum_congr rfl fun i _ => Complex.conj_mul' (v i)

/-- Cauchy–Schwarz: `|⟨u, v⟩|² ≤ ‖u‖² ‖v‖²`. -/
theorem norm_star_dotProduct_sq_le (u v : ι → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ sqNorm u * sqNorm v := by
  have h : ‖star u ⬝ᵥ v‖ ≤ ∑ i, ‖u i‖ * ‖v i‖ := by
    refine (norm_sum_le _ _).trans_eq (sum_congr rfl fun i _ => ?_)
    rw [Pi.star_apply, norm_mul, norm_star]
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (sum_mul_sq_le_sq_mul_sq _ _ _)

/-- The adjoint: `⟨u, M v⟩ = ⟨M^* u, v⟩`. -/
theorem star_dotProduct_mulVec (M : Matrix ι ι ℂ) (u v : ι → ℂ) :
    star u ⬝ᵥ (M *ᵥ v) = star (Mᴴ *ᵥ u) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

/-- Compression: `‖∑_P c_P v_P‖² ≤ (∑_P |c_P|²) ∑_P ‖v_P‖²`. -/
theorem sqNorm_sum_smul_le {κ : Type*} (T : Finset κ) (c : κ → ℂ) (v : κ → ι → ℂ) :
    sqNorm (∑ P ∈ T, c P • v P) ≤ (∑ P ∈ T, ‖c P‖ ^ 2) * ∑ P ∈ T, sqNorm (v P) := by
  unfold sqNorm
  rw [sum_comm, mul_sum]
  refine sum_le_sum fun i _ => ?_
  have h : ‖(∑ P ∈ T, c P • v P) i‖ ≤ ∑ P ∈ T, ‖c P‖ * ‖v P i‖ := by
    rw [Finset.sum_apply]
    refine (norm_sum_le _ _).trans_eq (sum_congr rfl fun P _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (sum_mul_sq_le_sq_mul_sq _ _ _)

/-! ### Alternating powers -/

/-- The alternating product `halfPow A R = ⋯ A A^* A A^*` of `R` factors. -/
noncomputable def halfPow [DecidableEq ι] (A : Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | k + 1 => (if Even k then Aᴴ else A) * halfPow A k

variable [DecidableEq ι]

/-- Consecutive factors are adjoint: `halfPow A (k + 2) = M^* halfPow A (k + 1)` with
`halfPow A (k + 1) = M halfPow A k`. -/
theorem halfPow_add_two (A : Matrix ι ι ℂ) (k : ℕ) :
    halfPow A (k + 2) = (if Even k then Aᴴ else A)ᴴ * halfPow A (k + 1) := by
  rw [halfPow]
  congr 1
  by_cases hk : Even k
  · rw [ite_eq_right_iff.2 fun h => absurd h (Nat.even_add_one.not.2 (not_not.2 hk)),
      ite_eq_left_iff.2 fun h => absurd hk h, Matrix.conjTranspose_conjTranspose]
  · rw [ite_eq_left_iff.2 fun h => absurd (Nat.even_add_one.2 hk) h,
      ite_eq_right_iff.2 fun h => absurd h hk]

/-- `halfPow A (2r) = B^r` and `halfPow A (2r + 1) = A^* B^r`. -/
theorem halfPow_two_mul (A : Matrix ι ι ℂ) (r : ℕ) :
    halfPow A (2 * r) = (A * Aᴴ) ^ r ∧ halfPow A (2 * r + 1) = Aᴴ * (A * Aᴴ) ^ r := by
  induction r with
  | zero => simp [halfPow]
  | succ r ih =>
    have h₁ : halfPow A (2 * (r + 1)) = (A * Aᴴ) ^ (r + 1) := by
      rw [show 2 * (r + 1) = 2 * r + 1 + 1 by ring, halfPow, ih.2,
        ite_eq_right_iff.2 fun h => absurd h (by simp [parity_simps]),
        pow_succ', Matrix.mul_assoc]
    refine ⟨h₁, ?_⟩
    rw [halfPow, h₁, ite_eq_left_iff.2 fun h => absurd (by simp [parity_simps]) h]

/-- `(halfPow A R)^* halfPow A R = B^R`. -/
theorem conjTranspose_halfPow_mul_halfPow (A : Matrix ι ι ℂ) (R : ℕ) :
    (halfPow A R)ᴴ * halfPow A R = (A * Aᴴ) ^ R := by
  have hB : (A * Aᴴ)ᴴ = A * Aᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' R
  · rw [(halfPow_two_mul A r).1, Matrix.conjTranspose_pow, hB, ← pow_add, two_mul]
  · rw [(halfPow_two_mul A r).2, Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hB,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc A,
      ← pow_succ', ← pow_add]
    ring_nf

/-! ### Spectral Hölder -/

/-- A nonnegative log-convex sequence satisfies `m_1^R ≤ m_0^{R - 1} m_R`. -/
theorem pow_le_of_logConvex {m : ℕ → ℝ} (hm : ∀ k, 0 ≤ m k)
    (hlog : ∀ k, m (k + 1) ^ 2 ≤ m k * m (k + 2)) (R : ℕ) :
    m 1 ^ (R + 1) ≤ m 0 ^ R * m (R + 1) := by
  -- the ratios increase: `m_1 m_{k+1} ≤ m_0 m_{k+2}`
  have hratio : ∀ k, m 1 * m (k + 1) ≤ m 0 * m (k + 2) := by
    intro k
    induction k with
    | zero => simpa [sq] using hlog 0
    | succ k ih =>
      rcases (hm (k + 2)).eq_or_lt with h | h
      · rw [← h, mul_zero]
        exact mul_nonneg (hm 0) (hm _)
      · have h₁ := hlog (k + 1)
        have h₂ := mul_le_mul_of_nonneg_right ih (hm (k + 3))
        refine le_of_mul_le_mul_right ?_ h
        nlinarith [hm 1]
  induction R with
  | zero => simp
  | succ R ih =>
    calc m 1 ^ (R + 2) = m 1 ^ (R + 1) * m 1 := pow_succ _ _
      _ ≤ m 0 ^ R * m (R + 1) * m 1 := mul_le_mul_of_nonneg_right ih (hm 1)
      _ = m 0 ^ R * (m 1 * m (R + 1)) := by ring
      _ ≤ m 0 ^ R * (m 0 * m (R + 2)) :=
          mul_le_mul_of_nonneg_left (hratio R) (pow_nonneg (hm 0) _)
      _ = m 0 ^ (R + 1) * m (R + 2) := by ring

/-- Spectral Hölder for a family of vectors: with `m_k = ∑_c ‖halfPow A k v_c‖²`,
`(∑_c ‖A^* v_c‖²)^R ≤ (∑_c ‖v_c‖²)^{R - 1} m_R`. -/
theorem sum_sqNorm_pow_le {κ : Type*} (A : Matrix ι ι ℂ) (T : Finset κ) (v : κ → ι → ℂ)
    (R : ℕ) :
    (∑ c ∈ T, sqNorm (Aᴴ *ᵥ v c)) ^ (R + 1) ≤
      (∑ c ∈ T, sqNorm (v c)) ^ R * ∑ c ∈ T, sqNorm (halfPow A (R + 1) *ᵥ v c) := by
  set m : ℕ → ℝ := fun k => ∑ c ∈ T, sqNorm (halfPow A k *ᵥ v c) with hm
  have hm0 : ∀ k, 0 ≤ m k := fun k => sum_nonneg fun c _ => sqNorm_nonneg _
  -- log-convexity: `‖w_{k+1}‖² = ⟨w_k, w_{k+2}⟩`, then Cauchy–Schwarz
  have hlog : ∀ k, m (k + 1) ^ 2 ≤ m k * m (k + 2) := by
    intro k
    set M := if Even k then Aᴴ else A
    have hterm : ∀ c, sqNorm (halfPow A (k + 1) *ᵥ v c) ≤
        √(sqNorm (halfPow A k *ᵥ v c)) * √(sqNorm (halfPow A (k + 2) *ᵥ v c)) := by
      intro c
      rw [← Real.sqrt_mul (sqNorm_nonneg _)]
      refine Real.le_sqrt_of_sq_le ?_
      have heq : star (halfPow A k *ᵥ v c) ⬝ᵥ (halfPow A (k + 2) *ᵥ v c) =
          (sqNorm (halfPow A (k + 1) *ᵥ v c) : ℂ) := by
        rw [halfPow_add_two, ← Matrix.mulVec_mulVec, star_dotProduct_mulVec,
          Matrix.conjTranspose_conjTranspose, Matrix.mulVec_mulVec, ← halfPow,
          star_dotProduct_self]
      have := norm_star_dotProduct_sq_le (halfPow A k *ᵥ v c) (halfPow A (k + 2) *ᵥ v c)
      rwa [heq, Complex.norm_real, Real.norm_of_nonneg (sqNorm_nonneg _)] at this
    have hsum : m (k + 1) ≤ √(m k) * √(m (k + 2)) :=
      (sum_le_sum fun c _ => hterm c).trans
        (Real.sum_sqrt_mul_sqrt_le T (fun c => sqNorm_nonneg _) fun c => sqNorm_nonneg _)
    calc m (k + 1) ^ 2 ≤ (√(m k) * √(m (k + 2))) ^ 2 :=
          pow_le_pow_left₀ (hm0 _) hsum 2
      _ = m k * m (k + 2) := by
          rw [mul_pow, Real.sq_sqrt (hm0 _), Real.sq_sqrt (hm0 _)]
  have h := pow_le_of_logConvex hm0 hlog R
  have h0 : m 0 = ∑ c ∈ T, sqNorm (v c) := by simp [hm, halfPow]
  have h1 : m 1 = ∑ c ∈ T, sqNorm (Aᴴ *ᵥ v c) := by simp [hm, halfPow]
  rwa [h0, h1] at h

/-! ### Cells -/

variable {β : Type*} [DecidableEq β]

omit [DecidableEq ι] in
/-- The moment `∑_P ⟨u_P, W^* W u_P⟩ = ∑_P ‖W u_P‖²`, where `u_P` is one at the indices of
position `P` and the left side sums the entries of `W^* W` between indices of equal
position. -/
theorem sum_ite_conjTranspose_mul (W : Matrix ι ι ℂ) (π : ι → β) :
    ∑ s, ∑ s', (if π s = π s' then (Wᴴ * W) s s' else 0) =
      ((∑ P ∈ univ.image π, sqNorm (W *ᵥ fun s => if π s = P then 1 else 0) : ℝ) : ℂ) := by
  -- `‖W u_P‖² = ⟨u_P, W^* W u_P⟩`
  have key : ∀ P, (sqNorm (W *ᵥ fun s => if π s = P then 1 else 0) : ℂ) =
      ∑ s, ∑ s', if π s = P then (if π s' = P then (Wᴴ * W) s s' else 0) else 0 := by
    intro P
    have h := star_dotProduct_mulVec Wᴴ (fun s => if π s = P then 1 else 0)
      (W *ᵥ fun s => if π s = P then 1 else 0)
    rw [Matrix.conjTranspose_conjTranspose, Matrix.mulVec_mulVec] at h
    rw [← star_dotProduct_self, ← h]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, mul_sum]
    refine sum_congr rfl fun s _ => sum_congr rfl fun s' _ => ?_
    split_ifs <;> simp
  push_cast
  simp_rw [key]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun s' _ => ?_
  rw [sum_ite_eq, ite_eq_left (mem_image_of_mem π (mem_univ s))]
  by_cases h : π s = π s'
  · rw [ite_eq_left h.symm, ite_eq_left h]
  · rw [ite_eq_right fun h' => h h'.symm, ite_eq_right h]

/-- PD §3.3 for an abstract matrix. The indices carry positions `π`, the positions carry
cells, `A` joins only cells at distance at most `w`, at most `N` positions lie in a cell, and
`f` is constant on positions with `|f|² ≤ σ`. Then
`|⟨f, A f⟩|^{2M} ≤ (2w + 1)^M ‖f‖^{2(2M - 1)} N σ |∑_P ⟨u_P, (A A^*)^M u_P⟩|`
with `M = R + 1`. -/
theorem norm_pow_le_of_cells (A : Matrix ι ι ℂ) (π : ι → β) (cell : β → ℤ) (f : ι → ℂ)
    {w N : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (R : ℕ)
    (hA : ∀ s s', A s s' ≠ 0 → |cell (π s) - cell (π s')| ≤ w)
    (hf : ∀ s s', π s = π s' → f s = f s')
    (hN : ∀ j, ((univ.image π).filter fun P => cell P = j).card ≤ N)
    (hfσ : ∀ s, ‖f s‖ ^ 2 ≤ σ) :
    ‖star f ⬝ᵥ (A *ᵥ f)‖ ^ (2 * (R + 1)) ≤
      (2 * w + 1) ^ (R + 1) * sqNorm f ^ (2 * R + 1) * (N * σ) *
        ‖∑ s, ∑ s', if π s = π s' then ((A * Aᴴ) ^ (R + 1)) s s' else 0‖ := by
  set Js := univ.image fun s => cell (π s) with hJs
  set Ps := univ.image π with hPs
  set fj : ℤ → ι → ℂ := fun j s => if cell (π s) = j then f s else 0 with hfj
  set gj : ℤ → ι → ℂ := fun j s => if |cell (π s) - j| ≤ w then f s else 0 with hgj
  set W := halfPow A (R + 1) with hW
  set u : β → ι → ℂ := fun P s => if π s = P then 1 else 0 with hu
  -- split the pairing into cells; `A f` on cell `j` only sees the neighbours `g_j`
  have hsplit : star f ⬝ᵥ (A *ᵥ f) = ∑ j ∈ Js, star (fj j) ⬝ᵥ (A *ᵥ gj j) := by
    have hloc : ∀ s, (A *ᵥ gj (cell (π s))) s = (A *ᵥ f) s := by
      intro s
      simp only [Matrix.mulVec, dotProduct]
      refine sum_congr rfl fun s' _ => ?_
      by_cases h : A s s' = 0
      · rw [h, zero_mul, zero_mul]
      · have h' : |cell (π s') - cell (π s)| ≤ w := by
          rw [abs_sub_comm]
          exact hA s s' h
        simp only [hgj]
        rw [ite_eq_left h']
    simp only [dotProduct]
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    simp only [hfj, Pi.star_apply, apply_ite star, star_zero, ite_mul, zero_mul]
    rw [sum_ite_eq, ite_eq_left (mem_image_of_mem _ (mem_univ s)), hloc]
  -- Cauchy–Schwarz in each cell and over the cells
  have hcs : ‖star f ⬝ᵥ (A *ᵥ f)‖ ^ 2 ≤
      (∑ j ∈ Js, sqNorm (Aᴴ *ᵥ fj j)) * ∑ j ∈ Js, sqNorm (gj j) := by
    have h₁ : ∀ j, ‖star (fj j) ⬝ᵥ (A *ᵥ gj j)‖ ≤
        √(sqNorm (Aᴴ *ᵥ fj j)) * √(sqNorm (gj j)) := by
      intro j
      rw [star_dotProduct_mulVec, ← Real.sqrt_mul (sqNorm_nonneg _)]
      exact Real.le_sqrt_of_sq_le (norm_star_dotProduct_sq_le _ _)
    have h₂ := (norm_sum_le _ _).trans ((sum_le_sum fun j _ => h₁ j).trans
      (Real.sum_sqrt_mul_sqrt_le Js (fun j => sqNorm_nonneg _) fun j => sqNorm_nonneg _))
    rw [hsplit]
    calc _ ≤ (√(∑ j ∈ Js, sqNorm (Aᴴ *ᵥ fj j)) * √(∑ j ∈ Js, sqNorm (gj j))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h₂ 2
      _ = _ := by
          rw [mul_pow, Real.sq_sqrt (sum_nonneg fun _ _ => sqNorm_nonneg _),
            Real.sq_sqrt (sum_nonneg fun _ _ => sqNorm_nonneg _)]
  -- bounded overlap: each index lies in at most `2w + 1` neighbourhoods
  have hoverlap : ∑ j ∈ Js, sqNorm (gj j) ≤ (2 * w + 1) * sqNorm f := by
    simp only [sqNorm, hgj]
    rw [sum_comm, mul_sum]
    refine sum_le_sum fun s _ => ?_
    simp_rw [apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero, zero_pow two_ne_zero]
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hsub : Js.filter (fun j => |cell (π s) - j| ≤ w) ⊆
        Icc (cell (π s) - w) (cell (π s) + w) := by
      intro j hj
      have := abs_le.1 (mem_filter.1 hj).2
      rw [mem_Icc]
      constructor <;> linarith
    have hcard := card_le_card hsub
    rw [Int.card_Icc, show cell (π s) + w + 1 - (cell (π s) - w) = ((2 * w + 1 : ℕ) : ℤ) by
      push_cast; ring, Int.toNat_natCast] at hcard
    exact_mod_cast hcard
  -- the cells partition `f`
  have hpart : ∑ j ∈ Js, sqNorm (fj j) = sqNorm f := by
    simp only [sqNorm, hfj]
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    simp_rw [apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero, zero_pow two_ne_zero]
    rw [sum_ite_eq, ite_eq_left (mem_image_of_mem _ (mem_univ s))]
  -- `f = F ∘ π`
  set F : β → ℂ := fun P => if h : ∃ s, π s = P then f h.choose else 0 with hF
  have hFπ : ∀ s, F (π s) = f s := by
    intro s
    have h : ∃ s', π s' = π s := ⟨s, rfl⟩
    rw [hF]
    dsimp only
    rw [dite_eq_left h]
    exact hf _ _ h.choose_spec
  -- compression in each cell
  have hcomp : ∀ j, sqNorm (W *ᵥ fj j) ≤
      (N * σ) * ∑ P ∈ Ps.filter (fun P => cell P = j), sqNorm (W *ᵥ u P) := by
    intro j
    have hfj' : fj j = ∑ P ∈ Ps.filter (fun P => cell P = j), F P • u P := by
      funext s
      simp only [hfj, hu, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero]
      rw [sum_ite_eq]
      by_cases h : cell (π s) = j
      · rw [ite_eq_left h, ite_eq_left (mem_filter.2 ⟨mem_image_of_mem _ (mem_univ _), h⟩),
          hFπ]
      · rw [ite_eq_right h, ite_eq_right
          (show π s ∉ Ps.filter (fun P => cell P = j) from fun hm => h (mem_filter.1 hm).2)]
    rw [hfj', Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul]
    refine (sqNorm_sum_smul_le _ _ _).trans
      (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sqNorm_nonneg _))
    have hle : ∀ P ∈ Ps.filter (fun P => cell P = j), ‖F P‖ ^ 2 ≤ σ := by
      intro P hP
      obtain ⟨s, -, rfl⟩ := mem_image.1 (mem_filter.1 hP).1
      rw [hFπ]
      exact hfσ s
    calc _ ≤ (Ps.filter (fun P => cell P = j)).card • σ := sum_le_card_nsmul _ _ _ hle
      _ ≤ N * σ := by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN j) hσ
  -- the moment
  have hmom : ∑ j ∈ Js, ∑ P ∈ Ps.filter (fun P => cell P = j), sqNorm (W *ᵥ u P) =
      ‖∑ s, ∑ s', if π s = π s' then ((A * Aᴴ) ^ (R + 1)) s s' else 0‖ := by
    rw [sum_fiberwise_of_maps_to fun P hP => ?_, ← conjTranspose_halfPow_mul_halfPow,
      sum_ite_conjTranspose_mul, Complex.norm_real,
      Real.norm_of_nonneg (sum_nonneg fun _ _ => sqNorm_nonneg _)]
    obtain ⟨s, -, rfl⟩ := mem_image.1 hP
    exact mem_image_of_mem _ (mem_univ s)
  -- assemble
  have hhold := sum_sqNorm_pow_le A Js fj R
  rw [hpart] at hhold
  have hW' : ∑ j ∈ Js, sqNorm (W *ᵥ fj j) ≤ (N * σ) *
      ‖∑ s, ∑ s', if π s = π s' then ((A * Aᴴ) ^ (R + 1)) s s' else 0‖ := by
    rw [← hmom, mul_sum]
    exact sum_le_sum fun j _ => hcomp j
  have hNσ : 0 ≤ (N : ℝ) * σ := mul_nonneg (Nat.cast_nonneg _) hσ
  calc ‖star f ⬝ᵥ (A *ᵥ f)‖ ^ (2 * (R + 1))
      = (‖star f ⬝ᵥ (A *ᵥ f)‖ ^ 2) ^ (R + 1) := by rw [pow_mul]
    _ ≤ ((∑ j ∈ Js, sqNorm (Aᴴ *ᵥ fj j)) * ∑ j ∈ Js, sqNorm (gj j)) ^ (R + 1) :=
        pow_le_pow_left₀ (sq_nonneg _) hcs _
    _ = (∑ j ∈ Js, sqNorm (Aᴴ *ᵥ fj j)) ^ (R + 1) * (∑ j ∈ Js, sqNorm (gj j)) ^ (R + 1) :=
        mul_pow _ _ _
    _ ≤ (sqNorm f ^ R * ((N * σ) *
          ‖∑ s, ∑ s', if π s = π s' then ((A * Aᴴ) ^ (R + 1)) s s' else 0‖)) *
          ((2 * w + 1) * sqNorm f) ^ (R + 1) := by
        refine mul_le_mul (hhold.trans (mul_le_mul_of_nonneg_left hW'
          (pow_nonneg (sqNorm_nonneg _) _))) (pow_le_pow_left₀
            (sum_nonneg fun _ _ => sqNorm_nonneg _) hoverlap _)
          (pow_nonneg (sum_nonneg fun _ _ => sqNorm_nonneg _) _) ?_
        exact mul_nonneg (pow_nonneg (sqNorm_nonneg _) _)
          (mul_nonneg hNσ (norm_nonneg _))
    _ = _ := by
        rw [mul_pow, show 2 * R + 1 = R + (R + 1) by ring, pow_add]
        ring

end Erdos408.OneSided
