import Erdos821.Blueprint.Analytic

/-! A fixed smooth partition of unity on `[lo, hi]` whose pieces have supports
of ratio at most two, and the derivative bounds of the pieces of a cutoff
multiplied by `y`. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter

namespace Erdos821.P5Marked
open Blueprint.Analytic

/-- Geometric partition points; `ptA lo 1 = lo`. -/
def ptA (lo : ℝ) (k : ℕ) : ℝ := 3 * lo / 4 * (4 / 3) ^ k

theorem ptA_pos {lo : ℝ} (hlo : 0 < lo) (k : ℕ) : 0 < ptA lo k := by unfold ptA; positivity

theorem ptA_succ (lo : ℝ) (k : ℕ) : ptA lo (k + 1) = 4 / 3 * ptA lo k := by
  unfold ptA; rw [pow_succ]; ring

theorem ptA_one (lo : ℝ) : ptA lo 1 = lo := by unfold ptA; ring

theorem ptA_lt_succ {lo : ℝ} (hlo : 0 < lo) (k : ℕ) : ptA lo k < ptA lo (k + 1) := by
  rw [ptA_succ]; have := ptA_pos hlo k; linarith

theorem ptA_mono {lo : ℝ} (hlo : 0 < lo) {k l : ℕ} (hkl : k ≤ l) : ptA lo k ≤ ptA lo l := by
  unfold ptA
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) hkl

theorem ptA_two_step (lo : ℝ) (k : ℕ) : ptA lo (k + 2) = 16 / 9 * ptA lo k := by
  rw [ptA_succ, ptA_succ]; ring

theorem ptA_two_step_le {lo : ℝ} (hlo : 0 < lo) (k : ℕ) : ptA lo (k + 2) ≤ 2 * ptA lo k := by
  rw [ptA_two_step]; have := ptA_pos hlo k; linarith

/-- The `k`th smooth step, from `0` at `ptA k` to `1` at `ptA (k+1)`. -/
def gstep (lo : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  Real.smoothTransition ((y - ptA lo k) / (ptA lo (k + 1) - ptA lo k))

/-- The partition pieces. -/
def psi (lo : ℝ) (k : ℕ) (y : ℝ) : ℝ := gstep lo k y - gstep lo (k + 1) y

theorem gstep_zero {lo : ℝ} (hlo : 0 < lo) {k : ℕ} {y : ℝ} (hy : y ≤ ptA lo k) :
    gstep lo k y = 0 := by
  unfold gstep
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg (by linarith)
  linarith [ptA_lt_succ hlo k]

theorem gstep_one {lo : ℝ} (hlo : 0 < lo) {k : ℕ} {y : ℝ} (hy : ptA lo (k + 1) ≤ y) :
    gstep lo k y = 1 := by
  unfold gstep
  apply Real.smoothTransition.one_of_one_le
  have h := ptA_lt_succ hlo k
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem contDiff_gstep (lo : ℝ) (k : ℕ) : ContDiff ℝ ∞ (gstep lo k) := by
  unfold gstep
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_id.sub contDiff_const).div_const _)

theorem contDiff_psi (lo : ℝ) (k : ℕ) : ContDiff ℝ ∞ (psi lo k) :=
  (contDiff_gstep lo k).sub (contDiff_gstep lo (k + 1))

theorem psi_eq_zero {lo : ℝ} (hlo : 0 < lo) (k : ℕ) {y : ℝ}
    (hy : y ∉ Set.Icc (ptA lo k) (ptA lo (k + 2))) : psi lo k y = 0 := by
  unfold psi
  rcases not_and_or.mp hy with h | h
  · rw [not_le] at h
    rw [gstep_zero hlo h.le, gstep_zero hlo (h.le.trans (ptA_lt_succ hlo k).le), sub_zero]
  · rw [not_le] at h
    rw [gstep_one hlo (le_trans (ptA_lt_succ hlo (k + 1)).le h.le), gstep_one hlo h.le, sub_self]

theorem sum_psi (lo : ℝ) (n : ℕ) (y : ℝ) :
    ∑ k ∈ Finset.range n, psi lo k y = gstep lo 0 y - gstep lo n y := by
  unfold psi
  exact Finset.sum_range_sub' (fun k => gstep lo k y) n

theorem sum_psi_eq_one {lo hi : ℝ} (hlo : 0 < lo) (n : ℕ) (hn : hi ≤ ptA lo n) {y : ℝ}
    (hy : y ∈ Set.Icc lo hi) : ∑ k ∈ Finset.range n, psi lo k y = 1 := by
  rw [sum_psi, gstep_one hlo (by rw [zero_add, ptA_one]; exact hy.1),
    gstep_zero hlo (hy.2.trans hn), sub_zero]

theorem exists_ptA_ge {lo : ℝ} (hlo : 0 < lo) (hi : ℝ) : ∃ n : ℕ, hi ≤ ptA lo n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (hi / (3 * lo / 4)) (by norm_num : (1 : ℝ) < 4 / 3)
  refine ⟨n, ?_⟩
  unfold ptA
  have hc : 0 < 3 * lo / 4 := by positivity
  rw [div_lt_iff₀ hc] at hn
  linarith

/-- The weight `y ψ_k(y)` as a complex function. -/
def chiW (lo : ℝ) (k : ℕ) (y : ℝ) : ℂ := ((y * psi lo k y : ℝ) : ℂ)

theorem contDiff_chiW (lo : ℝ) (k : ℕ) : ContDiff ℝ ∞ (chiW lo k) := by
  unfold chiW
  exact Complex.ofRealCLM.contDiff.comp (contDiff_id.mul (contDiff_psi lo k))

theorem chiW_eq_zero {lo : ℝ} (hlo : 0 < lo) (k : ℕ) {y : ℝ}
    (hy : y ∉ Set.Icc (ptA lo k) (ptA lo (k + 2))) : chiW lo k y = 0 := by
  simp [chiW, psi_eq_zero hlo k hy]

theorem hasCompactSupport_chiW {lo : ℝ} (hlo : 0 < lo) (k : ℕ) : HasCompactSupport (chiW lo k) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := ptA lo k)
    (b := ptA lo (k + 2)))
  intro y hy
  by_contra h
  exact hy (chiW_eq_zero hlo k h)

theorem chiW_deriv_bound {lo : ℝ} (hlo : 0 < lo) (k j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ‖iteratedFDeriv ℝ j (chiW lo k) y‖ ≤ M := by
  have hc : Continuous (iteratedFDeriv ℝ j (chiW lo k)) :=
    (contDiff_chiW lo k).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support
    ((hasCompactSupport_chiW hlo k).iteratedFDeriv j)
  exact ⟨max M 0, le_max_right _ _, fun y => (hM y).trans (le_max_left _ _)⟩

/-- A fixed choice of the derivative bounds of `chiW`. -/
def chiBound (lo : ℝ) (k j : ℕ) : ℝ :=
  if h : 0 < lo then Classical.choose (chiW_deriv_bound h k j) else 0

theorem chiBound_spec {lo : ℝ} (hlo : 0 < lo) (k j : ℕ) :
    0 ≤ chiBound lo k j ∧ ∀ y, ‖iteratedFDeriv ℝ j (chiW lo k) y‖ ≤ chiBound lo k j := by
  unfold chiBound
  simp only [hlo, dite_true]
  exact Classical.choose_spec (chiW_deriv_bound hlo k j)

/-- Bounds of the pieces of the partitioned cutoff. -/
def pieceBounds (lo : ℝ) (bounds : ℕ → ℝ) (k j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * bounds i * chiBound lo k (j - i)

theorem pieceBounds_nonneg {lo : ℝ} (hlo : 0 < lo) {bounds : ℕ → ℝ} (hb : ∀ j, 0 ≤ bounds j)
    (k j : ℕ) : 0 ≤ pieceBounds lo bounds k j := by
  unfold pieceBounds
  apply Finset.sum_nonneg
  intro i _
  have := (chiBound_spec hlo k (j - i)).1
  have := hb i
  positivity

/-- The pieces `Ψ(y) y ψ_k(y)` satisfy the cutoff hypotheses on `[ptA k, ptA (k+2)]`. -/
theorem cutoff_piece {x C lo hi : ℝ} {Ψ : ℝ → ℂ} {bounds : ℕ → ℝ} (hlo : 0 < lo) (hC : 0 ≤ C)
    (hL : 1 ≤ L x) (hb : ∀ j, 0 ≤ bounds j) (hΨ : CutoffBound x C lo hi Ψ bounds) (k : ℕ) :
    CutoffBound x C (ptA lo k) (ptA lo (k + 2)) (fun y => Ψ y * chiW lo k y)
      (pieceBounds lo bounds k) := by
  obtain ⟨hsmooth, hsupp, hder⟩ := hΨ
  refine ⟨hsmooth.mul (contDiff_chiW lo k), ?_, ?_⟩
  · intro y hy
    by_contra h
    exact hy (by simp [chiW_eq_zero hlo k h])
  · intro j y
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    refine (norm_iteratedFDeriv_mul_le hsmooth (contDiff_chiW lo k) y
      (by exact_mod_cast le_top)).trans ?_
    unfold pieceBounds
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : ‖iteratedFDeriv ℝ i Ψ y‖ ≤ bounds i * L x ^ (C * (i + 1)) := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hder i y
    have h2 := (chiBound_spec hlo k (j - i)).2 y
    have hpow : L x ^ (C * (i + 1)) ≤ L x ^ (C * (j + 1)) := by
      apply Real.rpow_le_rpow_of_exponent_le hL
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      nlinarith
    have hLp : 0 ≤ L x ^ (C * (i + 1)) := Real.rpow_nonneg (by linarith) _
    have hcb := (chiBound_spec hlo k (j - i)).1
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i Ψ y‖ * ‖iteratedFDeriv ℝ (j - i) (chiW lo k) y‖
        ≤ (j.choose i : ℝ) * (bounds i * L x ^ (C * (i + 1))) * chiBound lo k (j - i) := by
          have := hb i
          gcongr
      _ ≤ (j.choose i : ℝ) * (bounds i * L x ^ (C * (j + 1))) * chiBound lo k (j - i) := by
          gcongr
          exact hb i
      _ = (j.choose i : ℝ) * bounds i * chiBound lo k (j - i) * L x ^ (C * (j + 1)) := by ring

end Erdos821.P5Marked
