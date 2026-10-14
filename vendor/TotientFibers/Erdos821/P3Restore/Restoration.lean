import Erdos821.S2.RestorationTask
import Erdos821.S2.ActualGhostNorms
import Erdos821.S2.CountableSchur
import Erdos821.P3Restore.RankSum
import Erdos821.P3Restore.Scalar

/-! The restored memory norm: the exact truncated distinct expression is the finite
equality-rank sum of low-rank expressions; low ranks use `LowRankMemoryTask`, high ranks
`HighRankMemoryTask`, and the scalar margin absorbs both. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Restore

open Erdos821.Blueprint.Graph

theorem normBound_mono {α : Type*} {mass : α → ℝ} {K : α → α → ℂ} {C C' : ℝ}
    (hK : NormBound mass K C) (hCC : C ≤ C') : NormBound mass K C' := by
  intro s t f g
  refine (hK s t f g).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCC (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem birthAddress_card_le (P : PrimeGroups) (J ell n B : ℕ) (ℓ C0 : ℝ)
    (hℓ : 4 ≤ ℓ) (hJ : (J : ℝ) + ell + 1 ≤ ℓ) (hC0 : 0 < C0)
    (hb : (Fintype.card P.BigGroup : ℝ) ≤ C0 * Real.log ℓ)
    (hn : (n : ℝ) + 1 ≤ 3 * ℓ) (hB : (B : ℝ) ≤ ℓ ^ 2 + 1)
    (h6 : 6 * C0 * Real.log ℓ ≤ ℓ) :
    (Fintype.card (Erdos821.S2Core.BirthAddress P (J + ell) n B) : ℝ) ≤ ℓ ^ (4 : ℕ) := by
  rw [Erdos821.S2Core.birthAddress_card]
  push_cast
  have hT : 0 ≤ Real.log ℓ := Real.log_nonneg (by linarith)
  have hb0 : (0 : ℝ) ≤ (Fintype.card P.BigGroup : ℝ) := Nat.cast_nonneg _
  have hℓsq : ℓ ≤ ℓ ^ 2 := by nlinarith
  have hJB : ((J : ℝ) + ell) + B ≤ 2 * ℓ ^ 2 := by linarith
  have heq : ((J : ℝ) + ell) * (Fintype.card P.BigGroup : ℝ) * ((n : ℝ) + 1) +
      ((n : ℝ) + 1) * (Fintype.card P.BigGroup : ℝ) * B =
      ((n : ℝ) + 1) * (Fintype.card P.BigGroup : ℝ) * (((J : ℝ) + ell) + B) := by ring
  rw [heq]
  calc ((n : ℝ) + 1) * (Fintype.card P.BigGroup : ℝ) * (((J : ℝ) + ell) + B)
      ≤ (3 * ℓ) * (C0 * Real.log ℓ) * (2 * ℓ ^ 2) := by
        apply mul_le_mul (mul_le_mul hn hb hb0 (by linarith)) hJB (by positivity)
          (mul_nonneg (by linarith) (mul_nonneg hC0.le hT))
    _ = (6 * C0 * Real.log ℓ) * ℓ ^ 3 := by ring
    _ ≤ ℓ * ℓ ^ 3 := mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = ℓ ^ (4 : ℕ) := by ring


end Erdos821.P3Restore

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph
open Erdos821.P3Restore

theorem RestoredMemoryNormTask_proof (F : FixedData) (r : MemoryParameters F) :
    RestoredMemoryNormTask F r := by
  intro hGA hBd hAbs hRare hClean hContr hLR hHR E hE
  obtain ⟨Cv, hCv, xg, hGx⟩ := hGA
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = E + Cv + 5 := ⟨_, rfl⟩
  have hGpos : 0 < G := by rw [hG]; linarith
  obtain ⟨Eid, hEid, hCtr⟩ := hContr hRare hClean G hGpos
  refine ⟨Eid, hEid, fun m C₁ => ?_⟩
  obtain ⟨Ca, hCa⟩ := hAbs m C₁
  obtain ⟨Ch, hCh0, hCh⟩ := hHR GhostRowsTask_proof hAbs m C₁
  obtain ⟨J₀, hJ₀⟩ := hCtr m C₁
  refine ⟨J₀, fun J hJ C₂ => ?_⟩
  obtain ⟨C, hCpos, xh, hHx⟩ := hCh J
  obtain ⟨xa, hAx⟩ := hCa J
  obtain ⟨xb, hBx⟩ := hBd F J
  obtain ⟨xc, hCx⟩ := hJ₀ J hJ C₂
  have hc : 0 < F.c := lt_trans (lt_trans F.a_pos F.ab) F.bc
  obtain ⟨Ca', hCa'⟩ : ∃ Ca' : ℝ, Ca' = max 0 Ca := ⟨_, rfl⟩
  have hCa'0 : 0 ≤ Ca' := by rw [hCa']; exact le_max_left _ _
  have hCaCa' : Ca ≤ Ca' := by rw [hCa']; exact le_max_right _ _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 8 + 2 * (Ca' + G) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  obtain ⟨C'', hC''⟩ : ∃ C'' : ℝ, C'' = 2 * (Ch + E + 2) := ⟨_, rfl⟩
  have hC''0 : 0 ≤ C'' := by rw [hC'']; linarith
  have hev : ∀ᶠ ℓ : ℝ in Filter.atTop,
      4 ≤ ℓ ∧ (J : ℝ) + F.ell + 1 ≤ ℓ ∧ 6 * F.C₀ * Real.log ℓ ≤ ℓ ^ (1 : ℝ) ∧
      (K + 1) * C'' * Real.log ℓ ≤ ℓ ^ F.c ∧ 32 * Real.log ℓ ≤ ℓ ^ F.c ∧
      4 * Real.log C ≤ ℓ ^ F.c ∧ 2 * Real.log 2 ≤ ℓ ^ F.c ∧
      max ((K + 2 + Cv) / 4) (Ch + 1) ≤
        ((2 * ⌈ℓ ^ ((52 : ℝ) / 100)⌉₊ : ℕ) : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (4 : ℝ),
      Filter.eventually_ge_atTop ((J : ℝ) + F.ell + 1),
      ev_log_le one_pos (6 * F.C₀), ev_log_le hc ((K + 1) * C''), ev_log_le hc 32,
      ev_rpow_ge hc (4 * Real.log C), ev_rpow_ge hc (2 * Real.log 2),
      ev_N_ge (max ((K + 2 + Cv) / 4) (Ch + 1))] with ℓ h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨xs, hxs⟩ := eventually_log hev
  refine ⟨max (max xg xh) (max (max xa xb) (max xc xs)), ?_⟩
  intro x hx P hP A hA hk0 hk hId theta
  have hxg : x ≥ xg := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxh : x ≥ xh := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxa : x ≥ xa := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hx
  have hxb : x ≥ xb := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _)) hx
  have hxc : x ≥ xc := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  have hxs' : x ≥ xs := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hxs x hxs'
  have q1 : 4 ≤ L x := q1
  have q2 : (J : ℝ) + F.ell + 1 ≤ L x := q2
  have q3 : 6 * F.C₀ * Real.log (L x) ≤ L x := by
    have h : 6 * F.C₀ * Real.log (L x) ≤ (L x) ^ (1 : ℝ) := q3
    rwa [Real.rpow_one] at h
  have q4 : (K + 1) * C'' * Real.log (L x) ≤ (L x) ^ F.c := q4
  have q5 : 32 * Real.log (L x) ≤ (L x) ^ F.c := q5
  have q6 : 4 * Real.log C ≤ (L x) ^ F.c := q6
  have q7 : 2 * Real.log 2 ≤ (L x) ^ F.c := q7
  have q8 : max ((K + 2 + Cv) / 4) (Ch + 1) ≤ (N x : ℝ) := q8
  obtain ⟨hV, hb, hmu, hCGle⟩ := hGx x hxg P hP
  set CG := (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card with hCGdef
  have hℓ0 : 0 < L x := by linarith
  have hℓ1 : 1 ≤ L x := by linarith
  have hT0 : 0 ≤ Real.log (L x) := Real.log_nonneg hℓ1
  -- the number of potential birth addresses
  have hcard : (Fintype.card P.BigGroup : ℝ) = (P.bigGroups.card : ℝ) := by
    congr 1
    simp only [PrimeGroups.bigGroups, Fintype.card_subtype]
  have hbig : (Fintype.card P.BigGroup : ℝ) ≤ F.C₀ * Real.log (L x) := by
    rw [hcard]; exact hP.2.2.2.1
  have hn : (N x : ℝ) + 1 ≤ 3 * L x := by
    have hR : (⌈(L x) ^ ((52 : ℝ) / 100)⌉₊ : ℝ) < (L x) ^ ((52 : ℝ) / 100) + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg hℓ0.le _)
    have hrp : (L x) ^ ((52 : ℝ) / 100) ≤ L x := by
      have h := Real.rpow_le_rpow_of_exponent_le hℓ1 (by norm_num : (52 : ℝ) / 100 ≤ 1)
      rwa [Real.rpow_one] at h
    have hN : (N x : ℝ) = 2 * (⌈(L x) ^ ((52 : ℝ) / 100)⌉₊ : ℝ) := by
      simp only [N, R, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have hBc : (memoryCutoff x : ℝ) ≤ (L x) ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (L x))).le
  have ha : (Fintype.card (BirthAddress P (J + F.ell) (N x) (memoryCutoff x)) : ℝ) ≤
      (L x) ^ (4 : ℕ) :=
    birthAddress_card_le P J F.ell (N x) (memoryCutoff x) (L x) F.C₀ q1 q2 F.C₀_pos
      hbig hn hBc q3
  -- the rank cutoff
  have hA4 : K + 2 + Cv ≤ 4 * (N x : ℝ) := by
    have := le_trans (le_max_left _ _) q8; linarith
  obtain ⟨hr0, hr0'⟩ := r0_bounds (L x) F.c K C'' Cv (N x) hℓ1 hK0 hC''0 q4 hA4
  have h5 : 8 * Real.log (L x) + Real.log C ≤ (L x) ^ F.c / 2 := by linarith only [q5, q6]
  have h7 : Real.log 4 + Ch * Real.log (L x) ≤ 2 * (N x : ℝ) * Real.log (L x) := by
    have hn1 : Ch + 1 ≤ (N x : ℝ) := le_trans (le_max_right _ _) q8
    have hl4 : Real.log 4 ≤ Real.log (L x) := Real.log_le_log (by norm_num) q1
    have h1 := mul_le_mul_of_nonneg_right hn1 hT0
    have h2 := mul_nonneg hCh0 hT0
    have h3 : (Ch + 1) * Real.log (L x) = Ch * Real.log (L x) + Real.log (L x) := by ring
    linarith only [h1, h2, h3, hl4, hT0]
  -- local norm inputs for the low-rank task
  have hmass : ∀ s : P.MemoryState (J + F.ell), 0 ≤ P.memoryMass F J (N x) s :=
    memoryMass_nonneg F J (N x) (fun g => (hV g).1) hb
  have hw : ∀ s : P.MemoryState (J + F.ell), 0 < P.memoryWeight r.v s := by
    intro s
    unfold PrimeGroups.memoryWeight
    exact pow_pos (by linarith [r.v_gt]) _
  have hCG0 : 0 ≤ CG :=
    pow_nonneg (Real.exp_pos _).le _
  have hCEpos : 0 < (L x) ^ (-G) := Real.rpow_pos_of_pos hℓ0 _
  have hCECA : (L x) ^ (-G) ≤ (L x) ^ Ca' :=
    Real.rpow_le_rpow_of_exponent_le hℓ1 (by linarith)
  have hedge : ∀ (i : Fin (N x))
      (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ),
      (∀ s t c, ‖phi s t c‖ ≤ 1) →
      NormBound (P.memoryMass F J (N x))
        (projectKernel (fun s => P.memorySize s ≤ memoryCutoff x)
          (memoryEdgeKernel A (N x) r.rho theta i .all phi)) ((L x) ^ Ca') := by
    intro i phi hphi
    have hW := hAx x hxa P hP A hA theta i
    have h1 : NormBound (P.memoryMass F J (N x))
        (memoryEdgeKernel A (N x) r.rho theta i .all phi) ((L x) ^ Ca) :=
      weightedBounds_domination _ _ _ _ _ hmass hw (Real.rpow_nonneg hℓ0.le _) hW
        (fun s t => by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact (memoryEdgeKernel_norm_le A (N x) r.rho theta i .all phi hphi s t).trans
            (le_abs_self _))
    have h2 := normBound_project _ _ _ (Real.rpow_nonneg hℓ0.le _) hmass h1
      (fun s => P.memorySize s ≤ memoryCutoff x)
    exact normBound_mono h2 (Real.rpow_le_rpow_of_exponent_le hℓ1 hCaCa')
  have hbd : initialMemoryBoundaryMass A (N x) ≤ 2 := hBx x hxb P hP m A
  -- the finite rank expansion and the two rank ranges
  rw [truncatedDistinctMemoryExpression_rank_expansion]
  have hVle := smallV_le hℓ0 hCpos ha h5
  have hhalf := exp_neg_half_le q7
  refine le_trans (rank_sum_bound
    (lowRankHistoryExpression A (N x) (memoryCutoff x) r.rho theta)
    (2 * CG ^ (N x + 1) *
      ((L x) ^ (-G)) ^ (N x))
    (((L x) ^ Ca' / (L x) ^ (-G)) ^ 2)
    ((L x) ^ (Ch * ((N x + 1 : ℕ) : ℝ)))
    (C / Real.exp ((L x) ^ F.c))
    ⌈C'' * (N x : ℝ) * Real.log (L x) / (L x) ^ F.c⌉₊
    (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hCG0 _)) (pow_nonneg hCEpos.le _))
    (sq_nonneg _) (Real.rpow_nonneg hℓ0.le _)
    (div_nonneg hCpos.le (Real.exp_pos _).le) (by linarith) ?_ ?_) ?_
  · intro π hπ _
    have h := hLR F P J m (N x) (memoryCutoff x) A r.rho theta
      CG ((L x) ^ (-G)) ((L x) ^ Ca') hCG0 hCEpos hCECA hmass
      (fun i phi hphi => actual_projected_ghost_norm F J (N x) (memoryCutoff x) r hV hb hmu
        i phi hphi)
      hedge (fun i => hCx x hxc P hP A hA hk0 hk hId theta i) π hπ
    have hQ : 0 ≤ CG ^ (N x + 1) *
        ((L x) ^ (-G)) ^ (N x) * ((L x) ^ Ca' / (L x) ^ (-G)) ^ (2 * birthRank π) :=
      mul_nonneg (mul_nonneg (pow_nonneg hCG0 _) (pow_nonneg hCEpos.le _))
        (pow_nonneg (div_nonneg (Real.rpow_nonneg hℓ0.le _) hCEpos.le) _)
    calc _ ≤ _ := h
      _ = initialMemoryBoundaryMass A (N x) *
          (CG ^ (N x + 1) *
            ((L x) ^ (-G)) ^ (N x) * ((L x) ^ Ca' / (L x) ^ (-G)) ^ (2 * birthRank π)) := by
          ring
      _ ≤ 2 * (CG ^ (N x + 1) *
            ((L x) ^ (-G)) ^ (N x) * ((L x) ^ Ca' / (L x) ^ (-G)) ^ (2 * birthRank π)) :=
          mul_le_mul_of_nonneg_right hbd hQ
      _ = _ := by rw [pow_mul]; ring
  · intro π hπ
    exact (lowRankHistoryExpression_norm_le A (N x) (memoryCutoff x) r.rho theta π).trans
      (hHx x hxh P hP A hA theta π hπ)
  · exact scalar_bound (L x) E Cv Ca' Ch C F.c
      CG G K (N x)
      (Fintype.card (BirthAddress P (J + F.ell) (N x) (memoryCutoff x)))
      ⌈C'' * (N x : ℝ) * Real.log (L x) / (L x) ^ F.c⌉₊
      hG hK q1 hCv hCa'0 hE.le hCpos hCG0 hCGle ha hr0 (by rw [← hC'']; exact hr0') h5 q7 h7


example : type_of% @RestoredMemoryNormTask_proof =
    ∀ (F : FixedData) (r : MemoryParameters F), RestoredMemoryNormTask F r := rfl

end Erdos821.S2Core
