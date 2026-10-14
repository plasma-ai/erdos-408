import Erdos821.P5MarkedEnergy.ThreeRange
import Erdos821.P5MarkedEnergy.Collapse
import Erdos821.P5.SparseTheorem
import Erdos821.Classical.DirichletMean

/-! The three-range estimate for one box of four dyadic polynomials, with the
mean square for the complementary product and the sparse residual mean square
on the exceptional unit intervals made explicit. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos821.P5Marked
open Blueprint.Analytic

theorem integral_unit_le_iSup (G : ℝ → ℂ) (hG : Continuous G) (a : ℝ) :
    ∫ s in a..(a + 1), ‖G s‖ ^ 2 ≤ ⨆ t : Set.Icc a (a + 1), ‖G t‖ ^ 2 := by
  have hc : Continuous fun s => ‖G s‖ ^ 2 := by fun_prop
  have hbdd : BddAbove (Set.range fun t : Set.Icc a (a + 1) => ‖G t‖ ^ 2) := by
    have := (isCompact_Icc (a := a) (b := a + 1)).bddAbove_image hc.continuousOn
    obtain ⟨M, hM⟩ := this
    refine ⟨M, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hM ⟨t.1, t.2, rfl⟩
  have hle : ∀ s ∈ Set.Icc a (a + 1), ‖G s‖ ^ 2 ≤ ⨆ t : Set.Icc a (a + 1), ‖G t‖ ^ 2 :=
    fun s hs => le_ciSup hbdd ⟨s, hs⟩
  calc ∫ s in a..(a + 1), ‖G s‖ ^ 2 ≤ ∫ _s in a..(a + 1), ⨆ t : Set.Icc a (a + 1), ‖G t‖ ^ 2 :=
        intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
          intervalIntegrable_const hle
    _ = _ := by simp

theorem dp_split_three (g : ℕ → ℂ) (U : ℕ) (hU : 1 ≤ U) (hg : ∀ n, n < U → g n = 0) (t : ℝ) :
    dp (Finset.Icc 1 (4 * U)) g t = dp (Finset.Ico U (2 * U)) g t + dp (Finset.Icc (2 * U) (4 * U)) g t := by
  unfold dp
  have h1 : Finset.Icc 1 (4 * U) = Finset.Ico 1 U ∪ (Finset.Ico U (2 * U) ∪ Finset.Icc (2 * U) (4 * U)) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico, Finset.mem_union]; omega
  rw [h1, Finset.sum_union, Finset.sum_union]
  · have : ∑ n ∈ Finset.Ico 1 U, g n * mellin n t = 0 :=
      Finset.sum_eq_zero fun n hn => by rw [hg n (Finset.mem_Ico.mp hn).2, zero_mul]
    rw [this, zero_add]
  · rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Ico, Finset.mem_Icc] at h1 h2; omega
  · rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Ico, Finset.mem_Icc, Finset.mem_union] at h1 h2; omega

/-- The three-range estimate for one box. -/
theorem box_three_range :
    ∃ K c Y₀ : ℝ, 0 < K ∧ 0 ≤ c ∧ 1 < Y₀ ∧
      ∀ (f1 f2 f3 f4 : ℕ → ℂ) (i1 i2 i3 i4 : ℕ) (B1 B4 Y T0 T1 θ ε1 ε3 : ℝ) (occ : Finset ℤ),
        0 ≤ B1 → 0 ≤ B4 → (∀ m ∈ dyad i1, ‖f1 m‖ ≤ B1) → (∀ m ∈ dyad i3, ‖f3 m‖ ≤ 1) →
        (∀ m ∈ dyad i4, ‖f4 m‖ ≤ B4) →
        0 ≤ T0 → 0 ≤ T1 → 0 ≤ θ → 0 ≤ ε3 → Y₀ ≤ Y →
        Y ^ (0.6 : ℝ) ≤ (2 : ℝ) ^ (i1 + i4) → 2 * (2 : ℝ) ^ (i1 + i4) ≤ Y →
        (occ.card : ℝ) ≤ Y ^ (0.05 : ℝ) → (∀ j ∈ occ, |(j : ℝ)| ≤ Y) →
        (∀ s, |s| ≤ T1 → (∀ j ∈ occ, s ∉ Set.Icc (j : ℝ) (j + 1)) → ‖hpoly f2 i2 s‖ ≤ θ) →
        (∀ s, ‖hpoly f2 i2 s‖ ≤ 1) →
        (∀ s, T0 ≤ |s| → |s| ≤ T1 → ‖hpoly f3 i3 s‖ ≤ ε3) →
        (∀ s, |s| ≤ T0 → ‖hpoly f1 i1 s‖ ≤ ε1) →
        ∫ s in (-T1)..T1, ‖hpoly f1 i1 s * hpoly f2 i2 s * hpoly f3 i3 s * hpoly f4 i4 s‖ ^ 2 ≤
          θ ^ 2 * (K * (2 * T1 + 2 ^ (i1 + i3 + i4 + 3) *
              Real.log (2 * 2 ^ (i1 + i3 + i4 + 3))) * (B1 * B4) ^ 2 *
              Real.log (2 * 2 ^ (i1 + i3 + i4 + 3)) ^ c / 2 ^ (i1 + i3 + i4)) +
          ε3 ^ 2 * (K * (B1 * B4) ^ 2 * Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ c *
              Real.log (2 * Y)) +
          2 * T0 * (ε1 ^ 2 * B4 ^ 2) := by
  obtain ⟨KMS, hKMS, hMS⟩ := Erdos821.Classical.blueprint_meanSquares
  obtain ⟨c3, K3, hc3, hK3, hcoll3⟩ := sqNorm_coll_le 3
  obtain ⟨c2, K2, hc2, hK2, hcoll2⟩ := sqNorm_coll_le 2
  obtain ⟨Ksp, Y₀, hKsp, hY₀, hsp⟩ := Erdos821.Blueprint.Analytic.sparse_residual_proof
  refine ⟨KMS * K3 + 6 * Ksp * K2, max c3 c2, Y₀, by positivity, le_max_of_le_left hc3, hY₀, ?_⟩
  intro f1 f2 f3 f4 i1 i2 i3 i4 B1 B4 Y T0 T1 θ ε1 ε3 occ hB1 hB4 hf1 hf3 hf4 hT0 hT1 hθ hε3
    hY hU1 hU2 hocc hoccY hoff hF2 hlong hdisc
  have hYpos : 0 < Y := by linarith
  have hlogY : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  -- logarithm comparisons for the unified exponent
  have hlogge1 : ∀ n : ℕ, 1 ≤ n → 1 ≤ Real.log (2 * 2 ^ n) := by
    intro n hn
    rw [← pow_succ']
    rw [Real.log_pow]
    have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n + 1)
    nlinarith
  have hpowc : ∀ (n : ℕ) (c' : ℝ), 1 ≤ n → c' ≤ max c3 c2 →
      Real.log (2 * 2 ^ n) ^ c' ≤ Real.log (2 * 2 ^ n) ^ max c3 c2 :=
    fun n c' hn hc' => Real.rpow_le_rpow_of_exponent_le (hlogge1 n hn) hc'
  -- the three-factor mean square
  set S3 := i1 + i3 + i4 with hS3
  set N3 : ℕ := 2 ^ (S3 + 3) with hN3
  let F3v : Fin 3 → ℕ → ℂ := ![f1, f3, f4]
  let I3 : Fin 3 → ℕ := ![i1, i3, i4]
  have hsum3 : ∑ j, I3 j = S3 := by simp [I3, Fin.sum_univ_three, hS3]
  have hprod3 : ∀ s, hpoly f1 i1 s * hpoly f3 i3 s * hpoly f4 i4 s =
      dp (Finset.Icc 1 N3) (coll F3v I3) s := by
    intro s
    have := prod_hpoly_eq F3v I3 s
    rw [Fin.prod_univ_three, hsum3] at this
    simpa [F3v, I3] using this
  have hsq3 : sqNorm (Finset.Icc 1 N3) (coll F3v I3) ≤
      K3 * (B1 * 1 * B4) ^ 2 * Real.log (2 * 2 ^ (S3 + 3)) ^ c3 / 2 ^ S3 := by
    have := hcoll3 F3v I3 ![B1, 1, B4]
      (fun j => by fin_cases j <;> simp [hB1, hB4])
      (fun j => by fin_cases j <;> simpa [F3v, I3] using ‹_›)
    rw [Fin.prod_univ_three, hsum3] at this
    simpa using this
  have hQ3 : ∫ s in (-T1)..T1, ‖hpoly f1 i1 s * hpoly f3 i3 s * hpoly f4 i4 s‖ ^ 2 ≤
      KMS * K3 * (2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) * (B1 * B4) ^ 2 *
        Real.log (2 * 2 ^ (S3 + 3)) ^ max c3 c2 / 2 ^ S3 := by
    simp_rw [hprod3]
    have hms := (hMS N3 (coll F3v I3) (-T1) T1 (by linarith)).1
    have hN3R : ((N3 : ℕ) : ℝ) = 2 ^ (S3 + 3) := by rw [hN3]; push_cast; ring
    rw [hN3R] at hms
    have hA0 : 0 ≤ 2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3)) := by
      have := hlogge1 (S3 + 3) (by omega); positivity
    refine hms.trans ?_
    have hpw := hpowc (S3 + 3) c3 (by omega) (le_max_left _ _)
    calc KMS * (T1 - -T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) *
          sqNorm (Finset.Icc 1 N3) (coll F3v I3)
        ≤ KMS * (2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) *
          (K3 * (B1 * 1 * B4) ^ 2 * Real.log (2 * 2 ^ (S3 + 3)) ^ c3 / 2 ^ S3) := by
          rw [show T1 - -T1 = 2 * T1 by ring]
          exact mul_le_mul_of_nonneg_left hsq3 (by positivity)
      _ ≤ KMS * (2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) *
          (K3 * (B1 * B4) ^ 2 * Real.log (2 * 2 ^ (S3 + 3)) ^ max c3 c2 / 2 ^ S3) := by
          rw [mul_one]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hpw (by positivity)
      _ = _ := by ring
  -- the two-factor sparse mean square
  set S2 := i1 + i4 with hS2
  set U : ℕ := 2 ^ S2 with hU
  let F2v : Fin 2 → ℕ → ℂ := ![f1, f4]
  let I2 : Fin 2 → ℕ := ![i1, i4]
  have hsum2 : ∑ j, I2 j = S2 := by simp [I2, Fin.sum_univ_two, hS2]
  have hN2 : 2 ^ (S2 + 2) = 4 * U := by rw [hU, pow_add]; ring
  have hprod2 : ∀ s, hpoly f1 i1 s * hpoly f4 i4 s =
      dp (Finset.Icc 1 (4 * U)) (coll F2v I2) s := by
    intro s
    have := prod_hpoly_eq F2v I2 s
    rw [Fin.prod_univ_two, hsum2, hN2] at this
    simpa [F2v, I2] using this
  set A : ℝ := K2 * (B1 * B4) ^ 2 * Real.log (2 * 2 ^ (S2 + 2)) ^ c2 with hA
  have hA0 : 0 ≤ A := by
    have := hlogge1 (S2 + 2) (by omega); positivity
  have hsq2 : sqNorm (Finset.Icc 1 (4 * U)) (coll F2v I2) ≤ A / U := by
    have := hcoll2 F2v I2 ![B1, B4]
      (fun j => by fin_cases j <;> simp [hB1, hB4])
      (fun j => by fin_cases j <;> simpa [F2v, I2] using ‹_›)
    rw [Fin.prod_univ_two, hsum2, hN2] at this
    simpa [hA, hU] using this
  have hUone : 1 ≤ U := Nat.one_le_two_pow
  have hUR : ((U : ℕ) : ℝ) = (2 : ℝ) ^ (i1 + i4) := by rw [hU, hS2]; push_cast; ring
  have hvan : ∀ n, n < U → coll F2v I2 n = 0 := fun n hn =>
    coll_eq_zero_of_lt F2v I2 n (by rw [hsum2]; exact hn)
  have hsub1 : sqNorm (Finset.Ico U (2 * U)) (coll F2v I2) ≤ A / U := by
    refine le_trans ?_ hsq2
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn; simp only [Finset.mem_Ico, Finset.mem_Icc] at hn ⊢; omega
    · intros; positivity
  have hsub2 : sqNorm (Finset.Icc (2 * U) (4 * U)) (coll F2v I2) ≤ (2 * A) / ((2 * U : ℕ) : ℝ) := by
    refine le_trans ?_ (hsq2.trans_eq ?_)
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
      · intros; positivity
    · push_cast; field_simp
  have hsp1 := hsp Y U A (Finset.Ico U (2 * U)) (coll F2v I2) occ hY (by rw [hUR]; exact hU1)
    (by rw [hUR]; linarith [show (0 : ℝ) ≤ 2 ^ (i1 + i4) by positivity]) hA0
    (fun n hn => by
      simp only [Finset.mem_Ico] at hn
      constructor <;> norm_cast <;> omega) hsub1 hocc hoccY
  have hsp2 := hsp Y (2 * U : ℕ) (2 * A) (Finset.Icc (2 * U) (4 * U)) (coll F2v I2) occ hY
    (by push_cast; rw [hUR]; linarith [show (0 : ℝ) ≤ 2 ^ (i1 + i4) by positivity])
    (by push_cast; rw [hUR]; exact hU2) (by positivity)
    (fun n hn => by
      simp only [Finset.mem_Icc] at hn
      constructor <;> norm_cast <;> omega) hsub2 hocc hoccY
  have hQ14 : ∑ j ∈ occ, ∫ s in (j : ℝ)..(j + 1), ‖hpoly f1 i1 s * hpoly f4 i4 s‖ ^ 2 ≤
      6 * Ksp * A * Real.log (2 * Y) := by
    have hpiece : ∀ j : ℤ, ∫ s in (j : ℝ)..(j + 1), ‖hpoly f1 i1 s * hpoly f4 i4 s‖ ^ 2 ≤
        2 * (⨆ t : Set.Icc (j : ℝ) (j + 1), ‖dp (Finset.Ico U (2 * U)) (coll F2v I2) t‖ ^ 2) +
        2 * (⨆ t : Set.Icc (j : ℝ) (j + 1),
          ‖dp (Finset.Icc (2 * U) (4 * U)) (coll F2v I2) t‖ ^ 2) := by
      intro j
      have hc1 := P5Core.continuous_dp (Finset.Ico U (2 * U)) (coll F2v I2)
      have hc2 := P5Core.continuous_dp (Finset.Icc (2 * U) (4 * U)) (coll F2v I2)
      have e1 := integral_unit_le_iSup _ hc1 (j : ℝ)
      have e2 := integral_unit_le_iSup _ hc2 (j : ℝ)
      have hpt : ∀ s ∈ Set.Icc (j : ℝ) (j + 1), ‖hpoly f1 i1 s * hpoly f4 i4 s‖ ^ 2 ≤
          2 * ‖dp (Finset.Ico U (2 * U)) (coll F2v I2) s‖ ^ 2 +
          2 * ‖dp (Finset.Icc (2 * U) (4 * U)) (coll F2v I2) s‖ ^ 2 := by
        intro s _
        rw [hprod2 s, dp_split_three _ U hUone hvan s]
        set a1 := dp (Finset.Ico U (2 * U)) (coll F2v I2) s
        set a2 := dp (Finset.Icc (2 * U) (4 * U)) (coll F2v I2) s
        have hadd := norm_add_le a1 a2
        calc ‖a1 + a2‖ ^ 2 ≤ (‖a1‖ + ‖a2‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hadd 2
          _ ≤ 2 * ‖a1‖ ^ 2 + 2 * ‖a2‖ ^ 2 := by nlinarith [sq_nonneg (‖a1‖ - ‖a2‖)]
      have ii1 : IntervalIntegrable (fun s => 2 * ‖dp (Finset.Ico U (2 * U)) (coll F2v I2) s‖ ^ 2)
          volume (j : ℝ) (j + 1) := ((hc1.norm.pow 2).const_mul 2).intervalIntegrable _ _
      have ii2 : IntervalIntegrable
          (fun s => 2 * ‖dp (Finset.Icc (2 * U) (4 * U)) (coll F2v I2) s‖ ^ 2)
          volume (j : ℝ) (j + 1) := ((hc2.norm.pow 2).const_mul 2).intervalIntegrable _ _
      calc ∫ s in (j : ℝ)..(j + 1), ‖hpoly f1 i1 s * hpoly f4 i4 s‖ ^ 2
          ≤ ∫ s in (j : ℝ)..(j + 1), (2 * ‖dp (Finset.Ico U (2 * U)) (coll F2v I2) s‖ ^ 2 +
            2 * ‖dp (Finset.Icc (2 * U) (4 * U)) (coll F2v I2) s‖ ^ 2) :=
            intervalIntegral.integral_mono_on (by linarith)
              (((continuous_hpoly f1 i1).mul (continuous_hpoly f4 i4)).norm.pow 2
                |>.intervalIntegrable _ _)
              (ii1.add ii2) hpt
        _ = 2 * (∫ s in (j : ℝ)..(j + 1), ‖dp (Finset.Ico U (2 * U)) (coll F2v I2) s‖ ^ 2) +
            2 * ∫ s in (j : ℝ)..(j + 1), ‖dp (Finset.Icc (2 * U) (4 * U)) (coll F2v I2) s‖ ^ 2 := by
            rw [intervalIntegral.integral_add ii1 ii2,
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        _ ≤ _ := by linarith
    calc ∑ j ∈ occ, ∫ s in (j : ℝ)..(j + 1), ‖hpoly f1 i1 s * hpoly f4 i4 s‖ ^ 2
        ≤ ∑ j ∈ occ, (2 * (⨆ t : Set.Icc (j : ℝ) (j + 1),
              ‖dp (Finset.Ico U (2 * U)) (coll F2v I2) t‖ ^ 2) +
            2 * (⨆ t : Set.Icc (j : ℝ) (j + 1),
              ‖dp (Finset.Icc (2 * U) (4 * U)) (coll F2v I2) t‖ ^ 2)) :=
          Finset.sum_le_sum fun j _ => hpiece j
      _ = 2 * (∑ j ∈ occ, ⨆ t : Set.Icc (j : ℝ) (j + 1),
              ‖dp (Finset.Ico U (2 * U)) (coll F2v I2) t‖ ^ 2) +
          2 * (∑ j ∈ occ, ⨆ t : Set.Icc (j : ℝ) (j + 1),
              ‖dp (Finset.Icc (2 * U) (4 * U)) (coll F2v I2) t‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * (Ksp * A * Real.log (2 * Y)) + 2 * (Ksp * (2 * A) * Real.log (2 * Y)) := by
          linarith
      _ = 6 * Ksp * A * Real.log (2 * Y) := by ring
  -- apply the abstract estimate
  have hF3b : ∀ s, ‖hpoly f3 i3 s‖ ≤ 1 := norm_hpoly_le f3 i3 1 hf3
  have hF4b : ∀ s, ‖hpoly f4 i4 s‖ ≤ B4 := norm_hpoly_le f4 i4 B4 hf4
  have hmain := three_range_integral (hpoly f1 i1) (hpoly f2 i2) (hpoly f3 i3) (hpoly f4 i4)
    (continuous_hpoly _ _) (continuous_hpoly _ _) (continuous_hpoly _ _) (continuous_hpoly _ _)
    T0 T1 θ ε1 ε3 B4 _ _ occ hT0 hT1 hθ hε3 hoff hF2 hF3b hF4b hlong hdisc hQ3 hQ14
  refine hmain.trans ?_
  have hpw2 := hpowc (S2 + 2) c2 (by omega) (le_max_right _ _)
  have hQ14' : 6 * Ksp * A * Real.log (2 * Y) ≤ 6 * Ksp * K2 * (B1 * B4) ^ 2 *
      Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ max c3 c2 * Real.log (2 * Y) := by
    rw [hA]
    have : 0 ≤ 6 * Ksp * K2 * (B1 * B4) ^ 2 := by positivity
    calc 6 * Ksp * (K2 * (B1 * B4) ^ 2 * Real.log (2 * 2 ^ (S2 + 2)) ^ c2) * Real.log (2 * Y)
        = (6 * Ksp * K2 * (B1 * B4) ^ 2) * Real.log (2 * 2 ^ (S2 + 2)) ^ c2 * Real.log (2 * Y) := by
          ring
      _ ≤ (6 * Ksp * K2 * (B1 * B4) ^ 2) * Real.log (2 * 2 ^ (S2 + 2)) ^ max c3 c2 *
          Real.log (2 * Y) := by gcongr
  have hlog3 := hlogge1 (S3 + 3) (by omega)
  have hlog2 := hlogge1 (i1 + i4 + 2) (by omega)
  have hX3 : 0 ≤ (2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) * (B1 * B4) ^ 2 *
      Real.log (2 * 2 ^ (S3 + 3)) ^ max c3 c2 / 2 ^ S3 := by positivity
  have hX2 : 0 ≤ (B1 * B4) ^ 2 * Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ max c3 c2 *
      Real.log (2 * Y) := by positivity
  have hθ2 : 0 ≤ θ ^ 2 := by positivity
  have hε32 : 0 ≤ ε3 ^ 2 := by positivity
  have k1 : KMS * K3 ≤ KMS * K3 + 6 * Ksp * K2 := by
    have : 0 ≤ 6 * Ksp * K2 := by positivity
    linarith
  have k2 : 6 * Ksp * K2 ≤ KMS * K3 + 6 * Ksp * K2 := by
    have : 0 ≤ KMS * K3 := by positivity
    linarith
  have t1 : θ ^ 2 * (KMS * K3 * (2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) *
      (B1 * B4) ^ 2 * Real.log (2 * 2 ^ (S3 + 3)) ^ max c3 c2 / 2 ^ S3) ≤
      θ ^ 2 * ((KMS * K3 + 6 * Ksp * K2) * (2 * T1 + 2 ^ (S3 + 3) *
        Real.log (2 * 2 ^ (S3 + 3))) * (B1 * B4) ^ 2 *
        Real.log (2 * 2 ^ (S3 + 3)) ^ max c3 c2 / 2 ^ S3) := by
    apply mul_le_mul_of_nonneg_left _ hθ2
    have e1 : KMS * K3 * (2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) *
      (B1 * B4) ^ 2 * Real.log (2 * 2 ^ (S3 + 3)) ^ max c3 c2 / 2 ^ S3 = KMS * K3 *
      ((2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) * (B1 * B4) ^ 2 *
        Real.log (2 * 2 ^ (S3 + 3)) ^ max c3 c2 / 2 ^ S3) := by ring
    have e2 : (KMS * K3 + 6 * Ksp * K2) * (2 * T1 + 2 ^ (S3 + 3) *
        Real.log (2 * 2 ^ (S3 + 3))) * (B1 * B4) ^ 2 *
        Real.log (2 * 2 ^ (S3 + 3)) ^ max c3 c2 / 2 ^ S3 = (KMS * K3 + 6 * Ksp * K2) *
      ((2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) * (B1 * B4) ^ 2 *
        Real.log (2 * 2 ^ (S3 + 3)) ^ max c3 c2 / 2 ^ S3) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right k1 hX3
  have t2 : ε3 ^ 2 * (6 * Ksp * A * Real.log (2 * Y)) ≤
      ε3 ^ 2 * ((KMS * K3 + 6 * Ksp * K2) * (B1 * B4) ^ 2 *
        Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ max c3 c2 * Real.log (2 * Y)) := by
    apply mul_le_mul_of_nonneg_left _ hε32
    refine hQ14'.trans ?_
    have e1 : 6 * Ksp * K2 * (B1 * B4) ^ 2 * Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ max c3 c2 *
      Real.log (2 * Y) = 6 * Ksp * K2 * ((B1 * B4) ^ 2 *
        Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ max c3 c2 * Real.log (2 * Y)) := by ring
    have e2 : (KMS * K3 + 6 * Ksp * K2) * (B1 * B4) ^ 2 *
        Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ max c3 c2 * Real.log (2 * Y) =
        (KMS * K3 + 6 * Ksp * K2) * ((B1 * B4) ^ 2 *
        Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ max c3 c2 * Real.log (2 * Y)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right k2 hX2
  linarith

end Erdos821.P5Marked
