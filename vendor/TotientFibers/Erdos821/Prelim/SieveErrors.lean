import Mathlib
import Erdos821.Prelim.SieveCalculus
import Erdos821.Prelim.SieveExpectation
import Erdos821.Prelim.SieveProduct

/-!
# Sieve errors: `R_h` decay and product expectations (`lem:sieve`)

For blocks `j ∈ range N` with `e_j = (j+1)*h`, densities `0 ≤ g ≤ 1-η`
and block mass `≤ C`, `R_h = ∑ e_j/a_j ≤ K·e^{-h}` uniformly in `N`
(via `tailTerm` + `block_avoidance_ge` + `exists_tailSum_bound`), and
`∏S - ∏A ≤ E_corr` via `prod_telescope_le` (using `blockExp_bounds`
for even `h`). `e^{R}` avoided: `∏S-∏A ≤ E_corr ≤ …` directly with
`R ≤ 1/2` from `1+h ≤ e^{h}`.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
namespace Erdos821
namespace PrelimLemmas

/-- Per-block `1/a_j ≤ e^{C/η}` from avoidance lower bound. -/
theorem inv_avoidance_le (B : Finset ℕ) (g : ℕ → ℝ) (η C : ℝ)
    (hη : 0 < η)
    (hg0 : ∀ p ∈ B, 0 ≤ g p) (hg1 : ∀ p ∈ B, g p ≤ 1 - η)
    (hsum : ∑ p ∈ B, g p ≤ C) :
    1 / blockExpA B g ≤ Real.exp (C / η) := by
  have ha := Prelim.SieveCalculus.block_avoidance_ge B g η C hη hg0 hg1 hsum
  have hexp : (0 : ℝ) < Real.exp (-C / η) := Real.exp_pos _
  have h1 : (1 : ℝ) / blockExpA B g ≤ 1 / Real.exp (-C / η) :=
    one_div_le_one_div_of_le hexp ha
  have h2 : (1 : ℝ) / Real.exp (-C / η) = Real.exp (C / η) := by
    rw [neg_div, Real.exp_neg, one_div, inv_inv]
  rw [h2] at h1
  exact h1

/-- Uniform `R_h` bound `∑ e_j/a_j ≤ K·e^{-h}` over `range N`
(independent of `N`, hence of `z`). -/
theorem exists_R_bound (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ m₀ : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ (h N : ℕ), m₀ ≤ h → 1 ≤ h →
        ∀ (B : ℕ → Finset ℕ) (g : ℕ → ℝ),
        (∀ j ∈ Finset.range N, ∀ p ∈ B j, 0 ≤ g p ∧ g p ≤ 1 - η) →
        (∀ j ∈ Finset.range N, ∑ p ∈ B j, g p ≤ C) →
        ∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g
          ≤ K * Real.exp (-((h : ℕ) : ℝ)) := by
  obtain ⟨m₀, K₀, hK0, hden0, hbound⟩ :=
    Prelim.SieveCalculus.exists_tailSum_bound C hC
  refine ⟨m₀, Real.exp (C / η) * K₀, mul_pos (Real.exp_pos _) hK0, ?_⟩
  intro h N hh0 hh1 B g hgB hsumB
  have hexpC : (0 : ℝ) < Real.exp (C / η) := Real.exp_pos _
  have hterm : ∀ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g
      ≤ Real.exp (C / η) * Prelim.SieveCalculus.tailTerm C ((j + 1) * h) := by
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hgB j hj p hp).1
    have hg1 : ∀ p ∈ B j, g p ≤ 1 - η := fun p hp => (hgB j hj p hp).2
    have hsum : ∑ p ∈ B j, g p ≤ C := hsumB j hj
    have he_le := blockExpE_le_tail (B j) g ((j + 1) * h) C hg0 hsum
    have ha_le := inv_avoidance_le (B j) g η C hη hg0 hg1 hsum
    have he_nn : (0 : ℝ) ≤ blockExpE (B j) g ((j + 1) * h) := by
      unfold blockExpE
      apply Finset.sum_nonneg
      intro T hT
      have hP := trialProb_nonneg (B j) g
        (fun p hp => hg0 p hp)
        (fun p hp => by
          have := hg1 p hp
          linarith [hη]) T (Finset.mem_powerset.mp hT)
      have hE : (0 : ℝ) ≤ blockEval ((j + 1) * h) T := by
        unfold blockEval
        exact Nat.cast_nonneg _
      exact mul_nonneg hP hE
    have ha_nn : (0 : ℝ) ≤ 1 / blockExpA (B j) g := by
      apply one_div_nonneg.mpr
      have ha := Prelim.SieveCalculus.block_avoidance_ge (B j) g η C
        hη hg0 hg1 hsum
      have hexp : (0 : ℝ) < Real.exp (-C / η) := Real.exp_pos _
      exact le_of_lt (lt_of_lt_of_le hexp ha)
    have htail_nn : (0 : ℝ) ≤ Prelim.SieveCalculus.tailTerm C ((j + 1) * h) :=
      Prelim.SieveCalculus.tailTerm_nonneg hC _
    calc blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g
        = blockExpE (B j) g ((j + 1) * h) * (1 / blockExpA (B j) g) := by
          rw [div_eq_mul_one_div]
      _ ≤ Prelim.SieveCalculus.tailTerm C ((j + 1) * h)
          * Real.exp (C / η) :=
          mul_le_mul he_le ha_le ha_nn htail_nn
      _ = Real.exp (C / η) * Prelim.SieveCalculus.tailTerm C ((j + 1) * h) := by
          ring
  calc ∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g
      ≤ ∑ j ∈ Finset.range N,
        Real.exp (C / η) * Prelim.SieveCalculus.tailTerm C ((j + 1) * h) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hterm j hj
    _ = Real.exp (C / η) * ∑ j ∈ Finset.range N,
        Prelim.SieveCalculus.tailTerm C ((j + 1) * h) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (C / η) * (K₀ * Real.exp (-((h : ℕ) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hexpC.le
        exact hbound h hh0 hh1 N
    _ = Real.exp (C / η) * K₀ * Real.exp (-((h : ℕ) : ℝ)) := by
        ring

/-- Correction sum `E_corr = ∑ e_j ∏_{k≠j} S_k` dominates `∏S-∏A`
via telescoping (needs even `h` for per-block `0≤S-A≤e`). -/
noncomputable def corrExp (N : ℕ) (B : ℕ → Finset ℕ) (g : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N,
    blockExpE (B j) g ((j + 1) * h) *
      ∏ k ∈ (Finset.range N).erase j, blockExpS (B k) g ((k + 1) * h)

theorem prod_sub_le_corr (N : ℕ) (B : ℕ → Finset ℕ) (g : ℕ → ℝ) (h : ℕ)
    (he : Even h)
    (hg : ∀ j ∈ Finset.range N, ∀ p ∈ B j, 0 ≤ g p ∧ g p ≤ 1) :
    (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
      - (∏ j ∈ Finset.range N, blockExpA (B j) g)
      ≤ corrExp N B g h := by
  have hej : ∀ j ∈ Finset.range N, Even ((j + 1) * h) :=
    fun j _ => he.mul_left _
  have hI : ∀ j ∈ Finset.range N, 0 ≤ blockExpA (B j) g := by
    intro j hj
    unfold blockExpA
    apply Finset.prod_nonneg
    intro p hp
    have hg1 : g p ≤ 1 := (hg j hj p hp).2
    linarith
  -- `A_j ≤ S_j` and `S_j-A_j ≤ e_j` from `blockExp_bounds` (even truncation)
  have hIU : ∀ j ∈ Finset.range N,
      blockExpA (B j) g ≤ blockExpS (B j) g ((j + 1) * h) := by
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hg j hj p hp).1
    have hg1 : ∀ p ∈ B j, g p ≤ 1 := fun p hp => (hg j hj p hp).2
    have hb := blockExp_bounds (B j) g ((j + 1) * h) (hej j hj) hg0 hg1
    linarith [hb.1]
  have hUE : ∀ j ∈ Finset.range N,
      blockExpS (B j) g ((j + 1) * h) - blockExpA (B j) g
        ≤ blockExpE (B j) g ((j + 1) * h) := by
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hg j hj p hp).1
    have hg1 : ∀ p ∈ B j, g p ≤ 1 := fun p hp => (hg j hj p hp).2
    have hb := blockExp_bounds (B j) g ((j + 1) * h) (hej j hj) hg0 hg1
    exact hb.2
  have htele := Prelim.SieveCalculus.prod_telescope_le (Finset.range N)
    (fun j => blockExpA (B j) g) (fun j => blockExpS (B j) g ((j + 1) * h))
    (fun j => blockExpE (B j) g ((j + 1) * h)) hI hIU hUE
  unfold corrExp
  exact htele

/-- `1/(1-R) ≤ 1+2R` for `0 ≤ R ≤ 1/2` (avoids `e^{R}`). -/
theorem one_div_one_sub_le (R : ℝ) (hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 2) :
    1 / (1 - R) ≤ 1 + 2 * R := by
  have h1R : (0 : ℝ) < 1 - R := by linarith
  rw [div_le_iff₀ h1R]
  have hkey : (1 : ℝ) ≤ (1 + 2 * R) * (1 - R) := by
    have : (1 + 2 * R) * (1 - R) - 1 = R * (1 - 2 * R) := by ring
    have hnn : (0 : ℝ) ≤ R * (1 - 2 * R) :=
      mul_nonneg hR0 (by linarith)
    linarith
  linarith [hkey]

/-- `E_corr = (∏S)·R'` with `R' = ∑ e_j/S_j`. -/
theorem corr_eq_prod_mul (N : ℕ) (B : ℕ → Finset ℕ) (g : ℕ → ℝ) (h : ℕ)
    (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C) (he : Even h)
    (hgB : ∀ j ∈ Finset.range N, ∀ p ∈ B j, 0 ≤ g p ∧ g p ≤ 1 - η)
    (hsumB : ∀ j ∈ Finset.range N, ∑ p ∈ B j, g p ≤ C) :
    corrExp N B g h
      = (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h)) *
        (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) /
            blockExpS (B j) g ((j + 1) * h)) := by
  have hej : ∀ j ∈ Finset.range N, Even ((j + 1) * h) :=
    fun j _ => he.mul_left _
  -- positivity `S_j > 0` via `A_j ≥ e^{-C/η} > 0` and `S_j ≥ A_j`
  have hSpos : ∀ j ∈ Finset.range N,
      0 < blockExpS (B j) g ((j + 1) * h) := by
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hgB j hj p hp).1
    have hg1 : ∀ p ∈ B j, g p ≤ 1 - η := fun p hp => (hgB j hj p hp).2
    have hsum : ∑ p ∈ B j, g p ≤ C := hsumB j hj
    have ha_ge := Prelim.SieveCalculus.block_avoidance_ge (B j) g η C
      hη hg0 hg1 hsum
    have hexp : (0 : ℝ) < Real.exp (-C / η) := Real.exp_pos _
    have ha_pos : (0 : ℝ) < blockExpA (B j) g :=
      lt_of_lt_of_le hexp ha_ge
    have hg0' : ∀ p ∈ B j, 0 ≤ g p := hg0
    have hg1' : ∀ p ∈ B j, g p ≤ 1 := fun p hp => by
      have := hg1 p hp
      linarith [hη]
    have hb := blockExp_bounds (B j) g ((j + 1) * h) (hej j hj) hg0' hg1'
    have hSA : blockExpA (B j) g ≤ blockExpS (B j) g ((j + 1) * h) := by
      linarith [hb.1]
    exact lt_of_lt_of_le ha_pos hSA
  have hSne : ∀ j ∈ Finset.range N,
      blockExpS (B j) g ((j + 1) * h) ≠ 0 := fun j hj =>
    ne_of_gt (hSpos j hj)
  unfold corrExp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hprod : blockExpS (B j) g ((j + 1) * h) *
      ∏ k ∈ (Finset.range N).erase j, blockExpS (B k) g ((k + 1) * h)
      = ∏ k ∈ Finset.range N, blockExpS (B k) g ((k + 1) * h) :=
    Finset.mul_prod_erase (Finset.range N)
      (fun k => blockExpS (B k) g ((k + 1) * h)) hj
  have hne := hSne j hj
  field_simp [hprod]
  linear_combination blockExpE (B j) g ((j + 1) * h) * hprod

/-- `R' = ∑ e_j/S_j ≤ R_h = ∑ e_j/A_j` via `S_j ≥ A_j > 0` and `e_j ≥ 0`. -/
theorem R'_le_R (N : ℕ) (B : ℕ → Finset ℕ) (g : ℕ → ℝ) (h : ℕ)
    (η C : ℝ) (hη : 0 < η) (he : Even h)
    (hgB : ∀ j ∈ Finset.range N, ∀ p ∈ B j, 0 ≤ g p ∧ g p ≤ 1 - η)
    (hsumB : ∀ j ∈ Finset.range N, ∑ p ∈ B j, g p ≤ C) :
    (∑ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) /
        blockExpS (B j) g ((j + 1) * h))
      ≤ (∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) := by
  have hej : ∀ j ∈ Finset.range N, Even ((j + 1) * h) :=
    fun j _ => he.mul_left _
  apply Finset.sum_le_sum
  intro j hj
  have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hgB j hj p hp).1
  have hg1η : ∀ p ∈ B j, g p ≤ 1 - η := fun p hp => (hgB j hj p hp).2
  have hsum : ∑ p ∈ B j, g p ≤ C := hsumB j hj
  have ha_ge := Prelim.SieveCalculus.block_avoidance_ge (B j) g η C
    hη hg0 hg1η hsum
  have hexp : (0 : ℝ) < Real.exp (-C / η) := Real.exp_pos _
  have ha_pos : (0 : ℝ) < blockExpA (B j) g :=
    lt_of_lt_of_le hexp ha_ge
  have hg0' : ∀ p ∈ B j, 0 ≤ g p := hg0
  have hg1' : ∀ p ∈ B j, g p ≤ 1 := fun p hp => by
    have := hg1η p hp
    linarith [hη]
  have hb := blockExp_bounds (B j) g ((j + 1) * h) (hej j hj) hg0' hg1'
  have hSA : blockExpA (B j) g ≤ blockExpS (B j) g ((j + 1) * h) := by
    linarith [hb.1]
  have hS_pos : (0 : ℝ) < blockExpS (B j) g ((j + 1) * h) :=
    lt_of_lt_of_le ha_pos hSA
  have he_nn : (0 : ℝ) ≤ blockExpE (B j) g ((j + 1) * h) := by
    unfold blockExpE
    apply Finset.sum_nonneg
    intro T hT
    have hP := trialProb_nonneg (B j) g hg0'
      (fun p hp => by
        have := hg1η p hp
        linarith [hη]) T (Finset.mem_powerset.mp hT)
    have hE : (0 : ℝ) ≤ blockEval ((j + 1) * h) T := by
      unfold blockEval
      exact Nat.cast_nonneg _
    exact mul_nonneg hP hE
  have hdiv : blockExpE (B j) g ((j + 1) * h) /
        blockExpS (B j) g ((j + 1) * h)
      = blockExpE (B j) g ((j + 1) * h) * (1 / blockExpS (B j) g ((j + 1) * h)) := by
    rw [div_eq_mul_one_div]
  have hdiv2 : blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g
      = blockExpE (B j) g ((j + 1) * h) * (1 / blockExpA (B j) g) := by
    rw [div_eq_mul_one_div]
  rw [hdiv, hdiv2]
  have hinv : (1 : ℝ) / blockExpS (B j) g ((j + 1) * h)
      ≤ 1 / blockExpA (B j) g :=
    one_div_le_one_div_of_le ha_pos hSA
  exact mul_le_mul_of_nonneg_left hinv he_nn

/-- Final product error `∏S-∏A ≤ K·e^{-h}·∏A` for large even `h`. -/
theorem exists_prod_error_bound (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ m₀ : ℕ, ∃ K' : ℝ, 0 < K' ∧
      ∀ (h N : ℕ), m₀ ≤ h → Even h →
        ∀ (B : ℕ → Finset ℕ) (g : ℕ → ℝ),
        (∀ j ∈ Finset.range N, ∀ p ∈ B j, 0 ≤ g p ∧ g p ≤ 1 - η) →
        (∀ j ∈ Finset.range N, ∑ p ∈ B j, g p ≤ C) →
        (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
          - (∏ j ∈ Finset.range N, blockExpA (B j) g)
          ≤ K' * Real.exp (-((h : ℕ) : ℝ)) *
            (∏ j ∈ Finset.range N, blockExpA (B j) g) := by
  obtain ⟨m₀R, KR, hKR, hRbound⟩ := exists_R_bound η C hη hC
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (2 * KR)
  refine ⟨max m₀R (max n₁ 1), 2 * KR, mul_pos (by norm_num) hKR, ?_⟩
  intro h N hh0 he B g hgB hsumB
  have hm₀R : m₀R ≤ h :=
    le_trans (le_max_left m₀R (max n₁ 1)) hh0
  have hn₁le : n₁ ≤ h :=
    le_trans (le_trans (le_max_left n₁ 1)
      (le_max_right m₀R (max n₁ 1))) hh0
  -- `le_max_left/right`? Actually `max m₀R (max n₁ 1) ≥ m₀R` via `le_max_left`,
  -- `≥ n₁` via `le_trans (le_max_left n₁ 1) (le_max_right m₀R _)`? Since
  -- `max m₀R (max n₁ 1) ≥ max n₁ 1` via `le_max_right`, and `max n₁ 1 ≥ n₁`
  -- via `le_max_left`. Good! Similarly `≥1` via `le_trans ... (le_max_right _ _)`.
  have hh1 : 1 ≤ h :=
    le_trans (le_trans (le_max_right n₁ 1)
      (le_max_right m₀R (max n₁ 1))) hh0
  have hR := hRbound h N hm₀R hh1 B g hgB hsumB
  -- `R_h ≤ 1/2` from `1+h ≤ e^{h}` + `(h:ℝ) ≥ 2*KR`
  have hRnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g := by
    apply Finset.sum_nonneg
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hgB j hj p hp).1
    have hg1 : ∀ p ∈ B j, g p ≤ 1 - η := fun p hp => (hgB j hj p hp).2
    have hsum : ∑ p ∈ B j, g p ≤ C := hsumB j hj
    have he_nn : (0 : ℝ) ≤ blockExpE (B j) g ((j + 1) * h) := by
      unfold blockExpE
      apply Finset.sum_nonneg
      intro T hT
      have hP := trialProb_nonneg (B j) g hg0
        (fun p hp => by
          have := hg1 p hp
          linarith [hη]) T (Finset.mem_powerset.mp hT)
      have hE : (0 : ℝ) ≤ blockEval ((j + 1) * h) T := by
        unfold blockEval
        exact Nat.cast_nonneg _
      exact mul_nonneg hP hE
    have ha_pos : (0 : ℝ) < blockExpA (B j) g := by
      have ha := Prelim.SieveCalculus.block_avoidance_ge (B j) g η C
        hη hg0 hg1 hsum
      have hexp : (0 : ℝ) < Real.exp (-C / η) := Real.exp_pos _
      exact lt_of_lt_of_le hexp ha
    exact div_nonneg he_nn ha_pos.le
  have hRhalf : ∑ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g ≤ 1 / 2 := by
    have hKRpos : (0 : ℝ) < KR := hKR
    have hn₁R : (2 : ℝ) * KR < ((n₁ : ℕ) : ℝ) := hn₁
    have hhR : ((n₁ : ℕ) : ℝ) ≤ ((h : ℕ) : ℝ) :=
      Nat.cast_le.mpr hn₁le
    have hh2KR : (2 : ℝ) * KR ≤ ((h : ℕ) : ℝ) :=
      le_trans (le_of_lt hn₁R) hhR
    have h1h : ((h : ℕ) : ℝ) + 1 ≤ Real.exp ((h : ℕ) : ℝ) :=
      Real.add_one_le_exp _
    have hexp_ge : (2 : ℝ) * KR ≤ Real.exp ((h : ℕ) : ℝ) :=
      le_trans (by linarith) h1h
    have hexp_pos : (0 : ℝ) < Real.exp ((h : ℕ) : ℝ) := Real.exp_pos _
    have hKR_exp : KR * Real.exp (-((h : ℕ) : ℝ)) ≤ 1 / 2 := by
      have hexp_neg : Real.exp (-((h : ℕ) : ℝ))
          = 1 / Real.exp ((h : ℕ) : ℝ) := by
        rw [Real.exp_neg, inv_eq_one_div]
      rw [hexp_neg, mul_one_div, div_le_iff₀ hexp_pos]
      linarith [hexp_ge]
    calc ∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g
        ≤ KR * Real.exp (-((h : ℕ) : ℝ)) := hR
      _ ≤ 1 / 2 := hKR_exp
  -- final `∏S-∏A ≤ 2·R_h·∏A ≤ K'·e^{-h}·∏A` via telescoping + `R'` + `1/(1-R)`
  have hg1 : ∀ j ∈ Finset.range N, ∀ p ∈ B j, 0 ≤ g p ∧ g p ≤ 1 := by
    intro j hj p hp
    have h1 := (hgB j hj p hp).1
    have h2 := (hgB j hj p hp).2
    exact ⟨h1, by linarith [hη]⟩
  have htele := prod_sub_le_corr N B g h he hg1
  have hcorr := corr_eq_prod_mul N B g h η C hη hC he hgB hsumB
  have hR' := R'_le_R N B g h η C hη he hgB hsumB
  -- `∏S ≥ 0` via `Prob≥0`, `U≥0` (even truncation, case `card=0` vs `≥1`)
  have hSnn : (0 : ℝ) ≤ ∏ j ∈ Finset.range N,
      blockExpS (B j) g ((j + 1) * h) := by
    apply Finset.prod_nonneg
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hgB j hj p hp).1
    have hg1' : ∀ p ∈ B j, g p ≤ 1 := fun p hp => by
      have := (hgB j hj p hp).2
      linarith [hη]
    have hej : Even ((j + 1) * h) := he.mul_left _
    unfold blockExpS
    apply Finset.sum_nonneg
    intro T hT
    have hP := trialProb_nonneg (B j) g hg0 hg1'
      T (Finset.mem_powerset.mp hT)
    have hU : (0 : ℝ) ≤ blockUval ((j + 1) * h) T := by
      unfold blockUval
      by_cases h0 : T.card = 0
      · have hz := Prelim.SieveCalculus.blockUpper_zero ((j + 1) * h)
        rw [h0, hz]
        simp
      · have h1 : 1 ≤ T.card := Nat.pos_of_ne_zero h0
        have hle := Prelim.SieveCalculus.blockUpper_nonneg_of_even
          ((j + 1) * h) T.card hej h1
        exact_mod_cast hle
    exact mul_nonneg hP hU
  -- `∏A ≥ 0` via `1-g ≥ 0`
  have hAnn : (0 : ℝ) ≤ ∏ j ∈ Finset.range N,
      blockExpA (B j) g := by
    apply Finset.prod_nonneg
    intro j hj
    unfold blockExpA
    apply Finset.prod_nonneg
    intro p hp
    have := (hgB j hj p hp).2
    linarith [hη]
  -- `E_corr ≤ (∏S)·R_h` via `R'≤R_h` + `∏S≥0`
  have hcorr_le : corrExp N B g h
      ≤ (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h)) *
        (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) := by
    rw [hcorr]
    apply mul_le_mul_of_nonneg_left _ hSnn
    exact hR'
  -- `∏S-∏A ≤ (∏S)·R_h` via telescoping + above
  have hprod_le : (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
      - (∏ j ∈ Finset.range N, blockExpA (B j) g)
      ≤ (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h)) *
        (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) :=
    le_trans htele hcorr_le
  -- `∏A ≥ 0` already have `hAnn`; `R_h ≥ 0` is `hRnn`; `R_h ≤ 1/2` is `hRhalf`
  have hR_le : (∑ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)
      ≤ KR * Real.exp (-((h : ℕ) : ℝ)) := hR
  have hRhalf' : (∑ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) ≤ 1 / 2 :=
    hRhalf
  -- `∏A ≥ 0` already have `hAnn`; `∏S ≥ 0` is `hSnn`
  have hA_nn := hAnn
  have hS_nn := hSnn
  -- final `∏S-∏A ≤ ∏A·2R_h ≤ K'·e^{-h}·∏A` via `1/(1-R)` + `R≤1/2`
  have h1Rpos : (0 : ℝ) <
      1 - (∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) := by
    linarith [hRhalf]
  have hSmul : (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h)) *
      (1 - (∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g))
      ≤ (∏ j ∈ Finset.range N, blockExpA (B j) g) := by
    have heq : (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h)) *
        (1 - (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g))
        = (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
          - (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h)) *
            (∑ j ∈ Finset.range N,
              blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) := by
      ring
    rw [heq]
    linarith [hprod_le]
  have hInv := one_div_one_sub_le _ hRnn hRhalf
  have hS_div : (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
      ≤ (∏ j ∈ Finset.range N, blockExpA (B j) g) /
        (1 - (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)) :=
    (le_div_iff₀ h1Rpos).mpr hSmul
  have hPA_le : (∏ j ∈ Finset.range N, blockExpA (B j) g) /
      (1 - (∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g))
      ≤ (∏ j ∈ Finset.range N, blockExpA (B j) g) *
        (1 + 2 * (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hInv hAnn
  have hS_le : (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
      ≤ (∏ j ∈ Finset.range N, blockExpA (B j) g) *
        (1 + 2 * (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)) :=
    le_trans hS_div hPA_le
  have hPSR_le : (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h)) *
      (∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)
      ≤ ((∏ j ∈ Finset.range N, blockExpA (B j) g) *
        (1 + 2 * (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g))) *
        (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) :=
    mul_le_mul_of_nonneg_right hS_le hRnn
  have h12 : 1 + 2 * (∑ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) ≤ 2 := by
    linarith [hRhalf]
  have hstep1 : (1 + 2 * (∑ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)) *
      (∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)
      ≤ 2 * (∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) :=
    mul_le_mul_of_nonneg_right h12 hRnn
  have hstep2 : 2 * (∑ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)
      ≤ 2 * (KR * Real.exp (-((h : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_left hR_le (by norm_num)
  have hmid : (1 + 2 * (∑ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)) *
      (∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)
      ≤ 2 * (KR * Real.exp (-((h : ℕ) : ℝ))) :=
    le_trans hstep1 hstep2
  have hPA_mid : (∏ j ∈ Finset.range N, blockExpA (B j) g) *
      ((1 + 2 * (∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)) *
        (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g))
      ≤ (∏ j ∈ Finset.range N, blockExpA (B j) g) *
        (2 * (KR * Real.exp (-((h : ℕ) : ℝ)))) :=
    mul_le_mul_of_nonneg_left hmid hAnn
  calc (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
        - (∏ j ∈ Finset.range N, blockExpA (B j) g)
      ≤ (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h)) *
        (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) :=
        hprod_le
    _ ≤ ((∏ j ∈ Finset.range N, blockExpA (B j) g) *
        (1 + 2 * (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g))) *
        (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) :=
        hPSR_le
    _ = (∏ j ∈ Finset.range N, blockExpA (B j) g) *
        ((1 + 2 * (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)) *
          (∑ j ∈ Finset.range N,
            blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)) := by
        ring
    _ ≤ (∏ j ∈ Finset.range N, blockExpA (B j) g) *
        (2 * (KR * Real.exp (-((h : ℕ) : ℝ)))) :=
        hPA_mid
    _ = 2 * KR * Real.exp (-((h : ℕ) : ℝ)) *
        (∏ j ∈ Finset.range N, blockExpA (B j) g) := by
        ring

/-- Fixed-`h` tail sum bound (constant, for `h = 2` upper; splits at `m₀`). -/
theorem exists_tailSum_fixed_bound (C : ℝ) (hC : 0 ≤ C) (h : ℕ) (hh : 1 ≤ h) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      ∑ j ∈ Finset.range N,
        Prelim.SieveCalculus.tailTerm C ((j + 1) * h) ≤ K := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (Real.exp 1 * C - 2)
  have hden0 : Real.exp 1 * C ≤ (m₀ : ℝ) + 2 := by linarith
  have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have hq := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hr0 : (0 : ℝ) ≤ (Real.exp 1)⁻¹ := inv_nonneg.mpr hexp_pos.le
  have hr1 : (Real.exp 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ he1
  have hrpos : (0 : ℝ) < (Real.exp 1)⁻¹ := inv_pos.mpr hexp_pos
  set r : ℝ := (Real.exp 1)⁻¹ with hrdef
  have hrm0 : (0 : ℝ) < r ^ m₀ := pow_pos hrpos _
  -- small sum over `range m₀`
  set Ksmall : ℝ := ∑ j ∈ Finset.range m₀,
    Prelim.SieveCalculus.tailTerm C ((j + 1) * h) with hKsmall
  have hKsmall_nn : 0 ≤ Ksmall :=
    Finset.sum_nonneg (fun j _ =>
      Prelim.SieveCalculus.tailTerm_nonneg hC _)
  -- geometric constant for large `j`
  have hrh_lt : r ^ h < 1 := by
    calc r ^ h ≤ r ^ 1 := pow_le_pow_of_le_one hr0 hr1.le hh
      _ = r := pow_one r
      _ < 1 := hr1
  have hrh_nn : (0 : ℝ) ≤ r ^ h := pow_nonneg hr0 _
  have h1rh : (0 : ℝ) < 1 - r ^ h := by linarith [hrh_lt]
  have htail0_nn : (0 : ℝ) ≤ Prelim.SieveCalculus.tailTerm C m₀ :=
    Prelim.SieveCalculus.tailTerm_nonneg hC _
  have hpos_div : (0 : ℝ) ≤ Prelim.SieveCalculus.tailTerm C m₀ / r ^ m₀ :=
    div_nonneg htail0_nn (pow_nonneg hr0 _)
  set C0 : ℝ := Prelim.SieveCalculus.tailTerm C m₀ / r ^ m₀ with hC0
  -- per-`j` geometric bound for `j ≥ m₀`
  have hterm : ∀ j : ℕ, m₀ ≤ j →
      Prelim.SieveCalculus.tailTerm C ((j + 1) * h)
        ≤ C0 * (r ^ h) ^ (j + 1) := by
    intro j hj
    have hmh : m₀ ≤ (j + 1) * h := by
      calc m₀ ≤ j := hj
        _ ≤ j + 1 := Nat.le_succ _
        _ ≤ (j + 1) * h := Nat.le_mul_of_pos_right _ hh
    have hgeo := Prelim.SieveCalculus.tailTerm_le_geometric hC m₀
      ((j + 1) * h) hden0 hmh
    have hsub_add : m₀ + ((j + 1) * h - m₀) = (j + 1) * h :=
      Nat.add_sub_cancel' hmh
    have hpow_eq : r ^ ((j + 1) * h)
        = r ^ m₀ * r ^ ((j + 1) * h - m₀) := by
      rw [← pow_add, hsub_add]
    have hpow_eq2 : r ^ ((j + 1) * h) = (r ^ h) ^ (j + 1) := by
      rw [← pow_mul, mul_comm]
    have hdiv : r ^ ((j + 1) * h - m₀)
        = r ^ ((j + 1) * h) / r ^ m₀ := by
      rw [eq_div_iff (ne_of_gt hrm0), hpow_eq, mul_comm]
    rw [← hrdef] at hgeo
    calc Prelim.SieveCalculus.tailTerm C ((j + 1) * h)
        ≤ Prelim.SieveCalculus.tailTerm C m₀ * r ^ ((j + 1) * h - m₀) := hgeo
      _ = Prelim.SieveCalculus.tailTerm C m₀
          * (r ^ ((j + 1) * h) / r ^ m₀) := by rw [hdiv]
      _ = (Prelim.SieveCalculus.tailTerm C m₀ / r ^ m₀)
          * r ^ ((j + 1) * h) := by ring
      _ = C0 * (r ^ h) ^ (j + 1) := by rw [hC0, hpow_eq2]
  have hgeom_total : ∀ N : ℕ,
      ∑ j ∈ Finset.range N, C0 * (r ^ h) ^ (j + 1)
        ≤ C0 * ((r ^ h) / (1 - r ^ h)) := by
    intro N
    have hle := Prelim.SieveCalculus.geom_succ_sum_le hrh_nn hrh_lt N
    calc ∑ j ∈ Finset.range N, C0 * (r ^ h) ^ (j + 1)
        = C0 * ∑ j ∈ Finset.range N, (r ^ h) ^ (j + 1) := by
          rw [Finset.mul_sum]
      _ ≤ C0 * ((r ^ h) / (1 - r ^ h)) :=
          mul_le_mul_of_nonneg_left hle hpos_div
  refine ⟨Ksmall + C0 * ((r ^ h) / (1 - r ^ h)) + 1, by positivity, fun N => ?_⟩
  by_cases hN : N ≤ m₀
  · calc ∑ j ∈ Finset.range N,
          Prelim.SieveCalculus.tailTerm C ((j + 1) * h)
        ≤ ∑ j ∈ Finset.range m₀,
          Prelim.SieveCalculus.tailTerm C ((j + 1) * h) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp only [Finset.mem_range] at hx ⊢
            omega
          · intro j _ _
            exact Prelim.SieveCalculus.tailTerm_nonneg hC _
      _ = Ksmall := rfl
      _ ≤ Ksmall + C0 * ((r ^ h) / (1 - r ^ h)) + 1 := by
          have : (0 : ℝ) ≤ C0 * ((r ^ h) / (1 - r ^ h)) + 1 := by
            have hnn : (0 : ℝ) ≤ C0 * ((r ^ h) / (1 - r ^ h)) :=
              mul_nonneg hpos_div (div_nonneg hrh_nn h1rh.le)
            linarith
          linarith
  · push_neg at hN
    have hleN : m₀ ≤ N := le_of_lt hN
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun j => Prelim.SieveCalculus.tailTerm C ((j + 1) * h)) hleN
    -- `∑ range N = ∑ range m₀ + ∑ Ico m₀ N`
    have hIco_sub : Finset.Ico m₀ N ⊆ Finset.range N := by
      intro x hx
      simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
      omega
    have hlarge_le : ∑ j ∈ Finset.Ico m₀ N,
        Prelim.SieveCalculus.tailTerm C ((j + 1) * h)
        ≤ C0 * ((r ^ h) / (1 - r ^ h)) := by
      calc ∑ j ∈ Finset.Ico m₀ N,
            Prelim.SieveCalculus.tailTerm C ((j + 1) * h)
          ≤ ∑ j ∈ Finset.Ico m₀ N, C0 * (r ^ h) ^ (j + 1) := by
            apply Finset.sum_le_sum
            intro j hj
            simp only [Finset.mem_Ico] at hj
            exact hterm j hj.1
        _ ≤ ∑ j ∈ Finset.range N, C0 * (r ^ h) ^ (j + 1) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hIco_sub
            intro j _ _
            exact mul_nonneg hpos_div (pow_nonneg hrh_nn _)
        _ ≤ C0 * ((r ^ h) / (1 - r ^ h)) := hgeom_total N
    linarith [hsplit, hlarge_le]

/-- Fixed-`h` uniform `R` bound (constant, for `h = 2` upper). -/
theorem exists_R_bound_fixed (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C)
    (h : ℕ) (hh : 1 ≤ h) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (B : ℕ → Finset ℕ) (g : ℕ → ℝ),
      (∀ j ∈ Finset.range N, ∀ p ∈ B j, 0 ≤ g p ∧ g p ≤ 1 - η) →
      (∀ j ∈ Finset.range N, ∑ p ∈ B j, g p ≤ C) →
      ∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g ≤ K := by
  obtain ⟨Ktail, hKtail, htailbound⟩ :=
    exists_tailSum_fixed_bound C hC h hh
  refine ⟨Real.exp (C / η) * Ktail, mul_pos (Real.exp_pos _) hKtail, ?_⟩
  intro N B g hgB hsumB
  have hexpC : (0 : ℝ) < Real.exp (C / η) := Real.exp_pos _
  have hterm : ∀ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g
      ≤ Real.exp (C / η) * Prelim.SieveCalculus.tailTerm C ((j + 1) * h) := by
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hgB j hj p hp).1
    have hg1 : ∀ p ∈ B j, g p ≤ 1 - η := fun p hp => (hgB j hj p hp).2
    have hsum : ∑ p ∈ B j, g p ≤ C := hsumB j hj
    have he_le := blockExpE_le_tail (B j) g ((j + 1) * h) C hg0 hsum
    have ha_le := inv_avoidance_le (B j) g η C hη hg0 hg1 hsum
    have he_nn : (0 : ℝ) ≤ blockExpE (B j) g ((j + 1) * h) := by
      unfold blockExpE
      apply Finset.sum_nonneg
      intro T hT
      have hP := trialProb_nonneg (B j) g hg0
        (fun p hp => by
          have := hg1 p hp
          linarith [hη]) T (Finset.mem_powerset.mp hT)
      have hE : (0 : ℝ) ≤ blockEval ((j + 1) * h) T := by
        unfold blockEval
        exact Nat.cast_nonneg _
      exact mul_nonneg hP hE
    have ha_nn : (0 : ℝ) ≤ 1 / blockExpA (B j) g := by
      apply one_div_nonneg.mpr
      have ha := Prelim.SieveCalculus.block_avoidance_ge (B j) g η C
        hη hg0 hg1 hsum
      have hexp : (0 : ℝ) < Real.exp (-C / η) := Real.exp_pos _
      exact le_of_lt (lt_of_lt_of_le hexp ha)
    have htail_nn : (0 : ℝ) ≤ Prelim.SieveCalculus.tailTerm C ((j + 1) * h) :=
      Prelim.SieveCalculus.tailTerm_nonneg hC _
    calc blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g
        = blockExpE (B j) g ((j + 1) * h) * (1 / blockExpA (B j) g) := by
          rw [div_eq_mul_one_div]
      _ ≤ Prelim.SieveCalculus.tailTerm C ((j + 1) * h)
          * Real.exp (C / η) :=
          mul_le_mul he_le ha_le ha_nn htail_nn
      _ = Real.exp (C / η) * Prelim.SieveCalculus.tailTerm C ((j + 1) * h) := by
          ring
  calc ∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g
      ≤ ∑ j ∈ Finset.range N,
        Real.exp (C / η) * Prelim.SieveCalculus.tailTerm C ((j + 1) * h) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hterm j hj
    _ = Real.exp (C / η) * ∑ j ∈ Finset.range N,
        Prelim.SieveCalculus.tailTerm C ((j + 1) * h) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (C / η) * Ktail := by
        apply mul_le_mul_of_nonneg_left _ hexpC.le
        exact htailbound N

/-- Fixed even-`h` product upper bound `∏S ≤ K·∏A`
(via `S ≤ A+e`, `1+R ≤ e^R`, `∏(1+R) ≤ e^{∑R}`). -/
theorem exists_prod_upper_fixed (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C)
    (h : ℕ) (hh : 1 ≤ h) (he : Even h) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (B : ℕ → Finset ℕ) (g : ℕ → ℝ),
      (∀ j ∈ Finset.range N, ∀ p ∈ B j, 0 ≤ g p ∧ g p ≤ 1 - η) →
      (∀ j ∈ Finset.range N, ∑ p ∈ B j, g p ≤ C) →
      (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
        ≤ K * (∏ j ∈ Finset.range N, blockExpA (B j) g) := by
  obtain ⟨KR, hKR, hRbound⟩ := exists_R_bound_fixed η C hη hC h hh
  refine ⟨Real.exp KR, Real.exp_pos _, fun N B g hgB hsumB => ?_⟩
  have hej : ∀ j ∈ Finset.range N, Even ((j + 1) * h) :=
    fun j _ => he.mul_left _
  -- positivity/nonneg facts
  have hApos : ∀ j ∈ Finset.range N, 0 < blockExpA (B j) g := by
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hgB j hj p hp).1
    have hg1 : ∀ p ∈ B j, g p ≤ 1 - η := fun p hp => (hgB j hj p hp).2
    have hsum : ∑ p ∈ B j, g p ≤ C := hsumB j hj
    have ha := Prelim.SieveCalculus.block_avoidance_ge (B j) g η C
      hη hg0 hg1 hsum
    have hexp : (0 : ℝ) < Real.exp (-C / η) := Real.exp_pos _
    exact lt_of_lt_of_le hexp ha
  have hAnn : (0 : ℝ) ≤ ∏ j ∈ Finset.range N, blockExpA (B j) g :=
    Finset.prod_nonneg (fun j hj => (hApos j hj).le)
  have he_nn : ∀ j ∈ Finset.range N,
      (0 : ℝ) ≤ blockExpE (B j) g ((j + 1) * h) := by
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hgB j hj p hp).1
    have hg1η : ∀ p ∈ B j, g p ≤ 1 - η := fun p hp => (hgB j hj p hp).2
    unfold blockExpE
    apply Finset.sum_nonneg
    intro T hT
    have hP := trialProb_nonneg (B j) g hg0
      (fun p hp => by
        have := hg1η p hp
        linarith [hη]) T (Finset.mem_powerset.mp hT)
    have hE : (0 : ℝ) ≤ blockEval ((j + 1) * h) T := by
      unfold blockEval
      exact Nat.cast_nonneg _
    exact mul_nonneg hP hE
  have hRnn : ∀ j ∈ Finset.range N, (0 : ℝ) ≤
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g :=
    fun j hj => div_nonneg (he_nn j hj) (hApos j hj).le
  have hR := hRbound N B g hgB hsumB
  -- `S_j ≤ A_j + e_j`
  have hSA_le : ∀ j ∈ Finset.range N,
      blockExpS (B j) g ((j + 1) * h)
        ≤ blockExpA (B j) g + blockExpE (B j) g ((j + 1) * h) := by
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hgB j hj p hp).1
    have hg1 : ∀ p ∈ B j, g p ≤ 1 := fun p hp => by
      have := (hgB j hj p hp).2
      linarith [hη]
    have hb := blockExp_bounds (B j) g ((j + 1) * h) (hej j hj) hg0 hg1
    linarith [hb.2]
  have hSnn : ∀ j ∈ Finset.range N,
      (0 : ℝ) ≤ blockExpS (B j) g ((j + 1) * h) := by
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hgB j hj p hp).1
    have hg1 : ∀ p ∈ B j, g p ≤ 1 := fun p hp => by
      have := (hgB j hj p hp).2
      linarith [hη]
    have hej' := hej j hj
    unfold blockExpS
    apply Finset.sum_nonneg
    intro T hT
    have hP := trialProb_nonneg (B j) g hg0 hg1 T (Finset.mem_powerset.mp hT)
    have hU : (0 : ℝ) ≤ blockUval ((j + 1) * h) T := by
      unfold blockUval
      by_cases h0 : T.card = 0
      · have hz := Prelim.SieveCalculus.blockUpper_zero ((j + 1) * h)
        rw [h0, hz]
        simp
      · have h1 : 1 ≤ T.card := Nat.pos_of_ne_zero h0
        have hle := Prelim.SieveCalculus.blockUpper_nonneg_of_even
          ((j + 1) * h) T.card hej' h1
        exact_mod_cast hle
    exact mul_nonneg hP hU
  -- `A+e = A*(1+R)`
  have hAe_eq : ∀ j ∈ Finset.range N,
      blockExpA (B j) g + blockExpE (B j) g ((j + 1) * h)
        = blockExpA (B j) g *
          (1 + blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) := by
    intro j hj
    have hne : blockExpA (B j) g ≠ 0 := ne_of_gt (hApos j hj)
    field_simp
  have h1R_le : ∀ j ∈ Finset.range N,
      1 + blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g
        ≤ Real.exp (blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) := by
    intro j hj
    have hq := Real.add_one_le_exp
      (blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)
    linarith
  have hprod_S_le : (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
      ≤ ∏ j ∈ Finset.range N,
        (blockExpA (B j) g + blockExpE (B j) g ((j + 1) * h)) := by
    apply Finset.prod_le_prod₀
    · intro j hj
      exact hSnn j hj
    · intro j hj
      exact hSA_le j hj
  have hprod_Ae : ∏ j ∈ Finset.range N,
      (blockExpA (B j) g + blockExpE (B j) g ((j + 1) * h))
      = (∏ j ∈ Finset.range N, blockExpA (B j) g) *
        (∏ j ∈ Finset.range N,
          (1 + blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)) := by
    have : ∀ j ∈ Finset.range N,
        blockExpA (B j) g + blockExpE (B j) g ((j + 1) * h)
          = blockExpA (B j) g *
            (1 + blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) :=
      hAe_eq
    rw [Finset.prod_congr rfl this]
    rw [Finset.prod_mul_distrib]
  have hprod_1R_le : ∏ j ∈ Finset.range N,
      (1 + blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)
      ≤ Real.exp (∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) := by
    have hle : ∏ j ∈ Finset.range N,
        (1 + blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)
        ≤ ∏ j ∈ Finset.range N,
          Real.exp (blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        linarith [hRnn j hj]
      · intro j hj
        exact h1R_le j hj
    rw [← Real.exp_sum] at hle
    exact hle
  have hexp_le : Real.exp (∑ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)
      ≤ Real.exp KR :=
    Real.exp_le_exp.mpr hR
  calc (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
      ≤ ∏ j ∈ Finset.range N,
        (blockExpA (B j) g + blockExpE (B j) g ((j + 1) * h)) := hprod_S_le
    _ = (∏ j ∈ Finset.range N, blockExpA (B j) g) *
        (∏ j ∈ Finset.range N,
          (1 + blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)) :=
        hprod_Ae
    _ ≤ (∏ j ∈ Finset.range N, blockExpA (B j) g) * Real.exp KR := by
        apply mul_le_mul_of_nonneg_left _ hAnn
        exact le_trans hprod_1R_le hexp_le
    _ = Real.exp KR * (∏ j ∈ Finset.range N, blockExpA (B j) g) := by
        ring

/-- Correction error `corrExp ≤ K·e^{-h}·∏A` for large even `h`
(via `corr=∏S·R'`, `R'≤R≤KR·e^{-h}`, `∏S-∏A≤K'·e^{-h}·∏A`). -/
theorem exists_corr_error_bound (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ m₀ : ℕ, ∃ Kcorr : ℝ, 0 < Kcorr ∧
      ∀ (h N : ℕ), m₀ ≤ h → Even h →
        ∀ (B : ℕ → Finset ℕ) (g : ℕ → ℝ),
        (∀ j ∈ Finset.range N, ∀ p ∈ B j, 0 ≤ g p ∧ g p ≤ 1 - η) →
        (∀ j ∈ Finset.range N, ∑ p ∈ B j, g p ≤ C) →
        corrExp N B g h
          ≤ Kcorr * Real.exp (-((h : ℕ) : ℝ)) *
            (∏ j ∈ Finset.range N, blockExpA (B j) g) := by
  obtain ⟨m₀R, KR, hKR, hRbound⟩ := exists_R_bound η C hη hC
  obtain ⟨m₀P, K', hK', hPbound⟩ := exists_prod_error_bound η C hη hC
  refine ⟨max m₀R (max m₀P 1), KR * (1 + K'), mul_pos hKR (by linarith), ?_⟩
  intro h N hh0 he B g hgB hsumB
  have hmR : m₀R ≤ h :=
    le_trans (le_max_left m₀R (max m₀P 1)) hh0
  have hmP : m₀P ≤ h :=
    le_trans (le_trans (le_max_left m₀P 1)
      (le_max_right m₀R (max m₀P 1))) hh0
  have hh1 : 1 ≤ h :=
    le_trans (le_trans (le_max_right m₀P 1)
      (le_max_right m₀R (max m₀P 1))) hh0
  have hR := hRbound h N hmR hh1 B g hgB hsumB
  have hP := hPbound h N hmP he B g hgB hsumB
  have hcorr := corr_eq_prod_mul N B g h η C hη hC he hgB hsumB
  have hR' := R'_le_R N B g h η C hη he hgB hsumB
  have hej : ∀ j ∈ Finset.range N, Even ((j + 1) * h) :=
    fun j _ => he.mul_left _
  -- nonneg facts
  have hSnn_prod : (0 : ℝ) ≤ ∏ j ∈ Finset.range N,
      blockExpS (B j) g ((j + 1) * h) := by
    apply Finset.prod_nonneg
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hgB j hj p hp).1
    have hg1 : ∀ p ∈ B j, g p ≤ 1 := fun p hp => by
      have := (hgB j hj p hp).2
      linarith [hη]
    have hej' := hej j hj
    unfold blockExpS
    apply Finset.sum_nonneg
    intro T hT
    have hPp := trialProb_nonneg (B j) g hg0 hg1 T (Finset.mem_powerset.mp hT)
    have hU : (0 : ℝ) ≤ blockUval ((j + 1) * h) T := by
      unfold blockUval
      by_cases h0 : T.card = 0
      · have hz := Prelim.SieveCalculus.blockUpper_zero ((j + 1) * h)
        rw [h0, hz]
        simp
      · have h1 : 1 ≤ T.card := Nat.pos_of_ne_zero h0
        have hle := Prelim.SieveCalculus.blockUpper_nonneg_of_even
          ((j + 1) * h) T.card hej' h1
        exact_mod_cast hle
    exact mul_nonneg hPp hU
  have hAnn : (0 : ℝ) ≤ ∏ j ∈ Finset.range N,
      blockExpA (B j) g := by
    apply Finset.prod_nonneg
    intro j hj
    unfold blockExpA
    apply Finset.prod_nonneg
    intro p hp
    have := (hgB j hj p hp).2
    linarith [hη]
  have hexp_nn : (0 : ℝ) ≤ Real.exp (-((h : ℕ) : ℝ)) :=
    (Real.exp_pos _).le
  have hexp_le_one : Real.exp (-((h : ℕ) : ℝ)) ≤ 1 := by
    have hle : -((h : ℕ) : ℝ) ≤ 0 := by
      have : (0 : ℝ) ≤ ((h : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    calc Real.exp (-((h : ℕ) : ℝ)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr hle
      _ = 1 := Real.exp_zero
  -- `corr = ∏S·R' ≤ ∏S·R`
  have hcorr_le : corrExp N B g h
      ≤ (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h)) *
        (∑ j ∈ Finset.range N,
          blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g) := by
    rw [hcorr]
    apply mul_le_mul_of_nonneg_left _ hSnn_prod
    exact hR'
  -- `(∏S)·R ≤ (∏A + K'e^{-h}∏A)·(KR·e^{-h})`
  have hRnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range N,
      blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g := by
    apply Finset.sum_nonneg
    intro j hj
    have hg0 : ∀ p ∈ B j, 0 ≤ g p := fun p hp => (hgB j hj p hp).1
    have hg1 : ∀ p ∈ B j, g p ≤ 1 - η := fun p hp => (hgB j hj p hp).2
    have hsum : ∑ p ∈ B j, g p ≤ C := hsumB j hj
    have he_nn : (0 : ℝ) ≤ blockExpE (B j) g ((j + 1) * h) := by
      unfold blockExpE
      apply Finset.sum_nonneg
      intro T hT
      have hPp := trialProb_nonneg (B j) g hg0
        (fun p hp => by
          have := hg1 p hp
          linarith [hη]) T (Finset.mem_powerset.mp hT)
      have hE : (0 : ℝ) ≤ blockEval ((j + 1) * h) T := by
        unfold blockEval
        exact Nat.cast_nonneg _
      exact mul_nonneg hPp hE
    have ha_pos : (0 : ℝ) < blockExpA (B j) g := by
      have ha := Prelim.SieveCalculus.block_avoidance_ge (B j) g η C
        hη hg0 hg1 hsum
      have hexp : (0 : ℝ) < Real.exp (-C / η) := Real.exp_pos _
      exact lt_of_lt_of_le hexp ha
    exact div_nonneg he_nn ha_pos.le
  have hK'nn : (0 : ℝ) ≤ K' * Real.exp (-((h : ℕ) : ℝ)) *
      (∏ j ∈ Finset.range N, blockExpA (B j) g) :=
    mul_nonneg (mul_nonneg hK'.le hexp_nn) hAnn
  have hstep : (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h)) *
      (∑ j ∈ Finset.range N,
        blockExpE (B j) g ((j + 1) * h) / blockExpA (B j) g)
      ≤ ((∏ j ∈ Finset.range N, blockExpA (B j) g)
        + K' * Real.exp (-((h : ℕ) : ℝ)) *
          (∏ j ∈ Finset.range N, blockExpA (B j) g))
        * (KR * Real.exp (-((h : ℕ) : ℝ))) := by
    have hS_eq : (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
        = (∏ j ∈ Finset.range N, blockExpA (B j) g)
          + ((∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
            - (∏ j ∈ Finset.range N, blockExpA (B j) g)) := by
      ring
    rw [hS_eq]
    apply mul_le_mul
    · -- `∏A + (∏S-∏A) ≤ ∏A + K'e^{-h}∏A`
      have := hP
      linarith
    · exact hR
    · exact hRnn
    · apply add_nonneg hAnn hK'nn
  have hexp2 : Real.exp (-((h : ℕ) : ℝ)) * Real.exp (-((h : ℕ) : ℝ))
      ≤ Real.exp (-((h : ℕ) : ℝ)) := by
    have hmul : Real.exp (-((h : ℕ) : ℝ)) * Real.exp (-((h : ℕ) : ℝ))
        = (Real.exp (-((h : ℕ) : ℝ))) ^ 2 := by ring
    rw [hmul]
    calc (Real.exp (-((h : ℕ) : ℝ))) ^ 2
        ≤ (Real.exp (-((h : ℕ) : ℝ))) ^ 1 := by
          apply pow_le_pow_of_le_one hexp_nn hexp_le_one (by norm_num)
      _ = Real.exp (-((h : ℕ) : ℝ)) := pow_one _
  calc corrExp N B g h
      ≤ ((∏ j ∈ Finset.range N, blockExpA (B j) g)
        + K' * Real.exp (-((h : ℕ) : ℝ)) *
          (∏ j ∈ Finset.range N, blockExpA (B j) g))
        * (KR * Real.exp (-((h : ℕ) : ℝ))) :=
        le_trans hcorr_le hstep
    _ = KR * Real.exp (-((h : ℕ) : ℝ)) *
          (∏ j ∈ Finset.range N, blockExpA (B j) g)
        + (KR * K') * (Real.exp (-((h : ℕ) : ℝ)) *
          Real.exp (-((h : ℕ) : ℝ))) *
          (∏ j ∈ Finset.range N, blockExpA (B j) g) := by
        ring
    _ ≤ KR * Real.exp (-((h : ℕ) : ℝ)) *
          (∏ j ∈ Finset.range N, blockExpA (B j) g)
        + (KR * K') * Real.exp (-((h : ℕ) : ℝ)) *
          (∏ j ∈ Finset.range N, blockExpA (B j) g) := by
        have hmul_le : (KR * K') * (Real.exp (-((h : ℕ) : ℝ)) *
            Real.exp (-((h : ℕ) : ℝ)))
            ≤ (KR * K') * Real.exp (-((h : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp2 (mul_nonneg hKR.le hK'.le)
        have := mul_le_mul_of_nonneg_right hmul_le hAnn
        linarith [this]
    _ = KR * (1 + K') * Real.exp (-((h : ℕ) : ℝ)) *
        (∏ j ∈ Finset.range N, blockExpA (B j) g) := by
        ring

end PrelimLemmas
end Erdos821
