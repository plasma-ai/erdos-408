import Erdos821.P5.ComparisonCellScales
import Erdos821.P5.CutoffSupport

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem comparison_cell_free_product_bounds
    {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool)
    (h : ℝ) (hh : 0 < h) (hwidth : Real.exp (2 * h) ≤ 2)
    (j : ℤ × ℤ) (u : FreeDraw ν) (z : SharedDraw ν) (hu : comparisonCellPair ν block h u = j) :
    comparisonJointScale h j ≤ (freeDrawProduct ν u : ℝ) ∧
      (freeDrawProduct ν u : ℝ) ≤ 2 * comparisonJointScale h j := by
  have hp := comparisonJointScale_product_bounds ν block h hh u
  rw [hu] at hp
  rw [freeDrawProduct_eq_comparisonProducts ν block u z, Nat.cast_mul]
  exact ⟨hp.1, hp.2.le.trans (mul_le_mul_of_nonneg_right hwidth
    (comparisonJointScale_pos h j).le)⟩

/-- Both endpoint locations lie in fixed positive intervals at the occupied
cell scale Y=Z*H'. The intervals do not depend on the free draw. -/
theorem comparison_cutoff_source_target_ranges
    {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool)
    (h : ℝ) (hh : 0 < h) (hwidth : Real.exp (2 * h) ≤ 2)
    (j : ℤ × ℤ) (u : FreeDraw ν) (z : SharedDraw ν) (hu : comparisonCellPair ν block h u = j)
    (lo hi Z : ℝ) (k : ℤ) (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (hk : |(k : ℝ)| ≤ lo * Z / 2) (n : ℕ)
    (hn : n ∈ cutoffRoots lo hi Z (freeDrawProduct ν u)) :
    lo * (Z * comparisonJointScale h j) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ 2 * hi * (Z * comparisonJointScale h j) ∧
      0 < (n : ℤ) + k * (freeDrawProduct ν u : ℤ) ∧
      lo / 2 * (Z * comparisonJointScale h j) ≤
        (((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat : ℝ) ∧
      (((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat : ℝ) ≤
        (2 * hi + lo) * (Z * comparisonJointScale h j) := by
  have hhi0 : 0 < hi := hlo.trans hhi
  have hD : (0 : ℝ) < freeDrawProduct ν u := by exact_mod_cast freeDrawProduct_pos ν u
  have hS := comparisonJointScale_pos h j
  obtain ⟨hDlo, hDhi⟩ := comparison_cell_free_product_bounds ν block h hh hwidth j u z hu
  obtain ⟨hnlo, hnhi⟩ := (mem_cutoffRoots lo hi Z _ n (by positivity)).mp hn
  have hkD := mul_le_mul_of_nonneg_right hk hD.le
  have hklo := mul_le_mul_of_nonneg_right (neg_abs_le (k : ℝ)) hD.le
  have hkhi := mul_le_mul_of_nonneg_right (le_abs_self (k : ℝ)) hD.le
  have hn'lo : lo / 2 * Z * freeDrawProduct ν u ≤
      (n : ℝ) + (k : ℝ) * freeDrawProduct ν u := by nlinarith
  have hn'hi : (n : ℝ) + (k : ℝ) * freeDrawProduct ν u ≤
      (hi + lo / 2) * Z * freeDrawProduct ν u := by nlinarith
  have hn'R : 0 < (n : ℝ) + (k : ℝ) * freeDrawProduct ν u :=
    (by positivity : 0 < lo / 2 * Z * freeDrawProduct ν u).trans_le hn'lo
  have hn' : 0 < (n : ℤ) + k * (freeDrawProduct ν u : ℤ) := by exact_mod_cast hn'R
  have hcast : (((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat : ℝ) =
      (n : ℝ) + (k : ℝ) * freeDrawProduct ν u := by
    exact_mod_cast Int.toNat_of_nonneg hn'.le
  refine ⟨?_, ?_, hn', ?_, ?_⟩
  · calc
      _ = lo * Z * comparisonJointScale h j := by ring
      _ ≤ lo * Z * freeDrawProduct ν u :=
        mul_le_mul_of_nonneg_left hDlo (mul_pos hlo hZ).le
      _ ≤ _ := hnlo
  · calc
      _ ≤ hi * Z * freeDrawProduct ν u := hnhi
      _ ≤ hi * Z * (2 * comparisonJointScale h j) :=
        mul_le_mul_of_nonneg_left hDhi (mul_pos hhi0 hZ).le
      _ = _ := by ring
  · rw [hcast]
    calc
      _ = lo / 2 * Z * comparisonJointScale h j := by ring
      _ ≤ lo / 2 * Z * freeDrawProduct ν u :=
        mul_le_mul_of_nonneg_left hDlo (by positivity)
      _ ≤ _ := hn'lo
  · rw [hcast]
    calc
      _ ≤ (hi + lo / 2) * Z * freeDrawProduct ν u := hn'hi
      _ ≤ (hi + lo / 2) * Z * (2 * comparisonJointScale h j) :=
        mul_le_mul_of_nonneg_left hDhi (by positivity)
      _ = _ := by ring

def comparisonCommonRoots (lo hi Y : ℝ) : Finset ℕ :=
  Finset.Icc ⌈lo / 2 * Y⌉₊ ⌊(2 * hi + lo) * Y⌋₊

theorem comparison_cutoffRoots_subset_common
    {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool)
    (h : ℝ) (hh : 0 < h) (hwidth : Real.exp (2 * h) ≤ 2)
    (j : ℤ × ℤ) (u : FreeDraw ν) (z : SharedDraw ν) (hu : comparisonCellPair ν block h u = j)
    (lo hi Z : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z) :
    cutoffRoots lo hi Z (freeDrawProduct ν u) ⊆
      comparisonCommonRoots lo hi (Z * comparisonJointScale h j) := by
  intro n hn
  have hr := comparison_cutoff_source_target_ranges ν block h hh hwidth j u z hu
    lo hi Z 0 hlo hhi hZ (by simp; positivity) n hn
  apply Finset.mem_Icc.mpr
  constructor
  · apply Nat.ceil_le.mpr
    nlinarith [mul_pos hZ (comparisonJointScale_pos h j)]
  · apply Nat.le_floor
    nlinarith [mul_pos hZ (comparisonJointScale_pos h j)]

/-- The coupled root interval is replaced by one fixed interval, using the
original cutoff's zero values. No cancellation estimate is used. -/
theorem comparison_sum_extend_common_roots
    {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool)
    (h : ℝ) (hh : 0 < h) (hwidth : Real.exp (2 * h) ≤ 2)
    (j : ℤ × ℤ) (u : FreeDraw ν) (z : SharedDraw ν) (hu : comparisonCellPair ν block h u = j)
    (lo hi Z : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (Ψ : ℝ → ℂ) (hs : Function.support Ψ ⊆ Set.Icc lo hi)
    (f : ℕ → ℂ) :
    (∑ n ∈ cutoffRoots lo hi Z (freeDrawProduct ν u),
      Ψ ((n : ℝ) / (Z * freeDrawProduct ν u)) * f n) =
    ∑ n ∈ comparisonCommonRoots lo hi (Z * comparisonJointScale h j),
      Ψ ((n : ℝ) / (Z * freeDrawProduct ν u)) * f n := by
  apply Finset.sum_subset (comparison_cutoffRoots_subset_common ν block h hh hwidth j u z hu
    lo hi Z hlo hhi hZ)
  intro n hn hnot
  have hz : Ψ ((n : ℝ) / (Z * freeDrawProduct ν u)) = 0 := by
    by_contra hne
    exact hnot (cutoffRoots_of_nonzero lo hi Z _ n Ψ hZ (freeDrawProduct_pos ν u)
      (hlo.trans hhi) hs hne)
  rw [hz, zero_mul]

theorem strippedLiftScalar_cutoff_factor (G : PrimeGroups) (x Z a₁ a₂ : ℝ)
    (E H : Endpoint) (Ψ : ℝ → ℂ) (w w' D : ℕ) :
    strippedLiftScalar G x Z a₁ a₂ E H Ψ w w' D =
      Ψ ((w : ℝ) / (Z * D)) * strippedLiftScalar G x Z a₁ a₂ E H (fun _ => 1) w w' D := by
  unfold strippedLiftScalar harmonicCutoff
  simp only [Int.cast_natCast]
  ring

/-- The actual cell correlation has one root interval independent of the
two free products. Zero values of the original cutoff justify extension. -/
theorem comparisonCellCorrelation_eq_common_roots
    {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
    (h : ℝ) (hh : 0 < h) (hwidth : Real.exp (2 * h) ≤ 2)
    (j : ℤ × ℤ) (χA χB : CharacterIndex Q) (z : SharedDraw ν)
    (x Z a₁ a₂ lo hi : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ)
    (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (hs : Function.support Ψ ⊆ Set.Icc lo hi) :
    comparisonCellCorrelation ν block h j χA χB x Z a₁ a₂ E H Ψ k
      (fun u => cutoffRoots lo hi Z (freeDrawProduct ν u)) =
    comparisonCellCorrelation ν block h j χA χB x Z a₁ a₂ E H Ψ k
      (fun _ => comparisonCommonRoots lo hi (Z * comparisonJointScale h j)) := by
  unfold comparisonCellCorrelation
  apply Finset.sum_congr rfl
  intro u hu
  simp_rw [strippedLiftScalar_cutoff_factor G x Z a₁ a₂ E H Ψ]
  congr 1
  have he := comparison_sum_extend_common_roots ν block h hh hwidth j u z
    (Finset.mem_filter.mp hu).2 lo hi Z hlo hhi hZ Ψ hs
    (fun n => strippedLiftScalar G x Z a₁ a₂ E H (fun _ => 1) n
      ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat (freeDrawProduct ν u) *
      (comparisonMarkedEndpoint ν block true h j.2 χB n *
        comparisonMarkedEndpoint ν block false h j.1 χA
          ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat))
  simpa only [mul_assoc] using he

theorem comparison_common_root_positivity
    {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool)
    (h : ℝ) (hh : 0 < h) (hwidth : Real.exp (2 * h) ≤ 2)
    (j : ℤ × ℤ) (u : FreeDraw ν) (z : SharedDraw ν)
    (hu : comparisonCellPair ν block h u = j) (lo hi Z : ℝ) (k : ℤ)
    (hlo : 0 < lo) (hZ : 0 < Z) (hk : |(k : ℝ)| ≤ lo * Z / 8)
    (n : ℕ) (hn : n ∈ comparisonCommonRoots lo hi (Z * comparisonJointScale h j)) :
    0 < n ∧ 0 < (n : ℤ) + k * (freeDrawProduct ν u : ℤ) := by
  have hY := mul_pos hZ (comparisonJointScale_pos h j)
  have hnlo : lo / 2 * (Z * comparisonJointScale h j) ≤ (n : ℝ) :=
    Nat.le_of_ceil_le (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < n := (by positivity : 0 < lo / 2 *
    (Z * comparisonJointScale h j)).trans_le hnlo
  have hD : (0 : ℝ) ≤ freeDrawProduct ν u := Nat.cast_nonneg _
  have hDhi := (comparison_cell_free_product_bounds ν block h hh hwidth j u z hu).2
  have hshift := mul_le_mul hk hDhi hD (by positivity : 0 ≤ lo * Z / 8)
  have hklo := mul_le_mul_of_nonneg_right (neg_abs_le (k : ℝ)) hD
  have hp : 0 < (n : ℝ) + (k : ℝ) * freeDrawProduct ν u := by
    nlinarith [mul_pos hlo hY]
  exact ⟨by exact_mod_cast hnpos, by exact_mod_cast hp⟩

end Erdos821.P5Core
