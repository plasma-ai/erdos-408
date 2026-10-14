import Erdos821.P5.IntegerComparisonSupport

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core

/-- Includes centers just outside [0,1], so boundary arcs are retained. -/
def rationalArcCenters (R : ℕ) : Finset ℝ :=
  (Finset.Icc 1 R).biUnion fun r =>
    (Finset.Icc (-(r : ℤ)) (2 * (r : ℤ))).image (fun u : ℤ => (u : ℝ) / r)

theorem rationalArcCenters_mem (R r : ℕ) (u : ℤ) (hr : 1 ≤ r) (hrR : r ≤ R)
    (hu : -(r : ℤ) ≤ u ∧ u ≤ 2 * (r : ℤ)) :
    (u : ℝ) / r ∈ rationalArcCenters R := by
  apply Finset.mem_biUnion.mpr
  exact ⟨r, Finset.mem_Icc.mpr ⟨hr, hrR⟩,
    Finset.mem_image.mpr ⟨u, Finset.mem_Icc.mpr hu, rfl⟩⟩

theorem rationalArcCenters_card_le (R : ℕ) (hR : 1 ≤ R) :
    (rationalArcCenters R).card ≤ 4 * R ^ 2 := by
  have hc (r : ℕ) (hr : r ∈ Finset.Icc 1 R) :
      ((Finset.Icc (-(r : ℤ)) (2 * (r : ℤ))).image
        (fun u : ℤ => (u : ℝ) / r)).card ≤ 4 * R := by
    apply Finset.card_image_le.trans
    rw [Int.card_Icc]
    have hrR := (Finset.mem_Icc.mp hr).2
    omega
  have hb := Finset.card_biUnion_le_card_mul (Finset.Icc 1 R)
    (fun r => (Finset.Icc (-(r : ℤ)) (2 * (r : ℤ))).image
      (fun u : ℤ => (u : ℝ) / r)) (4 * R) hc
  simpa [rationalArcCenters, Nat.card_Icc, pow_two, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hb

theorem rationalArcCenters_cover (R r : ℕ) (u : ℤ) (θ Δ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hΔ : Δ < 1)
    (hr : 1 ≤ r) (hrR : r ≤ R) (hnear : |θ - (u : ℝ) / r| ≤ Δ) :
    (u : ℝ) / r ∈ rationalArcCenters R := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hdist := abs_le.mp hnear
  have hul : -(r : ℝ) ≤ (u : ℝ) := by
    have h := (le_div_iff₀ hrpos).mp (show (-1 : ℝ) ≤ (u : ℝ) / r by
      linarith [hθ.1, hdist.2])
    simpa only [neg_one_mul] using h
  have hur : (u : ℝ) ≤ 2 * (r : ℝ) :=
    (div_le_iff₀ hrpos).mp (by linarith [hθ.2, hdist.1])
  apply rationalArcCenters_mem R r u hr hrR
  exact ⟨by exact_mod_cast hul, by exact_mod_cast hur⟩

theorem rationalArcCenters_card_real_le (Rbound : ℝ) (hRbound : 1 ≤ Rbound) :
    ((rationalArcCenters ⌊Rbound⌋₊).card : ℝ) ≤ 4 * Rbound ^ 2 := by
  have hR : 1 ≤ ⌊Rbound⌋₊ := Nat.le_floor (by simpa using hRbound)
  have hc : ((rationalArcCenters ⌊Rbound⌋₊).card : ℝ) ≤ 4 * (⌊Rbound⌋₊ : ℝ) ^ 2 := by
    exact_mod_cast rationalArcCenters_card_le ⌊Rbound⌋₊ hR
  have hf : (⌊Rbound⌋₊ : ℝ) ≤ Rbound := Nat.floor_le (by linarith : 0 ≤ Rbound)
  have hf0 : (0 : ℝ) ≤ (⌊Rbound⌋₊ : ℝ) := Nat.cast_nonneg _
  exact hc.trans (by nlinarith)

theorem rationalArcCenters_avoid_all (R : ℕ) (θ Δ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hΔ : Δ < 1)
    (haway : ∀ c ∈ rationalArcCenters R, Δ < |θ - c|) :
    ∀ (r : ℕ) (u : ℤ), 1 ≤ r → r ≤ R → Δ < |θ - (u : ℝ) / r| := by
  intro r u hr hrR
  by_contra hnot
  exact (not_lt_of_ge (le_of_not_gt hnot))
    (haway _ (rationalArcCenters_cover R r u θ Δ hθ hΔ hr hrR (le_of_not_gt hnot)))

theorem rationalArcCenters_avoid_real_bound (Rbound θ Δ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hΔ : Δ < 1)
    (haway : ∀ c ∈ rationalArcCenters ⌊Rbound⌋₊, Δ < |θ - c|) :
    ∀ (r : ℕ) (u : ℤ), 1 ≤ r → (r : ℝ) ≤ Rbound →
      Δ < |θ - (u : ℝ) / r| := by
  intro r u hr hrR
  exact rationalArcCenters_avoid_all _ θ Δ hθ hΔ haway r u hr (Nat.le_floor hrR)

end Erdos821.P5Core
