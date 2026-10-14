import Mathlib
import Erdos821.Blueprint.Sieve

/-!
# Sieve geometry: dyadic blocks `B_j = {p : Z_{j+1} < p ≤ Z_j}` (`lem:sieve`)

For `z > 1`, `Z_j = z^{1/2^j}` (`Real.rpow`), so `Z_0 = z`, `Z_j = (Z_{j+1})^2`,
`Z_j > 1`, decreasing to `1`. For `Jmax` with `Z_{Jmax} < 2`, the blocks
`B_j`, `j < Jmax`, partition `{p ∈ S.primes}` (`2 ≤ p ≤ z`), each of the form
`(w, w^2]` with `w > 1`, so the blueprint density hypothesis gives block mass
`≤ C`. The level exponent sum `∑ (j+1)/2^j ≤ 4` (`SieveCalculus.level_sum_le`)
gives the paper's `z^{4h+2}` level.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
namespace Erdos821
namespace PrelimLemmas

/-- Geometric scale `Z_j = z^{1/2^j}`. -/
noncomputable def Zscale (z : ℝ) (j : ℕ) : ℝ :=
  z ^ ((1 : ℝ) / ((2 : ℝ) ^ j))

theorem Zscale_pos {z : ℝ} (hz : 0 < z) (j : ℕ) : 0 < Zscale z j := by
  unfold Zscale
  exact Real.rpow_pos_of_pos hz _

theorem Zscale_gt_one {z : ℝ} (hz : 1 < z) (j : ℕ) : 1 < Zscale z j := by
  unfold Zscale
  apply Real.one_lt_rpow hz
  apply one_div_pos.mpr
  exact pow_pos (by norm_num) j

theorem Zscale_zero {z : ℝ} : Zscale z 0 = z := by
  unfold Zscale
  simp [Real.rpow_one]

/-- `Z_j = (Z_{j+1})^2` (so each block is `(w, w^2]`). -/
theorem Zscale_succ_sq {z : ℝ} (hz : 0 ≤ z) (j : ℕ) :
    Zscale z j = (Zscale z (j + 1)) ^ (2 : ℕ) := by
  unfold Zscale
  have h2j1 : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := pow_succ' 2 j
  have hexp : (1 : ℝ) / (2 : ℝ) ^ (j + 1) * 2 = (1 : ℝ) / (2 : ℝ) ^ j := by
    rw [h2j1]
    field_simp
  have h1 : (z ^ ((1 : ℝ) / (2 : ℝ) ^ (j + 1))) ^ (2 : ℕ)
      = z ^ (((1 : ℝ) / (2 : ℝ) ^ (j + 1)) * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz]
    congr 1
  rw [h1, hexp]

theorem Zscale_succ_le {z : ℝ} (hz : 1 < z) (j : ℕ) :
    Zscale z (j + 1) ≤ Zscale z j := by
  have hsq : Zscale z j = (Zscale z (j + 1)) ^ (2 : ℕ) :=
    Zscale_succ_sq (le_of_lt (lt_trans one_pos hz)) j
  have hw : 1 ≤ Zscale z (j + 1) := le_of_lt (Zscale_gt_one hz _)
  have hle : Zscale z (j + 1) ≤ (Zscale z (j + 1)) ^ (2 : ℕ) := by
    calc Zscale z (j + 1) = Zscale z (j + 1) * 1 := (mul_one _).symm
      _ ≤ Zscale z (j + 1) * Zscale z (j + 1) :=
          mul_le_mul_of_nonneg_left hw (le_of_lt (Zscale_pos (lt_trans one_pos hz) _))
      _ = (Zscale z (j + 1)) ^ (2 : ℕ) := by rw [pow_two]
  calc Zscale z (j + 1) ≤ (Zscale z (j + 1)) ^ (2 : ℕ) := hle
    _ = Zscale z j := hsq.symm

theorem Zscale_antitone {z : ℝ} (hz : 1 < z) {j₁ j₂ : ℕ} (h : j₁ ≤ j₂) :
    Zscale z j₂ ≤ Zscale z j₁ := by
  induction j₂, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact le_trans (Zscale_succ_le hz n) ih

/-- There is `J` with `Z_J < 2` (so blocks up to `J` cover all primes `≥ 2`). -/
theorem exists_Zscale_lt_two {z : ℝ} (hz : 1 < z) :
    ∃ J : ℕ, Zscale z J < 2 := by
  have hz0 : (0 : ℝ) < z := lt_trans one_pos hz
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos hz
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (Real.log z / Real.log 2) one_lt_two
  refine ⟨J, ?_⟩
  have h2J : (0 : ℝ) < (2 : ℝ) ^ J := pow_pos (by norm_num) J
  have hlt : Real.log z * ((1 : ℝ) / (2 : ℝ) ^ J) < Real.log 2 := by
    rw [mul_one_div, div_lt_iff₀ h2J]
    rw [div_lt_iff₀ hlog2] at hJ
    linarith [hJ]
  have hzJ : Zscale z J = Real.exp (Real.log z * ((1 : ℝ) / (2 : ℝ) ^ J)) := by
    unfold Zscale
    rw [Real.rpow_def_of_pos hz0]
  rw [hzJ]
  have h2eq : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  conv_rhs => rw [← h2eq]
  exact Real.exp_lt_exp.mpr hlt

/-- Geometric block `B_j` of sieve primes. -/
noncomputable def Block (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (j : ℕ) : Finset ℕ :=
  S.primes.filter (fun p => Zscale z (j + 1) < (p : ℝ) ∧ (p : ℝ) ≤ Zscale z j)

theorem Block_subset (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (j : ℕ) : Block α S z j ⊆ S.primes :=
  Finset.filter_subset _ _

theorem Block_disjoint (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) {j₁ j₂ : ℕ} (hne : j₁ ≠ j₂) :
    Disjoint (Block α S z j₁) (Block α S z j₂) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  simp only [Block, Finset.mem_filter] at hp1 hp2
  obtain ⟨_, hlow1, hhigh1⟩ := hp1
  obtain ⟨_, hlow2, hhigh2⟩ := hp2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : j₁ + 1 ≤ j₂ := hlt
    have hZle : Zscale z j₂ ≤ Zscale z (j₁ + 1) :=
      Zscale_antitone hz hle
    linarith
  · have hle : j₂ + 1 ≤ j₁ := hgt
    have hZle : Zscale z j₁ ≤ Zscale z (j₂ + 1) :=
      Zscale_antitone hz hle
    linarith

/-- Every prime `p ≤ z` lies in some block `j < Jmax` (with `Z_Jmax < 2`). -/
theorem Block_cover (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax : ℕ) (hJ : Zscale z Jmax < 2)
    (p : ℕ) (hpmem : p ∈ S.primes) (hple : (p : ℝ) ≤ z) :
    ∃ j, j < Jmax ∧ p ∈ Block α S z j := by
  have hprime : p.Prime := S.prime p hpmem
  have h2p : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hprime.two_le
  have hZJlt : Zscale z Jmax < (p : ℝ) := lt_of_lt_of_le hJ h2p
  have hZ0 : Zscale z 0 = z := Zscale_zero
  have hex : ∃ j, Zscale z j < (p : ℝ) := ⟨Jmax, hZJlt⟩
  set j₀ : ℕ := Nat.find hex with hj₀def
  have hj₀spec : Zscale z j₀ < (p : ℝ) := Nat.find_spec hex
  have hj₀min : ∀ m, m < j₀ → ¬ Zscale z m < (p : ℝ) :=
    fun m hm => Nat.find_min hex hm
  have hj₀le : j₀ ≤ Jmax := Nat.find_min' hex hZJlt
  have hj₀ne0 : j₀ ≠ 0 := by
    intro h0
    rw [h0, hZ0] at hj₀spec
    linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hj₀ne0
  have hj_lt : j < j₀ := by omega
  have hj_notlt : ¬ Zscale z j < (p : ℝ) := hj₀min j hj_lt
  have hj_ge : (p : ℝ) ≤ Zscale z j := le_of_not_gt hj_notlt
  have hj_J : j < Jmax := by omega
  have hj_succ : Zscale z (j + 1) < (p : ℝ) := by
    have : j + 1 = j₀ := by omega
    rw [this]
    exact hj₀spec
  refine ⟨j, hj_J, ?_⟩
  simp only [Block, Finset.mem_filter]
  exact ⟨hpmem, hj_succ, hj_ge⟩

/-- Block mass bound from the blueprint density hypothesis
(`∑_{w<p≤w²} g ≤ C` with `w = Z_{j+1}`). -/
theorem Block_mass_le (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z η C : ℝ) (hdb : S.densityBounds z η C) (j : ℕ) :
    ∑ p ∈ Block α S z j, S.density p ≤ C := by
  obtain ⟨hz1, hη, hprime_mem, hmass⟩ := hdb
  have hz0 : (0 : ℝ) < z := lt_trans one_pos hz1
  have hw1 : (1 : ℝ) < Zscale z (j + 1) := Zscale_gt_one hz1 _
  have hZeq : Zscale z j = (Zscale z (j + 1)) ^ (2 : ℕ) :=
    Zscale_succ_sq hz0.le j
  have hBlock_eq : Block α S z j
      = S.primes.filter (fun p : ℕ =>
        Zscale z (j + 1) < (p : ℝ) ∧ (p : ℝ) ≤ (Zscale z (j + 1)) ^ (2 : ℕ)) := by
    unfold Block
    apply Finset.filter_congr
    intro p _
    rw [hZeq]
  rw [hBlock_eq]
  exact hmass (Zscale z (j + 1)) hw1

/-- Every block prime is `≤ Z_j` (for the level bound). -/
theorem Block_le_Z (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (j : ℕ) (p : ℕ) (hp : p ∈ Block α S z j) :
    (p : ℝ) ≤ Zscale z j := by
  simp only [Block, Finset.mem_filter] at hp
  exact hp.2.2

end PrelimLemmas
end Erdos821
