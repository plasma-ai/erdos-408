import Erdos821.S2High.Baseline

noncomputable section
open scoped BigOperators

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph

lemma reciprocalPrime_sum_eq_V (P : PrimeGroups) (g : P.BigGroup) :
    (∑ p : P.Prime g.val, (p.val : ℝ)⁻¹) = P.V g.val := by
  classical
  simp only [PrimeGroups.V, PrimeGroups.Prime]
  change (∑ p ∈ (P.primes g.val).attach, (p.1 : ℝ)⁻¹) =
    ∑ p ∈ P.primes g.val, (p : ℝ)⁻¹
  exact Finset.sum_attach (P.primes g.val) (fun p : ℕ => (p : ℝ)⁻¹)

lemma reciprocalTilt_sum_eq_one (P : PrimeGroups) (g : P.BigGroup)
    (hV : 0 < P.V g.val) :
    (∑ p : P.Prime g.val, (P.V g.val * (p.val : ℝ))⁻¹) = 1 := by
  calc
    (∑ p : P.Prime g.val, (P.V g.val * (p.val : ℝ))⁻¹) =
        ∑ p : P.Prime g.val, (P.V g.val)⁻¹ * (p.val : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [mul_inv_rev]
      ring
    _ = (P.V g.val)⁻¹ * ∑ p : P.Prime g.val, (p.val : ℝ)⁻¹ := by
      change (∑ p ∈ (Finset.univ : Finset (P.Prime g.val)),
          (P.V g.val)⁻¹ * (p.val : ℝ)⁻¹) =
        (P.V g.val)⁻¹ * ∑ p ∈ (Finset.univ : Finset (P.Prime g.val)), (p.val : ℝ)⁻¹
      rw [← Finset.mul_sum]
    _ = 1 := by rw [reciprocalPrime_sum_eq_V, inv_mul_cancel₀ hV.ne']

theorem tiltedMu_factor (F : FixedData) (P : PrimeGroups) (n : ℕ)
    (g : P.BigGroup) (p : P.Prime g.val) :
    tiltedMu F P n g.val p =
      (P.V g.val * (p.val : ℝ))⁻¹ * (baselinePrime F n p.val)⁻¹ := by
  unfold tiltedMu
  rw [mul_inv_rev]
  ring

theorem tiltedMu_atom_bound (F : FixedData) (P : PrimeGroups) (n : ℕ)
    (g : P.BigGroup) (p : P.Prime g.val) (Pstar : ℝ)
    (hV : F.vMin ≤ P.V g.val) (hp : Pstar ≤ (p.val : ℝ))
    (hPstarPos : 0 < Pstar) (hbase : 1 / 2 ≤ baselinePrime F n p.val) :
    tiltedMu F P n g.val p ≤ 2 / (F.vMin * Pstar) := by
  have hVpos : 0 < P.V g.val := lt_of_lt_of_le F.vMin_pos hV
  have hpPos : 0 < (p.val : ℝ) := by
    exact_mod_cast (P.prime g.val p.val p.property).pos
  have hbasePos : 0 < baselinePrime F n p.val := by linarith
  have hden : F.vMin * Pstar * (1 / 2) ≤
      P.V g.val * (p.val : ℝ) * baselinePrime F n p.val := by
    calc
      F.vMin * Pstar * (1 / 2) ≤ P.V g.val * (Pstar * (1 / 2)) := by
        calc
          F.vMin * Pstar * (1 / 2) = F.vMin * (Pstar * (1 / 2)) := by ring
          _ ≤ P.V g.val * (Pstar * (1 / 2)) :=
            mul_le_mul_of_nonneg_right hV (mul_nonneg hPstarPos.le (by norm_num))
      _ ≤ P.V g.val * ((p.val : ℝ) * baselinePrime F n p.val) := by
        apply mul_le_mul_of_nonneg_left _ hVpos.le
        exact mul_le_mul hp hbase (by norm_num) hpPos.le
      _ = P.V g.val * (p.val : ℝ) * baselinePrime F n p.val := by ring
  have hdenPos : 0 < F.vMin * Pstar * (1 / 2) :=
    mul_pos (mul_pos F.vMin_pos hPstarPos) (by norm_num)
  calc
    tiltedMu F P n g.val p =
        1 / (P.V g.val * (p.val : ℝ) * baselinePrime F n p.val) := by
          simp [tiltedMu, mul_assoc]
    _ ≤ 1 / (F.vMin * Pstar * (1 / 2)) :=
          one_div_le_one_div_of_le hdenPos hden
    _ = 2 / (F.vMin * Pstar) := by field_simp [ne_of_gt F.vMin_pos, ne_of_gt hPstarPos]

theorem tiltedMu_group_mass_bounds (F : FixedData) (P : PrimeGroups) (x : ℝ)
    (n : ℕ) (hP : P.Admissible F x)
    (hcut : (n + 1 : ℝ) ≤ Real.exp ((L x) ^ F.c) / 2)
    (g : P.BigGroup) :
    (∀ p : P.Prime g.val, 0 < tiltedMu F P n g.val p ∧
      tiltedMu F P n g.val p ≤ 2 / (F.vMin * Real.exp ((L x) ^ F.c))) ∧
    1 ≤ (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ∧
      (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ 2 := by
  have hAdm := hP
  rcases hP with ⟨_, _, _, _, hV, hPrime⟩
  have hVmin : F.vMin ≤ P.V g.val := (hV g.val).1
  have hVpos : 0 < P.V g.val := lt_of_lt_of_le F.vMin_pos hVmin
  have hBase (p : P.Prime g.val) := baselinePrime_bounds_of_cutoff F P x n hAdm hcut g p
  have hPstar (p : P.Prime g.val) :
      Real.exp ((L x) ^ F.c) ≤ (p.val : ℝ) := by
    have h := hPrime g.val p.val p.property
    simp only [g.property, ite_true] at h
    exact h.1
  have hpos (p : P.Prime g.val) : 0 < tiltedMu F P n g.val p := by
    rw [tiltedMu_factor F P n g p]
    have hpPos : 0 < (p.val : ℝ) := by
      exact_mod_cast (P.prime g.val p.val p.property).pos
    exact mul_pos (inv_pos.mpr (mul_pos hVpos hpPos))
      (inv_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < (1 / 2 : ℝ)) (hBase p).1))
  have hAtom (p : P.Prime g.val) := tiltedMu_atom_bound F P n g p
    (Real.exp ((L x) ^ F.c)) hVmin (hPstar p) (Real.exp_pos _) (hBase p).1
  have hfactor (p : P.Prime g.val) :
      tiltedMu F P n g.val p =
        (P.V g.val * (p.val : ℝ))⁻¹ * (baselinePrime F n p.val)⁻¹ :=
    tiltedMu_factor F P n g p
  have hInvLower (p : P.Prime g.val) :
      1 ≤ (baselinePrime F n p.val)⁻¹ := by
    have hbasePos : 0 < baselinePrime F n p.val :=
      lt_of_lt_of_le (by norm_num : 0 < (1 / 2 : ℝ)) (hBase p).1
    simpa using one_div_le_one_div_of_le hbasePos (hBase p).2
  have hInvUpper (p : P.Prime g.val) :
      (baselinePrime F n p.val)⁻¹ ≤ 2 := by
    simpa using (one_div_le_one_div_of_le
      (by norm_num : 0 < (1 / 2 : ℝ)) (hBase p).1)
  have hmuBaseNonneg (p : P.Prime g.val) :
      0 ≤ (P.V g.val * (p.val : ℝ))⁻¹ := by positivity
  constructor
  · intro p
    exact ⟨hpos p, hAtom p⟩
  constructor
  · calc
      1 = ∑ p : P.Prime g.val, (P.V g.val * (p.val : ℝ))⁻¹ :=
        (reciprocalTilt_sum_eq_one P g hVpos).symm
      _ ≤ ∑ p : P.Prime g.val, tiltedMu F P n g.val p :=
        Finset.sum_le_sum fun p _ => by
          rw [hfactor p]
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (hInvLower p) (hmuBaseNonneg p)
  · calc
      (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤
          ∑ p : P.Prime g.val, 2 * (P.V g.val * (p.val : ℝ))⁻¹ :=
        Finset.sum_le_sum fun p _ => by
          rw [hfactor p]
          calc
            (P.V g.val * (p.val : ℝ))⁻¹ * (baselinePrime F n p.val)⁻¹ ≤
                (P.V g.val * (p.val : ℝ))⁻¹ * 2 :=
              mul_le_mul_of_nonneg_left (hInvUpper p) (hmuBaseNonneg p)
            _ = 2 * (P.V g.val * (p.val : ℝ))⁻¹ := by ring
      _ = 2 := by
        calc
          (∑ p : P.Prime g.val, 2 * (P.V g.val * (p.val : ℝ))⁻¹) =
              2 * ∑ p : P.Prime g.val, (P.V g.val * (p.val : ℝ))⁻¹ := by
            rw [← Finset.mul_sum]
          _ = 2 := by rw [reciprocalTilt_sum_eq_one P g hVpos]; ring


end Erdos821.S2High
