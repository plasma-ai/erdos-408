import Erdos821.P3Clean.QuantitativeScales
import Erdos821.P3Clean.UniformComparison

/-! Big-prime exponential separation makes the signed perturbation negligible. -/

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

def comparisonPolynomial (F : FixedData) (J : ℕ) : ℝ :=
  20 * (J + F.ell) * F.C₀ + 6 * F.C₀ * J * (J + F.ell) / F.vMin

theorem comparisonPolynomial_nonneg (F : FixedData) (J : ℕ) : 0 ≤ comparisonPolynomial F J := by
  have hC := F.C₀_pos
  have hv := F.vMin_pos
  unfold comparisonPolynomial
  positivity

theorem eventually_tiltedBanned_norm (F : FixedData) (J m : ℕ) (C₁ Eid : ℝ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
      (0 < L x ∧ (∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F (N x) p.val)) ∧
      ∀ A : Model F P J m, A.patternMass ≤ (L x) ^ C₁ →
        (∀ theta : ℝ, NormBound P.idealMass (A.idealKernel theta) ((L x) ^ (-Eid))) →
        ∀ theta : ℝ, ∀ forward : Bool,
          NormBound (tiltedIdealMass F (N x)) (tiltedBannedKernel A (N x) theta forward)
            (2 * (L x) ^ (-Eid)) := by
  have hC₀ := F.C₀_pos
  have hv := F.vMin_pos
  have hPolynomial := comparisonPolynomial_nonneg F J
  have hc : 0 < F.c := lt_trans F.a_pos (lt_trans F.ab F.bc)
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ L x := Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hprime := eventually_polynomial_exp F.c hc 10 1 0
  have hsmall := eventually_polynomial_exp F.c hc (10 * (J + F.ell) * F.C₀) 2 0
  have herr := eventually_polynomial_exp F.c hc (comparisonPolynomial F J) (2 + C₁) Eid
  have hall : ∀ᶠ x : ℝ in atTop,
      1 ≤ L x ∧ 10 * L x / Real.exp ((L x) ^ F.c) ≤ 1 ∧
      (10 * (J + F.ell) * F.C₀) * (L x) ^ (2 : ℕ) / Real.exp ((L x) ^ F.c) ≤ 1 ∧
      comparisonPolynomial F J * (L x) ^ (2 + C₁) / Real.exp ((L x) ^ F.c) ≤ (L x) ^ (-Eid) := by
    filter_upwards [hL, hprime, hsmall, herr] with x hL hp hs he
    exact ⟨hL, by simpa only [Real.rpow_one, neg_zero, Real.rpow_zero] using hp,
      by simpa only [Real.rpow_two, neg_zero, Real.rpow_zero] using hs, he⟩
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hall
  refine ⟨x₀, ?_⟩
  intro x hx P hP
  obtain ⟨hL1, hprime, hsmall, herr⟩ := hx₀ x hx
  have hLpos : 0 < L x := zero_lt_one.trans_le hL1
  let pstar := Real.exp ((L x) ^ F.c)
  let t := pstar⁻¹
  have hpstar : 0 < pstar := Real.exp_pos _
  have ht : 0 < t := inv_pos.mpr hpstar
  have hG := bigGroup_card_le F x P hP hL1
  have hN := N_add_one_le x hL1
  have hpbound : 10 * L x ≤ pstar := by
    exact (div_le_one hpstar).mp hprime
  have hV (g : P.Group) : 0 < P.V g := F.vMin_pos.trans_le (hP.2.2.2.2.1 g).1
  have hbase (g : P.BigGroup) (p : P.Prime g.val) :
      0 < baselinePrime F (N x) p.val ∧ 1 ≤ (baselinePrime F (N x) p.val)⁻¹ ∧
        (baselinePrime F (N x) p.val)⁻¹ ≤ 1 + 10 * L x * t := by
    have hpl := bigPrime_lower F x P hP g p
    have hpp : 0 < (p.val : ℝ) := hpstar.trans_le hpl
    have hn : 2 * (N x + 1) ≤ p.val := by
      have hnR : 2 * ((N x : ℝ) + 1) ≤ (p.val : ℝ) := by linarith
      exact_mod_cast hnR
    obtain ⟨hb, h1, h2⟩ := baselinePrime_bounds F (N x) p.val (P.prime g.val p.val p.property).pos hn
    have hinv : (p.val : ℝ)⁻¹ ≤ t := (inv_le_inv₀ hpp hpstar).mpr hpl
    have hfrac : 2 * ((N x + 1 : ℕ) : ℝ) / p.val ≤ 10 * L x * t := by
      have hnum : 2 * ((N x + 1 : ℕ) : ℝ) ≤ 10 * L x := by push_cast; linarith
      exact (by simpa only [div_eq_mul_inv] using
        mul_le_mul hnum hinv (inv_nonneg.mpr hpp.le) (by positivity : 0 ≤ 10 * L x))
    exact ⟨hb, h1, h2.trans (by linarith)⟩
  have hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F (N x) p.val :=
    fun g p => (hbase g p).1
  refine ⟨⟨hLpos, hb⟩, ?_⟩
  intro A hpat hideal theta forward
  let eps := 10 * L x * t
  let atom := F.vMin⁻¹ * t
  let q := (J + F.ell) * Fintype.card P.BigGroup
  let D := (1 + eps) ^ q
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hatom0 : 0 ≤ atom := by dsimp [atom]; positivity
  have hatom (g : P.BigGroup) (p : P.Prime g.val) : P.mu g.val p ≤ atom := by
    have hden : F.vMin * pstar ≤ P.V g.val * (p.val : ℝ) :=
      mul_le_mul (hP.2.2.2.2.1 g.val).1 (bigPrime_lower F x P hP g p)
        hpstar.le (hV g.val).le
    have hi := (inv_le_inv₀
      (mul_pos (hV g.val) (hpstar.trans_le (bigPrime_lower F x P hP g p)))
      (mul_pos F.vMin_pos hpstar)).mpr hden
    simpa only [PrimeGroups.mu, atom, t, mul_inv_rev, mul_comm] using hi
  have hqeps : (q : ℝ) * eps ≤ (10 * (J + F.ell) * F.C₀) * (L x) ^ (2 : ℕ) * t := by
    have h := mul_le_mul_of_nonneg_left hG
      (show 0 ≤ 10 * ((J + F.ell : ℕ) : ℝ) * L x * t by positivity)
    dsimp [q, eps]
    push_cast at h ⊢
    nlinarith only [h]
  have hqt : (q : ℝ) * eps ≤ 1 := hqeps.trans (by simpa only [div_eq_mul_inv, t] using hsmall)
  obtain ⟨hD, hDe, hD3⟩ := density_power_error eps heps q hqt
  have hsqrt (v : Fin A.patternCount) (a b : P.BigLabels (J + F.ell)) :
      1 ≤ Real.sqrt (freshDensity F (N x) (A.pattern v) a) * Real.sqrt (freshDensity F (N x) (A.pattern v) b) ∧
        Real.sqrt (freshDensity F (N x) (A.pattern v) a) * Real.sqrt (freshDensity F (N x) (A.pattern v) b) ≤ D :=
    freshSqrtFactor_bounds F P (N x) (A.pattern v) eps heps (fun g p => (hbase g p).2) a b
  let banCost := (Fintype.card P.BigGroup : ℝ) * J * (J + F.ell) * (2 * atom)
  have hban0 : 0 ≤ banCost := by dsimp [banCost]; positivity
  have hLsq : L x ≤ (L x) ^ (2 : ℕ) := by nlinarith
  have hban : 3 * banCost ≤
      (6 * F.C₀ * J * (J + F.ell) / F.vMin) * (L x) ^ (2 : ℕ) * t := by
    have hGs : (Fintype.card P.BigGroup : ℝ) ≤ F.C₀ * (L x) ^ (2 : ℕ) :=
      hG.trans (mul_le_mul_of_nonneg_left hLsq F.C₀_pos.le)
    have h := mul_le_mul_of_nonneg_left hGs
      (show 0 ≤ 6 * (J : ℝ) * (J + F.ell : ℕ) * F.vMin⁻¹ * t by positivity)
    dsimp [banCost, atom]
    push_cast at h ⊢
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]
  have hdelta : (D - 1) + D * banCost ≤
      comparisonPolynomial F J * (L x) ^ (2 : ℕ) * t := by
    have hfirst : D - 1 ≤ (20 * (J + F.ell) * F.C₀) * (L x) ^ (2 : ℕ) * t :=
      hDe.trans (by nlinarith only [hqeps])
    have hsecond := (mul_le_mul_of_nonneg_right hD3 hban0).trans hban
    dsimp [comparisonPolynomial]
    nlinarith only [hfirst, hsecond]
  have hdelta0 : 0 ≤ (D - 1) + D * banCost := by positivity
  have hp0 : 0 ≤ A.patternMass := by rw [← sum_patternAmplitude]; exact Finset.sum_nonneg (fun v _ => patternAmplitude_nonneg A v)
  have herror : ((D - 1) + D * banCost) * A.patternMass ≤ (L x) ^ (-Eid) := by
    calc
      _ ≤ (comparisonPolynomial F J * (L x) ^ (2 : ℕ) * t) * (L x) ^ C₁ :=
        mul_le_mul hdelta hpat hp0 (by positivity)
      _ = comparisonPolynomial F J * (L x) ^ (2 + C₁) / pstar := by
        rw [Real.rpow_add hLpos, Real.rpow_two]
        dsimp [t]
        ring
      _ ≤ _ := herr
  have hnorm := normBound_tiltedBannedKernel A (N x) ((L x) ^ (-Eid)) D atom hD hatom0
    (fun g => (hV g.val).ne') hb hatom hsqrt hideal theta forward
  exact normBound_mono hnorm (by change (L x) ^ (-Eid) + ((D - 1) + D * banCost) * A.patternMass ≤ _; linarith)


end Erdos821.P3Clean
