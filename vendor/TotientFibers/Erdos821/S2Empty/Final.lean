import Erdos821.S2Empty.BoundaryBound
import Erdos821.S2.AnalyticParametersTasks

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Empty

open Erdos821.Blueprint.Graph

theorem EmptyBoundaryMassTask_proof : Erdos821.S2Core.EmptyBoundaryMassTask := by
  intro F J
  let M : ℕ := J + F.ell
  have hEvent := eventually_big_deficit_budget F M
  rcases Filter.eventually_atTop.1 hEvent with ⟨x₀, hx₀⟩
  refine ⟨x₀, ?_⟩
  intro x hx P hP m A
  let e : ℝ := ((N x : ℝ) + 1) / Real.exp ((L x) ^ F.c)
  rcases hx₀ x hx with ⟨hL, hT, hTle, hN, hdecay, hbudgetRaw⟩
  have hePos : 0 < e := by
    dsimp [e]
    exact div_pos (by positivity) (Real.exp_pos _)
  have he0 : 0 ≤ e := hePos.le
  have hLsq : 5 * L x ≤ 5 * (L x) ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL)
      (show 0 ≤ 5 * L x by positivity)]
  have hehalf : e ≤ 1 / 2 := by
    dsimp [e]
    calc
      _ ≤ 5 * L x / Real.exp ((L x) ^ F.c) :=
        div_le_div_of_nonneg_right hN (Real.exp_pos _).le
      _ ≤ 5 * (L x) ^ (2 : ℕ) / Real.exp ((L x) ^ F.c) :=
        div_le_div_of_nonneg_right hLsq (Real.exp_pos _).le
      _ = 5 * (L x) ^ (2 : ℕ) * Real.exp (-((L x) ^ F.c)) := by
        rw [div_eq_mul_inv, Real.exp_neg]
      _ ≤ 1 / 2 := le_of_lt hdecay
  have hV : ∀ g, 0 < P.V g := by
    intro g
    exact lt_of_lt_of_le F.vMin_pos (hP.2.2.2.2.1 g).1
  have hfloor : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      1 - e ≤ baselinePrime F (N x) p.val := by
    intro g p
    have h := baseline_prime_floor_of_admissible F P x hP g p
    simpa [e] using h
  have hcardBig : Fintype.card P.BigGroup = P.bigGroups.card := by
    unfold PrimeGroups.BigGroup PrimeGroups.bigGroups
    exact Fintype.card_of_subtype
      (Finset.univ.filter (fun g : P.Group => P.big g = true))
      (by intro g; simp)
  have hBigCard : (Fintype.card P.BigGroup : ℝ) ≤ F.C₀ * T x := by
    rw [hcardBig]
    exact hP.2.2.2.1
  have hbudget : (J + F.ell : ℝ) * (Fintype.card P.BigGroup : ℝ) * e ≤ 1 / 2 := by
    calc
      _ ≤ (J + F.ell : ℝ) * (F.C₀ * T x) * e := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hBigCard (by positivity)
        · exact he0
      _ = (J + F.ell : ℝ) * F.C₀ * T x *
          ((N x : ℝ) + 1) / Real.exp ((L x) ^ F.c) := by
        dsimp [e]
        ring
      _ ≤ 1 / 2 := by
        simpa [M, Nat.cast_add] using hbudgetRaw
  exact initial_boundary_mass_le_two_of_budget F P J m (N x) A e
    he0 hehalf hbudget hV hfloor


end Erdos821.S2Empty
