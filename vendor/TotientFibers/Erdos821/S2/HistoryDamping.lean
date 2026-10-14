import Erdos821.S2.MemoryIndices

/-! The inserted memory damping parameter cancels over every valid history. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def pendingZeroCount {M : ℕ} (s : P.MemoryState M) : ℕ :=
  ∑ g : P.BigGroup, (zeroMemoryIndices (s.2.2 g)).card

theorem rawEdgeWeight_rho_factor (A : Model F P J m) (n : ℕ) (rho : ℝ)
    (ν : Pattern P J F.ell m) (u : P.Aux J) (s t : P.MemoryState (J + F.ell))
    (c : TransferChoice s) :
    rawEdgeWeight A n rho ν u s t c =
      rho ^ (pendingZeroCount s + pendingZeroCount t) * rawEdgeWeight A n 1 ν u s t c := by
  simp only [rawEdgeWeight, pendingZeroCount, one_pow, mul_one]
  ring

theorem edgeChoiceCoefficient_rho_factor (A : Model F P J m) (n : ℕ)
    (rho theta : ℝ) (i : Fin n) (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) :
    edgeChoiceCoefficient A n rho theta i s t c =
      (rho ^ (pendingZeroCount s + pendingZeroCount t) : ℝ) *
        edgeChoiceCoefficient A n 1 theta i s t c := by
  dsimp only [edgeChoiceCoefficient]
  have he := rawEdgeWeight_rho_factor A n rho (A.pattern c.2.2.1) c.2.2.2.1
    (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2
  rw [he]
  simp only [pendingZeroCount, permuteActive, Complex.ofReal_mul]
  ring

/-- The two empty boundary coordinates supply the missing endpoint factors. -/
theorem interleaved_product {R : Type*} [CommMonoid R] (n : ℕ)
    (u v g : Fin (n + 1) → R) (e : Fin n → R) (hu : u 0 = 1) (hv : v (Fin.last n) = 1) :
    (∏ i, g i) * (∏ i : Fin n, v i.castSucc * e i * u i.succ) =
      (∏ i, u i * g i * v i) * (∏ i, e i) := by
  have hU : (∏ i, u i) = ∏ i : Fin n, u i.succ := by
    rw [Fin.prod_univ_succ, hu, one_mul]
  have hV : (∏ i, v i) = ∏ i : Fin n, v i.castSucc := by
    rw [Fin.prod_univ_castSucc, hv, mul_one]
  simp only [Finset.prod_mul_distrib]
  rw [hU, hV]
  ac_rfl

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

theorem weight_rho_independent (rho theta : ℝ) (hρ : rho ≠ 0) (hH : H.Valid) :
    H.Weight rho theta = H.Weight 1 theta := by
  let u (i : Fin (n + 1)) : ℂ := (rho ^ pendingZeroCount (H.before i) : ℝ)
  let v (i : Fin (n + 1)) : ℂ := (rho ^ pendingZeroCount (H.after i) : ℝ)
  let g (i : Fin (n + 1)) : ℂ := (ghostChoiceWeight F n rho i (H.ghost i) : ℝ)
  let e (i : Fin n) : ℂ := (edgeSymmetryFactor P (J + F.ell) : ℂ) *
    edgeChoiceCoefficient A n 1 theta i (H.after i.castSucc) (H.before i.succ) (H.edge i)
  have hU : u 0 = 1 := by
    simp [u, pendingZeroCount, zeroMemoryIndices_card, hH.1]
  have hV : v (Fin.last n) = 1 := by
    simp [v, pendingZeroCount, zeroMemoryIndices_card, hH.2.1]
  have hG (i : Fin (n + 1)) : u i * g i * v i = (ghostChoiceWeight F n 1 i (H.ghost i) : ℝ) := by
    have he := ghostChoiceWeight_rho_cancel F n rho hρ i (H.ghost i) (hH.2.2.1 i).2.2
    dsimp only [u, v, g, pendingZeroCount]
    exact_mod_cast he
  have hE (i : Fin n) :
      (edgeSymmetryFactor P (J + F.ell) : ℂ) *
        edgeChoiceCoefficient A n rho theta i (H.after i.castSucc) (H.before i.succ) (H.edge i) =
      v i.castSucc * e i * u i.succ := by
    rw [edgeChoiceCoefficient_rho_factor]
    dsimp only [u, v, e]
    simp only [pow_add, Complex.ofReal_mul]
    ring
  unfold Weight
  simp_rw [hE]
  rw [mul_assoc, interleaved_product n u v g e hU hV]
  simp_rw [hG]
  dsimp only [e]
  rw [mul_assoc]

end MemoryHistory

theorem distinctMemoryExpression_rho_independent (A : Model F P J m) (n : ℕ)
    (rho theta : ℝ) (hρ : rho ≠ 0) :
    distinctMemoryExpression A n rho theta = distinctMemoryExpression A n 1 theta := by
  apply tsum_congr
  intro H
  by_cases hh : H.Valid ∧ H.DistinctBirths
  · simp only [distinctMemoryExpression, ite_eq_left hh]
    exact H.weight_rho_independent rho theta hρ hh.1
  · simp only [ite_eq_right hh]


end Erdos821.S2Core
