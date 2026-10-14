import Erdos821.P5.FullMellinLift

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem endpoint_eq_zero_of_groupFreePart_lt_lo (G : PrimeGroups) (x : ℝ)
    (E : Endpoint) (n : ℕ) (h : (groupFreePart G n : ℝ) < E.lo) :
    endpoint G x E n = 0 := by
  unfold endpoint
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro r hr
  have hpR : (p : ℝ) ≤ groupFreePart G n := by exact_mod_cast (Finset.mem_Icc.mp hp).2
  have hlo : ¬ E.lo ≤ (p : ℝ) := not_le.mpr (hpR.trans_lt h)
  simp only [hlo, false_and, and_false, ite_false]

/-- A positive endpoint root must be at least the lower prime-factor scale. -/
theorem endpoint_eq_zero_of_lt_lo (G : PrimeGroups) (x : ℝ) (E : Endpoint)
    (n : ℕ) (hn : 0 < n) (hlo : (n : ℝ) < E.lo) : endpoint G x E n = 0 := by
  apply endpoint_eq_zero_of_groupFreePart_lt_lo
  have hle : groupFreePart G n ≤ n := Nat.le_of_dvd hn (groupFreePart_dvd G n)
  exact (by exact_mod_cast hle : (groupFreePart G n : ℝ) ≤ n).trans_lt hlo

theorem liftedEndpoint_eq_zero_of_lt_lo {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (A : Blueprint.Graph.Model P.graph G.graph J m) (x : ℝ) (E : Endpoint) (t : ℝ)
    (n : ℤ) (hn : 0 < n) (hlo : (n : ℝ) < E.lo) : liftedEndpoint A x E t n = 0 := by
  have hnN : 0 < n.toNat := by omega
  have hcast : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn.le
  have hloN : (n.toNat : ℝ) < E.lo := by
    rwa [hcast]
  simp only [liftedEndpoint, endpoint_eq_zero_of_lt_lo G x E n.toNat hnN hloN,
    mul_zero, zero_mul]

theorem liftedEndpoint_eq_zero_below_scale {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (A : Blueprint.Graph.Model P.graph G.graph J m) (x C τ η : ℝ) (E : Endpoint)
    (hE : EndpointBound x C τ η E) (t : ℝ) (n : ℤ)
    (hn : 0 < n) (hlo : (n : ℝ) < x ^ τ) : liftedEndpoint A x E t n = 0 := by
  exact liftedEndpoint_eq_zero_of_lt_lo A x E t n hn
    (hlo.trans_le hE.2.2.2.2.2.2.2.2.1)

end Erdos821.P5Core
