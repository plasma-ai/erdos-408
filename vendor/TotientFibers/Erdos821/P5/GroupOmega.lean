import Erdos821.P5.SharedProducts

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem omegaGroup_mul_coprime (G : PrimeGroups) (g : Fin G.size) (D n : ℕ)
    (hcop : Nat.Coprime D n) : omegaGroup G g (D * n) = omegaGroup G g D + omegaGroup G g n := by
  classical
  have heq : (G.primes g).filter (fun p => p ∣ D * n) =
      ((G.primes g).filter (fun p => p ∣ D)) ∪ ((G.primes g).filter (fun p => p ∣ n)) := by
    ext p
    by_cases hp : p ∈ G.primes g
    · simp only [Finset.mem_filter, hp, true_and, Finset.mem_union]
      exact (G.prime g p hp).dvd_mul
    · simp [hp]
  have hd : Disjoint ((G.primes g).filter (fun p => p ∣ D))
      ((G.primes g).filter (fun p => p ∣ n)) := by
    apply Finset.disjoint_left.mpr
    intro p hpD hpn
    have hp := G.prime g p (Finset.mem_filter.mp hpD).1
    have hpd := Nat.dvd_gcd (Finset.mem_filter.mp hpD).2 (Finset.mem_filter.mp hpn).2
    rw [hcop.gcd_eq_one] at hpd
    exact hp.not_dvd_one hpd
  unfold omegaGroup
  rw [heq, Finset.card_union_of_disjoint hd]

theorem omega_mul_coprime (G : PrimeGroups) (D n : ℕ) (hcop : Nat.Coprime D n) :
    omega G (D * n) = omega G D + omega G n := by
  unfold omega
  simp_rw [omegaGroup_mul_coprime G _ D n hcop]
  rw [Finset.sum_add_distrib]

theorem graph_omegaGroup_nat (G : PrimeGroups) (g : Fin G.size) (n : ℕ) :
    G.graph.omegaGroup g (n : ℤ) = omegaGroup G g n := by
  simp only [Blueprint.Graph.PrimeGroups.omegaGroup, PrimeGroups.graph,
    Int.natCast_dvd_natCast, omegaGroup]

theorem graph_omega_nat (G : PrimeGroups) (n : ℕ) : G.graph.omega (n : ℤ) = omega G n := by
  unfold Blueprint.Graph.PrimeGroups.omega omega
  simp only [graph_omegaGroup_nat]

/-- The two square-root damping factors give the full integer power used in
the marked-weight definition; no natural subtraction is used. -/
theorem damping_sq_int (P : Geometry) (G : PrimeGroups) (J m : ℕ)
    (A : Blueprint.Graph.Model P.graph G.graph J m) (n : ℕ) :
    A.damping (n : ℤ) ^ 2 =
      P.q ^ ((omega G n : ℤ) - (((J + P.ell) * G.size : ℕ) : ℤ)) := by
  simp only [Blueprint.Graph.Model.damping, Geometry.graph, PrimeGroups.graph,
    graph_omega_nat, Nat.cast_add, Nat.cast_mul]
  let b : ℝ := ((omega G n : ℝ) - ((J : ℝ) + P.ell) * G.size) / 2
  change (P.q ^ b) ^ 2 = _
  have heq : b * (2 : ℝ) =
      (((omega G n : ℤ) - (((J + P.ell) * G.size : ℕ) : ℤ) : ℤ) : ℝ) := by
    dsimp [b]
    push_cast
    ring
  rw [← Real.rpow_mul_natCast P.damping.1.le b 2]
  simp only [Nat.cast_ofNat]
  rw [heq]
  simpa only [Nat.cast_add, Nat.cast_mul] using
    Real.rpow_intCast P.q ((omega G n : ℤ) - (((J + P.ell) * G.size : ℕ) : ℤ))

/-- Exact damping conversion once the shared-product counts and the excluded
overlap condition have been proved for a stripped configuration. -/
theorem damping_sq_strip_of_counts (P : Geometry) (G : PrimeGroups) (J m : ℕ)
    (A : Blueprint.Graph.Model P.graph G.graph J m)
    (ν : Blueprint.Graph.Pattern G.graph J P.ell m) (D n : ℕ)
    (hcop : Nat.Coprime D n) (hcounts : ∀ g, omegaGroup G g D = (sharedSlots ν g).card) :
    A.damping ((D * n : ℕ) : ℤ) ^ 2 = P.q ^ ((omega G n : ℤ) - ∑ g, (ν.t g : ℤ)) := by
  have hN : omega G D + ∑ g, ν.t g = (J + P.ell) * G.size := by
    unfold omega
    simp_rw [hcounts]
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ g : Fin G.size, (J + P.ell) := Finset.sum_congr rfl
        (fun g hg => (shared_slot_count ν g).symm)
      _ = _ := by simp; ring
  have hZ : (omega G D : ℤ) + ∑ g, (ν.t g : ℤ) = (((J + P.ell) * G.size : ℕ) : ℤ) := by
    exact_mod_cast hN
  rw [damping_sq_int, omega_mul_coprime G D n hcop]
  congr 1
  push_cast at hZ ⊢
  omega

end Erdos821.P5Core
