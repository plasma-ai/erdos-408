import Erdos821.P5.CollisionLog

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem admissible_group_prime_lower (P : Geometry) (G : PrimeGroups) (x : ℝ)
    (hL : 1 ≤ L x) (hG : Admissible P x G) (g : Fin G.size)
    (p : ℕ) (hp : p ∈ G.primes g) : Real.exp (L x ^ P.a) ≤ (p : ℝ) := by
  classical
  have h := hG.2.2.2.1 g p hp
  by_cases hs : g ∈ G.small
  · simp only [if_pos hs] at h
    exact h.1
  · simp only [if_neg hs] at h
    have hac : P.a ≤ P.c := (P.ordered.2.1.trans P.ordered.2.2.1).le
    exact (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL hac)).trans
      h.1

theorem admissible_group_prime_inv (P : Geometry) (G : PrimeGroups) (x : ℝ)
    (hL : 1 ≤ L x) (hG : Admissible P x G) (g : Fin G.size)
    (p : ℕ) (hp : p ∈ G.primes g) : (p : ℝ)⁻¹ ≤ Real.exp (-(L x ^ P.a)) := by
  rw [Real.exp_neg]
  exact inv_anti₀ (Real.exp_pos _) (admissible_group_prime_lower P G x hL hG g p hp)

theorem admissible_group_atom_le (P : Geometry) (G : PrimeGroups) (x : ℝ)
    (hL : 1 ≤ L x) (hG : Admissible P x G) (g : Fin G.size)
    (p : G.graph.Prime g) :
    G.graph.mu g p ≤ P.vmin⁻¹ * Real.exp (-(L x ^ P.a)) := by
  change (G.graph.V g * (p.val : ℝ))⁻¹ ≤ _
  rw [graph_mass, mul_inv]
  have hV : (mass G g)⁻¹ ≤ P.vmin⁻¹ :=
    inv_anti₀ P.positive.2.2.1 (hG.2.2.1 g).1
  have hp := admissible_group_prime_inv P G x hL hG g p.val p.property
  exact mul_le_mul hV hp (inv_nonneg.mpr (Nat.cast_nonneg _))
    (inv_nonneg.mpr P.positive.2.2.1.le)

/-- Every single free-label endpoint collision has arbitrary log saving,
uniformly in the actual signed shift and all bounded endpoint coefficients. -/
theorem endpoint_free_prime_error_negligible (P : Geometry) (A C τ η R : ℝ) (hR : 0 < R) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (E H : Endpoint) (g : Fin G.size) (p D : ℕ)
        (k : ℤ) (X Y : ℝ) (s : Finset ℕ),
        Admissible P x G → EndpointBound x C τ η E → EndpointBound x C τ η H →
        p ∈ G.primes g → 0 < X → (p : ℝ) ≤ Y → p ∣ D →
        Y ≤ x ^ (2 : ℕ) → Y ≤ R * X →
        (∀ n ∈ s, X ≤ (n : ℝ)) →
        (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ Y ∧ p ∣ n ∧
          0 < (n : ℤ) + k * (D : ℤ) ∧
          ((n : ℤ) + k * (D : ℤ)).toNat ≤ Y) →
        (∑ n ∈ s, ‖endpoint G x E n‖ *
          ‖endpoint G x H ((n : ℤ) + k * (D : ℤ)).toNat‖ / (n : ℝ)) ≤ L x ^ (-A) := by
  obtain ⟨c, K, hc, hK, hm⟩ := endpoint_shift_sum_free_multiples_log
  filter_upwards [hm,
    eventual_constant_log_power_mul_exp_neg P.a A (4 * C + c) (K * R) P.ordered.1]
    with x hx hdecay
  intro G E H g p D k X Y s hG hE hH hp hX hpY hpD hYx hYRX hlo hs
  have hpprime := G.prime g p hp
  have hp1 : 1 ≤ p := by have := hpprime.two_le; omega
  have hprimes : p.primeFactors ⊆ Finset.univ.biUnion G.primes := by
    rw [hpprime.primeFactors, Finset.singleton_subset_iff]
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hp⟩
  have hLpos : 0 < L x := by linarith [hdecay.1]
  have hinv := admissible_group_prime_inv P G x hdecay.1 hG g p hp
  calc
    _ ≤ K * R * L x ^ (4 * C + c) / p :=
      hx G C τ η X Y R E H p D k hE hH hX hR hp1 hpY hpD hprimes hYx hYRX s hlo hs
    _ = (K * R * L x ^ (4 * C + c)) * (p : ℝ)⁻¹ := div_eq_mul_inv _ _
    _ ≤ (K * R * L x ^ (4 * C + c)) * Real.exp (-(L x ^ P.a)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ _ := hdecay.2

end Erdos821.P5Core
