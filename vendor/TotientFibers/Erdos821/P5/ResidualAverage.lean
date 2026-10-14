import Erdos821.P5.LinearFreeBan
import Erdos821.P5.ResidualRowSaving

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

def weightedResidualRowError {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (v : Fin B.count)
    (x : ℝ) (E H : Endpoint) (k : ℤ) (ζ : ℝ) (z₀ unused : SharedDraw (B.pattern v))
    (s : FreeDraw (B.pattern v) → Finset ℕ) : ℝ :=
  ∑ u : FreeDraw (B.pattern v), freeDrawLaw (B.pattern v) u *
    ∑ n ∈ s u, ‖endpoint G x E n‖ *
      ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat‖ /
      (n : ℝ) *
      ‖residualSharedAverage B v k ζ u unused n
          ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat -
        strippedMarkedRow (B.pattern v) n
          ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat
          (residualUnsharedCoefficient B v z₀ u)‖

/-- Shared overlaps, missing shared mass, and all free bans have arbitrary
log saving after the endpoint and free harmonic averages. The error stays
linear in the actual coefficient cost of the pattern. Range hypotheses are
retained for the later cutoff and finite-root support argument. -/
theorem weighted_residual_row_error_negligible (P : Geometry) (J m : ℕ)
    (A C τ η R : ℝ) (hR : 0 < R) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (Q : ℕ) (h ξ : ℝ)
        (B : Blueprint.Graph.Family P.graph G.graph J m) (v : Fin B.count)
        (E H : Endpoint) (k : ℤ) (ζ : ℝ) (z₀ unused : SharedDraw (B.pattern v))
        (X Y : FreeDraw (B.pattern v) → ℝ) (s : FreeDraw (B.pattern v) → Finset ℕ),
        Admissible P x G → B.Residual Q h ξ →
        EndpointBound x C τ η E → EndpointBound x C τ η H →
        (∀ u, (freeDrawProduct (B.pattern v) u : ℝ) ≤ x ^ (2 : ℕ)) →
        (∀ u, 0 < X u ∧ 1 ≤ Y u ∧ Y u ≤ x ^ (2 : ℕ) ∧ Y u ≤ R * X u ∧
          (∀ n ∈ s u, X u ≤ (n : ℝ)) ∧
          (∀ n ∈ s u, 1 ≤ n ∧ (n : ℝ) ≤ Y u ∧
            0 < (n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ) ∧
            ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat ≤ Y u)) →
        weightedResidualRowError B v x E H k ζ z₀ unused s ≤
          patternCost (B.pattern v) * L x ^ (-A) := by
  obtain ⟨d, K, hd, hK, hm⟩ := endpoint_shift_sum_free_multiples_log
  let F : ℝ := 4 * C + d
  let precision : ℝ := A + F + 2
  filter_upwards [hm, eventual_residual_shared_error_le P J m 2 precision (by norm_num),
    residual_free_ban_error_linear P J m (A + 1) C τ η R hR,
    Real.tendsto_log_atTop.eventually_ge_atTop (max 2 (K * R))]
    with x hx hrow hfree hL
  change max 2 (K * R) ≤ L x at hL
  have hL2 : 2 ≤ L x := (le_max_left _ _).trans hL
  have hLpos : 0 < L x := by linarith
  intro G Q h ξ B v E H k ζ z₀ unused X Y s hG hB hE hH hD hs
  let ν := B.pattern v
  let cost := patternCost ν
  let W := fun (u : FreeDraw ν) (n : ℕ) => ‖endpoint G x E n‖ *
    ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat‖ / (n : ℝ)
  have hcost : 0 ≤ cost := patternCost_nonneg ν
  have hV (g : Fin G.size) : 0 < G.graph.V g := by
    rw [graph_mass]
    exact P.positive.2.2.1.trans_le (hG.2.2.1 g).1
  have hsfree : ∀ u, 0 < X u ∧ Y u ≤ x ^ (2 : ℕ) ∧ Y u ≤ R * X u ∧
      (∀ n ∈ s u, X u ≤ (n : ℝ)) ∧
      (∀ n ∈ s u, 1 ≤ n ∧ (n : ℝ) ≤ Y u ∧
        0 < (n : ℤ) + k * (freeDrawProduct ν u : ℤ) ∧
        ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat ≤ Y u) :=
    fun u => ⟨(hs u).1, (hs u).2.2⟩
  have hsum (u : FreeDraw ν) : (∑ n ∈ s u, W u n) ≤ K * R * L x ^ F := by
    have hprimes : (1 : ℕ).primeFactors ⊆ Finset.univ.biUnion G.primes := by simp
    simpa only [W, Nat.cast_one, div_one] using
      hx G C τ η (X u) (Y u) R E H 1 (freeDrawProduct ν u) k hE hH
        (hs u).1 hR (by norm_num) (by simpa only [Nat.cast_one] using (hs u).2.1)
        (one_dvd _) hprimes (hs u).2.2.1 (hs u).2.2.2.1 (s u)
        (hs u).2.2.2.2.1 (fun n hn => ⟨((hs u).2.2.2.2.2 n hn).1,
          ((hs u).2.2.2.2.2 n hn).2.1, one_dvd n,
          ((hs u).2.2.2.2.2 n hn).2.2⟩)
  have hpoint (u : FreeDraw ν) (n : ℕ) (hn : n ∈ s u) :
      ‖residualSharedAverage B v k ζ u unused n
          ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat -
        strippedMarkedRow ν n ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat
          (residualUnsharedCoefficient B v z₀ u)‖ ≤
      cost * L x ^ (-precision) +
        ‖unsharedBanRow P ν u n ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat
          (residualUnsharedCoefficient B v z₀ u)‖ := by
    obtain ⟨hn1, hnY, hn'pos, hn'Y⟩ := (hs u).2.2.2.2.2 n hn
    have hnpos : 0 < n := by omega
    have hn'nat : 0 < ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat := by
      change 0 < ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat
      omega
    apply hrow G Q h ξ B v k ζ z₀ unused u n _ hG hB hnpos hn'nat
    · simpa only [Real.rpow_two] using hnY.trans (hs u).2.2.1
    · simpa only [Real.rpow_two] using hn'Y.trans (hs u).2.2.1
    · simpa only [Real.rpow_two] using hD u
  have hshared (u : FreeDraw ν) :
      (∑ n ∈ s u, W u n * (cost * L x ^ (-precision))) ≤ cost * L x ^ (-A - 1) := by
    calc
      _ = (∑ n ∈ s u, W u n) * (cost * L x ^ (-precision)) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (K * R * L x ^ F) * (cost * L x ^ (-precision)) :=
        mul_le_mul_of_nonneg_right (hsum u) (by positivity)
      _ = cost * (K * R) * L x ^ (-A - 2) := by
        rw [show (K * R * L x ^ F) * (cost * L x ^ (-precision)) =
          cost * (K * R) * (L x ^ F * L x ^ (-precision)) by ring,
          ← Real.rpow_add hLpos]
        congr 2
        dsimp [precision]
        ring
      _ ≤ cost * L x * L x ^ (-A - 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hL) hcost)
          (Real.rpow_nonneg hLpos.le _)
      _ = cost * L x ^ (-A - 1) := by
        have hp : L x * L x ^ (-A - 2) = L x ^ (1 + (-A - 2)) := by
          rw [Real.rpow_add hLpos, Real.rpow_one]
        rw [mul_assoc, hp]
        congr 2
        ring
  have hsharedAvg : (∑ u : FreeDraw ν, freeDrawLaw ν u *
      ∑ n ∈ s u, W u n * (cost * L x ^ (-precision))) ≤ cost * L x ^ (-A - 1) := by
    calc
      _ ≤ ∑ u : FreeDraw ν, freeDrawLaw ν u * (cost * L x ^ (-A - 1)) :=
        Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hshared u)
          (freeDrawLaw_nonneg ν u (fun g => (hV g).le)))
      _ = _ := by rw [← Finset.sum_mul, freeDrawLaw_sum ν (fun g => (hV g).ne'), one_mul]
  have hban := hfree G B v z₀ E H k X Y s hG hE hH hsfree
  have hban' : weightedFreeBanError P ν x E H k s
      (fun u _ => residualUnsharedCoefficient B v z₀ u) ≤ cost * L x ^ (-A - 1) := by
    simpa only [show -(A + 1) = -A - 1 by ring] using hban
  change (∑ u : FreeDraw ν, freeDrawLaw ν u *
    ∑ n ∈ s u, W u n * ‖_‖) ≤ cost * L x ^ (-A)
  calc
    _ ≤ ∑ u : FreeDraw ν, freeDrawLaw ν u *
        ∑ n ∈ s u, W u n * (cost * L x ^ (-precision) +
          ‖unsharedBanRow P ν u n ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat
            (residualUnsharedCoefficient B v z₀ u)‖) := by
      apply Finset.sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_left _ (freeDrawLaw_nonneg ν u (fun g => (hV g).le))
      exact Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hpoint u n hn)
        (by dsimp [W]; positivity))
    _ = (∑ u : FreeDraw ν, freeDrawLaw ν u *
        ∑ n ∈ s u, W u n * (cost * L x ^ (-precision))) +
        weightedFreeBanError P ν x E H k s (fun u _ => residualUnsharedCoefficient B v z₀ u) := by
      simp only [mul_add, Finset.sum_add_distrib]
      rfl
    _ ≤ cost * L x ^ (-A - 1) + cost * L x ^ (-A - 1) := add_le_add hsharedAvg hban'
    _ = cost * 2 * L x ^ (-A - 1) := by ring
    _ ≤ cost * L x * L x ^ (-A - 1) := by gcongr
    _ = cost * L x ^ (-A) := by
      have hp : L x * L x ^ (-A - 1) = L x ^ (1 + (-A - 1)) := by
        rw [Real.rpow_add hLpos, Real.rpow_one]
      rw [mul_assoc, hp]
      congr 2
      ring

end Erdos821.P5Core
