import Erdos821.P5.FreeDraws
import Erdos821.P5.ListScales

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

def FreeCollisionEvent {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (u : FreeDraw ν) (n : ℕ) : Prop :=
  ∃ i : FreeIndex ν, (u i).val ∣ n

def freeCollisionError {G : PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G.graph J ell m) (u : FreeDraw ν)
    (x : ℝ) (E H : Endpoint) (k : ℤ) (s : Finset ℕ) : ℝ :=
  ∑ n ∈ s, if FreeCollisionEvent ν u n then
    ‖endpoint G x E n‖ *
      ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat‖ / (n : ℝ) else 0

theorem free_prime_dvd_freeDrawProduct {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (u : FreeDraw ν) (i : FreeIndex ν) :
    (u i).val ∣ freeDrawProduct ν u := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem freeCollisionError_union_le {G : PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G.graph J ell m) (u : FreeDraw ν)
    (x : ℝ) (E H : Endpoint) (k : ℤ) (s : Finset ℕ) :
    freeCollisionError ν u x E H k s ≤
      ∑ i : FreeIndex ν, ∑ n ∈ s.filter (fun n => (u i).val ∣ n),
        ‖endpoint G x E n‖ *
          ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat‖ / (n : ℝ) := by
  let f := fun n : ℕ => ‖endpoint G x E n‖ *
    ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat‖ / (n : ℝ)
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; positivity
  have hp (n : ℕ) : (if FreeCollisionEvent ν u n then f n else 0) ≤
      ∑ i : FreeIndex ν, if (u i).val ∣ n then f n else 0 := by
    by_cases h : FreeCollisionEvent ν u n
    · rw [if_pos h]
      obtain ⟨i, hi⟩ := h
      apply (show f n ≤ if (u i).val ∣ n then f n else 0 by rw [if_pos hi]).trans
      exact Finset.single_le_sum
        (f := fun j : FreeIndex ν => if (u j).val ∣ n then f n else 0)
        (fun j hj => by split_ifs <;> first | exact hf n | rfl)
        (Finset.mem_univ i)
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun i hi => by split_ifs <;> first | exact hf n | rfl)
  unfold freeCollisionError
  calc
    _ ≤ ∑ n ∈ s, ∑ i : FreeIndex ν, if (u i).val ∣ n then f n else 0 :=
      Finset.sum_le_sum (fun n hn => hp n)
    _ = ∑ i : FreeIndex ν, ∑ n ∈ s, if (u i).val ∣ n then f n else 0 := Finset.sum_comm
    _ = _ := by simp only [Finset.sum_filter]; rfl

/-- The sum of all free-slot endpoint collisions remains negligible after
any fixed pattern, cutoff and mark log costs. Free labels may repeat. -/
theorem free_slot_collision_error_negligible (P : Geometry) (J ell m : ℕ)
    (A C τ η R B K : ℝ) (hR : 0 < R) (hK : 0 ≤ K) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (ν : Blueprint.Graph.Pattern G.graph J ell m) (u : FreeDraw ν)
        (E H : Endpoint) (k : ℤ) (X Y : ℝ) (s : Finset ℕ),
        Admissible P x G → EndpointBound x C τ η E → EndpointBound x C τ η H →
        0 < X → Y ≤ x ^ (2 : ℕ) → Y ≤ R * X → (∀ n ∈ s, X ≤ (n : ℝ)) →
        (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ Y ∧
          0 < (n : ℤ) + k * (freeDrawProduct ν u : ℤ) ∧
          ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat ≤ Y) →
        K * L x ^ B * freeCollisionError ν u x E H k s ≤ L x ^ (-A) := by
  let Q : ℝ := 2 * m * P.C₀
  have hC₀ : 0 ≤ P.C₀ := P.positive.2.1.le
  have hQ : 0 ≤ Q := by dsimp [Q]; exact mul_nonneg (by positivity) P.positive.2.1.le
  filter_upwards [endpoint_free_prime_error_negligible P (A + B + 2) C τ η R hR,
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (K * Q))] with x hx hL
  change max 1 (K * Q) ≤ L x at hL
  have hL1 : 1 ≤ L x := (le_max_left _ _).trans hL
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL1
  intro G ν u E H k X Y s hG hE hH hX hYx hYRX hlo hs
  have hslot (i : FreeIndex ν) :
      (∑ n ∈ s.filter (fun n => (u i).val ∣ n), ‖endpoint G x E n‖ *
        ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat‖ / (n : ℝ)) ≤
          L x ^ (-(A + B + 2)) := by
    let S := s.filter (fun n => (u i).val ∣ n)
    by_cases hS : S.Nonempty
    · obtain ⟨n, hn⟩ := hS
      have hns : n ∈ s := (Finset.mem_filter.mp hn).1
      have hnpos : 0 < n := by have := (hs n hns).1; omega
      have hpn : ((u i).val : ℝ) ≤ n := by
        exact_mod_cast Nat.le_of_dvd hnpos (Finset.mem_filter.mp hn).2
      have hpY : ((u i).val : ℝ) ≤ Y := hpn.trans (hs n hns).2.1
      apply hx G E H i.1 (u i).val (freeDrawProduct ν u) k X Y S hG hE hH
        (u i).property hX hpY (free_prime_dvd_freeDrawProduct ν u i) hYx hYRX
      · intro n hn
        exact hlo n (Finset.mem_filter.mp hn).1
      · intro n hn
        have hns := (Finset.mem_filter.mp hn).1
        exact ⟨(hs n hns).1, (hs n hns).2.1, (Finset.mem_filter.mp hn).2,
          (hs n hns).2.2.1, (hs n hns).2.2.2⟩
    · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      change (∑ n ∈ S, _) ≤ _
      rw [hSempty, Finset.sum_empty]
      exact Real.rpow_nonneg hLpos.le _
  have hcard : (Fintype.card (FreeIndex ν) : ℝ) ≤ Q * L x := by
    have hc : (Fintype.card (FreeIndex ν) : ℝ) ≤ (m : ℝ) * G.size := by
      exact_mod_cast freeIndex_card_le ν
    have hTL : T x ≤ L x := by
      change Real.log (L x) ≤ L x
      linarith [Real.log_le_sub_one_of_pos hLpos]
    calc
      _ ≤ (m : ℝ) * G.size := hc
      _ ≤ (m : ℝ) * (2 * P.C₀ * T x) :=
        mul_le_mul_of_nonneg_left (admissible_count_le P G x hG) (Nat.cast_nonneg _)
      _ ≤ (m : ℝ) * (2 * P.C₀ * L x) := by gcongr <;> positivity
      _ = _ := by dsimp [Q]; ring
  have hsum : freeCollisionError ν u x E H k s ≤ Q * L x * L x ^ (-(A + B + 2)) := by
    calc
      _ ≤ ∑ i : FreeIndex ν, ∑ n ∈ s.filter (fun n => (u i).val ∣ n),
          ‖endpoint G x E n‖ *
            ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat‖ / (n : ℝ) :=
        freeCollisionError_union_le ν u x E H k s
      _ ≤ ∑ i : FreeIndex ν, L x ^ (-(A + B + 2)) := Finset.sum_le_sum (fun i hi => hslot i)
      _ = (Fintype.card (FreeIndex ν) : ℝ) * L x ^ (-(A + B + 2)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hLpos.le _)
  calc
    _ ≤ K * L x ^ B * (Q * L x * L x ^ (-(A + B + 2))) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hK (Real.rpow_nonneg hLpos.le _))
    _ = (K * Q) * L x ^ (-A - 1) := by
      have heq : L x ^ B * L x * L x ^ (-(A + B + 2)) = L x ^ (-A - 1) := by
        have hB : L x ^ B * L x = L x ^ (B + 1) := by
          rw [Real.rpow_add hLpos, Real.rpow_one]
        rw [hB, ← Real.rpow_add hLpos]
        congr 1
        ring
      calc
        _ = (K * Q) * (L x ^ B * L x * L x ^ (-(A + B + 2))) := by ring
        _ = _ := by rw [heq]
    _ ≤ L x * L x ^ (-A - 1) :=
      mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hL) (Real.rpow_nonneg hLpos.le _)
    _ = L x ^ (-A) := by
      have heq : L x * L x ^ (-A - 1) = L x ^ (1 + (-A - 1)) := by
        rw [Real.rpow_add hLpos, Real.rpow_one]
      rw [heq]
      congr 1
      ring

theorem freeDrawLaw_nonneg {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (u : FreeDraw ν)
    (hV : ∀ g, 0 ≤ G.V g) : 0 ≤ freeDrawLaw ν u := by
  apply productLaw_nonneg
  intro i p
  exact inv_nonneg.mpr (mul_nonneg (hV i.1) (Nat.cast_nonneg p.val))

/-- Integrating the free labels keeps the same saving, even when the root
dyad and its finite support depend on those labels. -/
theorem free_slot_average_negligible (P : Geometry) (J ell m : ℕ)
    (A C τ η R B K : ℝ) (hR : 0 < R) (hK : 0 ≤ K) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (ν : Blueprint.Graph.Pattern G.graph J ell m)
        (E H : Endpoint) (k : ℤ) (X Y : FreeDraw ν → ℝ) (s : FreeDraw ν → Finset ℕ),
        Admissible P x G → EndpointBound x C τ η E → EndpointBound x C τ η H →
        (∀ u, 0 < X u ∧ Y u ≤ x ^ (2 : ℕ) ∧ Y u ≤ R * X u ∧
          (∀ n ∈ s u, X u ≤ (n : ℝ)) ∧
          (∀ n ∈ s u, 1 ≤ n ∧ (n : ℝ) ≤ Y u ∧
            0 < (n : ℤ) + k * (freeDrawProduct ν u : ℤ) ∧
            ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat ≤ Y u)) →
        (∑ u : FreeDraw ν, freeDrawLaw ν u *
          (K * L x ^ B * freeCollisionError ν u x E H k (s u))) ≤ L x ^ (-A) := by
  filter_upwards [free_slot_collision_error_negligible P J ell m A C τ η R B K hR hK]
    with x hx
  intro G ν E H k X Y s hG hE hH hs
  have hV (g : Fin G.size) : 0 < G.graph.V g := by
    rw [graph_mass]
    exact P.positive.2.2.1.trans_le (hG.2.2.1 g).1
  calc
    _ ≤ ∑ u : FreeDraw ν, freeDrawLaw ν u * L x ^ (-A) := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left
        (hx G ν u E H k (X u) (Y u) (s u) hG hE hH (hs u).1 (hs u).2.1
          (hs u).2.2.1 (hs u).2.2.2.1 (hs u).2.2.2.2)
        (freeDrawLaw_nonneg ν u (fun g => (hV g).le))
    _ = _ := by rw [← Finset.sum_mul, freeDrawLaw_sum ν (fun g => (hV g).ne'), one_mul]

end Erdos821.P5Core
