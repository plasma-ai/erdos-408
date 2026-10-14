import Erdos821.P5.ComparableNorms
import Erdos821.P5.EndpointVectorSup

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T

def rootMask (S : Finset ℤ) (f : ℤ → ℂ) (n : ℤ) : ℂ := if n ∈ S then f n else 0

theorem rootMask_norm_le (S : Finset ℤ) (f : ℤ → ℂ) (n : ℤ) :
    ‖rootMask S f n‖ ≤ ‖f n‖ := by
  unfold rootMask
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (f n)

theorem eventual_half_dyad_displacement (P : Geometry) (J : ℕ) (C γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ (G : Blueprint.Analytic.PrimeGroups) (m : ℕ)
      (A : Model P.graph G.graph J m) (X : ℝ),
      Admissible P x G → |(A.k : ℝ)| ≤ L x ^ C → x ^ γ ≤ X →
      ∀ v a u, |(A.k : ℝ)| * ((A.pattern v).D a u : ℝ) ≤ X / 2 := by
  filter_upwards [eventual_edge_displacement_le P J C (γ / 2) (by linarith),
    (tendsto_rpow_atTop (by linarith : 0 < γ / 2)).eventually_ge_atTop (2 : ℝ)]
    with x hedge hhalf
  intro G m A X hG hk hX v a u
  have hpow : x ^ (γ / 2) * x ^ (γ / 2) = x ^ γ := by
    rw [← Real.rpow_add (by linarith [hedge.1] : 0 < x)]
    congr 1
    ring
  have hsmall : 2 * x ^ (γ / 2) ≤ x ^ γ := by
    rw [← hpow]
    exact mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg (zero_le_one.trans hedge.1) _)
  have h := hedge.2.2 G hG P.ell m (A.pattern v) a u A.k hk
  linarith

/-- All P3 endpoint bounds for the exact Mellin source and its restricted
target. The norm exponent and pointwise exponent precede J and m. -/
theorem eventual_dyadic_endpoint_bounds (P : Geometry) (C : ℝ) :
    ∃ C₃ : ℝ, ∀ (J m : ℕ) (γ : ℝ), 0 < γ →
      ∀ᶠ x : ℝ in atTop, ∀ (G : Blueprint.Analytic.PrimeGroups)
        (A : Model P.graph G.graph J m) (X Z τ η a₁ a₂ v : ℝ)
        (E H : Endpoint) (S T : Finset ℤ),
        Admissible P x G → EndpointBound x C τ η E → EndpointBound x C τ η H →
        x ^ γ ≤ X → X ≤ x ^ (2 : ℕ) →
        (∀ n ∈ dyad X,
          ‖mellinPairingSource X Z (rootMask S (liftedEndpoint A x E (-a₁))) v n‖ ≤
            Real.exp ((2 + 6 * Real.log 2) * Real.sqrt (L x))) ∧
        A.normOn ((dyad X).product Finset.univ)
          (fun z => mellinPairingSource X Z (rootMask S (liftedEndpoint A x E (-a₁))) v z.1) ≤
            Real.sqrt X * L x ^ C₃ ∧
        A.normOn ((T ∩ comparableRoots X).product Finset.univ)
          (fun z => liftedEndpoint A x H a₂ z.1) ≤ Real.sqrt X * L x ^ C₃ := by
  obtain ⟨c, hc⟩ := eventual_physical_endpoint_norm_any_power P C
  refine ⟨c + 1, ?_⟩
  intro J m γ hγ
  filter_upwards [hc J m (γ / 2) 3 (by linarith) (by norm_num),
    eventual_liftedEndpoint_sup P C J m, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ),
    (tendsto_rpow_atTop (by linarith : 0 < γ / 2)).eventually_ge_atTop (2 : ℝ)]
    with x hnorm hsup hx hL hhalf
  intro G A X Z τ η a₁ a₂ v E H S T hG hE hH hXlo hXhi
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := by change 2 ≤ L x at hL; linarith
  have hXpos : 0 < X := (Real.rpow_pos_of_pos hxpos γ).trans_le hXlo
  have hX1 : 1 ≤ X := (Real.one_le_rpow (by linarith) hγ.le).trans hXlo
  have hpow : x ^ (γ / 2) * x ^ (γ / 2) = x ^ γ := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hXhalf : x ^ (γ / 2) ≤ X / 2 := by
    have hsmall : 2 * x ^ (γ / 2) ≤ x ^ γ := by
      rw [← hpow]
      exact mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hxpos.le _)
    linarith
  have hXcube : 2 * X ≤ x ^ (3 : ℝ) := by
    rw [Real.rpow_ofNat]
    nlinarith [sq_nonneg x]
  have hV (g : Fin G.size) : 0 < G.graph.V g := by
    rw [graph_mass]
    exact P.positive.2.2.1.trans_le (hG.2.2.1 g).1
  have hsource (n : ℤ) (hn : n ∈ dyad X) :
      ‖mellinPairingSource X Z (rootMask S (liftedEndpoint A x E (-a₁))) v n‖ ≤
        ‖liftedEndpoint A x E (-a₁) n‖ :=
    (mellinPairingSource_norm_le X Z _ v hXpos n ((mem_graph_dyad X n).mp hn).1).trans
      (rootMask_norm_le S _ n)
  have hsrc := hnorm G A X τ η E
    (fun z => mellinPairingSource X Z (rootMask S (liftedEndpoint A x E (-a₁))) v z.1)
    hG hE (by linarith) (by linarith)
    (fun n hn a ha => (hsource n hn).trans (liftedEndpoint_norm_le A x E (-a₁) a ha))
  have htarget (Y : ℝ) (hYlo : x ^ (γ / 2) ≤ Y) (hYhi : Y ≤ x ^ (3 : ℝ)) :
      A.normOn ((dyad Y).product Finset.univ) (fun z => liftedEndpoint A x H a₂ z.1) ≤
        Real.sqrt Y * L x ^ c :=
    hnorm G A Y τ η H _ hG hH hYlo hYhi
      (fun n hn a ha => liftedEndpoint_norm_le A x H a₂ a ha)
  have htgt := comparable_normOn_le A hV X (L x ^ c) hXpos
    (Real.rpow_nonneg hLpos.le _) T (fun z => liftedEndpoint A x H a₂ z.1)
    (htarget (X / 2) hXhalf (by linarith))
    (htarget X (by linarith) (by linarith))
    (htarget (2 * X) (by linarith) hXcube)
  have hloggrow : L x ^ c ≤ L x ^ (c + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by change 2 ≤ L x at hL; linarith) (by linarith)
  have htwo : 2 * L x ^ c ≤ L x ^ (c + 1) := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
    calc
      _ ≤ L x * L x ^ c := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hLpos.le _)
      _ = _ := mul_comm _ _
  refine ⟨?_, hsrc.trans (mul_le_mul_of_nonneg_left hloggrow (Real.sqrt_nonneg _)), ?_⟩
  · intro n hn
    exact (hsource n hn).trans (hsup G A X τ η E (-a₁) hG hE hX1 hXhi n hn)
  · calc
      _ ≤ 2 * Real.sqrt X * L x ^ c := htgt
      _ = Real.sqrt X * (2 * L x ^ c) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htwo (Real.sqrt_nonneg _)

end Erdos821.P5Core
