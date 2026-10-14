import Erdos821.P5.PhysicalNorms
import Erdos821.P5.ListScales

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem physical_group_count_ge (G : Blueprint.Graph.PrimeGroups) {M : ℕ}
    {n : ℤ} (a : G.Labels M) (ha : G.physical M n a) (g : G.Group) :
    M ≤ G.omegaGroup g n := by
  classical
  let s := (G.primes g).filter (fun p : ℕ => (p : ℤ) ∣ n)
  let f (i : Fin M) : {p : ℕ // p ∈ s} :=
    ⟨(a g i).val, Finset.mem_filter.mpr ⟨(a g i).property, (ha g).2 i⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hval : (a g i).val = (a g j).val :=
      congrArg (fun p : {p : ℕ // p ∈ s} => p.val) hij
    exact (ha g).1 (Subtype.ext hval)
  simpa only [Fintype.card_fin, Fintype.card_coe, s,
    Blueprint.Graph.PrimeGroups.omegaGroup] using Fintype.card_le_of_injective f hf

theorem physical_omega_ge (G : Blueprint.Graph.PrimeGroups) {M : ℕ}
    {n : ℤ} (a : G.Labels M) (ha : G.physical M n a) : M * G.count ≤ G.omega n := by
  have h := Finset.sum_le_sum (fun g (hg : g ∈ Finset.univ) => physical_group_count_ge G a ha g)
  simpa only [Blueprint.Graph.PrimeGroups.omega, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_comm] using h

theorem physical_damping_le_one {F : Blueprint.Graph.FixedData}
    {G : Blueprint.Graph.PrimeGroups} {J m : ℕ} (A : Blueprint.Graph.Model F G J m)
    {n : ℤ} (a : A.Labels) (ha : G.physical (J + F.ell) n a) : A.damping n ≤ 1 := by
  have h := physical_omega_ge G a ha
  have hR : ((J + F.ell : ℕ) : ℝ) * G.count ≤ (G.omega n : ℝ) := by exact_mod_cast h
  apply Real.rpow_le_one F.q_pos.le F.q_lt.le
  push_cast at hR ⊢
  linarith

def liftedEndpoint {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (A : Blueprint.Graph.Model P.graph G.graph J m) (x : ℝ) (E : Endpoint) (t : ℝ)
    (n : ℤ) : ℂ := mellin n t * endpoint G x E n.toNat * (A.damping n : ℂ)

theorem liftedEndpoint_norm_le {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (A : Blueprint.Graph.Model P.graph G.graph J m) (x : ℝ) (E : Endpoint) (t : ℝ)
    {n : ℤ} (a : A.Labels) (ha : G.graph.physical (J + P.ell) n a) :
    ‖liftedEndpoint A x E t n‖ ≤ ‖endpoint G x E n.toNat‖ := by
  have hd : 0 ≤ A.damping n := Real.rpow_nonneg P.damping.1.le _
  simp only [liftedEndpoint, norm_mul, norm_mellin, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hd]
  exact mul_le_of_le_one_right (norm_nonneg _) (physical_damping_le_one A a ha)

/-- The physical endpoint norm exponent is chosen before J and the probe bound. -/
theorem eventual_physical_endpoint_norm (P : Geometry) (C : ℝ) :
    ∃ C₃ : ℝ, ∀ (J m : ℕ) (γ : ℝ), 0 < γ →
      ∀ᶠ x : ℝ in atTop, ∀ (G : PrimeGroups)
        (A : Blueprint.Graph.Model P.graph G.graph J m) (X τ η : ℝ) (E : Endpoint)
        (f : A.State → ℂ),
        Admissible P x G → EndpointBound x C τ η E →
        x ^ γ ≤ X → X ≤ x ^ (2 : ℕ) →
        (∀ n ∈ Blueprint.Graph.dyad X, ∀ a : A.Labels,
          G.graph.physical (J + P.ell) n a → ‖f (n, a)‖ ≤ ‖endpoint G x E n.toNat‖) →
        A.normOn ((Blueprint.Graph.dyad X).product Finset.univ) f ≤
          Real.sqrt X * L x ^ C₃ := by
  obtain ⟨c, K, hc, hK, hm⟩ := physical_endpoint_square_sum
  let R := Real.log 4 + 2
  have hR : 0 < R := by dsimp [R]; positivity
  let K₀ := K * R ^ c
  have hK₀ : 0 < K₀ := mul_pos hK (Real.rpow_pos_of_pos hR c)
  refine ⟨2 * C + c / 2 + 1, ?_⟩
  intro J m γ hγ
  filter_upwards [eventual_listProduct_le P (J + P.ell) γ hγ,
    eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop K₀] with x hx hxx hKx
  intro G A X τ η E f hG hE hXlo hXhi hf
  have hL : 0 < L x := by linarith [hx.1]
  have hxpos : 0 < x := by linarith
  have hX : 1 ≤ X := (Real.one_le_rpow hxx hγ.le).trans hXlo
  have hXpos : 0 < X := by linarith
  have hsum := hm G x C τ η X E hx.1 hE hX
    (fun g => lt_of_lt_of_le P.positive.2.2.1 (hG.2.2.1 g).1)
    P.graph J m A (fun a => (hx.2 G hG a).trans hXlo)
  have hdom : (∑ z ∈ (Blueprint.Graph.dyad X).product Finset.univ,
      A.stateMass z * ‖f z‖ ^ 2) ≤
      ∑ z ∈ (Blueprint.Graph.dyad X).product Finset.univ,
        A.stateMass z * ‖endpoint G x E z.1.toNat‖ ^ 2 := by
    apply Finset.sum_le_sum
    rintro ⟨n, a⟩ hz
    have hn := (Finset.mem_product.mp hz).1
    by_cases hp : G.graph.physical (J + P.ell) n a
    · apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hf n hn a hp) 2)
      simpa only [Blueprint.Graph.Model.stateMass, if_pos hp] using
        markMass_nonneg G.graph (J + P.ell)
          (fun g => by rw [graph_mass]; exact lt_of_lt_of_le P.positive.2.2.1 (hG.2.2.1 g).1)
    · simp only [Blueprint.Graph.Model.stateMass, if_neg hp, zero_mul, le_refl]
  have hlogX : Real.log X ≤ 2 * L x := by
    apply (Real.log_le_log hXpos hXhi).trans
    simp [L, Real.log_pow]
  have hlog : Real.log (4 * X) ≤ R * L x := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hXpos.ne']
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h := mul_le_mul_of_nonneg_left hx.1 hlog4
    dsimp [R]
    nlinarith
  have hlogpow : Real.log (4 * X) ^ c ≤ R ^ c * L x ^ c := by
    calc
      _ ≤ (R * L x) ^ c := Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog hc
      _ = _ := Real.mul_rpow hR.le hL.le
  have hKpow : K₀ ≤ L x ^ (2 : ℕ) := by
    have hKx' : K₀ ≤ L x := hKx
    nlinarith [hx.1, hKx']
  have hmain : K * X * L x ^ (4 * C) * Real.log (4 * X) ^ c ≤
      X * L x ^ (4 * C + c + 2) := by
    calc
      _ ≤ K * X * L x ^ (4 * C) * (R ^ c * L x ^ c) :=
        mul_le_mul_of_nonneg_left hlogpow (by positivity)
      _ = K₀ * X * L x ^ (4 * C + c) := by
        rw [Real.rpow_add hL]; dsimp [K₀]; ring
      _ ≤ L x ^ (2 : ℕ) * X * L x ^ (4 * C + c) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKpow hXpos.le) (by positivity)
      _ = _ := by rw [Real.rpow_add hL (4 * C + c) 2, Real.rpow_two]; ring
  change Real.sqrt _ ≤ _
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hexp : (2 * C + c / 2 + 1) * (2 : ℝ) = 4 * C + c + 2 := by ring
  rw [mul_pow, Real.sq_sqrt hXpos.le,
    ← Real.rpow_mul_natCast hL.le (2 * C + c / 2 + 1) 2]
  simp only [Nat.cast_ofNat]
  rw [hexp]
  exact hdom.trans (hsum.trans hmain)

theorem eventual_liftedEndpoint_norm (P : Geometry) (C : ℝ) :
    ∃ C₃ : ℝ, ∀ (J m : ℕ) (γ : ℝ), 0 < γ →
      ∀ᶠ x : ℝ in atTop, ∀ (G : PrimeGroups)
        (A : Blueprint.Graph.Model P.graph G.graph J m) (X τ η : ℝ) (E : Endpoint) (t : ℝ),
        Admissible P x G → EndpointBound x C τ η E →
        x ^ γ ≤ X → X ≤ x ^ (2 : ℕ) →
        A.normOn ((Blueprint.Graph.dyad X).product Finset.univ)
          (fun z => liftedEndpoint A x E t z.1) ≤ Real.sqrt X * L x ^ C₃ := by
  obtain ⟨C₃, hC₃⟩ := eventual_physical_endpoint_norm P C
  refine ⟨C₃, ?_⟩
  intro J m γ hγ
  filter_upwards [hC₃ J m γ hγ] with x hx
  intro G A X τ η E t hG hE hXlo hXhi
  exact hx G A X τ η E _ hG hE hXlo hXhi
    (fun n hn a ha => liftedEndpoint_norm_le A x E t a ha)

end Erdos821.P5Core
