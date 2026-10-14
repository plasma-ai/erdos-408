import Erdos821.P5.EndpointSup
import Erdos821.P5.PhysicalNormTheorem

noncomputable section
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- Off physical states damping may exceed one, but its loss is only a fixed
logarithmic power. This is needed for P3's pointwise bound on every root. -/
theorem damping_le_log_power (P : Geometry) (G : PrimeGroups) (x : ℝ) (J m : ℕ)
    (A : Blueprint.Graph.Model P.graph G.graph J m) (hL : 1 ≤ L x)
    (hG : Admissible P x G) (n : ℤ) :
    A.damping n ≤ L x ^ ((-Real.log P.q) * ((J + P.ell : ℕ) : ℝ) * P.C₀) := by
  have hLpos : 0 < L x := by linarith
  have hlogq : Real.log P.q < 0 := Real.log_neg P.damping.1 P.damping.2
  have hω : 0 ≤ (G.graph.omega n : ℝ) := Nat.cast_nonneg _
  have hM : 0 ≤ ((J + P.ell : ℕ) : ℝ) := Nat.cast_nonneg _
  have hdrop : Real.log P.q * (((G.graph.omega n : ℝ) -
      ((J + P.ell : ℕ) : ℝ) * G.size) / 2) ≤
      (-Real.log P.q) * ((J + P.ell : ℕ) : ℝ) * G.size / 2 := by
    have hneg := mul_nonpos_of_nonpos_of_nonneg hlogq.le hω
    nlinarith
  have hβ : 0 ≤ (-Real.log P.q) * ((J + P.ell : ℕ) : ℝ) / 2 :=
    div_nonneg (mul_nonneg (neg_nonneg.mpr hlogq.le) hM) (by norm_num)
  have hscale := mul_le_mul_of_nonneg_left (admissible_count_le P G x hG) hβ
  unfold Blueprint.Graph.Model.damping
  rw [Real.rpow_def_of_pos P.damping.1, Real.rpow_def_of_pos hLpos]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (-Real.log P.q) * ((J + P.ell : ℕ) : ℝ) * G.size / 2 := by
      convert hdrop using 1 <;> push_cast <;> ring
    _ ≤ (-Real.log P.q) * ((J + P.ell : ℕ) : ℝ) * P.C₀ * T x := by
      convert hscale using 1 <;> ring
    _ = _ := by unfold T; ring

theorem eventual_damping_sup (P : Geometry) (J m : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (G : PrimeGroups)
      (A : Blueprint.Graph.Model P.graph G.graph J m), Admissible P x G →
        ∀ n : ℤ, A.damping n ≤ Real.exp (Real.sqrt (L x)) := by
  filter_upwards [eventual_log_rpow_le_exp_sqrt
    ((-Real.log P.q) * ((J + P.ell : ℕ) : ℝ) * P.C₀)] with x hx
  intro G A hG n
  exact (damping_le_log_power P G x J m A hx.1 hG n).trans hx.2

theorem graph_dyad_nat_le_cube {x X : ℝ} (hx : 2 ≤ x) (hX : 1 ≤ X)
    (hXx : X ≤ x ^ (2 : ℕ)) {n : ℤ} (hn : n ∈ Blueprint.Graph.dyad X) :
    0 < n.toNat ∧ (n.toNat : ℝ) ≤ x ^ (3 : ℕ) := by
  have hnpos := graph_dyad_positive hX hn
  have hcast : (n.toNat : ℝ) = n := by exact_mod_cast Int.toNat_of_nonneg hnpos.le
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnat : 0 < n.toNat := Nat.cast_pos.mp (by rwa [hcast])
  have hhi : (n : ℝ) < 2 * X := Int.lt_ceil.mp (Finset.mem_Ico.mp hn).2
  have hcube : 2 * x ^ (2 : ℕ) ≤ x ^ (3 : ℕ) := by
    calc
      _ ≤ x * x ^ (2 : ℕ) := mul_le_mul_of_nonneg_right hx (sq_nonneg _)
      _ = _ := by ring
  refine ⟨hnat, ?_⟩
  rw [hcast]
  exact (hhi.le.trans (mul_le_mul_of_nonneg_left hXx (by norm_num))).trans hcube

/-- The exact mark-independent lift vector satisfies P3's sup hypothesis on
the entire root dyad, including roots with no admissible mark list. -/
theorem eventual_liftedEndpoint_sup (P : Geometry) (C : ℝ) (J m : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (G : PrimeGroups)
      (A : Blueprint.Graph.Model P.graph G.graph J m) (X τ η : ℝ) (E : Endpoint) (t : ℝ),
      Admissible P x G → EndpointBound x C τ η E → 1 ≤ X → X ≤ x ^ (2 : ℕ) →
      ∀ n ∈ Blueprint.Graph.dyad X,
        ‖liftedEndpoint A x E t n‖ ≤ Real.exp ((2 + 6 * Real.log 2) * Real.sqrt (L x)) := by
  filter_upwards [eventual_endpoint_sup C 3, eventual_damping_sup P J m,
    eventually_ge_atTop (2 : ℝ)] with x he hd hxx
  intro G A X τ η E t hG hE hX hXx n hn
  obtain ⟨hnpos, hnX⟩ := graph_dyad_nat_le_cube hxx hX hXx hn
  have he' := he.2 G τ η E hE n.toNat hnpos (by simpa only [Real.rpow_ofNat] using hnX)
  have hd' := hd G A hG n
  have hd0 : 0 ≤ A.damping n := Real.rpow_nonneg P.damping.1.le _
  simp only [liftedEndpoint, norm_mul, norm_mellin, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hd0]
  calc
    _ ≤ Real.exp ((1 + 2 * 3 * Real.log 2) * Real.sqrt (L x)) * Real.exp (Real.sqrt (L x)) :=
      mul_le_mul he' hd' hd0 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos821.P5Core
