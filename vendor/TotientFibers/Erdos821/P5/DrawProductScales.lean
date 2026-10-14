import Erdos821.P5.FreeDraws
import Erdos821.P5.CompressedPairing
import Erdos821.P5.GoodSharedDraws
import Erdos821.P5.ListScales

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- Shared and free auxiliary coordinates partition the full J-slot list.
The identity allows repeated labels in both parts. -/
theorem auxProduct_assemble {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (u : FreeDraw ν) (z : SharedDraw ν) :
    listProduct G (assembleAux ν u z) = freeDrawProduct ν u * sharedDrawProduct ν z := by
  unfold listProduct freeDrawProduct sharedDrawProduct
  rw [Fintype.prod_sigma, Fintype.prod_sigma, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  have hc : (∏ i ∈ ν.changed g, (assembleAux ν u z g i).val) =
      ∏ i : {i : Fin J // i ∈ ν.changed g}, (u ⟨g, i⟩).val := by
    rw [Finset.prod_subtype (ν.changed g) (fun i => Iff.rfl)
      (fun i => (assembleAux ν u z g i).val)]
    apply Finset.prod_congr rfl
    intro i hi
    rw [assembleAux_free]
  have hs : (∏ i ∈ sharedSlots ν g, (assembleAux ν u z g i).val) =
      ∏ i : {i : Fin J // i ∈ sharedSlots ν g}, (z ⟨g, i⟩).val := by
    rw [Finset.prod_subtype (sharedSlots ν g) (fun i => Iff.rfl)
      (fun i => (assembleAux ν u z g i).val)]
    apply Finset.prod_congr rfl
    intro i hi
    rw [assembleAux_unused]
  rw [← hc, ← hs, mul_comm]
  exact (Finset.prod_sdiff (Finset.subset_univ (ν.changed g))).symm

theorem freeDrawProduct_pos {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (u : FreeDraw ν) : 0 < freeDrawProduct ν u :=
  Finset.prod_pos (fun i hi => (G.prime i.1 _ (u i).property).pos)

/-- The total edge product is subpower, uniformly over shared and free
draws and over every pattern with fixed J. -/
theorem eventual_joint_draw_product_le (P : Geometry) (J ell m : ℕ)
    (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ L x ∧
      ∀ (G : PrimeGroups) (ν : Blueprint.Graph.Pattern G.graph J ell m)
        (u : FreeDraw ν) (z : SharedDraw ν), Admissible P x G →
        (freeDrawProduct ν u : ℝ) * sharedDrawProduct ν z ≤ x ^ γ := by
  filter_upwards [eventual_listProduct_le P J γ hγ] with x hx
  refine ⟨hx.1, ?_⟩
  intro G ν u z hG
  simpa only [auxProduct_assemble, Nat.cast_mul] using hx.2 G hG (assembleAux ν u z)

theorem eventual_constant_log_power_le_power (a A K : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ L x ∧ K * L x ^ A ≤ x ^ a := by
  filter_upwards [eventual_log_power_le_power a (A + 1) ha,
    Real.tendsto_log_atTop.eventually_ge_atTop K] with x hx hK
  change K ≤ L x at hK
  refine ⟨hx.1, hx.2.1, ?_⟩
  have hLpos : 0 < L x := by linarith [hx.2.1]
  calc
    _ ≤ L x * L x ^ A := mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hLpos.le _)
    _ = L x ^ (A + 1) := by
      rw [Real.rpow_add hLpos, Real.rpow_one]
      ring
    _ ≤ _ := hx.2.2

/-- The original and stripped endpoint ranges lie below x² on the fixed
cutoff support. The signed shift is smaller than half the lower endpoint.
Every bound is uniform over the actual shared and free draws. -/
theorem eventual_cutoff_draw_ranges (P : Geometry) (J ell m : ℕ)
    (C lo hi : ℝ) (hC : 0 < C) (hlo : 0 < lo) (hhi : lo < hi) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (ν : Blueprint.Graph.Pattern G.graph J ell m)
        (u : FreeDraw ν) (Z : ℝ) (k : ℤ),
        Admissible P x G → |(k : ℝ)| ≤ L x ^ C →
        x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
        0 < Z ∧ 1 ≤ lo * Z * freeDrawProduct ν u ∧ |(k : ℝ)| ≤ lo * Z / 2 ∧
        (freeDrawProduct ν u : ℝ) ≤ x ^ (2 : ℕ) ∧
        (hi + lo) * Z * freeDrawProduct ν u ≤ x ^ (2 : ℕ) ∧
        ∀ z : SharedDraw ν,
          (sharedDrawProduct ν z : ℝ) * ((hi + lo) * Z * freeDrawProduct ν u) ≤ x ^ (2 : ℕ) := by
  filter_upwards [eventual_joint_draw_product_le P J ell m (1 / 4) (by norm_num),
    eventual_constant_log_power_le_power (1 / 4) C (hi + lo) (by norm_num),
    eventual_constant_log_power_le_power (1 / 2) (2 * C) (2 / lo) (by norm_num)]
    with x hprod hup hlow
  have hx1 : 1 ≤ x := hup.1
  have hxpos : 0 < x := by linarith
  have hL1 : 1 ≤ L x := hup.2.1
  have hLpos : 0 < L x := by linarith
  intro G ν u Z k hG hk hZlo hZhi
  have hZpos : 0 < Z := (mul_pos hxpos (Real.rpow_pos_of_pos hLpos (-C))).trans_le hZlo
  have hDC : 1 ≤ (freeDrawProduct ν u : ℝ) := by exact_mod_cast freeDrawProduct_pos ν u
  have hV (g : Fin G.size) : G.graph.V g ≠ 0 := by
    rw [graph_mass]
    exact (P.positive.2.2.1.trans_le (hG.2.2.1 g).1).ne'
  let z₀ := unusedAuxDraw ν hV
  have hDR (z : SharedDraw ν) : 1 ≤ (sharedDrawProduct ν z : ℝ) := by
    exact_mod_cast sharedDrawProduct_pos ν z
  have hDCbound : (freeDrawProduct ν u : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
    (le_mul_of_one_le_right (Nat.cast_nonneg _) (hDR z₀)).trans (hprod.2 G ν u z₀ hG)
  have hhalf : x ^ (1 / 2 : ℝ) ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hsmall : (2 / lo) * L x ^ (2 * C) ≤ x := hlow.2.2.trans hhalf
  have hsmall' : 2 * L x ^ (2 * C) ≤ lo * x := by
    have ht := mul_le_mul_of_nonneg_left hsmall hlo.le
    have heq : lo * ((2 / lo) * L x ^ (2 * C)) = 2 * L x ^ (2 * C) := by
      field_simp
    rwa [heq] at ht
  have hscale : 2 * L x ^ C ≤ lo * Z := by
    have ht := mul_le_mul_of_nonneg_right hsmall' (Real.rpow_nonneg hLpos.le (-C))
    have heq : L x ^ (2 * C) * L x ^ (-C) = L x ^ C := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    rw [mul_assoc, heq] at ht
    exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_left hZlo hlo.le])
  have hlog1 : 1 ≤ L x ^ C := Real.one_le_rpow hL1 hC.le
  have hX1 : 1 ≤ lo * Z * freeDrawProduct ν u := by
    have hbase : 1 ≤ lo * Z := by linarith
    nlinarith
  have hshift : |(k : ℝ)| ≤ lo * Z / 2 := by linarith
  have hDCx : (freeDrawProduct ν u : ℝ) ≤ x ^ (2 : ℕ) := by
    apply hDCbound.trans
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 4 : ℝ) ≤ 2)
  have hY (z : SharedDraw ν) :
      (sharedDrawProduct ν z : ℝ) * ((hi + lo) * Z * freeDrawProduct ν u) ≤ x ^ (2 : ℕ) := by
    have hI : 0 < hi + lo := by linarith
    calc
      _ = (hi + lo) * Z * ((freeDrawProduct ν u : ℝ) * sharedDrawProduct ν z) := by ring
      _ ≤ (hi + lo) * (x * L x ^ C) * x ^ (1 / 4 : ℝ) := by
        gcongr
        exact hprod.2 G ν u z hG
      _ = x * ((hi + lo) * L x ^ C) * x ^ (1 / 4 : ℝ) := by ring
      _ ≤ x * x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
        gcongr
        exact hup.2.2
      _ = x ^ (3 / 2 : ℝ) := by
        calc
          _ = (x ^ (1 : ℝ) * x ^ (1 / 4 : ℝ)) * x ^ (1 / 4 : ℝ) := by
            rw [Real.rpow_one]
          _ = x ^ (1 + 1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) :=
            congrArg (fun y : ℝ => y * x ^ (1 / 4 : ℝ)) (Real.rpow_add hxpos 1 (1 / 4)).symm
          _ = x ^ ((1 + 1 / 4) + 1 / 4 : ℝ) := (Real.rpow_add hxpos (1 + 1 / 4) (1 / 4)).symm
          _ = _ := by congr 1; norm_num
      _ ≤ _ := by
        simpa only [Real.rpow_two] using
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (3 / 2 : ℝ) ≤ 2)
  refine ⟨hZpos, hX1, hshift, hDCx, ?_, hY⟩
  have hIpos : 0 < hi + lo := by linarith
  exact (le_mul_of_one_le_left (by positivity : 0 ≤ (hi + lo) * Z * freeDrawProduct ν u)
    (hDR z₀)).trans (hY z₀)

end Erdos821.P5Core
