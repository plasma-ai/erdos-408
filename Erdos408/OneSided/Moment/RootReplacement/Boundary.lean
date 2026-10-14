import Erdos408.OneSided.Moment.RootReplacement.Tube
import Erdos408.OneSided.Moment.RootReplacement.Grid
import Erdos408.OneSided.Moment.RootReplacement.BoundaryCount

/-!
# Boundary cubes

RR6 of `blueprint/one_sided_type_ii.md` §15. For a live configuration with `c(ω) ≠ 0`, the
archimedean indicator `A(ω, ·)` is constant on the roots of every cube except at most
`n² exp(L^{1/2})` of them (`badCubes`). A cube on which `A` is not constant meets

* a face of the box condition of some visit: `u τ(z_j) ∈ {U, 16U}` or
  `v τ(z_j) + z_{j,2}/u ∈ {V, 2V}`. On the box `τ(z_j) ∈ [1/16, 16]`, and the slope argument
  of `det:tube` gives `|z_{j,2}| ≤ 2560 N H`, so each face meets `O(n² (1 + |z_{j,2}|))` cubes;
* or a breakpoint of the good-state tests of some visit in `r`. The transported ratio
  `r ↦ τ(w)/τ(z)` is monotone with derivative `τ(z)^{-2} ≤ 256`, and the tests depend only on
  finitely many comparisons `‖m ρ‖ ≶ θ` with `|m| ≤ exp(C_K L^{0.21})`, each changing at most
  `256 |m| + 1` times.

PD (3.31)–(3.32) and the boundary cubes in the proof of Lemma 3.4; the counts are those of
the budget table of §5.4. The classification of the bad cubes of one visit and the counts are
in `BoundaryCount.lean`; here a bad cube is traced to one visit (`badCubes_subset`) and the
counts are summed over the `N + 1` visits, with the sizes of `det:tube` (`tube_of_live`,
`confCoeff_ne_zero_imp`).
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

open scoped Classical in
/-- The cubes on whose roots the indicator of `ω` is not constant, equal to its value at the
lower corner. -/
def badCubes (x : ℝ) (d : Data K) (Y d₀ : ℝ) (n : ℕ) (ω : Conf x d Y d₀) :
    Finset (ℕ × ℕ × ℕ) :=
  (cubeIndices n).filter fun i => ∃ P₀ ∈ cubeRoots (d₀ * Y * d.Hm) d.Hn n i,
    confInd x d Y d₀ ω P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) ≠
      confInd x d Y d₀ ω (d₀ * Y * d.Hm * (1 + i.1 / n)) (d.Hn * (1 + i.2.1 / n)) (i.2.2 / n)

/-- The integer roots of a cube lie in the real cube. -/
theorem inCube_of_mem_cubeRoots {U V : ℝ} {n : ℕ} {i : ℕ × ℕ × ℕ} {P₀ : ℕ × ℕ}
    (hP₀ : P₀ ∈ cubeRoots U V n i) :
    InCube U V n i P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) := by
  unfold cubeRoots boxRoots at hP₀
  obtain ⟨hmem, -, h₂, h₄, h₅, h₆⟩ := mem_filter.1 hP₀
  obtain ⟨h₁, h₃⟩ := mem_product.1 hmem
  exact ⟨Nat.ceil_le.1 (mem_Icc.1 h₁).1, h₂, Nat.ceil_le.1 (mem_Icc.1 h₃).1, h₄, h₅, h₆⟩

/-- The lower corner of a cube lies in the real cube. -/
theorem inCube_corner {U V : ℝ} (hU : 0 < U) (hV : 0 < V) {n : ℕ} (hn : 1 ≤ n)
    (i : ℕ × ℕ × ℕ) :
    InCube U V n i (U * (1 + i.1 / n)) (V * (1 + i.2.1 / n)) (i.2.2 / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h : ∀ a : ℝ, a / n < (a + 1) / n := fun a => div_lt_div_of_pos_right (by linarith) hn'
  refine ⟨by rw [mul_comm], ?_, by rw [mul_comm], ?_, le_rfl, h _⟩
  · rw [mul_comm]
    exact mul_lt_mul_of_pos_right (by linarith [h i.1]) hU
  · rw [mul_comm]
    exact mul_lt_mul_of_pos_right (by linarith [h i.2.1]) hV

open scoped Classical in
/-- A bad cube is made bad by some visit: the indicator of one visit differs between a root
of the cube and its corner, so `visitBad_of_ne` applies. -/
theorem badCubes_subset (x : ℝ) (d : Data K) {Y d₀ : ℝ} (hU : 0 < d₀ * Y * d.Hm)
    (hV : 0 < d.Hn) {n : ℕ} (hn : 1 ≤ n) (ω : Conf x d Y d₀) :
    badCubes x d Y d₀ n ω ⊆ univ.biUnion fun j => (cubeIndices n).filter
      (VisitBad x d Y (d₀ * Y * d.Hm) d.Hn (ω j).1.2 n (ω j).1.1.1) := by
  intro i hi
  unfold badCubes at hi
  obtain ⟨hi, P₀, hP₀, hne⟩ := mem_filter.1 hi
  -- step: some visit indicator differs
  obtain ⟨j, hj⟩ : ∃ j, visitInd x d Y d₀ P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) (ω j) ≠
      visitInd x d Y d₀ (d₀ * Y * d.Hm * (1 + i.1 / n)) (d.Hn * (1 + i.2.1 / n)) (i.2.2 / n)
        (ω j) := by
    by_contra h
    push Not at h
    exact hne (prod_congr rfl fun j _ => h j)
  have hiff := fun h => hj (by unfold visitInd; exact if_congr h rfl rfl)
  obtain ⟨hi₁, hi₂, hi₃⟩ : i.1 < 15 * n ∧ i.2.1 < n ∧ i.2.2 < n := by
    simp only [cubeIndices, mem_product, mem_range] at hi
    exact hi
  exact mem_biUnion.2 ⟨j, mem_univ _, mem_filter.2 ⟨hi, visitBad_of_ne hU hV hn hi₁ hi₂ hi₃ _
    (inCube_of_mem_cubeRoots hP₀) (inCube_corner hU hV hn i) hiff⟩⟩

/-- **RR6 (boundary cubes)**: eventually, a live configuration with `c(ω) ≠ 0` has at most
`n² exp(L^{1/2})` bad cubes, for every `n ≥ 1`. -/
theorem eventually_card_badCubes_le {C CX alo ahi g : ℝ} (hahi : ahi < 1 / 5) (A₀ : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ n : ℕ, 1 ≤ n → ∀ ω : Conf x d (2 ^ j) (2 ^ k), ConfLive ω →
        confCoeff A₀ x d (2 ^ j) (2 ^ k) ω ≠ 0 →
        ((badCubes x d (2 ^ j) (2 ^ k) n ω).card : ℝ) ≤
          (n : ℝ) ^ 2 * Real.exp (Real.log x ^ (1 / 2 : ℝ)) := by
  classical
  filter_upwards [eventually_visits_le K, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 1] with x hvis hL hx d hd j k n hn ω hω hc
  -- step: the scales
  have hY₁ : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hd₁ : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hγ : 0 ≤ d.γ := (Real.rpow_pos_of_pos (by linarith) _).le.trans hd.γ_ge
  have hHm : 1 ≤ d.Hm := (Real.one_le_rpow hx hγ).trans hd.Hm_ge
  have hHn : 1 ≤ d.Hn := (Real.one_le_rpow hx hγ).trans hd.Hn_ge
  have hU₁ : 1 ≤ 2 ^ k * 2 ^ j * d.Hm := by
    have := mul_le_mul hd₁ hY₁ zero_le_one (by positivity)
    nlinarith
  have hU : 0 < (2 : ℝ) ^ k * 2 ^ j * d.Hm := by linarith
  have hV : 0 < d.Hn := by linarith
  have hUV : 1 ≤ 2 ^ k * 2 ^ j * d.Hm * d.Hn := by nlinarith
  have hR : 0 < momentPower x := Nat.ceil_pos.2 (by positivity)
  -- step: the labels, band primes and band sizes are at most `Λ = exp(2 L^{1/5})`
  set Λ := Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) with hΛ_def
  have hL5 : 1 ≤ Real.log x ^ (1 / 5 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hΛ : 2 ≤ Λ := by linarith [Real.add_one_le_exp (2 * Real.log x ^ (1 / 5 : ℝ))]
  have hexp : ∀ i, Real.exp (2 * Real.log x ^ d.a i) ≤ Λ := fun i =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL
      (((hd.window i).2.trans hahi.le))) zero_le_two)
  have hband : ∀ i, ∀ q ∈ band x (d.a i), (q : ℝ) ≤ Λ := fun i q hq =>
    (le_exp_of_mem_band hq).trans (hexp i)
  have hcard : ∀ i, ((band x (d.a i)).card : ℝ) ≤ Λ := fun i =>
    (card_band_le x (d.a i)).trans (hexp i)
  have hJ : (padCount x : ℝ) + 1 ≤ Λ := by
    have hJL : (padCount x : ℝ) ≤ Real.log x ^ (1 / 5 : ℝ) :=
      (Nat.floor_le (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))
    linarith [Real.add_one_le_exp (2 * Real.log x ^ (1 / 5 : ℝ))]
  have hlab : ∀ (s : (squareModel d (2 ^ j) (2 ^ k)).State x d) i h,
      (s.1.2 i h : ℝ) ≤ Λ := fun s i h => by
    have hs := (mem_product.1 (mem_filter.1 s.2).1).2
    exact hband i _ (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 (mem_filter.1 hs).1 i) h)
  -- step: the tube, with `d₀, Y ≤ ∏ labels ≤ Λ^{K(J+1)}`
  obtain ⟨-, -, hd₀le, hYle⟩ := confCoeff_ne_zero_imp (by positivity) (by positivity) hR hc
  have hM := listProd_le_pow (hlab (ω 0))
  have hY : (2 : ℝ) ^ j ≤ Λ ^ (K * (padCount x + 1)) := hYle.le.trans hM
  have hd₀ : (2 : ℝ) ^ k ≤ Λ ^ (K * (padCount x + 1)) := hd₀le.trans hM
  have hMS : Λ ^ (K * (padCount x + 1)) ≤ Λ ^ (K * (padCount x + 2)) :=
    pow_le_pow_right₀ (by linarith) (by gcongr; omega)
  have hN : (1 : ℝ) ≤ ((2 * momentPower x : ℕ) : ℝ) := by
    have : 1 ≤ 2 * momentPower x := by omega
    exact_mod_cast this
  have hz : ∀ j', |((ω j').1.1.1.2 : ℝ)| ≤
      2560 * ((2 * momentPower x : ℕ) : ℝ) * (Λ ^ (K * (padCount x + 2))) ^ 2 := by
    intro j'
    have ht := (tube_of_live (by positivity) (by positivity) (by linarith) hR hc hω j').1
    have hdY : (2 : ℝ) ^ k * 2 ^ j ≤ (Λ ^ (K * (padCount x + 2))) ^ 2 := by
      rw [sq]
      exact mul_le_mul (hd₀.trans hMS) (hY.trans hMS) (by positivity) (by positivity)
    push_cast
    calc |((ω j').1.1.1.2 : ℝ)| ≤ 2560 * (2 * momentPower x) * (2 ^ k * 2 ^ j) := ht
      _ ≤ 2560 * (2 * momentPower x) * (Λ ^ (K * (padCount x + 2))) ^ 2 := by gcongr
  -- step: sum over the visits
  have hvisit : ∀ j' : Fin (2 * momentPower x + 1),
      (((cubeIndices n).filter (VisitBad x d (2 ^ j) (2 ^ k * 2 ^ j * d.Hm) d.Hn (ω j').1.2 n
        (ω j').1.1.1)).card : ℝ) ≤
        (n : ℝ) ^ 2 * (10 ^ 7 * ((2 * momentPower x : ℕ) : ℝ) *
          (Λ ^ (K * (padCount x + 2))) ^ 9) := fun j' =>
    card_filter_visitBad_le_pow hU hV hUV hΛ (hlab (ω j')) hband hcard hJ hY₁ hY hn hN (hz j')
  calc ((badCubes x d (2 ^ j) (2 ^ k) n ω).card : ℝ)
      ≤ ((univ.biUnion fun j' => (cubeIndices n).filter (VisitBad x d (2 ^ j)
          (2 ^ k * 2 ^ j * d.Hm) d.Hn (ω j').1.2 n (ω j').1.1.1)).card : ℝ) :=
        Nat.cast_le.2 (card_le_card (badCubes_subset x d hU hV hn ω))
    _ ≤ ∑ j' : Fin (2 * momentPower x + 1), (((cubeIndices n).filter (VisitBad x d (2 ^ j)
          (2 ^ k * 2 ^ j * d.Hm) d.Hn (ω j').1.2 n (ω j').1.1.1)).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _j' : Fin (2 * momentPower x + 1), (n : ℝ) ^ 2 * (10 ^ 7 *
          ((2 * momentPower x : ℕ) : ℝ) * (Λ ^ (K * (padCount x + 2))) ^ 9) :=
        sum_le_sum fun j' _ => hvisit j'
    _ = (n : ℝ) ^ 2 * ((((2 * momentPower x : ℕ) : ℝ) + 1) * (10 ^ 7 *
          ((2 * momentPower x : ℕ) : ℝ) * (Λ ^ (K * (padCount x + 2))) ^ 9)) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (n : ℝ) ^ 2 * Real.exp (Real.log x ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hvis (by positivity)

end Erdos408.OneSided
