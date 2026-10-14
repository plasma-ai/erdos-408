import Mathlib
import Erdos821.Blueprint.Classical
import OAI.NumberTheory.EgyptianFractions.DiscreteFirstDerivative
import OAI.NumberTheory.EgyptianFractions.DiscreteSecondDerivative
import OAI.NumberTheory.EgyptianFractions.SecondDifference

/-!
# Elementary derivative tests for exponential sums

This file copies the architect's interface while its Blueprint module is being
merged.  The estimates below use the corresponding discrete proofs in OAI and
translate their natural-indexed sums to the integer interval in the contract.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.Classical.Deriv

/-- The additive character `e(t) = exp(2πit)`. -/
def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * t * Complex.I)

/-- The two classical derivative tests, with constants uniform in the interval. -/
def DerivativeTests : Prop :=
  (∃ K : ℝ, 0 < K ∧ ∀ (lo hi lam : ℝ) (j : ℤ) (f : ℝ → ℝ),
    lo ≤ hi → 0 < lam → lam ≤ 1 / 2 → DifferentiableOn ℝ f (Set.Icc lo hi) →
    (MonotoneOn (deriv f) (Set.Icc lo hi) ∨ AntitoneOn (deriv f) (Set.Icc lo hi)) →
    (∀ y ∈ Set.Icc lo hi, j + lam ≤ deriv f y ∧ deriv f y ≤ j + 1 - lam) →
    ‖∑ n ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, e (f n)‖ ≤ K / lam) ∧
  (∀ C : ℝ, 1 ≤ C → ∃ K : ℝ, 0 < K ∧ ∀ (lo hi lam : ℝ) (f : ℝ → ℝ),
    lo ≤ hi → 0 < lam → ContDiffOn ℝ 2 f (Set.Icc lo hi) →
    (∀ y ∈ Set.Icc lo hi, lam ≤ |iteratedDeriv 2 f y| ∧
      |iteratedDeriv 2 f y| ≤ C * lam) →
    ‖∑ n ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, e (f n)‖ ≤
      K * ((hi - lo + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹))

private lemma e_eq_phase (t : ℝ) :
    e t = OAI.Problem337.ExponentialSum.phase t := by
  unfold e OAI.Problem337.ExponentialSum.phase
  congr 1
  push_cast
  ring

private lemma slope_on_unit_interval (f : ℝ → ℝ) (lo hi x : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Icc lo hi)) (hlo : lo ≤ x) (hhi : x + 1 ≤ hi) :
    ∃ c ∈ Set.Ioo x (x + 1), deriv f c = f (x + 1) - f x := by
  have hsub : Set.Icc x (x + 1) ⊆ Set.Icc lo hi := by
    intro y hy
    exact ⟨hlo.trans hy.1, hy.2.trans hhi⟩
  obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_slope f (by linarith)
    (hf.continuousOn.mono hsub) (hf.mono (Set.Ioo_subset_Icc_self.trans hsub))
  refine ⟨c, hc, ?_⟩
  rw [hderiv]
  have hx : (x + 1) - x = (1 : ℝ) := by ring
  rw [hx, div_one]

private lemma expSum_int_Icc_eq_range (a b : ℤ) (N : ℕ)
    (hN : (b + 1 - a).toNat = N) (z : ℤ → ℂ) :
    (∑ n ∈ Finset.Icc a b, z n) =
      ∑ i ∈ Finset.range N, z (a + (i : ℤ)) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map, hN]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]

private lemma sqrt_plus_inv_sqrt_ge_two {lam : ℝ} (hlam : 0 < lam) :
    2 ≤ Real.sqrt lam + 1 / Real.sqrt lam := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hprod : Real.sqrt lam * (1 / Real.sqrt lam) = 1 := by field_simp
  have hsq : 0 ≤ (Real.sqrt lam - 1) ^ 2 := sq_nonneg _
  nlinarith

theorem kusmin_landau_part :
    (∃ K : ℝ, 0 < K ∧ ∀ (lo hi lam : ℝ) (j : ℤ) (f : ℝ → ℝ),
      lo ≤ hi → 0 < lam → lam ≤ 1 / 2 → DifferentiableOn ℝ f (Set.Icc lo hi) →
      (MonotoneOn (deriv f) (Set.Icc lo hi) ∨ AntitoneOn (deriv f) (Set.Icc lo hi)) →
      (∀ y ∈ Set.Icc lo hi, j + lam ≤ deriv f y ∧ deriv f y ≤ j + 1 - lam) →
      ‖∑ n ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, e (f n)‖ ≤ K / lam) := by
    refine ⟨3, by norm_num, ?_⟩
    intro lo hi lam j f hlohi hlam hlam2 hdiff hmono hrange
    let a : ℤ := ⌈lo⌉
    let b : ℤ := ⌊hi⌋
    change ‖∑ n ∈ Finset.Icc a b, e (f n)‖ ≤ 3 / lam
    by_cases hab : a ≤ b
    · by_cases hgap : 1 ≤ b - a
      · let N : ℕ := (b - a - 1).toNat
        have hNcast : (N : ℤ) = b - a - 1 := by
          dsimp [N]
          exact Int.toNat_of_nonneg (by omega)
        have hlen : (b + 1 - a).toNat = N + 2 := by
          have hcast : (((b + 1 - a).toNat : ℕ) : ℤ) = (N + 2 : ℕ) := by
            rw [Int.toNat_of_nonneg (by omega : 0 ≤ b + 1 - a), Nat.cast_add,
              Nat.cast_ofNat, hNcast]
            omega
          exact_mod_cast hcast
        have hloA : lo ≤ (a : ℝ) := by
          dsimp [a]
          exact Int.le_ceil lo
        have hbHi : (b : ℝ) ≤ hi := by
          dsimp [b]
          exact Int.floor_le hi
        let g : ℕ → ℝ := fun i => f ((a : ℝ) + i)
        have hunitBounds (i : ℕ) (hiN : i ≤ N) :
            lo ≤ (a : ℝ) + i ∧ (a : ℝ) + i + 1 ≤ hi := by
          have hik : (a : ℤ) + (i : ℤ) + 1 ≤ b := by
            have hiInt : (i : ℤ) ≤ N := by exact_mod_cast hiN
            omega
          have hikR : (((a : ℤ) + (i : ℤ) + 1 : ℤ) : ℝ) ≤ (b : ℝ) := by
            exact_mod_cast hik
          push_cast at hikR
          constructor
          · have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
            linarith
          · exact hikR.trans hbHi
        have hstep (i : ℕ) (hiN : i ≤ N) :
            ∃ c ∈ Set.Ioo ((a : ℝ) + i) ((a : ℝ) + i + 1),
              deriv f c = g (i + 1) - g i := by
          rcases hunitBounds i hiN with ⟨hleft, hright⟩
          obtain ⟨c, hc, hder⟩ := slope_on_unit_interval f lo hi
            ((a : ℝ) + i) hdiff hleft hright
          refine ⟨c, hc, ?_⟩
          have hg : g (i + 1) - g i =
              f ((a : ℝ) + i + 1) - f ((a : ℝ) + i) := by
            dsimp [g]
            congr 1
            simp only [Nat.cast_add, Nat.cast_one, add_assoc]
          rw [hg]
          exact hder
        have hstepI (i : ℕ) (hiN : i ≤ N) :
            ∃ c ∈ Set.Ioo ((a : ℝ) + i) ((a : ℝ) + i + 1),
              deriv f c = g (i + 1) - g i ∧ c ∈ Set.Icc lo hi := by
          obtain ⟨c, hc, hder⟩ := hstep i hiN
          rcases hunitBounds i hiN with ⟨hleft, hright⟩
          refine ⟨c, hc, hder, ?_⟩
          exact ⟨hleft.trans hc.1.le, hc.2.le.trans hright⟩
        have hloStep : ∀ i ≤ N, (j : ℝ) + lam ≤ g (i + 1) - g i := by
          intro i hiN
          obtain ⟨c, hc, hder, hcI⟩ := hstepI i hiN
          have hh := (hrange c hcI).1
          rw [← hder]
          exact hh
        have hhiStep : ∀ i ≤ N, g (i + 1) - g i ≤ (j : ℝ) + 1 - lam := by
          intro i hiN
          obtain ⟨c, hc, hder, hcI⟩ := hstepI i hiN
          have hh := (hrange c hcI).2
          rw [← hder]
          exact hh
        have hmonoStep :
            MonotoneOn (fun i => g (i + 1) - g i) (Set.Iic N) ∨
              AntitoneOn (fun i => g (i + 1) - g i) (Set.Iic N) := by
          rcases hmono with hm | ha
          · left
            intro i hi j hj hij
            have hiN : i ≤ N := Set.mem_Iic.mp hi
            have hjN : j ≤ N := Set.mem_Iic.mp hj
            by_cases heq : i = j
            · subst j
              exact le_rfl
            · have hij' : i < j := lt_of_le_of_ne hij heq
              obtain ⟨ci, hci, hciEq, hciI⟩ := hstepI i hiN
              obtain ⟨cj, hcj, hcjEq, hcjI⟩ := hstepI j hjN
              have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
                have hNat : i + 1 ≤ j := Nat.succ_le_iff.mpr hij'
                exact_mod_cast hNat
              have hcij : ci ≤ cj := by
                have hleft : ci < (a : ℝ) + i + 1 := hci.2
                have hright : (a : ℝ) + j < cj := hcj.1
                linarith
              change g (i + 1) - g i ≤ g (j + 1) - g j
              rw [← hciEq, ← hcjEq]
              exact hm hciI hcjI hcij
          · right
            intro i hi j hj hij
            have hiN : i ≤ N := Set.mem_Iic.mp hi
            have hjN : j ≤ N := Set.mem_Iic.mp hj
            by_cases heq : i = j
            · subst j
              exact le_rfl
            · have hij' : i < j := lt_of_le_of_ne hij heq
              obtain ⟨ci, hci, hciEq, hciI⟩ := hstepI i hiN
              obtain ⟨cj, hcj, hcjEq, hcjI⟩ := hstepI j hjN
              have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
                have hNat : i + 1 ≤ j := Nat.succ_le_iff.mpr hij'
                exact_mod_cast hNat
              have hcij : ci ≤ cj := by
                have hleft : ci < (a : ℝ) + i + 1 := hci.2
                have hright : (a : ℝ) + j < cj := hcj.1
                linarith
              change g (j + 1) - g j ≤ g (i + 1) - g i
              rw [← hciEq, ← hcjEq]
              exact ha hciI hcjI hcij
        have hKL := OAI.Problem337.ExponentialSum.first_derivative_sum_bound_either_succ
          g N lam j hlam hloStep hhiStep hmonoStep
        have hgcast (i : ℕ) : g i = f (((a + (i : ℤ) : ℤ) : ℝ)) := by
          dsimp [g]
          congr 1
          simp only [Int.cast_add, Int.cast_natCast]
        have hsum :
            (∑ n ∈ Finset.Icc a b, e (f n)) =
              (∑ i ∈ Finset.range (N + 1), OAI.Problem337.ExponentialSum.phase (g i)) +
                OAI.Problem337.ExponentialSum.phase (g (N + 1)) := by
          rw [expSum_int_Icc_eq_range a b (N + 2) hlen (fun n => e (f n)),
            show N + 2 = (N + 1) + 1 by omega, Finset.sum_range_succ]
          apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro i hi
            rw [e_eq_phase, ← hgcast]
          · rw [e_eq_phase, ← hgcast]
        have hinv : 1 ≤ 1 / lam := by
          apply (le_div_iff₀ hlam).2
          linarith
        rw [hsum]
        calc
          _ ≤ ‖∑ i ∈ Finset.range (N + 1),
                OAI.Problem337.ExponentialSum.phase (g i)‖ +
                ‖OAI.Problem337.ExponentialSum.phase (g (N + 1))‖ := norm_add_le _ _
          _ ≤ 2 / lam + 1 := by
            exact add_le_add hKL (by simp [OAI.Problem337.ExponentialSum.phase_norm])
          _ ≤ 3 / lam := by
            calc
              2 / lam + 1 ≤ 2 / lam + 1 / lam := add_le_add le_rfl hinv
              _ = 3 / lam := by ring
      · have heq : a = b := by omega
        have heq' : ⌈lo⌉ = ⌊hi⌋ := by simpa [a, b] using heq
        have hs : Finset.Icc ⌈lo⌉ ⌊hi⌋ = {⌈lo⌉} := by
          rw [heq']
          exact Finset.Icc_self _
        rw [hs, Finset.sum_singleton]
        have hnorm : ‖e (f (⌈lo⌉ : ℝ))‖ = 1 := by
          rw [e_eq_phase]
          exact OAI.Problem337.ExponentialSum.phase_norm _
        rw [hnorm]
        have hinv : 1 ≤ 1 / lam := by
          apply (le_div_iff₀ hlam).2
          linarith
        calc
          1 ≤ 1 / lam := hinv
          _ ≤ 3 / lam := by
            apply div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3)
            positivity
    · have he : Finset.Icc a b = ∅ := Finset.Icc_eq_empty (by omega)
      rw [he, Finset.sum_empty, norm_zero]
      positivity

private lemma contDiffAt_deriv_interior {lo hi : ℝ} {f : ℝ → ℝ} {y : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Icc lo hi)) (hy : y ∈ Set.Ioo lo hi) :
    ContDiffAt ℝ 1 (deriv f) y := by
  have hyInt : y ∈ interior (Set.Icc lo hi) := by
    simpa [interior_Icc] using hy
  have hyNhds : Set.Icc lo hi ∈ nhds y :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hyInt) interior_subset
  exact (hf.contDiffAt hyNhds).derivWithin (by norm_num)

private lemma hasDerivAt_interior {lo hi : ℝ} {f : ℝ → ℝ} {y : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Icc lo hi)) (hy : y ∈ Set.Ioo lo hi) :
    HasDerivAt f (deriv f y) y := by
  have hyInt : y ∈ interior (Set.Icc lo hi) := by
    simpa [interior_Icc] using hy
  have hyNhds : Set.Icc lo hi ∈ nhds y :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hyInt) interior_subset
  exact (hf.contDiffAt hyNhds).differentiableAt (by norm_num) |>.hasDerivAt

private lemma hasDerivAt_deriv_interior {lo hi : ℝ} {f : ℝ → ℝ} {y : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Icc lo hi)) (hy : y ∈ Set.Ioo lo hi) :
    HasDerivAt (deriv f) (iteratedDeriv 2 f y) y := by
  have hh :=
    ((contDiffAt_deriv_interior hf hy).differentiableAt (by norm_num)).hasDerivAt
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using hh

private lemma second_difference_eq_iteratedDeriv {lo hi : ℝ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Icc lo hi)) {x : ℝ}
    (hlo : lo ≤ x) (hhi : x + 2 ≤ hi) :
    ∃ d ∈ Set.Ioo x (x + 2),
      f (x + 2) - 2 * f (x + 1) + f x = iteratedDeriv 2 f d := by
  let g : ℝ → ℝ := fun y => f (y + 1) - f y
  have hmap0 : Set.Icc x (x + 1) ⊆ Set.Icc lo hi := by
    intro y hy
    have hyUpper : y ≤ x + 2 := by linarith [hy.2]
    exact ⟨hlo.trans hy.1, hyUpper.trans hhi⟩
  have hmap1 : ∀ y ∈ Set.Icc x (x + 1), y + 1 ∈ Set.Icc lo hi := by
    intro y hy
    exact ⟨by linarith [hlo, hy.1], by linarith [hy.2, hhi]⟩
  have hfc : ContinuousOn f (Set.Icc lo hi) := hf.continuousOn
  have hgcont : ContinuousOn g (Set.Icc x (x + 1)) := by
    dsimp [g]
    exact (hfc.comp (continuousOn_id.add continuousOn_const) hmap1).sub
      (hfc.mono hmap0)
  have hgd (y : ℝ) (hy : y ∈ Set.Ioo x (x + 1)) :
      HasDerivAt g (deriv f (y + 1) - deriv f y) y := by
    have hy0 : y ∈ Set.Ioo lo hi :=
      ⟨lt_of_le_of_lt hlo hy.1, lt_of_lt_of_le hy.2 (by linarith [hhi])⟩
    have hy1 : y + 1 ∈ Set.Ioo lo hi :=
      ⟨by linarith [hlo, hy.1], lt_of_lt_of_le (by linarith [hy.2]) hhi⟩
    have ht := (hasDerivAt_interior hf hy1).comp_add_const y 1
    simpa [g] using ht.fun_sub (hasDerivAt_interior hf hy0)
  have hgdiff : DifferentiableOn ℝ g (Set.Ioo x (x + 1)) := by
    intro y hy
    exact (hgd y hy).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hcg⟩ := exists_deriv_eq_slope g (by linarith : x < x + 1)
    hgcont hgdiff
  have hc0 : c ∈ Set.Ioo lo hi :=
    ⟨lt_of_le_of_lt hlo hc.1, lt_of_lt_of_le hc.2 (by linarith [hhi])⟩
  have hc1 : c + 1 ∈ Set.Ioo lo hi :=
    ⟨by linarith [hlo, hc.1], lt_of_lt_of_le (by linarith [hc.2]) hhi⟩
  have hgc : deriv g c = deriv f (c + 1) - deriv f c := hgd c hc |>.deriv
  have hfirst : f (x + 2) - 2 * f (x + 1) + f x = deriv g c := by
    have htmp := hcg
    rw [show (x + 1) - x = 1 by ring, div_one] at htmp
    simp only [g, show x + 1 + 1 = x + 2 by ring] at htmp
    calc
      _ = (f (x + 2) - f (x + 1)) - (f (x + 1) - f x) := by ring
      _ = deriv g c := htmp.symm
  have hmapDeriv : Set.Icc c (c + 1) ⊆ Set.Ioo lo hi := by
    intro y hy
    refine ⟨lt_of_le_of_lt hlo (lt_of_lt_of_le hc.1 hy.1), ?_⟩
    have hcEnd : c + 1 < hi := lt_of_lt_of_le (by linarith [hc.2]) hhi
    exact lt_of_le_of_lt hy.2 hcEnd
  have hderivcont : ContinuousOn (deriv f) (Set.Icc c (c + 1)) := by
    intro y hy
    exact (contDiffAt_deriv_interior hf (hmapDeriv hy)).continuousAt.continuousWithinAt
  have hderivdiff : DifferentiableOn ℝ (deriv f) (Set.Ioo c (c + 1)) := by
    intro y hy
    have hyGlobal := hmapDeriv ⟨hy.1.le, hy.2.le⟩
    exact (hasDerivAt_deriv_interior hf hyGlobal).differentiableAt.differentiableWithinAt
  obtain ⟨d, hd, hdd⟩ := exists_deriv_eq_slope (deriv f) (by linarith : c < c + 1)
    hderivcont hderivdiff
  have hdd' : deriv (deriv f) d = deriv f (c + 1) - deriv f c := by
    rw [show (c + 1) - c = 1 by ring, div_one] at hdd
    exact hdd
  have hdGlobal := hmapDeriv ⟨hd.1.le, hd.2.le⟩
  have hderiv2 := (hasDerivAt_deriv_interior hf hdGlobal).deriv
  refine ⟨d, ⟨lt_trans hc.1 hd.1, lt_trans hd.2 (by linarith [hc.2])⟩, ?_⟩
  calc
    f (x + 2) - 2 * f (x + 1) + f x = deriv g c := hfirst
    _ = deriv f (c + 1) - deriv f c := hgc
    _ = deriv (deriv f) d := hdd'.symm
    _ = iteratedDeriv 2 f d := hderiv2

private lemma second_difference_bounds_of_contDiff {lo hi : ℝ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Icc lo hi)) {x L U : ℝ}
    (hlo : lo ≤ x) (hhi : x + 2 ≤ hi)
    (hbound : ∀ y ∈ Set.Ioo lo hi, L ≤ iteratedDeriv 2 f y ∧
      iteratedDeriv 2 f y ≤ U) :
    L ≤ f (x + 2) - 2 * f (x + 1) + f x ∧
      f (x + 2) - 2 * f (x + 1) + f x ≤ U := by
  obtain ⟨d, hd, heq⟩ := second_difference_eq_iteratedDeriv hf hlo hhi
  rw [heq]
  exact hbound d ⟨lt_of_le_of_lt hlo hd.1, lt_of_lt_of_le hd.2 hhi⟩

private lemma discrete_second_derivative_bound_of_contDiff {lo hi x lam A : ℝ}
    {f : ℝ → ℝ} (N : ℕ) (hf : ContDiffOn ℝ 2 f (Set.Icc lo hi))
    (hlo : lo ≤ x) (hhi : x + N ≤ hi) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hbound : ∀ y ∈ Set.Ioo lo hi,
      lam ≤ iteratedDeriv 2 f y ∧ iteratedDeriv 2 f y ≤ A * lam) :
    ‖∑ j ∈ Finset.range N,
      OAI.Problem337.ExponentialSum.phase (f (x + (j : ℝ)))‖ ≤
        6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  let g : ℕ → ℝ := fun j => f (x + (j : ℝ))
  let d : ℕ → ℝ := fun j => g (j + 1) - g j
  have hstep (n j : ℕ) (hj : j < N) (hnj : n ∈ Finset.Ico 0 j) :
      lam ≤ d (n + 1) - d n ∧ d (n + 1) - d n ≤ A * lam := by
    have hn2 : n + 2 ≤ N := by
      have hnj' := Finset.mem_Ico.mp hnj
      omega
    have hn2R : (n : ℝ) + 2 ≤ (N : ℝ) := by exact_mod_cast hn2
    have hleft : lo ≤ x + (n : ℝ) := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hright : x + (n : ℝ) + 2 ≤ hi := by linarith
    have hlocal : lam ≤ f (x + (n : ℝ) + 2) - 2 * f (x + (n : ℝ) + 1) +
          f (x + (n : ℝ)) ∧
        f (x + (n : ℝ) + 2) - 2 * f (x + (n : ℝ) + 1) +
          f (x + (n : ℝ)) ≤ A * lam :=
      second_difference_bounds_of_contDiff (L := lam) (U := A * lam) hf hleft hright hbound
    have hrewrite : d (n + 1) - d n =
        f (x + (n : ℝ) + 2) - 2 * f (x + (n : ℝ) + 1) + f (x + (n : ℝ)) := by
      dsimp [d, g]
      push_cast
      ring
    rw [hrewrite]
    exact hlocal
  have hsepBoth : ∀ i < N, ∀ j < N, i ≤ j →
      lam * ((j : ℝ) - i) ≤ d j - d i ∧
      d j - d i ≤ A * lam * ((j : ℝ) - i) := by
    intro i hi j hj hij
    exact OAI.Problem337.discrete_increment_bounds d i j lam (A * lam) hij
      (by
        intro n hn
        have h := hstep n j hj (by
          have hn' := Finset.mem_Ico.mp hn
          exact Finset.mem_Ico.mpr ⟨Nat.zero_le _, hn'.2⟩)
        simpa only [mul_assoc] using h)
  have hsep : ∀ i < N, ∀ j < N, i ≤ j →
      lam * ((j : ℝ) - i) ≤ d j - d i := by
    intro i hi j hj hij
    exact (hsepBoth i hi j hj hij).1
  have hmono : MonotoneOn d (Set.Iio N) := by
    intro i hi j hj hij
    by_cases heq : i = j
    · subst j
      exact le_rfl
    · have hij' : i < j := lt_of_le_of_ne hij heq
      have h := hsep i (Set.mem_Iio.mp hi) j (Set.mem_Iio.mp hj) (le_of_lt hij')
      have hijR : (i : ℝ) < j := by exact_mod_cast hij'
      have hdist : 0 < (j : ℝ) - i := by linarith
      have hpos := mul_pos hlam hdist
      change d i ≤ d j
      linarith
  have hrange : ∀ j < N, d 0 ≤ d j ∧ d j ≤ d 0 + A * lam * N := by
    intro j hj
    have h := hsepBoth 0 (by omega) j hj (Nat.zero_le j)
    have hjN : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj.le
    have hAL : 0 ≤ A * lam := mul_nonneg hA hlam.le
    have hupper := mul_le_mul_of_nonneg_left hjN hAL
    have hlow : lam * (j : ℝ) ≤ d j - d 0 := by
      simpa only [Nat.cast_zero, sub_zero] using h.1
    have hup : d j - d 0 ≤ A * lam * (j : ℝ) := by
      simpa only [Nat.cast_zero, sub_zero] using h.2
    have hnonneg : 0 ≤ lam * (j : ℝ) := mul_nonneg hlam.le (Nat.cast_nonneg j)
    constructor
    · linarith
    · calc
        d j ≤ d 0 + A * lam * (j : ℝ) := by linarith
        _ ≤ d 0 + A * lam * N := by linarith [hupper]
  simpa only [g, d] using
    (OAI.Problem337.ExponentialSum.discrete_second_derivative_sqrt_bound
      g N lam A (d 0) hlam hlam1 hA hmono hsep hrange)

theorem second_derivative_part :
    (∀ C : ℝ, 1 ≤ C → ∃ K : ℝ, 0 < K ∧
      ∀ (lo hi lam : ℝ) (f : ℝ → ℝ),
        lo ≤ hi → 0 < lam → ContDiffOn ℝ 2 f (Set.Icc lo hi) →
        (∀ y ∈ Set.Icc lo hi, lam ≤ |iteratedDeriv 2 f y| ∧
          |iteratedDeriv 2 f y| ≤ C * lam) →
        ‖∑ n ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, e (f n)‖ ≤
          K * ((hi - lo + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹)) := by
  intro C hC
  refine ⟨6 * C + 16, by positivity, ?_⟩
  intro lo hi lam f hlohi hlam hf hbound
  let a : ℤ := ⌈lo⌉
  let b : ℤ := ⌊hi⌋
  change ‖∑ n ∈ Finset.Icc a b, e (f n)‖ ≤
    (6 * C + 16) * ((hi - lo + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹)
  by_cases hab : a ≤ b
  ·
    let N : ℕ := (b - a).toNat
    have hNInt : (N : ℤ) = b - a := by
      dsimp [N]
      exact Int.toNat_of_nonneg (by omega)
    have hNReal : (N : ℝ) = (b : ℝ) - (a : ℝ) := by
      exact_mod_cast hNInt
    have hlen : (b + 1 - a).toNat = N + 1 := by
      have hcast : (((b + 1 - a).toNat : ℕ) : ℤ) = ((N + 1 : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ b + 1 - a), Nat.cast_add,
          Nat.cast_one, hNInt]
        omega
      exact_mod_cast hcast
    let g : ℕ → ℝ := fun i => f ((a : ℝ) + (i : ℝ))
    have hgcast (i : ℕ) : g i = f (((a + (i : ℤ) : ℤ) : ℝ)) := by
      dsimp [g]
      congr 1
      simp only [Int.cast_add, Int.cast_natCast]
    have hsum :
        (∑ n ∈ Finset.Icc a b, e (f n)) =
          ∑ i ∈ Finset.range (N + 1),
            OAI.Problem337.ExponentialSum.phase (g i) := by
      rw [expSum_int_Icc_eq_range a b (N + 1) hlen (fun n => e (f n))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [e_eq_phase, ← hgcast]
    have ha : lo ≤ (a : ℝ) := by
      dsimp [a]
      exact Int.le_ceil lo
    have hb : (b : ℝ) ≤ hi := by
      dsimp [b]
      exact Int.floor_le hi
    have hNle : (N : ℝ) ≤ hi - lo := by
      rw [hNReal]
      linarith
    have hH : 0 ≤ hi - lo := sub_nonneg.mpr hlohi
    have hK : 1 ≤ 6 * C + 16 := by linarith
    have hroot : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have hInvNonneg : 0 ≤ (Real.sqrt lam)⁻¹ := by positivity
    let X : ℝ := (hi - lo + 1) * Real.sqrt lam
    let Y : ℝ := (Real.sqrt lam)⁻¹
    have hXnonneg : 0 ≤ X := by
      dsimp [X]
      exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    have hYnonneg : 0 ≤ Y := hInvNonneg
    by_cases hlam1 : lam ≤ 1
    · have hsle : Real.sqrt lam ≤ 1 := by
        nlinarith [Real.sq_sqrt hlam.le]
      have hInvOne : 1 ≤ 1 / Real.sqrt lam := by
        apply (le_div_iff₀ hroot).2
        simpa using hsle
      by_cases hNzero : N = 0
      · have hsingle :
            ‖∑ n ∈ Finset.Icc a b, e (f n)‖ = 1 := by
          rw [hsum]
          simp [hNzero, OAI.Problem337.ExponentialSum.phase_norm]
        have hYle : Y ≤ (6 * C + 16) * Y := by
          have hh := mul_le_mul_of_nonneg_right hK hInvNonneg
          simpa using hh
        have hYTarget : (6 * C + 16) * Y ≤
            (6 * C + 16) * (X + Y) := by
          apply mul_le_mul_of_nonneg_left
          · dsimp [X]
            linarith
          · positivity
        rw [hsingle]
        exact le_trans (le_trans (by simpa [Y] using hInvOne) hYle) hYTarget
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hNzero
        have habReal : (a : ℝ) < b := by
          have : 0 < (N : ℝ) := by exact_mod_cast hNpos
          rw [hNReal] at this
          linarith
        have hlohi : lo < hi := by linarith
        have hsecond : ∀ y ∈ Set.Ioo lo hi,
            HasDerivAt (deriv f) (iteratedDeriv 2 f y) y := by
          intro y hy
          exact hasDerivAt_deriv_interior hf hy
        have hboundOpen : ∀ y ∈ Set.Ioo lo hi,
            lam ≤ |iteratedDeriv 2 f y| ∧
              |iteratedDeriv 2 f y| ≤ C * lam := by
          intro y hy
          exact hbound y ⟨hy.1.le, hy.2.le⟩
        rcases OAI.Problem337.second_derivative_signed_bounds
            (deriv f) (iteratedDeriv 2 f) (Set.Ioo lo hi)
            (convex_Ioo lo hi) lam (C * lam) hlam hsecond hboundOpen with
          hpos | hneg
        · have hCurv : ∀ y ∈ Set.Ioo lo hi,
              lam ≤ iteratedDeriv 2 f y ∧ iteratedDeriv 2 f y ≤ C * lam := hpos
          have hright : (a : ℝ) + N ≤ hi := by
            rw [hNReal]
            linarith
          have hinner := discrete_second_derivative_bound_of_contDiff
            (lo := lo) (hi := hi) (x := (a : ℝ)) (lam := lam) (A := C)
            N hf ha hright hlam hlam1 (by linarith) hCurv
          have hfull :
              ‖∑ i ∈ Finset.range (N + 1),
                  OAI.Problem337.ExponentialSum.phase (g i)‖ ≤
                6 * C * N * Real.sqrt lam + 6 / Real.sqrt lam + 10 := by
            rw [Finset.sum_range_succ]
            calc
              _ ≤ ‖∑ i ∈ Finset.range N,
                    OAI.Problem337.ExponentialSum.phase (g i)‖ +
                  ‖OAI.Problem337.ExponentialSum.phase (g N)‖ := norm_add_le _ _
              _ ≤ (6 * C * N * Real.sqrt lam + 6 / Real.sqrt lam + 9) + 1 :=
                add_le_add hinner (by simp [OAI.Problem337.ExponentialSum.phase_norm])
              _ = 6 * C * N * Real.sqrt lam + 6 / Real.sqrt lam + 10 := by ring
          have hterm : 6 * C * N * Real.sqrt lam ≤ 6 * C * X := by
            have hNplus : (N : ℝ) ≤ hi - lo + 1 := by linarith
            have hmul := mul_le_mul_of_nonneg_right hNplus (Real.sqrt_nonneg lam)
            dsimp [X]
            nlinarith [mul_nonneg (by linarith : 0 ≤ 6 * C)
              (mul_nonneg (Real.sqrt_nonneg lam) (by linarith : 0 ≤ hi - lo + 1))]
          have hrest : 6 / Real.sqrt lam + 10 ≤ 16 * Y := by
            have hInvOneY : 1 ≤ Y := by simpa [Y] using hInvOne
            have hsix : 6 / Real.sqrt lam = 6 * Y := by
              rw [div_eq_mul_inv]
            nlinarith [hInvOneY, hsix]
          have hcoeffX : 6 * C ≤ 6 * C + 16 := by linarith
          have hcoeffY : 16 ≤ 6 * C + 16 := by linarith
          have hcompare : 6 * C * X + 16 * Y ≤
              (6 * C + 16) * (X + Y) := by
            calc
              _ ≤ (6 * C + 16) * X + (6 * C + 16) * Y := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_right hcoeffX hXnonneg)
                  (mul_le_mul_of_nonneg_right hcoeffY hYnonneg)
              _ = (6 * C + 16) * (X + Y) := by ring
          rw [hsum]
          exact (hfull.trans (by nlinarith [hterm, hrest])).trans hcompare
        · let fneg : ℝ → ℝ := fun y => -f y
          have hfneg : ContDiffOn ℝ 2 fneg (Set.Icc lo hi) := by
            simpa [fneg] using hf.neg
          have hiterNeg (y : ℝ) : iteratedDeriv 2 fneg y = -iteratedDeriv 2 f y := by
            simp [fneg, iteratedDeriv_succ]
          have hCurv : ∀ y ∈ Set.Ioo lo hi,
              lam ≤ iteratedDeriv 2 fneg y ∧ iteratedDeriv 2 fneg y ≤ C * lam := by
            intro y hy
            have hh := hneg y hy
            rw [hiterNeg]
            constructor <;> nlinarith [hh.1, hh.2]
          have hright : (a : ℝ) + N ≤ hi := by
            rw [hNReal]
            linarith
          have hinnerNeg := discrete_second_derivative_bound_of_contDiff
            (lo := lo) (hi := hi) (x := (a : ℝ)) (lam := lam) (A := C)
            N hfneg ha hright hlam hlam1 (by linarith) hCurv
          have hinner :
              ‖∑ i ∈ Finset.range N,
                  OAI.Problem337.ExponentialSum.phase (g i)‖ ≤
                6 * C * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
            simpa only [fneg, OAI.Problem337.ExponentialSum.phase_neg,
              ← map_sum, Complex.norm_conj] using hinnerNeg
          have hfull :
              ‖∑ i ∈ Finset.range (N + 1),
                  OAI.Problem337.ExponentialSum.phase (g i)‖ ≤
                6 * C * N * Real.sqrt lam + 6 / Real.sqrt lam + 10 := by
            rw [Finset.sum_range_succ]
            calc
              _ ≤ ‖∑ i ∈ Finset.range N,
                    OAI.Problem337.ExponentialSum.phase (g i)‖ +
                  ‖OAI.Problem337.ExponentialSum.phase (g N)‖ := norm_add_le _ _
              _ ≤ (6 * C * N * Real.sqrt lam + 6 / Real.sqrt lam + 9) + 1 :=
                add_le_add hinner (by simp [OAI.Problem337.ExponentialSum.phase_norm])
              _ = 6 * C * N * Real.sqrt lam + 6 / Real.sqrt lam + 10 := by ring
          have hterm : 6 * C * N * Real.sqrt lam ≤ 6 * C * X := by
            have hNplus : (N : ℝ) ≤ hi - lo + 1 := by linarith
            have hmul := mul_le_mul_of_nonneg_right hNplus (Real.sqrt_nonneg lam)
            dsimp [X]
            nlinarith [mul_nonneg (by linarith : 0 ≤ 6 * C)
              (mul_nonneg (Real.sqrt_nonneg lam) (by linarith : 0 ≤ hi - lo + 1))]
          have hrest : 6 / Real.sqrt lam + 10 ≤ 16 * Y := by
            have hInvOneY : 1 ≤ Y := by simpa [Y] using hInvOne
            have hsix : 6 / Real.sqrt lam = 6 * Y := by
              rw [div_eq_mul_inv]
            nlinarith [hInvOneY, hsix]
          have hcoeffX : 6 * C ≤ 6 * C + 16 := by linarith
          have hcoeffY : 16 ≤ 6 * C + 16 := by linarith
          have hcompare : 6 * C * X + 16 * Y ≤
              (6 * C + 16) * (X + Y) := by
            calc
              _ ≤ (6 * C + 16) * X + (6 * C + 16) * Y := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_right hcoeffX hXnonneg)
                  (mul_le_mul_of_nonneg_right hcoeffY hYnonneg)
              _ = (6 * C + 16) * (X + Y) := by ring
          rw [hsum]
          exact (hfull.trans (by nlinarith [hterm, hrest])).trans hcompare
    · have hlarge : 1 < lam := lt_of_not_ge hlam1
      have hsge : 1 ≤ Real.sqrt lam := by
        nlinarith [Real.sq_sqrt hlam.le]
      have htrivial :
          ‖∑ n ∈ Finset.Icc a b, e (f n)‖ ≤ (N : ℝ) + 1 := by
        rw [hsum]
        calc
          _ ≤ ∑ i ∈ Finset.range (N + 1),
              ‖OAI.Problem337.ExponentialSum.phase (g i)‖ := norm_sum_le _ _
          _ = (N : ℝ) + 1 := by
            simp [OAI.Problem337.ExponentialSum.phase_norm]
      have hNplus : (N : ℝ) + 1 ≤ hi - lo + 1 := by linarith
      have hXlower : (hi - lo + 1) ≤ X := by
        dsimp [X]
        have hbase : 0 ≤ hi - lo + 1 := by linarith
        calc
          _ = (hi - lo + 1) * 1 := by ring
          _ ≤ (hi - lo + 1) * Real.sqrt lam :=
            mul_le_mul_of_nonneg_left hsge hbase
      have hbase : 0 ≤ hi - lo + 1 := by linarith
      have htarget : X ≤ (6 * C + 16) * (X + Y) := by
        have hXY : X ≤ X + Y := by linarith [hYnonneg]
        have hmul := mul_le_mul_of_nonneg_left hXY (by positivity : 0 ≤ 6 * C + 16)
        nlinarith [mul_nonneg (sub_nonneg.mpr hK) hXnonneg]
      exact htrivial.trans (hNplus.trans (hXlower.trans htarget))
  · have he : Finset.Icc a b = ∅ := Finset.Icc_eq_empty (by omega)
    rw [he, Finset.sum_empty, norm_zero]
    positivity


end Erdos821.Classical.Deriv

namespace Erdos821.Blueprint

theorem DerivativeTests_proof : DerivativeTests := by
  exact ⟨Erdos821.Classical.Deriv.kusmin_landau_part,
    Erdos821.Classical.Deriv.second_derivative_part⟩

example : type_of% @DerivativeTests_proof = DerivativeTests := rfl

end Erdos821.Blueprint


end
