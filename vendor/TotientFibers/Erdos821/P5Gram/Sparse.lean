import Erdos821.Blueprint.Classical

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Gram
open Blueprint.Analytic
open Blueprint

attribute [local instance] Classical.propDecidable

/-- §4 sparse-gram-kernel: the full containing interval, never an arbitrary subset.
For |z|<1 use the number of terms. For 1≤|z|≤cU apply the first derivative
test to z log(v)/(2π), whose derivative stays below 1/2 in absolute value.
For cU<|z|≤Y apply the second derivative test, obtaining
O(sqrt(|z|)+U/sqrt(|z|))=O(sqrt(Y)). Handle both signs by conjugation.
The conversion between natural-index dp and integer-index e must retain
the ceiling/floor endpoints. Only the two P1 derivative fields are inputs. -/
def SparseGramKernelTask : Prop :=
  Blueprint.DerivativeTests → ∃ K : ℝ, 0 < K ∧ ∀ (Y U z : ℝ),
    1 ≤ U → U ≤ Y → |z| ≤ Y →
    ‖dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) z‖ ≤
      K * (U / (1 + |z|) + Real.sqrt Y)

-- Phase function for the exponential sum.
def phase (z : ℝ) (v : ℝ) : ℝ := z * Real.log v / (2 * Real.pi)

lemma phase_eq (z v : ℝ) : phase z v = (z / (2 * Real.pi)) * Real.log v := by
  unfold phase; ring

lemma deriv_phase_eq (z : ℝ) : deriv (phase z) = fun x => (z / (2 * Real.pi)) * x⁻¹ := by
  have h : phase z = fun v => (z / (2 * Real.pi)) * Real.log v := by
    funext v; unfold phase; ring
  rw [h, deriv_const_mul_field', Real.deriv_log']

lemma deriv_phase_apply (z x : ℝ) : deriv (phase z) x = (z / (2 * Real.pi)) * x⁻¹ := by
  rw [deriv_phase_eq]

lemma iteratedDeriv2_phase_eq (z : ℝ) :
    iteratedDeriv 2 (phase z) = fun x => (z / (2 * Real.pi)) * (-(x ^ 2)⁻¹) := by
  have h1 : iteratedDeriv 2 (phase z) = deriv (deriv (phase z)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h1, deriv_phase_eq, deriv_const_mul_field', deriv_inv']

lemma iteratedDeriv2_phase_apply (z x : ℝ) :
    iteratedDeriv 2 (phase z) x = (z / (2 * Real.pi)) * (-(x ^ 2)⁻¹) := by
  rw [iteratedDeriv2_phase_eq]

lemma mellin_eq_phase (n z : ℝ) : Blueprint.Analytic.mellin n z = Blueprint.Analytic.e (phase z n) := by
  unfold Blueprint.Analytic.mellin Blueprint.Analytic.e phase
  congr 1
  push_cast
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

lemma norm_mellin (n z : ℝ) : ‖Blueprint.Analytic.mellin n z‖ = 1 := by
  simp [Blueprint.Analytic.mellin, Complex.norm_exp]

lemma norm_mellin_nat (n : ℕ) (z : ℝ) : ‖Blueprint.Analytic.mellin (n : ℝ) z‖ = 1 :=
  norm_mellin _ _

lemma dp_eq_phase_sum (U z : ℝ) :
    Blueprint.Analytic.dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) z =
      ∑ n ∈ Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊, Blueprint.Analytic.e (phase z (n : ℝ)) := by
  unfold Blueprint.Analytic.dp
  apply Finset.sum_congr rfl
  intro n _
  simp only [one_mul]
  exact mellin_eq_phase (n : ℝ) z

lemma norm_dp_le_card (U z : ℝ) :
    ‖Blueprint.Analytic.dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) z‖ ≤
      ((Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊).card : ℝ) := by
  calc ‖Blueprint.Analytic.dp _ _ _‖
      ≤ ∑ _n ∈ Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊, ‖(1 : ℂ) * Blueprint.Analytic.mellin _ _‖ :=
        norm_sum_le _ _
    _ = ((Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊).card : ℝ) := by
        have h : ∀ n : ℕ, n ∈ Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊ →
            ‖(1 : ℂ) * Blueprint.Analytic.mellin (n : ℝ) z‖ = 1 := by
          intro n _
          rw [one_mul, norm_mellin_nat]
        rw [Finset.sum_congr rfl (fun n hn => h n hn)]
        simp [Finset.sum_const, nsmul_eq_mul]

lemma card_le_succ (U : ℝ) (hU : 1 ≤ U) :
    ((Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊).card : ℝ) ≤ U + 1 := by
  have h0U : (0 : ℝ) ≤ U := by linarith
  have hfloor : ((⌊2 * U⌋₊ : ℕ) : ℝ) ≤ 2 * U := Nat.floor_le (by positivity)
  have hceil : U ≤ ((⌈U⌉₊ : ℕ) : ℝ) := Nat.le_ceil U
  have hcard : (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊).card = ⌊2 * U⌋₊ + 1 - ⌈U⌉₊ :=
    Nat.card_Icc _ _
  by_cases hle : ⌈U⌉₊ ≤ ⌊2 * U⌋₊
  · rw [hcard]
    have hcast : (((⌊2 * U⌋₊ + 1 - ⌈U⌉₊ : ℕ)) : ℝ) =
        ((⌊2 * U⌋₊ : ℝ)) + 1 - ((⌈U⌉₊ : ℝ)) := by
      rw [Nat.cast_sub (by omega : ⌈U⌉₊ ≤ ⌊2 * U⌋₊ + 1)]
      push_cast
      ring
    rw [hcast]
    linarith
  · have hle' : ⌊2 * U⌋₊ + 1 ≤ ⌈U⌉₊ := by omega
    rw [hcard, Nat.sub_eq_zero_of_le hle']
    simp
    linarith

lemma differentiableOn_phase (z U : ℝ) (hU : 1 ≤ U) :
    DifferentiableOn ℝ (phase z) (Set.Icc U (2 * U)) := by
  have hsub : Set.Icc U (2 * U) ⊆ {0}ᶜ := by
    intro y hy
    simp only [Set.mem_Icc] at hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  have hlog : DifferentiableOn ℝ Real.log (Set.Icc U (2 * U)) :=
    Real.differentiableOn_log.mono hsub
  have hphase : phase z = fun v => (z / (2 * Real.pi)) * Real.log v := by
    funext v; unfold phase; ring
  rw [hphase]
  exact hlog.const_mul _

lemma contDiffOn_phase (z U : ℝ) (hU : 1 ≤ U) :
    ContDiffOn ℝ 2 (phase z) (Set.Icc U (2 * U)) := by
  have hsub : Set.Icc U (2 * U) ⊆ {0}ᶜ := by
    intro y hy
    simp only [Set.mem_Icc] at hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  have hlog : ContDiffOn ℝ (2 : ℕ) Real.log (Set.Icc U (2 * U)) :=
    Real.contDiffOn_log.mono hsub
  have hphase : phase z = fun v => (z / (2 * Real.pi)) * Real.log v := by
    funext v; unfold phase; ring
  rw [hphase]
  exact (contDiffOn_const).mul hlog

lemma antitoneOn_deriv_phase_of_nonneg (z U : ℝ) (hz : 0 ≤ z) (hU : 1 ≤ U) :
    AntitoneOn (deriv (phase z)) (Set.Icc U (2 * U)) := by
  rw [deriv_phase_eq]
  intro a ha b hb hab
  simp only [Set.mem_Icc] at ha hb
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hinv : b⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hb0 ha0).mpr hab
  have hC : (0 : ℝ) ≤ z / (2 * Real.pi) := by
    apply div_nonneg hz
    linarith [Real.pi_pos]
  exact mul_le_mul_of_nonneg_left hinv hC

lemma monotoneOn_deriv_phase_of_nonpos (z U : ℝ) (hz : z ≤ 0) (hU : 1 ≤ U) :
    MonotoneOn (deriv (phase z)) (Set.Icc U (2 * U)) := by
  rw [deriv_phase_eq]
  intro a ha b hb hab
  simp only [Set.mem_Icc] at ha hb
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hinv : b⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hb0 ha0).mpr hab
  have hC : z / (2 * Real.pi) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg hz
    linarith [Real.pi_pos]
  exact mul_le_mul_of_nonpos_left hinv hC

lemma abs_deriv_phase (z y : ℝ) (hy : 0 < y) :
    |deriv (phase z) y| = (|z| / (2 * Real.pi)) * y⁻¹ := by
  rw [deriv_phase_apply, abs_mul]
  congr 1
  · rw [abs_div]
    have hpi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
    rw [abs_of_pos hpi]
  · rw [abs_of_pos (inv_pos.mpr hy)]

lemma abs_iter2_phase (z y : ℝ) (hy : 0 < y) :
    |iteratedDeriv 2 (phase z) y| = (|z| / (2 * Real.pi)) * ((y ^ 2)⁻¹) := by
  rw [iteratedDeriv2_phase_apply, abs_mul]
  congr 1
  · rw [abs_div]
    have hpi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
    rw [abs_of_pos hpi]
  · rw [abs_neg, abs_inv]
    have hy2 : (0 : ℝ) < y ^ 2 := by positivity
    rw [abs_of_pos hy2]

lemma lam1_pos (z U : ℝ) (hz : 0 < |z|) (hU : 0 < U) :
    (0 : ℝ) < |z| / (4 * Real.pi * U) := by
  apply div_pos hz
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

lemma lam1_le_half (z U : ℝ) (hU : 1 ≤ U) (hzU : |z| ≤ U) :
    |z| / (4 * Real.pi * U) ≤ 1 / 2 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hU0 : (0 : ℝ) < U := by linarith
  have h4piU : (0 : ℝ) < 4 * Real.pi * U := by
    have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  rw [div_le_iff₀ h4piU]
  nlinarith [abs_nonneg z, hzU, hpi, hU0, Real.pi_pos]

lemma three_lam1_le_one (z U : ℝ) (hU : 1 ≤ U) (hzU : |z| ≤ U) :
    3 * (|z| / (4 * Real.pi * U)) ≤ 1 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hU0 : (0 : ℝ) < U := by linarith
  have h4piU : (0 : ℝ) < 4 * Real.pi * U := by
    have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  have h1 : 3 * (|z| / (4 * Real.pi * U)) = (3 * |z|) / (4 * Real.pi * U) := by ring
  rw [h1, div_le_one h4piU]
  nlinarith [abs_nonneg z, hzU, hpi, hU0, Real.pi_pos]

lemma first_abs_lower (z U y : ℝ) (hU : 1 ≤ U) (hy : y ∈ Set.Icc U (2 * U)) :
    |z| / (4 * Real.pi * U) ≤ (|z| / (2 * Real.pi)) * y⁻¹ := by
  simp only [Set.mem_Icc] at hy
  obtain ⟨hUy, hyU⟩ := hy
  have hU0 : (0 : ℝ) < U := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have h2U0 : (0 : ℝ) < 2 * U := by linarith
  have hC0 : (0 : ℝ) ≤ |z| / (2 * Real.pi) := by
    apply div_nonneg (abs_nonneg _)
    linarith [Real.pi_pos]
  have hinv : (2 * U)⁻¹ ≤ y⁻¹ := (inv_le_inv₀ h2U0 hy0).mpr hyU
  have hle : (|z| / (2 * Real.pi)) * (2 * U)⁻¹ ≤ (|z| / (2 * Real.pi)) * y⁻¹ :=
    mul_le_mul_of_nonneg_left hinv hC0
  have heq : (|z| / (2 * Real.pi)) * (2 * U)⁻¹ = |z| / (4 * Real.pi * U) := by
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have hU' : U ≠ 0 := ne_of_gt hU0
    field_simp
    ring
  rw [heq] at hle
  exact hle

lemma first_abs_upper (z U y : ℝ) (hU : 1 ≤ U) (hzU : |z| ≤ U)
    (hy : y ∈ Set.Icc U (2 * U)) :
    (|z| / (2 * Real.pi)) * y⁻¹ ≤ 1 - |z| / (4 * Real.pi * U) := by
  simp only [Set.mem_Icc] at hy
  obtain ⟨hUy, hyU⟩ := hy
  have hU0 : (0 : ℝ) < U := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hC0 : (0 : ℝ) ≤ |z| / (2 * Real.pi) := by
    apply div_nonneg (abs_nonneg _)
    linarith [Real.pi_pos]
  have hinv : y⁻¹ ≤ U⁻¹ := (inv_le_inv₀ hy0 hU0).mpr hUy
  have hle : (|z| / (2 * Real.pi)) * y⁻¹ ≤ (|z| / (2 * Real.pi)) * U⁻¹ :=
    mul_le_mul_of_nonneg_left hinv hC0
  have heq : (|z| / (2 * Real.pi)) * U⁻¹ = 2 * (|z| / (4 * Real.pi * U)) := by
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have hU' : U ≠ 0 := ne_of_gt hU0
    field_simp
    ring
  rw [heq] at hle
  have h3 : 3 * (|z| / (4 * Real.pi * U)) ≤ 1 := three_lam1_le_one z U hU hzU
  linarith

lemma lam2_pos (z U : ℝ) (hz : 0 < |z|) (hU : 0 < U) :
    (0 : ℝ) < |z| / (8 * Real.pi * U ^ 2) := by
  apply div_pos hz
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

lemma second_abs_bounds (z U y : ℝ) (hU : 1 ≤ U) (hy : y ∈ Set.Icc U (2 * U)) :
    |z| / (8 * Real.pi * U ^ 2) ≤ (|z| / (2 * Real.pi)) * ((y ^ 2)⁻¹) ∧
      (|z| / (2 * Real.pi)) * ((y ^ 2)⁻¹) ≤ 4 * (|z| / (8 * Real.pi * U ^ 2)) := by
  simp only [Set.mem_Icc] at hy
  obtain ⟨hUy, hyU⟩ := hy
  have hU0 : (0 : ℝ) < U := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hy20 : (0 : ℝ) < y ^ 2 := by positivity
  have hU20 : (0 : ℝ) < U ^ 2 := by positivity
  have h4U20 : (0 : ℝ) < 4 * U ^ 2 := by positivity
  have hC0 : (0 : ℝ) ≤ |z| / (2 * Real.pi) := by
    apply div_nonneg (abs_nonneg _)
    linarith [Real.pi_pos]
  have hy2_lo : U ^ 2 ≤ y ^ 2 := by
    exact pow_le_pow_left₀ (by linarith) hUy 2
  have hy2_hi : y ^ 2 ≤ (2 * U) ^ 2 := by
    exact pow_le_pow_left₀ (by linarith) hyU 2
  have h4U_eq : (2 * U) ^ 2 = 4 * U ^ 2 := by ring
  rw [h4U_eq] at hy2_hi
  have hinv_lo : (4 * U ^ 2)⁻¹ ≤ ((y ^ 2))⁻¹ := (inv_le_inv₀ h4U20 hy20).mpr hy2_hi
  have hinv_hi : ((y ^ 2))⁻¹ ≤ (U ^ 2)⁻¹ := (inv_le_inv₀ hy20 hU20).mpr hy2_lo
  constructor
  · have hle : (|z| / (2 * Real.pi)) * (4 * U ^ 2)⁻¹ ≤
        (|z| / (2 * Real.pi)) * ((y ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hinv_lo hC0
    have heq : (|z| / (2 * Real.pi)) * (4 * U ^ 2)⁻¹ = |z| / (8 * Real.pi * U ^ 2) := by
      have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
      have hU' : U ≠ 0 := ne_of_gt hU0
      field_simp
      ring
    rw [heq] at hle
    exact hle
  · have hle : (|z| / (2 * Real.pi)) * ((y ^ 2)⁻¹) ≤
        (|z| / (2 * Real.pi)) * (U ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv_hi hC0
    have heq : (|z| / (2 * Real.pi)) * (U ^ 2)⁻¹ = 4 * (|z| / (8 * Real.pi * U ^ 2)) := by
      have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
      have hU' : U ≠ 0 := ne_of_gt hU0
      field_simp
      ring
    rw [heq] at hle
    exact hle

lemma toNat_cast (m : ℤ) (hm : 0 ≤ m) : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
  have h : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
  have hR : ((((m.toNat : ℕ) : ℤ)) : ℝ) = (m : ℝ) := by rw [h]
  have hC : ((((m.toNat : ℕ) : ℤ)) : ℝ) = ((m.toNat : ℕ) : ℝ) :=
    Int.cast_natCast _
  rw [← hC] at *
  exact hR

lemma ceil_nonneg (U : ℝ) (hU : 1 ≤ U) : (0 : ℤ) ≤ ⌈U⌉ := by
  have hle : (U : ℝ) ≤ ((⌈U⌉ : ℤ) : ℝ) := Int.le_ceil U
  have h1 : (1 : ℝ) ≤ ((⌈U⌉ : ℤ) : ℝ) := le_trans hU hle
  have h0 : (0 : ℝ) < ((⌈U⌉ : ℤ) : ℝ) := lt_of_lt_of_le (by norm_num) h1
  exact le_of_lt (Int.cast_pos.mp h0)

lemma floor_nonneg (U : ℝ) (hU : 1 ≤ U) : (0 : ℤ) ≤ ⌊2 * U⌋ := by
  have hlt : (2 * U - 1 : ℝ) < ((⌊2 * U⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor _
  have h0 : (0 : ℝ) < (((⌊2 * U⌋ : ℤ)) : ℝ) := by linarith
  exact le_of_lt (Int.cast_pos.mp h0)

lemma image_eq (U : ℝ) (hU : 1 ≤ U) :
    Finset.image Int.toNat (Finset.Icc ⌈U⌉ ⌊2 * U⌋) =
      Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊ := by
  have ha0 : (0 : ℤ) ≤ ⌈U⌉ := ceil_nonneg U hU
  have hb0 : (0 : ℤ) ≤ ⌊2 * U⌋ := floor_nonneg U hU
  have ha_eq : (⌈U⌉).toNat = ⌈U⌉₊ := Int.ceil_toNat U
  have hb_eq : (⌊2 * U⌋).toNat = ⌊2 * U⌋₊ := Int.floor_toNat _
  apply Finset.ext
  intro x
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨m, ⟨ham, hmb⟩, rfl⟩
    rw [← ha_eq, ← hb_eq]
    exact ⟨Int.toNat_le_toNat ham, Int.toNat_le_toNat hmb⟩
  · intro hx
    obtain ⟨hax, hxb⟩ := hx
    rw [← ha_eq] at hax
    rw [← hb_eq] at hxb
    refine ⟨(x : ℤ), ⟨?_, ?_⟩, Int.toNat_natCast x⟩
    · rw [Int.toNat_le] at hax
      exact hax
    · have hxb' : x ≤ (⌊2 * U⌋).toNat := hxb
      rw [Int.le_toNat hb0] at hxb'
      exact hxb'

lemma sum_eq (U z : ℝ) (hU : 1 ≤ U) :
    (∑ n ∈ Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊, Blueprint.Analytic.e (phase z (n : ℝ))) =
      ∑ m ∈ Finset.Icc ⌈U⌉ ⌊2 * U⌋, Blueprint.Analytic.e (phase z (m : ℝ)) := by
  have ha0 : (0 : ℤ) ≤ ⌈U⌉ := ceil_nonneg U hU
  have him : Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊ =
      Finset.image Int.toNat (Finset.Icc ⌈U⌉ ⌊2 * U⌋) := (image_eq U hU).symm
  rw [him, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.mem_Icc] at hm
    obtain ⟨ham, _⟩ := hm
    have hm0 : (0 : ℤ) ≤ m := le_trans ha0 ham
    have hcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := toNat_cast m hm0
    rw [hcast]
  · intro x hx y hy hxy
    simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
    obtain ⟨hax, _⟩ := hx
    obtain ⟨hay, _⟩ := hy
    have hx0 : (0 : ℤ) ≤ x := le_trans ha0 hax
    have hy0 : (0 : ℤ) ≤ y := le_trans ha0 hay
    have hx_eq : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx0
    have hy_eq : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy0
    have h : ((x.toNat : ℕ) : ℤ) = ((y.toNat : ℕ) : ℤ) := by rw [hxy]
    rw [hx_eq, hy_eq] at h
    exact h

lemma first_pos_apply (K1 : ℝ) (hK1 : ∀ (lo hi lam : ℝ) (j : ℤ) (f : ℝ → ℝ),
      lo ≤ hi → 0 < lam → lam ≤ 1 / 2 → DifferentiableOn ℝ f (Set.Icc lo hi) →
      (MonotoneOn (deriv f) (Set.Icc lo hi) ∨ AntitoneOn (deriv f) (Set.Icc lo hi)) →
      (∀ y ∈ Set.Icc lo hi, j + lam ≤ deriv f y ∧ deriv f y ≤ j + 1 - lam) →
      ‖∑ n ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, Blueprint.Analytic.e (f n)‖ ≤ K1 / lam)
    (_Y U z : ℝ) (hU : 1 ≤ U) (hz1 : 1 ≤ z) (hzU : z ≤ U) :
    ‖Blueprint.Analytic.dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) z‖ ≤
      K1 / (|z| / (4 * Real.pi * U)) := by
  have hz0 : (0 : ℝ) ≤ z := by linarith
  have hz_abs : |z| = z := abs_of_nonneg hz0
  have hU0 : (0 : ℝ) < U := by linarith
  have hzU_abs : |z| ≤ U := by rw [hz_abs]; exact hzU
  have hz_pos_abs : (0 : ℝ) < |z| := by rw [hz_abs]; linarith
  have hlam_pos : (0 : ℝ) < |z| / (4 * Real.pi * U) := lam1_pos z U hz_pos_abs hU0
  have hlam_half : |z| / (4 * Real.pi * U) ≤ 1 / 2 := lam1_le_half z U hU hzU_abs
  have hlohi : U ≤ 2 * U := by linarith
  have hdiff : DifferentiableOn ℝ (phase z) (Set.Icc U (2 * U)) :=
    differentiableOn_phase z U hU
  have hmono : (MonotoneOn (deriv (phase z)) (Set.Icc U (2 * U)) ∨
      AntitoneOn (deriv (phase z)) (Set.Icc U (2 * U))) :=
    Or.inr (antitoneOn_deriv_phase_of_nonneg z U hz0 hU)
  have hbds : ∀ y ∈ Set.Icc U (2 * U),
      (0 : ℤ) + |z| / (4 * Real.pi * U) ≤ deriv (phase z) y ∧
        deriv (phase z) y ≤ (0 : ℤ) + 1 - |z| / (4 * Real.pi * U) := by
    intro y hy
    have hlow : |z| / (4 * Real.pi * U) ≤ (|z| / (2 * Real.pi)) * y⁻¹ :=
      first_abs_lower z U y hU hy
    have hhigh : (|z| / (2 * Real.pi)) * y⁻¹ ≤ 1 - |z| / (4 * Real.pi * U) :=
      first_abs_upper z U y hU hzU_abs hy
    have hderiv_eq : deriv (phase z) y = (|z| / (2 * Real.pi)) * y⁻¹ := by
      rw [deriv_phase_apply, hz_abs]
    rw [hderiv_eq]
    constructor
    · simpa using hlow
    · simpa using hhigh
  have hbound := hK1 U (2 * U) (|z| / (4 * Real.pi * U)) 0 (phase z)
    hlohi hlam_pos hlam_half hdiff hmono hbds
  have hdp_eq : Blueprint.Analytic.dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) z =
      ∑ m ∈ Finset.Icc ⌈U⌉ ⌊2 * U⌋, Blueprint.Analytic.e (phase z (m : ℝ)) := by
    rw [dp_eq_phase_sum, sum_eq U z hU]
  rw [hdp_eq]
  exact hbound

lemma first_neg_apply (K1 : ℝ) (hK1 : ∀ (lo hi lam : ℝ) (j : ℤ) (f : ℝ → ℝ),
      lo ≤ hi → 0 < lam → lam ≤ 1 / 2 → DifferentiableOn ℝ f (Set.Icc lo hi) →
      (MonotoneOn (deriv f) (Set.Icc lo hi) ∨ AntitoneOn (deriv f) (Set.Icc lo hi)) →
      (∀ y ∈ Set.Icc lo hi, j + lam ≤ deriv f y ∧ deriv f y ≤ j + 1 - lam) →
      ‖∑ n ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, Blueprint.Analytic.e (f n)‖ ≤ K1 / lam)
    (_Y U z : ℝ) (hU : 1 ≤ U) (hz1 : z ≤ -1) (hzU : -U ≤ z) :
    ‖Blueprint.Analytic.dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) z‖ ≤
      K1 / (|z| / (4 * Real.pi * U)) := by
  have hz0 : z ≤ (0 : ℝ) := by linarith
  have hz_abs : |z| = -z := abs_of_nonpos hz0
  have hU0 : (0 : ℝ) < U := by linarith
  have hzU_abs : |z| ≤ U := by rw [hz_abs]; linarith
  have hz_pos_abs : (0 : ℝ) < |z| := by rw [hz_abs]; linarith
  have hlam_pos : (0 : ℝ) < |z| / (4 * Real.pi * U) := lam1_pos z U hz_pos_abs hU0
  have hlam_half : |z| / (4 * Real.pi * U) ≤ 1 / 2 := lam1_le_half z U hU hzU_abs
  have hlohi : U ≤ 2 * U := by linarith
  have hdiff : DifferentiableOn ℝ (phase z) (Set.Icc U (2 * U)) :=
    differentiableOn_phase z U hU
  have hmono : (MonotoneOn (deriv (phase z)) (Set.Icc U (2 * U)) ∨
      AntitoneOn (deriv (phase z)) (Set.Icc U (2 * U))) :=
    Or.inl (monotoneOn_deriv_phase_of_nonpos z U hz0 hU)
  have hbds : ∀ y ∈ Set.Icc U (2 * U),
      (-1 : ℤ) + |z| / (4 * Real.pi * U) ≤ deriv (phase z) y ∧
        deriv (phase z) y ≤ (-1 : ℤ) + 1 - |z| / (4 * Real.pi * U) := by
    intro y hy
    have hlow : |z| / (4 * Real.pi * U) ≤ (|z| / (2 * Real.pi)) * y⁻¹ :=
      first_abs_lower z U y hU hy
    have hhigh : (|z| / (2 * Real.pi)) * y⁻¹ ≤ 1 - |z| / (4 * Real.pi * U) :=
      first_abs_upper z U y hU hzU_abs hy
    have hy_mem : y ∈ Set.Icc U (2 * U) := hy
    simp only [Set.mem_Icc] at hy_mem
    obtain ⟨hUy, _⟩ := hy_mem
    have hy0 : (0 : ℝ) < y := by linarith
    have hderiv_abs : |deriv (phase z) y| = (|z| / (2 * Real.pi)) * y⁻¹ :=
      abs_deriv_phase z y hy0
    have hderiv_nonpos : deriv (phase z) y ≤ 0 := by
      rw [deriv_phase_apply]
      apply mul_nonpos_of_nonpos_of_nonneg
      · apply div_nonpos_of_nonpos_of_nonneg hz0
        linarith [Real.pi_pos]
      · exact inv_nonneg.mpr hy0.le
    have hderiv_eq : deriv (phase z) y = -(((|z| / (2 * Real.pi)) * y⁻¹)) := by
      have h := abs_of_nonpos hderiv_nonpos
      rw [hderiv_abs] at h
      linarith
    rw [hderiv_eq]
    constructor
    · simp only [Int.cast_neg, Int.cast_one]
      linarith
    · simp only [Int.cast_neg, Int.cast_one]
      linarith
  have hbound := hK1 U (2 * U) (|z| / (4 * Real.pi * U)) (-1) (phase z)
    hlohi hlam_pos hlam_half hdiff hmono hbds
  have hdp_eq : Blueprint.Analytic.dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) z =
      ∑ m ∈ Finset.Icc ⌈U⌉ ⌊2 * U⌋, Blueprint.Analytic.e (phase z (m : ℝ)) := by
    rw [dp_eq_phase_sum, sum_eq U z hU]
  rw [hdp_eq]
  exact hbound

lemma second_apply (K2 : ℝ) (hK2 : ∀ (lo hi lam : ℝ) (f : ℝ → ℝ),
      lo ≤ hi → 0 < lam → ContDiffOn ℝ 2 f (Set.Icc lo hi) →
      (∀ y ∈ Set.Icc lo hi, lam ≤ |iteratedDeriv 2 f y| ∧
        |iteratedDeriv 2 f y| ≤ 4 * lam) →
      ‖∑ n ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, Blueprint.Analytic.e (f n)‖ ≤
        K2 * ((hi - lo + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹))
    (_Y U z : ℝ) (hU : 1 ≤ U) (hzU : U < |z|) :
    ‖Blueprint.Analytic.dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) z‖ ≤
      K2 * ((U + 1) * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) +
        (Real.sqrt (|z| / (8 * Real.pi * U ^ 2)))⁻¹) := by
  have hU0 : (0 : ℝ) < U := by linarith
  have hz_pos : (0 : ℝ) < |z| := lt_trans hU0 hzU
  have hlam_pos : (0 : ℝ) < |z| / (8 * Real.pi * U ^ 2) :=
    lam2_pos z U hz_pos hU0
  have hlohi : U ≤ 2 * U := by linarith
  have hcont : ContDiffOn ℝ 2 (phase z) (Set.Icc U (2 * U)) :=
    contDiffOn_phase z U hU
  have hbds : ∀ y ∈ Set.Icc U (2 * U),
      |z| / (8 * Real.pi * U ^ 2) ≤ |iteratedDeriv 2 (phase z) y| ∧
        |iteratedDeriv 2 (phase z) y| ≤ 4 * (|z| / (8 * Real.pi * U ^ 2)) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := by
      simp only [Set.mem_Icc] at hy
      linarith
    have habs : |iteratedDeriv 2 (phase z) y| = (|z| / (2 * Real.pi)) * ((y ^ 2)⁻¹) :=
      abs_iter2_phase z y hy0
    rw [habs]
    exact second_abs_bounds z U y hU hy
  have hbound := hK2 U (2 * U) (|z| / (8 * Real.pi * U ^ 2)) (phase z)
    hlohi hlam_pos hcont hbds
  have hdp_eq : Blueprint.Analytic.dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) z =
      ∑ m ∈ Finset.Icc ⌈U⌉ ⌊2 * U⌋, Blueprint.Analytic.e (phase z (m : ℝ)) := by
    rw [dp_eq_phase_sum, sum_eq U z hU]
  rw [hdp_eq]
  have hhi : (2 * U - U + 1 : ℝ) = U + 1 := by ring
  simpa [hhi] using hbound

lemma U_mul_sqrt_lam (U z : ℝ) (hU : 0 < U) (hz : 0 ≤ |z|) :
    U * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) = Real.sqrt (|z| / (8 * Real.pi)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h8pi : (0 : ℝ) < 8 * Real.pi := by positivity
  have hU2 : (0 : ℝ) < U ^ 2 := by positivity
  have h1 : |z| / (8 * Real.pi * U ^ 2) = (|z| / (8 * Real.pi)) / (U ^ 2) := by
    rw [div_mul_eq_div_div]
  rw [h1, Real.sqrt_div (div_nonneg hz (le_of_lt h8pi)) _,
    Real.sqrt_sq hU.le, mul_comm, div_mul_cancel₀ _ (ne_of_gt hU)]

lemma first_final_le (K1 Y U z : ℝ) (hK1 : 0 < K1) (hU : 1 ≤ U)
    (hz1 : 1 ≤ |z|) :
    K1 / (|z| / (4 * Real.pi * U)) ≤ K1 * 8 * Real.pi * (U / (1 + |z|) + Real.sqrt Y) := by
  have hU0 : (0 : ℝ) < U := by linarith [hU]
  have hz0 : (0 : ℝ) < |z| := lt_of_lt_of_le (by norm_num) hz1
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h4piU : (0 : ℝ) < 4 * Real.pi * U := by positivity
  have h1pz : (0 : ℝ) < 1 + |z| := by positivity
  have hz_ne : |z| ≠ 0 := ne_of_gt hz0
  have hU_ne : U ≠ 0 := ne_of_gt hU0
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have h_eq : K1 / (|z| / (4 * Real.pi * U)) = K1 * 4 * Real.pi * U / |z| := by
    field_simp
  rw [h_eq]
  have h_one_div : (1 : ℝ) / |z| ≤ 2 / (1 + |z|) := by
    rw [div_le_div_iff₀ hz0 h1pz]
    linarith
  have hC_nonneg : (0 : ℝ) ≤ K1 * 4 * Real.pi * U := by positivity
  have h_step1 : K1 * 4 * Real.pi * U / |z| ≤ K1 * 4 * Real.pi * U * (2 / (1 + |z|)) := by
    have h1 : K1 * 4 * Real.pi * U / |z| = (K1 * 4 * Real.pi * U) * (1 / |z|) := by
      rw [div_eq_mul_one_div]
    have h2 : K1 * 4 * Real.pi * U * (2 / (1 + |z|)) =
        (K1 * 4 * Real.pi * U) * (2 / (1 + |z|)) := rfl
    rw [h1]
    exact mul_le_mul_of_nonneg_left h_one_div hC_nonneg
  have h_step2 : K1 * 4 * Real.pi * U * (2 / (1 + |z|)) =
      K1 * 8 * Real.pi * (U / (1 + |z|)) := by
    field_simp
    ring
  rw [h_step2] at h_step1
  have h_sqrt_nonneg : (0 : ℝ) ≤ Real.sqrt Y := Real.sqrt_nonneg _
  have hK8pi_nonneg : (0 : ℝ) ≤ K1 * 8 * Real.pi := by positivity
  have h_le_add : U / (1 + |z|) ≤ U / (1 + |z|) + Real.sqrt Y :=
    le_add_of_nonneg_right h_sqrt_nonneg
  have h_step3 : K1 * 8 * Real.pi * (U / (1 + |z|)) ≤
      K1 * 8 * Real.pi * (U / (1 + |z|) + Real.sqrt Y) :=
    mul_le_mul_of_nonneg_left h_le_add hK8pi_nonneg
  linarith

lemma succ_mul_sqrt_le (U Y z : ℝ) (hU : 1 ≤ U) (hUY : U ≤ Y) (hzY : |z| ≤ Y) :
    (U + 1) * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) ≤ 2 * Real.sqrt Y := by
  have hU0 : (0 : ℝ) < U := by linarith
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h8pi : (0 : ℝ) < 8 * Real.pi := by positivity
  have h8pi_ge : (1 : ℝ) ≤ 8 * Real.pi := by linarith
  have hU1 : U + 1 ≤ 2 * U := by linarith
  have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) :=
    Real.sqrt_nonneg _
  have hle1 : (U + 1) * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) ≤
      (2 * U) * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) :=
    mul_le_mul_of_nonneg_right hU1 hsqrt_nonneg
  have hU_mul : U * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) =
      Real.sqrt (|z| / (8 * Real.pi)) :=
    U_mul_sqrt_lam U z hU0 (abs_nonneg _)
  have h2U_eq : (2 * U) * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) =
      2 * Real.sqrt (|z| / (8 * Real.pi)) := by
    calc (2 * U) * Real.sqrt _ = 2 * (U * Real.sqrt _) := by ring
      _ = 2 * Real.sqrt (|z| / (8 * Real.pi)) := by rw [hU_mul]
  rw [h2U_eq] at hle1
  have hdiv_le : |z| / (8 * Real.pi) ≤ Y := by
    have h1 : |z| / (8 * Real.pi) ≤ Y / (8 * Real.pi) :=
      (div_le_div_iff_of_pos_right h8pi).mpr hzY
    have h2 : Y / (8 * Real.pi) ≤ Y :=
      div_le_self hY0 h8pi_ge
    linarith
  have hsqrt_le : Real.sqrt (|z| / (8 * Real.pi)) ≤ Real.sqrt Y :=
    Real.sqrt_le_sqrt hdiv_le
  have hle2 : 2 * Real.sqrt (|z| / (8 * Real.pi)) ≤ 2 * Real.sqrt Y :=
    mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)
  linarith

lemma inv_sqrt_le (U Y z : ℝ) (hU : 1 ≤ U) (hUY : U ≤ Y) (_hzY : |z| ≤ Y)
    (hzU : U < |z|) :
    (Real.sqrt (|z| / (8 * Real.pi * U ^ 2)))⁻¹ ≤
      Real.sqrt (8 * Real.pi) * Real.sqrt Y := by
  have hU0 : (0 : ℝ) < U := by linarith
  have hz0 : (0 : ℝ) < |z| := lt_trans hU0 hzU
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le hU0 hUY
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h8pi : (0 : ℝ) < 8 * Real.pi := by positivity
  have hsqrt_z_pos : (0 : ℝ) < Real.sqrt |z| := Real.sqrt_pos.mpr hz0
  have hU_div_le : U / Real.sqrt |z| ≤ Real.sqrt Y := by
    have hU_eq : U = Real.sqrt U * Real.sqrt U :=
      (Real.mul_self_sqrt hU0.le).symm
    have hdiv_eq : U / Real.sqrt |z| =
        Real.sqrt U * (Real.sqrt U / Real.sqrt |z|) := by
      conv_lhs => rw [hU_eq]
      rw [mul_div_assoc]
    rw [hdiv_eq]
    have hsqrt_div : Real.sqrt U / Real.sqrt |z| = Real.sqrt (U / |z|) := by
      rw [Real.sqrt_div hU0.le _]
    rw [hsqrt_div]
    have hUdiv_le_one : U / |z| ≤ 1 := by
      rw [div_le_one hz0]
      linarith
    have hsqrt_le_one : Real.sqrt (U / |z|) ≤ 1 := by
      have h1 : Real.sqrt (U / |z|) ≤ Real.sqrt 1 :=
        Real.sqrt_le_sqrt hUdiv_le_one
      rwa [Real.sqrt_one] at h1
    have hsqrtU_nonneg : (0 : ℝ) ≤ Real.sqrt U := Real.sqrt_nonneg _
    have hle1 : Real.sqrt U * Real.sqrt (U / |z|) ≤ Real.sqrt U * 1 :=
      mul_le_mul_of_nonneg_left hsqrt_le_one hsqrtU_nonneg
    rw [mul_one] at hle1
    have hle2 : Real.sqrt U ≤ Real.sqrt Y := Real.sqrt_le_sqrt hUY
    linarith
  have hsqrt_lam_eq : Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) =
      Real.sqrt |z| / (Real.sqrt (8 * Real.pi) * U) := by
    have h8pi_nonneg : (0 : ℝ) ≤ 8 * Real.pi := le_of_lt h8pi
    have hU2_nonneg : (0 : ℝ) ≤ U ^ 2 := by positivity
    have h1 : (8 : ℝ) * Real.pi * U ^ 2 = (8 * Real.pi) * (U ^ 2) := by ring
    rw [h1, Real.sqrt_div (abs_nonneg z) _,
      Real.sqrt_mul h8pi_nonneg _, Real.sqrt_sq hU0.le]
  have h_inv_eq : (Real.sqrt (|z| / (8 * Real.pi * U ^ 2)))⁻¹ =
      (Real.sqrt (8 * Real.pi) * U) / Real.sqrt |z| := by
    rw [hsqrt_lam_eq, inv_div]
  rw [h_inv_eq, mul_div_assoc]
  have h8pi_sqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (8 * Real.pi) := Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_left hU_div_le h8pi_sqrt_nonneg

lemma trivial_final_le (Y U z : ℝ) (hU : 1 ≤ U) (hUY : U ≤ Y) (hz : |z| < 1) :
    ‖Blueprint.Analytic.dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) z‖ ≤
      2 * (U / (1 + |z|) + Real.sqrt Y) := by
  have hcard := norm_dp_le_card U z
  have hcard_le := card_le_succ U hU
  have hY1 : (1 : ℝ) ≤ Y := le_trans hU hUY
  have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt Y := Real.one_le_sqrt.mpr hY1
  have hU0 : (0 : ℝ) < U := by linarith
  have h1pz_pos : (0 : ℝ) < 1 + |z| := by positivity
  have h1pz_le : 1 + |z| ≤ 2 := by
    have h := abs_nonneg z
    linarith
  have h_one_div : (1 : ℝ) / 2 ≤ 1 / (1 + |z|) :=
    one_div_le_one_div_of_le h1pz_pos h1pz_le
  have hU_div_ge : U / 2 ≤ U / (1 + |z|) := by
    have h1 : U / 2 = U * (1 / 2) := by rw [div_eq_mul_one_div]
    have h2 : U / (1 + |z|) = U * (1 / (1 + |z|)) := by rw [div_eq_mul_one_div]
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left h_one_div hU0.le
  have hU_le : U ≤ 2 * (U / (1 + |z|)) := by
    have h1 : 2 * (U / 2) = U := by field_simp
    have h2 : 2 * (U / 2) ≤ 2 * (U / (1 + |z|)) :=
      mul_le_mul_of_nonneg_left hU_div_ge (by norm_num)
    linarith
  have h1_le : (1 : ℝ) ≤ 2 * Real.sqrt Y := by linarith [Real.sqrt_nonneg Y]
  have hU1_le : U + 1 ≤ 2 * (U / (1 + |z|)) + 2 * Real.sqrt Y := by linarith
  have h2_eq : 2 * (U / (1 + |z|)) + 2 * Real.sqrt Y =
      2 * (U / (1 + |z|) + Real.sqrt Y) := by ring
  rw [h2_eq] at hU1_le
  linarith

lemma second_final_le (K2 Y U z : ℝ) (hK2 : 0 < K2) (hU : 1 ≤ U) (hUY : U ≤ Y)
    (hzY : |z| ≤ Y) (hzU : U < |z|) :
    K2 * ((U + 1) * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) +
      (Real.sqrt (|z| / (8 * Real.pi * U ^ 2)))⁻¹) ≤
      K2 * (2 + Real.sqrt (8 * Real.pi)) * (U / (1 + |z|) + Real.sqrt Y) := by
  have hU0 : (0 : ℝ) < U := by linarith
  have h1 : (U + 1) * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) ≤ 2 * Real.sqrt Y :=
    succ_mul_sqrt_le U Y z hU hUY hzY
  have h2 : (Real.sqrt (|z| / (8 * Real.pi * U ^ 2)))⁻¹ ≤
      Real.sqrt (8 * Real.pi) * Real.sqrt Y :=
    inv_sqrt_le U Y z hU hUY hzY hzU
  have hsum_le : (U + 1) * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) +
      (Real.sqrt (|z| / (8 * Real.pi * U ^ 2)))⁻¹ ≤
      (2 + Real.sqrt (8 * Real.pi)) * Real.sqrt Y := by
    have h3 : (U + 1) * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) +
        (Real.sqrt (|z| / (8 * Real.pi * U ^ 2)))⁻¹ ≤
        2 * Real.sqrt Y + Real.sqrt (8 * Real.pi) * Real.sqrt Y := by
      exact add_le_add h1 h2
    have h4 : 2 * Real.sqrt Y + Real.sqrt (8 * Real.pi) * Real.sqrt Y =
        (2 + Real.sqrt (8 * Real.pi)) * Real.sqrt Y := by ring
    linarith
  have hY_nonneg : (0 : ℝ) ≤ U / (1 + |z|) := by
    apply div_nonneg (le_of_lt hU0)
    positivity
  have hle_add : Real.sqrt Y ≤ U / (1 + |z|) + Real.sqrt Y :=
    le_add_of_nonneg_left hY_nonneg
  have hle_mul : (2 + Real.sqrt (8 * Real.pi)) * Real.sqrt Y ≤
      (2 + Real.sqrt (8 * Real.pi)) * (U / (1 + |z|) + Real.sqrt Y) := by
    apply mul_le_mul_of_nonneg_left hle_add
    positivity
  have hK2_nonneg : (0 : ℝ) ≤ K2 := le_of_lt hK2
  have h_le : (U + 1) * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) +
      (Real.sqrt (|z| / (8 * Real.pi * U ^ 2)))⁻¹ ≤
      (2 + Real.sqrt (8 * Real.pi)) * (U / (1 + |z|) + Real.sqrt Y) :=
    le_trans hsum_le hle_mul
  calc K2 * ((U + 1) * Real.sqrt (|z| / (8 * Real.pi * U ^ 2)) +
      (Real.sqrt (|z| / (8 * Real.pi * U ^ 2)))⁻¹) ≤
      K2 * ((2 + Real.sqrt (8 * Real.pi)) * (U / (1 + |z|) + Real.sqrt Y)) :=
        mul_le_mul_of_nonneg_left h_le hK2_nonneg
    _ = K2 * (2 + Real.sqrt (8 * Real.pi)) * (U / (1 + |z|) + Real.sqrt Y) := by ring

theorem SparseGramKernelTask_proof : SparseGramKernelTask := by
  intro hD
  obtain ⟨K1, hK1pos, hK1⟩ := hD.1
  obtain ⟨K2, hK2pos, hK2⟩ := hD.2 4 (by norm_num)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h8pi_sqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (8 * Real.pi) := Real.sqrt_nonneg _
  have hK1_8pi_pos : (0 : ℝ) < K1 * 8 * Real.pi := by positivity
  have hK2_2pi_pos : (0 : ℝ) < K2 * (2 + Real.sqrt (8 * Real.pi)) := by
    apply mul_pos hK2pos
    linarith
  let K := max (max 2 (K1 * 8 * Real.pi)) (K2 * (2 + Real.sqrt (8 * Real.pi)))
  have hK_pos : (0 : ℝ) < K := by
    unfold K
    apply lt_max_of_lt_left
    apply lt_max_of_lt_left
    norm_num
  refine ⟨K, hK_pos, fun Y U z hU hUY hzY => ?_⟩
  have hU0 : (0 : ℝ) < U := by linarith
  have hR_nonneg : (0 : ℝ) ≤ U / (1 + |z|) + Real.sqrt Y := by
    have h1 : (0 : ℝ) ≤ U / (1 + |z|) := by
      apply div_nonneg (le_of_lt hU0)
      positivity
    linarith [Real.sqrt_nonneg Y]
  have h2_le_K : (2 : ℝ) ≤ K := by
    unfold K
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hK1_le_K : K1 * 8 * Real.pi ≤ K := by
    unfold K
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hK2_le_K : K2 * (2 + Real.sqrt (8 * Real.pi)) ≤ K := by
    unfold K
    exact le_max_right _ _
  by_cases h_triv : |z| < 1
  · have hbound := trivial_final_le Y U z hU hUY h_triv
    calc ‖Blueprint.Analytic.dp _ _ _‖ ≤ 2 * (U / (1 + |z|) + Real.sqrt Y) := hbound
      _ ≤ K * (U / (1 + |z|) + Real.sqrt Y) :=
        mul_le_mul_of_nonneg_right h2_le_K hR_nonneg
  · push Not at h_triv
    have h1_le : (1 : ℝ) ≤ |z| := h_triv
    by_cases h_first : |z| ≤ U
    · rcases le_total 0 z with hz_nonneg | hz_nonpos
      · have hz_abs : |z| = z := abs_of_nonneg hz_nonneg
        have hz1 : (1 : ℝ) ≤ z := by rw [← hz_abs]; exact h1_le
        have hzU : z ≤ U := by rw [← hz_abs]; exact h_first
        have hbound1 := first_pos_apply K1 hK1 Y U z hU hz1 hzU
        have hbound2 := first_final_le K1 Y U z hK1pos hU h1_le
        have hbound : ‖Blueprint.Analytic.dp _ _ _‖ ≤
            K1 * 8 * Real.pi * (U / (1 + |z|) + Real.sqrt Y) :=
          le_trans hbound1 hbound2
        calc ‖Blueprint.Analytic.dp _ _ _‖ ≤ _ := hbound
          _ ≤ K * _ := mul_le_mul_of_nonneg_right hK1_le_K hR_nonneg
      · have hz_abs : |z| = -z := abs_of_nonpos hz_nonpos
        have hz1 : z ≤ (-1 : ℝ) := by
          have h : (1 : ℝ) ≤ -z := by rw [← hz_abs]; exact h1_le
          linarith
        have hzU : -U ≤ z := by
          have h : -z ≤ U := by rw [← hz_abs]; exact h_first
          linarith
        have hbound1 := first_neg_apply K1 hK1 Y U z hU hz1 hzU
        have hbound2 := first_final_le K1 Y U z hK1pos hU h1_le
        have hbound : ‖Blueprint.Analytic.dp _ _ _‖ ≤
            K1 * 8 * Real.pi * (U / (1 + |z|) + Real.sqrt Y) :=
          le_trans hbound1 hbound2
        calc ‖Blueprint.Analytic.dp _ _ _‖ ≤ _ := hbound
          _ ≤ K * _ := mul_le_mul_of_nonneg_right hK1_le_K hR_nonneg
    · push Not at h_first
      have hzU : U < |z| := h_first
      have hbound1 := second_apply K2 hK2 Y U z hU hzU
      have hbound2 := second_final_le K2 Y U z hK2pos hU hUY hzY hzU
      have hbound : ‖Blueprint.Analytic.dp _ _ _‖ ≤
          K2 * (2 + Real.sqrt (8 * Real.pi)) * (U / (1 + |z|) + Real.sqrt Y) :=
        le_trans hbound1 hbound2
      calc ‖Blueprint.Analytic.dp _ _ _‖ ≤ _ := hbound
        _ ≤ K * _ := mul_le_mul_of_nonneg_right hK2_le_K hR_nonneg

end Erdos821.P5Gram
