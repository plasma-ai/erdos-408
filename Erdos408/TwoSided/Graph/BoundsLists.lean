module

public import Erdos408.TwoSided.Setup
public import Mathlib.Data.Int.CardIntervalMod

/-!
# Counting physical lists

The list counts behind Lemmas G1 and G2a of `blueprint/two_sided_correlation.md` §4.

* `#physicalLists(n) ≤ ∏_g ω_g(n)^M`.
* The labels of a physical list are distinct primes, so their product `Π(p)` divides `n`.
* Over an interval of length at most `Y + 1`,
  `∑_n #lists(n) ∏ V^{-M} ≤ ∑_p (Y/Π(p) + 2) ∏ V^{-M} = Y + 2 ∏_g (|P_g|/V_g)^M`, which is
  (6.12) plus a list count; eventually the list count is at most `√x / 2`.
-/

@[expose] public section

namespace Erdos408.TwoSided

namespace GraphBounds

open Filter Finset

/-- There are at most `(b - a)/d + 1` multiples of `d ≥ 1` in `[a, b)`. -/
private theorem card_filter_dvd_Ico_le {a b d : ℕ} (hd : 0 < d) (hab : a ≤ b) :
    (#{n ∈ Ico a b | d ∣ n} : ℝ) ≤ ((b : ℝ) - a) / d + 1 := by
  have hfilt : {n ∈ Ico a b | d ∣ n} = {n ∈ Ico a b | n ≡ 0 [MOD d]} :=
    filter_congr fun n _ => Nat.modEq_zero_iff_dvd.symm
  have h := Nat.Ico_filter_modEq_card a b hd 0
  rw [← hfilt] at h
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have key : ((#{n ∈ Ico a b | d ∣ n} : ℤ) : ℚ) ≤ ((b : ℚ) - a) / d + 1 := by
    rw [h]
    push_cast
    refine max_le ?_ ?_
    · have h₁ := Int.ceil_lt_add_one ((b : ℚ) / d)
      have h₂ := Int.le_ceil ((a : ℚ) / d)
      simp only [sub_zero]
      rw [sub_div]
      linarith
    · have : (0 : ℚ) ≤ ((b : ℚ) - a) / d :=
        div_nonneg (sub_nonneg.2 (by exact_mod_cast hab)) hd'.le
      linarith
  have key' : ((#{n ∈ Ico a b | d ∣ n} : ℕ) : ℚ) ≤ ((b : ℚ) - a) / d + 1 := by
    exact_mod_cast key
  have := (Rat.cast_le (K := ℝ)).2 key'
  push_cast at this
  exact this

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `#physicalLists(n) ≤ ∏_g ω_g(n)^M`. -/
theorem card_physicalLists_le (P : ι → Finset ℕ) (M n : ℕ) :
    #(physicalLists P M n) ≤ ∏ g, primeCount (P g) n ^ M := by
  calc #(physicalLists P M n)
      ≤ #(Fintype.piFinset fun g => Fintype.piFinset fun _ : Fin M => (P g).filter (· ∣ n)) := by
        refine card_le_card fun p hp => ?_
        obtain ⟨hp, hdvd⟩ := mem_filter.1 hp
        rw [Fintype.mem_piFinset] at hp ⊢
        intro g
        have hg := hp g
        rw [Fintype.mem_piFinset] at hg ⊢
        exact fun i => mem_filter.2 ⟨hg i, (hdvd g).2 i⟩
    _ = ∏ g, primeCount (P g) n ^ M := by
        simp [Fintype.card_piFinset, primeCount]

/-- The product `Π(p) = ∏_g ∏_i p_{g,i}` of the labels of a list. -/
def listProduct {M : ℕ} (p : ι → Fin M → ℕ) : ℕ :=
  ∏ g, ∏ i, p g i

/-- The labels of a physical list are distinct primes dividing `n`, so `Π(p) ∣ n`. -/
theorem listProduct_dvd {P : ι → Finset ℕ} (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h))
    (hprime : ∀ g, ∀ p ∈ P g, p.Prime) {M n : ℕ} {p : ι → Fin M → ℕ}
    (hp : p ∈ physicalLists P M n) : listProduct p ∣ n := by
  obtain ⟨hmem, hlist⟩ := mem_filter.1 hp
  have hmem' : ∀ g i, p g i ∈ P g := fun g i =>
    Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hmem g) i
  set e : ι × Fin M → ℕ := fun gi => p gi.1 gi.2
  have hinj : Set.InjOn e (univ : Finset (ι × Fin M)) := by
    rintro ⟨g, i⟩ - ⟨h, j⟩ - hgh
    simp only [e] at hgh
    by_cases hg : g = h
    · subst hg
      rw [(hlist g).1 hgh]
    · exact absurd (hmem' h j) (Finset.disjoint_left.1 (hdisj g h hg) (hgh ▸ hmem' g i))
  have heq : listProduct p = ∏ y ∈ univ.image e, y := by
    rw [prod_image hinj, listProduct, ← Fintype.prod_prod_type']
  rw [heq]
  refine Finset.prod_primes_dvd n (fun y hy => ?_) fun y hy => ?_
  · obtain ⟨⟨g, i⟩, -, rfl⟩ := mem_image.1 hy
    exact (hprime g _ (hmem' g i)).prime
  · obtain ⟨⟨g, i⟩, -, rfl⟩ := mem_image.1 hy
    exact (hlist g).2 i

/-- **The physical list sum.** Over `[a, b)` with `b - a ≤ Y + 1`,
`∑_n #lists(n) ∏_g V_g^{-M} ≤ Y + 2 ∏_g (|P_g| V_g⁻¹)^M`: each list `p` is counted at the
multiples of `Π(p)`, and `∑_p 1/Π(p) = ∏_g V_g^M`. -/
theorem sum_card_physicalLists_le {P : ι → Finset ℕ}
    (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h)) (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    (hV : ∀ g, 0 < harmonicMass (P g)) (M : ℕ) {a b : ℕ} (hab : a ≤ b) {Y : ℝ}
    (hba : (b : ℝ) - a ≤ Y + 1) :
    ∑ n ∈ Ico a b, (#(physicalLists P M n) : ℝ) * ∏ g, (harmonicMass (P g))⁻¹ ^ M ≤
      Y + 2 * ∏ g, ((#(P g) : ℝ) * (harmonicMass (P g))⁻¹) ^ M := by
  set U := Fintype.piFinset fun g => Fintype.piFinset fun _ : Fin M => P g
  set W := ∏ g, (harmonicMass (P g))⁻¹ ^ M
  have hW : 0 ≤ W := prod_nonneg fun g _ => pow_nonneg (inv_nonneg.2 (hV g).le) _
  have hmemU : ∀ p ∈ U, ∀ g i, p g i ∈ P g := fun p hp g i =>
    Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hp g) i
  have hpos : ∀ p ∈ U, 0 < listProduct p := fun p hp =>
    prod_pos fun g _ => prod_pos fun i _ => (hprime g _ (hmemU p hp g i)).pos
  -- each list is counted at the multiples of its product
  have hA : ∀ n, #(physicalLists P M n) ≤ #{p ∈ U | listProduct p ∣ n} := fun n =>
    card_le_card fun p hp => mem_filter.2 ⟨(mem_filter.1 hp).1, listProduct_dvd hdisj hprime hp⟩
  have hB : ∑ n ∈ Ico a b, (#{p ∈ U | listProduct p ∣ n} : ℝ) =
      ∑ p ∈ U, (#{n ∈ Ico a b | listProduct p ∣ n} : ℝ) := by
    simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact sum_comm
  have hC : ∀ p ∈ U, (#{n ∈ Ico a b | listProduct p ∣ n} : ℝ) ≤
      Y * ∏ g, ∏ i, ((p g i : ℝ))⁻¹ + 2 := by
    intro p hp
    have hprod : (1 : ℝ) ≤ listProduct p := by exact_mod_cast hpos p hp
    have h := card_filter_dvd_Ico_le (hpos p hp) hab
    have heq : ∏ g, ∏ i, ((p g i : ℝ))⁻¹ = ((listProduct p : ℕ) : ℝ)⁻¹ := by
      simp only [listProduct, Nat.cast_prod, prod_inv_distrib]
    rw [heq]
    have h₁ : ((b : ℝ) - a) / listProduct p ≤ (Y + 1) / listProduct p :=
      div_le_div_of_nonneg_right hba (by linarith)
    have h₂ : (1 : ℝ) / listProduct p ≤ 1 := by rw [div_le_one (by linarith)]; exact hprod
    rw [add_div] at h₁
    rw [← div_eq_mul_inv]
    linarith
  -- `∑_p 1/Π(p) = ∏_g V_g^M` and `#U = ∏_g |P_g|^M`
  have hD : ∑ p ∈ U, ∏ g, ∏ i, ((p g i : ℝ))⁻¹ = ∏ g, harmonicMass (P g) ^ M := by
    refine (prod_univ_sum (fun g => Fintype.piFinset fun _ : Fin M => P g)
      (fun g (pg : Fin M → ℕ) => ∏ i, ((pg i : ℝ))⁻¹)).symm.trans
      (prod_congr rfl fun g _ => ?_)
    rw [← prod_univ_sum (fun _ : Fin M => P g) (fun _ (p : ℕ) => ((p : ℝ))⁻¹), prod_const,
      card_univ, Fintype.card_fin, harmonicMass]
    simp only [one_div]
  have hE : (#U : ℝ) = ∏ g, (#(P g) : ℝ) ^ M := by
    simp [U, Fintype.card_piFinset]
  calc ∑ n ∈ Ico a b, (#(physicalLists P M n) : ℝ) * W
      ≤ ∑ n ∈ Ico a b, (#{p ∈ U | listProduct p ∣ n} : ℝ) * W :=
        sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hA n) hW
    _ = (∑ p ∈ U, (#{n ∈ Ico a b | listProduct p ∣ n} : ℝ)) * W := by rw [← sum_mul, hB]
    _ ≤ (∑ p ∈ U, (Y * ∏ g, ∏ i, ((p g i : ℝ))⁻¹ + 2)) * W :=
        mul_le_mul_of_nonneg_right (sum_le_sum hC) hW
    _ = Y * ((∏ g, harmonicMass (P g) ^ M) * W) + 2 * ((#U : ℝ) * W) := by
        rw [sum_add_distrib, ← mul_sum, hD, sum_const, nsmul_eq_mul]
        ring
    _ = Y + 2 * ∏ g, ((#(P g) : ℝ) * (harmonicMass (P g))⁻¹) ^ M := by
        rw [hE, ← prod_mul_distrib, ← prod_mul_distrib]
        simp only [← mul_pow, mul_inv_cancel₀ (hV _).ne', one_pow, prod_const_one, mul_one]

/-- **The physical norm on an interval.** If `‖f‖ ≤ B` on `[a, b)` with `b - a ≤ Y + 1`, then
`physicalNormSq P M [a, b) f ≤ B² (Y + 2 ∏_g (|P_g| V_g⁻¹)^M)`. -/
theorem physicalNormSq_Ico_le {P : ι → Finset ℕ} (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h))
    (hprime : ∀ g, ∀ p ∈ P g, p.Prime) (hV : ∀ g, 0 < harmonicMass (P g)) (M : ℕ) {a b : ℕ}
    (hab : a ≤ b) {Y : ℝ} (hba : (b : ℝ) - a ≤ Y + 1) {f : ℕ → ℂ} {B : ℝ}
    (hf : ∀ n ∈ Ico a b, ‖f n‖ ≤ B) :
    physicalNormSq P M (Ico a b) f ≤
      B ^ 2 * (Y + 2 * ∏ g, ((#(P g) : ℝ) * (harmonicMass (P g))⁻¹) ^ M) := by
  have hW : 0 ≤ ∏ g, (harmonicMass (P g))⁻¹ ^ M :=
    prod_nonneg fun g _ => pow_nonneg (inv_nonneg.2 (hV g).le) _
  calc physicalNormSq P M (Ico a b) f
      ≤ ∑ n ∈ Ico a b, B ^ 2 * ((#(physicalLists P M n) : ℝ) *
          ∏ g, (harmonicMass (P g))⁻¹ ^ M) := by
        refine sum_le_sum fun n hn => ?_
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)) hW
        exact pow_le_pow_left₀ (norm_nonneg _) (hf n hn) 2
    _ ≤ B ^ 2 * (Y + 2 * ∏ g, ((#(P g) : ℝ) * (harmonicMass (P g))⁻¹) ^ M) := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_card_physicalLists_le hdisj hprime hV M hab hba)
          (sq_nonneg _)

/-- A set of primes in `[lo, hi]` has at most `hi` elements. -/
private theorem card_le_of_subset_primesIcc {S : Finset ℕ} {lo hi : ℝ} (hhi : 0 ≤ hi)
    (hS : S ⊆ primesIcc lo hi) : (#S : ℝ) ≤ hi := by
  have hsub : S ⊆ Icc 1 ⌊hi⌋₊ := fun p hp => by
    obtain ⟨hp₁, hp₂⟩ := mem_filter.1 (hS hp)
    exact mem_Icc.2 ⟨hp₂.one_lt.le, (mem_Icc.1 hp₁).2⟩
  have := card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  exact (Nat.cast_le.2 this).trans (Nat.floor_le hhi)

/-- Eventually `2 ∏_g (|P_g| V_g⁻¹)^M ≤ √x` for groups as in (6.1): `|P_g| ≤ exp(L^{0.46})`,
`V_g ≥ v₋` and `s_P ≤ 2C₀T`, while `T L^{0.46} = o(L)`. -/
theorem eventually_two_mul_prod_card_le_sqrt (c₀ C₀ vlo vhi : ℝ) (hvlo : 0 < vlo) (M : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        2 * ∏ g, ((#(P g) : ℝ) * (harmonicMass (P g))⁻¹) ^ M ≤ √x := by
  set β := max 1 vlo⁻¹
  set C := max C₀ 0
  set K := M * (2 * C) * (1 + Real.log β)
  have hβ : 1 ≤ β := le_max_left _ _
  have hlogβ : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hK : 0 ≤ K := by positivity
  have hlog := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 0.04 by norm_num)).bound one_pos
  have hL := Real.tendsto_log_atTop
  filter_upwards [hL.eventually hlog, hL.eventually_ge_atTop 1,
    hL.eventually ((tendsto_rpow_atTop (show (0 : ℝ) < 0.5 by norm_num)).eventually_ge_atTop
      (2 * (K + 1))), eventually_gt_atTop 0]
    with x hlogL hL1 hL5 hx0 ι _ _ P big hP
  set L := Real.log x
  set T := Real.log L
  have hT0 : 0 ≤ T := Real.log_nonneg hL1
  have hL0 : 0 < L := by linarith
  have hT : T ≤ L ^ (0.04 : ℝ) := by
    rw [one_mul, Real.norm_of_nonneg hT0, Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _)]
      at hlogL
    exact hlogL
  -- `s_P ≤ 2 C T`
  have hs : (Fintype.card ι : ℝ) ≤ 2 * C * T := by
    have h := card_sdiff_add_card_eq_card (subset_univ big)
    rw [card_univ] at h
    have h₁ := hP.2.2.1
    have h₂ := hP.2.2.2.2.1
    have h₃ : C₀ * T ≤ C * T := mul_le_mul_of_nonneg_right (le_max_left _ _) hT0
    rw [← h]
    push_cast
    linarith
  -- each factor is at most `E = exp(L^{0.46}) β`
  set E := Real.exp (L ^ (0.46 : ℝ)) * β
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le
    (Real.one_le_exp (Real.rpow_nonneg hL0.le _)) hβ
  have hfac : ∀ g, (#(P g) : ℝ) * (harmonicMass (P g))⁻¹ ≤ E := by
    intro g
    have hV := (hP.2.2.2.2.2.1 g).1
    have hcard : (#(P g) : ℝ) ≤ Real.exp (L ^ (0.46 : ℝ)) := by
      by_cases hg : g ∈ big
      · exact card_le_of_subset_primesIcc (Real.exp_pos _).le (hP.2.2.2.2.2.2.2.1 g hg)
      · refine (card_le_of_subset_primesIcc (Real.exp_pos _).le
          (hP.2.2.2.2.2.2.1 g hg)).trans (Real.exp_le_exp.2 ?_)
        exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hinv : (harmonicMass (P g))⁻¹ ≤ β :=
      (inv_anti₀ hvlo hV).trans (le_max_right _ _)
    exact mul_le_mul hcard hinv (inv_nonneg.2 (hvlo.trans_le hV).le) (Real.exp_pos _).le
  have hprod : ∏ g, ((#(P g) : ℝ) * (harmonicMass (P g))⁻¹) ^ M ≤
      E ^ ((M : ℝ) * (2 * C * T)) := by
    calc ∏ g, ((#(P g) : ℝ) * (harmonicMass (P g))⁻¹) ^ M ≤ ∏ _g : ι, E ^ M :=
          prod_le_prod₀ (fun g _ => pow_nonneg (mul_nonneg (Nat.cast_nonneg _)
            (inv_nonneg.2 (hvlo.trans_le (hP.2.2.2.2.2.1 g).1).le)) _)
            fun g _ => pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _)
              (inv_nonneg.2 (hvlo.trans_le (hP.2.2.2.2.2.1 g).1).le)) (hfac g) _
      _ = E ^ (((M * Fintype.card ι : ℕ) : ℝ)) := by
          rw [prod_const, card_univ, ← pow_mul, Real.rpow_natCast]
      _ ≤ E ^ ((M : ℝ) * (2 * C * T)) := by
          refine Real.rpow_le_rpow_of_exponent_le hE1 ?_
          push_cast
          exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
  -- `log 2 + log E · M · 2CT ≤ L / 2`
  have hlogE : Real.log E = L ^ (0.46 : ℝ) + Real.log β := by
    rw [Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp]
  have h46 : 1 ≤ L ^ (0.46 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have h50 : L ^ (0.46 : ℝ) * L ^ (0.04 : ℝ) = L ^ (0.5 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hhalf : L ^ (0.5 : ℝ) * L ^ (0.5 : ℝ) = L := by
    rw [← Real.rpow_add hL0]
    norm_num
  have h5 : 1 ≤ L ^ (0.5 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hkey : Real.log 2 + Real.log E * ((M : ℝ) * (2 * C * T)) ≤ L / 2 := by
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hC : 0 ≤ C := le_max_right _ _
    have h₁ : Real.log E ≤ (1 + Real.log β) * L ^ (0.46 : ℝ) := by
      rw [hlogE]
      nlinarith
    have h₂ : Real.log E * ((M : ℝ) * (2 * C * T)) ≤ K * L ^ (0.5 : ℝ) := by
      have hMC : 0 ≤ (M : ℝ) * (2 * C) := by positivity
      calc Real.log E * ((M : ℝ) * (2 * C * T))
          ≤ (1 + Real.log β) * L ^ (0.46 : ℝ) * ((M : ℝ) * (2 * C) * L ^ (0.04 : ℝ)) := by
            rw [show (M : ℝ) * (2 * C * T) = (M : ℝ) * (2 * C) * T by ring]
            refine mul_le_mul h₁ (mul_le_mul_of_nonneg_left hT hMC) (by positivity)
              (by positivity)
        _ = K * (L ^ (0.46 : ℝ) * L ^ (0.04 : ℝ)) := by ring
        _ = K * L ^ (0.5 : ℝ) := by rw [h50]
    have h₃ : 2 * (K + 1) * L ^ (0.5 : ℝ) ≤ L := by
      calc 2 * (K + 1) * L ^ (0.5 : ℝ) ≤ L ^ (0.5 : ℝ) * L ^ (0.5 : ℝ) :=
            mul_le_mul_of_nonneg_right hL5 (by linarith)
        _ = L := hhalf
    nlinarith
  calc 2 * ∏ g, ((#(P g) : ℝ) * (harmonicMass (P g))⁻¹) ^ M
      ≤ Real.exp (Real.log 2) * Real.exp (Real.log E * ((M : ℝ) * (2 * C * T))) := by
        rw [Real.exp_log (by norm_num), ← Real.rpow_def_of_pos (by linarith)]
        exact mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ Real.exp (L / 2) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 hkey
    _ = √x := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
        congr 1
        ring

end GraphBounds

end Erdos408.TwoSided
