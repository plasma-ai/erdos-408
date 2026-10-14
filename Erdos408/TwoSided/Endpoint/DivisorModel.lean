import Erdos408.Extraction.Allocation.Groups
import Erdos408.TwoSided.Endpoint.DivisorModel.Lists

/-!
# The truncated divisor model

Lemma E1 of `blueprint/two_sided_correlation.md` §6.1 (PD Lemma 6.5, with the
`r ≤ K₀ + C_N s` inert bands of X5). The marks `H_m(n) = 𝒲(n) W_S^b(n)` have a model
`∑_{d ∣ n} A_d` with squarefree `d ≤ exp(2L^{0.47})` built from the active and band primes,
`∑ |A_d|/d ≤ L^{C₈}`, and mean-square error `C_N R L^{-N}` on every dyad `(R, 2R]`. One model
serves every scale, which S12 uses at the scales `Y/l` and `Y`.

The truncation of a general list form is in `DivisorModel/Truncation.lean`, and the list forms
of the two marked weights in `DivisorModel/Lists.lean`. Here `DivModel.divisorModel_of_facts`
assembles them under explicit size conditions, and `exists_divisorModel` checks the conditions
eventually, with `C₈ = 2|C₀||v₊| + 2`, `C_N = 1` and depth `h₀ = ⌊L^{0.01}⌋`.
-/

namespace Erdos408.TwoSided

open Filter

/-- `A` is a truncated divisor model of the marks `H(n) = 𝒲(n) W_S^b(n)` (PD Lemma 6.5):
(a) `A_d ≠ 0` only for squarefree `d ≤ exp(2L^{0.47})` whose primes are active or band
primes; (b) `∑_d |A_d|/d ≤ L^{C₈}`; (c) for every `R ≥ 1`,
`∑_{R < n ≤ 2R} |H(n) - ∑_{d ∣ n} A_d|² ≤ C_N R L^{-N}`. -/
def DivisorModel (x q q₀ : ℝ) {r : ℕ} (a : Fin r → ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) {M : ℕ} (S : ι → Finset (Fin M)) (b : (ι → Fin M → ℕ) → ℂ)
    (C₈ CN : ℝ) (N : ℕ) (A : ℕ → ℂ) : Prop :=
  (∀ d, A d ≠ 0 → Squarefree d ∧ (d : ℝ) ≤ Real.exp (2 * Real.log x ^ (0.47 : ℝ)) ∧
      ∀ p ∈ d.primeFactors, p ∈ Finset.univ.biUnion P ∨ ∃ i, p ∈ band x (a i)) ∧
    ∑ d ∈ Finset.Icc 1 ⌊Real.exp (2 * Real.log x ^ (0.47 : ℝ))⌋₊, ‖A d‖ / d ≤
      Real.log x ^ C₈ ∧
    ∀ R : ℝ, 1 ≤ R →
      ∑ n ∈ Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊,
          ‖(markedWeight Finset.univ q (fun i => band x (a i)) n : ℂ) *
              markedListWeight P q₀ S b n - ∑ d ∈ n.divisors, A d‖ ^ 2 ≤
        CN * R * Real.log x ^ (-(N : ℝ))


namespace DivModel

open Finset

/-- `‖t - 1‖ ≤ 1` for `0 < t < 1`. -/
theorem norm_ofReal_sub_one_le {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) : ‖(t : ℂ) - 1‖ ≤ 1 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg (by linarith)]
  linarith

/-- **E1 from the size facts.** For bands and groups that are disjoint, consist of primes
`≤ exp(L^{0.46})` and have the harmonic masses of (6.1) and U2, the truncated model of the
list form of `𝒲 W_S^b` at depth `h₀` is a divisor model, once the three numerical conditions
of steps 3, 4 and 6 hold. -/
theorem divisorModel_of_facts {x q q₀ vlo vhi : ℝ} (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀)
    (hq₀₁ : q₀ < 1) (hvlo : 0 < vlo) {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : ι → Finset ℕ} {r : ℕ} {a : Fin r → ℝ} {M : ℕ} {S : ι → Finset (Fin M)}
    {b : (ι → Fin M → ℕ) → ℂ} {m₀ : ℕ} (C₈ CNN : ℝ) (N h₀ : ℕ)
    (hL0 : 0 ≤ Real.log x) (hPd : ∀ g h, g ≠ h → Disjoint (P g) (P h))
    (hGd : ∀ i j, i ≠ j → Disjoint (band x (a i)) (band x (a j)))
    (hQd : Disjoint (univ.biUnion fun i => band x (a i)) (univ.biUnion P))
    (hprime : ∀ p ∈ (univ.biUnion fun i => band x (a i)) ∪ univ.biUnion P, p.Prime)
    (hsize : ∀ p ∈ (univ.biUnion fun i => band x (a i)) ∪ univ.biUnion P,
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.46 : ℝ)))
    (hVB : ∀ i, 1 / 2 ≤ harmonicMass (band x (a i)) ∧ harmonicMass (band x (a i)) ≤ 1)
    (hVP : ∀ g, vlo ≤ harmonicMass (P g) ∧ harmonicMass (P g) ≤ vhi)
    (hS : ∀ g, (S g).card ≤ m₀ + 1) (hb : ∀ p, ‖b p‖ ≤ 1)
    (hsupp : ((r + (m₀ + 1) * Fintype.card ι + h₀ : ℕ) : ℝ) * Real.log x ^ (0.46 : ℝ) ≤
      2 * Real.log x ^ (0.47 : ℝ))
    (hmass : Real.exp (r + Fintype.card ι * vhi) ≤ Real.log x ^ C₈)
    (hms : 2 * (2 ^ r * (max 1 vlo⁻¹) ^ ((m₀ + 1) * Fintype.card ι)) ^ 2 *
        Real.exp ((4 ^ (m₀ + 3) - 1) * (r + Fintype.card ι * vhi)) / 4 ^ h₀ ≤
      CNN * Real.log x ^ (-(N : ℝ))) :
    ∃ A : ℕ → ℂ, DivisorModel x q q₀ a P S b C₈ CNN N A := by
  set G : Fin r → Finset ℕ := fun i => band x (a i) with hG
  set QB := univ.biUnion G with hQB
  set QP := univ.biUnion P with hQP
  set Q := QB ∪ QP with hQ
  set w : ℕ → ℂ := fun p => if p ∈ QB then (q : ℂ) else q₀ with hw
  set J := Fintype.piFinset G ×ˢ groupLists P S with hJ
  set R : (Fin r → ℕ) × (ι → Fin M → ℕ) → Finset ℕ :=
    fun j => univ.image j.1 ∪ groupRep S j.2 with hR
  set c : (Fin r → ℕ) × (ι → Fin M → ℕ) → ℂ :=
    fun j => bandCoeff G * groupCoeff P S b j.2 with hc
  set B := max 1 vlo⁻¹ with hB
  set L := Real.log x with hL
  have hRB : ∀ β ∈ Fintype.piFinset G, univ.image β ⊆ QB := fun β hβ =>
    image_subset_biUnion hβ
  have hRP : ∀ p ∈ groupLists P S, groupRep S p ⊆ QP := fun p hp => groupRep_subset hp
  have hRQ : ∀ j ∈ J, R j ⊆ Q := by
    intro j hj
    obtain ⟨h₁, h₂⟩ := mem_product.1 hj
    exact union_subset_union (hRB _ h₁) (hRP _ h₂)
  have hwB : ∀ p ∈ QB, w p = q := fun p hp => by simp [hw, hp]
  have hwP : ∀ p ∈ QP, w p = q₀ := fun p hp => by
    simp [hw, disjoint_right.1 hQd hp]
  have hw1 : ∀ p ∈ Q, ‖w p - 1‖ ≤ 1 := by
    intro p _
    by_cases hp : p ∈ QB
    · rw [hwB p hp]; exact norm_ofReal_sub_one_le hq hq₁
    · simp only [hw, hp, ite_false]; exact norm_ofReal_sub_one_le hq₀ hq₀₁
  -- the marks are the list form
  have hH : ∀ n, (markedWeight univ q (fun i => band x (a i)) n : ℂ) *
      markedListWeight P q₀ S b n = listForm Q J R c w n := by
    intro n
    rw [markedWeight_eq_listForm hGd q hwB, markedListWeight_eq_listForm hPd q₀ S b hwP,
      listForm_mul hQd hRB hRP]
  -- `∑_{p ∈ Q} 1/p ≤ r + |ι| v₊`
  have hsumQ : ∑ p ∈ Q, (1 : ℝ) / p ≤ r + Fintype.card ι * vhi := by
    rw [sum_union hQd, sum_biUnion fun i _ j _ hij => hGd i j hij,
      sum_biUnion fun g _ h _ hgh => hPd g h hgh]
    have h₁ : ∑ i, ∑ p ∈ G i, (1 : ℝ) / p ≤ r := by
      calc _ ≤ ∑ _i : Fin r, (1 : ℝ) := sum_le_sum fun i _ => (hVB i).2
        _ = r := by simp
    have h₂ : ∑ g, ∑ p ∈ P g, (1 : ℝ) / p ≤ Fintype.card ι * vhi := by
      calc _ ≤ ∑ _g : ι, vhi := sum_le_sum fun g _ => (hVP g).2
        _ = _ := by simp
    linarith
  refine ⟨truncModel Q J R c w h₀, ?_, ?_, ?_⟩
  · -- (a) support
    intro d hd
    obtain ⟨j, hj, U, hU, hUh, rfl⟩ := exists_of_truncModel_ne_zero hd
    have hsub : R j ∪ U ⊆ Q := union_subset (hRQ j hj) (hU.trans sdiff_subset)
    have hpr : ∀ p ∈ R j ∪ U, p.Prime := fun p hp => hprime p (hsub hp)
    obtain ⟨h₁, h₂⟩ := mem_product.1 hj
    refine ⟨?_, ?_, ?_⟩
    · refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp => (hpr p hp).squarefree
      intro p hp p' hp' hne
      exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes (hpr p hp) (hpr p' hp')).2 hne)
    · -- `|R_j ∪ U| ≤ r + (m₀ + 1)|ι| + h₀`
      have hcard : #(R j ∪ U) ≤ r + (m₀ + 1) * Fintype.card ι + h₀ := by
        have hR₁ : #(univ.image j.1) ≤ r := (card_image_le).trans (by simp)
        have hR₂ : #(groupRep S j.2) ≤ (m₀ + 1) * Fintype.card ι := by
          rw [card_groupRep hPd h₂]
          calc ∑ g, #(S g) ≤ ∑ _g : ι, (m₀ + 1) := sum_le_sum fun g _ => hS g
            _ = _ := by rw [sum_const, card_univ, smul_eq_mul, mul_comm]
        calc #(R j ∪ U) ≤ #(R j) + #U := card_union_le _ _
          _ ≤ #(univ.image j.1) + #(groupRep S j.2) + #U := by
              gcongr
              exact card_union_le _ _
          _ ≤ _ := by omega
      have hL46 : 0 ≤ L ^ (0.46 : ℝ) := Real.rpow_nonneg hL0 _
      have hprod : ((∏ p ∈ R j ∪ U, p : ℕ) : ℝ) ≤
          Real.exp (L ^ (0.46 : ℝ)) ^ #(R j ∪ U) := by
        rw [Nat.cast_prod, ← prod_const]
        exact prod_le_prod₀ (fun p _ => Nat.cast_nonneg _) fun p hp => hsize p (hsub hp)
      refine hprod.trans ?_
      rw [← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ((mul_le_mul_of_nonneg_right ?_ hL46).trans hsupp)
      exact_mod_cast hcard
    · intro p hp
      rw [Nat.primeFactors_prod hpr] at hp
      rcases mem_union.1 (hsub hp) with h | h
      · obtain ⟨i, -, hi⟩ := mem_biUnion.1 h
        exact Or.inr ⟨i, hi⟩
      · exact Or.inl h
  · -- (b) mass
    refine (sum_norm_truncModel_div_le J R c hw1 h₀ _).trans ?_
    have hm : ∑ j ∈ J, ‖c j‖ / ∏ p ∈ R j, (p : ℝ) ≤ 1 := by
      rw [show (∑ j ∈ J, ‖c j‖ / ∏ p ∈ R j, (p : ℝ)) = _ from
        sum_norm_div_mul hQd hRB hRP (fun _ => bandCoeff G) (groupCoeff P S b)]
      exact (mul_le_mul (sum_norm_bandCoeff_div_le hGd)
        (sum_norm_groupCoeff_div_le (fun g => hvlo.trans_le (hVP g).1) hb hPd)
        (sum_nonneg fun _ _ => by positivity) zero_le_one).trans_eq (one_mul 1)
    calc (∑ j ∈ J, ‖c j‖ / ∏ p ∈ R j, (p : ℝ)) * ∏ p ∈ Q, (1 + 1 / (p : ℝ))
        ≤ 1 * ∏ p ∈ Q, (1 + 1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_right hm (prod_nonneg fun _ _ => by positivity)
      _ ≤ Real.exp (1 * ∑ p ∈ Q, (1 : ℝ) / p) := by
          rw [one_mul]
          exact prod_one_add_div_le_exp Q zero_le_one
      _ ≤ Real.exp (r + Fintype.card ι * vhi) := Real.exp_le_exp.2 (by linarith)
      _ ≤ L ^ C₈ := hmass
  · -- (c) mean square
    intro R₀ hR₀
    set Cx : ℝ := 2 ^ r * B ^ ((m₀ + 1) * Fintype.card ι) with hCx
    have hB1 : 1 ≤ B := le_max_left _ _
    have hCx0 : 0 ≤ Cx := by positivity
    -- the pointwise error
    have hpt : ∀ n ∈ Ioc ⌊R₀⌋₊ ⌊2 * R₀⌋₊,
        ‖(markedWeight univ q (fun i => band x (a i)) n : ℂ) * markedListWeight P q₀ S b n -
            ∑ d ∈ n.divisors, truncModel Q J R c w h₀ d‖ ^ 2 ≤
          Cx ^ 2 / 4 ^ h₀ * ((4 : ℝ) ^ (m₀ + 3)) ^ #(divs Q n) := by
      intro n hn
      have hn0 : n ≠ 0 := by
        have := (mem_Ioc.1 hn).1
        omega
      rw [hH n]
      have h1 := norm_listForm_sub_le (hR := hRQ) (fun p hp => hprime p hp) c hw1 h₀ hn0
      rw [show (∑ j ∈ J, if R j ⊆ divs Q n then ‖c j‖ else 0) = _ from
        sum_norm_mul hQd hRB hRP (fun _ => bandCoeff G) (groupCoeff P S b) n] at h1
      have hB' := sum_norm_bandCoeff_le hGd (fun i => (hVB i).1) n
      have hP' := sum_norm_groupCoeff_le hvlo (fun g => (hVP g).1) hS hb hPd n
      rw [Fintype.card_fin] at hB'
      have hcardD : #(divs Q n) = #(divs QB n) + #(divs QP n) := by
        rw [hQ, divs_union, card_union_of_disjoint (disjoint_of_subset_left (divs_subset _ n)
          (disjoint_of_subset_right (divs_subset _ n) hQd))]
      set u := #(divs QB n)
      set v := #(divs QP n)
      have hS0 : 0 ≤ ∑ j ∈ groupLists P S,
          (if groupRep S j ⊆ divs QP n then ‖groupCoeff P S b j‖ else 0) :=
        sum_nonneg fun _ _ => by positivity
      have hSB0 : 0 ≤ ∑ β ∈ Fintype.piFinset G,
          (if univ.image β ⊆ divs QB n then ‖bandCoeff G‖ else 0) :=
        sum_nonneg fun _ _ => by positivity
      -- `S 4^{|D|} ≤ C_x 2^{(m₀+3)|D|}`
      have hkey₁ : ∀ t : ℝ, t ^ r * t ^ u * (B ^ Fintype.card ι * t ^ v) ^ (m₀ + 1) *
          (t ^ 2) ^ (u + v) = t ^ r * B ^ ((m₀ + 1) * Fintype.card ι) *
            (t ^ u * t ^ (v * (m₀ + 1)) * t ^ (2 * (u + v))) := fun t => by ring
      have hkey₂ : ∀ t : ℝ, t ^ r * B ^ ((m₀ + 1) * Fintype.card ι) *
          (t ^ (u * (m₀ + 1)) * t ^ (v * (m₀ + 1)) * t ^ (2 * (u + v))) =
            (t ^ r * B ^ ((m₀ + 1) * Fintype.card ι)) * (t ^ (m₀ + 3)) ^ (u + v) :=
        fun t => by ring
      have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
      have hu : (2 : ℝ) ^ u ≤ 2 ^ (u * (m₀ + 1)) :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_right _ (by omega))
      have hE : ‖listForm Q J R c w n - ∑ d ∈ n.divisors, truncModel Q J R c w h₀ d‖ ≤
          Cx * ((2 : ℝ) ^ (m₀ + 3)) ^ (u + v) / 2 ^ h₀ := by
        refine h1.trans ?_
        rw [hcardD, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
        calc _ ≤ (2 ^ r * 2 ^ u) * (B ^ Fintype.card ι * 2 ^ v) ^ (m₀ + 1) *
              (4 : ℝ) ^ (u + v) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hB' hP' hS0 (by positivity))
              (by positivity)
          _ = 2 ^ r * B ^ ((m₀ + 1) * Fintype.card ι) *
              (2 ^ u * 2 ^ (v * (m₀ + 1)) * 2 ^ (2 * (u + v))) := by
            rw [h4, ← hkey₁ 2]
          _ ≤ 2 ^ r * B ^ ((m₀ + 1) * Fintype.card ι) *
              (2 ^ (u * (m₀ + 1)) * 2 ^ (v * (m₀ + 1)) * 2 ^ (2 * (u + v))) := by
            gcongr
          _ = Cx * ((2 : ℝ) ^ (m₀ + 3)) ^ (u + v) := hkey₂ 2
      rw [hcardD]
      calc _ ≤ (Cx * ((2 : ℝ) ^ (m₀ + 3)) ^ (u + v) / 2 ^ h₀) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hE 2
        _ = Cx ^ 2 / 4 ^ h₀ * ((4 : ℝ) ^ (m₀ + 3)) ^ (u + v) := by
            have hsq : ∀ t : ℝ, (Cx * (t ^ (m₀ + 3)) ^ (u + v) / t ^ h₀) ^ 2 =
                Cx ^ 2 / (t ^ 2) ^ h₀ * ((t ^ 2) ^ (m₀ + 3)) ^ (u + v) := fun t => by ring
            rw [hsq 2, ← h4]
    have hz : (1 : ℝ) ≤ 4 ^ (m₀ + 3) := one_le_pow₀ (by norm_num)
    have hR2 : 0 ≤ 2 * R₀ := by linarith
    calc ∑ n ∈ Ioc ⌊R₀⌋₊ ⌊2 * R₀⌋₊,
          ‖(markedWeight univ q (fun i => band x (a i)) n : ℂ) * markedListWeight P q₀ S b n -
            ∑ d ∈ n.divisors, truncModel Q J R c w h₀ d‖ ^ 2
        ≤ ∑ n ∈ Ioc ⌊R₀⌋₊ ⌊2 * R₀⌋₊, Cx ^ 2 / 4 ^ h₀ * ((4 : ℝ) ^ (m₀ + 3)) ^ #(divs Q n) :=
          sum_le_sum hpt
      _ ≤ ∑ n ∈ Ioc 0 ⌊2 * R₀⌋₊, Cx ^ 2 / 4 ^ h₀ * ((4 : ℝ) ^ (m₀ + 3)) ^ #(divs Q n) :=
          sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le _))
            fun _ _ _ => by positivity
      _ = Cx ^ 2 / 4 ^ h₀ * ∑ n ∈ Ioc 0 ⌊2 * R₀⌋₊, ((4 : ℝ) ^ (m₀ + 3)) ^ #(divs Q n) := by
          rw [mul_sum]
      _ ≤ Cx ^ 2 / 4 ^ h₀ * (⌊2 * R₀⌋₊ * ∏ p ∈ Q, (1 + (4 ^ (m₀ + 3) - 1) / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left (sum_pow_card_divs_le (fun p hp => hprime p hp) hz _)
            (by positivity)
      _ ≤ Cx ^ 2 / 4 ^ h₀ *
            (2 * R₀ * Real.exp ((4 ^ (m₀ + 3) - 1) * (r + Fintype.card ι * vhi))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul (Nat.floor_le hR2) ?_
            (prod_nonneg fun p _ => by positivity) hR2) (by positivity)
          refine (prod_one_add_div_le_exp Q (by linarith)).trans (Real.exp_le_exp.2 ?_)
          exact mul_le_mul_of_nonneg_left hsumQ (by linarith)
      _ = R₀ * (2 * Cx ^ 2 * Real.exp ((4 ^ (m₀ + 3) - 1) * (r + Fintype.card ι * vhi)) /
            4 ^ h₀) := by ring
      _ ≤ R₀ * (CNN * L ^ (-(N : ℝ))) :=
          mul_le_mul_of_nonneg_left hms (by linarith)
      _ = CNN * R₀ * L ^ (-(N : ℝ)) := by ring

/-- The numerical condition of step 6: `2 C_x² e^{(z - 1)(r + |ι| v₊)} 4^{-h₀} ≤ L^{-N}`,
with `C_x = 2^r B^{(m₀+1)|ι|}`, once `(2κ₂ + (z - 1)κ₁ + N + 2) T ≤ L^{0.01} ≤ h₀ + 1`. -/
theorem meanSquare_numeric {L κ₁ κ₂ B C₀ vhi : ℝ} {r m₀ c h₀ N : ℕ} (hL0 : 0 < L)
    (hT1 : 1 ≤ Real.log L) (hB1 : 1 ≤ B) (hrT : (r : ℝ) ≤ Real.log L)
    (hι : (c : ℝ) ≤ 2 * |C₀| * Real.log L)
    (hrι : (r : ℝ) + c * vhi ≤ κ₁ * Real.log L) (hh₀ge : L ^ (0.01 : ℝ) - 1 ≤ h₀)
    (hκ₂ : κ₂ = Real.log 2 + 2 * (m₀ + 1) * |C₀| * Real.log B)
    (hK₂ : (2 * κ₂ + (4 ^ (m₀ + 3) - 1) * κ₁ + N + 2) * Real.log L ≤ L ^ (0.01 : ℝ)) :
    2 * (2 ^ r * B ^ ((m₀ + 1) * c)) ^ 2 *
        Real.exp ((4 ^ (m₀ + 3) - 1) * (r + c * vhi)) / 4 ^ h₀ ≤
      1 * L ^ (-(N : ℝ)) := by
  set T := Real.log L with hT
  have hB0 : 0 < B := by linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hpow : ∀ (y : ℝ) (n : ℕ), 0 < y → y ^ n = Real.exp (n * Real.log y) := fun y n hy => by
    rw [Real.exp_nat_mul, Real.exp_log hy]
  have hCx : 2 ^ r * B ^ ((m₀ + 1) * c) ≤ Real.exp (κ₂ * T) := by
    rw [hpow 2 r two_pos, hpow B _ hB0, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h₁ : (r : ℝ) * Real.log 2 ≤ T * Real.log 2 := mul_le_mul_of_nonneg_right hrT hl2
    have h₂ : ((m₀ : ℝ) + 1) * c * Real.log B ≤ (2 * (m₀ + 1) * |C₀| * T) * Real.log B := by
      refine mul_le_mul_of_nonneg_right ?_ hlogB
      calc ((m₀ : ℝ) + 1) * c ≤ (m₀ + 1) * (2 * |C₀| * T) :=
            mul_le_mul_of_nonneg_left hι (by positivity)
        _ = 2 * (m₀ + 1) * |C₀| * T := by ring
    rw [Nat.cast_mul, Nat.cast_add_one, hκ₂]
    linarith
  have hz1 : (0 : ℝ) ≤ 4 ^ (m₀ + 3) - 1 := by
    have : (1 : ℝ) ≤ 4 ^ (m₀ + 3) := one_le_pow₀ (by norm_num)
    linarith
  have hE : Real.exp ((4 ^ (m₀ + 3) - 1) * (r + c * vhi)) ≤
      Real.exp ((4 ^ (m₀ + 3) - 1) * κ₁ * T) := by
    rw [mul_assoc]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hrι hz1)
  have hlog4 : 1 ≤ Real.log 4 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have h4 : Real.exp (L ^ (0.01 : ℝ) - 1) ≤ 4 ^ h₀ := by
    rw [hpow 4 h₀ (by norm_num)]
    refine Real.exp_le_exp.2 (hh₀ge.trans ?_)
    nlinarith [Nat.cast_nonneg (α := ℝ) h₀]
  have hl2 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp two_pos]
    linarith [Real.exp_one_gt_d9]
  have hCx0 : 0 ≤ 2 ^ r * B ^ ((m₀ + 1) * c) := by positivity
  have hsq : Real.exp (κ₂ * T) ^ 2 = Real.exp (2 * κ₂ * T) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  calc 2 * (2 ^ r * B ^ ((m₀ + 1) * c)) ^ 2 *
        Real.exp ((4 ^ (m₀ + 3) - 1) * (r + c * vhi)) / 4 ^ h₀
      ≤ 2 * Real.exp (κ₂ * T) ^ 2 * Real.exp ((4 ^ (m₀ + 3) - 1) * κ₁ * T) /
          Real.exp (L ^ (0.01 : ℝ) - 1) := by
        gcongr
    _ = Real.exp (Real.log 2 + 2 * κ₂ * T + (4 ^ (m₀ + 3) - 1) * κ₁ * T -
          (L ^ (0.01 : ℝ) - 1)) := by
        rw [hsq]
        conv_rhs => rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log two_pos]
    _ ≤ Real.exp (-(N : ℝ) * T) := by
        refine Real.exp_le_exp.2 ?_
        nlinarith
    _ = 1 * L ^ (-(N : ℝ)) := by
        rw [one_mul, Real.rpow_def_of_pos hL0, mul_comm]

end DivModel

open Finset in
/-- **Lemma E1 (truncated divisor model, X5).** For `m₀` fixed there is `C₈`
(`2|C₀||v₊| + 2`) such that for every `N` there is `C_N` with: eventually, for groups as in
(6.1), at most `K₀ + C_N s` disjoint bands in the window, every `S` with `|S g| ≤ m₀ + 1`
(zero allowed) and every `|b| ≤ 1`, the marks have a truncated divisor model. Expand both
marked weights over represented lists, with the damping as
`∏_{p ∤ lists} (1 - (1 - q_p) 1_{p ∣ n})`; keep the subsets `T` of unrepresented primes with
`|T| ≤ h₀ = ⌊L^{0.01}⌋`, so that `log d ≤ 2L^{0.47}` (step 3). The bands enter only through
`e^r ≤ L^{1/10}` (U2). With `Q` the group and band primes and `D(n)` those dividing `n`, the
squared pointwise error is `≤ C_x² 4^{-h₀} z^{|D(n)|}` with `z = 4^{m₀+3}` and
`C_x = 2^r max(1, v₋⁻¹)^{(m₀+1)|ι|}` (step 5), and
`∑_{n ≤ 2R} z^{|D(n)|} ≤ 2R ∏_{p ∈ Q} (1 + (z - 1)/p)` is (6.27).

The proof is `DivModel.divisorModel_of_facts`: the list forms
`DivModel.markedWeight_eq_listForm` and `DivModel.markedListWeight_eq_listForm`, their product
`DivModel.listForm_mul`, the truncation bounds `DivModel.norm_listForm_sub_le` and
`DivModel.sum_norm_truncModel_div_le`, and (6.27) as `DivModel.sum_pow_card_divs_le`. -/
theorem exists_divisorModel (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN : ℝ)
    (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) (hvlo : 0 < vlo)
    (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) (m₀ : ℕ) :
    ∃ C₈ : ℝ, ∀ N : ℕ, ∃ CNN : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ), InertAdmissible K₀ CN alo ahi x a →
        ∀ (M : ℕ) (S : ι → Finset (Fin M)) (b : (ι → Fin M → ℕ) → ℂ),
          (∀ g, (S g).card ≤ m₀ + 1) → (∀ p, ‖b p‖ ≤ 1) →
          ∃ A : ℕ → ℂ, DivisorModel x q q₀ a P S b C₈ CNN N A := by
  set B := max 1 vlo⁻¹ with hB
  -- the exponents of steps 4 and 6
  set κ₁ : ℝ := 1 + 2 * |C₀| * |vhi| with hκ₁
  set κ₂ : ℝ := Real.log 2 + 2 * (m₀ + 1) * |C₀| * Real.log B with hκ₂
  refine ⟨2 * |C₀| * |vhi| + 2, fun N => ⟨1, ?_⟩⟩
  have hB1 : 1 ≤ B := le_max_left _ _
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  filter_upwards [OneSided.eventually_harmonicMass_band halo.le,
    Real.tendsto_log_atTop.eventually_ge_atTop 1, Sieve.tendsto_logLog.eventually_ge_atTop 1,
    Sieve.eventually_mul_logLogLog_le (K₀ + |CN|),
    OneSided.eventually_two_mul_rpow_lt (show (0 : ℝ) < 0.27 - ahi by linarith),
    Sieve.eventually_mul_rpow_le_log_rpow (1 + 2 * (m₀ + 1) * |C₀|) 1
      (show (0 : ℝ) < 0.01 by norm_num),
    Sieve.eventually_mul_rpow_le_log_rpow
      (2 * κ₂ + ((4 : ℝ) ^ (m₀ + 3) - 1) * κ₁ + N + 2) 1 (show (0 : ℝ) < 0.01 by norm_num)]
    with x hVB hL1 hT1 hs htwo hK₁ hK₂
  intro ι _ _ P big hadm r a hin M S b hS hb
  simp only [logLog, logLogLog, Real.rpow_one] at hT1 hs hK₁ hK₂
  set L := Real.log x with hL
  set T := Real.log L with hT
  have hL0 : 0 < L := by linarith
  have hT0 : 0 ≤ T := by linarith
  obtain ⟨hPd, -, hsm, -, hbg, hVP, hsmall, hbig, -⟩ := hadm
  obtain ⟨hr, ha, hGd⟩ := hin
  -- `|ι| ≤ 2 |C₀| T` and `r ≤ T`
  have hι : (Fintype.card ι : ℝ) ≤ 2 * |C₀| * T := by
    have : Fintype.card ι ≤ (univ \ big).card + big.card := by
      rw [← card_univ]
      calc (univ : Finset ι).card = ((univ \ big) ∪ big).card := by
            rw [sdiff_union_of_subset (subset_univ big)]
        _ ≤ _ := card_union_le _ _
    have h' : (Fintype.card ι : ℝ) ≤ (univ \ big).card + big.card := by exact_mod_cast this
    have : C₀ * T ≤ |C₀| * T := mul_le_mul_of_nonneg_right (le_abs_self C₀) hT0
    linarith
  have hsT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hrT : (r : ℝ) ≤ T := by
    have h₁ : CN * Real.log T ≤ |CN| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self _) hsT
    have h₂ := hs
    have : (0 : ℝ) ≤ K₀ := Nat.cast_nonneg _
    nlinarith [abs_nonneg CN]
  -- the primes: sizes and disjointness
  have hband_lt : ∀ i, ∀ p ∈ band x (a i), (p : ℝ) < Real.exp (L ^ (0.27 : ℝ)) := by
    intro i p hp
    have := Real.exp_lt_exp.2 (htwo (a i) 0.27 (by linarith [(ha i).2]))
    linarith [OneSided.le_exp_of_mem_band hp]
  have hgroup : ∀ g, ∀ p ∈ P g, p.Prime ∧ Real.exp (L ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (L ^ (0.46 : ℝ)) := by
    intro g p hp
    have h27 : L ^ (0.27 : ℝ) ≤ L ^ (0.39 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h36 : L ^ (0.36 : ℝ) ≤ L ^ (0.46 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    by_cases hg : g ∈ big
    · obtain ⟨h₁, h₂, h₃⟩ := mem_primesIcc.1 (hbig g hg hp)
      exact ⟨h₁, (Real.exp_le_exp.2 h27).trans h₂, h₃⟩
    · obtain ⟨h₁, h₂, h₃⟩ := mem_primesIcc.1 (hsmall g hg hp)
      exact ⟨h₁, h₂, h₃.trans (Real.exp_le_exp.2 h36)⟩
  have hQd : Disjoint (univ.biUnion fun i => band x (a i)) (univ.biUnion P) := by
    refine disjoint_left.2 fun p hp hp' => ?_
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 hp
    obtain ⟨g, -, hg⟩ := mem_biUnion.1 hp'
    linarith [hband_lt i p hi, (hgroup g p hg).2.1]
  have h2746 : Real.exp (L ^ (0.27 : ℝ)) ≤ Real.exp (L ^ (0.46 : ℝ)) :=
    Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have hprime : ∀ p ∈ (univ.biUnion fun i => band x (a i)) ∪ univ.biUnion P, p.Prime ∧
      (p : ℝ) ≤ Real.exp (L ^ (0.46 : ℝ)) := by
    intro p hp
    rcases mem_union.1 hp with h | h
    · obtain ⟨i, -, hi⟩ := mem_biUnion.1 h
      exact ⟨TypeII.band_prime hi, (hband_lt i p hi).le.trans h2746⟩
    · obtain ⟨g, -, hg⟩ := mem_biUnion.1 h
      exact ⟨(hgroup g p hg).1, (hgroup g p hg).2.2⟩
  -- the depth `h₀ = ⌊L^{0.01}⌋`
  set h₀ := ⌊L ^ (0.01 : ℝ)⌋₊ with hh₀
  have hL01 : 0 ≤ L ^ (0.01 : ℝ) := Real.rpow_nonneg hL0.le _
  have hh₀le : (h₀ : ℝ) ≤ L ^ (0.01 : ℝ) := Nat.floor_le hL01
  have hh₀ge : L ^ (0.01 : ℝ) - 1 ≤ h₀ := by
    have := Nat.lt_floor_add_one (L ^ (0.01 : ℝ))
    rw [← hh₀] at this
    linarith
  have hrι : (r : ℝ) + Fintype.card ι * vhi ≤ κ₁ * T := by
    have : (Fintype.card ι : ℝ) * vhi ≤ 2 * |C₀| * T * |vhi| :=
      (mul_le_mul_of_nonneg_left (le_abs_self vhi) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hι (abs_nonneg _))
    rw [hκ₁]
    nlinarith
  refine DivModel.divisorModel_of_facts hq hq₁ hq₀ hq₀₁ hvlo _ 1 N h₀ hL0.le hPd hGd hQd
    (fun p hp => (hprime p hp).1) (fun p hp => (hprime p hp).2)
    (fun i => hVB (a i) (ha i).1) hVP hS hb ?_ ?_ ?_
  · -- step 3: `log d ≤ 2 L^{0.47}`
    have hcnt : ((r + (m₀ + 1) * Fintype.card ι + h₀ : ℕ) : ℝ) ≤ 2 * L ^ (0.01 : ℝ) := by
      push_cast
      have : ((m₀ : ℝ) + 1) * Fintype.card ι ≤ 2 * (m₀ + 1) * |C₀| * T := by
        nlinarith
      linarith
    calc ((r + (m₀ + 1) * Fintype.card ι + h₀ : ℕ) : ℝ) * L ^ (0.46 : ℝ)
        ≤ 2 * L ^ (0.01 : ℝ) * L ^ (0.46 : ℝ) :=
          mul_le_mul_of_nonneg_right hcnt (Real.rpow_nonneg hL0.le _)
      _ = 2 * L ^ (0.47 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add hL0]
          norm_num
  · -- step 4: the mass
    rw [Sieve.log_rpow_eq hL0]
    refine Real.exp_le_exp.2 (hrι.trans ?_)
    rw [logLog, hκ₁]
    nlinarith
  · -- step 6: the mean square, `2^{-h₀}` beats every power of `L`
    exact DivModel.meanSquare_numeric hL0 hT1 hB1 hrT hι hrι hh₀ge (by rw [hκ₂]) hK₂

end Erdos408.TwoSided
