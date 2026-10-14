import Erdos408.Extraction.Defs

/-!
# The independent divisor model

In the independent divisor model on a finite set `A` of primes (PD §7.1),
each `p ∈ A` divides independently with probability `1 / p`. The set
`S ⊆ A` of divisors then has weight `π_A(S) = ∏_{p ∈ S} 1/p ∏_{p ∈ A \ S} (1 - 1/p)`,
and the model mean of `f` is `E_A[f] = ∑_{S ⊆ A} π_A(S) f(S)`. For an
arithmetic function `H`, `M_A(H) = E_A[S ↦ H(∏ S)]`.

This file proves the facts about the model that the extraction uses:
`∑ π_A = 1`, linearity and monotonicity, the one-prime recursion, the
product rule `E_{A ∪ B} = E_A E_B` for disjoint `A, B`, and independence of
functions of disjoint blocks.
-/

namespace Erdos408

open Finset

namespace Sieve

noncomputable section

/-- The weight `π_A(S) = ∏_{p ∈ S} 1/p ∏_{p ∈ A \ S} (1 - 1/p)` of `S ⊆ A`. -/
def modelWeight (A S : Finset ℕ) : ℝ :=
  (∏ p ∈ S, (1 : ℝ) / p) * ∏ p ∈ A \ S, (1 - (1 : ℝ) / p)

/-- The model mean `E_A[f] = ∑_{S ⊆ A} π_A(S) f(S)`. -/
def modelMean (A : Finset ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ A.powerset, modelWeight A S * f S

/-- The independent divisor model mean `M_A(H) = E_A[S ↦ H(∏ S)]` of an
arithmetic function. -/
def divisorModel (A : Finset ℕ) (H : ℕ → ℝ) : ℝ :=
  modelMean A fun S => H (∏ p ∈ S, p)

/-! ### Basic properties -/

/-- The model weights are nonnegative when every element of `A` is positive. -/
lemma modelWeight_nonneg {A : Finset ℕ} (hA : ∀ p ∈ A, 0 < p) (S : Finset ℕ) :
    0 ≤ modelWeight A S := by
  refine mul_nonneg (prod_nonneg fun p _ => by positivity) (prod_nonneg fun p hp => ?_)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hA p (mem_sdiff.1 hp).1
  rw [sub_nonneg, div_le_one (by linarith)]
  exact hp1

/-- The model weights sum to one. -/
lemma sum_modelWeight (A : Finset ℕ) : ∑ S ∈ A.powerset, modelWeight A S = 1 := by
  have h := prod_add (fun p : ℕ => (1 : ℝ) / p) (fun p => 1 - (1 : ℝ) / p) A
  simp only [add_sub_cancel, prod_const_one] at h
  exact h.symm

/-- The mean over the empty set is the value at `∅`. -/
lemma modelMean_empty (f : Finset ℕ → ℝ) : modelMean ∅ f = f ∅ := by
  simp [modelMean, modelWeight]

/-- The model mean only sees the values on subsets of `A`. -/
lemma modelMean_congr {A : Finset ℕ} {f g : Finset ℕ → ℝ} (h : ∀ S ⊆ A, f S = g S) :
    modelMean A f = modelMean A g :=
  sum_congr rfl fun S hS => by rw [h S (mem_powerset.1 hS)]

/-- The mean of a constant. -/
lemma modelMean_const (A : Finset ℕ) (c : ℝ) : modelMean A (fun _ => c) = c := by
  rw [modelMean, ← sum_mul, sum_modelWeight, one_mul]

/-- The model mean is additive. -/
lemma modelMean_add (A : Finset ℕ) (f g : Finset ℕ → ℝ) :
    modelMean A (fun S => f S + g S) = modelMean A f + modelMean A g := by
  simp only [modelMean, mul_add, sum_add_distrib]

/-- The model mean commutes with scalars. -/
lemma modelMean_mul_left (A : Finset ℕ) (c : ℝ) (f : Finset ℕ → ℝ) :
    modelMean A (fun S => c * f S) = c * modelMean A f := by
  simp only [modelMean, mul_sum]
  exact sum_congr rfl fun S _ => by ring

/-- The model mean commutes with subtraction. -/
lemma modelMean_sub (A : Finset ℕ) (f g : Finset ℕ → ℝ) :
    modelMean A (fun S => f S - g S) = modelMean A f - modelMean A g := by
  simp only [modelMean, mul_sub, sum_sub_distrib]

/-- The model mean of a finite sum. -/
lemma modelMean_sum {ι : Type*} (A : Finset ℕ) (I : Finset ι) (f : ι → Finset ℕ → ℝ) :
    modelMean A (fun S => ∑ i ∈ I, f i S) = ∑ i ∈ I, modelMean A (f i) := by
  simp only [modelMean, mul_sum]
  exact sum_comm

/-- The model mean is monotone. -/
lemma modelMean_mono {A : Finset ℕ} (hA : ∀ p ∈ A, 0 < p) {f g : Finset ℕ → ℝ}
    (h : ∀ S ⊆ A, f S ≤ g S) : modelMean A f ≤ modelMean A g :=
  sum_le_sum fun S hS => mul_le_mul_of_nonneg_left (h S (mem_powerset.1 hS))
    (modelWeight_nonneg hA S)

/-- The model mean of a nonnegative function is nonnegative. -/
lemma modelMean_nonneg {A : Finset ℕ} (hA : ∀ p ∈ A, 0 < p) {f : Finset ℕ → ℝ}
    (h : ∀ S ⊆ A, 0 ≤ f S) : 0 ≤ modelMean A f := by
  have := modelMean_mono hA (f := fun _ => 0) h
  rwa [modelMean_const] at this

/-- The model mean of a function at most one is at most one. -/
lemma modelMean_le_one {A : Finset ℕ} (hA : ∀ p ∈ A, 0 < p) {f : Finset ℕ → ℝ}
    (h : ∀ S ⊆ A, f S ≤ 1) : modelMean A f ≤ 1 := by
  have := modelMean_mono hA (g := fun _ => 1) h
  rwa [modelMean_const] at this

/-! ### The product structure -/

/-- Adding one prime `b ∉ A`: `E_{A ∪ {b}}[f] = (1 - 1/b) E_A[f] + (1/b) E_A[f(· ∪ {b})]`. -/
lemma modelMean_insert {A : Finset ℕ} {b : ℕ} (hb : b ∉ A) (f : Finset ℕ → ℝ) :
    modelMean (insert b A) f =
      (1 - (1 : ℝ) / b) * modelMean A f + (1 : ℝ) / b * modelMean A fun T => f (insert b T) := by
  rw [modelMean, sum_powerset_insert hb, modelMean, modelMean, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun T hT => ?_
    have hbT : b ∉ T := fun h => hb (mem_powerset.1 hT h)
    have : insert b A \ T = insert b (A \ T) := by
      rw [insert_sdiff_of_notMem _ hbT]
    rw [modelWeight, modelWeight, this, prod_insert (fun h => hb (mem_sdiff.1 h).1)]
    ring
  · refine sum_congr rfl fun T hT => ?_
    have hbT : b ∉ T := fun h => hb (mem_powerset.1 hT h)
    have : insert b A \ insert b T = A \ T := by
      rw [insert_sdiff_insert, sdiff_insert_of_notMem hb]
    rw [modelWeight, modelWeight, this, prod_insert hbT]
    ring

/-- The product rule (Fubini): for disjoint `A` and `B`,
`E_{A ∪ B}[f] = E_A[S ↦ E_B[T ↦ f(S ∪ T)]]`. -/
lemma modelMean_union {A B : Finset ℕ} (hAB : Disjoint A B) (f : Finset ℕ → ℝ) :
    modelMean (A ∪ B) f = modelMean A fun S => modelMean B fun T => f (S ∪ T) := by
  induction B using Finset.induction_on generalizing f with
  | empty =>
    simp only [union_empty, modelMean_empty]
  | insert b B hbB ih =>
    have hbA : b ∉ A := fun h => disjoint_left.1 hAB h (mem_insert_self b B)
    have hAB' : Disjoint A B := disjoint_of_subset_right (subset_insert b B) hAB
    have hb : b ∉ A ∪ B := by simp [hbA, hbB]
    rw [union_insert, modelMean_insert hb, ih hAB', ih hAB']
    simp only [modelMean_insert hbB, union_insert]
    rw [modelMean_add, modelMean_mul_left, modelMean_mul_left]

/-- The marginal: if `f(S)` depends only on `S ∩ U` with `U ⊆ A`, then
`E_A[f] = E_U[f]`. -/
lemma modelMean_eq_of_subset {A U : Finset ℕ} (hUA : U ⊆ A) {f : Finset ℕ → ℝ}
    (hf : ∀ S ⊆ A, f S = f (S ∩ U)) : modelMean A f = modelMean U f := by
  have hA : A = U ∪ (A \ U) := (union_sdiff_of_subset hUA).symm
  rw [hA, modelMean_union disjoint_sdiff]
  refine modelMean_congr fun S hS => ?_
  rw [← modelMean_const (A \ U) (f S)]
  refine modelMean_congr fun T hT => ?_
  have hsub : S ∪ T ⊆ A := union_subset (hS.trans hUA) (hT.trans sdiff_subset)
  rw [hf _ hsub, union_inter_distrib_right, inter_eq_left.2 hS,
    disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left hT sdiff_disjoint), union_empty]

/-- Independence: functions of pairwise disjoint blocks `B_i ⊆ A` have
`E_A[∏ f_i(S ∩ B_i)] = ∏ E_{B_i}[f_i]`. -/
lemma modelMean_prod {ι : Type*} [DecidableEq ι] (I : Finset ι) (B : ι → Finset ℕ)
    (hB : (I : Set ι).PairwiseDisjoint B) {A : Finset ℕ} (hA : I.biUnion B ⊆ A)
    (f : ι → Finset ℕ → ℝ) :
    modelMean A (fun S => ∏ i ∈ I, f i (S ∩ B i)) = ∏ i ∈ I, modelMean (B i) (f i) := by
  rw [modelMean_eq_of_subset hA fun S _ => prod_congr rfl fun i hi => by
    rw [inter_assoc, inter_eq_right.2 (subset_biUnion_of_mem B hi)]]
  clear hA
  induction I using Finset.induction_on with
  | empty => simp [modelMean_empty]
  | insert i₀ I hi₀ ih =>
    have hB' : (I : Set ι).PairwiseDisjoint B := hB.subset (by simp)
    have hdisj : Disjoint (B i₀) (I.biUnion B) := by
      rw [disjoint_biUnion_right]
      intro i hi
      exact hB (by simp) (by simp [hi]) (fun h => hi₀ (h ▸ hi))
    rw [biUnion_insert, modelMean_union hdisj, prod_insert hi₀, ← ih hB', mul_comm,
      ← modelMean_mul_left]
    refine modelMean_congr fun S hS => ?_
    rw [mul_comm, ← modelMean_mul_left]
    refine modelMean_congr fun T hT => ?_
    rw [prod_insert hi₀]
    have hT0 : T ∩ B i₀ = ∅ :=
      disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left hT hdisj.symm)
    congr 1
    · rw [union_inter_distrib_right, inter_eq_left.2 hS, hT0, union_empty]
    · refine prod_congr rfl fun i hi => ?_
      have hS0 : S ∩ B i = ∅ := disjoint_iff_inter_eq_empty.1
        (disjoint_of_subset_left hS (hB (by simp) (by simp [hi]) fun h => hi₀ (h ▸ hi)))
      rw [union_inter_distrib_right, hS0, empty_union]

/-! ### Two explicit means -/

/-- `E_A[t^{|S|}] = ∏_{p ∈ A} (1 - (1 - t)/p)`. -/
lemma modelMean_pow_card (A : Finset ℕ) (t : ℝ) :
    modelMean A (fun S => t ^ #S) = ∏ p ∈ A, (1 - (1 - t) / p) := by
  have h := prod_add (fun p : ℕ => t * ((1 : ℝ) / p)) (fun p => 1 - (1 : ℝ) / p) A
  rw [modelMean]
  convert h.symm using 1
  · refine sum_congr rfl fun S _ => ?_
    rw [modelWeight, prod_mul_distrib, prod_const]
    ring
  · exact prod_congr rfl fun p _ => by ring

/-- The marked count `|S| t^{|S| - 1}` has mean at least
`(∑_{p ∈ A} 1/p) ∏_{p ∈ A} (1 - (1 - t)/p)` for `0 ≤ t ≤ 1`. -/
lemma le_modelMean_card_mul_zpow {A : Finset ℕ} (hA : ∀ p ∈ A, 0 < p) {t : ℝ} (ht : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    (∑ p ∈ A, (1 : ℝ) / p) * ∏ p ∈ A, (1 - (1 - t) / p) ≤
      modelMean A (fun S => t ^ ((#S : ℤ) - 1) * #S) := by
  -- the factors lie in `[0, 1]`
  have hfac : ∀ p ∈ A, 0 ≤ 1 - (1 - t) / p ∧ 1 - (1 - t) / p ≤ 1 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hA p hp
    constructor
    · rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    · have : 0 ≤ (1 - t) / p := div_nonneg (by linarith) (by linarith)
      linarith
  -- `|S| t^{|S| - 1} = ∑_{p ∈ A} [p ∈ S] t^{|S \ {p}|}` on subsets of `A`
  have hid : ∀ S ⊆ A, t ^ ((#S : ℤ) - 1) * #S =
      ∑ p ∈ A, if p ∈ S then t ^ #(S.erase p) else 0 := by
    intro S hS
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 hS]
    rcases S.eq_empty_or_nonempty with h | h
    · simp [h]
    · have hc : 1 ≤ #S := card_pos.2 h
      have hz : t ^ ((#S : ℤ) - 1) = t ^ (#S - 1) := by
        rw [← zpow_natCast, Nat.cast_sub hc, Nat.cast_one]
      rw [hz, sum_congr rfl fun p hp => by rw [card_erase_of_mem hp], sum_const, nsmul_eq_mul,
        mul_comm]
  rw [modelMean_congr hid, modelMean_sum, sum_mul]
  refine sum_le_sum fun p hp => ?_
  -- the mean of `[p ∈ S] t^{|S \ {p}|}` is `(1/p) ∏_{A \ {p}} (1 - (1 - t)/p')`
  have hpA : p ∉ A.erase p := notMem_erase p A
  have hA' : insert p (A.erase p) = A := insert_erase hp
  conv_rhs => rw [← hA', modelMean_insert hpA]
  have h0 : modelMean (A.erase p) (fun S => if p ∈ S then t ^ #(S.erase p) else 0) = 0 := by
    rw [modelMean_congr (g := fun _ => (0 : ℝ)) fun S hS => ite_eq_right fun h => hpA (hS h)]
    exact modelMean_const _ 0
  have h1 : modelMean (A.erase p) (fun T => if p ∈ insert p T then t ^ #((insert p T).erase p)
      else 0) = modelMean (A.erase p) fun T => t ^ #T := by
    refine modelMean_congr fun T hT => ?_
    rw [ite_eq_left (mem_insert_self p T), erase_insert fun h => hpA (hT h)]
  rw [h0, h1, modelMean_pow_card, mul_zero, zero_add, ← prod_erase_mul _ _ hp]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hnn : 0 ≤ ∏ x ∈ A.erase p, (1 - (1 - t) / x) :=
    prod_nonneg fun q hq => (hfac q (mem_of_mem_erase hq)).1
  calc (∏ x ∈ A.erase p, (1 - (1 - t) / x)) * (1 - (1 - t) / p)
      ≤ (∏ x ∈ A.erase p, (1 - (1 - t) / x)) * 1 :=
        mul_le_mul_of_nonneg_left (hfac p hp).2 hnn
    _ = ∏ x ∈ A.erase p, (1 - (1 - t) / x) := mul_one _

/-! ### Marginals -/

/-- The probability that a given `p ∈ A` divides is `1/p`. -/
lemma sum_modelWeight_mem {A : Finset ℕ} {p : ℕ} (hp : p ∈ A) :
    ∑ S ∈ A.powerset with p ∈ S, modelWeight A S = 1 / p := by
  have h : ∑ S ∈ A.powerset with p ∈ S, modelWeight A S =
      modelMean A fun S => if p ∈ S then 1 else 0 := by
    rw [modelMean, sum_filter]
    exact sum_congr rfl fun S _ => by split_ifs <;> simp
  rw [h, ← insert_erase hp, modelMean_insert (notMem_erase p A)]
  have h0 : modelMean (A.erase p) (fun S => if p ∈ S then (1 : ℝ) else 0) = 0 := by
    rw [modelMean_congr (g := fun _ => (0 : ℝ)) fun S hS =>
      ite_eq_right fun h => notMem_erase p A (hS h)]
    exact modelMean_const _ 0
  rw [h0, modelMean_congr (g := fun _ => (1 : ℝ)) fun T _ => ite_eq_left (mem_insert_self p T),
    modelMean_const]
  ring

/-- Removing primes `R ⊆ A`: for `S ⊆ A \ R`, `π_A(S) = π_{A \ R}(S) ∏_{p ∈ R} (1 - 1/p)`. -/
lemma modelWeight_sdiff {A R S : Finset ℕ} (hRA : R ⊆ A) (hS : S ⊆ A \ R) :
    modelWeight A S = modelWeight (A \ R) S * ∏ p ∈ R, (1 - (1 : ℝ) / p) := by
  have h : A \ S = ((A \ R) \ S) ∪ R := by
    ext p
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hA, hS'⟩
      by_cases hR : p ∈ R
      · exact Or.inr hR
      · exact Or.inl ⟨⟨hA, hR⟩, hS'⟩
    · rintro (⟨⟨hA, -⟩, hS'⟩ | hR)
      · exact ⟨hA, hS'⟩
      · exact ⟨hRA hR, fun h => (mem_sdiff.1 (hS h)).2 hR⟩
  have hd : Disjoint ((A \ R) \ S) R := disjoint_left.2 fun p hp hR =>
    (mem_sdiff.1 (mem_sdiff.1 hp).1).2 hR
  rw [modelWeight, modelWeight, h, prod_union hd]
  ring

end

end Sieve

end Erdos408
