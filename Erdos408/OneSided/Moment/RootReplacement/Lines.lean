import Erdos408.OneSided.Moment.Lines
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The kernel lines of `SL₂(ℤ/S)` are independent and uniform

RR5 of `blueprint/one_sided_type_ii.md` §15 (PD Lemma 3.3′). For `g ∈ SL₂(ℤ/S)` and a prime
`p ∣ S`, the kernel line of the first row `(u, c)` of `g` modulo `p` is `[(c, -u)]_p`
(`matLine`). For `S = ∏_{p ∈ P} p` a product of distinct band primes, the average over
`SL₂(ℤ/S)` of a function of these lines is the average over independent uniform lines.

Every unimodular row `(u, c)` over `ℤ/S` is the first row of exactly `S` matrices of
`SL₂(ℤ/S)`. By the Chinese remainder theorem a row is unimodular when it is nonzero modulo
every `p ∣ S`, and each projective line mod `p` contains `p - 1` nonzero rows. So every
assignment of lines at the primes of `P` comes from exactly `S ∏_{p ∈ P} (p - 1)` matrices.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

open scoped Classical in
/-- The line assignments at the primes of `Q`: a line `ℓ p ∈ {0, …, p}` for each `p ∈ Q`, and
`0` elsewhere. -/
def lineSet (Q : Finset ℕ) : Finset (ℕ → ℕ) :=
  (Q.pi fun p => range (p + 1)).image fun f p => if h : p ∈ Q then f p h else 0

/-- The line assignments are the line assignments at the band primes. -/
theorem lineAssignments_eq_lineSet (x : ℝ) (d : Data K) :
    lineAssignments x d = lineSet (bandPrimes x d) := rfl

/-- `ℓ` is a line assignment at the primes of `Q` iff `ℓ p ≤ p` on `Q` and `ℓ p = 0` off `Q`. -/
theorem mem_lineSet {Q : Finset ℕ} {ℓ : ℕ → ℕ} :
    ℓ ∈ lineSet Q ↔ (∀ p ∈ Q, ℓ p ≤ p) ∧ ∀ p ∉ Q, ℓ p = 0 := by
  classical
  rw [lineSet, mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun p hp => ?_, fun p hp => by simp [hp]⟩
    simpa [hp, Nat.lt_succ_iff] using mem_pi.1 hf p hp
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun p _ => ℓ p, mem_pi.2 fun p hp => mem_range.2 (Nat.lt_succ_of_le (h₁ p hp)), ?_⟩
    funext p
    by_cases hp : p ∈ Q <;> simp [hp, h₂]

/-- If every point of `t` has `N ≠ 0` preimages in `s` under `f`, then the average of `F ∘ f`
over `s` is the average of `F` over `t`. -/
theorem average_comp_eq {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β} {f : α → β}
    (hf : ∀ x ∈ s, f x ∈ t) {N : ℕ} (hN : ∀ y ∈ t, #{x ∈ s | f x = y} = N) (hN0 : N ≠ 0)
    (F : β → ℂ) :
    ((#s : ℂ))⁻¹ * ∑ x ∈ s, F (f x) = ((#t : ℂ))⁻¹ * ∑ y ∈ t, F y := by
  have hs : #s = #t * N := by
    rw [card_eq_sum_card_fiberwise hf, sum_congr rfl hN, sum_const, smul_eq_mul]
  have hsum : ∑ x ∈ s, F (f x) = N * ∑ y ∈ t, F y := by
    rw [← sum_fiberwise_of_maps_to hf, mul_sum]
    refine sum_congr rfl fun y hy => ?_
    rw [sum_congr rfl fun x hx => by rw [(mem_filter.1 hx).2], sum_const, hN y hy, nsmul_eq_mul]
  have hN0' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN0
  rw [hs, hsum, Nat.cast_mul, mul_inv, mul_assoc, ← mul_assoc (N : ℂ)⁻¹, inv_mul_cancel₀ hN0',
    one_mul]

/-- The first row of an element of `SL₂(R)` is unimodular. -/
theorem isCoprime_row {R : Type*} [CommRing R] (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    IsCoprime (g 0 0) (g 0 1) := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  exact ⟨g 1 1, -g 1 0, by linear_combination h⟩

/-- A row `(u, c)` with `a u + b c = 1` is the first row of exactly `|R|` elements of `SL₂(R)`:
the second rows are `(-b + t u, a + t c)` for `t ∈ R`. -/
theorem card_filter_row_eq {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] {u c : R}
    (h : IsCoprime u c) :
    #{g : Matrix.SpecialLinearGroup (Fin 2) R | g 0 0 = u ∧ g 0 1 = c} = Fintype.card R := by
  obtain ⟨a, b, hab⟩ := h
  -- step: the matrix with second row `(-b + t u, a + t c)`
  let i : R → Matrix.SpecialLinearGroup (Fin 2) R := fun t =>
    ⟨!![u, c; -b + t * u, a + t * c], by rw [Matrix.det_fin_two_of]; linear_combination hab⟩
  rw [← card_univ]
  refine (card_nbij' i (fun g => a * g 1 0 + b * g 1 1) (fun t _ => ?_) (fun g _ => mem_univ _)
    (fun t _ => ?_) (fun g hg => ?_)).symm
  · exact mem_coe.2 (mem_filter.2 ⟨mem_univ _, rfl, rfl⟩)
  · simp only [i]
    simp
    linear_combination t * hab
  · obtain ⟨hu, hc⟩ := (mem_filter.1 hg).2
    have hdet := g.2
    rw [Matrix.det_fin_two, hu, hc] at hdet
    refine Subtype.ext ?_
    ext k l
    fin_cases k <;> fin_cases l
    · simp [i, hu]
    · simp [i, hc]
    · simp [i]
      linear_combination b * hdet + g 1 0 * hab
    · simp [i]
      linear_combination -a * hdet + g 1 1 * hab

/-- The kernel line `[(c, -u)]_p` of the first row `(u, c)` of `g` modulo `p`. -/
def matLine {S : ℕ} (p : ℕ) (g : Matrix (Fin 2) (Fin 2) (ZMod S)) : ℕ :=
  lineOf p (((g 0 1).val : ℤ), -((g 0 0).val : ℤ))

/-- The kernel line `[(c, -u)]_p` of a row `z = (u, c)` over `ℤ/p`. -/
def localLine (p : ℕ) (z : ZMod p × ZMod p) : ℕ :=
  if z.2 = 0 then p else (-z.1 * z.2⁻¹).val

/-- `matLine` is the local line of the first row reduced modulo `p`. -/
theorem matLine_eq {S : ℕ} (p : ℕ) (g : Matrix (Fin 2) (Fin 2) (ZMod S)) :
    matLine p g = localLine p (((g 0 0).val : ZMod p), ((g 0 1).val : ZMod p)) := by
  simp only [matLine, lineOf, localLine, Int.cast_natCast, Int.cast_neg, neg_mul]

/-- A local line is at most `p`. -/
theorem localLine_le {p : ℕ} [NeZero p] (z : ZMod p × ZMod p) : localLine p z ≤ p := by
  unfold localLine
  split_ifs
  · exact le_rfl
  · exact (ZMod.val_lt _).le

/-- Over `ℤ/p`, each line `l ≤ p` contains exactly `p - 1` nonzero rows. -/
theorem card_localLine_eq {p : ℕ} [NeZero p] (hp : p.Prime) {l : ℕ} (hl : l ≤ p) :
    #{z : ZMod p × ZMod p | z ≠ 0 ∧ localLine p z = l} = p - 1 := by
  have := Fact.mk hp
  have hcard : #(univ.erase (0 : ZMod p)) = p - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  rw [← hcard]
  rcases hl.lt_or_eq with hl | hl
  · -- step: for `l < p`, the line consists of the rows `(-l y, y)`, `y ≠ 0`
    have hiff : ∀ z : ZMod p × ZMod p,
        z ≠ 0 ∧ localLine p z = l ↔ z.2 ≠ 0 ∧ z.1 = -(l : ZMod p) * z.2 := by
      intro z
      by_cases hz : z.2 = 0
      · simp only [localLine, hz, ↓reduceIte, hl.ne', and_false, ne_eq, not_true_eq_false,
          false_and]
      · have hz' : z ≠ 0 := fun h => hz (by rw [h]; rfl)
        simp only [localLine, hz, ↓reduceIte, ne_eq, hz', not_false_eq_true, true_and]
        have hval : ∀ w : ZMod p, w.val = l ↔ w = l := fun w =>
          ⟨fun h => by rw [← h, ZMod.natCast_zmod_val], fun h => by rw [h, ZMod.val_cast_of_lt hl]⟩
        rw [hval]
        have hu : IsUnit z.2 := isUnit_iff_ne_zero.2 hz
        constructor
        · intro h
          rw [← h]
          linear_combination -z.1 * ZMod.inv_mul_of_unit z.2 hu
        · intro h
          rw [h]
          linear_combination (l : ZMod p) * ZMod.mul_inv_of_unit z.2 hu
    refine card_nbij' Prod.snd (fun y => (-(l : ZMod p) * y, y)) (fun z hz => ?_)
      (fun y hy => ?_) (fun z hz => ?_) (fun y _ => rfl)
    · exact mem_coe.2 (mem_erase.2 ⟨((hiff z).1 (mem_filter.1 hz).2).1, mem_univ _⟩)
    · exact mem_coe.2 (mem_filter.2 ⟨mem_univ _, (hiff _).2 ⟨ne_of_mem_erase hy, rfl⟩⟩)
    · exact Prod.ext ((hiff z).1 (mem_filter.1 hz).2).2.symm rfl
  · -- step: the line `p` consists of the rows `(x, 0)`, `x ≠ 0`
    rw [hl]
    have hiff : ∀ z : ZMod p × ZMod p, z ≠ 0 ∧ localLine p z = p ↔ z.1 ≠ 0 ∧ z.2 = 0 := by
      intro z
      by_cases hz : z.2 = 0
      · simp only [localLine, hz, ↓reduceIte, and_true, ne_eq]
        exact not_congr ⟨fun h => by rw [h]; rfl, fun h => Prod.ext h hz⟩
      · simp only [localLine, hz, ↓reduceIte, (ZMod.val_lt _).ne, and_false]
    refine card_nbij' Prod.fst (fun x => (x, 0)) (fun z hz => ?_) (fun x hx => ?_)
      (fun z hz => ?_) (fun x _ => rfl)
    · exact mem_coe.2 (mem_erase.2 ⟨((hiff z).1 (mem_filter.1 hz).2).1, mem_univ _⟩)
    · exact mem_coe.2 (mem_filter.2 ⟨mem_univ _, (hiff _).2 ⟨ne_of_mem_erase hx, rfl⟩⟩)
    · exact Prod.ext rfl ((hiff z).1 (mem_filter.1 hz).2).2.symm

/-- Reduction `ℤ/S → ∏_{p ∈ P} ℤ/p` modulo the primes of `P`, for `S = ∏_{p ∈ P} p`. -/
def reduce {P : Finset ℕ} {S : ℕ} (hS : ∏ p ∈ P, p = S) : ZMod S →+* ∀ p : P, ZMod p :=
  RingHom.pi fun p => ZMod.castHom (by rw [← hS]; exact dvd_prod_of_mem (fun p => p) p.2) _

/-- The reduction of `x` modulo `p` is the cast of its representative. -/
theorem reduce_apply {P : Finset ℕ} {S : ℕ} [NeZero S] (hS : ∏ p ∈ P, p = S) (x : ZMod S)
    (p : P) : reduce hS x p = (x.val : ZMod p) :=
  ZMod.cast_eq_val x

/-- **Chinese remainder theorem**: for `S = ∏_{p ∈ P} p` with `P` a set of primes, the
reduction `ℤ/S → ∏_{p ∈ P} ℤ/p` is bijective. -/
theorem bijective_reduce {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {S : ℕ} [NeZero S]
    (hS : ∏ p ∈ P, p = S) : Function.Bijective (reduce hS) := by
  have : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(hP p p.2).ne_zero⟩
  have hinj : Function.Injective (reduce hS) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have hdvd : ∏ p ∈ P, p ∣ x.val := by
      refine prod_primes_dvd _ (fun p hp => (hP p hp).prime) fun p hp => ?_
      have := congrFun hx ⟨p, hp⟩
      rwa [reduce_apply, Pi.zero_apply, ZMod.natCast_eq_zero_iff] at this
    rw [hS] at hdvd
    exact (ZMod.val_eq_zero x).1 (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt x))
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩
  rw [Fintype.card_pi, ZMod.card, ← hS, ← prod_coe_sort]
  exact prod_congr rfl fun p _ => (ZMod.card _).symm

open scoped Classical in
/-- For every assignment `m` of lines at the primes of `P`, exactly `∏_{p ∈ P} (p - 1)`
unimodular rows over `ℤ/S` have kernel line `m p` modulo every `p ∈ P`: by the Chinese
remainder theorem a row is unimodular iff it is nonzero modulo every `p ∈ P`. -/
theorem card_rows_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {S : ℕ} [NeZero S]
    (hS : ∏ p ∈ P, p = S) {m : ℕ → ℕ} (hm : ∀ p ∈ P, m p ≤ p) :
    #{r : ZMod S × ZMod S | IsCoprime r.1 r.2 ∧
        ∀ p ∈ P, localLine p ((r.1.val : ZMod p), (r.2.val : ZMod p)) = m p} =
      ∏ p ∈ P, (p - 1) := by
  have : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(hP p p.2).ne_zero⟩
  have hψ := bijective_reduce hP hS
  set ψ := reduce hS
  set B : ∀ p : P, Finset (ZMod p × ZMod p) := fun p => {z | z ≠ 0 ∧ localLine p z = m p}
  -- step: a row is unimodular iff it is nonzero modulo every `p ∈ P`
  have hco : ∀ u c : ZMod S, IsCoprime u c ↔ ∀ p : P, (ψ u p, ψ c p) ≠ 0 := by
    intro u c
    constructor
    · rintro ⟨a, b, hab⟩ p h
      have := Fact.mk (hP p p.2)
      have h' := congrFun (congrArg ψ hab) p
      simp only [map_add, map_mul, map_one, Pi.add_apply, Pi.mul_apply, Pi.one_apply,
        Prod.mk_eq_zero.1 h, mul_zero, add_zero] at h'
      exact zero_ne_one h'
    · intro h
      have hp : ∀ p : P, IsCoprime (ψ u p) (ψ c p) := by
        intro p
        have := Fact.mk (hP p p.2)
        by_cases hu : ψ u p = 0
        · have hc : ψ c p ≠ 0 := fun hc => h p (by rw [hu, hc]; rfl)
          exact ⟨0, (ψ c p)⁻¹, by simp [hc]⟩
        · exact ⟨(ψ u p)⁻¹, 0, by simp [hu]⟩
      choose a b hab using hp
      obtain ⟨a', ha'⟩ := hψ.2 a
      obtain ⟨b', hb'⟩ := hψ.2 b
      refine ⟨a', b', hψ.1 ?_⟩
      rw [map_add, map_mul, map_mul, map_one, ha', hb']
      exact funext hab
  -- step: the rows with lines `m` correspond to the tuples of rows in `B p`
  have hmem : ∀ r : ZMod S × ZMod S, (IsCoprime r.1 r.2 ∧
      ∀ p ∈ P, localLine p ((r.1.val : ZMod p), (r.2.val : ZMod p)) = m p) ↔
        (fun p => (ψ r.1 p, ψ r.2 p)) ∈ Fintype.piFinset B := by
    intro r
    simp only [hco, Fintype.mem_piFinset, B, mem_filter, mem_univ, true_and, ψ, reduce_apply,
      Subtype.forall, forall_and]
  rw [← prod_coe_sort, ← prod_congr rfl fun (p : P) _ => card_localLine_eq (hP p p.2) (hm p p.2),
    ← Fintype.card_piFinset]
  refine card_nbij (fun r p => (ψ r.1 p, ψ r.2 p)) (fun r hr => ?_) (fun r _ r' _ h => ?_)
    (fun x hx => ?_)
  · exact (hmem r).1 (mem_filter.1 hr).2
  · exact Prod.ext (hψ.1 (funext fun p => congrArg Prod.fst (congrFun h p)))
      (hψ.1 (funext fun p => congrArg Prod.snd (congrFun h p)))
  · obtain ⟨u, hu⟩ := hψ.2 fun p => (x p).1
    obtain ⟨c, hc⟩ := hψ.2 fun p => (x p).2
    have hx' : (fun p => (ψ (u, c).1 p, ψ (u, c).2 p)) = x := by
      funext p
      simp only [hu, hc]
    refine ⟨(u, c), mem_filter.2 ⟨mem_univ _, (hmem _).2 ?_⟩, hx'⟩
    rw [hx']
    exact hx

/-- Every assignment `m` of lines at the primes of `P` is the assignment of kernel lines of
exactly `S ∏_{p ∈ P} (p - 1)` elements of `SL₂(ℤ/S)`. -/
theorem card_matLine_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {S : ℕ} [NeZero S]
    (hS : ∏ p ∈ P, p = S) {m : ℕ → ℕ} (hm : ∀ p ∈ P, m p ≤ p) :
    #{g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) | ∀ p ∈ P, matLine p g.1 = m p} =
      S * ∏ p ∈ P, (p - 1) := by
  classical
  rw [← card_rows_eq hP hS hm, mul_comm, ← smul_eq_mul, ← sum_const]
  refine (card_eq_sum_card_fiberwise (f := fun g => (g 0 0, g 0 1)) fun g hg => ?_).trans
    (sum_congr rfl fun r hr => ?_)
  · exact mem_filter.2 ⟨mem_univ _, isCoprime_row g, fun p hp => by
      rw [← matLine_eq]; exact (mem_filter.1 hg).2 p hp⟩
  rw [filter_filter]
  refine ((congrArg card (filter_congr fun g _ => ?_)).trans
    (card_filter_row_eq (mem_filter.1 hr).2.1)).trans (ZMod.card S)
  constructor
  · rintro ⟨-, h⟩
    rw [← h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun p hp => ?_, Prod.ext h₁ h₂⟩
    rw [matLine_eq, h₁, h₂]
    exact (mem_filter.1 hr).2.2 p hp

/-- **RR5 (lines)**: for `S = ∏_{p ∈ P} p` with `P` a set of band primes, and `G` depending
only on the lines at the primes of `P`, the average of `G` at the kernel lines over
`SL₂(ℤ/S)` is the average over independent uniform lines. -/
theorem average_matLine_eq_lineAverage (x : ℝ) (d : Data K) {P : Finset ℕ}
    (hP : P ⊆ bandPrimes x d) (S : ℕ) [NeZero S] (hS : ∏ p ∈ P, p = S) (G : (ℕ → ℕ) → ℂ)
    (hG : ∀ ℓ ℓ' : ℕ → ℕ, (∀ p ∈ P, ℓ p = ℓ' p) → G ℓ = G ℓ') :
    ((Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℂ))⁻¹ *
        ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S), G (fun p => matLine p g.1) =
      lineAverage x d G := by
  classical
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => by
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 (hP hp)
    exact prime_of_mem_band hi
  -- step: restriction of a line assignment to the primes of `P`
  set ρ : (ℕ → ℕ) → ℕ → ℕ := fun ℓ p => if p ∈ P then ℓ p else 0
  have hρ : ∀ ℓ, G (ρ ℓ) = G ℓ := fun ℓ => hG _ _ fun p hp => by simp [ρ, hp]
  have hρmem : ∀ ℓ : ℕ → ℕ, (∀ p ∈ P, ℓ p ≤ p) → ρ ℓ ∈ lineSet P := fun ℓ h =>
    mem_lineSet.2 ⟨fun p hp => by simpa [ρ, hp] using h p hp, fun p hp => by simp [ρ, hp]⟩
  have hρeq : ∀ ℓ m : ℕ → ℕ, m ∈ lineSet P → (ρ ℓ = m ↔ ∀ p ∈ P, ℓ p = m p) := by
    intro ℓ m hm
    constructor
    · rintro rfl p hp
      simp [ρ, hp]
    · intro h
      funext p
      by_cases hp : p ∈ P
      · simp [ρ, hp, h p hp]
      · simp [ρ, hp, (mem_lineSet.1 hm).2 p hp]
  -- step: the average over `SL₂(ℤ/S)` is the average over `lineSet P`
  have h₁ : ((Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℂ))⁻¹ *
      ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S), G (fun p => matLine p g.1) =
        ((#(lineSet P) : ℂ))⁻¹ * ∑ m ∈ lineSet P, G m := by
    rw [← card_univ, ← sum_congr rfl fun g _ => hρ (fun p => matLine p g.1)]
    refine average_comp_eq (fun g _ => hρmem _ fun p hp => ?_) (N := S * ∏ p ∈ P, (p - 1))
      (fun m hm => ?_) ?_ G
    · have : NeZero p := ⟨(hPp p hp).ne_zero⟩
      rw [matLine_eq]
      exact localLine_le _
    · rw [← card_matLine_eq hPp hS (mem_lineSet.1 hm).1]
      exact congrArg card (filter_congr fun g _ => hρeq _ m hm)
    · refine mul_ne_zero (NeZero.ne S) (prod_ne_zero_iff.2 fun p hp => ?_)
      have := (hPp p hp).two_le
      omega
  -- step: the line average is the average over `lineSet P`
  have h₂ : lineAverage x d G = ((#(lineSet P) : ℂ))⁻¹ * ∑ m ∈ lineSet P, G m := by
    rw [lineAverage, lineAssignments_eq_lineSet, ← sum_congr rfl fun ℓ _ => hρ ℓ]
    refine average_comp_eq (fun ℓ hℓ => hρmem ℓ fun p hp => (mem_lineSet.1 hℓ).1 p (hP hp))
      (N := #(lineSet (bandPrimes x d \ P))) (fun m hm => ?_)
      (card_ne_zero_of_mem (s := lineSet (bandPrimes x d \ P)) (a := 0)
        (mem_lineSet.2 ⟨fun p _ => Nat.zero_le p, fun _ _ => rfl⟩)) G
    have hm' := mem_lineSet.1 hm
    -- step: the fibre over `m` is a copy of the line assignments off `P`
    refine card_nbij' (fun ℓ p => if p ∈ P then 0 else ℓ p) (fun k p => if p ∈ P then m p else k p)
      (fun ℓ hℓ => ?_) (fun k hk => ?_) (fun ℓ hℓ => ?_) (fun k hk => ?_)
    · obtain ⟨hℓ, -⟩ := mem_filter.1 hℓ
      refine mem_coe.2 (mem_lineSet.2 ⟨fun p hp => ?_, fun p hp => ?_⟩)
      · simp [(mem_sdiff.1 hp).2, (mem_lineSet.1 hℓ).1 p (mem_sdiff.1 hp).1]
      · by_cases hpP : p ∈ P
        · simp [hpP]
        · simp only [hpP, ↓reduceIte]
          exact (mem_lineSet.1 hℓ).2 p fun h => hp (mem_sdiff.2 ⟨h, hpP⟩)
    · have hk' := mem_lineSet.1 (mem_coe.1 hk)
      refine mem_coe.2 (mem_filter.2 ⟨mem_lineSet.2 ⟨fun p hp => ?_, fun p hp => ?_⟩, ?_⟩)
      · by_cases hpP : p ∈ P
        · simpa [hpP] using hm'.1 p hpP
        · simpa [hpP] using hk'.1 p (mem_sdiff.2 ⟨hp, hpP⟩)
      · have hpP : p ∉ P := fun h => hp (hP h)
        simpa [hpP] using hk'.2 p fun h => hp (mem_sdiff.1 h).1
      · funext p
        by_cases hpP : p ∈ P
        · simp [ρ, hpP]
        · simp [ρ, hpP, hm'.2 p hpP]
    · obtain ⟨-, hρℓ⟩ := mem_filter.1 (mem_coe.1 hℓ)
      funext p
      by_cases hpP : p ∈ P
      · simp only [hpP, ↓reduceIte]
        rw [← hρℓ]
        simp [ρ, hpP]
      · simp [hpP]
    · have hk' := mem_lineSet.1 (mem_coe.1 hk)
      funext p
      by_cases hpP : p ∈ P
      · simp [hpP, hk'.2 p fun h => (mem_sdiff.1 h).2 hpP]
      · simp [hpP]
  rw [h₁, h₂]

end Erdos408.OneSided
