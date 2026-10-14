import Mathlib

/-!
# Sieve calculus: one-block inclusion–exclusion and product telescoping

Combinatorial core of the proof of the block sieve (`lem:sieve` in
`01-preliminaries.tex`, "An elementary weighted sieve"). The analytic half
(independent-probability expectations, the `O(e^{-h})` error and the counting
conclusion `eq:block-sieve`, and the rough-integer corollary
`lem:rough-sieve-polynomial`) will follow in `BlockSieve.lean` on top of
these algebraic identities.

For one block with `t` bad conditions holding and (even) truncation degree
`h`, the inclusion–exclusion polynomial through degree `h` evaluates to
`U(t) = ∑_{a=0}^{min(h,t)} (-1)^a C(t,a)`, which is `1` for `t = 0` and
`C(t-1,h)` for `t ≥ 1` (the paper's displayed computation). Hence
`U ≥ 1_{t=0}` with overcount `U - 1_{t=0} ≤ C(t,h+1)`, and telescoping a
product of nonnegative block factors gives the paper's
`0 ≤ ∏ U_j - ∏ I_j ≤ ∑_j E_j ∏_{k≠j} U_k`.
-/

namespace Erdos821
namespace Prelim
namespace SieveCalculus

open Finset

/-- One-block truncated inclusion–exclusion sum: `U(t)` for truncation
degree `h` and `t` bad conditions holding. Terms with `a > t` vanish, so
this is `∑_{a=0}^{min(h,t)} (-1)^a C(t,a)`. -/
def blockUpper (h t : ℕ) : ℤ :=
  ∑ a ∈ Finset.range (h + 1), (-1 : ℤ) ^ a * (t.choose a : ℤ)

/-- Closed form at `t = n + 1`: the whole sum collapses to the top term.
This is the paper's `U_j = C(t-1,h_j)` computation (up to the `(-1)^h`
sign, which is `1` for the paper's even `h_j`). -/
theorem blockUpper_succ (h n : ℕ) :
    blockUpper h (n + 1) = (-1 : ℤ) ^ h * (n.choose h : ℤ) := by
  have hS1 : (∑ b ∈ Finset.range h, (-1 : ℤ) ^ b * ((n.choose b : ℕ) : ℤ))
      = (∑ b ∈ Finset.range (h + 1), (-1 : ℤ) ^ b * ((n.choose b : ℕ) : ℤ))
        - (-1 : ℤ) ^ h * ((n.choose h : ℕ) : ℤ) := by
    rw [Finset.sum_range_succ]
    ring
  have hS2 : (∑ b ∈ Finset.range h, (-1 : ℤ) ^ b * ((n.choose (b + 1) : ℕ) : ℤ))
      = -((∑ b ∈ Finset.range (h + 1), (-1 : ℤ) ^ b * ((n.choose b : ℕ) : ℤ))
        - 1) := by
    have e1 : ∀ b : ℕ, (-1 : ℤ) ^ b * ((n.choose (b + 1) : ℕ) : ℤ)
        = -((-1 : ℤ) ^ (b + 1) * ((n.choose (b + 1) : ℕ) : ℤ)) := by
      intro b
      rw [pow_succ]
      ring
    simp only [e1, Finset.sum_neg_distrib]
    congr 1
    have hpeel := Finset.sum_range_succ'
      (fun b => (-1 : ℤ) ^ b * ((n.choose b : ℕ) : ℤ)) h
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul] at hpeel
    linarith
  have hsplit : (∑ b ∈ Finset.range h,
        (-1 : ℤ) ^ (b + 1) * (((n + 1).choose (b + 1) : ℕ) : ℤ))
      = -(∑ b ∈ Finset.range h, (-1 : ℤ) ^ b * ((n.choose b : ℕ) : ℤ))
        - (∑ b ∈ Finset.range h, (-1 : ℤ) ^ b * ((n.choose (b + 1) : ℕ) : ℤ)) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [pow_succ, Nat.choose_succ_succ', Nat.cast_add]
    ring
  unfold blockUpper
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
  show (∑ b ∈ Finset.range h,
      (-1 : ℤ) ^ (b + 1) * (((n + 1).choose (b + 1) : ℕ) : ℤ)) + 1
      = (-1 : ℤ) ^ h * ((n.choose h : ℕ) : ℤ)
  rw [hsplit, hS1, hS2]
  ring

/-- Value at `t = 0`: only the empty monomial contributes. -/
theorem blockUpper_zero (h : ℕ) : blockUpper h 0 = 1 := by
  have hvan : ∀ b ∈ Finset.range (h + 1), b ≠ 0 →
      (-1 : ℤ) ^ b * (((0 : ℕ).choose b : ℕ) : ℤ) = 0 := by
    intro b _ hb0
    rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb0), Nat.cast_zero, mul_zero]
  unfold blockUpper
  rw [Finset.sum_eq_single 0 hvan]
  · simp
  · intro hc
    simp at hc

/-- Paper's displayed formula: `1` at `t = 0`, `(-1)^h C(t-1,h)` at `t ≥ 1`. -/
theorem blockUpper_eq (h t : ℕ) :
    blockUpper h t
      = if t = 0 then 1 else (-1 : ℤ) ^ h * (((t - 1).choose h : ℕ) : ℤ) := by
  cases t with
  | zero =>
    rw [if_pos rfl]
    exact blockUpper_zero h
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero n)]
    exact blockUpper_succ h n

/-- For even `h` (the paper's `h_j` are even) and `t ≥ 1`: `U(t) = C(t-1,h)`. -/
theorem blockUpper_of_even (h t : ℕ) (he : Even h) (ht : 1 ≤ t) :
    blockUpper h t = (((t - 1).choose h : ℕ) : ℤ) := by
  have ht' : t - 1 + 1 = t := Nat.sub_add_cancel ht
  conv_lhs => rw [← ht']
  rw [blockUpper_succ, he.neg_one_pow, one_mul]

/-- Nonnegativity for `t ≥ 1` (towards `U_j ≥ I_j`). -/
theorem blockUpper_nonneg_of_even (h t : ℕ) (he : Even h) (ht : 1 ≤ t) :
    0 ≤ blockUpper h t := by
  rw [blockUpper_of_even h t he ht]
  exact Nat.cast_nonneg _

/-- The paper's `U_j ≥ I_j`: the block polynomial dominates avoidance. -/
theorem blockUpper_ge_indicator (h t : ℕ) (he : Even h) :
    (if t = 0 then (1 : ℤ) else 0) ≤ blockUpper h t := by
  by_cases ht : t = 0
  · subst ht
    simp [blockUpper_zero]
  · have ht1 : 1 ≤ t := Nat.pos_of_ne_zero ht
    rw [if_neg ht, blockUpper_of_even h t he ht1]
    exact Nat.cast_nonneg _

/-- The paper's `U_j - I_j ≤ E_j`: overcount bounded by the degree-`h+1`
monomial sum `C(t,h+1)`, via Pascal's rule. -/
theorem blockUpper_sub_indicator_le_error (h t : ℕ) (he : Even h) :
    blockUpper h t - (if t = 0 then (1 : ℤ) else 0)
      ≤ ((t.choose (h + 1) : ℕ) : ℤ) := by
  by_cases ht : t = 0
  · subst ht
    have e : Nat.choose 0 (h + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [blockUpper_zero, e]
  · have ht1 : 1 ≤ t := Nat.pos_of_ne_zero ht
    rw [if_neg ht, blockUpper_of_even h t he ht1, sub_zero]
    have hpascal : t.choose (h + 1)
        = (t - 1).choose h + (t - 1).choose (h + 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel ht1, Nat.choose_succ_succ']
    calc (((t - 1).choose h : ℕ) : ℤ)
        ≤ (((t - 1).choose h : ℕ) : ℤ)
            + (((t - 1).choose (h + 1) : ℕ) : ℤ) :=
          le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = ((t.choose (h + 1) : ℕ) : ℤ) := by
          rw [hpascal, Nat.cast_add]

/-- Monotonicity of finite products under pointwise bounds (all factors
nonnegative on one side). -/
theorem prod_le_prod_of_nonneg_le {ι : Type*} (J : Finset ι) (I U : ι → ℝ)
    (hI : ∀ j ∈ J, 0 ≤ I j) (hIU : ∀ j ∈ J, I j ≤ U j) :
    ∏ j ∈ J, I j ≤ ∏ j ∈ J, U j :=
  Finset.prod_le_prod₀ (fun j hj => hI j hj) (fun j hj => hIU j hj)

/-- The paper's telescoping inequality for a product of nonnegative block
factors: `0 ≤ ∏ U_j - ∏ I_j ≤ ∑_j E_j ∏_{k≠j} U_k`. -/
theorem prod_telescope_le {ι : Type*} [DecidableEq ι] (J : Finset ι) (I U E : ι → ℝ)
    (hI : ∀ j ∈ J, 0 ≤ I j) (hIU : ∀ j ∈ J, I j ≤ U j)
    (hUE : ∀ j ∈ J, U j - I j ≤ E j) :
    ∏ j ∈ J, U j - ∏ j ∈ J, I j
      ≤ ∑ j ∈ J, E j * ∏ k ∈ J.erase j, U k := by
  revert hI hIU hUE
  induction J using Finset.induction with
  | empty =>
    intro hI hIU hUE
    simp
  | @insert a s has ih =>
    intro hI hIU hUE
    have hIs : ∀ j ∈ s, 0 ≤ I j := fun j hj => hI j (Finset.mem_insert_of_mem hj)
    have hIUs : ∀ j ∈ s, I j ≤ U j := fun j hj => hIU j (Finset.mem_insert_of_mem hj)
    have hUEs : ∀ j ∈ s, U j - I j ≤ E j :=
      fun j hj => hUE j (Finset.mem_insert_of_mem hj)
    have ihle := ih hIs hIUs hUEs
    have hPIU : ∏ j ∈ s, I j ≤ ∏ j ∈ s, U j :=
      prod_le_prod_of_nonneg_le s I U hIs hIUs
    have hPI0 : 0 ≤ ∏ j ∈ s, I j :=
      Finset.prod_nonneg (fun j hj => hIs j hj)
    have hPU0 : 0 ≤ ∏ j ∈ s, U j :=
      Finset.prod_nonneg (fun j hj => le_trans (hIs j hj) (hIUs j hj))
    have hUa0 : 0 ≤ U a :=
      le_trans (hI a (Finset.mem_insert_self a s))
        (hIU a (Finset.mem_insert_self a s))
    have hsuba : 0 ≤ U a - I a :=
      sub_nonneg.mpr (hIU a (Finset.mem_insert_self a s))
    have hterm : ∀ j ∈ s, ∏ k ∈ (insert a s).erase j, U k
        = U a * ∏ k ∈ s.erase j, U k := by
      intro j hj
      have hja : j ≠ a := fun heq => has (heq ▸ hj)
      have herase : (insert a s).erase j = insert a (s.erase j) := by
        ext k
        simp only [Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨hkj, rfl | hks⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hkj, hks⟩
        · rintro (rfl | ⟨hkj, hks⟩)
          · exact ⟨Ne.symm hja, Or.inl rfl⟩
          · exact ⟨hkj, Or.inr hks⟩
      rw [herase, Finset.prod_insert (fun hc => has (Finset.mem_of_mem_erase hc))]
    have hsum : (∑ j ∈ s, E j * ∏ k ∈ (insert a s).erase j, U k)
        = ∑ j ∈ s, E j * (U a * ∏ k ∈ s.erase j, U k) :=
      Finset.sum_congr rfl (fun j hj => by rw [hterm j hj])
    have hb1 : U a * (∏ j ∈ s, U j - ∏ j ∈ s, I j)
        ≤ U a * ∑ j ∈ s, E j * ∏ k ∈ s.erase j, U k :=
      mul_le_mul_of_nonneg_left ihle hUa0
    have hb2 : (U a - I a) * ∏ j ∈ s, I j ≤ E a * ∏ j ∈ s, U j := by
      calc (U a - I a) * ∏ j ∈ s, I j
          ≤ (U a - I a) * ∏ j ∈ s, U j :=
            mul_le_mul_of_nonneg_left hPIU hsuba
        _ ≤ E a * ∏ j ∈ s, U j :=
            mul_le_mul_of_nonneg_right
              (hUE a (Finset.mem_insert_self a s)) hPU0
    rw [Finset.prod_insert has, Finset.prod_insert has, Finset.sum_insert has,
      Finset.erase_insert has, hsum]
    calc U a * ∏ j ∈ s, U j - I a * ∏ j ∈ s, I j
        = U a * (∏ j ∈ s, U j - ∏ j ∈ s, I j)
          + (U a - I a) * ∏ j ∈ s, I j := by ring
      _ ≤ U a * (∑ j ∈ s, E j * ∏ k ∈ s.erase j, U k)
          + E a * ∏ j ∈ s, U j :=
          add_le_add hb1 hb2
      _ = E a * ∏ j ∈ s, U j
          + ∑ j ∈ s, E j * (U a * ∏ k ∈ s.erase j, U k) := by
          have e : U a * (∑ j ∈ s, E j * ∏ k ∈ s.erase j, U k)
              = ∑ j ∈ s, E j * (U a * ∏ k ∈ s.erase j, U k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          rw [e]
          exact add_comm _ _

/-! ## Independent-trial expectation bounds -/

/-- One-factor exponential lower bound: `1 - u ≥ exp(-u/η₀)` for
`u ∈ [0, 1-η₀]` (paper: `-log(1-u) ≤ u/η₀`). From `exp t ≥ 1 + t` and
`(1 + v)(1 - η₀v) ≥ 1` on the range. -/
theorem one_sub_ge_exp_neg (η₀ u : ℝ) (hη : 0 < η₀) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 - η₀) : Real.exp (-u / η₀) ≤ 1 - u := by
  have h1u : (0 : ℝ) ≤ 1 - u := by linarith
  have key : (1 : ℝ) ≤ (1 + u / η₀) * (1 - u) := by
    have hηne : η₀ ≠ 0 := ne_of_gt hη
    have h1 : (1 + u / η₀) * (1 - u) - 1 = (u / η₀) * (1 - η₀ - u) := by
      field_simp
      ring
    have h2 : 0 ≤ (u / η₀) * (1 - η₀ - u) :=
      mul_nonneg (div_nonneg hu0 hη.le) (by linarith)
    linarith
  have hexp : (1 : ℝ) + u / η₀ ≤ Real.exp (u / η₀) := by
    have h := Real.add_one_le_exp (u / η₀)
    linarith
  have hprod : (1 : ℝ) ≤ Real.exp (u / η₀) * (1 - u) :=
    calc (1 : ℝ) ≤ (1 + u / η₀) * (1 - u) := key
      _ ≤ Real.exp (u / η₀) * (1 - u) :=
          mul_le_mul_of_nonneg_right (by linarith [hexp]) h1u
  have hE : (0 : ℝ) < Real.exp (-u / η₀) := Real.exp_pos _
  calc Real.exp (-u / η₀) = Real.exp (-u / η₀) * 1 := (mul_one _).symm
    _ ≤ Real.exp (-u / η₀) * (Real.exp (u / η₀) * (1 - u)) :=
        mul_le_mul_of_nonneg_left hprod hE.le
    _ = 1 - u := by
        have hexp0 : -u / η₀ + u / η₀ = (0 : ℝ) := by
          rw [neg_div]
          exact neg_add_cancel _
        calc Real.exp (-u / η₀) * (Real.exp (u / η₀) * (1 - u))
            = (Real.exp (-u / η₀) * Real.exp (u / η₀)) * (1 - u) := by ring
          _ = Real.exp (-u / η₀ + u / η₀) * (1 - u) := by
              rw [Real.exp_add]
          _ = 1 - u := by rw [hexp0, Real.exp_zero, one_mul]

/-- Block avoidance lower bound: under `0 ≤ g ≤ 1 - η₀` and total mass
`≤ C`, `∏ (1 - g) ≥ exp(-C/η₀)` (paper's `a_j ≥ exp(-C/η₀) =: a_*`). -/
theorem block_avoidance_ge {ι : Type*} (B : Finset ι) (g : ι → ℝ) (η₀ C : ℝ)
    (hη : 0 < η₀)
    (hg0 : ∀ p ∈ B, 0 ≤ g p) (hg1 : ∀ p ∈ B, g p ≤ 1 - η₀)
    (hsum : ∑ p ∈ B, g p ≤ C) :
    Real.exp (-C / η₀) ≤ ∏ p ∈ B, (1 - g p) := by
  have hfac : ∀ p ∈ B, Real.exp (-(g p) / η₀) ≤ 1 - g p :=
    fun p hp => one_sub_ge_exp_neg η₀ (g p) hη (hg0 p hp) (hg1 p hp)
  have hexp_prod : ∏ p ∈ B, Real.exp (-(g p) / η₀)
      = Real.exp (-(∑ p ∈ B, g p) / η₀) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [neg_div, Finset.sum_neg_distrib, ← Finset.sum_div]
  have hsd : (∑ p ∈ B, g p) / η₀ ≤ C / η₀ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr hη.le)
  calc Real.exp (-C / η₀) ≤ Real.exp (-(∑ p ∈ B, g p) / η₀) := by
        apply Real.exp_le_exp.mpr
        simp only [neg_div]
        exact neg_le_neg hsd
    _ = ∏ p ∈ B, Real.exp (-(g p) / η₀) := hexp_prod.symm
    _ ≤ ∏ p ∈ B, (1 - g p) :=
        Finset.prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) hfac

/-- Degree-zero case of the symmetric bound (both sides are one). -/
theorem esymm_zero {ι : Type*} [DecidableEq ι] (B : Finset ι) (g : ι → ℝ) :
    (∑ d ∈ B.powersetCard 0, ∏ p ∈ d, g p) * (Nat.factorial 0 : ℝ)
      ≤ (∑ p ∈ B, g p) ^ 0 := by
  simp [Finset.powersetCard_zero]

/-- Elementary symmetric bound, multiplied form (paper's
`e_j ≤ C^{h_j+1}/(h_j+1)!` core): the degree-`m` squarefree monomial sum
times `m!` is at most the `m`-th power of the total. Induction on the
index set; the step uses `powersetCard_succ_insert` and a binomial
two-term bound proved by its own induction (no analysis). -/
theorem esymm_mul_factorial_le {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (g : ι → ℝ) (m : ℕ) (h0 : ∀ p ∈ B, 0 ≤ g p) :
    (∑ d ∈ B.powersetCard m, ∏ p ∈ d, g p) * (Nat.factorial m : ℝ)
      ≤ (∑ p ∈ B, g p) ^ m := by
  revert m h0
  induction B using Finset.induction with
  | empty =>
    intro m h0
    cases m with
    | zero => exact esymm_zero _ _
    | succ n =>
      show (∑ d ∈ (∅ : Finset ι).powersetCard (n + 1), ∏ p ∈ d, g p)
          * ((Nat.factorial (n + 1) : ℝ)) ≤ (∑ p ∈ (∅ : Finset ι), g p) ^ (n + 1)
      have hempty : (∅ : Finset ι).powersetCard (n + 1) = ∅ := by
        rw [← Finset.card_eq_zero, Finset.card_powersetCard,
          Finset.card_empty]
        exact Nat.choose_eq_zero_of_lt (by omega)
      rw [hempty, Finset.sum_empty, zero_mul]
      exact pow_nonneg (Finset.sum_nonneg (fun p hp => h0 p hp)) _
  | @insert q B₀ has ih =>
    intro m h0
    have h0₀ : ∀ p ∈ B₀, 0 ≤ g p := fun p hp => h0 p (Finset.mem_insert_of_mem hp)
    have h0q : 0 ≤ g q := h0 q (Finset.mem_insert_self q B₀)
    have hS0 : 0 ≤ ∑ p ∈ B₀, g p := Finset.sum_nonneg (fun p hp => h0₀ p hp)
    cases m with
    | zero => exact esymm_zero _ _
    | succ n =>
      show (∑ d ∈ (insert q B₀).powersetCard (n + 1), ∏ p ∈ d, g p)
          * ((Nat.factorial (n + 1) : ℝ))
          ≤ (∑ p ∈ insert q B₀, g p) ^ (n + 1)
      have hS : (∑ p ∈ insert q B₀, g p) = (∑ p ∈ B₀, g p) + g q := by
        rw [Finset.sum_insert has]; ring
      have hsplit : ((insert q B₀).powersetCard (n + 1))
          = B₀.powersetCard (n + 1) ∪ (B₀.powersetCard n).image (insert q) :=
        Finset.powersetCard_succ_insert has n
      have hdisj : Disjoint (B₀.powersetCard (n + 1))
          ((B₀.powersetCard n).image (insert q)) := by
        rw [Finset.disjoint_left]
        intro d hd1 hd2
        obtain ⟨d', hd'mem, hd'eq⟩ := Finset.mem_image.mp hd2
        have hqd : q ∈ d := hd'eq ▸ Finset.mem_insert_self q d'
        have hqd' : q ∉ d := by
          have hdsub : d ⊆ B₀ := (Finset.mem_powersetCard.mp hd1).1
          exact fun h => has (hdsub h)
        exact hqd' hqd
      have hsum : (∑ d ∈ (insert q B₀).powersetCard (n + 1), ∏ p ∈ d, g p)
          = (∑ d ∈ B₀.powersetCard (n + 1), ∏ p ∈ d, g p)
            + ∑ d ∈ (B₀.powersetCard n).image (insert q), ∏ p ∈ d, g p := by
        rw [hsplit, Finset.sum_union hdisj]
      have hinj : Set.InjOn (insert q : Finset ι → Finset ι)
          ↑(B₀.powersetCard n) := by
        intro d₁ hd₁ d₂ hd₂ heq
        have hq1 : q ∉ d₁ := by
          have hdsub : d₁ ⊆ B₀ :=
            (Finset.mem_powersetCard.mp (Finset.mem_coe.mp hd₁)).1
          exact fun h => has (hdsub h)
        have hq2 : q ∉ d₂ := by
          have hdsub : d₂ ⊆ B₀ :=
            (Finset.mem_powersetCard.mp (Finset.mem_coe.mp hd₂)).1
          exact fun h => has (hdsub h)
        calc d₁ = (insert q d₁).erase q := (Finset.erase_insert hq1).symm
          _ = (insert q d₂).erase q := by rw [heq]
          _ = d₂ := Finset.erase_insert hq2
      have hprod_ins : ∀ d ∈ B₀.powersetCard n,
          (∏ p ∈ insert q d, g p) = g q * ∏ p ∈ d, g p := by
        intro d hd
        have hqd : q ∉ d := fun h =>
          has ((Finset.mem_powersetCard.mp hd).1 h)
        exact Finset.prod_insert hqd
      have himg : (∑ d ∈ (B₀.powersetCard n).image (insert q), ∏ p ∈ d, g p)
          = g q * ∑ d ∈ B₀.powersetCard n, ∏ p ∈ d, g p := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        exact hprod_ins d hd
      -- binomial two-term bound by its own induction
      have hbin : ∀ k : ℕ, (∑ p ∈ B₀, g p) ^ (k + 1)
            + ((k + 1 : ℕ) : ℝ) * g q * (∑ p ∈ B₀, g p) ^ k
          ≤ ((∑ p ∈ B₀, g p) + g q) ^ (k + 1) := by
        intro k
        induction k with
        | zero => simp
        | succ k ihk =>
          show (∑ p ∈ B₀, g p) ^ (k + 1 + 1)
              + (((k + 1 + 1 : ℕ)) : ℝ) * g q * (∑ p ∈ B₀, g p) ^ (k + 1)
              ≤ ((∑ p ∈ B₀, g p) + g q) ^ (k + 1 + 1)
          have hSg : (0 : ℝ) ≤ (∑ p ∈ B₀, g p) + g q := add_nonneg hS0 h0q
          have hmul := mul_le_mul_of_nonneg_right ihk hSg
          have hexp : ((∑ p ∈ B₀, g p) + g q) ^ (k + 1)
              * ((∑ p ∈ B₀, g p) + g q)
              = ((∑ p ∈ B₀, g p) + g q) ^ (k + 1 + 1) := by
            calc ((∑ p ∈ B₀, g p) + g q) ^ (k + 1)
                * ((∑ p ∈ B₀, g p) + g q)
                = ((∑ p ∈ B₀, g p) + g q) ^ ((k + 1) + 1) :=
                  (pow_succ _ _).symm
              _ = ((∑ p ∈ B₀, g p) + g q) ^ (k + 1 + 1) := rfl
          have hnn : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)
              * (g q ^ 2 * (∑ p ∈ B₀, g p) ^ k) :=
            mul_nonneg (Nat.cast_nonneg _)
              (mul_nonneg (sq_nonneg _) (pow_nonneg hS0 _))
          have key : ((∑ p ∈ B₀, g p) ^ (k + 1)
                + ((k + 1 : ℕ) : ℝ) * g q * (∑ p ∈ B₀, g p) ^ k)
              * ((∑ p ∈ B₀, g p) + g q)
              - ((∑ p ∈ B₀, g p) ^ (k + 1 + 1)
                + (((k + 1 + 1 : ℕ)) : ℝ) * g q * (∑ p ∈ B₀, g p) ^ (k + 1))
              = ((k + 1 : ℕ) : ℝ) * (g q ^ 2 * (∑ p ∈ B₀, g p) ^ k) := by
            push_cast
            ring
          rw [hexp] at hmul
          linarith [hmul, key, hnn]
      have hA : (∑ d ∈ B₀.powersetCard (n + 1), ∏ p ∈ d, g p)
          * ((Nat.factorial (n + 1) : ℝ)) ≤ (∑ p ∈ B₀, g p) ^ (n + 1) := ih _ h0₀
      have hAn : (∑ d ∈ B₀.powersetCard n, ∏ p ∈ d, g p) * (Nat.factorial n : ℝ)
          ≤ (∑ p ∈ B₀, g p) ^ n := ih _ h0₀
      have hfactR : ((Nat.factorial (n + 1) : ℝ))
          = ((n + 1 : ℕ) : ℝ) * (Nat.factorial n : ℝ) := by
        exact_mod_cast Nat.factorial_succ n
      have e2 : (g q * ∑ d ∈ B₀.powersetCard n, ∏ p ∈ d, g p)
          * ((Nat.factorial (n + 1) : ℝ))
          ≤ ((n + 1 : ℕ) : ℝ) * g q * (∑ p ∈ B₀, g p) ^ n := by
        have hnn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * g q :=
          mul_nonneg (Nat.cast_nonneg _) h0q
        have hstep : (g q * ∑ d ∈ B₀.powersetCard n, ∏ p ∈ d, g p)
            * (((n + 1 : ℕ) : ℝ) * (Nat.factorial n : ℝ))
            ≤ (((n + 1 : ℕ) : ℝ) * g q) * ((∑ p ∈ B₀, g p) ^ n) := by
          have hbase : (∑ d ∈ B₀.powersetCard n, ∏ p ∈ d, g p)
              * (Nat.factorial n : ℝ) ≤ (∑ p ∈ B₀, g p) ^ n := hAn
          calc (g q * ∑ d ∈ B₀.powersetCard n, ∏ p ∈ d, g p)
              * (((n + 1 : ℕ) : ℝ) * (Nat.factorial n : ℝ))
              = (((n + 1 : ℕ) : ℝ) * g q)
                * ((∑ d ∈ B₀.powersetCard n, ∏ p ∈ d, g p)
                  * (Nat.factorial n : ℝ)) := by ring
            _ ≤ (((n + 1 : ℕ) : ℝ) * g q) * ((∑ p ∈ B₀, g p) ^ n) :=
                mul_le_mul_of_nonneg_left hbase hnn
        rw [hfactR]
        exact hstep
      rw [hS, hsum, himg]
      calc ((∑ d ∈ B₀.powersetCard (n + 1), ∏ p ∈ d, g p)
            + g q * ∑ d ∈ B₀.powersetCard n, ∏ p ∈ d, g p)
          * ((Nat.factorial (n + 1) : ℝ))
          = ((∑ d ∈ B₀.powersetCard (n + 1), ∏ p ∈ d, g p)
            * ((Nat.factorial (n + 1) : ℝ)))
            + ((g q * ∑ d ∈ B₀.powersetCard n, ∏ p ∈ d, g p)
              * ((Nat.factorial (n + 1) : ℝ))) := by ring
        _ ≤ (∑ p ∈ B₀, g p) ^ (n + 1)
            + ((n + 1 : ℕ) : ℝ) * g q * (∑ p ∈ B₀, g p) ^ n :=
            add_le_add hA e2
        _ ≤ ((∑ p ∈ B₀, g p) + g q) ^ (n + 1) := hbin n

/-- Divided form of the symmetric bound. -/
theorem esymm_le {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (g : ι → ℝ) (m : ℕ) (h0 : ∀ p ∈ B, 0 ≤ g p) :
    (∑ d ∈ B.powersetCard m, ∏ p ∈ d, g p)
      ≤ (∑ p ∈ B, g p) ^ m / (Nat.factorial m : ℝ) := by
  have hpos : (0 : ℝ) < ((Nat.factorial m : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.factorial_ne_zero m))
  rw [le_div_iff₀ hpos]
  exact esymm_mul_factorial_le B g m h0

/-! ## Factorial tails and the `R_h ≪ e^{-h}` decay -/

/-- Factorial tail term `C^{m+1}/(m+1)!` dominating `e_j`
(paper's `C^{h_j+1}/(h_j+1)!`). -/
noncomputable def tailTerm (C : ℝ) (m : ℕ) : ℝ :=
  C ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)

theorem tailTerm_nonneg {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    0 ≤ tailTerm C m := by
  unfold tailTerm
  apply div_nonneg (pow_nonneg hC _)
  exact Nat.cast_nonneg _

theorem tailTerm_succ (C : ℝ) (m : ℕ) :
    tailTerm C (m + 1) = tailTerm C m * (C / ((m : ℝ) + 2)) := by
  unfold tailTerm
  have hfact1 : ((Nat.factorial (m + 1) : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.factorial_ne_zero _)))
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  have h_nat : Nat.factorial (m + 1 + 1) = (m + 1 + 1) * Nat.factorial (m + 1) :=
    Nat.factorial_succ (m + 1)
  have hcast : (((m + 1 + 1 : ℕ)) : ℝ) = ((m : ℝ) + 2) := by push_cast; ring
  have hfact_eq : ((Nat.factorial (m + 1 + 1) : ℕ) : ℝ)
      = (((m : ℝ) + 2)) * ((Nat.factorial (m + 1) : ℕ) : ℝ) := by
    calc ((Nat.factorial (m + 1 + 1) : ℕ) : ℝ)
        = (((m + 1 + 1 : ℕ)) : ℝ) * ((Nat.factorial (m + 1) : ℕ) : ℝ) := by
          rw [h_nat, Nat.cast_mul]
      _ = (((m : ℝ) + 2)) * ((Nat.factorial (m + 1) : ℕ) : ℝ) := by
          rw [hcast]
  rw [pow_succ, hfact_eq]
  field_simp

/-- One-step ratio bound by `1/e` once the denominator exceeds `e*C`. -/
theorem ratio_le_inv_exp_one {C : ℝ} (hC : 0 ≤ C) (m : ℕ)
    (hden : Real.exp 1 * C ≤ (m : ℝ) + 2) :
    C / ((m : ℝ) + 2) ≤ (Real.exp 1)⁻¹ := by
  have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  by_cases hC0 : C = 0
  · simp [hC0, inv_nonneg.mpr hexp.le]
  · have h2 : C * Real.exp 1 ≤ (m : ℝ) + 2 := by
      calc C * Real.exp 1 = Real.exp 1 * C := by ring
        _ ≤ (m : ℝ) + 2 := hden
    rw [div_le_iff₀ hm]
    have hdiv : (Real.exp 1)⁻¹ * ((m : ℝ) + 2) = ((m : ℝ) + 2) / Real.exp 1 := by
      rw [div_eq_mul_inv, mul_comm]
    rw [hdiv, le_div_iff₀ hexp]
    exact h2

/-- Geometric decay of the tail from `m₀` onward. -/
theorem tailTerm_le_geometric {C : ℝ} (hC : 0 ≤ C) (m₀ m : ℕ)
    (hden : Real.exp 1 * C ≤ (m₀ : ℝ) + 2) (hm : m₀ ≤ m) :
    tailTerm C m ≤ tailTerm C m₀ * ((Real.exp 1)⁻¹ ^ (m - m₀)) := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp
  | succ n hn ih =>
    have hden_n : Real.exp 1 * C ≤ (n : ℝ) + 2 := by
      have h1 : ((m₀ : ℝ) + 2) ≤ ((n : ℝ) + 2) := by
        have : (m₀ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
        linarith
      exact le_trans hden h1
    have hratio := ratio_le_inv_exp_one hC n hden_n
    have hr_nonneg : (0 : ℝ) ≤ (Real.exp 1)⁻¹ :=
      inv_nonneg.mpr (Real.exp_pos _).le
    have hpow_nn : (0 : ℝ) ≤ (Real.exp 1)⁻¹ ^ (n - m₀) :=
      pow_nonneg hr_nonneg _
    have htail0 : (0 : ℝ) ≤ tailTerm C m₀ := tailTerm_nonneg hC m₀
    have hratio_nn : (0 : ℝ) ≤ C / ((n : ℝ) + 2) :=
      div_nonneg hC (by positivity)
    have hsub : n + 1 - m₀ = (n - m₀) + 1 := by omega
    rw [tailTerm_succ, hsub, pow_succ]
    calc tailTerm C n * (C / ((n : ℝ) + 2))
        ≤ (tailTerm C m₀ * (Real.exp 1)⁻¹ ^ (n - m₀)) * (Real.exp 1)⁻¹ :=
          mul_le_mul ih hratio hratio_nn (mul_nonneg htail0 hpow_nn)
      _ = tailTerm C m₀ * ((Real.exp 1)⁻¹ ^ (n - m₀) * (Real.exp 1)⁻¹) := by ring

/-- Finite geometric partial sums: `(∑ s^j)(1-s) = 1-s^N`. -/
theorem geom_mul_one_sub {s : ℝ} (N : ℕ) :
    (∑ j ∈ Finset.range N, s ^ j) * (1 - s) = 1 - s ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    ring

/-- Partial geometric sums are bounded by `1/(1-s)` for `0 ≤ s < 1`. -/
theorem geom_sum_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, s ^ j ≤ 1 / (1 - s) := by
  have h1s : (0 : ℝ) < 1 - s := by linarith
  have hsN : (0 : ℝ) ≤ s ^ N := pow_nonneg hs0 _
  have h := geom_mul_one_sub (s := s) N
  have hle : (∑ j ∈ Finset.range N, s ^ j) * (1 - s) ≤ 1 := by
    rw [h]
    linarith
  rw [le_div_iff₀ h1s]
  exact hle

/-- Shifted geometric sums `∑ s^{j+1} ≤ s/(1-s)`. -/
theorem geom_succ_sum_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, s ^ (j + 1) ≤ s / (1 - s) := by
  have h : ∑ j ∈ Finset.range N, s ^ (j + 1)
      = s * ∑ j ∈ Finset.range N, s ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ', mul_comm]
  rw [h]
  have hsum := geom_sum_le hs0 hs1 N
  calc s * ∑ j ∈ Finset.range N, s ^ j
      ≤ s * (1 / (1 - s)) := by
        apply mul_le_mul_of_nonneg_left hsum hs0
    _ = s / (1 - s) := by rw [mul_one_div]

/-- Level exponent sum: partial sums of `(j+1)/2^j` equal `4-(N+2)/2^{N-1}`. -/
theorem level_sum_eq (N : ℕ) (hN : 1 ≤ N) :
    ∑ j ∈ Finset.range N, (((j : ℝ) + 1) / (2 : ℝ) ^ j)
      = 4 - (((N : ℝ) + 2) / (2 : ℝ) ^ (N - 1)) := by
  induction N, hN using Nat.le_induction with
  | base =>
    norm_num
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih]
    have hexp_eq : n + 1 - 1 = n := by omega
    rw [hexp_eq]
    push_cast
    have hn1 : n = (n - 1) + 1 := by omega
    have hpow_rel : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
      conv_lhs => rw [hn1]
      rw [pow_succ']
    have h1 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2 : (2 : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hpow_rel]
    field_simp
    ring

/-- Level exponent sums are at most `4` (paper: `∑ h(j+1)2^{-j} = 4h`). -/
theorem level_sum_le (N : ℕ) :
    ∑ j ∈ Finset.range N, (((j : ℝ) + 1) / (2 : ℝ) ^ j) ≤ 4 := by
  by_cases hN : N = 0
  · simp [hN, Finset.sum_empty]
  · have h1 : 1 ≤ N := Nat.pos_of_ne_zero hN
    rw [level_sum_eq N h1]
    have hnn : (0 : ℝ) ≤ (((N : ℝ) + 2) / (2 : ℝ) ^ (N - 1)) := by positivity
    linarith

/-- . -/
theorem exp_neg_one : Real.exp (-1 : ℝ) = (Real.exp 1)⁻¹ := by
  have h : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  exact eq_inv_of_mul_eq_one_left h

/--  for . -/
theorem exp_neg_nat (n : ℕ) :
    Real.exp (-((n : ℕ) : ℝ)) = ((Real.exp 1)⁻¹ ^ n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hcast : (((k + 1 : ℕ)) : ℝ) = ((k : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast, neg_add, Real.exp_add, ih, exp_neg_one, pow_succ]

/-- Uniform factorial-tail sum bound ,
independent of the number of blocks (paper's ). -/
theorem exists_tailSum_bound (C : ℝ) (hC : 0 ≤ C) :
    ∃ m₀ : ℕ, ∃ K₀ : ℝ, 0 < K₀ ∧ Real.exp 1 * C ≤ (m₀ : ℝ) + 2 ∧
      ∀ h : ℕ, m₀ ≤ h → 1 ≤ h → ∀ N : ℕ,
        ∑ j ∈ Finset.range N, tailTerm C ((j + 1) * h)
          ≤ K₀ * Real.exp (-((h : ℕ) : ℝ)) := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (Real.exp 1 * C - 2)
  have hden0 : Real.exp 1 * C ≤ (m₀ : ℝ) + 2 := by linarith
  have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hr0 : (0 : ℝ) ≤ (Real.exp 1)⁻¹ := inv_nonneg.mpr hexp_pos.le
  have hr1 : (Real.exp 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ he1
  have hrpos : (0 : ℝ) < (Real.exp 1)⁻¹ := inv_pos.mpr hexp_pos
  have h1r : (0 : ℝ) < 1 - (Real.exp 1)⁻¹ := by linarith
  have hrpow0 : ∀ n : ℕ, (0 : ℝ) < (Real.exp 1)⁻¹ ^ n :=
    fun n => pow_pos hrpos n
  -- constant , plus one for positivity
  set r : ℝ := (Real.exp 1)⁻¹ with hrdef
  have hrm0 : (0 : ℝ) < r ^ m₀ := hrpow0 m₀
  set K1 : ℝ := tailTerm C m₀ / r ^ m₀ / (1 - r) with hK1
  have hK1nn : 0 ≤ K1 := by
    unfold K1
    apply div_nonneg
    · apply div_nonneg (tailTerm_nonneg hC m₀) (pow_nonneg hr0 _)
    · linarith
  refine ⟨m₀, K1 + 1, by positivity, hden0, fun h hh0 hh1 N => ?_⟩
  have hrh : r ^ h = Real.exp (-((h : ℕ) : ℝ)) := by
    rw [hrdef, ← exp_neg_nat]
  -- each term bounded by 
  have hterm : ∀ j : ℕ, tailTerm C ((j + 1) * h)
      ≤ (tailTerm C m₀ / r ^ m₀) * (r ^ h) ^ (j + 1) := by
    intro j
    have hmh : m₀ ≤ (j + 1) * h := by
      calc m₀ ≤ h := hh0
        _ ≤ (j + 1) * h := Nat.le_mul_of_pos_left h (Nat.succ_pos j)
    have hgeo := tailTerm_le_geometric hC m₀ ((j + 1) * h) hden0 hmh
    have hsub_add : m₀ + ((j + 1) * h - m₀) = (j + 1) * h :=
      Nat.add_sub_cancel' hmh
    have hpow_eq : r ^ ((j + 1) * h)
        = r ^ m₀ * r ^ ((j + 1) * h - m₀) := by
      rw [← pow_add, hsub_add]
    have hpow_eq2 : r ^ ((j + 1) * h) = (r ^ h) ^ (j + 1) := by
      rw [← pow_mul, mul_comm]
    have hdiv : r ^ ((j + 1) * h - m₀)
        = r ^ ((j + 1) * h) / r ^ m₀ := by
      rw [eq_div_iff (ne_of_gt hrm0), hpow_eq, mul_comm]
    rw [← hrdef] at hgeo
    calc tailTerm C ((j + 1) * h)
        ≤ tailTerm C m₀ * r ^ ((j + 1) * h - m₀) := hgeo
      _ = tailTerm C m₀ * (r ^ ((j + 1) * h) / r ^ m₀) := by rw [hdiv]
      _ = (tailTerm C m₀ / r ^ m₀) * r ^ ((j + 1) * h) := by ring
      _ = (tailTerm C m₀ / r ^ m₀) * (r ^ h) ^ (j + 1) := by rw [hpow_eq2]
  have hsum : ∑ j ∈ Finset.range N, tailTerm C ((j + 1) * h)
      ≤ (tailTerm C m₀ / r ^ m₀) * ((r ^ h) / (1 - r ^ h)) := by
    calc ∑ j ∈ Finset.range N, tailTerm C ((j + 1) * h)
        ≤ ∑ j ∈ Finset.range N, (tailTerm C m₀ / r ^ m₀) * (r ^ h) ^ (j + 1) := by
          apply Finset.sum_le_sum
          intro j _
          exact hterm j
      _ = (tailTerm C m₀ / r ^ m₀) * ∑ j ∈ Finset.range N, (r ^ h) ^ (j + 1) := by
          rw [Finset.mul_sum]
      _ ≤ (tailTerm C m₀ / r ^ m₀) * ((r ^ h) / (1 - r ^ h)) := by
          have hrh0 : (0 : ℝ) ≤ r ^ h := pow_nonneg hr0 _
          have hrh1 : r ^ h < 1 := by
            calc r ^ h ≤ r ^ 1 := pow_le_pow_of_le_one hr0 hr1.le hh1
              _ = r := pow_one r
              _ < 1 := hr1
          have hle := geom_succ_sum_le hrh0 hrh1 N
          apply mul_le_mul_of_nonneg_left hle
          apply div_nonneg (tailTerm_nonneg hC m₀) (pow_nonneg hr0 _)
  have hrh_le : r ^ h ≤ r := by
    calc r ^ h ≤ r ^ 1 := pow_le_pow_of_le_one hr0 hr1.le hh1
      _ = r := pow_one r
  have hden_ineq : (1 : ℝ) - r ≤ 1 - r ^ h := by linarith [pow_nonneg hr0 h]
  have h1rh : (0 : ℝ) < 1 - r ^ h := by
    have : r ^ h < 1 := by
      calc r ^ h ≤ r ^ 1 := pow_le_pow_of_le_one hr0 hr1.le hh1
        _ = r := pow_one r
        _ < 1 := hr1
    linarith
  have hfrac : (r ^ h) / (1 - r ^ h) ≤ r ^ h / (1 - r) :=
    div_le_div_of_nonneg_left (pow_nonneg hr0 h) h1r hden_ineq
  have hpos_div : (0 : ℝ) ≤ tailTerm C m₀ / r ^ m₀ :=
    div_nonneg (tailTerm_nonneg hC m₀) (pow_nonneg hr0 _)
  have heqK : K1 * (r ^ h)
      = (tailTerm C m₀ / r ^ m₀) * (r ^ h / (1 - r)) := by
    unfold K1
    ring
  have hK1_eq : (tailTerm C m₀ / r ^ m₀) * ((r ^ h) / (1 - r ^ h))
      ≤ K1 * (r ^ h) := by
    rw [heqK]
    exact mul_le_mul_of_nonneg_left hfrac hpos_div
  calc ∑ j ∈ Finset.range N, tailTerm C ((j + 1) * h)
      ≤ (tailTerm C m₀ / r ^ m₀) * ((r ^ h) / (1 - r ^ h)) := hsum
    _ ≤ K1 * (r ^ h) := hK1_eq
    _ = K1 * Real.exp (-((h : ℕ) : ℝ)) := by rw [← hrh]
    _ ≤ (K1 + 1) * Real.exp (-((h : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith

end SieveCalculus
end Prelim
end Erdos821
