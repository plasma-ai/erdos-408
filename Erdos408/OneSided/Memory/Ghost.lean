import Erdos408.OneSided.Analysis.Schur
import Erdos408.OneSided.Memory.Space
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Sum

/-!
# The ghost operation

The ghost operation `𝒢_j` of PD §4 (`mem:ghost-row`, `mem:ghost-norm`), on the memory space
of multiplicity functions. At the current position some particles *hit*: their anchor is
the current line. In each group the operation deletes a sub-multiset of the hitting
particles, paying `del` for each deletion and `surv` for each surviving hit. It then
creates a batch of particles anchored at the current lines, with coefficient `cre` and
measure `ν^{⊗l} / l!` per batch. In PD, `del = -η'_j/ρ`, `surv = q_j/ρ²` and
`cre = -η'_j V_i/ρ`.

On multiplicity functions the coefficient factors over particles. A particle with `h`
hits, `d` of them deleted and `n` created, carries
`C(h, d) del^d surv^{h - d} (cre ν)^n / n!`. The binomial coefficient counts the indexed
deletion choices. The `n!` comes from the ordered batch: summing `ν^{⊗l} / l!` over the
orderings of a multiset gives `∏ ν^n / n!`.

The weighted Schur test with weight `v₀^{size}` then reduces to the binomial theorem and
the exponential series. For each hitting particle the row sum is
`(surv + |del|/v₀)^h exp(v₀ |cre| ν)`, and the column sum is
`(surv + |cre|/v₀)^h exp(v₀ |del| ν)`. Once `v₀` makes both bases at most one, the norm is
at most the square root of
`exp(v₀ ∑_{hits} |cre| ν) exp(v₀ |del| ∑_{hits} ν)`.
-/

namespace Erdos408.OneSided

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Two summation lemmas -/

/-- The choice values: multiplicity functions with values at most `B`. -/
def multBox (B : ℕ) : Finset (X → ℕ) := Fintype.piFinset fun _ => range (B + 1)

/-- A sum over pairs of multiplicity functions of a product over particles is the product
over particles of the double sums. -/
theorem sum_multBox_prod (B : ℕ) (G : X → ℕ → ℕ → ℝ) :
    ∑ c ∈ multBox B ×ˢ multBox B, ∏ x, G x (c.1 x) (c.2 x) =
      ∏ x, ∑ d ∈ range (B + 1), ∑ n ∈ range (B + 1), G x d n := by
  rw [sum_product]
  have h₁ : ∀ D : X → ℕ, ∑ N ∈ multBox B, ∏ x, G x (D x) (N x) =
      ∏ x, ∑ n ∈ range (B + 1), G x (D x) n := fun D =>
    (prod_univ_sum (fun _ => range (B + 1)) fun x n => G x (D x) n).symm
  simp_rw [h₁]
  exact (prod_univ_sum (fun _ => range (B + 1)) fun x d => ∑ n ∈ range (B + 1), G x d n).symm

omit [Fintype X] [DecidableEq X] in
/-- The per-particle sum: the binomial theorem in the first variable and the exponential
series in the second. For a particle that cannot hit, only `(0, 0)` survives. -/
theorem sum_binom_exp_le {B s : ℕ} {a b e : ℝ} (P : Prop) [Decidable P] (ha : 0 ≤ a)
    (hb : 0 ≤ b) (he : 0 ≤ e) (hab : a + b ≤ 1) (hs : s ≤ B) (hP : ¬P → s = 0) :
    ∑ d ∈ range (B + 1), ∑ n ∈ range (B + 1),
        (if d ≤ s ∧ (P ∨ n = 0) then
          s.choose d * a ^ d * b ^ (s - d) * (e ^ n / n.factorial) else 0) ≤
      if P then Real.exp e else 1 := by
  by_cases hP' : P
  · simp only [hP', true_or, and_true, ite_true]
    have h₁ : ∀ d ∈ range (B + 1), ∑ n ∈ range (B + 1),
        (if d ≤ s then s.choose d * a ^ d * b ^ (s - d) * (e ^ n / n.factorial) else 0) =
        (if d ≤ s then s.choose d * a ^ d * b ^ (s - d) else 0) *
          ∑ n ∈ range (B + 1), e ^ n / n.factorial := by
      intro d _
      split_ifs <;> simp [mul_sum]
    rw [sum_congr rfl h₁, ← sum_mul]
    have h₂ : ∑ d ∈ range (B + 1), (if d ≤ s then s.choose d * a ^ d * b ^ (s - d) else 0) =
        (a + b) ^ s := by
      rw [← sum_filter, add_pow]
      have : (range (B + 1)).filter (· ≤ s) = range (s + 1) := by
        ext d; simp only [mem_filter, mem_range]; omega
      rw [this]
      exact sum_congr rfl fun d _ => by ring
    rw [h₂]
    calc (a + b) ^ s * ∑ n ∈ range (B + 1), e ^ n / n.factorial
        ≤ 1 * Real.exp e :=
          mul_le_mul (pow_le_one₀ (add_nonneg ha hb) hab) (Real.sum_le_exp_of_nonneg he _)
            (sum_nonneg fun n _ => div_nonneg (pow_nonneg he _) (Nat.cast_nonneg _)) zero_le_one
      _ = Real.exp e := one_mul _
  · have hs0 := hP hP'
    subst hs0
    simp only [hP', false_or, nonpos_iff_eq_zero, ite_false]
    rw [sum_eq_single 0, sum_eq_single 0]
    · simp
    · intro n _ hn; simp [hn]
    · intro h; simp at h
    · intro d _ hd
      exact sum_eq_zero fun n _ => ite_eq_right fun h => hd h.1
    · intro h; simp at h

/-! ### The ghost operation -/

section Ghost

variable (hit : X → Prop) [DecidablePred hit]

/-- The multiplicities of the particles hitting the current position. -/
def hitPart (S : X → ℕ) (x : X) : ℕ := if hit x then S x else 0

/-- A ghost choice `(D, N)` at `S`: `D` deletes hitting particles, `N` creates particles
anchored at the current lines, and the result has size at most `B`. -/
def GhostValid (B : ℕ) (S : X → ℕ) (c : (X → ℕ) × (X → ℕ)) : Prop :=
  (∀ x, c.1 x ≤ hitPart hit S x) ∧ (∀ x, ¬ hit x → c.2 x = 0) ∧
    memSize (fun x => S x - c.1 x + c.2 x) ≤ B

instance (B : ℕ) (S : X → ℕ) (c : (X → ℕ) × (X → ℕ)) : Decidable (GhostValid hit B S c) := by
  unfold GhostValid; infer_instance

variable (ν : X → ℝ) (del surv : ℝ) (cre : X → ℝ)

/-- The per-particle factor `C(h, d) del^d surv^{h - d} (cre ν)^n / n!`. -/
noncomputable def ghostFactor (x : X) (h d n : ℕ) : ℝ :=
  h.choose d * del ^ d * surv ^ (h - d) * (cre x * ν x) ^ n / n.factorial

/-- The coefficient of a ghost choice. -/
noncomputable def ghostCoef (B : ℕ) (S : MemState X B) (c : (X → ℕ) × (X → ℕ)) : ℂ :=
  if GhostValid hit B S.1 c then
    ((∏ x, ghostFactor ν del surv cre x (hitPart hit S.1 x) (c.1 x) (c.2 x) : ℝ) : ℂ)
  else 0

/-- The output `S - D + N` of a ghost choice. -/
def ghostOut (B : ℕ) (S : MemState X B) (c : (X → ℕ) × (X → ℕ)) : MemState X B :=
  if hc : GhostValid hit B S.1 c then
    ⟨fun x => S.1 x - c.1 x + c.2 x, mem_memStates.2 hc.2.2⟩
  else S

/-- The ghost operation `𝒢_j` on the capped memory space. -/
noncomputable def ghostOp (B : ℕ) : (MemState X B → ℂ) → MemState X B → ℂ :=
  choiceOp (multBox B ×ˢ multBox B) (ghostCoef hit ν del surv cre B) (ghostOut hit B)

variable {hit ν del surv cre}

omit [Fintype X] [DecidableEq X] in
theorem abs_ghostFactor (hν : ∀ x, 0 ≤ ν x) (hsurv : 0 ≤ surv) (x : X) (h d n : ℕ) :
    |ghostFactor ν del surv cre x h d n| =
      h.choose d * |del| ^ d * surv ^ (h - d) * (|cre x| * ν x) ^ n / n.factorial := by
  simp only [ghostFactor, abs_div, abs_mul, abs_pow, Nat.abs_cast, abs_of_nonneg hsurv,
    abs_of_nonneg (hν x)]

theorem norm_ghostCoef (hν : ∀ x, 0 ≤ ν x) (hsurv : 0 ≤ surv) {B : ℕ} (S : MemState X B)
    {c : (X → ℕ) × (X → ℕ)} (hc : GhostValid hit B S.1 c) :
    ‖ghostCoef hit ν del surv cre B S c‖ = ∏ x, (hitPart hit S.1 x).choose (c.1 x) *
      |del| ^ c.1 x * surv ^ (hitPart hit S.1 x - c.1 x) * (|cre x| * ν x) ^ c.2 x /
        (c.2 x).factorial := by
  rw [ghostCoef, ite_eq_left hc, Complex.norm_real, Real.norm_eq_abs, abs_prod]
  exact prod_congr rfl fun x _ => abs_ghostFactor hν hsurv x _ _ _

/-- The row sums: `∑_c |a(S, c)| v₀^{size(out)} ≤ exp(v₀ ∑_{hits} |cre| ν) v₀^{size(S)}`. -/
theorem ghost_row (hν : ∀ x, 0 ≤ ν x) (hsurv : 0 ≤ surv) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hdel : surv + |del| / v₀ ≤ 1) {B : ℕ} (S : MemState X B) :
    ∑ c ∈ multBox B ×ˢ multBox B,
        ‖ghostCoef hit ν del surv cre B S c‖ * v₀ ^ memSize (ghostOut hit B S c).1 ≤
      Real.exp (v₀ * ∑ x with hit x, |cre x| * ν x) * v₀ ^ memSize S.1 := by
  -- the per-particle bound `G`
  set G : X → ℕ → ℕ → ℝ := fun x d n =>
    if d ≤ hitPart hit S.1 x ∧ (hit x ∨ n = 0) then
      (hitPart hit S.1 x).choose d * (|del| / v₀) ^ d * surv ^ (hitPart hit S.1 x - d) *
        ((|cre x| * ν x * v₀) ^ n / n.factorial)
    else 0 with hG
  have hG0 : ∀ x d n, 0 ≤ G x d n := by
    intro x d n
    simp only [hG]
    split_ifs
    · have := hν x
      positivity
    · exact le_rfl
  -- each choice is bounded by `v₀^{size(S)} ∏_x G`
  have hterm : ∀ c ∈ multBox B ×ˢ multBox B,
      ‖ghostCoef hit ν del surv cre B S c‖ * v₀ ^ memSize (ghostOut hit B S c).1 ≤
        v₀ ^ memSize S.1 * ∏ x, G x (c.1 x) (c.2 x) := by
    intro c _
    by_cases hc : GhostValid hit B S.1 c
    · rw [norm_ghostCoef hν hsurv S hc, ghostOut, dite_eq_left hc]
      simp only [memSize]
      rw [← prod_pow_eq_pow_sum, ← prod_pow_eq_pow_sum, ← prod_mul_distrib,
        ← prod_mul_distrib]
      refine le_of_eq (prod_congr rfl fun x _ => ?_)
      have hd := hc.1 x
      have hn : hit x ∨ c.2 x = 0 := by
        by_cases hx : hit x
        · exact Or.inl hx
        · exact Or.inr (hc.2.1 x hx)
      have hhs : hitPart hit S.1 x ≤ S.1 x := by
        unfold hitPart; split_ifs <;> omega
      rw [hG]
      dsimp only
      rw [ite_eq_left ⟨hd, hn⟩]
      obtain ⟨r, hr⟩ : ∃ r, S.1 x = r + c.1 x := ⟨S.1 x - c.1 x, by omega⟩
      rw [hr, show r + c.1 x - c.1 x + c.2 x = r + c.2 x by omega, pow_add, pow_add]
      have hv : v₀ ≠ 0 := hv₀.ne'
      simp only [div_pow, mul_pow]
      field_simp
    · rw [ghostCoef, ite_eq_right hc, norm_zero, zero_mul]
      exact mul_nonneg (pow_nonneg hv₀.le _) (prod_nonneg fun x _ => hG0 x _ _)
  -- sum over the box, factor over particles, and bound each factor
  have hfac : ∀ x, ∑ d ∈ range (B + 1), ∑ n ∈ range (B + 1), G x d n ≤
      if hit x then Real.exp (|cre x| * ν x * v₀) else 1 := by
    intro x
    have hhB : hitPart hit S.1 x ≤ B := by
      have := mem_memStates.1 S.2
      have := le_memSize S.1 x
      unfold hitPart; split_ifs <;> omega
    refine sum_binom_exp_le (hit x) (div_nonneg (abs_nonneg _) hv₀.le) hsurv
      (by have := hν x; positivity) (by linarith) hhB fun hx => ?_
    simp [hitPart, hx]
  calc ∑ c ∈ multBox B ×ˢ multBox B,
        ‖ghostCoef hit ν del surv cre B S c‖ * v₀ ^ memSize (ghostOut hit B S c).1
      ≤ ∑ c ∈ multBox B ×ˢ multBox B, v₀ ^ memSize S.1 * ∏ x, G x (c.1 x) (c.2 x) :=
        sum_le_sum hterm
    _ = v₀ ^ memSize S.1 * ∏ x, ∑ d ∈ range (B + 1), ∑ n ∈ range (B + 1), G x d n := by
        rw [← mul_sum, sum_multBox_prod]
    _ ≤ v₀ ^ memSize S.1 * ∏ x, (if hit x then Real.exp (|cre x| * ν x * v₀) else 1) :=
        mul_le_mul_of_nonneg_left (prod_le_prod₀
          (fun x _ => sum_nonneg fun d _ => sum_nonneg fun n _ => hG0 x d n)
          (fun x _ => hfac x)) (pow_nonneg hv₀.le _)
    _ = Real.exp (v₀ * ∑ x with hit x, |cre x| * ν x) * v₀ ^ memSize S.1 := by
        rw [prod_ite, prod_const_one, mul_one, ← Real.exp_sum, mul_sum, mul_comm]
        congr 2
        exact sum_congr rfl fun x _ => by ring

omit [Fintype X] [DecidableEq X] in
/-- `C(r + d, d) / (r + d)! = 1 / (r! d!)`, in the form used for the column identity. -/
theorem choose_cast_eq (r d : ℕ) :
    (((r + d).choose d : ℕ) : ℝ) = ((r + d).factorial : ℝ) / (r.factorial * d.factorial) := by
  rw [eq_div_iff (by positivity), ← Nat.add_choose_mul_factorial_mul_factorial r d]
  push_cast
  ring

/-- The column sums:
`∑_{S, c : out(S, c) = T} w(S) |a(S, c)| v₀^{size(S)} ≤ exp(v₀ |del| ∑_{hits} ν) w(T) v₀^{size(T)}`.
A choice `(D, N)` with output `T` comes from at most one input, `S = T - N + D`. For that
input the factorial weights turn the choice into the adjoint one (`mem:ghost-factorial`):
choose the `n` births among the `t` hits of `T`, and integrate the `d` deletions against
`ν^{⊗d} / d!`. -/
theorem ghost_col (hν : ∀ x, 0 ≤ ν x) (hsurv : 0 ≤ surv) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hcre : ∀ x, surv + |cre x| / v₀ ≤ 1) {B : ℕ} (T : MemState X B) :
    ∑ S : MemState X B, ∑ c ∈ multBox B ×ˢ multBox B with ghostOut hit B S c = T,
        memWeight ν S.1 * ‖ghostCoef hit ν del surv cre B S c‖ * v₀ ^ memSize S.1 ≤
      Real.exp (v₀ * |del| * ∑ x with hit x, ν x) * (memWeight ν T.1 * v₀ ^ memSize T.1) := by
  have hv : v₀ ≠ 0 := hv₀.ne'
  -- the per-particle column factor `G'`: `d` deletions, `n` births
  set G' : X → ℕ → ℕ → ℝ := fun x d n =>
    if n ≤ hitPart hit T.1 x ∧ (hit x ∨ d = 0) then
      (hitPart hit T.1 x).choose n * (|cre x| / v₀) ^ n * surv ^ (hitPart hit T.1 x - n) *
        ((|del| * ν x * v₀) ^ d / d.factorial)
    else 0 with hG'
  have hG'0 : ∀ x d n, 0 ≤ G' x d n := by
    intro x d n
    simp only [hG']
    split_ifs
    · have := hν x
      positivity
    · exact le_rfl
  set V : (X → ℕ) × (X → ℕ) → ℝ := fun c =>
    memWeight ν T.1 * v₀ ^ memSize T.1 * ∏ x, G' x (c.1 x) (c.2 x) with hV
  have hV0 : ∀ c, 0 ≤ V c := fun c =>
    mul_nonneg (mul_nonneg (memWeight_nonneg hν _) (pow_nonneg hv₀.le _))
      (prod_nonneg fun x _ => hG'0 x _ _)
  -- for a valid choice with output `T`, the input is `T - N + D`
  have hout : ∀ (S : MemState X B) (c : (X → ℕ) × (X → ℕ)), GhostValid hit B S.1 c →
      ghostOut hit B S c = T → ∀ x, T.1 x = S.1 x - c.1 x + c.2 x := by
    intro S c hc hST x
    rw [← hST, ghostOut, dite_eq_left hc]
  have hdS : ∀ (S : MemState X B) (c : (X → ℕ) × (X → ℕ)), GhostValid hit B S.1 c →
      ∀ x, c.1 x ≤ S.1 x := by
    intro S c hc x
    have := hc.1 x
    unfold hitPart at this
    split_ifs at this <;> omega
  -- the identity for the unique input
  have hval : ∀ (S : MemState X B) (c : (X → ℕ) × (X → ℕ)), GhostValid hit B S.1 c →
      ghostOut hit B S c = T →
      memWeight ν S.1 * ‖ghostCoef hit ν del surv cre B S c‖ * v₀ ^ memSize S.1 = V c := by
    intro S c hc hST
    rw [norm_ghostCoef hν hsurv S hc, hV]
    simp only [memWeight, memSize]
    rw [← prod_pow_eq_pow_sum, ← prod_pow_eq_pow_sum, ← prod_mul_distrib, ← prod_mul_distrib,
      ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun x _ => ?_
    have hT := hout S c hc hST x
    have hd := hdS S c hc x
    rw [hG']
    dsimp only
    by_cases hx : hit x
    · simp only [hitPart, hx, ite_true] at hT ⊢
      rw [ite_eq_left ⟨by omega, Or.inl trivial⟩]
      obtain ⟨r, hr⟩ : ∃ r, S.1 x = r + c.1 x := ⟨S.1 x - c.1 x, by omega⟩
      have hTr : T.1 x = r + c.2 x := by omega
      rw [hr, hTr, show r + c.1 x - c.1 x = r by omega, show r + c.2 x - c.2 x = r by omega,
        choose_cast_eq, choose_cast_eq, pow_add, pow_add, pow_add, pow_add]
      simp only [div_pow, mul_pow]
      field_simp
    · have hd0 : c.1 x = 0 := by
        have := hc.1 x
        simp only [hitPart, hx, ite_false] at this
        omega
      have hn0 : c.2 x = 0 := hc.2.1 x hx
      simp only [hitPart, hx, ite_false] at hT ⊢
      rw [ite_eq_left ⟨by omega, Or.inr hd0⟩, hT, hd0, hn0]
      simp
  -- each choice contributes at most `V c`
  have hchoice : ∀ c ∈ multBox B ×ˢ multBox B,
      ∑ S ∈ univ.filter (fun S : MemState X B => ghostOut hit B S c = T),
        memWeight ν S.1 * ‖ghostCoef hit ν del surv cre B S c‖ * v₀ ^ memSize S.1 ≤ V c := by
    intro c _
    rw [← sum_filter_of_ne (p := fun S : MemState X B => GhostValid hit B S.1 c)]
    · refine (sum_le_card_nsmul _ _ (V c) fun S hS => ?_).trans ?_
      · simp only [mem_filter] at hS
        exact (hval S c hS.2 hS.1.2).le
      · have hcard : ((univ.filter fun S : MemState X B => ghostOut hit B S c = T).filter
            fun S => GhostValid hit B S.1 c).card ≤ 1 := by
          refine card_le_one.2 fun S hS S' hS' => ?_
          simp only [mem_filter] at hS hS'
          refine Subtype.ext (funext fun x => ?_)
          have h₁ := hout S c hS.2 hS.1.2 x
          have h₂ := hout S' c hS'.2 hS'.1.2 x
          have h₃ := hdS S c hS.2 x
          have h₄ := hdS S' c hS'.2 x
          omega
        calc _ • V c ≤ 1 • V c := nsmul_le_nsmul_left (hV0 c) hcard
          _ = V c := one_nsmul _
    · intro S _ hne
      by_contra hc
      rw [ghostCoef, ite_eq_right hc, norm_zero, mul_zero, zero_mul] at hne
      exact hne rfl
  -- the per-particle bound, with the roles of births and deletions exchanged
  have hfac : ∀ x, ∑ d ∈ range (B + 1), ∑ n ∈ range (B + 1), G' x d n ≤
      if hit x then Real.exp (|del| * ν x * v₀) else 1 := by
    intro x
    have hhB : hitPart hit T.1 x ≤ B := by
      have := mem_memStates.1 T.2
      have := le_memSize T.1 x
      unfold hitPart; split_ifs <;> omega
    rw [sum_comm]
    refine sum_binom_exp_le (hit x) (div_nonneg (abs_nonneg _) hv₀.le) hsurv
      (by have := hν x; positivity) (by linarith [hcre x]) hhB fun hx => ?_
    simp [hitPart, hx]
  calc ∑ S : MemState X B, ∑ c ∈ multBox B ×ˢ multBox B with ghostOut hit B S c = T,
        memWeight ν S.1 * ‖ghostCoef hit ν del surv cre B S c‖ * v₀ ^ memSize S.1
      = ∑ c ∈ multBox B ×ˢ multBox B,
          ∑ S ∈ univ.filter (fun S : MemState X B => ghostOut hit B S c = T),
            memWeight ν S.1 * ‖ghostCoef hit ν del surv cre B S c‖ * v₀ ^ memSize S.1 :=
        sum_comm' fun S c => by simp only [mem_filter, mem_univ, true_and, and_comm]
    _ ≤ ∑ c ∈ multBox B ×ˢ multBox B, V c := sum_le_sum hchoice
    _ = memWeight ν T.1 * v₀ ^ memSize T.1 *
          ∏ x, ∑ d ∈ range (B + 1), ∑ n ∈ range (B + 1), G' x d n := by
        rw [hV, ← mul_sum, sum_multBox_prod]
    _ ≤ memWeight ν T.1 * v₀ ^ memSize T.1 *
          ∏ x, (if hit x then Real.exp (|del| * ν x * v₀) else 1) :=
        mul_le_mul_of_nonneg_left (prod_le_prod₀
          (fun x _ => sum_nonneg fun d _ => sum_nonneg fun n _ => hG'0 x d n)
          (fun x _ => hfac x)) (mul_nonneg (memWeight_nonneg hν _) (pow_nonneg hv₀.le _))
    _ = Real.exp (v₀ * |del| * ∑ x with hit x, ν x) * (memWeight ν T.1 * v₀ ^ memSize T.1) := by
        rw [prod_ite, prod_const_one, mul_one, ← Real.exp_sum, mul_sum, mul_comm]
        congr 2
        exact sum_congr rfl fun x _ => by ring

/-- **The ghost bound** (PD `mem:ghost-norm`): if `v₀` makes `surv + |del|/v₀` and every
`surv + |cre|/v₀` at most one, the ghost operation has norm at most
`√(exp(v₀ ∑_{hits} |cre| ν) exp(v₀ |del| ∑_{hits} ν))` on the capped memory space. -/
theorem ghostOp_normLe (hν : ∀ x, 0 ≤ ν x) (hsurv : 0 ≤ surv) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hdel : surv + |del| / v₀ ≤ 1) (hcre : ∀ x, surv + |cre x| / v₀ ≤ 1) (B : ℕ) :
    NormLe (fun S : MemState X B => memWeight ν S.1) (fun S : MemState X B => memWeight ν S.1)
      (ghostOp hit ν del surv cre B)
      (Real.sqrt (Real.exp (v₀ * ∑ x with hit x, |cre x| * ν x) *
        Real.exp (v₀ * |del| * ∑ x with hit x, ν x))) := by
  refine normLe_choiceOp (h := fun S => v₀ ^ memSize S.1) (h' := fun S => v₀ ^ memSize S.1)
    (Real.exp_pos _).le (Real.exp_pos _).le (fun S => memWeight_nonneg hν _)
    (fun S => pow_pos hv₀ _) (fun S => ?_) (fun T => ?_)
  · exact ghost_row hν hsurv hv₀ hdel S
  · exact ghost_col hν hsurv hv₀ hcre T

end Ghost

end Erdos408.OneSided
