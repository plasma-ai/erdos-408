import Erdos408.OneSided.Moment.Phased.Rows

/-!
# Ghost rows with prescribed births

PD `mem:ghost-atoms`: a ghost row with prescribed batch primes. If `s` ordered coordinates of
a batch are prescribed, the creation sum `∑_n ∏_x (|cre| ν v₀)^{n_x} / n_x!` only runs over
the batches containing each prescribed prime with its multiplicity, and each prescribed
coordinate costs one atom `|cre| ν v₀ ≤ c ν(p)`.

* `sum_binom_exp_req_le`, `ghost_row_req`: the row sums of the ghost operation of
  `Memory/Ghost.lean` restricted to `n ≥ m` are at most
  `∏_{x hit} (|cre x| ν x v₀)^{m x} exp(v₀ ∑_{hits} |cre| ν) v₀^{size}`, since
  `∑_{n ≥ m} e^n / n! ≤ e^m exp(e)`.
* `card_le_count_of_getElem`, `count_batchPrimes`: if a list takes the value `p` at the
  indices of `T`, then `p` occurs at least `|T|` times; the batch primes count the created
  particles of each prime.
* `sum_chainGhost_pres_le`: the weighted row sums of a chain ghost against the prescription
  indicators `∏_k [β_k = π_k]` of its batch indices are at most `∏_k atomCost(π_k)` times the
  row factor `exp(v₀ ∑_{hits} |cre| ν)`. A hitting particle is determined by its prime, so the
  required multiplicities live on the hitting particles.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset

/-! ### Required births in the ghost operation -/

section Generic

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The tail of the exponential series: `∑_{n ≤ B, n ≥ m} e^n / n! ≤ e^m exp(e)`. -/
theorem sum_exp_tail_le {B m : ℕ} {e : ℝ} (he : 0 ≤ e) :
    ∑ n ∈ range (B + 1), e ^ n / n.factorial * (if m ≤ n then 1 else 0) ≤ e ^ m * Real.exp e := by
  set g : ℕ → ℝ := fun k => e ^ k / k.factorial with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => by positivity
  -- each term is at most `e^m g(n - m)`
  have hpt : ∀ n ∈ range (B + 1), e ^ n / n.factorial * (if m ≤ n then 1 else 0) ≤
      e ^ m * ((if m ≤ n then 1 else 0) * g (n - m)) := by
    intro n _
    split_ifs with hmn
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [Nat.add_sub_cancel_left, hg, mul_one, one_mul, pow_add, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_) (by positivity)
      exact_mod_cast Nat.factorial_le (Nat.le_add_left k m)
    · simp
  -- the shifted terms are a part of the exponential series
  have hshift : ∑ n ∈ range (B + 1), (if m ≤ n then 1 else 0) * g (n - m) ≤
      ∑ k ∈ range (B + 1), g k := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [← sum_filter, ← sum_image (g := fun n => n - m) (f := g) fun n hn n' hn' h => by
      rw [mem_coe, mem_filter] at hn hn'
      simp only at h
      omega]
    refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => hg0 k
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hk
    simp only [mem_filter, mem_range] at hn ⊢
    omega
  calc ∑ n ∈ range (B + 1), e ^ n / n.factorial * (if m ≤ n then 1 else 0)
      ≤ ∑ n ∈ range (B + 1), e ^ m * ((if m ≤ n then 1 else 0) * g (n - m)) := sum_le_sum hpt
    _ = e ^ m * ∑ n ∈ range (B + 1), (if m ≤ n then 1 else 0) * g (n - m) := (mul_sum _ _ _).symm
    _ ≤ e ^ m * ∑ k ∈ range (B + 1), g k := mul_le_mul_of_nonneg_left hshift (by positivity)
    _ ≤ e ^ m * Real.exp e :=
        mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg he _) (by positivity)

omit [Fintype X] [DecidableEq X] in
/-- The per-particle sum with at least `m` births: the binomial theorem in the first variable
and the tail of the exponential series in the second. For a particle that cannot hit, only
`(0, 0)` survives. -/
theorem sum_binom_exp_req_le {B s m : ℕ} {a b e : ℝ} (P : Prop) [Decidable P] (ha : 0 ≤ a)
    (hb : 0 ≤ b) (he : 0 ≤ e) (hab : a + b ≤ 1) (hs : s ≤ B) (hP : ¬P → s = 0) :
    ∑ d ∈ range (B + 1), ∑ n ∈ range (B + 1),
        (if d ≤ s ∧ (P ∨ n = 0) then
          s.choose d * a ^ d * b ^ (s - d) * (e ^ n / n.factorial) else 0) *
          (if m ≤ n then 1 else 0) ≤
      if P then e ^ m * Real.exp e else 1 := by
  by_cases hP' : P
  · simp only [hP', true_or, and_true, ite_true]
    have h₁ : ∀ d ∈ range (B + 1), ∑ n ∈ range (B + 1),
        (if d ≤ s then s.choose d * a ^ d * b ^ (s - d) * (e ^ n / n.factorial) else 0) *
          (if m ≤ n then 1 else 0) =
        (if d ≤ s then s.choose d * a ^ d * b ^ (s - d) else 0) *
          ∑ n ∈ range (B + 1), e ^ n / n.factorial * (if m ≤ n then 1 else 0) := by
      intro d _
      rw [mul_sum]
      refine sum_congr rfl fun n _ => ?_
      split_ifs <;> ring
    rw [sum_congr rfl h₁, ← sum_mul]
    -- the binomial theorem
    have h₂ : ∑ d ∈ range (B + 1), (if d ≤ s then s.choose d * a ^ d * b ^ (s - d) else 0) =
        (a + b) ^ s := by
      rw [← sum_filter, add_pow]
      have : (range (B + 1)).filter (· ≤ s) = range (s + 1) := by
        ext d; simp only [mem_filter, mem_range]; omega
      rw [this]
      exact sum_congr rfl fun d _ => by ring
    rw [h₂]
    calc (a + b) ^ s * ∑ n ∈ range (B + 1), e ^ n / n.factorial * (if m ≤ n then 1 else 0)
        ≤ 1 * (e ^ m * Real.exp e) :=
          mul_le_mul (pow_le_one₀ (add_nonneg ha hb) hab) (sum_exp_tail_le he)
            (sum_nonneg fun n _ => mul_nonneg (by positivity) (by split_ifs <;> norm_num))
            zero_le_one
      _ = e ^ m * Real.exp e := one_mul _
  · -- the requirement only removes terms
    have h := sum_binom_exp_le (B := B) P ha hb he hab hs hP
    simp only [hP', ↓reduceIte] at h ⊢
    refine le_trans (sum_le_sum fun d _ => sum_le_sum fun n _ => ?_) h
    refine mul_le_of_le_one_right ?_ (by split_ifs <;> norm_num)
    split_ifs
    · positivity
    · exact le_rfl

variable {hit : X → Prop} [DecidablePred hit] {ν : X → ℝ} {del surv : ℝ} {cre : X → ℝ}

/-- **The ghost rows with required births**: restricted to the choices with at least `m x`
births of each particle `x`, the weighted row sums are at most
`∏_{x hit} (|cre x| ν x v₀)^{m x} exp(v₀ ∑_{hits} |cre| ν) v₀^{size(S)}`. -/
theorem ghost_row_req (hν : ∀ x, 0 ≤ ν x) (hsurv : 0 ≤ surv) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hdel : surv + |del| / v₀ ≤ 1) (m : X → ℕ) {B : ℕ} (S : MemState X B) :
    ∑ c ∈ multBox B ×ˢ multBox B,
        ‖ghostCoef hit ν del surv cre B S c‖ * (∏ x, if m x ≤ c.2 x then (1 : ℝ) else 0) *
          v₀ ^ memSize (ghostOut hit B S c).1 ≤
      (∏ x, if hit x then (|cre x| * ν x * v₀) ^ m x else 1) *
        (Real.exp (v₀ * ∑ x with hit x, |cre x| * ν x) * v₀ ^ memSize S.1) := by
  -- the per-particle bound `G`, with the requirement
  set G : X → ℕ → ℕ → ℝ := fun x d n =>
    (if d ≤ hitPart hit S.1 x ∧ (hit x ∨ n = 0) then
      (hitPart hit S.1 x).choose d * (|del| / v₀) ^ d * surv ^ (hitPart hit S.1 x - d) *
        ((|cre x| * ν x * v₀) ^ n / n.factorial)
    else 0) * (if m x ≤ n then 1 else 0) with hG
  have hG0 : ∀ x d n, 0 ≤ G x d n := by
    intro x d n
    simp only [hG]
    refine mul_nonneg ?_ (by split_ifs <;> norm_num)
    split_ifs
    · have := hν x
      positivity
    · exact le_rfl
  -- each choice is bounded by `v₀^{size(S)} ∏_x G`
  have hterm : ∀ c ∈ multBox B ×ˢ multBox B,
      ‖ghostCoef hit ν del surv cre B S c‖ * (∏ x, if m x ≤ c.2 x then (1 : ℝ) else 0) *
          v₀ ^ memSize (ghostOut hit B S c).1 ≤
        v₀ ^ memSize S.1 * ∏ x, G x (c.1 x) (c.2 x) := by
    intro c _
    by_cases hc : GhostValid hit B S.1 c
    · rw [norm_ghostCoef hν hsurv S hc, ghostOut, dite_eq_left hc]
      simp only [memSize]
      rw [← prod_pow_eq_pow_sum, ← prod_pow_eq_pow_sum, ← prod_mul_distrib,
        ← prod_mul_distrib, ← prod_mul_distrib]
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
      rw [ite_eq_left (show c.1 x ≤ hitPart hit S.1 x ∧ (hit x ∨ c.2 x = 0) from ⟨hd, hn⟩)]
      obtain ⟨r, hr⟩ : ∃ r, S.1 x = r + c.1 x := ⟨S.1 x - c.1 x, by omega⟩
      rw [hr, show r + c.1 x - c.1 x + c.2 x = r + c.2 x by omega, pow_add, pow_add]
      have hv : v₀ ≠ 0 := hv₀.ne'
      simp only [div_pow, mul_pow]
      field_simp
    · rw [ghostCoef, ite_eq_right hc, norm_zero, zero_mul, zero_mul]
      exact mul_nonneg (pow_nonneg hv₀.le _) (prod_nonneg fun x _ => hG0 x _ _)
  -- sum over the box, factor over particles, and bound each factor
  have hfac : ∀ x, ∑ d ∈ range (B + 1), ∑ n ∈ range (B + 1), G x d n ≤
      if hit x then (|cre x| * ν x * v₀) ^ m x * Real.exp (|cre x| * ν x * v₀) else 1 := by
    intro x
    have hhB : hitPart hit S.1 x ≤ B := by
      have := mem_memStates.1 S.2
      have := le_memSize S.1 x
      unfold hitPart; split_ifs <;> omega
    refine sum_binom_exp_req_le (hit x) (div_nonneg (abs_nonneg _) hv₀.le) hsurv
      (by have := hν x; positivity) (by linarith) hhB fun hx => ?_
    simp [hitPart, hx]
  calc ∑ c ∈ multBox B ×ˢ multBox B,
        ‖ghostCoef hit ν del surv cre B S c‖ * (∏ x, if m x ≤ c.2 x then (1 : ℝ) else 0) *
          v₀ ^ memSize (ghostOut hit B S c).1
      ≤ ∑ c ∈ multBox B ×ˢ multBox B, v₀ ^ memSize S.1 * ∏ x, G x (c.1 x) (c.2 x) :=
        sum_le_sum hterm
    _ = v₀ ^ memSize S.1 * ∏ x, ∑ d ∈ range (B + 1), ∑ n ∈ range (B + 1), G x d n := by
        rw [← mul_sum, sum_multBox_prod]
    _ ≤ v₀ ^ memSize S.1 * ∏ x, (if hit x then
          (|cre x| * ν x * v₀) ^ m x * Real.exp (|cre x| * ν x * v₀) else 1) :=
        mul_le_mul_of_nonneg_left (prod_le_prod₀
          (fun x _ => sum_nonneg fun d _ => sum_nonneg fun n _ => hG0 x d n)
          (fun x _ => hfac x)) (pow_nonneg hv₀.le _)
    _ = (∏ x, if hit x then (|cre x| * ν x * v₀) ^ m x else 1) *
          (Real.exp (v₀ * ∑ x with hit x, |cre x| * ν x) * v₀ ^ memSize S.1) := by
        have hsplit : ∀ x, (if hit x then
            (|cre x| * ν x * v₀) ^ m x * Real.exp (|cre x| * ν x * v₀) else 1) =
            (if hit x then (|cre x| * ν x * v₀) ^ m x else 1) *
              (if hit x then Real.exp (|cre x| * ν x * v₀) else 1) := fun x => by
          split_ifs <;> ring
        simp only [hsplit, prod_mul_distrib]
        rw [prod_ite (fun x => Real.exp (|cre x| * ν x * v₀)), prod_const_one, mul_one,
          ← Real.exp_sum, mul_sum]
        have hexp : ∑ x with hit x, |cre x| * ν x * v₀ = ∑ x with hit x, v₀ * (|cre x| * ν x) :=
          sum_congr rfl fun x _ => by ring
        rw [hexp]
        ring

end Generic

/-! ### Prescribed indices of a list -/

/-- If a list takes the value `p` at every index of `T`, then `p` occurs at least `|T|`
times. -/
theorem card_le_count_of_getElem {p : ℕ} :
    ∀ (l : List ℕ) (T : Finset ℕ), (∀ k ∈ T, l[k]? = some p) → T.card ≤ l.count p
  | [], T, hT => by
    have hT0 : T = ∅ := eq_empty_of_forall_notMem fun k hk => by simpa using hT k hk
    simp [hT0]
  | a :: l, T, hT => by
    -- the indices after the head shift down by one
    have hT' : ∀ k ∈ (T.erase 0).image (· - 1), l[k]? = some p := by
      intro k hk
      obtain ⟨k₀, hk₀, rfl⟩ := mem_image.1 hk
      obtain ⟨hk₀0, hk₀T⟩ := mem_erase.1 hk₀
      have := hT k₀ hk₀T
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk₀0
      simpa using this
    have hinj : Set.InjOn (· - 1) ((T.erase 0 : Finset ℕ) : Set ℕ) := fun k hk k' hk' h => by
      rw [mem_coe, mem_erase] at hk hk'
      simp only at h
      omega
    have ih := card_le_count_of_getElem l _ hT'
    rw [card_image_of_injOn hinj] at ih
    rw [List.count_cons]
    by_cases h0 : 0 ∈ T
    · have ha : a = p := by simpa using hT 0 h0
      have := card_erase_add_one h0
      simp only [ha, beq_self_eq_true, ite_true]
      omega
    · rw [erase_eq_of_notMem h0] at ih
      omega

variable {K : ℕ}

section Chain

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B : ℕ}

/-- The batch primes count the created particles of each prime:
`#{p in the batch} = ∑_{x : x.prime = p} n(x)`. -/
theorem count_batchPrimes (n : Particle x d → ℕ) (p : ℕ) :
    (batchPrimes x d n).count p = ∑ xp : Particle x d, if xp.1.1 = p then n xp else 0 := by
  rw [batchPrimes, ← Multiset.coe_count, Multiset.sort_eq, Multiset.count_sum']
  exact sum_congr rfl fun xp _ => Multiset.count_replicate _ _ _

/-- Two particles hitting the same position with the same prime are equal: the line of a
hitting particle is `[z]_p`. -/
theorem hitsAt_eq_of_prime {z : ℤ × ℤ} {xp yp : Particle x d} (hx : HitsAt x d z xp)
    (hy : HitsAt x d z yp) (h : xp.1.1 = yp.1.1) : xp = yp := by
  refine Subtype.ext (Prod.ext h ?_)
  rw [← hx, ← hy, h]

/-- For a valid ghost choice, the batch contains each prime with the multiplicity of the
hitting particle of that prime, or not at all. -/
theorem count_batchPrimes_of_valid {z : ℤ × ℤ} {S : Particle x d → ℕ}
    {c : GhostChoice x d} (hc : GhostValid (HitsAt x d z) B S c) (p : ℕ) :
    (batchPrimes x d c.2).count p ≤ 0 ∨
      ∃ xp, HitsAt x d z xp ∧ xp.1.1 = p ∧ (batchPrimes x d c.2).count p = c.2 xp := by
  rw [count_batchPrimes]
  by_cases hex : ∃ xp, HitsAt x d z xp ∧ xp.1.1 = p
  · obtain ⟨xp, hxp, rfl⟩ := hex
    refine Or.inr ⟨xp, hxp, rfl, ?_⟩
    rw [sum_eq_single xp]
    · rw [ite_eq_left rfl]
    · intro yp _ hne
      refine ite_eq_right_iff.2 fun hp => ?_
      by_cases hyp : HitsAt x d z yp
      · exact absurd (hitsAt_eq_of_prime hyp hxp hp) hne
      · exact hc.2.1 yp hyp
    · intro h
      exact absurd (mem_univ _) h
  · refine Or.inl (le_of_eq (sum_eq_zero fun yp _ => ite_eq_right_iff.2 fun hp => ?_))
    by_contra hne
    exact hex ⟨yp, by_contra fun hyp => hne (hc.2.1 yp hyp), hp⟩

/-- **The ghost rows with prescribed batch primes** (PD `mem:ghost-atoms`): the weighted row
sums of a chain ghost against `∏_k [β_k = π_k]`, over the batch indices `k`, are at most
`∏_k atomCost(π_k)` times the row factor `exp(v₀ ∑_{hits} |cre| ν) v₀^{size}`, once each
creation atom `|cre| ν v₀` is at most `c₀ ν`. -/
theorem sum_chainGhost_pres_le {N j : ℕ} (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hsurv : 0 ≤ (1 - dampDefect q N j) / pendingWeight q ^ 2) {v₀ c₀ : ℝ} (hv₀ : 0 < v₀)
    (hc₀0 : 0 ≤ c₀)
    (hdel : (1 - dampDefect q N j) / pendingWeight q ^ 2 +
      |-dampDefect q N j / pendingWeight q| / v₀ ≤ 1)
    (hc₀ : ∀ xp : Particle x d, |-dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q| *
      primeWeight q x d N xp.1.1 * v₀ ≤ c₀ * primeWeight q x d N xp.1.1)
    (π : Fin B → Option ℕ) (t : ChainState x d Y d₀ u v r B) :
    ∑ c ∈ multBox B ×ˢ multBox B, ‖chainGhostCoef q x d Y d₀ u v r B N j t c‖ *
        (∏ k : Fin B, presInd (π k) (batchPrimes x d c.2)[k.1]?) *
        v₀ ^ memSize (chainGhostOut x d Y d₀ u v r B t c).2.2.1 ≤
      (∏ k, atomCost c₀ (primeWeight q x d N) (π k)) *
        (Real.exp (v₀ * ∑ xp with HitsAt x d t.1.1 xp,
          |-dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q| *
            primeWeight q x d N xp.1.1) * v₀ ^ memSize t.2.2.1) := by
  classical
  set z := t.1.1 with hz
  set ν : ℕ → ℝ := primeWeight q x d N with hνdef
  set cre : Particle x d → ℝ :=
    fun xp => -dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q with hcre
  have hRHS0 : 0 ≤ (∏ k, atomCost c₀ ν (π k)) *
      (Real.exp (v₀ * ∑ xp with HitsAt x d z xp, |cre xp| * ν xp.1.1) * v₀ ^ memSize t.2.2.1) :=
    mul_nonneg (prod_nonneg fun k _ => atomCost_nonneg hc₀0 hν _)
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg hv₀.le _))
  -- the prescriptions met by a valid choice: each prescribed prime occurs with multiplicity
  have hmet : ∀ c : GhostChoice x d, GhostValid (HitsAt x d z) B t.2.2.1 c →
      (∏ k : Fin B, presInd (π k) (batchPrimes x d c.2)[k.1]?) ≠ 0 →
      ∀ p, (univ.filter fun k : Fin B => π k = some p).card ≤ (batchPrimes x d c.2).count p := by
    intro c _ hW p
    rw [← card_image_of_injective _ Fin.val_injective]
    refine card_le_count_of_getElem _ _ fun k hk => ?_
    obtain ⟨k', hk', rfl⟩ := mem_image.1 hk
    have hkp := (mem_filter.1 hk').2
    have hne := (prod_ne_zero_iff.1 hW) k' (mem_univ _)
    unfold presInd at hne
    rw [hkp] at hne
    by_contra h
    exact hne (ite_eq_right (by simp [h]))
  by_cases hall : ∀ k p, π k = some p → ∃ xp, HitsAt x d z xp ∧ xp.1.1 = p
  · -- the required multiplicities on the hitting particles
    set m : Particle x d → ℕ := fun xp =>
      if HitsAt x d z xp then (univ.filter fun k : Fin B => π k = some xp.1.1).card else 0
      with hm
    have hle : ∀ c ∈ multBox B ×ˢ multBox B, ‖chainGhostCoef q x d Y d₀ u v r B N j t c‖ *
        (∏ k : Fin B, presInd (π k) (batchPrimes x d c.2)[k.1]?) *
        v₀ ^ memSize (chainGhostOut x d Y d₀ u v r B t c).2.2.1 ≤
        ‖ghostCoef (HitsAt x d z) (fun xp : Particle x d => ν xp.1.1)
            (-dampDefect q N j / pendingWeight q) ((1 - dampDefect q N j) / pendingWeight q ^ 2)
            cre B t.2.2 c‖ * (∏ xp, if m xp ≤ c.2 xp then (1 : ℝ) else 0) *
          v₀ ^ memSize (ghostOut (HitsAt x d z) B t.2.2 c).1 := by
      intro c _
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hv₀.le _)
      by_cases hc : GhostValid (HitsAt x d z) B t.2.2.1 c
      · by_cases hW : (∏ k : Fin B, presInd (π k) (batchPrimes x d c.2)[k.1]?) = 0
        · rw [hW, mul_zero]
          exact mul_nonneg (norm_nonneg _) (prod_nonneg fun xp _ => by split_ifs <;> norm_num)
        · -- every requirement holds, and the prescriptions are at most one
          have hreq : ∀ xp, m xp ≤ c.2 xp := by
            intro xp
            simp only [hm]
            split_ifs with hxp
            · have h₁ := hmet c hc hW xp.1.1
              rcases count_batchPrimes_of_valid hc xp.1.1 with h₂ | ⟨yp, hyp, hp, h₂⟩
              · omega
              · have hxy := hitsAt_eq_of_prime hxp hyp hp.symm
                subst hxy
                omega
            · exact Nat.zero_le _
          rw [prod_eq_one fun xp _ => ite_eq_left (hreq xp), mul_one]
          exact mul_le_of_le_one_right (norm_nonneg _)
            (prod_le_one₀ (fun k _ => presInd_nonneg _ _) fun k _ => presInd_le_one _ _)
      · change ‖ghostCoef (HitsAt x d z) _ _ _ _ B t.2.2 c‖ * _ ≤ _
        rw [ghostCoef, ite_eq_right hc, norm_zero, zero_mul, zero_mul]
    -- convert the hitting atoms into the atoms of the prescriptions
    have hconv : (∏ xp : Particle x d, if HitsAt x d z xp then
        (|cre xp| * ν xp.1.1 * v₀) ^ m xp else 1) ≤ ∏ k, atomCost c₀ ν (π k) := by
      have hk : ∀ k, atomCost c₀ ν (π k) = ∏ xp : Particle x d,
          if HitsAt x d z xp ∧ π k = some xp.1.1 then c₀ * ν xp.1.1 else 1 := by
        intro k
        cases hπ : π k with
        | none => simp [atomCost]
        | some p =>
          obtain ⟨x₀, hx₀, rfl⟩ := hall k _ hπ
          rw [prod_eq_single x₀]
          · simp [atomCost, hx₀]
          · intro xp _ hne
            refine ite_eq_right fun h => absurd (hitsAt_eq_of_prime h.1 hx₀ ?_) hne
            exact (Option.some_injective _ h.2).symm
          · intro h
            exact absurd (mem_univ _) h
      simp only [hk]
      rw [prod_comm]
      have he0 : ∀ xp : Particle x d, 0 ≤ |cre xp| * ν xp.1.1 * v₀ := fun xp =>
        mul_nonneg (mul_nonneg (abs_nonneg _) (hν _)) hv₀.le
      refine prod_le_prod₀ (fun xp _ => by
        split_ifs
        exacts [pow_nonneg (he0 xp) _, zero_le_one]) fun xp _ => ?_
      by_cases hxp : HitsAt x d z xp
      · simp only [hxp, true_and, ite_true, hm]
        rw [prod_ite, prod_const, prod_const_one, mul_one]
        exact pow_le_pow_left₀ (he0 xp) (hc₀ xp) _
      · simp [hxp]
    calc _ ≤ ∑ c ∈ multBox B ×ˢ multBox B,
          ‖ghostCoef (HitsAt x d z) (fun xp : Particle x d => ν xp.1.1)
              (-dampDefect q N j / pendingWeight q) ((1 - dampDefect q N j) / pendingWeight q ^ 2)
              cre B t.2.2 c‖ * (∏ xp, if m xp ≤ c.2 xp then (1 : ℝ) else 0) *
            v₀ ^ memSize (ghostOut (HitsAt x d z) B t.2.2 c).1 := sum_le_sum hle
      _ ≤ (∏ xp : Particle x d, if HitsAt x d z xp then
            (|cre xp| * ν xp.1.1 * v₀) ^ m xp else 1) *
          (Real.exp (v₀ * ∑ xp with HitsAt x d z xp, |cre xp| * ν xp.1.1) *
            v₀ ^ memSize t.2.2.1) :=
          ghost_row_req (fun xp => hν _) hsurv hv₀ hdel m t.2.2
      _ ≤ _ := mul_le_mul_of_nonneg_right hconv
          (mul_nonneg (Real.exp_pos _).le (pow_nonneg hv₀.le _))
  · -- some prescribed prime has no hitting particle, so every valid choice misses it
    push Not at hall
    obtain ⟨k₀, p, hk₀, hp⟩ := hall
    refine le_trans (le_of_eq (sum_eq_zero fun c _ => ?_)) hRHS0
    by_cases hc : GhostValid (HitsAt x d z) B t.2.2.1 c
    · by_cases hW : (∏ k : Fin B, presInd (π k) (batchPrimes x d c.2)[k.1]?) = 0
      · rw [hW, mul_zero, zero_mul]
      · have h₁ := hmet c hc hW p
        have h₀ : 1 ≤ (univ.filter fun k : Fin B => π k = some p).card :=
          card_pos.2 ⟨k₀, mem_filter.2 ⟨mem_univ _, hk₀⟩⟩
        rcases count_batchPrimes_of_valid hc p with h₂ | ⟨yp, hyp, hyp', -⟩
        · omega
        · exact absurd hyp' (hp yp hyp)
    · change ‖ghostCoef (HitsAt x d z) _ _ _ _ B t.2.2 c‖ * _ * _ = 0
      rw [ghostCoef, ite_eq_right hc, norm_zero, zero_mul, zero_mul]

end Chain

end Erdos408.OneSided
