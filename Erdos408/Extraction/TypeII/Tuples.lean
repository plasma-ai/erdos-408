module

public import Erdos408.Extraction.TypeII.Euler
public import Mathlib.Data.Fin.Tuple.Finset

/-!
# Sums over tuples

Sums over `r`-tuples `m ∈ S^r` of positive integers weighted by `∏ v_k(m_k)`.

* Splitting off coordinate `i`: `∑_{m ∈ S^{r+1}} G(m) = ∑_{m₀ ∈ S} ∑_{m' ∈ S^r} G(m₀ ⋆ m')`.
* Telescoping: `∏ A(m_k) - ∏ B(m_k)` is a sum over `i` of hybrid products with
  `A - B` at `i`, `B` before `i` and `A` after.
* Mass bounds: the tuples with `∏ m ≤ X` have mass `≤ X ∏_k ∑ v_k(a)/a`, and
  `≤ c X ∏_{k ≥ 1} ∑ v_k(a)/a` if `∑_{a ≤ w} v_0(a) ≤ c w`.
* The number of ordered factorizations `n = m_1 ⋯ m_r` is at most `r^{Ω(n)}`.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset

/-- Splitting a tuple sum at coordinate `i`. -/
theorem sum_piFinset_succ_eq {M : Type*} [AddCommMonoid M] (S : Finset ℕ) {r : ℕ}
    (i : Fin (r + 1)) (G : (Fin (r + 1) → ℕ) → M) :
    ∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 1) => S), G m =
      ∑ m₀ ∈ S, ∑ m' ∈ Fintype.piFinset (fun _ : Fin r => S), G (i.insertNth m₀ m') := by
  have h := Finset.filter_piFinset_eq_map_insertNthEquiv (p := i)
    (fun _ : Fin (r + 1) => S) (fun _ => True)
  simp only [filter_true] at h
  rw [h, sum_map, sum_product]
  rfl

/-- The product of `i.insertNth m₀ m'` is `m₀ ∏ m'`. -/
theorem prod_insertNth {r : ℕ} (i : Fin (r + 1)) (m₀ : ℕ) (m' : Fin r → ℕ) :
    ∏ k, (i.insertNth m₀ m' : Fin (r + 1) → ℕ) k = m₀ * ∏ k, m' k := by
  rw [Fin.prod_univ_succAbove _ i]
  simp

/-- Telescoping a difference of products over tuples. -/
theorem sum_prod_sub_prod_eq (S : Finset ℕ) (Ψ : ℕ → ℝ) (A B : ℕ → ℝ) (r : ℕ) :
    ∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 1) => S),
        Ψ (∏ k, m k) * (∏ k, A (m k) - ∏ k, B (m k)) =
      ∑ i : Fin (r + 1), ∑ m₀ ∈ S, ∑ m' ∈ Fintype.piFinset (fun _ : Fin r => S),
        Ψ (m₀ * ∏ k, m' k) * (A m₀ - B m₀) *
          ∏ k, (if i.succAbove k < i then B else A) (m' k) := by
  -- the hybrid with `B` on the coordinates `< i`
  set H : ℕ → ℝ := fun i => ∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 1) => S),
    Ψ (∏ k, m k) * ∏ k : Fin (r + 1), (if (k : ℕ) < i then B else A) (m k) with hH
  have h0 : H 0 = ∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 1) => S),
      Ψ (∏ k, m k) * ∏ k, A (m k) := by simp [hH]
  have h1 : H (r + 1) = ∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 1) => S),
      Ψ (∏ k, m k) * ∏ k, B (m k) := by
    simp only [hH]
    refine sum_congr rfl fun m _ => ?_
    congr 1
    exact prod_congr rfl fun k _ => by simp [k.isLt]
  have hstep : ∀ i : Fin (r + 1), H i - H (i + 1) =
      ∑ m₀ ∈ S, ∑ m' ∈ Fintype.piFinset (fun _ : Fin r => S),
        Ψ (m₀ * ∏ k, m' k) * (A m₀ - B m₀) *
          ∏ k, (if i.succAbove k < i then B else A) (m' k) := by
    intro i
    simp only [hH]
    rw [← sum_sub_distrib, sum_piFinset_succ_eq S i]
    refine sum_congr rfl fun m₀ _ => sum_congr rfl fun m' _ => ?_
    rw [prod_insertNth, Fin.prod_univ_succAbove _ i, Fin.prod_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, lt_irrefl,
      ite_false, lt_add_one, ite_true]
    have hsame : ∀ k : Fin r,
        (if ((i.succAbove k : Fin (r + 1)) : ℕ) < (i : ℕ) + 1 then B else A) =
          (if i.succAbove k < i then B else A) := by
      intro k
      have hne : i.succAbove k ≠ i := Fin.succAbove_ne i k
      have : ((i.succAbove k : Fin (r + 1)) : ℕ) < (i : ℕ) + 1 ↔ i.succAbove k < i := by
        rw [Fin.lt_def]
        constructor
        · intro h
          have : ((i.succAbove k : Fin (r + 1)) : ℕ) ≠ i := fun h' => hne (Fin.ext h')
          omega
        · intro h; omega
      simp only [this]
    have hsame' : ∀ k : Fin r,
        (if ((i.succAbove k : Fin (r + 1)) : ℕ) < (i : ℕ) then B else A) =
          (if i.succAbove k < i then B else A) := by
      intro k
      simp only [Fin.lt_def]
    simp only [hsame, hsame']
    ring
  have hL : ∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 1) => S),
      Ψ (∏ k, m k) * (∏ k, A (m k) - ∏ k, B (m k)) = H 0 - H (r + 1) := by
    rw [h0, h1, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => mul_sub _ _ _
  rw [hL, ← Finset.sum_range_sub' H (r + 1), ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun i _ => ?_
  rw [← hstep i]

/-- The mass of the tuples with `∏ m ≤ X`: at most `X ∏_k ∑_{a ∈ S} v_k(a)/a`. -/
theorem sum_prod_le_mass {S : Finset ℕ} (hS : ∀ a ∈ S, 1 ≤ a) {r : ℕ} (v : Fin r → ℕ → ℝ)
    (hv : ∀ k a, 0 ≤ v k a) {X : ℝ} (hX : 0 ≤ X) :
    ∑ m ∈ Fintype.piFinset (fun _ : Fin r => S),
        (if ((∏ k, m k : ℕ) : ℝ) ≤ X then ∏ k, v k (m k) else 0) ≤
      X * ∏ k, ∑ a ∈ S, v k a / a := by
  rw [prod_univ_sum, mul_sum]
  refine sum_le_sum fun m hm => ?_
  have hpos : ∀ k, (1 : ℝ) ≤ m k := fun k => by
    exact_mod_cast hS _ (Fintype.mem_piFinset.1 hm k)
  have hprodpos : (0 : ℝ) < ∏ k, (m k : ℝ) := prod_pos fun k _ => by linarith [hpos k]
  have hdiv : ∏ k, v k (m k) / m k = (∏ k, v k (m k)) / ∏ k, (m k : ℝ) := prod_div_distrib _ _
  rw [hdiv]
  split_ifs with h
  · push_cast at h
    rw [mul_div, le_div_iff₀ hprodpos]
    exact mul_le_mul_of_nonneg_left h (prod_nonneg fun k _ => hv k _) |>.trans_eq (mul_comm _ _)
  · exact mul_nonneg hX (div_nonneg (prod_nonneg fun k _ => hv k _) hprodpos.le)

/-- The mass bound with a counting bound `∑_{a ≤ w} v_0(a) ≤ c w` on the first factor. -/
theorem sum_prod_le_mass_count {S : Finset ℕ} (hS : ∀ a ∈ S, 1 ≤ a) {r : ℕ}
    (v : Fin (r + 1) → ℕ → ℝ) (hv : ∀ k a, 0 ≤ v k a) {c : ℝ}
    (hc : ∀ w : ℝ, 0 ≤ w → ∑ a ∈ S, (if (a : ℝ) ≤ w then v 0 a else 0) ≤ c * w)
    {X : ℝ} (hX : 0 ≤ X) :
    ∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 1) => S),
        (if ((∏ k, m k : ℕ) : ℝ) ≤ X then ∏ k, v k (m k) else 0) ≤
      c * X * ∏ k : Fin r, ∑ a ∈ S, v k.succ a / a := by
  rw [sum_piFinset_succ_eq S 0, sum_comm, prod_univ_sum, mul_sum]
  refine sum_le_sum fun m' hm' => ?_
  have hpos : ∀ k, (1 : ℝ) ≤ m' k := fun k => by
    exact_mod_cast hS _ (Fintype.mem_piFinset.1 hm' k)
  have hprodpos : (0 : ℝ) < ∏ k, (m' k : ℝ) := prod_pos fun k _ => by linarith [hpos k]
  have hV : 0 ≤ ∏ k : Fin r, v k.succ (m' k) := prod_nonneg fun k _ => hv _ _
  have hterm : ∀ m₀ ∈ S,
      (if ((∏ k, (Fin.insertNth (0 : Fin (r + 1)) m₀ m' : Fin (r + 1) → ℕ) k : ℕ) : ℝ) ≤ X
        then ∏ k, v k ((Fin.insertNth (0 : Fin (r + 1)) m₀ m' : Fin (r + 1) → ℕ) k) else 0) =
        (∏ k : Fin r, v k.succ (m' k)) *
          (if (m₀ : ℝ) ≤ X / ∏ k, (m' k : ℝ) then v 0 m₀ else 0) := by
    intro m₀ _
    rw [prod_insertNth, Fin.prod_univ_succ]
    simp only [Fin.insertNth_zero', Fin.cons_zero, Fin.cons_succ]
    push_cast
    have hiff : (m₀ : ℝ) * ∏ i, (m' i : ℝ) ≤ X ↔ (m₀ : ℝ) ≤ X / ∏ k, (m' k : ℝ) :=
      (le_div_iff₀ hprodpos).symm
    split_ifs with h1 h2 h2
    · ring
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · ring
  rw [sum_congr rfl hterm, ← mul_sum]
  calc (∏ k : Fin r, v k.succ (m' k)) *
        ∑ m₀ ∈ S, (if (m₀ : ℝ) ≤ X / ∏ k, (m' k : ℝ) then v 0 m₀ else 0)
      ≤ (∏ k : Fin r, v k.succ (m' k)) * (c * (X / ∏ k, (m' k : ℝ))) :=
        mul_le_mul_of_nonneg_left (hc _ (div_nonneg hX hprodpos.le)) hV
    _ = c * X * ∏ k, v k.succ (m' k) / m' k := by
        rw [prod_div_distrib]
        field_simp

/-- Regrouping a tuple sum by the product. -/
theorem sum_piFinset_eq_sum_fiber {M : Type*} [AddCommMonoid M] (S : Finset ℕ) {r : ℕ}
    (G : ℕ → (Fin r → ℕ) → M) {T : Finset ℕ}
    (hT : ∀ m ∈ Fintype.piFinset (fun _ : Fin r => S), ∏ k, m k ∈ T) :
    ∑ m ∈ Fintype.piFinset (fun _ : Fin r => S), G (∏ k, m k) m =
      ∑ n ∈ T, ∑ m ∈ Fintype.piFinset (fun _ : Fin r => S) with ∏ k, m k = n, G n m := by
  rw [← sum_fiberwise_of_maps_to hT]
  exact sum_congr rfl fun n _ => sum_congr rfl fun m hm => by rw [(mem_filter.1 hm).2]

/-- The ordered factorizations of `n` into `r` factors. -/
def factorizationTuples (r n : ℕ) : Finset (Fin r → ℕ) :=
  (Fintype.piFinset fun _ : Fin r => n.divisors).filter fun m => ∏ k, m k = n

/-- There are at most `r^{Ω(n)}` ordered factorizations of `n` into `r` factors. -/
theorem card_factorizationTuples_le (r : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ((factorizationTuples r n).card : ℝ) ≤ cmul (fun _ => (r : ℝ)) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases h1 : n = 1
  · subst h1
    rw [map_one]
    have : factorizationTuples r 1 ⊆ {fun _ => 1} := by
      intro m hm
      rw [mem_singleton]
      funext k
      have := Fintype.mem_piFinset.1 (mem_filter.1 hm).1 k
      simpa using this
    exact_mod_cast (card_le_card this).trans (card_singleton _).le
  have hc0 : 0 ≤ cmul (fun _ => (r : ℝ)) n := cmul_nonneg (fun _ _ => Nat.cast_nonneg r) n
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have : factorizationTuples 0 n = ∅ := by
      refine filter_eq_empty_iff.2 fun m _ hm => h1 ?_
      rw [← hm]
      simp
    rw [this, card_empty, Nat.cast_zero]
    exact cmul_nonneg (fun _ _ => le_rfl) n
  have hp := Nat.minFac_prime h1
  set p := n.minFac with hpdef
  have hpn : p ∣ n := Nat.minFac_dvd n
  set n' := n / p with hn'def
  have hnn' : n = p * n' := (Nat.mul_div_cancel' hpn).symm
  have hn'0 : n' ≠ 0 := by
    intro h; rw [h, mul_zero] at hnn'; exact hn hnn'
  have hn'lt : n' < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt
  classical
  -- the first factor divisible by `p`
  let idx : (Fin r → ℕ) → Fin r := fun m =>
    if h : (univ.filter fun k => p ∣ m k).Nonempty then
      (univ.filter fun k => p ∣ m k).min' h else ⟨0, hr⟩
  have hidx : ∀ m ∈ factorizationTuples r n, p ∣ m (idx m) := by
    intro m hm
    have hprod := (mem_filter.1 hm).2
    have : p ∣ ∏ k, m k := hprod ▸ hpn
    obtain ⟨k, -, hk⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 this
    have hne : (univ.filter fun k => p ∣ m k).Nonempty := ⟨k, mem_filter.2 ⟨mem_univ _, hk⟩⟩
    simp only [idx, hne, dite_true]
    exact (mem_filter.1 ((univ.filter fun k => p ∣ m k).min'_mem hne)).2
  let φ : (Fin r → ℕ) → Fin r × (Fin r → ℕ) := fun m =>
    (idx m, Function.update m (idx m) (m (idx m) / p))
  have hmaps : ∀ m ∈ factorizationTuples r n,
      φ m ∈ (univ : Finset (Fin r)) ×ˢ factorizationTuples r n' := by
    intro m hm
    have hprod := (mem_filter.1 hm).2
    have hk := hidx m hm
    refine mem_product.2 ⟨mem_univ _, ?_⟩
    have hprod' : ∏ k, Function.update m (idx m) (m (idx m) / p) k = n' := by
      rw [Finset.prod_update_of_mem (mem_univ _), sdiff_singleton_eq_erase]
      have h2 := Finset.mul_prod_erase univ m (mem_univ (idx m))
      rw [hprod] at h2
      obtain ⟨c, hc⟩ := hk
      rw [hc, Nat.mul_div_cancel_left _ hp.pos]
      rw [hc, mul_assoc] at h2
      rw [hn'def, ← h2, Nat.mul_div_cancel_left _ hp.pos]
    refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun k => ?_, hprod'⟩
    rw [Nat.mem_divisors]
    exact ⟨hprod' ▸ Finset.dvd_prod_of_mem _ (mem_univ k), hn'0⟩
  have hinj : Set.InjOn φ (factorizationTuples r n) := by
    intro m hm m' hm' h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨hidx', hupd⟩ := h
    have hk := hidx m hm
    have hk' := hidx m' hm'
    funext k
    by_cases hkk : k = idx m
    · subst hkk
      have := congrFun hupd (idx m)
      rw [Function.update_self, ← hidx', Function.update_self] at this
      have hk'' : p ∣ m' (idx m) := by rw [hidx']; exact hk'
      rw [← Nat.div_mul_cancel hk, ← Nat.div_mul_cancel hk'', this]
    · have := congrFun hupd k
      have hkk' : k ≠ idx m' := hidx' ▸ hkk
      rw [Function.update_of_ne hkk, Function.update_of_ne hkk'] at this
      exact this
  have hcard := card_le_card_of_injOn φ (fun m hm => hmaps m hm) hinj
  rw [card_product, card_univ, Fintype.card_fin] at hcard
  have hih := ih n' hn'lt hn'0
  calc ((factorizationTuples r n).card : ℝ) ≤ r * (factorizationTuples r n').card := by
        exact_mod_cast hcard
    _ ≤ r * cmul (fun _ => (r : ℝ)) n' := by gcongr
    _ = cmul (fun _ => (r : ℝ)) n := by
        rw [hnn', map_mul, cmul_prime _ hp]

end Erdos408.TypeII
