import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

/-!
# The lifespan values of one prime

The per-prime bookkeeping behind S3 (`blueprint/one_sided_type_ii.md` §12, PD §4
`mem:orphan-identity`–`mem:rho-cancellation`). Fix a prime `p`, visits `j = 0, …, N` with
lines `L_j`, defects `η'_j`, the set `A ⊆ {0, …, N}` of active visits, and the birth
constant `c = ((p + 1) b'_p)⁻¹`. The factor of `p` at the line `ℓ` and the visit `j` is
`λ_j(ℓ) = [ℓ = L_j]` if `j ∈ A` and `1 - η'_j [ℓ = L_j]` otherwise, and
`Λ_t(ℓ) = ∏_{t ≤ j ≤ N} λ_j(ℓ)` is its tail from `t`. Let `a_t = [A ∩ [t, N] = ∅]`.

Before the ghost at visit `t`, the prime is in one of four states (`Status`). The total
weight of its future in the memory chain is its *lifespan value* (`lifeValue`):

* active: `Λ_t(L_t)`;
* pending with anchor `ℓ`: `Λ_t(ℓ) - a_t`. It must eventually be promoted (the term `Λ_t`)
  or deleted (the suffix expansion of `Λ_t`, without its leading `1`);
* dead: `a_t`, since a dead prime cannot become active again;
* unborn: `c (∑_ℓ Λ_t(ℓ) - a_t ∑_{j < t} η'_j)`.

`postValue` is the same after the ghost at `t`. The one-step identities say that these
values are reproduced by the ghost and edge transitions of the chain:

* the ghost (`lifeValue_active`, `lifeValue_dead`, `lifeValue_pending_*`, `lifeValue_unborn`):
  a pending hit survives with `q_t = 1 - η'_t` or is deleted with `-η'_t`; an unborn prime
  may be created with `-η'_t c`;
* the edge (`postValue_*`): a leaving prime is stored or dropped; a staying prime keeps
  its line; an entering prime is promoted from its anchor (weight `1`) or is fresh (weight
  `c`); every other prime is unchanged.

At `t = 0` the unborn and active values are `c ∑_ℓ Λ_0(ℓ)` and `∑_ℓ Λ_0(ℓ)`, the line
averages of PD `mem:prime-factor`; after the last ghost, a pending prime has value `0` and
every other prime value `1`.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset

/-- The state of one prime before a ghost: active, pending with an anchor, dead, or
unborn. -/
inductive Status
  | active
  | pending (ℓ : ℕ)
  | dead
  | unborn
  deriving DecidableEq

section Lifespan

variable (p N : ℕ) (L : ℕ → ℕ) (η' : ℕ → ℝ) (A : Finset ℕ) (c : ℝ)

/-- The factor `λ_j(ℓ)`: `[ℓ = L_j]` at an active visit and `1 - η'_j [ℓ = L_j]` otherwise. -/
def lifeStep (j ℓ : ℕ) : ℝ :=
  if j ∈ A then (if ℓ = L j then 1 else 0) else 1 - η' j * if ℓ = L j then 1 else 0

/-- The tail `Λ_t(ℓ) = ∏_{t ≤ j ≤ N} λ_j(ℓ)`. -/
def lifeTail (t ℓ : ℕ) : ℝ := ∏ j ∈ Ico t (N + 1), lifeStep L η' A j ℓ

/-- `a_t = [A ∩ [t, N] = ∅]`: the prime is never active from the visit `t` on. -/
def lifeQuiet (t : ℕ) : ℝ := if ∀ j ∈ A, j < t then 1 else 0

/-- The lifespan value of the prime at the visit `t`, before the ghost. -/
def lifeValue (t : ℕ) : Status → ℝ
  | .active => lifeTail N L η' A t (L t)
  | .pending ℓ => lifeTail N L η' A t ℓ - lifeQuiet A t
  | .dead => lifeQuiet A t
  | .unborn => c * (∑ ℓ ∈ range (p + 1), lifeTail N L η' A t ℓ -
      lifeQuiet A t * ∑ j ∈ range t, η' j)

/-- The lifespan value of the prime at the visit `t`, after the ghost. -/
def postValue (t : ℕ) : Status → ℝ
  | .active => lifeTail N L η' A (t + 1) (L t)
  | .pending ℓ => lifeTail N L η' A (t + 1) ℓ - lifeQuiet A (t + 1)
  | .dead => lifeQuiet A (t + 1)
  | .unborn => if t + 1 ∈ A then c * lifeTail N L η' A (t + 1) (L (t + 1))
      else lifeValue p N L η' A c (t + 1) .unborn

variable {p N L η' A c} {t : ℕ}

/-- The tail from a visit `t ≤ N` is its first factor times the tail from `t + 1`. -/
theorem lifeTail_eq_mul (ht : t ≤ N) (ℓ : ℕ) :
    lifeTail N L η' A t ℓ = lifeStep L η' A t ℓ * lifeTail N L η' A (t + 1) ℓ := by
  rw [lifeTail, lifeTail, prod_eq_prod_Ico_succ_bot (by omega)]

/-- The tail past the last visit is `1`. -/
theorem lifeTail_of_lt (ht : N < t) (ℓ : ℕ) : lifeTail N L η' A t ℓ = 1 := by
  rw [lifeTail, Ico_eq_empty (by omega), prod_empty]

/-- At an inactive visit, `a_t = a_{t+1}`. -/
theorem lifeQuiet_succ (ht : t ∉ A) : lifeQuiet A t = lifeQuiet A (t + 1) := by
  unfold lifeQuiet
  refine if_congr ⟨fun h j hj => (h j hj).trans (Nat.lt_succ_self t), fun h j hj => ?_⟩ rfl rfl
  have := h j hj
  have hne : j ≠ t := fun hjt => ht (hjt ▸ hj)
  omega

/-- At an active visit, `a_t = 0`. -/
theorem lifeQuiet_of_mem (ht : t ∈ A) : lifeQuiet A t = 0 :=
  ite_eq_right fun h => absurd (h t ht) (lt_irrefl t)

/-- Past the last visit, `a_t = 1`. -/
theorem lifeQuiet_of_lt (hA : A ⊆ range (N + 1)) (ht : N < t) : lifeQuiet A t = 1 :=
  ite_eq_left fun _ hj => (mem_range.1 (hA hj)).trans_le ht

/-- At an active visit, the line sum of the tail is the tail at the active line. -/
theorem sum_lifeTail_of_mem (hL : ∀ j ≤ N, L j ≤ p) (ht : t ∈ A) (htN : t ≤ N) :
    ∑ ℓ ∈ range (p + 1), lifeTail N L η' A t ℓ = lifeTail N L η' A t (L t) := by
  simp only [lifeTail_eq_mul htN, lifeStep, ht, ite_true, ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq', ite_eq_left (mem_range.2 (Nat.lt_succ_of_le (hL t htN)))]

/-! ### The ghost -/

/-- The ghost keeps an active prime. -/
theorem lifeValue_active (ht : t ∈ A) (htN : t ≤ N) :
    lifeValue p N L η' A c t .active = postValue p N L η' A c t .active := by
  simp only [lifeValue, postValue, lifeTail_eq_mul htN, lifeStep, ht, ite_true, one_mul]

/-- The ghost keeps a dead prime. -/
theorem lifeValue_dead (ht : t ∉ A) :
    lifeValue p N L η' A c t .dead = postValue p N L η' A c t .dead :=
  lifeQuiet_succ ht

/-- A pending prime hitting its line survives with `q_t = 1 - η'_t` or is deleted with
`-η'_t` (PD `mem:rho-cancellation`). -/
theorem lifeValue_pending_hit (ht : t ∉ A) (htN : t ≤ N) :
    lifeValue p N L η' A c t (.pending (L t)) =
      (1 - η' t) * postValue p N L η' A c t (.pending (L t)) +
        -η' t * postValue p N L η' A c t .dead := by
  simp only [lifeValue, postValue, lifeTail_eq_mul htN, lifeStep, ht, ite_false, ite_true,
    mul_one, lifeQuiet_succ ht]
  ring

/-- A pending prime missing its line is unchanged by the ghost. -/
theorem lifeValue_pending_miss {ℓ : ℕ} (ht : t ∉ A) (htN : t ≤ N) (hℓ : ℓ ≠ L t) :
    lifeValue p N L η' A c t (.pending ℓ) = postValue p N L η' A c t (.pending ℓ) := by
  simp only [lifeValue, postValue, lifeTail_eq_mul htN, lifeStep, ht, hℓ, ite_false, mul_zero,
    sub_zero, one_mul, lifeQuiet_succ ht]

/-- An unborn prime stays unborn or is created at its current line with `-η'_t c`
(PD `mem:orphan-identity` and `mem:prefix`, one visit at a time). -/
theorem lifeValue_unborn (hL : ∀ j ≤ N, L j ≤ p) (hA : A ⊆ range (N + 1)) (ht : t ∉ A)
    (htN : t ≤ N) :
    lifeValue p N L η' A c t .unborn =
      postValue p N L η' A c t .unborn +
        -η' t * c * postValue p N L η' A c t (.pending (L t)) := by
  -- the line sum loses `η'_t Λ_{t+1}(L_t)` at the visit `t`
  have hsum : ∑ ℓ ∈ range (p + 1), lifeTail N L η' A t ℓ =
      ∑ ℓ ∈ range (p + 1), lifeTail N L η' A (t + 1) ℓ -
        η' t * lifeTail N L η' A (t + 1) (L t) := by
    simp only [lifeTail_eq_mul htN, lifeStep, ht, ite_false, sub_mul, one_mul, sum_sub_distrib]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    rw [sum_ite_eq', ite_eq_left (mem_range.2 (Nat.lt_succ_of_le (hL t htN)))]
  simp only [lifeValue, postValue, hsum, lifeQuiet_succ ht]
  by_cases h₁ : t + 1 ∈ A
  · -- the prime enters at `t + 1`: the lifeQuiet value vanishes
    have hN : t + 1 ≤ N := Nat.lt_succ_iff.1 (mem_range.1 (hA h₁))
    rw [ite_eq_left h₁, lifeQuiet_of_mem h₁, sum_lifeTail_of_mem hL h₁ hN]
    ring
  · rw [ite_eq_right h₁]
    simp only [sum_range_succ]
    ring

/-! ### The edge -/

/-- A prime leaving activity is stored at its line or dropped. -/
theorem postValue_leave :
    postValue p N L η' A c t .active =
      lifeValue p N L η' A c (t + 1) (.pending (L t)) + lifeValue p N L η' A c (t + 1) .dead := by
  simp only [postValue, lifeValue]
  ring

/-- A prime staying active keeps its line. -/
theorem postValue_stay (hline : L (t + 1) = L t) :
    postValue p N L η' A c t .active = lifeValue p N L η' A c (t + 1) .active := by
  simp only [postValue, lifeValue, hline]

/-- An unborn prime entering activity is fresh, with weight `c`. -/
theorem postValue_enter_unborn (h₁ : t + 1 ∈ A) :
    postValue p N L η' A c t .unborn = c * lifeValue p N L η' A c (t + 1) .active := by
  simp only [postValue, lifeValue, h₁, ite_true]

/-- A pending prime entering activity is promoted, if its anchor is the new line. -/
theorem postValue_enter_pending (h₁ : t + 1 ∈ A) (hN : t + 1 ≤ N) (ℓ : ℕ) :
    postValue p N L η' A c t (.pending ℓ) =
      (if ℓ = L (t + 1) then 1 else 0) * lifeValue p N L η' A c (t + 1) .active := by
  simp only [postValue, lifeValue, lifeQuiet_of_mem h₁, sub_zero]
  rw [lifeTail_eq_mul hN, lifeTail_eq_mul hN]
  simp only [lifeStep, h₁, ite_true]
  split_ifs with h <;> simp [h]

/-- A dead prime cannot enter activity. -/
theorem postValue_enter_dead (h₁ : t + 1 ∈ A) : postValue p N L η' A c t .dead = 0 :=
  lifeQuiet_of_mem h₁

/-- An inactive prime that does not enter is unchanged by the edge. -/
theorem postValue_idle (h₁ : t + 1 ∉ A) (st : Status) (hst : st ≠ .active) :
    postValue p N L η' A c t st = lifeValue p N L η' A c (t + 1) st := by
  cases st with
  | active => exact absurd rfl hst
  | pending ℓ => rfl
  | dead => rfl
  | unborn => simp only [postValue, h₁, ite_false]

/-! ### The ends -/

/-- After the last ghost, a pending prime has value `0` and any other prime value `1`, when
`c ((p + 1) - ∑_{j ≤ N} η'_j) = 1`. -/
theorem postValue_last (hA : A ⊆ range (N + 1))
    (hc : c * ((p : ℝ) + 1 - ∑ j ∈ range (N + 1), η' j) = 1) (st : Status) :
    postValue p N L η' A c N st = match st with
      | .pending _ => 0
      | _ => 1 := by
  have hN : N + 1 ∉ A := fun h => by simpa using hA h
  have hq : lifeQuiet A (N + 1) = 1 := lifeQuiet_of_lt hA (Nat.lt_succ_self N)
  cases st with
  | active => exact lifeTail_of_lt (Nat.lt_succ_self N) _
  | pending ℓ => simp only [postValue, lifeTail_of_lt (Nat.lt_succ_self N), hq, sub_self]
  | dead => exact hq
  | unborn =>
    simp only [postValue, hN, ite_false, lifeValue, lifeTail_of_lt (Nat.lt_succ_self N), hq,
      sum_const, card_range, nsmul_eq_mul, mul_one, one_mul]
    rw [← hc]
    push_cast
    ring

/-- At the first visit, the unborn value is `c ∑_ℓ Λ_0(ℓ)`. -/
theorem lifeValue_zero_unborn :
    lifeValue p N L η' A c 0 .unborn = c * ∑ ℓ ∈ range (p + 1), lifeTail N L η' A 0 ℓ := by
  simp only [lifeValue, range_zero, sum_empty, mul_zero, sub_zero]

/-- At the first visit, the active value is `∑_ℓ Λ_0(ℓ)`. -/
theorem lifeValue_zero_active (hL : ∀ j ≤ N, L j ≤ p) (h₀ : 0 ∈ A) :
    lifeValue p N L η' A c 0 .active = ∑ ℓ ∈ range (p + 1), lifeTail N L η' A 0 ℓ :=
  (sum_lifeTail_of_mem hL h₀ (Nat.zero_le N)).symm

end Lifespan

end Erdos408.OneSided
