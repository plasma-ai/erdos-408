import Erdos408.Extraction.Sieve.Basic
import Mathlib.Data.Int.CardIntervalMod

/-!
# Smooth sums in progressions

The input to the progression lemma (PD (7.9)): a sum of `f` over a residue
class modulo `q` in `[1, N]` is `1/q` of the full sum, up to the total
variation `∑ |f(m) - f(m-1)|`, uniformly in `q`. By the Chinese remainder
theorem this applies to the conditions `r ∣ u + 1`, `d ∣ u` with `(r, d) = 1`.
For a cutoff, `f(u) = Φ(u/x)` has total variation `≤ κ M₁ T^{C_Φ}`.
-/

namespace Erdos408

open Filter Real Finset

namespace Sieve

noncomputable section

/-- The number of `x ∈ [m, N]` with `x ≡ v (mod q)` is `(N + 1 - m) / q + O(1)`. -/
lemma abs_card_modEq_sub_le {q : ℕ} (hq : 0 < q) (v : ℕ) {m N : ℕ} (hm : 1 ≤ m)
    (hmN : m ≤ N + 1) :
    |(#((Icc m N).filter (· ≡ v [MOD q])) : ℝ) - ((N + 1 - m : ℕ) : ℝ) / q| ≤ 1 := by
  have hIcc : Icc m N = Ioc (m - 1) N := by
    ext x
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [hIcc]
  have h := Nat.Ioc_filter_modEq_card (m - 1) N hq v
  set A : ℚ := ((N : ℚ) - v) / q
  set B : ℚ := (((m - 1 : ℕ) : ℚ) - v) / q
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hAB : A - B = ((N + 1 - m : ℕ) : ℚ) / q := by
    simp only [A, B]
    rw [Nat.cast_sub hm, Nat.cast_sub hmN]
    field_simp
    push_cast
    ring
  have hAB0 : 0 ≤ A - B := by rw [hAB]; positivity
  have h1 := Int.floor_le A
  have h2 := Int.lt_floor_add_one A
  have h3 := Int.floor_le B
  have h4 := Int.lt_floor_add_one B
  have hk : (0 : ℤ) ≤ ⌊A⌋ - ⌊B⌋ := by
    have : (-1 : ℚ) < ((⌊A⌋ - ⌊B⌋ : ℤ) : ℚ) := by push_cast; linarith
    have : (-1 : ℤ) < ⌊A⌋ - ⌊B⌋ := by exact_mod_cast this
    omega
  rw [max_eq_left hk] at h
  have hQ : |(#((Ioc (m - 1) N).filter (· ≡ v [MOD q])) : ℚ) - ((N + 1 - m : ℕ) : ℚ) / q| ≤ 1 := by
    have hc : (#((Ioc (m - 1) N).filter (· ≡ v [MOD q])) : ℚ) = ((⌊A⌋ - ⌊B⌋ : ℤ) : ℚ) := by
      exact_mod_cast h
    rw [hc, ← hAB, abs_le]
    push_cast
    constructor <;> linarith
  have hR := (Rat.cast_le (K := ℝ)).2 hQ
  push_cast at hR
  exact hR

/-- `f(u) = ∑_{1 ≤ m ≤ u} (f(m) - f(m-1))` when `f(0) = 0`. -/
lemma eq_sum_Icc_sub {f : ℕ → ℝ} (hf0 : f 0 = 0) (u : ℕ) :
    f u = ∑ m ∈ Icc 1 u, (f m - f (m - 1)) := by
  induction u with
  | zero => simp [hf0]
  | succ u ih => rw [sum_Icc_succ_top (by omega), ← ih, Nat.add_sub_cancel]; ring

/-- A sum over `[1, N]` restricted by a condition, through the increments of `f`. -/
lemma sum_filter_eq_sum_sub {f : ℕ → ℝ} (hf0 : f 0 = 0) (N : ℕ) (p : ℕ → Prop)
    [DecidablePred p] :
    ∑ u ∈ (Icc 1 N).filter p, f u =
      ∑ m ∈ Icc 1 N, (f m - f (m - 1)) * #((Icc m N).filter p) := by
  rw [sum_congr rfl fun u _ => eq_sum_Icc_sub hf0 u]
  rw [sum_comm' (t' := Icc 1 N) (s' := fun m => (Icc m N).filter p)]
  · refine sum_congr rfl fun m _ => ?_
    rw [sum_const, nsmul_eq_mul, mul_comm]
  · intro u m
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩
      exact ⟨⟨⟨h5, h2⟩, h3⟩, h4, h5.trans h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩
      exact ⟨⟨⟨h4.trans h1, h2⟩, h3⟩, h4, h1⟩

/-- A sum over a residue class modulo `q` in `[1, N]` is `1/q` of the full sum, up to the
total variation. -/
lemma abs_sum_modEq_sub_le {q : ℕ} (hq : 0 < q) (v N : ℕ) {f : ℕ → ℝ} (hf0 : f 0 = 0) :
    |∑ u ∈ (Icc 1 N).filter (· ≡ v [MOD q]), f u - (1 / q) * ∑ u ∈ Icc 1 N, f u| ≤
      ∑ m ∈ Icc 1 N, |f m - f (m - 1)| := by
  have hfull : ∑ u ∈ Icc 1 N, f u = ∑ m ∈ Icc 1 N, (f m - f (m - 1)) * ((N + 1 - m : ℕ) : ℝ) := by
    have := sum_filter_eq_sum_sub hf0 N (fun _ => True)
    rw [filter_true_of_mem fun _ _ => trivial] at this
    rw [this]
    refine sum_congr rfl fun m _ => ?_
    rw [filter_true_of_mem fun _ _ => trivial, Nat.card_Icc]
  rw [sum_filter_eq_sum_sub hf0, hfull, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
  obtain ⟨hm1, hmN⟩ := mem_Icc.1 hm
  have h := abs_card_modEq_sub_le hq v hm1 (by omega : m ≤ N + 1)
  rw [show (f m - f (m - 1)) * (#((Icc m N).filter (· ≡ v [MOD q])) : ℝ) -
      1 / q * ((f m - f (m - 1)) * ((N + 1 - m : ℕ) : ℝ)) =
      (f m - f (m - 1)) * ((#((Icc m N).filter (· ≡ v [MOD q])) : ℝ) -
        ((N + 1 - m : ℕ) : ℝ) / q) by ring, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) h

/-- By the Chinese remainder theorem, `r ∣ u + 1 ∧ d ∣ u` is a residue class modulo `r d`. -/
lemma exists_modEq_iff {r d : ℕ} (hr : 0 < r) (hrd : Nat.Coprime r d) :
    ∃ v, ∀ u, (r ∣ u + 1 ∧ d ∣ u) ↔ u ≡ v [MOD r * d] := by
  obtain ⟨k, hk₁, hk₂⟩ := Nat.chineseRemainder hrd (r - 1) 0
  refine ⟨k, fun u => ?_⟩
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hrd]
  have h1 : r ∣ u + 1 ↔ u ≡ k [MOD r] := by
    rw [← Nat.modEq_zero_iff_dvd]
    constructor
    · intro h
      refine (Nat.ModEq.add_right_cancel' 1 ?_).trans hk₁.symm
      rw [Nat.sub_add_cancel hr]
      exact h.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl).symm
    · intro h
      have := (h.trans hk₁).add_right 1
      rw [Nat.sub_add_cancel hr] at this
      exact this.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)
  have h2 : d ∣ u ↔ u ≡ k [MOD d] := by
    rw [← Nat.modEq_zero_iff_dvd]
    exact ⟨fun h => h.trans hk₂.symm, fun h => h.trans hk₂⟩
  rw [h1, h2]

/-- The progression sum `∑_{u ≤ N, r ∣ u+1, d ∣ u} f(u)` is `1/(r d)` of the full sum up to
the total variation, for coprime `r, d`. -/
lemma abs_sum_dvd_sub_le {r d : ℕ} (hr : 0 < r) (hd : 0 < d) (hrd : Nat.Coprime r d) (N : ℕ)
    {f : ℕ → ℝ} (hf0 : f 0 = 0) :
    |∑ u ∈ (Icc 1 N).filter (fun u => r ∣ u + 1 ∧ d ∣ u), f u -
        (1 / ((r * d : ℕ) : ℝ)) * ∑ u ∈ Icc 1 N, f u| ≤
      ∑ m ∈ Icc 1 N, |f m - f (m - 1)| := by
  obtain ⟨v, hv⟩ := exists_modEq_iff hr hrd
  rw [filter_congr fun u _ => hv u]
  exact abs_sum_modEq_sub_le (Nat.mul_pos hr hd) v N hf0

/-- The total variation of `u ↦ Φ(u/x)` on `[1, N]` is at most `N M₁ T^{C_Φ} / x`. -/
lemma sum_abs_sub_cutoff_le {κ CΦ : ℝ} {M : ℕ → ℝ} {x : ℝ} (hx : 0 < x) {Φ : ℝ → ℝ}
    (hΦ : IsCutoff κ CΦ M x Φ) (N : ℕ) :
    ∑ m ∈ Icc 1 N, |Φ ((m : ℝ) / x) - Φ (((m - 1 : ℕ) : ℝ) / x)| ≤
      N * (M 1 * logLog x ^ CΦ / x) := by
  have hd : Differentiable ℝ Φ := hΦ.1.differentiable (by simp)
  have hbd : ∀ y, ‖deriv Φ y‖ ≤ M 1 * logLog x ^ CΦ := fun y => by
    have := hΦ.2.2.2 1 y
    rwa [iteratedDeriv_one, Nat.cast_one, mul_one] at this
  have hterm : ∀ m ∈ Icc 1 N, |Φ ((m : ℝ) / x) - Φ (((m - 1 : ℕ) : ℝ) / x)| ≤
      M 1 * logLog x ^ CΦ / x := by
    intro m hm
    have hm1 := (mem_Icc.1 hm).1
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (fun y _ => hd y)
      (fun y _ => hbd y) convex_univ (Set.mem_univ (((m - 1 : ℕ) : ℝ) / x))
      (Set.mem_univ ((m : ℝ) / x))
    have he : ‖(m : ℝ) / x - ((m - 1 : ℕ) : ℝ) / x‖ = 1 / x := by
      rw [Nat.cast_sub hm1, Nat.cast_one, show (m : ℝ) / x - ((m : ℝ) - 1) / x = 1 / x by ring,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [he, Real.norm_eq_abs] at h
    calc _ ≤ M 1 * logLog x ^ CΦ * (1 / x) := h
      _ = _ := by ring
  calc _ ≤ ∑ _m ∈ Icc 1 N, M 1 * logLog x ^ CΦ / x := sum_le_sum hterm
    _ = _ := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

end

end Sieve

end Erdos408
