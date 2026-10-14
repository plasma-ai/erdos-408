module

public import Erdos408.OneSided.Analysis.Kloosterman
public import Erdos408.OneSided.RootResidue.Fourier

/-!
# Exponential sums over a twisted modular hyperbola

PD `det:CRT-Fourier`. For a unit `a` mod `n` and residues `t, c₀`, let
`G = {(x, y) mod n : x y = a, t x = t c₀}`. Detecting `t x = t c₀` by additive characters
gives

`n Ŝ_G(h, k) = ∑_j e(-j t c₀/n) K_n(h + j t, k a)`,

so the weak Kloosterman bound `det:weak-kloosterman` gives
`|Ŝ_G(h, k)| ≤ C n^{3/4 + 1/100} (k, n)` (`norm_pairSum_hyperbola_le`). In PD Lemma 3.3,
`n = u S₁` with `S₁ = (u, S)`, `t = u` and `a = u d₀ - 1`; the condition `t x = t c₀`
is `x ≡ c₀ (mod S₁)`.
-/

@[expose] public section

namespace Erdos408.OneSided.RootResidue

open Finset

variable {n : ℕ} [NeZero n]

variable (n) in
/-- The twisted hyperbola `{(x, y) mod n : x y = a, t x = t c₀}`. -/
noncomputable def hyperbola (a t c₀ : ZMod n) : Finset (ZMod n × ZMod n) :=
  {p | p.1 * p.2 = a ∧ t * p.1 = t * c₀}

/-- On the hyperbola `x` is a unit and `y = a x⁻¹`: `Ŝ_G(h, k)` is a sum over the units
`x` with `t x = t c₀`. -/
theorem pairSum_hyperbola_eq {a : ZMod n} (ha : IsUnit a) (t c₀ h k : ZMod n) :
    pairSum (hyperbola n a t c₀) h k = ∑ x : (ZMod n)ˣ,
      if t * (x : ZMod n) = t * c₀ then
        ZMod.stdAddChar (h * (x : ZMod n) + k * a * ((x⁻¹ : (ZMod n)ˣ) : ZMod n))
      else 0 := by
  rw [← sum_filter, pairSum]
  refine sum_nbij' (fun p => if hp : IsUnit p.1 then hp.unit else 1)
    (fun x => ((x : ZMod n), a * ((x⁻¹ : (ZMod n)ˣ) : ZMod n))) (fun p hp => ?_)
    (fun x hx => ?_) (fun p hp => ?_) (fun x _ => ?_) (fun p hp => ?_)
  · obtain ⟨h₁, h₂⟩ := (mem_filter.1 hp).2
    have hu : IsUnit p.1 := isUnit_of_mul_isUnit_left (h₁ ▸ ha)
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    simp only [hu, ↓reduceDIte, IsUnit.unit_spec]
    exact h₂
  · refine mem_filter.2 ⟨mem_univ _, ?_, (mem_filter.1 hx).2⟩
    rw [mul_left_comm, Units.mul_inv, mul_one]
  · obtain ⟨h₁, -⟩ := (mem_filter.1 hp).2
    have hu : IsUnit p.1 := isUnit_of_mul_isUnit_left (h₁ ▸ ha)
    simp only [hu, ↓reduceDIte, IsUnit.unit_spec]
    refine Prod.ext rfl ?_
    rw [← h₁, mul_comm p.1, mul_assoc, hu.mul_val_inv, mul_one]
  · simp
  · obtain ⟨h₁, -⟩ := (mem_filter.1 hp).2
    have hu : IsUnit p.1 := isUnit_of_mul_isUnit_left (h₁ ▸ ha)
    simp only [hu, ↓reduceDIte]
    congr 1
    rw [IsUnit.unit_spec, ← h₁, mul_comm p.1, mul_assoc, mul_assoc, hu.mul_val_inv,
      mul_one]

/-- `det:CRT-Fourier`: `n Ŝ_G(h, k) = ∑_j e(-j t c₀/n) K_n(h + j t, k a)`. -/
theorem natCast_mul_pairSum_hyperbola_eq {a : ZMod n} (ha : IsUnit a) (t c₀ h k : ZMod n) :
    (n : ℂ) * pairSum (hyperbola n a t c₀) h k = ∑ j : ZMod n,
      ZMod.stdAddChar (-(j * t * c₀)) * kloostermanZMod n (h + j * t) (k * a) := by
  rw [pairSum_hyperbola_eq ha, mul_sum]
  -- detect `t x = t c₀` by orthogonality
  have hdet : ∀ x : (ZMod n)ˣ, (n : ℂ) * (if t * (x : ZMod n) = t * c₀ then
      ZMod.stdAddChar (h * (x : ZMod n) + k * a * ((x⁻¹ : (ZMod n)ˣ) : ZMod n)) else 0) =
      ∑ j : ZMod n, ZMod.stdAddChar (j * (t * (x : ZMod n) - t * c₀)) *
        ZMod.stdAddChar (h * (x : ZMod n) + k * a * ((x⁻¹ : (ZMod n)ˣ) : ZMod n)) := by
    intro x
    rw [← sum_mul, sum_stdAddChar_mul]
    by_cases hx : t * (x : ZMod n) = t * c₀
    · simp only [hx, sub_self, ite_true]
    · simp only [hx, sub_eq_zero, ite_false, mul_zero, zero_mul]
  simp only [hdet, kloostermanZMod, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun x _ => ?_
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The weak Kloosterman bound over `ZMod n`, in the crude form
`|K_n(x, y)| ≤ C n^{3/4 + 1/100} (y, n)`. -/
theorem norm_kloostermanZMod_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n] (x y : ZMod n),
      ‖kloostermanZMod n x y‖ ≤ C * (n : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * Nat.gcd y.val n := by
  obtain ⟨C, hC⟩ := norm_kloosterman_le (ε := 1 / 100) (by norm_num)
  have hC0 : 0 ≤ C := by
    have h := hC 1 0 0 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one, Nat.gcd_zero_left] at h
    exact (norm_nonneg _).trans h
  refine ⟨C, hC0, fun n _ x y => ?_⟩
  have hn : 1 ≤ n := NeZero.one_le
  have h := hC n x.val y.val hn
  rw [kloosterman_eq_kloostermanZMod, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h
  refine h.trans ?_
  -- `(x, y, n)^{1/4} ≤ (x, y, n) ≤ (y, n)`
  have hg : 1 ≤ Nat.gcd (Nat.gcd x.val y.val) n := Nat.gcd_pos_of_pos_right _ hn
  have hgy : Nat.gcd (Nat.gcd x.val y.val) n ≤ Nat.gcd y.val n :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ hn)
      (Nat.gcd_dvd_gcd_of_dvd_left _ (Nat.gcd_dvd_right _ _))
  have hg' : (1 : ℝ) ≤ (Nat.gcd (Nat.gcd x.val y.val) n : ℕ) := by exact_mod_cast hg
  gcongr
  calc ((Nat.gcd (Nat.gcd x.val y.val) n : ℕ) : ℝ) ^ (1 / 4 : ℝ)
      ≤ ((Nat.gcd (Nat.gcd x.val y.val) n : ℕ) : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hg' (by norm_num)
    _ ≤ Nat.gcd y.val n := by rw [Real.rpow_one]; exact_mod_cast hgy

/-- **The hyperbola bound.** `|Ŝ_G(h, k)| ≤ C n^{3/4 + 1/100} (k, n)` on the twisted
hyperbola `G = {x y = a, t x = t c₀}`, `a` a unit. -/
theorem norm_pairSum_hyperbola_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n] (a t c₀ : ZMod n), IsUnit a → ∀ h k : ZMod n,
      ‖pairSum (hyperbola n a t c₀) h k‖ ≤
        C * (n : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * Nat.gcd k.val n := by
  obtain ⟨C, hC0, hC⟩ := norm_kloostermanZMod_le
  refine ⟨C, hC0, fun n _ a t c₀ ha h k => ?_⟩
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (NeZero.pos n)
  set B := C * (n : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * Nat.gcd k.val n
  refine le_of_mul_le_mul_left ?_ hn
  calc (n : ℝ) * ‖pairSum (hyperbola n a t c₀) h k‖
      = ‖(n : ℂ) * pairSum (hyperbola n a t c₀) h k‖ := by
        rw [norm_mul, Complex.norm_natCast]
    _ ≤ ∑ j : ZMod n, ‖kloostermanZMod n (h + j * t) (k * a)‖ := by
        rw [natCast_mul_pairSum_hyperbola_eq ha]
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        rw [norm_mul, norm_stdAddChar, one_mul]
    _ ≤ ∑ _j : ZMod n, B := by
        refine sum_le_sum fun j _ => (hC n _ _).trans ?_
        rw [gcd_val_mul_of_isUnit k ha]
    _ = n * B := by rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]

end Erdos408.OneSided.RootResidue
