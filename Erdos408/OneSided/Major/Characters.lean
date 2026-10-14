import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Expansion into Dirichlet characters

On the arc `h/k + λ/Y` of the major term, the phase `e(h(bmn - b)/k)` depends only on the
units `b, m, n` modulo `k`. Expand it into products of three Dirichlet characters
(`blueprint/one_sided_type_ii.md` §6.3 step 1). Over the units, every function with
`|f| ≤ 1` is `∑ c(χ₁, χ₂, χ₃) χ₁ χ₂ χ₃` with `|c| ≤ 1`. Iterate the one-variable expansion
`g(y) = ∑_χ ĝ(χ) χ(y)`, where `ĝ(χ) = φ(k)⁻¹ ∑_{u unit} g(u) χ̄(u)`, which follows from
the orthogonality of characters. There are at most `k` characters modulo `k`.
-/

namespace Erdos408.OneSided

open Finset

/-- `ℂ` has the roots of unity needed for the orthogonality of characters modulo `k`. -/
private instance hasEnoughRootsOfUnity_units_exponent (k : ℕ) [NeZero k] :
    HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod k)ˣ) :=
  have : NeZero (Monoid.exponent (ZMod k)ˣ : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  inferInstance

/-- There are at most `k` Dirichlet characters modulo `k`. -/
theorem card_dirichletCharacter_le (k : ℕ) [NeZero k] :
    Fintype.card (DirichletCharacter ℂ k) ≤ k := by
  rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  exact Nat.totient_le k

/-- The one-variable expansion: `∑_χ ĝ(χ) χ(y) = φ(k) g(y)` at a unit `y`, where
`ĝ(χ) = ∑_{u unit} g(u) χ(u⁻¹)` is the unnormalized coefficient. -/
private theorem sum_dirichletCharacter_coeff_mul {k : ℕ} [NeZero k] (g : ZMod k → ℂ)
    {y : ZMod k} (hy : IsUnit y) :
    ∑ χ : DirichletCharacter ℂ k, (∑ u : (ZMod k)ˣ, g u * χ (↑u)⁻¹) * χ y =
      k.totient * g y := by
  obtain ⟨y, rfl⟩ := hy
  -- swap the sums and apply the column orthogonality at each unit `u`
  simp_rw [sum_mul]
  rw [sum_comm]
  simp_rw [mul_assoc, ← mul_sum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit _),
    Units.val_inj, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true, mul_comm]

/-- The unnormalized coefficient has modulus at most `φ(k)` times the bound on `g`. -/
private theorem norm_sum_mul_dirichletCharacter_le {k : ℕ} [NeZero k] (g : (ZMod k)ˣ → ℂ)
    (χ : DirichletCharacter ℂ k) {B : ℝ} (hg : ∀ u, ‖g u‖ ≤ B) :
    ‖∑ u : (ZMod k)ˣ, g u * χ (↑u)⁻¹‖ ≤ k.totient * B := by
  refine (norm_sum_le _ _).trans ?_
  -- each term is at most `B`, and there are `φ(k)` units
  calc ∑ u : (ZMod k)ˣ, ‖g u * χ (↑u)⁻¹‖ ≤ ∑ _u : (ZMod k)ˣ, B := by
        refine sum_le_sum fun u _ => ?_
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)).trans (hg u)
    _ = k.totient * B := by
        rw [sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]

/-- A function of three units modulo `k` with `|f| ≤ 1` is a combination of products of
three characters with coefficients of modulus at most one. -/
theorem exists_dirichletCharacter_expansion {k : ℕ} [NeZero k]
    (f : ZMod k → ZMod k → ZMod k → ℂ) (hf : ∀ a b c, ‖f a b c‖ ≤ 1) :
    ∃ coeff : DirichletCharacter ℂ k → DirichletCharacter ℂ k → DirichletCharacter ℂ k → ℂ,
      (∀ χ₁ χ₂ χ₃, ‖coeff χ₁ χ₂ χ₃‖ ≤ 1) ∧
      ∀ a b c : ZMod k, IsUnit a → IsUnit b → IsUnit c →
        f a b c = ∑ χ₁, ∑ χ₂, ∑ χ₃, coeff χ₁ χ₂ χ₃ * χ₁ a * χ₂ b * χ₃ c := by
  have hφ := (Nat.totient_pos.mpr (NeZero.pos k)).ne'
  -- expand in `a`, then in `b`, then in `c`
  refine ⟨fun χ₁ χ₂ χ₃ => (k.totient : ℂ)⁻¹ ^ 3 * ∑ w : (ZMod k)ˣ,
    (∑ v : (ZMod k)ˣ, (∑ u : (ZMod k)ˣ, f u v w * χ₁ (↑u)⁻¹) * χ₂ (↑v)⁻¹) * χ₃ (↑w)⁻¹,
    fun χ₁ χ₂ χ₃ => ?_, fun a b c ha hb hc => ?_⟩
  · -- each expansion multiplies the bound by `φ(k)`
    have h₁ := fun v w : (ZMod k)ˣ => norm_sum_mul_dirichletCharacter_le (fun u => f u v w) χ₁
      (fun u => hf u v w)
    have h₂ := fun w : (ZMod k)ˣ => norm_sum_mul_dirichletCharacter_le _ χ₂ (fun v => h₁ v w)
    have h₃ := norm_sum_mul_dirichletCharacter_le _ χ₃ h₂
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
    calc (k.totient : ℝ)⁻¹ ^ 3 * _ ≤ (k.totient : ℝ)⁻¹ ^ 3 *
          (k.totient * (k.totient * (k.totient * 1))) := by gcongr
      _ = 1 := by field_simp [hφ]
  · -- the expansion in `c` collapses the sum over `χ₃`
    have hc' := fun χ₁ χ₂ : DirichletCharacter ℂ k => sum_dirichletCharacter_coeff_mul
      (fun w => ∑ v : (ZMod k)ˣ, (∑ u : (ZMod k)ˣ, f u v w * χ₁ (↑u)⁻¹) * χ₂ (↑v)⁻¹) hc
    -- the expansion in `b` collapses the sum over `χ₂`
    have hb' := fun χ₁ : DirichletCharacter ℂ k => sum_dirichletCharacter_coeff_mul
      (fun v => ∑ u : (ZMod k)ˣ, f u v c * χ₁ (↑u)⁻¹) hb
    -- the expansion in `a` collapses the sum over `χ₁`
    have ha' := sum_dirichletCharacter_coeff_mul (fun u => f u b c) ha
    symm
    calc _ = ∑ χ₁ : DirichletCharacter ℂ k, ∑ χ₂ : DirichletCharacter ℂ k,
          ((k.totient : ℂ)⁻¹ ^ 3 * χ₁ a * χ₂ b) * ∑ χ₃ : DirichletCharacter ℂ k,
            (∑ w : (ZMod k)ˣ, (∑ v : (ZMod k)ˣ,
              (∑ u : (ZMod k)ˣ, f u v w * χ₁ (↑u)⁻¹) * χ₂ (↑v)⁻¹) * χ₃ (↑w)⁻¹) * χ₃ c := by
          refine sum_congr rfl fun χ₁ _ => sum_congr rfl fun χ₂ _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun χ₃ _ => by ring
      _ = ∑ χ₁ : DirichletCharacter ℂ k, ((k.totient : ℂ)⁻¹ ^ 3 * k.totient * χ₁ a) *
          ∑ χ₂ : DirichletCharacter ℂ k,
            (∑ v : (ZMod k)ˣ, (∑ u : (ZMod k)ˣ, f u v c * χ₁ (↑u)⁻¹) * χ₂ (↑v)⁻¹) * χ₂ b := by
          refine sum_congr rfl fun χ₁ _ => ?_
          simp_rw [hc']
          rw [mul_sum]
          exact sum_congr rfl fun χ₂ _ => by ring
      _ = (k.totient : ℂ)⁻¹ ^ 3 * k.totient * k.totient *
          ∑ χ₁ : DirichletCharacter ℂ k, (∑ u : (ZMod k)ˣ, f u b c * χ₁ (↑u)⁻¹) * χ₁ a := by
          simp_rw [hb']
          rw [mul_sum]
          exact sum_congr rfl fun χ₁ _ => by ring
      _ = f a b c := by
          rw [ha']
          field_simp [hφ]

end Erdos408.OneSided
