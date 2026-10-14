module

public import Erdos408.OneSided.Goodness
public import Erdos408.OneSided.Goodness.BadMass
public import Erdos408.OneSided.Goodness.Symmetry

/-!
# Removing the good-state projections

Leaf B of interface 2 (`blueprint/one_sided_type_ii.md` §5.6 and §14, PD §4.9). The pairing
`⟨f, 𝒜 f⟩` with `𝒜 = 𝒢 𝒮 𝒯 𝒮 𝒢` differs from the raw pairing `⟨f, 𝒯 f⟩` only through the
bad states.

* `norm_rowPairing_sub_pairing_le`: since `f` and goodness are invariant under list
  permutations (`Symmetry.lean`), `𝒮 𝒢 f = 𝒢 f`, and `𝒮` is real and symmetric, so
  `⟨f, 𝒜 f⟩ = ⟨𝒢 f, 𝒯 𝒢 f⟩`. The difference is `∑ f̄(s) 𝒯(s, s') f(s') (1 - g(s) g(s'))`, so
  it is at most `L^{4C}` times the absolute row mass of `𝒯` on pairs with a bad source or a
  bad target.
* `eventually_badMass_le`: that mass is at most `C₀ UV L^{3A₀} exp(-L^{α₋}/8)`. For fixed
  lists, the targets of a source number `O(1)` in the raw part and `O(L^{3A₀})` after
  weighting in the comparison part (PD `mem:neighbor`, `mem:major-absolute`). The bad
  sources are counted by the root residues (`RootResidue.lean`) on the intervals where
  test (i) fails, and by Markov's inequality on those where test (ii) fails, as in
  Lemma 3.2. The lists then carry total mass at most one (PD `mem:one-edge-label-mass`).
-/

@[expose] public section

namespace Erdos408.OneSided

open Filter Finset Real
open scoped Matrix

variable {K : ℕ}

open scoped Classical in
/-- The absolute row mass of `𝒯` on the pairs whose source or target is bad. -/
noncomputable def badMass (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) : ℝ :=
  ∑ s : State x d Y d₀, ∑ s' : State x d Y d₀,
    ((if IsGood x d Y d₀ s.1.1 s.1.2 then 0 else 1) +
        (if IsGood x d Y d₀ s'.1.1 s'.1.2 then 0 else 1)) * ‖rowOp q A₀ x d Y d₀ s s'‖

open scoped Classical in
/-- The good indicator, the diagonal of `𝒢`. -/
private noncomputable def goodVec (x : ℝ) (d : Data K) (Y d₀ : ℝ) (s : State x d Y d₀) : ℂ :=
  if IsGood x d Y d₀ s.1.1 s.1.2 then 1 else 0

/-- The good indicator is real. -/
private theorem star_goodVec {x : ℝ} {d : Data K} {Y d₀ : ℝ} (s : State x d Y d₀) :
    star (goodVec x d Y d₀ s) = goodVec x d Y d₀ s := by
  unfold goodVec
  split_ifs <;> simp

open scoped Classical in
/-- The good indicator is slot invariant, because goodness is. -/
private theorem slotInvariant_goodVec {x : ℝ} {d : Data K} {Y d₀ : ℝ} :
    SlotInvariant (goodVec x d Y d₀) := by
  intro s s' σ h₁ hσ
  have hp : s'.1.2 = permuteLists s.1.2 σ := funext hσ
  have hgood : IsGood x d Y d₀ s'.1.1 s'.1.2 ↔ IsGood x d Y d₀ s.1.1 s.1.2 := by
    rw [hp, ← h₁, isGood_permuteLists_iff]
  exact if_congr hgood rfl rfl

open scoped Classical in
/-- `1 - g g'` is at most the number of bad states among the two. -/
private theorem norm_one_sub_goodVec_le {x : ℝ} {d : Data K} {Y d₀ : ℝ}
    (s s' : State x d Y d₀) :
    ‖1 - goodVec x d Y d₀ s * goodVec x d Y d₀ s'‖ ≤
      (if IsGood x d Y d₀ s.1.1 s.1.2 then 0 else 1) +
        (if IsGood x d Y d₀ s'.1.1 s'.1.2 then 0 else 1) := by
  unfold goodVec
  split_ifs <;> norm_num

/-- `|f| ≤ L^{2C}`, from the bounds on `α` and `β`. -/
private theorem norm_endVec_le {C CX alo ahi g x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d) (hL : 0 ≤ Real.log x) {Y d₀ : ℝ}
    (s : State x d Y d₀) : ‖endVec x d Y d₀ s‖ ≤ (Real.log x ^ C) ^ 2 := by
  have hB : 0 ≤ Real.log x ^ C := Real.rpow_nonneg hL C
  have hα : ‖d.α (s.1.1.1 / listProd s.1.2)‖ ≤ Real.log x ^ C := by
    by_cases h : d.α (s.1.1.1 / listProd s.1.2) = 0
    · rw [h, norm_zero]
      exact hB
    · exact (hd.α_supp _ h).2.2.2
  have hβ : ‖d.β s.1.1.2‖ ≤ Real.log x ^ C := by
    by_cases h : d.β s.1.1.2 = 0
    · rw [h, norm_zero]
      exact hB
    · exact (hd.β_supp _ h).2.2.2
  rw [endVec, norm_mul, norm_star, sq]
  exact mul_le_mul hα hβ (norm_nonneg _) hB

/-- `⟨f, 𝒯 f⟩` as a double sum. -/
private theorem rowPairing_eq_sum (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) :
    rowPairing q A₀ x d Y d₀ = stateMass x d * ∑ s, ∑ s',
      star (endVec x d Y d₀ s) * (rowOp q A₀ x d Y d₀ s s' * endVec x d Y d₀ s') := by
  simp only [rowPairing, stateInner, Matrix.mulVec, dotProduct, mul_sum]

/-- `⟨f, 𝒜 f⟩ = ⟨𝒢 f, 𝒯 𝒢 f⟩`: since `𝒢 f` is slot invariant, `𝒮` fixes it on both sides. -/
private theorem pairing_eq (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) :
    pairing q A₀ x d Y d₀ = stateMass x d * ∑ s, ∑ s',
      star (goodVec x d Y d₀ s * endVec x d Y d₀ s) *
        (rowOp q A₀ x d Y d₀ s s' * (goodVec x d Y d₀ s' * endVec x d Y d₀ s')) := by
  -- `𝒢 v` multiplies `v` by the good indicator
  have hG : ∀ v : State x d Y d₀ → ℂ,
      goodOp x d Y d₀ *ᵥ v = fun s => goodVec x d Y d₀ s * v s := fun v => by
    funext s
    rw [goodOp, Matrix.mulVec_diagonal]
    rfl
  -- `𝒢 f` is slot invariant, so `𝒮 𝒢 f = 𝒢 f`
  have hGf : SlotInvariant fun s => goodVec x d Y d₀ s * endVec x d Y d₀ s :=
    fun s s' σ h₁ hσ => by
      simp only [slotInvariant_goodVec s s' σ h₁ hσ, slotInvariant_endVec s s' σ h₁ hσ]
  have hu : SlotInvariant fun s => star (goodVec x d Y d₀ s * endVec x d Y d₀ s) :=
    fun s s' σ h₁ hσ => congrArg star (hGf s s' σ h₁ hσ)
  have hSGf : symOp x d Y d₀ *ᵥ (fun s => goodVec x d Y d₀ s * endVec x d Y d₀ s) =
      fun s => goodVec x d Y d₀ s * endVec x d Y d₀ s :=
    funext (sum_symOp_mul hGf)
  rw [pairing, stateInner, edgeOp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hG (endVec x d Y d₀), hSGf, hG]
  congr 1
  calc ∑ s, star (endVec x d Y d₀ s) * (goodVec x d Y d₀ s *
        (symOp x d Y d₀ *ᵥ (rowOp q A₀ x d Y d₀ *ᵥ
          fun s => goodVec x d Y d₀ s * endVec x d Y d₀ s)) s)
      = ∑ s, star (goodVec x d Y d₀ s * endVec x d Y d₀ s) *
          (symOp x d Y d₀ *ᵥ (rowOp q A₀ x d Y d₀ *ᵥ
            fun s => goodVec x d Y d₀ s * endVec x d Y d₀ s)) s := by
        refine sum_congr rfl fun s _ => ?_
        rw [star_mul', star_goodVec]
        ring
    _ = ∑ s, star (goodVec x d Y d₀ s * endVec x d Y d₀ s) *
          (rowOp q A₀ x d Y d₀ *ᵥ fun s => goodVec x d Y d₀ s * endVec x d Y d₀ s) s :=
        sum_mul_symOp_mulVec hu _
    _ = _ := by simp only [Matrix.mulVec, dotProduct, mul_sum]

/-- Removing the projections costs at most `L^{4C}` times the bad mass: `|f| ≤ L^{2C}` at both
ends. -/
theorem norm_rowPairing_sub_pairing_le {q C CX alo ahi g x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d) (hx : 1 ≤ x) (A₀ Y d₀ : ℝ) :
    ‖rowPairing q A₀ x d Y d₀ - pairing q A₀ x d Y d₀‖ ≤
      stateMass x d * Real.log x ^ (4 * C) * badMass q A₀ x d Y d₀ := by
  classical
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hm := stateMass_nonneg x d
  have hL4 : Real.log x ^ (4 * C) = (Real.log x ^ C) ^ 4 := by
    rw [mul_comm, Real.rpow_mul hL, ← Real.rpow_natCast]
    norm_num
  -- the difference is `∑ f̄ 𝒯 f (1 - g g')`
  rw [rowPairing_eq_sum, pairing_eq, ← mul_sub, ← sum_sub_distrib]
  simp only [← sum_sub_distrib]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm, mul_assoc, hL4, badMass, mul_sum]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun s _ => ?_)) hm
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun s' _ => ?_)
  have hdiff : star (endVec x d Y d₀ s) * (rowOp q A₀ x d Y d₀ s s' * endVec x d Y d₀ s') -
      star (goodVec x d Y d₀ s * endVec x d Y d₀ s) *
        (rowOp q A₀ x d Y d₀ s s' * (goodVec x d Y d₀ s' * endVec x d Y d₀ s')) =
      star (endVec x d Y d₀ s) * rowOp q A₀ x d Y d₀ s s' * endVec x d Y d₀ s' *
        (1 - goodVec x d Y d₀ s * goodVec x d Y d₀ s') := by
    rw [star_mul', star_goodVec]
    ring
  -- each factor `f` costs `L^{2C}`, and `1 - g g'` is at most the bad count
  rw [hdiff, norm_mul, norm_mul, norm_mul, norm_star]
  calc ‖endVec x d Y d₀ s‖ * ‖rowOp q A₀ x d Y d₀ s s'‖ * ‖endVec x d Y d₀ s'‖ *
        ‖1 - goodVec x d Y d₀ s * goodVec x d Y d₀ s'‖
      ≤ (Real.log x ^ C) ^ 2 * ‖rowOp q A₀ x d Y d₀ s s'‖ * (Real.log x ^ C) ^ 2 *
          ((if IsGood x d Y d₀ s.1.1 s.1.2 then 0 else 1) +
            (if IsGood x d Y d₀ s'.1.1 s'.1.2 then 0 else 1)) := by
        gcongr
        · exact norm_endVec_le hd hL s
        · exact norm_endVec_le hd hL s'
        · exact norm_one_sub_goodVec_le s s'
    _ = _ := by ring

/-- The bad mass is at most `C₀ UV L^{3A₀} exp(-L^{α₋}/8)`, where `UV = d₀ Y X`. -/
theorem eventually_badMass_le {q C CX alo ahi g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (hCX : 1 ≤ CX) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) (hg : 0 < g) (A₀ : ℝ) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      stateMass x d * badMass q A₀ x d (2 ^ j) (2 ^ k) ≤
        C₀ * (2 ^ k * 2 ^ j * d.X) * Real.log x ^ (3 * A₀) *
          Real.exp (-Real.log x ^ alo / 8) :=
  eventually_stateMass_mul_sum_le hq hq₁ hCX halo hahi hg A₀

end Erdos408.OneSided
