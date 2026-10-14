import Erdos821.S34.BilinearRestrictions
import Erdos821.S34.ProductSupport
import Erdos821.P5.Basic

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem atom_cap_on_range (G : PrimeGroups) (k : Fin G.size → ℕ)
    (s : Finset (Tuple G k)) (U H : ℝ) (hU : 0 < U) (hH : 0 ≤ H)
    (hlo : ∀ z ∈ s, U / 2 ≤ (product G k z : ℝ))
    (hρ : ∀ n : ℕ, 0 < n → rho G k n ≤ H / n) :
    ∀ n ∈ s.image (fun z => (product G k z : ℤ)),
      (∑ z, if (product G k z : ℤ) = n then tupleWeight G k z else 0) ≤ 2 * H / U := by
  intro n hn
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
  have he : (∑ D, if (product G k D : ℤ) = (product G k z : ℤ) then tupleWeight G k D else 0) =
      rho G k (product G k z) := by
    simp only [rho, Int.natCast_inj]
  rw [he]
  calc
    _ ≤ H / product G k z := hρ _ (tuple_product_pos G k z)
    _ ≤ H / (U / 2) := div_le_div_of_nonneg_left hH (by linarith) (hlo z hz)
    _ = _ := by field_simp

theorem probability_bilinear_dyads (G : PrimeGroups) (a b : Fin G.size → ℕ)
    (s : Finset (Tuple G a)) (t : Finset (Tuple G b))
    (f : Tuple G a → ℂ) (g : Tuple G b → ℂ) (U V H θ η ζ : ℝ) (u : ℤ) (r : ℕ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hH : 0 ≤ H) (hr : 1 ≤ r)
    (hu : Nat.Coprime u.natAbs r) (hθ : θ = (u : ℝ) / r + η)
    (hη : |η| ≤ (r : ℝ) ^ (-2 : ℤ))
    (hs : ∀ z ∈ s, U / 2 ≤ (product G a z : ℝ) ∧ (product G a z : ℝ) ≤ 4 * U)
    (ht : ∀ z ∈ t, V / 2 ≤ (product G b z : ℝ) ∧ (product G b z : ℝ) ≤ 4 * V)
    (hρa : ∀ n : ℕ, 0 < n → rho G a n ≤ H / n)
    (hρb : ∀ n : ℕ, 0 < n → rho G b n ≤ H / n) :
    ‖∑ X ∈ s, ∑ Y ∈ t, (tupleWeight G a X : ℂ) * (tupleWeight G b Y : ℂ) *
        f X * g Y * mellin (product G a X * product G b Y) ζ *
        e (θ * product G a X * product G b Y)‖ ≤
      integerBilinearConstant * Real.sqrt (2 * H / U) * tupleNorm G a f *
        Real.sqrt (2 * H / V) * tupleNorm G b g *
        Real.sqrt (U + (1 + V / r) * (U + r * Real.log (2 * r))) := by
  have hUp : 0 < U := by linarith
  have hVp : 0 < V := by linarith
  let f' := fun X => f X * mellin (product G a X) ζ
  let g' := fun Y => g Y * mellin (product G b Y) ζ
  have hwa := Erdos821.S34.Proofs.tupleWeight_nonneg (coreGroups G) a
  have hwb := Erdos821.S34.Proofs.tupleWeight_nonneg (coreGroups G) b
  have hp (z : Tuple G a) (hz : z ∈ s) :
      U / 2 ≤ ((product G a z : ℤ) : ℝ) ∧ ((product G a z : ℤ) : ℝ) ≤ U / 2 + 4 * U := by
    norm_cast
    constructor
    · exact (hs z hz).1
    · linarith [(hs z hz).2]
  have hq (z : Tuple G b) (hz : z ∈ t) :
      V / 2 ≤ ((product G b z : ℤ) : ℝ) ∧ ((product G b z : ℤ) : ℝ) ≤ V / 2 + 4 * V := by
    norm_cast
    constructor
    · exact (ht z hz).1
    · linarith [(ht z hz).2]
  have hb := bilinear_reduction_restricted (tupleWeight G a) (tupleWeight G b) hwa hwb
    (fun X => (product G a X : ℤ)) (fun Y => (product G b Y : ℤ)) f' g' s t
    U V (U / 2) (V / 2) θ η u r (2 * H / U) (2 * H / V)
    hU hV hr hu hθ hη hp hq (by positivity) (by positivity)
    (atom_cap_on_range G a s U H hUp hH (fun z hz => (hs z hz).1) hρa)
    (atom_cap_on_range G b t V H hVp hH (fun z hz => (ht z hz).1) hρb)
  have heq : (∑ X ∈ s, ∑ Y ∈ t, (tupleWeight G a X : ℂ) * (tupleWeight G b Y : ℂ) *
      f' X * g' Y * e (θ * (product G a X : ℤ) * (product G b Y : ℤ))) =
      ∑ X ∈ s, ∑ Y ∈ t, (tupleWeight G a X : ℂ) * (tupleWeight G b Y : ℂ) *
        f X * g Y * mellin (product G a X * product G b Y) ζ *
        e (θ * product G a X * product G b Y) := by
    apply Finset.sum_congr rfl
    intro X _
    apply Finset.sum_congr rfl
    intro Y _
    have hX : (0 : ℝ) < product G a X := by exact_mod_cast tuple_product_pos G a X
    have hY : (0 : ℝ) < product G b Y := by exact_mod_cast tuple_product_pos G b Y
    simp only [f', g', Erdos821.P5Core.mellin_mul _ _ ζ hX hY, Int.cast_natCast]
    ring
  rw [heq] at hb
  have hf : weightedFrameNorm (tupleWeight G a) f' = tupleNorm G a f := by
    simp only [weightedFrameNorm, tupleNorm, f', norm_mul, Erdos821.P5Core.norm_mellin, mul_one]
  have hg : weightedFrameNorm (tupleWeight G b) g' = tupleNorm G b g := by
    simp only [weightedFrameNorm, tupleNorm, g', norm_mul, Erdos821.P5Core.norm_mellin, mul_one]
  rwa [hf, hg] at hb

end
end Erdos821.S34Core
