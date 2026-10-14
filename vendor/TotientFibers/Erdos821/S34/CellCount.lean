import Erdos821.S34.ProductSupport

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem occupied_cell_count {α : Type*} [Fintype α] (n : α → ℕ)
    (h H : ℝ) (hh : 0 < h) (hH : 0 ≤ H)
    (hn : ∀ x, Real.log (n x) ≤ H) :
    ((Finset.univ.image (fun x => cell h (n x))).card : ℝ) ≤ H / h + 1 := by
  have hfloor : 0 ≤ ⌊H / h⌋ := Int.floor_nonneg.mpr (div_nonneg hH hh.le)
  have hs : Finset.univ.image (fun x => cell h (n x)) ⊆ Finset.Icc 0 ⌊H / h⌋ := by
    intro j hj
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_Icc.mpr
    constructor
    · exact Int.floor_nonneg.mpr (div_nonneg (Real.log_natCast_nonneg _) hh.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right (hn x) hh.le)
  have hc : ((Finset.Icc (0 : ℤ) ⌊H / h⌋).card : ℝ) = (⌊H / h⌋ : ℝ) + 1 := by
    have ht := Int.card_Icc_of_le (a := (0 : ℤ)) (b := ⌊H / h⌋) (by omega)
    simp only [sub_zero] at ht
    exact_mod_cast ht
  calc
    _ ≤ ((Finset.Icc (0 : ℤ) ⌊H / h⌋).card : ℝ) := by exact_mod_cast Finset.card_le_card hs
    _ = _ := hc
    _ ≤ _ := by linarith [Int.floor_le (H / h)]

theorem product_cell_count (P : Geometry) (x : ℝ) (G : PrimeGroups)
    (hL : 0 ≤ L x) (hT : 0 ≤ T x) (hG : Admissible P x G)
    (k : Fin G.size → ℕ) (m : ℕ) (hk : bigSlots G k m)
    (h : ℝ) (hh : 0 < h) :
    ((Finset.univ.image (fun z : Tuple G k => cell h (product G k z))).card : ℝ) ≤
      ((m : ℝ) * P.C₀ * T x * L x ^ P.d) / h + 1 := by
  apply occupied_cell_count (fun z => product G k z) h _ hh
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg m)
      P.positive.2.1.le) hT) (Real.rpow_nonneg hL _)
  · exact fun z => (log_product_bounds P x G hL hG k m hk z).2

end
end Erdos821.S34Core
