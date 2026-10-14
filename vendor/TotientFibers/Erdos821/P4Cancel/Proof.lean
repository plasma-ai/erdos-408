import Erdos821.P4Cancel.Reindex
import Erdos821.P4Bridge.Bridge

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Cancel
open Blueprint.Graph P4Probe

noncomputable section

local instance (priority := high) rowSiteDecEq'' (s M : ℕ) : DecidableEq (RowSite s M) :=
  Classical.decEq _

variable {P : PrimeGroups}

/-- `SymmetricFullComponentTask`, transported to big labels: the tail-averaged
full component of one side of a symmetric test is small. -/
lemma sideFull_tail_norm (hSFC : SymmetricFullComponentTask) (hV : ∀ g, 0 < P.V g)
    (J ell m : ℕ) (hm : 1 ≤ m) (hell : 1 ≤ ell) (hmJ : m ≤ J)
    (hcond : (m + ell) * (m + ell - 1) ≤ J + ell)
    (block : P.BigGroup → Bool) (side : Bool) (F : P.BigLabels (J + ell) → ℂ)
    (hF : ∀ (π : P.BigPermutations (J + ell)) a, F (P.actBig π a) = F a) :
    idealVectorNorm P (J + ell)
        (bigCoordinateAverage P (J + ell) (tailCoordinates P J ell)
          (sideFull (sideSites (P := P) (M := J + ell) m block side) F)) ≤
      Real.sqrt ((2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^
          (Finset.univ.filter (fun g : P.BigGroup => block g = side)).card) *
        idealVectorNorm P (J + ell) F := by
  have hβ : 0 ≤ 2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell := by positivity
  rw [tail_sideFull hV, idealVectorNorm_flat, idealVectorNorm_flat, flatTest_of,
    ← Real.sqrt_mul (pow_nonneg hβ _)]
  apply Real.sqrt_le_sqrt
  let f : ProbeSample (rowAlpha P) (J + ell) → ℂ := fun x => F ((toRows P (J + ell)).symm x)
  have hft : flatTest F = fun y => f (flattenRows.symm y) := rfl
  have hfun : productProbeProjection (flatW P (J + ell)) (tailSites J ell)
      (sideSites m block side) (flatTest F) =
      fun y => fullProbeComponent (rowW P) (tailSites J ell) (sideSites m block side) f
        (flattenRows.symm y) := by
    funext y
    rw [hft]
    have h := flat_fullProbe (rowW P) (rowW_sum hV) (tailSites J ell) (sideSites m block side)
      f (flattenRows.symm y)
    simpa only [Equiv.apply_symm_apply] using h
  rw [hfun, hft, flatSqNorm_eq (rowW P)
      (fullProbeComponent (rowW P) (tailSites J ell) (sideSites m block side) f),
    flatSqNorm_eq (rowW P) f, ← blockSet_card]
  have hsym : ∀ (π : Fin (rowCount P) → Equiv.Perm (Fin (J + ell))) x,
      f (fun g i => x g (π g i)) = f x := fun π x => rows_symmetric F hF π x
  exact hSFC (rowCount P) J ell m (rowAlpha P) (rowW P) (blockSet block side) f
    (rowW_nonneg hV) (rowW_sum hV) hm hell hmJ hcond hsym

lemma probeChoice_card_le (m : ℕ) (block : P.BigGroup → Bool) :
    (Fintype.card (ProbeChoice P m block) : ℝ) ≤ (3 : ℝ) ^ (m * Fintype.card P.BigGroup) := by
  have h1 : Fintype.card (ProbeChoice P m block) ≤
      Fintype.card (P.BigGroup → Finset (Fin m)) :=
    Fintype.card_le_of_injective (fun c : ProbeChoice P m block => c.val) Subtype.val_injective
  rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin, ← pow_mul] at h1
  have h2 : 2 ^ (m * Fintype.card P.BigGroup) ≤ 3 ^ (m * Fintype.card P.BigGroup) :=
    Nat.pow_le_pow_left (by norm_num) _
  exact_mod_cast h1.trans h2

end
end Erdos821.P4Cancel

namespace Erdos821.P4Probe
open Blueprint.Graph Erdos821.P4Cancel

noncomputable section

local instance (priority := high) rowSiteDecEqFinal (s M : ℕ) : DecidableEq (RowSite s M) :=
  Classical.decEq _

theorem FiniteProbeCancellationTask_proof : FiniteProbeCancellationTask := by
  intro hSFC Fd P J m hj block Q h ξ θ ζ ε hV hm hcond hε hLC
  dsimp only
  set beta : ℝ := 2 * (Fd.ell : ℝ) ^ Fd.ell / (m : ℝ) ^ Fd.ell with hbeta
  set b₁ := (Finset.univ.filter (fun g : P.BigGroup => block g = false)).card with hb₁
  set b₂ := (Finset.univ.filter (fun g : P.BigGroup => block g = true)).card with hb₂
  apply normBound_of_full_pair
  intro f g
  change ‖idealFullPair (fun a b =>
      ((Fintype.card (P.BigPermutations (J + Fd.ell)) : ℂ) ^ 2)⁻¹ *
        ∑ π : P.BigPermutations (J + Fd.ell), ∑ τ : P.BigPermutations (J + Fd.ell),
          ((probeFamily Fd P J m hj block Q h ξ).model 1 ζ).idealRaw θ
            (P.actBig π a) (P.actBig τ b)) f g‖ ≤
    (Real.sqrt (beta ^ b₁) + Real.sqrt (beta ^ b₂) +
        (3 : ℝ) ^ (m * Fintype.card P.BigGroup) * ε) *
      idealVectorNorm P (J + Fd.ell) f * idealVectorNorm P (J + Fd.ell) g
  rw [symmetrized_pair]
  set Fs := symTest P (J + Fd.ell) f with hFs
  set Gs := symTest P (J + Fd.ell) g with hGs
  set R := ((rawFamily Fd P J m).model 1 ζ).idealRaw θ with hR
  set Kp := ((probeFamily Fd P J m hj block Q h ξ).model 1 ζ).idealRaw θ with hKp
  set u := sideFull (sideSites (P := P) (M := J + Fd.ell) m block false) Fs with hu
  set v := sideFull (sideSites (P := P) (M := J + Fd.ell) m block true) Gs with hv
  set nF := idealVectorNorm P (J + Fd.ell) Fs with hnF
  set nG := idealVectorNorm P (J + Fd.ell) Gs with hnG
  set nf := idealVectorNorm P (J + Fd.ell) f with hnf
  set ng := idealVectorNorm P (J + Fd.ell) g with hng
  have hnF0 : 0 ≤ nF := Real.sqrt_nonneg _
  have hnG0 : 0 ≤ nG := Real.sqrt_nonneg _
  have hFf : nF ≤ nf := symTest_norm_le hV f
  have hGg : nG ≤ ng := symTest_norm_le hV g
  have hsF : ∀ (π : P.BigPermutations (J + Fd.ell)) a, Fs (P.actBig π a) = Fs a :=
    fun π a => symTest_invariant f π a
  have hsG : ∀ (π : P.BigPermutations (J + Fd.ell)) a, Gs (P.actBig π a) = Gs a :=
    fun π a => symTest_invariant g π a
  -- per-pattern comparison, summed over all probe choices
  have hcmp : ‖idealFullPair Kp Fs Gs - idealFullPair R Fs Gs +
      idealFullPair R (fun a => Fs a - u a) (fun b => Gs b - v b)‖ ≤
      (Fintype.card (ProbeChoice P m block) : ℝ) * ε * nF * nG := by
    have h0 := probeFamily_comparison_bound PatternComparisonBridgeTask_proof Fd P J m hj block
      Q h ξ θ ζ ε hV hε hLC Fs Gs
    rw [← correction_sum_eq hV hj block Q h ξ R Fs Gs]
    exact h0
  -- the two projection exceptions
  have hsplit : idealFullPair R Fs Gs -
      idealFullPair R (fun a => Fs a - u a) (fun b => Gs b - v b) =
      idealFullPair R u Gs + idealFullPair R (fun a => Fs a - u a) v := by
    rw [idealFullPair_sub_target, idealFullPair_sub_source]
    ring
  have hUb : ‖idealFullPair R u Gs‖ ≤ Real.sqrt (beta ^ b₁) * nF * nG := by
    rw [rawFullPair_tail_average Fd P J m hV θ ζ u Gs]
    refine (rawFullPair_bound Fd P J m hV θ ζ _ _).trans ?_
    apply mul_le_mul
    · exact sideFull_tail_norm hSFC hV J Fd.ell m hm Fd.ell_pos hj hcond block false Fs hsF
    · exact bigCoordinateAverage_norm_le P (J + Fd.ell) hV _ Gs
    · exact Real.sqrt_nonneg _
    · exact mul_nonneg (Real.sqrt_nonneg _) hnF0
  have hVb : ‖idealFullPair R (fun a => Fs a - u a) v‖ ≤ nF * (Real.sqrt (beta ^ b₂) * nG) := by
    rw [rawFullPair_tail_average Fd P J m hV θ ζ _ v]
    refine (rawFullPair_bound Fd P J m hV θ ζ _ _).trans ?_
    apply mul_le_mul
    · exact (bigCoordinateAverage_norm_le P (J + Fd.ell) hV _ _).trans
        (sub_sideFull_norm_le hV _ Fs)
    · exact sideFull_tail_norm hSFC hV J Fd.ell m hm Fd.ell_pos hj hcond block true Gs hsG
    · exact Real.sqrt_nonneg _
    · exact hnF0
  have hcard := probeChoice_card_le (P := P) m block
  have hkey : idealFullPair Kp Fs Gs =
      (idealFullPair Kp Fs Gs - idealFullPair R Fs Gs +
        idealFullPair R (fun a => Fs a - u a) (fun b => Gs b - v b)) +
      (idealFullPair R u Gs + idealFullPair R (fun a => Fs a - u a) v) := by
    rw [← hsplit]
    ring
  have hβ1 : 0 ≤ Real.sqrt (beta ^ b₁) := Real.sqrt_nonneg _
  have hβ2 : 0 ≤ Real.sqrt (beta ^ b₂) := Real.sqrt_nonneg _
  have h3 : 0 ≤ (3 : ℝ) ^ (m * Fintype.card P.BigGroup) * ε := by positivity
  rw [hkey]
  calc _ ≤ ‖idealFullPair Kp Fs Gs - idealFullPair R Fs Gs +
        idealFullPair R (fun a => Fs a - u a) (fun b => Gs b - v b)‖ +
        (‖idealFullPair R u Gs‖ + ‖idealFullPair R (fun a => Fs a - u a) v‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ (Fintype.card (ProbeChoice P m block) : ℝ) * ε * nF * nG +
        (Real.sqrt (beta ^ b₁) * nF * nG + nF * (Real.sqrt (beta ^ b₂) * nG)) :=
        add_le_add hcmp (add_le_add hUb hVb)
    _ = (Real.sqrt (beta ^ b₁) + Real.sqrt (beta ^ b₂) +
          (Fintype.card (ProbeChoice P m block) : ℝ) * ε) * (nF * nG) := by ring
    _ ≤ (Real.sqrt (beta ^ b₁) + Real.sqrt (beta ^ b₂) +
          (3 : ℝ) ^ (m * Fintype.card P.BigGroup) * ε) * (nf * ng) := by
        apply mul_le_mul
        · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard hε)
        · exact mul_le_mul hFf hGg hnG0 (hnF0.trans hFf)
        · exact mul_nonneg hnF0 hnG0
        · exact add_nonneg (add_nonneg hβ1 hβ2) h3
    _ = _ := by ring

end
end Erdos821.P4Probe
