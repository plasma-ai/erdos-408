import Erdos821.P5.MellinPatternIntegral

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

def gatedFamilySum {F : FixedData} {G : Blueprint.Graph.PrimeGroups} {J m : ℕ}
    (B : Family F G J m) (k : ℤ) (ζ : ℝ) (S T : Finset ℤ)
    (f g : ℤ → ℂ) (weight : ℤ → ℕ → ℂ)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v)) : ℂ :=
  ∑ v : Fin B.count, ∑ u : FreeDraw (B.pattern v), (freeDrawLaw (B.pattern v) u : ℂ) *
    ∑ n ∈ S, ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
      gatedPatternTerm (B.model k ζ) (B.pattern v) (assembleAux (B.pattern v) u (unused v))
        T f g weight n a b

theorem gatedPatternTerm_aux_ext {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (ν : Pattern G J F.ell m) (u u' : G.Aux J)
    (T : Finset ℤ) (f g : ℤ → ℂ) (weight : ℤ → ℕ → ℂ)
    (n : ℤ) (a b : A.Labels) (hu : ∀ g i, i ∈ ν.changed g → u g i = u' g i) :
    gatedPatternTerm A ν u T f g weight n a b =
      gatedPatternTerm A ν u' T f g weight n a b := by
  have ht : patternTarget A ν u n a = patternTarget A ν u' n a := by
    rw [patternTarget, patternTarget, pattern_D_aux_ext ν a u u' hu]
  unfold gatedPatternTerm
  rw [pattern_D_aux_ext ν a u u' hu, ht,
    physicalPatternBody_aux_ext A ν u u' n (patternTarget A ν u' n a) a b hu]

/-- The unweighted family sum is the actual graph pairing. The unused
auxiliary coordinates may be filled by any shared draws. -/
theorem gatedFamilySum_eq_pairing {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ X : ℝ) (T : Finset ℤ)
    (f g : ℤ → ℂ) (hV : ∀ g, G.V g ≠ 0)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v)) :
    gatedFamilySum B k ζ (dyad X) T f g (fun _ _ => 1) unused =
      (B.model k ζ).pairing X (T.product Finset.univ) f (fun z => g z.1) := by
  rw [pairing_shift_expansion (B.model k ζ) hV X T f g]
  simp only [show (B.model k ζ).pattern = B.pattern from rfl]
  unfold gatedFamilySum
  simp_rw [Finset.mul_sum]
  let H := fun v u n => ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
    (freeDrawLaw (B.pattern v) u : ℂ) *
      gatedPatternTerm (B.model k ζ) (B.pattern v) (assembleAux (B.pattern v) u (unused v))
        T f g (fun _ _ => 1) n a b
  have hswap : (∑ v : Fin B.count, ∑ u : FreeDraw (B.pattern v), ∑ n ∈ dyad X, H v u n) =
      ∑ n ∈ dyad X, ∑ v : Fin B.count, ∑ u : FreeDraw (B.pattern v), H v u n := by
    calc
      _ = ∑ v : Fin B.count, ∑ n ∈ dyad X, ∑ u : FreeDraw (B.pattern v), H v u n :=
        Finset.sum_congr rfl (fun v hv => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [hswap]
  dsimp only [H]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [gatedPatternTerm_aux_ext (B.model k ζ) (B.pattern v)
    (assembleAux (B.pattern v) u (unused v))
    (assembleAux (B.pattern v) u (unusedAuxDraw (B.pattern v) hV)) T f g
    (fun _ _ => 1) n a b (fun g i hi => by
      rw [assembleAux_free (B.pattern v) u (unused v) g ⟨i, hi⟩,
        assembleAux_free (B.pattern v) u (unusedAuxDraw (B.pattern v) hV) g ⟨i, hi⟩])]
  unfold gatedPatternTerm
  dsimp only [Family.model]
  simp only [one_mul, mul_assoc]
  rfl

theorem integrable_family_sum {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (S : Finset ℤ)
    (H : (v : Fin B.count) → FreeDraw (B.pattern v) → ℤ →
      G.Labels (J + F.ell) → G.Labels (J + F.ell) → (Fin 1 → ℝ) → ℂ)
    (hH : ∀ v u n, n ∈ S → ∀ a b, Integrable (H v u n a b)) :
    Integrable (fun ξ => ∑ v : Fin B.count, ∑ u : FreeDraw (B.pattern v),
      (freeDrawLaw (B.pattern v) u : ℂ) *
      ∑ n ∈ S, ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell), H v u n a b ξ) := by
  apply integrable_finsetSum
  intro v hv
  apply integrable_finsetSum
  intro u hu
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro n hn
  apply integrable_finsetSum
  intro a ha
  exact integrable_finsetSum _ (fun b hb => hH v u n hn a b)

theorem integral_family_sum {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (S : Finset ℤ)
    (H : (v : Fin B.count) → FreeDraw (B.pattern v) → ℤ →
      G.Labels (J + F.ell) → G.Labels (J + F.ell) → (Fin 1 → ℝ) → ℂ)
    (hH : ∀ v u n, n ∈ S → ∀ a b, Integrable (H v u n a b)) :
    (∫ ξ, ∑ v : Fin B.count, ∑ u : FreeDraw (B.pattern v),
      (freeDrawLaw (B.pattern v) u : ℂ) *
      ∑ n ∈ S, ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell), H v u n a b ξ) =
    ∑ v : Fin B.count, ∑ u : FreeDraw (B.pattern v), (freeDrawLaw (B.pattern v) u : ℂ) *
      ∑ n ∈ S, ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell), ∫ ξ, H v u n a b ξ := by
  have hab v u n hn a : Integrable (fun ξ => ∑ b : G.Labels (J + F.ell), H v u n a b ξ) :=
    integrable_finsetSum _ (fun b hb => hH v u n hn a b)
  have ha v u n hn : Integrable (fun ξ => ∑ a : G.Labels (J + F.ell),
      ∑ b : G.Labels (J + F.ell), H v u n a b ξ) :=
    integrable_finsetSum _ (fun a ha => hab v u n hn a)
  have hn v u : Integrable (fun ξ => ∑ n ∈ S, ∑ a : G.Labels (J + F.ell),
      ∑ b : G.Labels (J + F.ell), H v u n a b ξ) :=
    integrable_finsetSum _ (fun n hn => ha v u n hn)
  have hu v : Integrable (fun ξ => ∑ u : FreeDraw (B.pattern v),
      (freeDrawLaw (B.pattern v) u : ℂ) * ∑ n ∈ S, ∑ a : G.Labels (J + F.ell),
      ∑ b : G.Labels (J + F.ell), H v u n a b ξ) :=
    integrable_finsetSum _ (fun u hu => (hn v u).const_mul _)
  rw [integral_finsetSum _ (fun v hv => hu v)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [integral_finsetSum _ (fun u hu => (hn v u).const_mul _)]
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_const_mul, integral_finsetSum _ (fun n hn => ha v u n hn)]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn'
  rw [integral_finsetSum _ (fun a ha => hab v u n hn' a)]
  apply Finset.sum_congr rfl
  intro a ha'
  exact integral_finsetSum _ (fun b hb => hH v u n hn' a b)

end Erdos821.P5Core
