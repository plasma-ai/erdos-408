import Erdos821.P4Probe.RawAssembly

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

lemma idealFullPair_sum_source {P : PrimeGroups} {M : ℕ} {ι : Type*}
    (K : P.BigLabels M → P.BigLabels M → ℂ) (V : Finset ι)
    (c : ι → ℂ) (f : ι → P.BigLabels M → ℂ) (g : P.BigLabels M → ℂ) :
    idealFullPair K (fun a => ∑ i ∈ V, c i * f i a) g =
      ∑ i ∈ V, star (c i) * idealFullPair K (f i) g := by
  unfold idealFullPair
  simp only [star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
  let term := fun (a b : P.BigLabels M) (i : ι) =>
    (P.idealMass a : ℂ) * (star (f i a) * star (c i)) * K a b * g b
  change (∑ a, ∑ b, ∑ i ∈ V, term a b i) = _
  calc
    _ = ∑ a, ∑ i ∈ V, ∑ b, term a b i := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ i ∈ V, ∑ a, ∑ b, term a b i := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp [term]
      ring

lemma idealFullPair_sum_target {P : PrimeGroups} {M : ℕ} {ι : Type*}
    (K : P.BigLabels M → P.BigLabels M → ℂ) (V : Finset ι)
    (c : ι → ℂ) (f : P.BigLabels M → ℂ) (g : ι → P.BigLabels M → ℂ) :
    idealFullPair K f (fun b => ∑ i ∈ V, c i * g i b) =
      ∑ i ∈ V, c i * idealFullPair K f (g i) := by
  unfold idealFullPair
  simp only [Finset.mul_sum]
  let term := fun (a b : P.BigLabels M) (i : ι) =>
    (P.idealMass a : ℂ) * star (f a) * K a b * (c i * g i b)
  change (∑ a, ∑ b, ∑ i ∈ V, term a b i) = _
  calc
    _ = ∑ a, ∑ i ∈ V, ∑ b, term a b i := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ i ∈ V, ∑ a, ∑ b, term a b i := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp [term]
      ring

lemma idealFullPair_sub_source {P : PrimeGroups} {M : ℕ}
    (K : P.BigLabels M → P.BigLabels M → ℂ) (f h g : P.BigLabels M → ℂ) :
    idealFullPair K (fun a => f a - h a) g = idealFullPair K f g - idealFullPair K h g := by
  simp [idealFullPair, star_sub, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma idealFullPair_sum_both {P : PrimeGroups} {M : ℕ} {ι κ : Type*}
    (K : P.BigLabels M → P.BigLabels M → ℂ) (V : Finset ι) (W : Finset κ)
    (c : ι → ℂ) (d : κ → ℂ)
    (f : ι → P.BigLabels M → ℂ) (g : κ → P.BigLabels M → ℂ) :
    idealFullPair K (fun a => ∑ i ∈ V, c i * f i a) (fun b => ∑ j ∈ W, d j * g j b) =
      ∑ i ∈ V, ∑ j ∈ W, star (c i) * d j * idealFullPair K (f i) (g j) := by
  rw [idealFullPair_sum_source]
  apply Finset.sum_congr rfl
  intro i _
  rw [idealFullPair_sum_target, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma idealFullPair_sub_target {P : PrimeGroups} {M : ℕ}
    (K : P.BigLabels M → P.BigLabels M → ℂ) (f g h : P.BigLabels M → ℂ) :
    idealFullPair K f (fun b => g b - h b) = idealFullPair K f g - idealFullPair K f h := by
  simp [idealFullPair, mul_sub, Finset.sum_sub_distrib]

end
end Erdos821.P4Probe
