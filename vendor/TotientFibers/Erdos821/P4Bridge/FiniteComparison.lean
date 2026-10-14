import Erdos821.P4Probe.FinitePairing
import Erdos821.P4Probe.ConditionalBounds

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open P4Probe
noncomputable section

lemma weighted_mean_sq_le {A : Type*} [Fintype A] (w : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1) (f : A → ℂ) :
    ‖∑ a, (w a : ℂ) * f a‖ ^ 2 ≤ ∑ a, w a * ‖f a‖ ^ 2 := by
  have h := weighted_pair_le w hw (fun _ => 1) f (fun _ => 1) (by simp)
  simp only [star_one, mul_one, norm_one, one_pow] at h
  rw [hsum, Real.sqrt_one, one_mul] at h
  have he : 0 ≤ ∑ a, w a * ‖f a‖ ^ 2 :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) (sq_nonneg _))
  have hh := Real.sq_sqrt he
  nlinarith [norm_nonneg (∑ a, (w a : ℂ) * f a), Real.sqrt_nonneg (∑ a, w a * ‖f a‖ ^ 2)]

lemma sum_pair_factor {A B : Type*} [Fintype A] [Fintype B]
    (w : A → ℝ) (v : B → ℝ) (f : A → ℂ) (g : B → ℂ) (K : ℂ) :
    (∑ a, ∑ b, ((w a * v b : ℝ) : ℂ) * star (f a) * g b * K) =
      star (∑ a, (w a : ℂ) * f a) * (∑ b, (v b : ℂ) * g b) * K := by
  simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma sum_four_factor {A T B U : Type*} [Fintype A] [Fintype T] [Fintype B] [Fintype U]
    (w : A → ℝ) (wt : T → ℝ) (v : B → ℝ) (vu : U → ℝ)
    (f : A → T → ℂ) (g : B → U → ℂ) (K : ℂ) :
    (∑ a, ∑ t, ∑ b, ∑ u,
      ((w a * wt t * v b * vu u : ℝ) : ℂ) * star (f a t) * g b u * K) =
      star (∑ a, ∑ t, ((w a * wt t : ℝ) : ℂ) * f a t) *
        (∑ b, ∑ u, ((v b * vu u : ℝ) : ℂ) * g b u) * K := by
  have hh := sum_pair_factor (fun x : A × T => w x.1 * wt x.2)
    (fun x : B × U => v x.1 * vu x.2) (fun x => f x.1 x.2) (fun x => g x.1 x.2) K
  simpa only [Fintype.sum_prod_type, mul_assoc] using hh

lemma sum_seven_permute {A B C D E F G : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F] [Fintype G]
    (H : A → B → C → D → E → F → G → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g, H a b c d e f g) =
      ∑ b, ∑ d, ∑ f, ∑ g, ∑ a, ∑ c, ∑ e, H a b c d e f g := by
  let e : (A × B × C × D × E × F × G) ≃ (B × D × F × G × A × C × E) :=
    { toFun := fun x => (x.2.1, x.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
        x.1, x.2.2.1, x.2.2.2.2.1)
      invFun := fun x => (x.2.2.2.2.1, x.1, x.2.2.2.2.2.1, x.2.1,
        x.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hh : (∑ x : A × B × C × D × E × F × G,
      H x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2) =
      ∑ x : B × D × F × G × A × C × E,
        H x.2.2.2.2.1 x.1 x.2.2.2.2.2.1 x.2.1 x.2.2.2.2.2.2 x.2.2.1 x.2.2.2.1 := by
    apply Fintype.sum_equiv e
    intro x
    rfl
  simpa only [Fintype.sum_prod_type] using hh

lemma mean_product_sq_le {A T : Type*} [Fintype A] [Fintype T]
    (w : A → ℝ) (v : T → ℝ) (hw : ∀ a, 0 ≤ w a) (hv : ∀ t, 0 ≤ v t)
    (hsw : ∑ a, w a = 1) (hsv : ∑ t, v t = 1) (f : A → T → ℂ) :
    ‖∑ a, ∑ t, ((w a * v t : ℝ) : ℂ) * f a t‖ ^ 2 ≤
      ∑ a, ∑ t, w a * v t * ‖f a t‖ ^ 2 := by
  have h := weighted_mean_sq_le (fun x : A × T => w x.1 * v x.2)
    (fun x => mul_nonneg (hw x.1) (hv x.2))
    (by rw [Fintype.sum_prod_type]; simp_rw [← Finset.mul_sum, hsv, mul_one]; exact hsw)
    (fun x => f x.1 x.2)
  simpa only [Fintype.sum_prod_type] using h

lemma sum_six_permute {A B C D E F : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F]
    (H : A → B → C → D → E → F → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, H a b c d e f) =
      ∑ b, ∑ d, ∑ a, ∑ c, ∑ e, ∑ f, H a b c d e f := by
  let e : (A × B × C × D × E × F) ≃ (B × D × A × C × E × F) :=
    { toFun := fun x => (x.2.1, x.2.2.2.1, x.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2)
      invFun := fun x => (x.2.2.1, x.1, x.2.2.2.1, x.2.1, x.2.2.2.2.1, x.2.2.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hh : (∑ x : A × B × C × D × E × F,
      H x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) =
      ∑ x : B × D × A × C × E × F,
        H x.2.2.1 x.1 x.2.2.2.1 x.2.1 x.2.2.2.2.1 x.2.2.2.2.2 := by
    apply Fintype.sum_equiv e
    intro x
    rfl
  simpa only [Fintype.sum_prod_type] using hh

end
end Erdos821.P4Bridge
