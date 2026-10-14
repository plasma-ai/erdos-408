import Erdos821.P5.MellinIntegralBound

noncomputable section

namespace Erdos821.P5Core

/-- The main Fourier mass, tail precision and dyad count are combined
without allowing the absolute-frequency cost to affect the main cutoff. -/
theorem logarithmic_main_tail_bound (Q N I U Cdyad Kmain KA Kcost Rcost D : ℝ)
    (hQ : 1 ≤ Q) (hN : 0 ≤ N) (hK : 0 ≤ Kmain) (hKA : 0 ≤ KA)
    (hcount : N ≤ Cdyad * Q) (hmass : I ≤ Q ^ Kcost)
    (htail : U ≤ KA * Q ^ (-(D + |Rcost| + 1))) :
    N * (I * (Kmain * Q ^ (-(D + Kcost + 1))) + U * Q ^ Rcost) ≤
      Cdyad * (Kmain + KA) * Q ^ (-D) := by
  have hQpos : 0 < Q := by linarith
  have hpow : Q ^ Kcost * Q ^ (-(D + Kcost + 1)) = Q ^ (-D - 1) := by
    rw [← Real.rpow_add hQpos]
    congr 1
    ring
  have hmain : I * (Kmain * Q ^ (-(D + Kcost + 1))) ≤ Kmain * Q ^ (-D - 1) := by
    calc
      _ ≤ Q ^ Kcost * (Kmain * Q ^ (-(D + Kcost + 1))) :=
        mul_le_mul_of_nonneg_right hmass (mul_nonneg hK (Real.rpow_nonneg hQpos.le _))
      _ = _ := by rw [← mul_assoc, mul_comm (Q ^ Kcost) Kmain, mul_assoc, hpow]
  have htailpow : Q ^ (-(D + |Rcost| + 1)) * Q ^ Rcost ≤ Q ^ (-D - 1) := by
    rw [← Real.rpow_add hQpos]
    apply Real.rpow_le_rpow_of_exponent_le hQ
    linarith [le_abs_self Rcost]
  have htail' : U * Q ^ Rcost ≤ KA * Q ^ (-D - 1) := by
    calc
      _ ≤ (KA * Q ^ (-(D + |Rcost| + 1))) * Q ^ Rcost :=
        mul_le_mul_of_nonneg_right htail (Real.rpow_nonneg hQpos.le _)
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left htailpow hKA
  have hsum : I * (Kmain * Q ^ (-(D + Kcost + 1))) + U * Q ^ Rcost ≤
      (Kmain + KA) * Q ^ (-D - 1) := by linarith
  have hcancel : Q * Q ^ (-D - 1) = Q ^ (-D) := by
    conv_lhs => lhs; rw [← Real.rpow_one Q]
    rw [← Real.rpow_add hQpos]
    congr 1
    ring
  calc
    _ ≤ N * ((Kmain + KA) * Q ^ (-D - 1)) := mul_le_mul_of_nonneg_left hsum hN
    _ ≤ (Cdyad * Q) * ((Kmain + KA) * Q ^ (-D - 1)) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg (add_nonneg hK hKA) (Real.rpow_nonneg hQpos.le _))
    _ = Cdyad * (Kmain + KA) * (Q * Q ^ (-D - 1)) := by ring
    _ = _ := by rw [hcancel]

end Erdos821.P5Core
