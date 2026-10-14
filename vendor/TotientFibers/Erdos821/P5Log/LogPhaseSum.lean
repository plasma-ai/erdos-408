import Erdos821.Classical.DerivativeTests
import OAI.NumberTheory.EgyptianFractions.CorrelationPhase
import OAI.NumberTheory.EgyptianFractions.ReciprocalDerivatives

noncomputable section
open scoped BigOperators
open scoped ContDiff Topology
open Filter

namespace Erdos821.P5Log
open Blueprint.Analytic

/-- §4 log-phase-sum on arbitrary subintervals. For |u|≤cN use the first
derivative test. Otherwise select 2≤k≤ceil(4/τ)+3 with
N^(k−2+1/10)≤|u|≤N^(k−1/10). For k=2 use the second derivative test.
For k>2 use k−2 van der Corput differences with integer shifts at most
floor(N^(1/(20k))). Their second derivatives are iterated integrals of the
kth log derivative and have constant sign and size between
c_k N^(−2+1/10) and C_k N^(−1/20). The second derivative bound is then
O(N^(1−1/40)). Zero-extend inside a containing interval of length O(N);
every correlation support is an interval. Iterate B_j²≤C(H⁻¹+B_(j+1)).
The final δ may be any smaller fixed positive exponent. All constants
must be uniform in q,a; a<q makes qy+a comparable to qN. -/
def LogPhaseSumTask : Prop :=
  Blueprint.DerivativeTests → ∀ τ : ℝ, 0 < τ →
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ (N lo hi u : ℝ) (q a : ℕ),
      x ^ (τ / 2) ≤ N → N ≤ lo → lo ≤ hi → hi ≤ 2 * N →
      1 ≤ q → a < q → 1 ≤ |u| → |u| ≤ x ^ (2 : ℕ) →
      ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
        mellin (q * (y : ℝ) + a) u‖ ≤ K * N * (|u|⁻¹ + N ^ (-δ))

private def logPhase (q a : ℕ) (u y : ℝ) : ℝ :=
  u / (2 * Real.pi) * Real.log ((q : ℝ) * y + a)

/-! Local logarithmic derivative lemmas. These are the forms used by the
generic positive-shift mean-value theorem imported through `CorrelationPhase`.
-/

private lemma logPhase_base_smooth (Z : ℝ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => Z * Real.log y) (Set.Ioi 0) :=
  contDiffOn_const.mul (Real.contDiffOn_log.mono (fun _ hx => ne_of_gt hx))

private lemma logPhase_base_iteratedDeriv (k : ℕ) (Z : ℝ) {x : ℝ}
    (hx : 0 < x) :
    iteratedDeriv (k + 1) (fun y : ℝ => Z * Real.log y) x =
      (-1 : ℝ) ^ k * (k.factorial : ℝ) * Z / x ^ (k + 1) := by
  have he : deriv (fun y : ℝ => Z * Real.log y) =ᶠ[nhds x]
      (fun y => Z / y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    have hd := (Real.hasDerivAt_log (ne_of_gt hy)).const_mul Z
    simpa only [div_eq_mul_inv] using hd.deriv
  rw [iteratedDeriv_succ', he.iteratedDeriv_eq k]
  exact OAI.Problem337.reciprocal_phase_iteratedDeriv k Z x

private lemma logPhase_base_abs_iteratedDeriv (k : ℕ) (Z : ℝ) {x : ℝ}
    (hx : 0 < x) :
    |iteratedDeriv (k + 1) (fun y : ℝ => Z * Real.log y) x| =
      (k.factorial : ℝ) * |Z| / x ^ (k + 1) := by
  rw [logPhase_base_iteratedDeriv k Z hx]
  simp [abs_div, abs_mul, abs_pow, abs_of_pos hx]

private lemma logPhase_forwardDifference_second_bounds (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (Z : ℝ) {U V x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxV : x + hs.sum ≤ V) :
    hs.prod * ((hs.length + 1).factorial : ℝ) * |Z| / V ^ (hs.length + 2) ≤
      |iteratedDeriv 2
        (OAI.Problem337.forwardDifference hs (fun y => Z * Real.log y)) x| ∧
    |iteratedDeriv 2
        (OAI.Problem337.forwardDifference hs (fun y => Z * Real.log y)) x| ≤
      hs.prod * ((hs.length + 1).factorial : ℝ) * |Z| / U ^ (hs.length + 2) := by
  obtain ⟨ξ, hxξ, hξ, he⟩ := OAI.Problem337.iteratedDeriv_forwardDifference_eq
    2 hs hhs (logPhase_base_smooth Z) (hU.trans_le hx)
  have hξ0 : 0 < ξ := hU.trans_le (hx.trans hxξ)
  have hp : 0 ≤ hs.prod := List.prod_nonneg (fun h hh => (hhs h hh).le)
  rw [he, abs_mul, abs_of_nonneg hp]
  rw [show hs.length + 2 = (hs.length + 1) + 1 by omega,
    logPhase_base_abs_iteratedDeriv (hs.length + 1) Z hξ0]
  constructor
  · have hpow := pow_le_pow_left₀ hξ0.le (hξ.trans hxV) (hs.length + 1 + 1)
    have hd := div_le_div_of_nonneg_left
      (by positivity : 0 ≤ ((hs.length + 1).factorial : ℝ) * |Z|)
      (pow_pos hξ0 _) hpow
    simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hd hp
  · have hpow := pow_le_pow_left₀ hU.le (hx.trans hxξ) (hs.length + 1 + 1)
    have hd := div_le_div_of_nonneg_left
      (by positivity : 0 ≤ ((hs.length + 1).factorial : ℝ) * |Z|)
      (pow_pos hU _) hpow
    simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hd hp

private lemma sum_Icc_int_toNat {M : Type*} [AddCommMonoid M] {L U : ℤ}
    (hL : 0 ≤ L) (hU : 0 ≤ U) (f : ℤ → M) :
    (∑ n ∈ Finset.Icc L U, f n) =
      ∑ n ∈ Finset.Icc L.toNat U.toNat, f (n : ℤ) := by
  classical
  apply Finset.sum_bij (fun n _ => n.toNat)
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨Int.toNat_le_toNat hn.1, Int.toNat_le_toNat hn.2⟩
  · intro n hn m hm hnm
    have hn0 : 0 ≤ n := hL.trans (Finset.mem_Icc.mp hn).1
    have hm0 : 0 ≤ m := hL.trans (Finset.mem_Icc.mp hm).1
    calc
      n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn0).symm
      _ = (m.toNat : ℤ) := congrArg (fun z : ℕ => (z : ℤ)) hnm
      _ = m := Int.toNat_of_nonneg hm0
  · intro n hn
    have hLcast : (L.toNat : ℤ) = L := Int.toNat_of_nonneg hL
    have hUcast : (U.toNat : ℤ) = U := Int.toNat_of_nonneg hU
    simp only [Finset.mem_Icc] at hn
    refine ⟨(n : ℤ), ?_, by simp⟩
    simp only [Finset.mem_Icc]
    constructor
    · rw [← hLcast]
      exact_mod_cast hn.1
    · rw [← hUcast]
      exact_mod_cast hn.2
  · intro n hn
    have hn0 : 0 ≤ n := hL.trans (Finset.mem_Icc.mp hn).1
    simp [Int.toNat_of_nonneg hn0]

private lemma forwardDifference_const_add_aux (hs : List ℝ) (c : ℝ)
    (f : ℝ → ℝ) :
    (hs = [] →
      OAI.Problem337.forwardDifference hs (fun x => c + f x) = fun x => c + f x) ∧
    (hs ≠ [] →
      OAI.Problem337.forwardDifference hs (fun x => c + f x) =
        OAI.Problem337.forwardDifference hs f) := by
  induction hs with
  | nil =>
    constructor
    · intro _
      rfl
    · intro h
      simp at h
  | cons h hs ih =>
    constructor
    · intro hnil
      simp at hnil
    · intro _
      by_cases htail : hs = []
      · subst hs
        funext x
        simp only [OAI.Problem337.forwardDifference]
        ring
      · have hIH := ih.2 htail
        funext x
        change OAI.Problem337.forwardDifference hs (fun y => c + f y) (x + h) -
            OAI.Problem337.forwardDifference hs (fun y => c + f y) x =
          OAI.Problem337.forwardDifference hs f (x + h) -
            OAI.Problem337.forwardDifference hs f x
        rw [hIH]

private lemma forwardDifference_const_add_translate {hs : List ℝ}
    (hne : hs ≠ []) (c b : ℝ) (f : ℝ → ℝ) :
    OAI.Problem337.forwardDifference hs (fun x => c + f (x + b)) =
      fun x => OAI.Problem337.forwardDifference hs f (x + b) := by
  have hc := (forwardDifference_const_add_aux hs c f).2 hne
  calc
    OAI.Problem337.forwardDifference hs (fun x => c + f (x + b)) =
        fun x => OAI.Problem337.forwardDifference hs (fun y => c + f y) (x + b) :=
      OAI.Problem337.forwardDifference_translate_input hs (fun y => c + f y) b
    _ = fun x => OAI.Problem337.forwardDifference hs f (x + b) := by rw [hc]

private lemma logPhase_decompose {q a : ℕ} {u y : ℝ}
    (hq : 1 ≤ q) (hy : 1 ≤ y) :
    logPhase q a u y =
      u / (2 * Real.pi) * Real.log (q : ℝ) +
        u / (2 * Real.pi) * Real.log (y + (a : ℝ) / q) := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have harg : 0 < y + (a : ℝ) / q := by positivity
  have hfactor : (q : ℝ) * y + a = (q : ℝ) * (y + (a : ℝ) / q) := by
    field_simp [ne_of_gt hqpos]
  rw [logPhase, hfactor, Real.log_mul (ne_of_gt hqpos) (ne_of_gt harg)]
  ring

private lemma forwardDifference_congr_on_Ici (hs : List ℝ) :
    ∀ (_hhs : ∀ h ∈ hs, 0 ≤ h) (lo : ℝ) (f g : ℝ → ℝ),
      (∀ y, lo ≤ y → f y = g y) →
      ∀ y, lo ≤ y →
        OAI.Problem337.forwardDifference hs f y =
          OAI.Problem337.forwardDifference hs g y := by
  induction hs with
  | nil =>
    intro _hhs lo f g hfg y hy
    exact hfg y hy
  | cons h hs ih =>
    intro _hhs lo f g hfg y hy
    have hh : 0 ≤ h := _hhs h (by simp)
    have htail : ∀ t ∈ hs, 0 ≤ t := fun t ht => _hhs t (by simp [ht])
    simp only [OAI.Problem337.forwardDifference]
    rw [ih htail lo f g hfg (y + h) (by linarith), ih htail lo f g hfg y hy]

private noncomputable def firstTestConstant
    (hD : Blueprint.DerivativeTests) : ℝ :=
  Classical.choose hD.1

private lemma firstTestConstant_spec (hD : Blueprint.DerivativeTests) :
    0 < firstTestConstant hD ∧
      ∀ (lo hi lam : ℝ) (j : ℤ) (f : ℝ → ℝ),
        lo ≤ hi → 0 < lam → lam ≤ 1 / 2 → DifferentiableOn ℝ f (Set.Icc lo hi) →
        (MonotoneOn (deriv f) (Set.Icc lo hi) ∨ AntitoneOn (deriv f) (Set.Icc lo hi)) →
        (∀ y ∈ Set.Icc lo hi, j + lam ≤ deriv f y ∧ deriv f y ≤ j + 1 - lam) →
        ‖∑ n ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, Blueprint.Analytic.e (f n)‖ ≤
          firstTestConstant hD / lam := by
  exact Classical.choose_spec hD.1

private noncomputable def secondTestConstant
    (hD : Blueprint.DerivativeTests) : ℝ :=
  Classical.choose (hD.2 9 (by norm_num))

private lemma secondTestConstant_spec (hD : Blueprint.DerivativeTests) :
    0 < secondTestConstant hD ∧
      ∀ (lo hi lam : ℝ) (f : ℝ → ℝ),
        lo ≤ hi → 0 < lam → ContDiffOn ℝ 2 f (Set.Icc lo hi) →
        (∀ y ∈ Set.Icc lo hi, lam ≤ |iteratedDeriv 2 f y| ∧
          |iteratedDeriv 2 f y| ≤ 9 * lam) →
        ‖∑ n ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, Blueprint.Analytic.e (f n)‖ ≤
          secondTestConstant hD *
            ((hi - lo + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹) := by
  exact Classical.choose_spec (hD.2 9 (by norm_num))

private noncomputable def secondTestConstantFor (hD : Blueprint.DerivativeTests)
    (C : ℝ) (hC : 1 ≤ C) : ℝ :=
  Classical.choose (hD.2 C hC)

private lemma secondTestConstantFor_spec (hD : Blueprint.DerivativeTests)
    (C : ℝ) (hC : 1 ≤ C) :
    0 < secondTestConstantFor hD C hC ∧
      ∀ (lo hi lam : ℝ) (f : ℝ → ℝ),
        lo ≤ hi → 0 < lam → ContDiffOn ℝ 2 f (Set.Icc lo hi) →
        (∀ y ∈ Set.Icc lo hi, lam ≤ |iteratedDeriv 2 f y| ∧
          |iteratedDeriv 2 f y| ≤ C * lam) →
        ‖∑ n ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, e (f n)‖ ≤
          secondTestConstantFor hD C hC *
            ((hi - lo + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹) := by
  exact Classical.choose_spec (hD.2 C hC)

private lemma analyticE_eq_differencingPhase (t : ℝ) :
    e t = OAI.Problem337.differencingPhase t := by
  unfold e OAI.Problem337.differencingPhase
  congr 1
  push_cast
  ring

private def logPhaseTerminalLambda (C N u : ℝ) (hs : List ℤ) : ℝ :=
  let hsR := hs.map (fun h : ℤ => (h : ℝ))
  hsR.prod * ((hsR.length + 1).factorial : ℝ) * |u / (2 * Real.pi)| /
    (C * N ^ (hsR.length + 2))

private def logPhaseBandAlpha (M : ℕ) : ℝ := 1 / (20 * (M : ℝ))

private def logPhaseBandH (N : ℝ) (k : ℕ) : ℕ :=
  ⌊N ^ (1 / (20 * (k : ℝ)))⌋₊

private def logPhaseBandR (N : ℝ) : ℕ := ⌊2 * N⌋₊ + 1

private noncomputable def logPhaseBandSecondConstant
    (hD : Blueprint.DerivativeTests) (M : ℕ) : ℝ :=
  secondTestConstantFor hD ((3 : ℝ) ^ M) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))

private noncomputable def logPhaseBandD
    (hD : Blueprint.DerivativeTests) (M : ℕ) : ℝ :=
  4 + logPhaseBandSecondConstant hD M *
    (Real.sqrt (M.factorial : ℝ) +
      Real.sqrt (8 * Real.pi * ((3 : ℝ) ^ M)))

private lemma logPhaseBandD_bounds (hD : Blueprint.DerivativeTests) (M : ℕ) :
    4 ≤ logPhaseBandD hD M ∧
    logPhaseBandSecondConstant hD M *
      (Real.sqrt (M.factorial : ℝ) + Real.sqrt (8 * Real.pi * ((3 : ℝ) ^ M))) ≤
        logPhaseBandD hD M := by
  have hK : 0 < logPhaseBandSecondConstant hD M :=
    (secondTestConstantFor_spec hD ((3 : ℝ) ^ M)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))).1
  have hS : 0 ≤ Real.sqrt (M.factorial : ℝ) +
      Real.sqrt (8 * Real.pi * ((3 : ℝ) ^ M)) := by positivity
  constructor <;> dsimp [logPhaseBandD] <;> linarith [mul_nonneg hK.le hS]

private lemma list_prod_lower_one (hs : List ℝ)
    (hhs : ∀ x ∈ hs, 1 ≤ x) : 1 ≤ hs.prod := by
  induction hs with
  | nil => simp
  | cons x hs ih =>
    have hx : 1 ≤ x := hhs x (by simp)
    have htail : ∀ y ∈ hs, 1 ≤ y := fun y hy => hhs y (by simp [hy])
    have hprod := ih htail
    simpa only [List.prod_cons, one_mul] using
      (mul_le_mul hx hprod (by norm_num) (by linarith [hx]))

private lemma list_prod_upper_pow (hs : List ℝ) (H : ℝ)
    (hH : 0 ≤ H) (hhs : ∀ x ∈ hs, 0 ≤ x ∧ x ≤ H) :
    hs.prod ≤ H ^ hs.length := by
  induction hs with
  | nil => simp
  | cons x hs ih =>
    have hx := hhs x (by simp)
    have htail : ∀ y ∈ hs, 0 ≤ y ∧ y ≤ H := fun y hy => hhs y (by simp [hy])
    have hprod0 : 0 ≤ hs.prod := List.prod_nonneg (fun y hy => (htail y hy).1)
    have hih := ih htail
    rw [List.prod_cons, List.length_cons, pow_succ]
    calc
      x * hs.prod ≤ H * hs.prod := mul_le_mul_of_nonneg_right hx.2 hprod0
      _ ≤ H * H ^ hs.length := mul_le_mul_of_nonneg_left hih hH
      _ = H ^ hs.length * H := by ring

private theorem logPhaseTerminalLambda_bounds
    {M k : ℕ} {N u : ℝ} {hs : List ℤ} {H : ℕ}
    (hk : 3 ≤ k) (hkM : k ≤ M) (hN : 1 ≤ N)
    (hlen : hs.length + 2 = k)
    (hHpow : (H : ℝ) ≤ N ^ (1 / (20 * (k : ℝ))))
    (hhs : ∀ h ∈ hs, 0 < h ∧ h < H)
    (hfreqLo : N ^ ((k : ℝ) - (19 : ℝ) / 10) ≤ |u|)
    (hfreqHi : |u| ≤ N ^ ((k : ℝ) - (1 : ℝ) / 10)) :
    (1 / (2 * Real.pi * ((3 : ℝ) ^ M)) * N ^ (-(19 : ℝ) / 10) ≤
      logPhaseTerminalLambda ((3 : ℝ) ^ M) N u hs) ∧
    logPhaseTerminalLambda ((3 : ℝ) ^ M) N u hs ≤
      (M.factorial : ℝ) * N ^ (-(1 : ℝ) / 20) := by
  let hsR : List ℝ := hs.map (fun h : ℤ => (h : ℝ))
  let Z : ℝ := u / (2 * Real.pi)
  let C : ℝ := (3 : ℝ) ^ M
  let β : ℝ := 1 / (20 * (k : ℝ))
  have hNpos : 0 < N := by linarith
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hMgeK : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hkM
  have hβpos : 0 < β := by dsimp [β]; positivity
  have hβK : β * (k : ℝ) = 1 / 20 := by
    dsimp [β]
    field_simp [ne_of_gt hkpos]
  have hlenNat : hsR.length + 2 = k := by simpa [hsR] using hlen
  have hlenR : (hsR.length : ℝ) + 2 = (k : ℝ) := by exact_mod_cast hlenNat
  have hlenLe : (hsR.length : ℝ) ≤ (k : ℝ) := by rw [← hlenR]; linarith
  have hβlen : β * (hsR.length : ℝ) ≤ 1 / 20 := by
    calc
      β * (hsR.length : ℝ) ≤ β * (k : ℝ) := mul_le_mul_of_nonneg_left hlenLe hβpos.le
      _ = 1 / 20 := hβK
  have hhsRpos : ∀ t ∈ hsR, 0 < t := by
    intro t ht
    rcases List.mem_map.mp ht with ⟨h, hh, rfl⟩
    exact_mod_cast (hhs h hh).1
  have hhsRone : ∀ t ∈ hsR, 1 ≤ t := by
    intro t ht
    rcases List.mem_map.mp ht with ⟨h, hh, rfl⟩
    have hpos : 0 < h := (hhs h hh).1
    have hInt : (1 : ℤ) ≤ h := by omega
    exact_mod_cast hInt
  have hhsRbounds : ∀ t ∈ hsR, 0 ≤ t ∧ t ≤ (H : ℝ) := by
    intro t ht
    rcases List.mem_map.mp ht with ⟨h, hh, rfl⟩
    have hIntLt : h < (H : ℤ) := by exact_mod_cast (hhs h hh).2
    have hInt : h ≤ (H : ℤ) := hIntLt.le
    have hReal : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hInt
    exact ⟨(hhsRpos _ (List.mem_map.mpr ⟨h, hh, rfl⟩)).le, hReal⟩
  have hprodLo : 1 ≤ hsR.prod := list_prod_lower_one hsR hhsRone
  have hprodHi : hsR.prod ≤ (H : ℝ) ^ hsR.length :=
    list_prod_upper_pow hsR (H : ℝ) (Nat.cast_nonneg _) hhsRbounds
  have hHpow' : (H : ℝ) ^ hsR.length ≤ N ^ ((1 : ℝ) / 20) := by
    calc
      (H : ℝ) ^ hsR.length ≤ (N ^ β) ^ hsR.length :=
        pow_le_pow_left₀ (by positivity) hHpow _
      _ = N ^ (β * (hsR.length : ℝ)) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul hNpos.le β (hsR.length : ℝ)).symm
      _ ≤ N ^ ((1 : ℝ) / 20) := Real.rpow_le_rpow_of_exponent_le hN hβlen
  have hprodScale : hsR.prod ≤ N ^ ((1 : ℝ) / 20) := hprodHi.trans hHpow'
  have hfactLo : 1 ≤ ((hsR.length + 1).factorial : ℝ) := by
    have hNat : 1 ≤ (hsR.length + 1).factorial := by
      have hp : 0 < (hsR.length + 1).factorial := Nat.factorial_pos _
      omega
    exact_mod_cast hNat
  have hlenFact : hsR.length + 1 ≤ M := by omega
  have hfactHi : ((hsR.length + 1).factorial : ℝ) ≤ (M.factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_le hlenFact)
  have hu0 : 0 ≤ |u| := abs_nonneg u
  have hZeq : |Z| = |u| / (2 * Real.pi) := by
    dsimp [Z]
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hpiDen : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hZupper : |Z| ≤ |u| := by
    rw [hZeq]
    exact div_le_self hu0 hpiDen
  have hZlower : N ^ ((k : ℝ) - (19 : ℝ) / 10) / (2 * Real.pi) ≤ |Z| := by
    rw [hZeq]
    exact div_le_div_of_nonneg_right hfreqLo (by positivity)
  have hnumLo :
      N ^ ((k : ℝ) - (19 : ℝ) / 10) / (2 * Real.pi) ≤
        hsR.prod * ((hsR.length + 1).factorial : ℝ) * |Z| := by
    have hpf : 1 ≤ hsR.prod * ((hsR.length + 1).factorial : ℝ) := by
      calc
        1 ≤ hsR.prod := hprodLo
        _ = hsR.prod * 1 := by ring
        _ ≤ hsR.prod * ((hsR.length + 1).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hfactLo (by positivity)
    calc
      _ ≤ |Z| := hZlower
      _ = 1 * |Z| := by ring
      _ ≤ (hsR.prod * ((hsR.length + 1).factorial : ℝ)) * |Z| :=
        mul_le_mul_of_nonneg_right hpf (abs_nonneg Z)
      _ = _ := by ring
  have hNumUpper :
      hsR.prod * ((hsR.length + 1).factorial : ℝ) * |Z| ≤
        N ^ ((1 : ℝ) / 20) * (M.factorial : ℝ) * |u| := by
    have hpf : hsR.prod * ((hsR.length + 1).factorial : ℝ) ≤
        N ^ ((1 : ℝ) / 20) * (M.factorial : ℝ) := by
      calc
        hsR.prod * ((hsR.length + 1).factorial : ℝ) ≤
            N ^ ((1 : ℝ) / 20) * ((hsR.length + 1).factorial : ℝ) :=
          mul_le_mul_of_nonneg_right hprodScale (by positivity)
        _ ≤ N ^ ((1 : ℝ) / 20) * (M.factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hfactHi (by positivity)
    calc
      _ = (hsR.prod * ((hsR.length + 1).factorial : ℝ)) * |Z| := by ring
      _ ≤ (N ^ ((1 : ℝ) / 20) * (M.factorial : ℝ)) * |Z| :=
        mul_le_mul_of_nonneg_right hpf (abs_nonneg Z)
      _ ≤ (N ^ ((1 : ℝ) / 20) * (M.factorial : ℝ)) * |u| :=
        mul_le_mul_of_nonneg_left hZupper (by positivity)
      _ = _ := by ring
  have hC : 1 ≤ C := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hCpos : 0 < C := by linarith
  have hlenCast : (hsR.length : ℝ) + 2 = (k : ℝ) := hlenR
  have hlenCastNat : ((hsR.length + 2 : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast hlenNat
  have hlamEq : logPhaseTerminalLambda C N u hs =
      hsR.prod * ((hsR.length + 1).factorial : ℝ) * |Z| /
        (C * N ^ (hsR.length + 2)) := by
    simp [logPhaseTerminalLambda, hsR, Z]
  have hNden : 0 < N ^ (hsR.length + 2) := pow_pos hNpos _
  have hCden : 0 < C * N ^ (hsR.length + 2) := mul_pos hCpos hNden
  have hdenLo : N ^ (hsR.length + 2) ≤ C * N ^ (hsR.length + 2) := by
    calc
      N ^ (hsR.length + 2) = 1 * N ^ (hsR.length + 2) := by ring
      _ ≤ C * N ^ (hsR.length + 2) :=
        mul_le_mul_of_nonneg_right hC (le_of_lt hNden)
  have hpowLo : N ^ ((k : ℝ) - (19 : ℝ) / 10) /
      N ^ (hsR.length + 2) = N ^ (-(19 : ℝ) / 10) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hNpos, hlenCastNat]
    congr 1
    ring
  have hratioLo :
      (N ^ ((k : ℝ) - (19 : ℝ) / 10) / (2 * Real.pi)) /
          (C * N ^ (hsR.length + 2)) =
        (1 / (2 * Real.pi * C)) * N ^ (-(19 : ℝ) / 10) := by
    calc
      _ = (N ^ ((k : ℝ) - (19 : ℝ) / 10) /
            N ^ (hsR.length + 2)) / (2 * Real.pi * C) := by
        field_simp [ne_of_gt hCpos, Real.pi_ne_zero, ne_of_gt hNpos]
      _ = _ := by rw [hpowLo]; ring
  have hratioHi :
      (N ^ ((1 : ℝ) / 20) * (M.factorial : ℝ) *
        N ^ ((k : ℝ) - (1 : ℝ) / 10)) /
          N ^ (hsR.length + 2) =
        (M.factorial : ℝ) * N ^ (-(1 : ℝ) / 20) := by
    have hpow : N ^ ((1 : ℝ) / 20) * N ^ ((k : ℝ) - (1 : ℝ) / 10) /
        N ^ (hsR.length + 2) = N ^ (-(1 : ℝ) / 20) := by
      rw [← Real.rpow_add hNpos]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_sub hNpos]
      rw [hlenCastNat]
      congr 1
      ring
    calc
      _ = (M.factorial : ℝ) *
            (N ^ ((1 : ℝ) / 20) * N ^ ((k : ℝ) - (1 : ℝ) / 10) /
              N ^ (hsR.length + 2)) := by ring
      _ = _ := by rw [hpow]
  constructor
  · rw [hlamEq]
    have hdiv := div_le_div_of_nonneg_right hnumLo (le_of_lt hCden)
    calc
      _ = (1 / (2 * Real.pi * C)) * N ^ (-(19 : ℝ) / 10) := by rfl
      _ = (N ^ ((k : ℝ) - (19 : ℝ) / 10) / (2 * Real.pi)) /
          (C * N ^ (hsR.length + 2)) := hratioLo.symm
      _ ≤ hsR.prod * ((hsR.length + 1).factorial : ℝ) * |Z| /
          (C * N ^ (hsR.length + 2)) := hdiv
  · rw [hlamEq]
    have hdiv := div_le_div_of_nonneg_right hNumUpper (le_of_lt hNden)
    have hnumNonneg : 0 ≤ hsR.prod * ((hsR.length + 1).factorial : ℝ) * |Z| := by
      positivity
    calc
      _ ≤ hsR.prod * ((hsR.length + 1).factorial : ℝ) * |Z| /
          N ^ (hsR.length + 2) := by
        exact div_le_div_of_nonneg_left hnumNonneg (pow_pos hNpos _) hdenLo
      _ ≤ (N ^ ((1 : ℝ) / 20) * (M.factorial : ℝ) * |u|) /
          N ^ (hsR.length + 2) := hdiv
      _ ≤ (N ^ ((1 : ℝ) / 20) * (M.factorial : ℝ) *
            N ^ ((k : ℝ) - (1 : ℝ) / 10)) /
          N ^ (hsR.length + 2) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfreqHi (by positivity)) (by positivity)
      _ = (M.factorial : ℝ) * N ^ (-(1 : ℝ) / 20) := hratioHi

private theorem logPhaseBand_scales {M k : ℕ} {N D : ℝ}
    (hM : 3 ≤ M) (hk : 3 ≤ k) (hkM : k ≤ M)
    (hN : 1 ≤ N) (hD4 : 4 ≤ D)
    (hDlarge : D ≤ N ^ (logPhaseBandAlpha M)) :
    1 ≤ logPhaseBandH N k ∧
    logPhaseBandH N k ≤ logPhaseBandR N ∧
    2 * N ≤ (logPhaseBandR N : ℝ) ∧
    (logPhaseBandR N : ℝ) ≤ 3 * N ∧
    2 / (logPhaseBandH N k : ℝ) ≤ D * N ^ (-logPhaseBandAlpha M) := by
  let α : ℝ := logPhaseBandAlpha M
  let β : ℝ := 1 / (20 * (k : ℝ))
  let y : ℝ := N ^ β
  let H : ℕ := logPhaseBandH N k
  let R : ℕ := logPhaseBandR N
  have hNpos : 0 < N := by linarith
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hαpos : 0 < α := by dsimp [α, logPhaseBandAlpha]; positivity
  have hβpos : 0 < β := by dsimp [β]; positivity
  have hαβ : α ≤ β := by
    dsimp [α, logPhaseBandAlpha, β]
    rw [div_le_div_iff₀ (by positivity : 0 < 20 * (M : ℝ))
      (by positivity : 0 < 20 * (k : ℝ))]
    have hkMreal : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hkM
    nlinarith [hkMreal]
  have hβ1 : β ≤ 1 := by
    dsimp [β]
    rw [div_le_one (by positivity : 0 < 20 * (k : ℝ))]
    have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [hkR]
  have hNα : 4 ≤ N ^ α := hD4.trans hDlarge
  have hNβ : N ^ α ≤ y := by
    dsimp [y]
    exact Real.rpow_le_rpow_of_exponent_le hN hαβ
  have hy4 : 4 ≤ y := hNα.trans hNβ
  have hypos : 0 < y := Real.rpow_pos_of_pos hNpos _
  have hHfloor : y < (H : ℝ) + 1 := by
    dsimp [H, logPhaseBandH, y]
    simpa only [Nat.cast_succ] using
      (Nat.floor_lt (le_of_lt (Real.rpow_pos_of_pos hNpos _))).1
        (Nat.lt_succ_self _)
  have hHhalf : y / 2 ≤ (H : ℝ) := by nlinarith
  have hHtwo : (2 : ℝ) ≤ (H : ℝ) := by nlinarith
  have hHone : 1 ≤ H := by exact_mod_cast (show (1 : ℝ) ≤ (H : ℝ) by linarith)
  have hHleN : (H : ℝ) ≤ N := by
    have hf := Nat.floor_le (show 0 ≤ y by positivity)
    have hyN : y ≤ N := by
      dsimp [y]
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN hβ1
    dsimp [H, logPhaseBandH] at hf ⊢
    exact hf.trans hyN
  have hRfloor : 2 * N < (⌊2 * N⌋₊ : ℝ) + 1 := by
    simpa only [Nat.cast_succ] using
      (Nat.floor_lt (by positivity : 0 ≤ 2 * N)).1 (Nat.lt_succ_self _)
  have hRlo : 2 * N ≤ (R : ℝ) := by
    dsimp [R, logPhaseBandR]
    rw [Nat.cast_add, Nat.cast_one]
    exact hRfloor.le
  have hRhi : (R : ℝ) ≤ 3 * N := by
    have hf := Nat.floor_le (by positivity : 0 ≤ 2 * N)
    calc
      (R : ℝ) = (⌊2 * N⌋₊ : ℝ) + 1 := by simp [R, logPhaseBandR]
      _ ≤ 2 * N + 1 := by nlinarith [hf]
      _ ≤ 3 * N := by linarith [hN]
  have hHR : H ≤ R := by
    have hNR : N ≤ (R : ℝ) := by linarith [hRlo, hN]
    have hHleR : (H : ℝ) ≤ (R : ℝ) := hHleN.trans hNR
    exact_mod_cast hHleR
  have hHpos : 0 < (H : ℝ) := by linarith
  have hInv : 2 / (H : ℝ) ≤ 4 / y := by
    rw [div_le_div_iff₀ hHpos hypos]
    nlinarith [hHhalf]
  have hNneg : N ^ (-β) = y⁻¹ := by
    dsimp [y]
    rw [Real.rpow_neg hNpos.le]
  have hβneg : -β ≤ -α := neg_le_neg hαβ
  have hpowNeg : N ^ (-β) ≤ N ^ (-α) :=
    Real.rpow_le_rpow_of_exponent_le hN hβneg
  have hHeps : 2 / (H : ℝ) ≤ D * N ^ (-α) := by
    calc
      _ ≤ 4 / y := hInv
      _ = 4 * N ^ (-β) := by rw [div_eq_mul_inv, ← hNneg]
      _ ≤ 4 * N ^ (-α) := mul_le_mul_of_nonneg_left hpowNeg (by norm_num)
      _ ≤ D * N ^ (-α) := mul_le_mul_of_nonneg_right hD4
        (Real.rpow_nonneg (by linarith) _)
  refine ⟨hHone, hHR, hRlo, hRhi, ?_⟩
  simpa [H, R, α, β] using hHeps

private theorem logPhase_terminal_secondDerivativeTest
    (hD : Blueprint.DerivativeTests) {C N : ℝ} {R : ℕ}
    {q a : ℕ} {u : ℝ} {L U T : ℤ} {hs : List ℤ}
    (hC : 1 ≤ C) (hCpow : (3 : ℝ) ^ (hs.length + 2) ≤ C)
    (hN : 1 ≤ N) (hR : 2 * N ≤ (R : ℝ))
    (hLT : L ≤ T)
    (hNLo : N ≤ (L : ℝ)) (hUhi : (U : ℝ) ≤ 2 * N)
    (hTdef : T = U - hs.sum)
    (hq : 1 ≤ q) (ha : a < q) (hu : 1 ≤ |u|)
    (hne : hs ≠ []) (hhs : ∀ h ∈ hs, 0 < h) :
    ‖∑ n ∈ Finset.Icc L T,
      OAI.Problem337.differencingPhase
        (OAI.Problem337.forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (logPhase q a u) (n : ℝ))‖ / (R : ℝ) ≤
      secondTestConstantFor hD C hC *
        (Real.sqrt (logPhaseTerminalLambda C N u hs) +
          (Real.sqrt (logPhaseTerminalLambda C N u hs))⁻¹ / (R : ℝ)) := by
  let hsR : List ℝ := hs.map (fun h : ℤ => (h : ℝ))
  let Z : ℝ := u / (2 * Real.pi)
  let b : ℝ := (a : ℝ) / (q : ℝ)
  let base : ℝ → ℝ := fun y => Z * Real.log y
  let terminal : ℝ → ℝ := fun y =>
    OAI.Problem337.forwardDifference hsR base (y + b)
  let A : ℝ := (L : ℝ)
  let B : ℝ := (T : ℝ)
  let lam : ℝ := logPhaseTerminalLambda C N u hs
  have hNpos : 0 < N := by linarith
  have hRpos : 0 < (R : ℝ) := by linarith
  have hCpos : 0 < C := by linarith
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have haR : (a : ℝ) < (q : ℝ) := by exact_mod_cast ha
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b < 1 := by
    dsimp [b]
    rw [div_lt_one hqpos]
    exact haR
  have hu0 : 0 < |u| := lt_of_lt_of_le (by norm_num) hu
  have hZpos : 0 < |Z| := by
    dsimp [Z]
    exact abs_pos.mpr (div_ne_zero (abs_pos.mp hu0) (ne_of_gt (by positivity)))
  have hAeq : A = (L : ℝ) := rfl
  have hBeq : B = (T : ℝ) := rfl
  have hAN : N ≤ A := by rw [hAeq]; exact hNLo
  have hAB : A ≤ B := by rw [hAeq, hBeq]; exact_mod_cast hLT
  have hApos : 0 < A := hNpos.trans_le hAN
  have hsumNonneg : 0 ≤ hs.sum := List.sum_nonneg (fun h hh => (hhs h hh).le)
  have hTleU : T ≤ U := by rw [hTdef]; omega
  have hTleUReal : (T : ℝ) ≤ (U : ℝ) := by exact_mod_cast hTleU
  have hsumR : hsR.sum = (hs.sum : ℝ) := by simp [hsR]
  have hTsumR : B + hsR.sum = (U : ℝ) := by
    rw [hBeq, hsumR, hTdef]
    simp only [Int.cast_sub]
    ring
  have hwidth : B - A + 1 ≤ (R : ℝ) := by
    calc
      B - A + 1 = (T : ℝ) - (L : ℝ) + 1 := by rw [hBeq, hAeq]
      _ ≤ (U : ℝ) - (L : ℝ) + 1 := by linarith
      _ ≤ N + 1 := by linarith [hUhi, hNLo]
      _ ≤ 2 * N := by linarith [hN]
      _ ≤ (R : ℝ) := hR
  have htermDomain : Set.Icc A B ⊆ Set.Ioi 0 := by
    intro y hy
    exact lt_of_lt_of_le (lt_of_lt_of_le hNpos hAN) hy.1
  have hhsRpos : ∀ t ∈ hsR, 0 < t := by
    intro t ht
    rcases List.mem_map.mp ht with ⟨h, hh, rfl⟩
    exact_mod_cast hhs h hh
  have hhsRnonneg : ∀ t ∈ hsR, 0 ≤ t := fun t ht => (hhsRpos t ht).le
  have hhsRne : hsR ≠ [] := by
    intro hnil
    have hnil' : List.map (fun h : ℤ => (h : ℝ)) hs = [] := by
      simpa [hsR] using hnil
    exact hne (List.map_eq_nil_iff.mp hnil')
  have hhsRlen : hsR.length = hs.length := by simp [hsR]
  have hbaseSmooth := OAI.Problem337.forwardDifference_contDiffOn
    hsR hhsRnonneg (logPhase_base_smooth Z)
  have hbaseSmooth2 : ContDiffOn ℝ 2
      (OAI.Problem337.forwardDifference hsR base) (Set.Ioi 0) := by
    exact hbaseSmooth.of_le (by norm_num)
  have hshiftSmooth : ContDiffOn ℝ 2 (fun y : ℝ => y + b) (Set.Ioi 0) := by
    fun_prop
  have hshiftMaps : Set.MapsTo (fun y : ℝ => y + b) (Set.Ioi 0) (Set.Ioi 0) := by
    intro y hy
    change 0 < y + b
    exact lt_of_lt_of_le hy (le_add_of_nonneg_right hb0)
  have hterminalSmoothIoi : ContDiffOn ℝ 2 terminal (Set.Ioi 0) := by
    dsimp [terminal, base]
    simpa only [Function.comp_def] using hbaseSmooth2.comp hshiftSmooth hshiftMaps
  have hterminalSmooth : ContDiffOn ℝ 2 terminal (Set.Icc A B) :=
    hterminalSmoothIoi.mono htermDomain
  have htermTranslate (y : ℝ) :
      iteratedDeriv 2 terminal y =
        iteratedDeriv 2 (OAI.Problem337.forwardDifference hsR base) (y + b) := by
    simpa [terminal] using
      congrFun (iteratedDeriv_comp_add_const 2
        (OAI.Problem337.forwardDifference hsR base) b) y
  have hnumPos : 0 < hsR.prod * ((hsR.length + 1).factorial : ℝ) * |Z| := by
    have hp : 0 < hsR.prod := List.prod_pos hhsRpos
    positivity
  have hlenRatio : (3 : ℝ) ^ (hsR.length + 2) ≤ C := by
    simpa [hhsRlen] using hCpow
  have hlamEq : lam =
      (hsR.prod * ((hsR.length + 1).factorial : ℝ) * |Z|) /
        (C * N ^ (hsR.length + 2)) := by
    simp [lam, logPhaseTerminalLambda, hsR, hhsRlen, Z]
  have hlamPos : 0 < lam := by
    rw [hlamEq]
    exact div_pos hnumPos (mul_pos hCpos (pow_pos hNpos _))
  have hden : (3 * N) ^ (hsR.length + 2) ≤ C * N ^ (hsR.length + 2) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hlenRatio (by positivity)
  have hlamLow : lam ≤
      (hsR.prod * ((hsR.length + 1).factorial : ℝ) * |Z|) /
        (3 * N) ^ (hsR.length + 2) := by
    rw [hlamEq]
    exact div_le_div_of_nonneg_left hnumPos.le (by positivity) hden
  have hupperEq : C * lam =
      (hsR.prod * ((hsR.length + 1).factorial : ℝ) * |Z|) /
        N ^ (hsR.length + 2) := by
    rw [hlamEq]
    field_simp [ne_of_gt hCpos, ne_of_gt hNpos]
  have hdecomp (y : ℝ) (hy : N ≤ y) :
      logPhase q a u y = Z * Real.log (q : ℝ) + base (y + b) := by
    have hy1 : 1 ≤ y := le_trans hN hy
    simpa [Z, b, base] using logPhase_decompose hq hy1
  have hphaseFD (y : ℝ) (hy : N ≤ y) :
      OAI.Problem337.forwardDifference hsR (logPhase q a u) y = terminal y := by
    calc
      OAI.Problem337.forwardDifference hsR (logPhase q a u) y =
          OAI.Problem337.forwardDifference hsR
            (fun z => Z * Real.log (q : ℝ) + base (z + b)) y :=
        forwardDifference_congr_on_Ici hsR hhsRnonneg N
          (logPhase q a u) (fun z => Z * Real.log (q : ℝ) + base (z + b))
          hdecomp y hy
      _ = terminal y := by
        exact congrFun (forwardDifference_const_add_translate hhsRne
          (Z * Real.log (q : ℝ)) b base) y
  have htermDeriv (y : ℝ) (hy : y ∈ Set.Icc A B) :
      lam ≤ |iteratedDeriv 2 terminal y| ∧
        |iteratedDeriv 2 terminal y| ≤ C * lam := by
    have hyN : N ≤ y := hAN.trans hy.1
    have hybN : N ≤ y + b := by linarith
    have hyend : y + b + hsR.sum ≤ 3 * N := by
      calc
        y + b + hsR.sum ≤ B + b + hsR.sum := by linarith [hy.2]
        _ = (U : ℝ) + b := by
          rw [show B + b + hsR.sum = (B + hsR.sum) + b by ring, hTsumR]
        _ ≤ 2 * N + 1 := by linarith [hUhi, hb1]
        _ ≤ 3 * N := by linarith [hN]
    have hraw := logPhase_forwardDifference_second_bounds hsR hhsRpos Z
      hNpos hybN hyend
    rw [htermTranslate y]
    constructor
    · exact hlamLow.trans hraw.1
    · exact hraw.2.trans_eq hupperEq.symm
  have hsumEq :
      (∑ n ∈ Finset.Icc L T,
        OAI.Problem337.differencingPhase
          (OAI.Problem337.forwardDifference hsR (logPhase q a u) (n : ℝ))) =
        ∑ n ∈ Finset.Icc L T, e (terminal (n : ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [← analyticE_eq_differencingPhase]
    congr 1
    apply hphaseFD
    calc
      N ≤ (L : ℝ) := hNLo
      _ ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rcases secondTestConstantFor_spec hD C hC with ⟨hK, htest⟩
  have htestRaw := htest A B lam terminal hAB hlamPos hterminalSmooth htermDeriv
  have htestSum :
      ‖∑ n ∈ Finset.Icc L T, e (terminal (n : ℝ))‖ ≤
        secondTestConstantFor hD C hC *
          ((B - A + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹) := by
    simpa [A, B] using htestRaw
  have hsumRaw :
      ‖∑ n ∈ Finset.Icc L T,
        OAI.Problem337.differencingPhase
          (OAI.Problem337.forwardDifference hsR (logPhase q a u) (n : ℝ))‖ ≤
        secondTestConstantFor hD C hC *
          ((B - A + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹) := by
    rw [hsumEq]
    exact htestSum
  have hroot : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  have hrootInv : 0 ≤ (Real.sqrt lam)⁻¹ := inv_nonneg.mpr hroot
  have hwidthRatio : (B - A + 1) / (R : ℝ) ≤ 1 :=
    (div_le_one hRpos).2 hwidth
  have hinner :
      (B - A + 1) / (R : ℝ) * Real.sqrt lam +
          (Real.sqrt lam)⁻¹ / (R : ℝ) ≤
        Real.sqrt lam + (Real.sqrt lam)⁻¹ / (R : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hwidthRatio hroot
    have hmul' :
        (B - A + 1) / (R : ℝ) * Real.sqrt lam ≤ Real.sqrt lam := by
      calc
        _ ≤ 1 * Real.sqrt lam := hmul
        _ = Real.sqrt lam := by ring
    exact add_le_add hmul' le_rfl
  calc
    _ ≤ (secondTestConstantFor hD C hC *
          ((B - A + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹)) / (R : ℝ) :=
      div_le_div_of_nonneg_right hsumRaw (le_of_lt hRpos)
    _ = secondTestConstantFor hD C hC *
          ((B - A + 1) / (R : ℝ) * Real.sqrt lam +
            (Real.sqrt lam)⁻¹ / (R : ℝ)) := by
      field_simp [ne_of_gt hRpos]
    _ ≤ secondTestConstantFor hD C hC *
          (Real.sqrt lam + (Real.sqrt lam)⁻¹ / (R : ℝ)) :=
      mul_le_mul_of_nonneg_left hinner hK.le

private theorem logPhase_terminal_epsilon
    (hD : Blueprint.DerivativeTests) {M k : ℕ} {N : ℝ}
    {q a : ℕ} {u : ℝ} {L U T : ℤ} {hs : List ℤ}
    (hM : 3 ≤ M) (hk : 3 ≤ k) (hkM : k ≤ M) (hN : 1 ≤ N)
    (hDlarge : logPhaseBandD hD M ≤ N ^ (logPhaseBandAlpha M))
    (hLT : L ≤ T) (hNLo : N ≤ (L : ℝ)) (hUhi : (U : ℝ) ≤ 2 * N)
    (hTdef : T = U - hs.sum) (hq : 1 ≤ q) (ha : a < q)
    (hu : 1 ≤ |u|) (hlen : hs.length + 2 = k)
    (hfreqLo : N ^ ((k : ℝ) - (19 : ℝ) / 10) ≤ |u|)
    (hfreqHi : |u| ≤ N ^ ((k : ℝ) - (1 : ℝ) / 10))
    (hhs : ∀ h ∈ hs, 0 < h ∧ h < logPhaseBandH N k) :
    ‖∑ n ∈ Finset.Icc L T,
      OAI.Problem337.differencingPhase
        (OAI.Problem337.forwardDifference
          (hs.map (fun h : ℤ => (h : ℝ))) (logPhase q a u) (n : ℝ))‖ /
      (logPhaseBandR N : ℝ) ≤
        logPhaseBandD hD M * N ^ (-logPhaseBandAlpha M) := by
  let H : ℕ := logPhaseBandH N k
  let R : ℕ := logPhaseBandR N
  let C : ℝ := (3 : ℝ) ^ M
  let D : ℝ := logPhaseBandD hD M
  let α : ℝ := logPhaseBandAlpha M
  have hDspec := logPhaseBandD_bounds hD M
  have hscales := logPhaseBand_scales hM hk hkM hN hDspec.1 hDlarge
  have hHone : 1 ≤ H := by simpa [H] using hscales.1
  have hHR : H ≤ R := by simpa [H, R] using hscales.2.1
  have hRlo : 2 * N ≤ (R : ℝ) := by simpa [R] using hscales.2.2.1
  have hRhi : (R : ℝ) ≤ 3 * N := by simpa [R] using hscales.2.2.2.1
  have hHε : 2 / (H : ℝ) ≤ D * N ^ (-α) := by
    simpa [H, D, α] using hscales.2.2.2.2
  have hNpos : 0 < N := by linarith
  have hRpos : 0 < (R : ℝ) := by linarith
  have hC : 1 ≤ C := by dsimp [C]; exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hCpos : 0 < C := by linarith
  have hCpow : (3 : ℝ) ^ (hs.length + 2) ≤ C := by
    have hlenM : hs.length + 2 ≤ M := by omega
    dsimp [C]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (3 : ℝ)) hlenM
  have hHpow : (H : ℝ) ≤ N ^ (1 / (20 * (k : ℝ))) := by
    dsimp [H, logPhaseBandH]
    exact Nat.floor_le (by positivity)
  have hLamBounds := logPhaseTerminalLambda_bounds hk hkM hN hlen hHpow
    (by simpa [H] using hhs) hfreqLo hfreqHi
  let lam : ℝ := logPhaseTerminalLambda C N u hs
  have hlamPos : 0 < lam := by
    have hcoeff : 0 < 1 / (2 * Real.pi * C) := by positivity
    have hp : 0 < N ^ (-(19 : ℝ) / 10) := Real.rpow_pos_of_pos hNpos _
    exact lt_of_lt_of_le (mul_pos hcoeff hp) (by simpa [lam, C] using hLamBounds.1)
  have hcWeak : 1 / (8 * Real.pi * C) ≤ 1 / (2 * Real.pi * C) := by
    have hden : 2 * Real.pi * C ≤ 8 * Real.pi * C := by
      have hp : 2 * Real.pi ≤ 8 * Real.pi := by nlinarith [Real.pi_gt_three]
      exact mul_le_mul_of_nonneg_right hp hCpos.le
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
  have hLamWeak :
      (1 / (8 * Real.pi * C)) * N ^ (-(19 : ℝ) / 10) ≤ lam := by
    calc
      _ ≤ (1 / (2 * Real.pi * C)) * N ^ (-(19 : ℝ) / 10) :=
        mul_le_mul_of_nonneg_right hcWeak
          (Real.rpow_nonneg (le_of_lt hNpos) _)
      _ ≤ lam := by simpa [lam, C] using hLamBounds.1
  have hpowHalf : (N ^ (-(1 : ℝ) / 40)) ^ 2 = N ^ (-(1 : ℝ) / 20) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  have hrootUpper : Real.sqrt lam ≤
      Real.sqrt (M.factorial : ℝ) * N ^ (-(1 : ℝ) / 40) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hpowHalf]
      simpa [lam, C] using hLamBounds.2
  let c : ℝ := 1 / (8 * Real.pi * C)
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hsqrtN : Real.sqrt (N ^ (-(19 : ℝ) / 10)) =
      N ^ (-(19 : ℝ) / 20) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
    congr 1
    norm_num
  have hsqrtLowEq :
      Real.sqrt (c * N ^ (-(19 : ℝ) / 10)) =
        Real.sqrt c * N ^ (-(19 : ℝ) / 20) := by
    rw [Real.sqrt_mul (le_of_lt hcpos), hsqrtN]
  have hrootLower : Real.sqrt c * N ^ (-(19 : ℝ) / 20) ≤ Real.sqrt lam := by
    rw [← hsqrtLowEq]
    exact Real.sqrt_le_sqrt (by simpa [c] using hLamWeak)
  have hpowMix : N * N ^ (-(19 : ℝ) / 20) = N ^ (1 / 20 : ℝ) := by
    calc
      _ = N ^ (1 : ℝ) * N ^ (-(19 : ℝ) / 20) := by rw [Real.rpow_one]
      _ = N ^ (1 + (-(19 : ℝ) / 20)) := by rw [← Real.rpow_add hNpos]
      _ = _ := by congr 1; norm_num
  have hNR : N ≤ (R : ℝ) := by linarith [hRlo]
  have hrootProduct :
      Real.sqrt c * N ^ (1 / 20 : ℝ) ≤ (R : ℝ) * Real.sqrt lam := by
    calc
      Real.sqrt c * N ^ (1 / 20 : ℝ) =
          N * (Real.sqrt c * N ^ (-(19 : ℝ) / 20)) := by rw [← hpowMix]; ring
      _ ≤ (R : ℝ) * (Real.sqrt c * N ^ (-(19 : ℝ) / 20)) :=
        mul_le_mul_of_nonneg_right hNR (by positivity)
      _ ≤ (R : ℝ) * Real.sqrt lam :=
        mul_le_mul_of_nonneg_left hrootLower (by positivity)
  have hsqrtInvC : (Real.sqrt c)⁻¹ = Real.sqrt (8 * Real.pi * C) := by
    have h := show
        (Real.sqrt (1 / (8 * Real.pi * C)))⁻¹ = Real.sqrt (8 * Real.pi * C) by
      rw [one_div, Real.sqrt_inv]
      simp
    simpa [c] using h
  have hInvEq :
      (Real.sqrt c * N ^ (1 / 20 : ℝ))⁻¹ =
        Real.sqrt (8 * Real.pi * C) * N ^ (-(1 : ℝ) / 20) := by
    rw [mul_inv, hsqrtInvC, ← Real.rpow_neg hNpos.le]
    congr 1
    norm_num
  have hprodPos : 0 < (R : ℝ) * Real.sqrt lam := by positivity
  have hlowPos : 0 < Real.sqrt c * N ^ (1 / 20 : ℝ) := by positivity
  have hInvOrder :
      ((R : ℝ) * Real.sqrt lam)⁻¹ ≤
        (Real.sqrt c * N ^ (1 / 20 : ℝ))⁻¹ :=
    (inv_le_inv₀ hprodPos hlowPos).2 hrootProduct
  have hInvBound :
      (Real.sqrt lam)⁻¹ / (R : ℝ) ≤
        Real.sqrt (8 * Real.pi * C) * N ^ (-(1 : ℝ) / 20) := by
    have hdiv : (Real.sqrt lam)⁻¹ / (R : ℝ) =
        ((R : ℝ) * Real.sqrt lam)⁻¹ := by
      field_simp [ne_of_gt hRpos, ne_of_gt (Real.sqrt_pos.mpr hlamPos)]
    rw [hdiv]
    exact hInvOrder.trans_eq hInvEq
  have hne : hs ≠ [] := by
    intro he
    simp [he] at hlen
    omega
  have hKeq : secondTestConstantFor hD C hC =
      logPhaseBandSecondConstant hD M := by rfl
  have hKpos : 0 ≤ logPhaseBandSecondConstant hD M := by
    have hK := (secondTestConstantFor_spec hD ((3 : ℝ) ^ M)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))).1
    simpa [logPhaseBandSecondConstant] using hK.le
  have htermTest := logPhase_terminal_secondDerivativeTest
    (hD := hD) (C := C) (N := N) (R := R) (q := q) (a := a) (u := u)
    (L := L) (U := U) (T := T) (hs := hs)
    hC hCpow hN hRlo hLT hNLo hUhi hTdef hq ha hu
    hne
    (fun h hh => (hhs h hh).1)
  have halpha40 : logPhaseBandAlpha M ≤ (1 : ℝ) / 40 := by
    have hαle60 : logPhaseBandAlpha M ≤ (1 : ℝ) / 60 := by
      dsimp [logPhaseBandAlpha]
      rw [div_le_div_iff₀ (by positivity : 0 < 20 * (M : ℝ)) (by norm_num : (0 : ℝ) < 60)]
      have hMreal : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith
    linarith
  have hpow40 : N ^ (-(1 : ℝ) / 40) ≤ N ^ (-logPhaseBandAlpha M) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith [halpha40])
  have hcoeff :
      logPhaseBandSecondConstant hD M *
          (Real.sqrt (M.factorial : ℝ) + Real.sqrt (8 * Real.pi * C)) ≤ D := by
    simpa [D, C] using (logPhaseBandD_bounds hD M).2
  have hDnonneg : 0 ≤ D := by dsimp [D]; linarith [hDspec.1]
  have hterms :
      Real.sqrt lam + (Real.sqrt lam)⁻¹ / (R : ℝ) ≤
        (Real.sqrt (M.factorial : ℝ) + Real.sqrt (8 * Real.pi * C)) *
          N ^ (-(1 : ℝ) / 40) := by
    calc
      _ ≤ Real.sqrt (M.factorial : ℝ) * N ^ (-(1 : ℝ) / 40) +
          Real.sqrt (8 * Real.pi * C) * N ^ (-(1 : ℝ) / 20) :=
        add_le_add hrootUpper hInvBound
      _ ≤ Real.sqrt (M.factorial : ℝ) * N ^ (-(1 : ℝ) / 40) +
          Real.sqrt (8 * Real.pi * C) * N ^ (-(1 : ℝ) / 40) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN (by norm_num)) (by positivity)
          )
      _ = _ := by ring
  calc
    _ ≤ logPhaseBandSecondConstant hD M *
          (Real.sqrt lam + (Real.sqrt lam)⁻¹ / (R : ℝ)) := by
      simpa only [hKeq] using htermTest
    _ ≤ logPhaseBandSecondConstant hD M *
          ((Real.sqrt (M.factorial : ℝ) + Real.sqrt (8 * Real.pi * C)) *
            N ^ (-(1 : ℝ) / 40)) :=
      mul_le_mul_of_nonneg_left hterms hKpos
    _ = (logPhaseBandSecondConstant hD M *
          (Real.sqrt (M.factorial : ℝ) + Real.sqrt (8 * Real.pi * C))) *
          N ^ (-(1 : ℝ) / 40) := by ring
    _ ≤ D * N ^ (-(1 : ℝ) / 40) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (by linarith) _)
    _ ≤ D * N ^ (-logPhaseBandAlpha M) :=
      mul_le_mul_of_nonneg_left hpow40 hDnonneg

private lemma logPhase_rpow_epsilon {D N α δ e : ℝ}
    (hD : 1 ≤ D) (hN : 1 ≤ N) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hδ : δ ≤ α * e) :
    (D * N ^ (-α)) ^ e ≤ D * N ^ (-δ) := by
  have hNpos : 0 < N := by linarith
  have hDpow : D ^ e ≤ D := by
    calc
      D ^ e ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD he1
      _ = D := by rw [Real.rpow_one]
  have hExp : -α * e ≤ -δ := by nlinarith [hδ]
  calc
    (D * N ^ (-α)) ^ e = D ^ e * (N ^ (-α)) ^ e := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hNpos.le _)]
    _ = D ^ e * N ^ (-α * e) := by rw [← Real.rpow_mul hNpos.le]
    _ ≤ D * N ^ (-α * e) :=
      mul_le_mul_of_nonneg_right hDpow (Real.rpow_nonneg hNpos.le _)
    _ ≤ D * N ^ (-δ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN hExp) (by positivity)

private lemma logPhase_hasDerivAt {q a : ℕ} {u y : ℝ}
    (hy : 0 < (q : ℝ) * y + a) :
    HasDerivAt (logPhase q a u)
      (u / (2 * Real.pi) * ((q : ℝ) / ((q : ℝ) * y + a))) y := by
  have harg : HasDerivAt (fun z : ℝ => (q : ℝ) * z + a) (q : ℝ) y := by
    simpa using (hasDerivAt_id y).const_mul (q : ℝ) |>.add_const (a : ℝ)
  have hlog := (Real.hasDerivAt_log (ne_of_gt hy)).comp y harg
  convert hlog.const_mul (u / (2 * Real.pi)) using 1
  · ext z
    simp [logPhase]
  · simp only [div_eq_mul_inv]
    field_simp [Real.pi_ne_zero, ne_of_gt hy]

private lemma logPhase_deriv {q a : ℕ} {u y : ℝ}
    (hy : 0 < (q : ℝ) * y + a) :
    deriv (logPhase q a u) y =
      u / (2 * Real.pi) * ((q : ℝ) / ((q : ℝ) * y + a)) :=
  (logPhase_hasDerivAt hy).deriv

private lemma logPhase_iteratedDeriv_two {q a : ℕ} {u y : ℝ}
    (hy : 0 < (q : ℝ) * y + a) :
    iteratedDeriv 2 (logPhase q a u) y =
      -(u / (2 * Real.pi)) * ((q : ℝ) ^ 2 / ((q : ℝ) * y + a) ^ 2) := by
  let c : ℝ := u / (2 * Real.pi) * (q : ℝ)
  have he : deriv (logPhase q a u) =ᶠ[nhds y]
      (fun z => c * ((q : ℝ) * z + a)⁻¹) := by
    have hcont : ContinuousAt (fun z : ℝ => (q : ℝ) * z + a) y := by fun_prop
    have hpos : ∀ᶠ z : ℝ in nhds y, 0 < (q : ℝ) * z + a :=
      hcont.eventually (isOpen_Ioi.mem_nhds hy)
    filter_upwards [hpos] with z hz
    have hz' := logPhase_deriv (q := q) (a := a) (u := u) (y := z) hz
    simpa [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hz'
  have harg : HasDerivAt (fun z : ℝ => (q : ℝ) * z + a) (q : ℝ) y := by
    simpa using (hasDerivAt_id y).const_mul (q : ℝ) |>.add_const (a : ℝ)
  have hinv := (hasDerivAt_inv (ne_of_gt hy)).comp y harg
  have hrecip : HasDerivAt (fun z : ℝ => c * ((q : ℝ) * z + a)⁻¹)
      (c * (-(q : ℝ) / ((q : ℝ) * y + a) ^ 2)) y := by
    convert hinv.const_mul c using 1
    · ext z
      simp
    · field_simp [ne_of_gt hy]
  calc
    iteratedDeriv 2 (logPhase q a u) y =
        iteratedDeriv 1 (deriv (logPhase q a u)) y := by
          rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ']
    _ = iteratedDeriv 1 (fun z => c * ((q : ℝ) * z + a)⁻¹) y :=
      he.iteratedDeriv_eq 1
    _ = deriv (fun z => c * ((q : ℝ) * z + a)⁻¹) y := by
      rw [iteratedDeriv_one]
    _ = c * (-(q : ℝ) / ((q : ℝ) * y + a) ^ 2) := hrecip.deriv
    _ = -(u / (2 * Real.pi)) *
        ((q : ℝ) ^ 2 / ((q : ℝ) * y + a) ^ 2) := by
          dsimp [c]
          field_simp [Real.pi_ne_zero, ne_of_gt hy]

private lemma logPhase_contDiffOn (q a : ℕ) (u lo hi : ℝ)
    (hbase : ∀ y ∈ Set.Icc lo hi, 0 < (q : ℝ) * y + a) :
    ContDiffOn ℝ 2 (logPhase q a u) (Set.Icc lo hi) := by
  have harg : ContDiffOn ℝ 2 (fun y : ℝ => (q : ℝ) * y + a) (Set.Icc lo hi) := by
    simpa using (contDiffOn_const.mul contDiffOn_id).add contDiffOn_const
  have hlog0 : ContDiffOn ℝ 2 Real.log (Set.Ioi 0) :=
    Real.contDiffOn_log.mono (fun _ hy => ne_of_gt hy)
  have hlog : ContDiffOn ℝ 2
      (fun y : ℝ => Real.log ((q : ℝ) * y + a)) (Set.Icc lo hi) := by
    apply hlog0.comp harg
    intro y hy
    exact Set.mem_Ioi.mpr (hbase y hy)
  change ContDiffOn ℝ 2
    (fun y : ℝ => (u / (2 * Real.pi)) * Real.log ((q : ℝ) * y + a))
    (Set.Icc lo hi)
  exact contDiffOn_const.mul hlog

private lemma logPhase_mellin (q a : ℕ) (u y : ℝ) :
    Blueprint.Analytic.e (logPhase q a u y) =
      Blueprint.Analytic.mellin ((q : ℝ) * y + a) u := by
  unfold Blueprint.Analytic.e Blueprint.Analytic.mellin logPhase
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- A second-derivative estimate for the undifferenced logarithmic phase. -/
theorem logPhaseSum_secondDerivative_bound
    (hD : Blueprint.DerivativeTests) {N lo hi u : ℝ} {q a : ℕ}
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N) (hlohi : lo ≤ hi)
    (hq : 1 ≤ q) (ha : a < q) (hu : 0 < |u|) :
    let lam : ℝ := |u| / (18 * Real.pi * N ^ 2)
    ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
      Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u‖ ≤
        2 * secondTestConstant hD * (N * Real.sqrt lam + (Real.sqrt lam)⁻¹) := by
  dsimp
  let lam : ℝ := |u| / (18 * Real.pi * N ^ 2)
  let f : ℝ → ℝ := logPhase q a u
  have hQ0 : 0 ≤ (q : ℝ) := by exact_mod_cast (Nat.zero_le q)
  have hQpos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hA0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg _
  have hAQ : (a : ℝ) < (q : ℝ) := by exact_mod_cast ha
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hbase (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      0 < (q : ℝ) * y + a := by
    have hyN : N ≤ y := hlo.trans hy.1
    have hqy : 0 < (q : ℝ) * y :=
      mul_pos hQpos (lt_of_lt_of_le hN0 hyN)
    linarith [hA0]
  have hbaseLower (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      (q : ℝ) * N ≤ (q : ℝ) * y + a := by
    have hyN : N ≤ y := hlo.trans hy.1
    have hmul := mul_le_mul_of_nonneg_left hyN hQ0
    linarith [hA0]
  have hbaseUpper (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      (q : ℝ) * y + a ≤ 3 * (q : ℝ) * N := by
    have hy2 : y ≤ 2 * N := hy.2.trans hhi
    have hmul := mul_le_mul_of_nonneg_left hy2 hQ0
    have hqN : (q : ℝ) ≤ (q : ℝ) * N := by
      calc
        (q : ℝ) = (q : ℝ) * 1 := by ring
        _ ≤ (q : ℝ) * N := mul_le_mul_of_nonneg_left hN hQ0
    nlinarith [hAQ.le, hmul]
  have hratio (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      1 / (3 * N) ≤ (q : ℝ) / ((q : ℝ) * y + a) ∧
      (q : ℝ) / ((q : ℝ) * y + a) ≤ 1 / N := by
    have hb := hbase y hy
    constructor
    · rw [div_le_div_iff₀ (by positivity : 0 < 3 * N) hb]
      nlinarith [hbaseUpper y hy]
    · rw [div_le_div_iff₀ hb hN0]
      nlinarith [hbaseLower y hy]
  have hsecondAbs (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      |iteratedDeriv 2 f y| =
        |u| / (2 * Real.pi) *
          (((q : ℝ) / ((q : ℝ) * y + a)) ^ 2) := by
    have hb := hbase y hy
    have hq2 : 0 < (q : ℝ) ^ 2 := pow_pos hQpos _
    have hb2 : 0 < ((q : ℝ) * y + a) ^ 2 := pow_pos hb _
    rw [show f = logPhase q a u by rfl, logPhase_iteratedDeriv_two hb]
    rw [abs_mul, abs_neg, abs_div, abs_of_pos Real.two_pi_pos]
    rw [abs_div, abs_of_pos hq2, abs_of_pos hb2]
    field_simp [ne_of_gt hb]
  have hsecondBounds (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      lam ≤ |iteratedDeriv 2 f y| ∧
        |iteratedDeriv 2 f y| ≤ 9 * lam := by
    rcases hratio y hy with ⟨hloR, hhiR⟩
    have hsquareLo :=
      pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (3 * N)) hloR 2
    have hr0 : 0 ≤ (q : ℝ) / ((q : ℝ) * y + a) :=
      div_nonneg hQ0 (hbase y hy).le
    have hsquareHi :=
      pow_le_pow_left₀ hr0 hhiR 2
    have hcoef : 0 ≤ |u| / (2 * Real.pi) := by positivity
    have hmulLo := mul_le_mul_of_nonneg_left hsquareLo hcoef
    have hmulHi := mul_le_mul_of_nonneg_left hsquareHi hcoef
    have hloEq : |u| / (2 * Real.pi) * (1 / (3 * N)) ^ 2 = lam := by
      dsimp [lam]
      field_simp [Real.pi_ne_zero, ne_of_gt hN0]
      norm_num
    have hhiEq : |u| / (2 * Real.pi) * (1 / N) ^ 2 = 9 * lam := by
      dsimp [lam]
      field_simp [Real.pi_ne_zero, ne_of_gt hN0]
      norm_num
    rw [hsecondAbs y hy]
    exact ⟨hloEq.symm ▸ hmulLo, hhiEq.symm ▸ hmulHi⟩
  let K : ℝ := secondTestConstant hD
  rcases secondTestConstant_spec hD with ⟨hK, htest⟩
  have hsum : (∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, e (f y)) =
      ∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
        Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u := by
    apply Finset.sum_congr rfl
    intro y hy
    exact logPhase_mellin q a u y
  have htest' := htest lo hi lam f hlohi hlam
    (logPhase_contDiffOn q a u lo hi hbase) hsecondBounds
  have hlength : hi - lo + 1 ≤ 2 * N := by linarith
  have hlength0 : 0 ≤ hi - lo + 1 := by linarith
  have hsqrt0 : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  have hinv0 : 0 ≤ (Real.sqrt lam)⁻¹ := inv_nonneg.mpr hsqrt0
  have hcompare :
      (hi - lo + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹ ≤
        2 * (N * Real.sqrt lam + (Real.sqrt lam)⁻¹) := by
    nlinarith [mul_nonneg hlength0 hsqrt0]
  change ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
      Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u‖ ≤
    2 * K * (N * Real.sqrt lam + (Real.sqrt lam)⁻¹)
  rw [← hsum]
  calc
    ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, e (f y)‖ ≤
        K * ((hi - lo + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹) := htest'
    _ ≤ K * (2 * (N * Real.sqrt lam + (Real.sqrt lam)⁻¹)) :=
      mul_le_mul_of_nonneg_left hcompare hK.le
    _ = 2 * K * (N * Real.sqrt lam + (Real.sqrt lam)⁻¹) := by ring

/-- The k=2 frequency band saves a fixed power by the second-derivative test. -/
theorem logPhaseSum_secondDerivative_power
    (hD : Blueprint.DerivativeTests) {N lo hi u : ℝ} {q a : ℕ}
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N) (hlohi : lo ≤ hi)
    (hq : 1 ≤ q) (ha : a < q)
    (hfreqLo : N ≤ |u|)
    (hfreqHi : |u| ≤ N ^ ((19 : ℝ) / 10)) :
    ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
      Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u‖ ≤
        2 * secondTestConstant hD * (1 + Real.sqrt (18 * Real.pi)) *
          N ^ ((19 : ℝ) / 20) := by
  let lam : ℝ := |u| / (18 * Real.pi * N ^ 2)
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hu0 : 0 < |u| := hN0.trans_le hfreqLo
  have hconst : 1 ≤ 18 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hpow19 : N ^ (-(1 : ℝ) / 10) * N ^ 2 =
      N ^ ((19 : ℝ) / 10) := by
    calc
      _ = N ^ (-(1 : ℝ) / 10) * N ^ (2 : ℝ) := by
        congr 1
        exact (Real.rpow_natCast N 2).symm
      _ = N ^ (-(1 : ℝ) / 10 + 2) := by
        rw [← Real.rpow_add hN0]
      _ = _ := by congr 1; norm_num
  have hlamLow : 1 / (18 * Real.pi * N) ≤ lam := by
    dsimp [lam]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hmul := mul_le_mul_of_nonneg_right hfreqLo
      (by positivity : 0 ≤ 18 * Real.pi * N)
    nlinarith [hmul]
  have hden : N ^ 2 ≤ 18 * Real.pi * N ^ 2 := by
    calc
      N ^ 2 = 1 * N ^ 2 := by ring
      _ ≤ (18 * Real.pi) * N ^ 2 :=
        mul_le_mul_of_nonneg_right hconst (sq_nonneg N)
  have hlamHi : lam ≤ N ^ (-(1 : ℝ) / 10) := by
    calc
      lam = |u| / (18 * Real.pi * N ^ 2) := rfl
      _ ≤ N ^ ((19 : ℝ) / 10) / (18 * Real.pi * N ^ 2) :=
        div_le_div_of_nonneg_right hfreqHi (by positivity)
      _ ≤ N ^ (-(1 : ℝ) / 10) := by
        apply (div_le_iff₀ (by positivity)).2
        rw [← hpow19]
        exact mul_le_mul_of_nonneg_left hden
          (Real.rpow_nonneg (le_of_lt hN0) (-(1 : ℝ) / 10))
  have hpowSq : (N ^ (-(1 : ℝ) / 20)) ^ 2 =
      N ^ (-(1 : ℝ) / 10) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    norm_num
  have hroot : Real.sqrt lam ≤ N ^ (-(1 : ℝ) / 20) := by
    have hlam : 0 < lam := by
      dsimp [lam]
      exact div_pos hu0 (by positivity)
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [hpowSq]
      exact hlamHi
  have hfirstPow : N * N ^ (-(1 : ℝ) / 20) =
      N ^ ((19 : ℝ) / 20) := by
    calc
      _ = N ^ (1 : ℝ) * N ^ (-(1 : ℝ) / 20) := by rw [Real.rpow_one]
      _ = N ^ (1 + (-(1 : ℝ) / 20)) := by
        rw [← Real.rpow_add hN0]
      _ = _ := by congr 1; norm_num
  have hfirst : N * Real.sqrt lam ≤ N ^ ((19 : ℝ) / 20) := by
    calc
      _ ≤ N * N ^ (-(1 : ℝ) / 20) :=
        mul_le_mul_of_nonneg_left hroot hN0.le
      _ = N ^ ((19 : ℝ) / 20) := hfirstPow
  have hlamPos : 0 < lam := by
    dsimp [lam]
    exact div_pos hu0 (by positivity)
  have hrootInv : (Real.sqrt lam)⁻¹ ≤ Real.sqrt (18 * Real.pi) *
      N ^ ((19 : ℝ) / 20) := by
    have hsqrtLower := Real.sqrt_le_sqrt hlamLow
    have hrootInvEq :
        (Real.sqrt (1 / (18 * Real.pi * N)))⁻¹ =
          Real.sqrt (18 * Real.pi * N) := by
      rw [one_div, Real.sqrt_inv]
      simp
    have hInvOrder : (Real.sqrt lam)⁻¹ ≤
        (Real.sqrt (1 / (18 * Real.pi * N)))⁻¹ :=
      (inv_le_inv₀ (Real.sqrt_pos.mpr hlamPos)
        (Real.sqrt_pos.mpr (by positivity))).2 hsqrtLower
    have hrootN : Real.sqrt N ≤ N ^ ((19 : ℝ) / 20) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    have hmulRoot : Real.sqrt (18 * Real.pi * N) =
        Real.sqrt (18 * Real.pi) * Real.sqrt N := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 18 * Real.pi)]
    calc
      (Real.sqrt lam)⁻¹ ≤
          (Real.sqrt (1 / (18 * Real.pi * N)))⁻¹ := hInvOrder
      _ = Real.sqrt (18 * Real.pi * N) := hrootInvEq
      _ = Real.sqrt (18 * Real.pi) * Real.sqrt N := hmulRoot
      _ ≤ Real.sqrt (18 * Real.pi) * N ^ ((19 : ℝ) / 20) :=
        mul_le_mul_of_nonneg_left hrootN (Real.sqrt_nonneg _)
  have hC9 : 0 < secondTestConstant hD := (secondTestConstant_spec hD).1
  have hsumBound :
      ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
        Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u‖ ≤
          2 * secondTestConstant hD * (N * Real.sqrt lam + (Real.sqrt lam)⁻¹) := by
    simpa [lam] using logPhaseSum_secondDerivative_bound hD
      hN hlo hhi hlohi hq ha hu0
  have hsumPow :
      N * Real.sqrt lam + (Real.sqrt lam)⁻¹ ≤
        (1 + Real.sqrt (18 * Real.pi)) * N ^ ((19 : ℝ) / 20) := by
    calc
      _ ≤ N ^ ((19 : ℝ) / 20) +
          Real.sqrt (18 * Real.pi) * N ^ ((19 : ℝ) / 20) :=
        add_le_add hfirst hrootInv
      _ = _ := by ring
  calc
    _ ≤ 2 * secondTestConstant hD * (N * Real.sqrt lam + (Real.sqrt lam)⁻¹) :=
      hsumBound
    _ ≤ 2 * secondTestConstant hD *
        ((1 + Real.sqrt (18 * Real.pi)) * N ^ ((19 : ℝ) / 20)) :=
      mul_le_mul_of_nonneg_left hsumPow (by positivity)
    _ = 2 * secondTestConstant hD * (1 + Real.sqrt (18 * Real.pi)) *
        N ^ ((19 : ℝ) / 20) := by ring

/-- The low-frequency range follows directly from the monotone first derivative test. -/
theorem logPhaseSum_firstDerivative
    (hD : Blueprint.DerivativeTests) {N lo hi u : ℝ} {q a : ℕ}
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N) (hlohi : lo ≤ hi)
    (hq : 1 ≤ q) (ha : a < q) (hu : 1 ≤ |u|) (hfreq : |u| ≤ N) :
    ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
      Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u‖ ≤
        24 * firstTestConstant hD * N / |u| := by
  let C : ℝ := firstTestConstant hD
  rcases firstTestConstant_spec hD with ⟨hC, htest⟩
  let lam : ℝ := |u| / (24 * N)
  let f : ℝ → ℝ := logPhase q a u
  let j : ℤ := if 0 ≤ u then 0 else -1
  have hQ0 : 0 ≤ (q : ℝ) := by exact_mod_cast (Nat.zero_le q)
  have hQ : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hQpos : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hQ
  have hA0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg _
  have hAQ : (a : ℝ) < (q : ℝ) := by exact_mod_cast ha
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hu0 : 0 < |u| := lt_of_lt_of_le zero_lt_one hu
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlam24 : lam ≤ 1 / 24 := by
    dsimp [lam]
    calc
      |u| / (24 * N) ≤ N / (24 * N) :=
        div_le_div_of_nonneg_right hfreq (by positivity)
      _ = 1 / 24 := by field_simp
  have hlamhalf : lam ≤ 1 / 2 := by linarith
  have hbase (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      0 < (q : ℝ) * y + a := by
    have hyN : N ≤ y := hlo.trans hy.1
    have hqy : 0 < (q : ℝ) * y :=
      mul_pos hQpos (lt_of_lt_of_le hN0 hyN)
    linarith [hA0]
  have hbaseLower (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      (q : ℝ) * N ≤ (q : ℝ) * y + a := by
    have hyN : N ≤ y := hlo.trans hy.1
    have hmul := mul_le_mul_of_nonneg_left hyN hQ0
    linarith [hA0]
  have hbaseUpper (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      (q : ℝ) * y + a ≤ 3 * (q : ℝ) * N := by
    have hy2 : y ≤ 2 * N := hy.2.trans hhi
    have hmul := mul_le_mul_of_nonneg_left hy2 hQ0
    have hqN : (q : ℝ) ≤ (q : ℝ) * N := by
      calc
        (q : ℝ) = (q : ℝ) * 1 := by ring
        _ ≤ (q : ℝ) * N := mul_le_mul_of_nonneg_left hN hQ0
    nlinarith [hAQ.le, hmul]
  have hratio (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      1 / (3 * N) ≤ (q : ℝ) / ((q : ℝ) * y + a) ∧
      (q : ℝ) / ((q : ℝ) * y + a) ≤ 1 / N := by
    have hb := hbase y hy
    constructor
    · rw [div_le_div_iff₀ (by positivity : 0 < 3 * N) hb]
      nlinarith [hbaseUpper y hy]
    · rw [div_le_div_iff₀ hb hN0]
      nlinarith [hbaseLower y hy]
  have hmag (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      lam ≤ |u| / (2 * Real.pi) * ((q : ℝ) / ((q : ℝ) * y + a)) ∧
      |u| / (2 * Real.pi) * ((q : ℝ) / ((q : ℝ) * y + a)) ≤ 1 / 6 := by
    rcases hratio y hy with ⟨hloR, hhiR⟩
    have hcoef : 0 < |u| / (2 * Real.pi) := by positivity
    have hloM := mul_le_mul_of_nonneg_left hloR hcoef.le
    have hhiM := mul_le_mul_of_nonneg_left hhiR hcoef.le
    have hlowSimple : |u| / (24 * N) ≤ |u| / (6 * Real.pi * N) := by
      apply div_le_div_of_nonneg_left (abs_nonneg u) (by positivity)
      nlinarith [Real.pi_lt_four, hN0]
    have hloEq : |u| / (6 * Real.pi * N) =
        |u| / (2 * Real.pi) * (1 / (3 * N)) := by
      field_simp [Real.pi_ne_zero]
      norm_num
    have hhighSimple : |u| / (2 * Real.pi) * (1 / N) ≤
        |u| / (2 * Real.pi * N) := by
      field_simp [Real.pi_ne_zero]
      norm_num
    have hfreq' : |u| / (2 * Real.pi * N) ≤ 1 / (2 * Real.pi) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [mul_le_mul_of_nonneg_right hfreq (by positivity : 0 ≤ 2 * Real.pi)]
    have hpi : 1 / (2 * Real.pi) ≤ 1 / 6 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [Real.pi_gt_three]
    refine ⟨?_, ?_⟩
    · dsimp [lam]
      calc
        |u| / (24 * N) ≤ |u| / (6 * Real.pi * N) := hlowSimple
        _ = |u| / (2 * Real.pi) * (1 / (3 * N)) := hloEq
        _ ≤ |u| / (2 * Real.pi) * ((q : ℝ) / ((q : ℝ) * y + a)) := hloM
    · exact hhiM.trans (hhighSimple.trans (hfreq'.trans hpi))
  have hdiff : DifferentiableOn ℝ f (Set.Icc lo hi) := by
    intro y hy
    exact (logPhase_hasDerivAt (hbase y hy)).differentiableAt.differentiableWithinAt
  have hderiv (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      deriv f y = u / (2 * Real.pi) *
        ((q : ℝ) / ((q : ℝ) * y + a)) := by
    simpa [f] using (logPhase_deriv (hbase y hy))
  have hratioAntitone (x y : ℝ) (hx : x ∈ Set.Icc lo hi)
      (hy : y ∈ Set.Icc lo hi) (hxy : x ≤ y) :
      (q : ℝ) / ((q : ℝ) * y + a) ≤
        (q : ℝ) / ((q : ℝ) * x + a) := by
    have hxbase := hbase x hx
    have hybase := hbase y hy
    have hden : (q : ℝ) * x + a ≤ (q : ℝ) * y + a := by
      nlinarith [mul_le_mul_of_nonneg_left hxy hQ0]
    rw [div_le_div_iff₀ hybase hxbase]
    exact mul_le_mul_of_nonneg_left hden hQ0
  have hmono :
      MonotoneOn (deriv f) (Set.Icc lo hi) ∨
        AntitoneOn (deriv f) (Set.Icc lo hi) := by
    by_cases hupos : 0 ≤ u
    · right
      intro x hx y hy hxy
      rw [hderiv x hx, hderiv y hy]
      exact mul_le_mul_of_nonneg_left (hratioAntitone x y hx hy hxy)
        (div_nonneg hupos (by positivity))
    · left
      have huneg : u ≤ 0 := le_of_not_ge hupos
      intro x hx y hy hxy
      rw [hderiv x hx, hderiv y hy]
      exact mul_le_mul_of_nonpos_left (hratioAntitone x y hx hy hxy)
        (div_nonpos_of_nonpos_of_nonneg huneg (by positivity))
  have hrange (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
      (j : ℝ) + lam ≤ deriv f y ∧ deriv f y ≤ (j : ℝ) + 1 - lam := by
    rcases hmag y hy with ⟨hmlo, hmhi⟩
    by_cases hupos : 0 ≤ u
    · have huPos : 0 < u := by
        have : 1 ≤ u := by simpa [abs_of_nonneg hupos] using hu
        linarith
      have hder : deriv f y =
          |u| / (2 * Real.pi) * ((q : ℝ) / ((q : ℝ) * y + a)) := by
        rw [hderiv y hy, abs_of_nonneg hupos]
      have hh : lam ≤ deriv f y ∧ deriv f y ≤ 1 - lam := by
        rw [hder]
        constructor
        · exact hmlo
        · nlinarith [hmhi, hlam24]
      simpa [j, hupos] using hh
    · have huneg : u < 0 := lt_of_not_ge hupos
      have hder : deriv f y =
          -(|u| / (2 * Real.pi) * ((q : ℝ) / ((q : ℝ) * y + a))) := by
        rw [hderiv y hy, abs_of_neg huneg]
        ring
      have hh : -1 + lam ≤ deriv f y ∧ deriv f y ≤ -lam := by
        rw [hder]
        constructor <;> nlinarith [hmlo, hmhi, hlam24]
      simpa [j, hupos] using hh
  have htest' := htest lo hi lam j f hlohi hlam hlamhalf hdiff hmono hrange
  have hsum : (∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, e (f y)) =
      ∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
        Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u := by
    apply Finset.sum_congr rfl
    intro y hy
    exact logPhase_mellin q a u y
  change ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
      Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u‖ ≤ 24 * C * N / |u|
  rw [← hsum]
  calc
    ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋, e (f y)‖ ≤ C / lam := htest'
    _ = (24 * C) * N / |u| := by
      dsimp [lam]
      field_simp [ne_of_gt hN0, ne_of_gt hu0]

/-- The first and second derivative tests cover frequencies through N^(19/10). -/
theorem logPhaseSum_lowMedium
    (hD : Blueprint.DerivativeTests) {N lo hi u : ℝ} {q a : ℕ}
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N) (hlohi : lo ≤ hi)
    (hq : 1 ≤ q) (ha : a < q) (hu : 1 ≤ |u|)
    (hfreq : |u| ≤ N ^ ((19 : ℝ) / 10)) :
    ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
      Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u‖ ≤
        (24 * firstTestConstant hD +
          2 * secondTestConstant hD * (1 + Real.sqrt (18 * Real.pi)) + 1) *
            N * (|u|⁻¹ + N ^ (-(1 : ℝ) / 20)) := by
  let K : ℝ := 24 * firstTestConstant hD +
    2 * secondTestConstant hD * (1 + Real.sqrt (18 * Real.pi)) + 1
  have hC1 : 0 < firstTestConstant hD := (firstTestConstant_spec hD).1
  have hC2 : 0 < secondTestConstant hD := (secondTestConstant_spec hD).1
  have hK : 0 < K := by dsimp [K]; positivity
  have hsecondNonneg :
      0 ≤ 2 * secondTestConstant hD * (1 + Real.sqrt (18 * Real.pi)) := by
    positivity
  have hfirstNonneg : 0 ≤ 24 * firstTestConstant hD := by positivity
  have hK1 : 24 * firstTestConstant hD ≤ K := by
    dsimp [K]
    linarith
  have hK2 :
      2 * secondTestConstant hD * (1 + Real.sqrt (18 * Real.pi)) ≤ K := by
    dsimp [K]
    linarith
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  change ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
      Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u‖ ≤
    K * N * (|u|⁻¹ + N ^ (-(1 : ℝ) / 20))
  by_cases hsmall : |u| ≤ N
  · have hbound := logPhaseSum_firstDerivative hD
      hN hlo hhi hlohi hq ha hu hsmall
    have hinvu : 0 ≤ |u|⁻¹ := inv_nonneg.mpr (abs_nonneg u)
    have hpow : 0 ≤ N ^ (-(1 : ℝ) / 20) :=
      Real.rpow_nonneg hN0.le _
    have hscale : 0 ≤ N * |u|⁻¹ := mul_nonneg (by linarith) hinvu
    have hinner : N * |u|⁻¹ ≤ N * (|u|⁻¹ + N ^ (-(1 : ℝ) / 20)) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hpow) hN0.le
    calc
      _ ≤ 24 * firstTestConstant hD * N / |u| := hbound
      _ = 24 * firstTestConstant hD * (N * |u|⁻¹) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ K * (N * |u|⁻¹) := mul_le_mul_of_nonneg_right hK1 hscale
      _ ≤ K * (N * (|u|⁻¹ + N ^ (-(1 : ℝ) / 20))) :=
        mul_le_mul_of_nonneg_left hinner hK.le
      _ = K * N * (|u|⁻¹ + N ^ (-(1 : ℝ) / 20)) := by ring
  · have hNleu : N ≤ |u| := (lt_of_not_ge hsmall).le
    have hbound := logPhaseSum_secondDerivative_power hD
      hN hlo hhi hlohi hq ha hNleu hfreq
    have hinvu : 0 ≤ |u|⁻¹ := inv_nonneg.mpr (abs_nonneg u)
    have hpow : 0 ≤ N ^ (-(1 : ℝ) / 20) :=
      Real.rpow_nonneg hN0.le _
    have hpow19 : N * N ^ (-(1 : ℝ) / 20) =
        N ^ ((19 : ℝ) / 20) := by
      calc
        _ = N ^ (1 : ℝ) * N ^ (-(1 : ℝ) / 20) := by rw [Real.rpow_one]
        _ = N ^ (1 + (-(1 : ℝ) / 20)) := by rw [← Real.rpow_add hN0]
        _ = _ := by congr 1; norm_num
    have hinner :
        N * N ^ (-(1 : ℝ) / 20) ≤
          N * (|u|⁻¹ + N ^ (-(1 : ℝ) / 20)) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hinvu) hN0.le
    calc
      _ ≤ 2 * secondTestConstant hD * (1 + Real.sqrt (18 * Real.pi)) *
          N ^ ((19 : ℝ) / 20) := hbound
      _ ≤ K * N ^ ((19 : ℝ) / 20) :=
        mul_le_mul_of_nonneg_right hK2 (Real.rpow_nonneg hN0.le _)
      _ = K * (N * N ^ (-(1 : ℝ) / 20)) := by rw [hpow19]
      _ ≤ K * (N * (|u|⁻¹ + N ^ (-(1 : ℝ) / 20))) :=
        mul_le_mul_of_nonneg_left hinner hK.le
      _ = K * N * (|u|⁻¹ + N ^ (-(1 : ℝ) / 20)) := by ring

/-- Overlapping power ranges cover every frequency up to N^(m-1/10). -/
private theorem logPhase_frequencyCover_aux (m : ℕ) :
    2 ≤ m → ∀ {N U : ℝ}, 1 ≤ N →
      U ≤ N ^ ((m : ℝ) - (1 : ℝ) / 10) →
      U ≤ N ^ ((19 : ℝ) / 10) ∨
        ∃ k : ℕ, 3 ≤ k ∧ k ≤ m ∧
          N ^ ((k : ℝ) - (19 : ℝ) / 10) ≤ U ∧
          U ≤ N ^ ((k : ℝ) - (1 : ℝ) / 10) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm N U hN hbound
    by_cases hbase : m = 2
    · subst m
      left
      have hexp : ((2 : ℕ) : ℝ) - (1 : ℝ) / 10 = (19 : ℝ) / 10 := by norm_num
      rw [hexp] at hbound
      exact hbound
    · have hm3 : 3 ≤ m := by omega
      let n : ℕ := m - 1
      have hnlt : n < m := by dsimp [n]; omega
      have hn2 : 2 ≤ n := by dsimp [n]; omega
      have hprevExp : (n : ℝ) - (1 : ℝ) / 10 =
          (m : ℝ) - (11 : ℝ) / 10 := by
        dsimp [n]
        have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ m)]
          simp
        rw [hcast]
        ring
      by_cases hsmall : U ≤ N ^ ((n : ℝ) - (1 : ℝ) / 10)
      · rcases ih n hnlt hn2 hN hsmall with hlow | ⟨k, hklo, hkhi, hklower, hkupper⟩
        · exact Or.inl hlow
        · right
          exact ⟨k, hklo, hkhi.trans (by dsimp [n]; omega), hklower, hkupper⟩
      · right
        have hprev : N ^ ((n : ℝ) - (1 : ℝ) / 10) < U :=
          lt_of_not_ge hsmall
        have hexp : (m : ℝ) - (19 : ℝ) / 10 ≤
            (n : ℝ) - (1 : ℝ) / 10 := by
          rw [hprevExp]
          norm_num
          linarith
        have hpower :
            N ^ ((m : ℝ) - (19 : ℝ) / 10) ≤
              N ^ ((n : ℝ) - (1 : ℝ) / 10) :=
          Real.rpow_le_rpow_of_exponent_le hN hexp
        exact ⟨m, by omega, le_rfl, hpower.trans hprev.le, hbound⟩

/-- The cutoff |u|≤x² falls in one of the bounded-depth bands once N≥x^(τ/2). -/
theorem logPhase_frequencyCover {τ x N u : ℝ}
    (hτ : 0 < τ) (hx : 1 ≤ x) (hNxN : x ^ (τ / 2) ≤ N)
    (_hu : 1 ≤ |u|) (hux : |u| ≤ x ^ (2 : ℕ)) :
    |u| ≤ N ^ ((19 : ℝ) / 10) ∨
      ∃ k : ℕ, 3 ≤ k ∧ k ≤ ⌈4 / τ⌉₊ + 3 ∧
        N ^ ((k : ℝ) - (19 : ℝ) / 10) ≤ |u| ∧
        |u| ≤ N ^ ((k : ℝ) - (1 : ℝ) / 10) := by
  let M : ℕ := ⌈4 / τ⌉₊ + 3
  have hM : 2 ≤ M := by dsimp [M]; omega
  have hN : 1 ≤ N := by
    have hxpow : 1 ≤ x ^ (τ / 2) := Real.one_le_rpow hx (by positivity)
    exact hxpow.trans hNxN
  have hceil : (4 / τ : ℝ) ≤ (⌈4 / τ⌉₊ : ℝ) := Nat.le_ceil _
  have hMexp : 4 / τ ≤ (M : ℝ) - (1 : ℝ) / 10 := by
    dsimp [M]
    push_cast
    nlinarith
  have hE : 0 < 4 / τ := by positivity
  have hexpMul : τ / 2 * (4 / τ) = 2 := by
    field_simp [ne_of_gt hτ]
    norm_num
  have hxpower : (x ^ (τ / 2)) ^ (4 / τ) = x ^ (2 : ℕ) := by
    rw [← Real.rpow_mul (by linarith : 0 ≤ x), hexpMul]
    exact Real.rpow_natCast x 2
  have hpowBound : x ^ (2 : ℕ) ≤ N ^ (4 / τ) := by
    rw [← hxpower]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _)
      hNxN hE.le
  have hpowM : N ^ (4 / τ) ≤ N ^ ((M : ℝ) - (1 : ℝ) / 10) :=
    Real.rpow_le_rpow_of_exponent_le hN hMexp
  have hbound : |u| ≤ N ^ ((M : ℝ) - (1 : ℝ) / 10) :=
    hux.trans (hpowBound.trans hpowM)
  simpa [M] using logPhase_frequencyCover_aux M hM hN hbound

/-- Uniform estimate required for the bands above the direct k=2 range. -/
def LogPhaseHighBands (_hD : Blueprint.DerivativeTests) (τ : ℝ) : Prop :=
  ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
    ∀ (N lo hi u : ℝ) (q a : ℕ) (k : ℕ),
      x ^ (τ / 2) ≤ N → N ≤ lo → lo ≤ hi → hi ≤ 2 * N →
      1 ≤ q → a < q → 1 ≤ |u| → |u| ≤ x ^ (2 : ℕ) →
      3 ≤ k → k ≤ ⌈4 / τ⌉₊ + 3 →
      N ^ ((k : ℝ) - (19 : ℝ) / 10) ≤ |u| →
      |u| ≤ N ^ ((k : ℝ) - (1 : ℝ) / 10) →
      ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
        Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u‖ ≤
          K * N * (|u|⁻¹ + N ^ (-δ))

theorem logPhaseHighBands_proof (hD : Blueprint.DerivativeTests)
    (τ : ℝ) (hτ : 0 < τ) : LogPhaseHighBands hD τ := by
  let M : ℕ := ⌈4 / τ⌉₊ + 3
  let α : ℝ := logPhaseBandAlpha M
  let δ : ℝ := α / (2 : ℝ) ^ M
  let D : ℝ := logPhaseBandD hD M
  let K : ℝ := 9 * D
  have hM : 3 ≤ M := by dsimp [M]; omega
  have hα : 0 < α := by dsimp [α, logPhaseBandAlpha]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hD4 : 4 ≤ D := by dsimp [D]; exact (logPhaseBandD_bounds hD M).1
  have hDpos : 0 < D := by linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hPowerTendsto : Tendsto (fun x : ℝ => x ^ (τ / 2 * α)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hD_event : ∀ᶠ x : ℝ in Filter.atTop, D ≤ x ^ (τ / 2 * α) :=
    Filter.tendsto_atTop.1 hPowerTendsto D
  refine ⟨δ, K, hδ, hK, ?_⟩
  filter_upwards [hD_event, Filter.eventually_ge_atTop (1 : ℝ)] with
    x hxD hxLarge
  intro N lo hi u q a k hNxN hNlo hlohi hhi hq ha hu _hux hklo hkhi
    hfreqLo hfreqHi
  have hxpow : 1 ≤ x ^ (τ / 2) := Real.one_le_rpow hxLarge (by positivity)
  have hN : 1 ≤ N := hxpow.trans hNxN
  have hNpos : 0 < N := by linarith
  have hDlarge : D ≤ N ^ α := by
    calc
      D ≤ x ^ (τ / 2 * α) := hxD
      _ = (x ^ (τ / 2)) ^ α := by
        exact Real.rpow_mul (le_trans zero_le_one hxLarge) (τ / 2) α
      _ ≤ N ^ α :=
        Real.rpow_le_rpow
          (Real.rpow_nonneg (le_trans zero_le_one hxLarge) _) hNxN (le_of_lt hα)
  have hscales := logPhaseBand_scales hM hklo hkhi hN hD4 hDlarge
  let H : ℕ := logPhaseBandH N k
  let R : ℕ := logPhaseBandR N
  let eps : ℝ := D * N ^ (-α)
  have hHone : 1 ≤ H := by simpa [H] using hscales.1
  have hHR : H ≤ R := by simpa [H, R] using hscales.2.1
  have hRlo : 2 * N ≤ (R : ℝ) := by simpa [R] using hscales.2.2.1
  have hRhi : (R : ℝ) ≤ 3 * N := by simpa [R] using hscales.2.2.2.1
  have hHε : 2 / (H : ℝ) ≤ eps := by simpa [H, eps, D, α] using hscales.2.2.2.2
  have hepsPos : 0 < eps := by
    dsimp [eps]
    exact mul_pos hDpos (Real.rpow_pos_of_pos hNpos _)
  have hNαpos : 0 < N ^ α := Real.rpow_pos_of_pos hNpos _
  have hepsOne : eps ≤ 1 := by
    dsimp [eps]
    rw [Real.rpow_neg hNpos.le]
    exact (div_le_one hNαpos).2 hDlarge
  let L : ℤ := ⌈lo⌉
  let U : ℤ := ⌊hi⌋
  have hlo1 : 1 ≤ lo := hN.trans hNlo
  have hLreal : (1 : ℝ) ≤ (L : ℝ) := by
    dsimp [L]
    exact hlo1.trans (Int.le_ceil lo)
  have hL : 1 ≤ L := by exact_mod_cast hLreal
  have hUhi : (U : ℝ) ≤ 2 * N := by
    dsimp [U]
    exact (Int.floor_le hi).trans hhi
  have hUreal : (U : ℝ) ≤ (R : ℝ) := hUhi.trans (le_trans (by linarith) hRlo)
  have hU : U ≤ R := by exact_mod_cast hUreal
  have hNLo : N ≤ (L : ℝ) := by
    dsimp [L]
    exact hNlo.trans (Int.le_ceil lo)
  have hRpos : 0 < (R : ℝ) := by linarith [hRlo, hN]
  have hterminal : ∀ hs : List ℤ, hs.length = k - 2 →
      (∀ h ∈ hs, 0 < h ∧ h < H) →
      ‖∑ n ∈ Finset.Icc L (U - hs.sum),
        OAI.Problem337.differencingPhase
          (OAI.Problem337.forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
            (logPhase q a u) (n : ℝ))‖ / (R : ℝ) ≤ eps := by
    intro hs hlenr hgood
    let T : ℤ := U - hs.sum
    by_cases hLT : L ≤ T
    · have hlen : hs.length + 2 = k := by omega
      have hterm := logPhase_terminal_epsilon hD hM hklo hkhi hN hDlarge
        hLT hNLo hUhi (by rfl) hq ha hu hlen hfreqLo hfreqHi
        (by simpa [H] using hgood)
      simpa [T, eps, D, α, H, R] using hterm
    · rw [Finset.Icc_eq_empty hLT]
      simp only [Finset.sum_empty, norm_zero, zero_div]
      exact le_of_lt hepsPos
  have hVdC := OAI.Problem337.interval_phase_ambient_power_bound
    (k - 2) R H L U hL hU hHone hHR eps hepsPos hepsOne hHε
    (logPhase q a u) hterminal
  have hsumPhase :
      (∑ y ∈ Finset.Icc L U,
        OAI.Problem337.differencingPhase (logPhase q a u (y : ℝ))) =
        ∑ y ∈ Finset.Icc L U,
          Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [← analyticE_eq_differencingPhase]
    exact logPhase_mellin q a u (y : ℝ)
  have hnorm :
      ‖∑ y ∈ Finset.Icc L U,
        Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u‖ / (R : ℝ) ≤
        3 * eps ^ (1 / (2 : ℝ) ^ (k - 2)) := by
    rw [← hsumPhase]
    exact hVdC
  let e : ℝ := 1 / (2 : ℝ) ^ (k - 2)
  have hpow2 : (2 : ℝ) ^ (k - 2) ≤ (2 : ℝ) ^ M := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hInv2 : 1 / (2 : ℝ) ^ M ≤ 1 / (2 : ℝ) ^ (k - 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hpow2]
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by
    dsimp [e]
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hδe : δ ≤ α * e := by
    dsimp [δ, e]
    calc
      α / (2 : ℝ) ^ M = α * (1 / (2 : ℝ) ^ M) := by ring
      _ ≤ α * (1 / (2 : ℝ) ^ (k - 2)) :=
        mul_le_mul_of_nonneg_left hInv2 (le_of_lt hα)
      _ = α * (1 / (2 : ℝ) ^ (k - 2)) := by ring
  have hD1 : 1 ≤ D := by linarith [hD4]
  have hpowEps : eps ^ e ≤ D * N ^ (-δ) := by
    simpa [eps, D, α] using logPhase_rpow_epsilon hD1 hN he.le he1 hδe
  have hNormRaw :
      ‖∑ y ∈ Finset.Icc L U,
        Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u‖ ≤
        (R : ℝ) * (3 * eps ^ e) := by
    have hnorm' :
        ‖∑ y ∈ Finset.Icc L U,
          Blueprint.Analytic.mellin ((q : ℝ) * (y : ℝ) + a) u‖ / (R : ℝ) ≤
          3 * eps ^ e := by simpa [e] using hnorm
    calc
      _ ≤ (3 * eps ^ e) * (R : ℝ) := (div_le_iff₀ hRpos).mp hnorm'
      _ = (R : ℝ) * (3 * eps ^ e) := by ring
  have hInvU : 0 ≤ |u|⁻¹ := inv_nonneg.mpr (abs_nonneg u)
  have hinner : N ^ (-δ) ≤ |u|⁻¹ + N ^ (-δ) := le_add_of_nonneg_left hInvU
  calc
    _ ≤ 9 * N * eps ^ e := by
      calc
        _ ≤ (R : ℝ) * (3 * eps ^ e) := hNormRaw
        _ ≤ (3 * N) * (3 * eps ^ e) :=
          mul_le_mul_of_nonneg_right hRhi (by positivity)
        _ = 9 * N * eps ^ e := by ring
    _ ≤ 9 * N * (D * N ^ (-δ)) :=
      mul_le_mul_of_nonneg_left hpowEps (by positivity)
    _ ≤ 9 * D * N * (|u|⁻¹ + N ^ (-δ)) := by
      have hcoef : 0 ≤ 9 * D * N := by positivity
      calc
        9 * N * (D * N ^ (-δ)) = 9 * D * N * N ^ (-δ) := by ring
        _ ≤ 9 * D * N * (|u|⁻¹ + N ^ (-δ)) :=
          mul_le_mul_of_nonneg_left hinner hcoef
    _ = K * N * (|u|⁻¹ + N ^ (-δ)) := by dsimp [K]

/-- Once the bounded-depth high bands are proved, the whole log-phase sum follows. -/
theorem logPhaseSumTask_of_highBands :
    (∀ (hD : Blueprint.DerivativeTests) (τ : ℝ), 0 < τ →
      LogPhaseHighBands hD τ) → LogPhaseSumTask := by
  intro hHigh
  unfold LogPhaseSumTask
  intro hD τ hτ
  obtain ⟨δH, KH, hδH, hKH, hev⟩ := hHigh hD τ hτ
  let δ : ℝ := min δH ((1 : ℝ) / 20)
  let Klow : ℝ := 24 * firstTestConstant hD +
    2 * secondTestConstant hD * (1 + Real.sqrt (18 * Real.pi)) + 1
  let K : ℝ := KH + Klow + 1
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδH (by norm_num)
  have hδH' : δ ≤ δH := by dsimp [δ]; exact min_le_left _ _
  have hδ20 : δ ≤ (1 : ℝ) / 20 := by dsimp [δ]; exact min_le_right _ _
  have hKlow : 0 < Klow := by
    dsimp [Klow]
    have hC1 := (firstTestConstant_spec hD).1
    have hC2 := (secondTestConstant_spec hD).1
    positivity
  have hK : 0 < K := by dsimp [K]; linarith
  have hKH : KH ≤ K := by dsimp [K]; linarith
  have hKlow' : Klow ≤ K := by dsimp [K]; linarith
  refine ⟨δ, K, hδ, hK, ?_⟩
  filter_upwards [hev, Filter.eventually_ge_atTop (1 : ℝ)] with x hxHigh hxLarge
  intro N lo hi u q a hNxN hNlo hlohi hhi hq ha hu hux
  have hxpow : 1 ≤ x ^ (τ / 2) := Real.one_le_rpow hxLarge (by positivity)
  have hN : 1 ≤ N := hxpow.trans hNxN
  rcases logPhase_frequencyCover hτ hxLarge hNxN hu hux with hlowFreq |
    ⟨k, hklo, hkhi, hkloFreq, hkhiFreq⟩
  · have hlow := logPhaseSum_lowMedium hD hN hNlo hhi hlohi hq ha hu hlowFreq
    have hpow : N ^ (-(1 : ℝ) / 20) ≤ N ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith [hδ20])
    have hinner : |u|⁻¹ + N ^ (-(1 : ℝ) / 20) ≤ |u|⁻¹ + N ^ (-δ) :=
      add_le_add le_rfl hpow
    have hKN0 : 0 ≤ K * N := mul_nonneg hK.le (by linarith)
    have hKlowN : Klow * N ≤ K * N :=
      mul_le_mul_of_nonneg_right hKlow' (by linarith)
    calc
      _ ≤ Klow * N * (|u|⁻¹ + N ^ (-(1 : ℝ) / 20)) := hlow
      _ ≤ K * N * (|u|⁻¹ + N ^ (-(1 : ℝ) / 20)) :=
        mul_le_mul_of_nonneg_right hKlowN
          (add_nonneg (inv_nonneg.mpr (abs_nonneg u))
            (Real.rpow_nonneg (by linarith) _))
      _ ≤ K * N * (|u|⁻¹ + N ^ (-δ)) :=
        mul_le_mul_of_nonneg_left hinner hKN0
  · have hhigh := hxHigh N lo hi u q a k
      hNxN hNlo hlohi hhi hq ha hu hux hklo hkhi hkloFreq hkhiFreq
    have hpow : N ^ (-δH) ≤ N ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith [hδH'])
    have hinner : |u|⁻¹ + N ^ (-δH) ≤ |u|⁻¹ + N ^ (-δ) :=
      add_le_add le_rfl hpow
    have hKN0 : 0 ≤ K * N := mul_nonneg hK.le (by linarith)
    have hKHN : KH * N ≤ K * N :=
      mul_le_mul_of_nonneg_right hKH (by linarith)
    calc
      _ ≤ KH * N * (|u|⁻¹ + N ^ (-δH)) := hhigh
      _ ≤ K * N * (|u|⁻¹ + N ^ (-δH)) :=
        mul_le_mul_of_nonneg_right hKHN
          (add_nonneg (inv_nonneg.mpr (abs_nonneg u))
            (Real.rpow_nonneg (by linarith) _))
      _ ≤ K * N * (|u|⁻¹ + N ^ (-δ)) :=
        mul_le_mul_of_nonneg_left hinner hKN0

theorem LogPhaseSumTask_proof : LogPhaseSumTask :=
  logPhaseSumTask_of_highBands (by
    intro hD τ hτ
    exact logPhaseHighBands_proof hD τ hτ)


end Erdos821.P5Log

