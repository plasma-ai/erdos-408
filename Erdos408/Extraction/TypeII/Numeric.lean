import Erdos408.Extraction.TypeII.Pointwise

/-!
# The size of the bounds

Every factor of `B₄` and `B₅` other than the powers of `L` is `exp(O(s³)) = L^{o(1)}`:

* `∑_{x^γ < p ≤ M} 1/p ≤ log(2/γ) + 1` and `∏_{Y < p ≤ M} (1 - ρ/p)⁻¹ ≤ exp(2ρ(log(2T²⁵) + 1))`
  by Mertens' second theorem, so the factor-sum powers are `exp(O(R² s))`;
* `𝒩, 2^{K N'}` and the endpoint bound are `exp(O(s))`, and `T^{C_Φ} = exp(C_Φ s)`.
-/

namespace Erdos408.TypeII

open Finset Real Filter

/-- `∑_{x^γ < p ≤ M} 1/p ≤ log(log M / log x^γ) + 1`, by Mertens. -/
theorem recipSum_le {E x γ : ℝ} {N : ℕ}
    (hE : ∀ y z : ℝ, 2 ≤ y → y ≤ z →
      |∑ p ∈ primesIoc y z, (1 : ℝ) / p - Real.log (Real.log z / Real.log y)| ≤ E / Real.log y)
    (h2 : 2 ≤ x ^ γ) (hN : x ^ γ ≤ N) (hEγ : E ≤ Real.log (x ^ γ)) :
    recipSum x γ N ≤ Real.log (Real.log N / Real.log (x ^ γ)) + 1 := by
  have h := hE _ _ h2 hN
  rw [abs_le] at h
  have hl : 0 < Real.log (x ^ γ) := Real.log_pos (by linarith)
  have : E / Real.log (x ^ γ) ≤ 1 := (div_le_one hl).2 hEγ
  unfold recipSum
  linarith [h.2]

/-- `∏_{Y < p ≤ M} (1 - ρ/p)⁻¹ ≤ exp(2ρ (log(log M / log Y) + 1))`, by Mertens. -/
theorem highProd_le {E x : ℝ} {N : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hE : ∀ y z : ℝ, 2 ≤ y → y ≤ z →
      |∑ p ∈ primesIoc y z, (1 : ℝ) / p - Real.log (Real.log z / Real.log y)| ≤ E / Real.log y)
    (h2 : 2 ≤ proxyCutoff x) (hρY : 2 * ρ ≤ proxyCutoff x) (hN : proxyCutoff x ≤ N)
    (hEY : E ≤ Real.log (proxyCutoff x)) :
    highProd x N ρ ≤
      Real.exp (2 * ρ * (Real.log (Real.log N / Real.log (proxyCutoff x)) + 1)) := by
  unfold highProd
  have hY0 : 0 < proxyCutoff x := by linarith
  have hpos : ∀ p ∈ primesIoc (proxyCutoff x) N, (0 : ℝ) < p := fun p hp => by
    have := (mem_primesIoc.1 hp).2.1
    linarith
  refine (prod_inv_one_sub_le_exp (primesIoc (proxyCutoff x) N) (fun p : ℕ => ρ / (p : ℝ))
    (fun p hp => div_nonneg hρ (hpos p hp).le) fun p hp => ?_).trans ?_
  · have := (mem_primesIoc.1 hp).2.1
    rw [div_le_iff₀ (by linarith)]; linarith
  · apply Real.exp_le_exp.2
    have h := hE _ _ h2 hN
    rw [abs_le] at h
    have hl : 0 < Real.log (proxyCutoff x) := Real.log_pos (by linarith)
    have : E / Real.log (proxyCutoff x) ≤ 1 := (div_le_one hl).2 hEY
    have hρs : ∑ i ∈ primesIoc (proxyCutoff x) N, ρ / (i : ℝ) =
        ρ * ∑ i ∈ primesIoc (proxyCutoff x) N, (1 : ℝ) / i := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    rw [hρs]
    have hsum : ∑ p ∈ primesIoc (proxyCutoff x) N, (1 : ℝ) / p ≤
        Real.log (Real.log N / Real.log (proxyCutoff x)) + 1 := by linarith [h.2]
    nlinarith

/-! ### Polynomial bookkeeping in `s` -/

theorem cube_bounds {s : ℝ} (hs : 0 ≤ s) : s + 1 ≤ 2 * (s ^ 3 + 1) ∧
    (s + 1) ^ 3 ≤ 4 * (s ^ 3 + 1) ∧ s ^ 2 + 1 ≤ 2 * (s ^ 3 + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (s - 1), sq_nonneg s]
  · nlinarith [sq_nonneg (s - 1), mul_nonneg hs (sq_nonneg (s - 1))]
  · nlinarith [sq_nonneg (s - 1), mul_nonneg hs (sq_nonneg (s - 1))]

/-- `R + 2R²(25s + 2) ≤ A (s³ + 1)` for `0 ≤ R ≤ b (s + 1)`. -/
theorem poly_le {s R b : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R) (hb : 0 ≤ b) (hRb : R ≤ b * (s + 1)) :
    R + 2 * R ^ 2 * (25 * s + 2) ≤ (2 * b + 216 * b ^ 2) * (s ^ 3 + 1) := by
  obtain ⟨h1, h2, -⟩ := cube_bounds hs
  have hR2 : R ^ 2 ≤ b ^ 2 * (s + 1) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hR hRb 2
  have h3 : (s + 1) ^ 2 * (25 * s + 2) ≤ 27 * (s + 1) ^ 3 := by nlinarith
  have hA : R ≤ 2 * b * (s ^ 3 + 1) := by nlinarith
  have hB : 2 * R ^ 2 * (25 * s + 2) ≤ 216 * b ^ 2 * (s ^ 3 + 1) := by
    calc 2 * R ^ 2 * (25 * s + 2) ≤ 2 * (b ^ 2 * (s + 1) ^ 2) * (25 * s + 2) := by gcongr
      _ = 2 * b ^ 2 * ((s + 1) ^ 2 * (25 * s + 2)) := by ring
      _ ≤ 2 * b ^ 2 * (27 * (s + 1) ^ 3) := by gcongr
      _ ≤ 2 * b ^ 2 * (27 * (4 * (s ^ 3 + 1))) := by gcongr
      _ = 216 * b ^ 2 * (s ^ 3 + 1) := by ring
  linarith

/-- The factor-sum powers: `(R ρ + exp(2R(log 2 + 25 s + 1)))^R ≤ exp(A(s³ + 1))`. -/
theorem factor_pow_le {s R b ρ : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hRb : R ≤ b * (s + 1)) (hρs : ρ ≤ Real.log 2 + 25 * s + 1) {Q : ℝ}
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ R * ρ + Real.exp (2 * R * (Real.log 2 + 25 * s + 1))) (n : ℕ)
    (hn : (n : ℝ) ≤ R) :
    Q ^ n ≤ Real.exp ((2 * b + 216 * b ^ 2) * (s ^ 3 + 1)) := by
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set u := 2 * R * (Real.log 2 + 25 * s + 1) with hu
  have hu0 : 0 ≤ u := by positivity
  have h1 : R * ρ ≤ Real.exp u := by
    calc R * ρ ≤ u := by
          rw [hu]; nlinarith
      _ ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hQ' : Q ≤ Real.exp (1 + u) := by
    rw [Real.exp_add]
    have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith [Real.exp_pos u]
  have hpow : Q ^ n ≤ Real.exp (n * (1 + u)) := by
    rw [Real.exp_nat_mul]  -- `exp (n * a) = exp a ^ n`
    exact pow_le_pow_left₀ hQ0 hQ' n
  refine hpow.trans (Real.exp_le_exp.2 ?_)
  have hnu : (n : ℝ) * (1 + u) ≤ R * (1 + u) := mul_le_mul_of_nonneg_right hn (by linarith)
  have : R * (1 + u) ≤ R + 2 * R ^ 2 * (25 * s + 2) := by
    rw [hu]; nlinarith
  linarith [poly_le hs hR hb hRb]

/-! ### The endpoint bounds are `L^{o(1)}` -/

/-- `N' ≤ |C_N| s + 1`. -/
theorem inertPerCluster_le {K : ℕ} (hK : 1 ≤ K) {CN x : ℝ} (hs : 0 ≤ logLogLog x) :
    (inertPerCluster K CN x : ℝ) ≤ |CN| * logLogLog x + 1 := by
  unfold inertPerCluster
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : CN * logLogLog x / K ≤ |CN| * logLogLog x := by
    rw [div_le_iff₀ (by linarith)]
    have : CN * logLogLog x ≤ |CN| * logLogLog x :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hs
    have : |CN| * logLogLog x ≤ |CN| * logLogLog x * K :=
      le_mul_of_one_le_right (by positivity) hK'
    linarith
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ |CN| * logLogLog x by positivity)
  have h3 : ⌈CN * logLogLog x / K⌉₊ ≤ ⌈|CN| * logLogLog x⌉₊ := Nat.ceil_mono h1
  have h4 : (⌈CN * logLogLog x / K⌉₊ : ℝ) ≤ ⌈|CN| * logLogLog x⌉₊ := by exact_mod_cast h3
  linarith

/-- `S_B ≤ C_s T^{60}` with `C_s = (2/c + 1)³ + (E₂ + 2)³`. -/
theorem slotBound_le_mul {c E₂ x : ℝ} (hc : 0 < c) (hE₂ : 0 ≤ E₂) (hT : 1 ≤ logLog x) :
    slotBound c E₂ x ≤ ((2 / c + 1) ^ 3 + (E₂ + 2) ^ 3) * logLog x ^ 60 := by
  unfold slotBound
  set T := logLog x
  have hT20 : 1 ≤ T ^ 20 := one_le_pow₀ hT
  have hc2 : 0 ≤ 2 / c := by positivity
  have h1 : 2 * T ^ 20 / c + 1 ≤ (2 / c + 1) * T ^ 20 := by
    have : 2 * T ^ 20 / c = 2 / c * T ^ 20 := by ring
    rw [this]; nlinarith
  have h2 : T + E₂ + 1 ≤ (E₂ + 2) * T ^ 20 := by
    have : T ≤ T ^ 20 := le_self_pow₀ hT (by norm_num)
    nlinarith
  have h1' : (2 * T ^ 20 / c + 1) ^ 3 ≤ ((2 / c + 1) * T ^ 20) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h1 3
  have h2' : (T + E₂ + 1) ^ 3 ≤ ((E₂ + 2) * T ^ 20) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h2 3
  have e1 : ((2 / c + 1) * T ^ 20) ^ 3 = (2 / c + 1) ^ 3 * T ^ 60 := by ring
  have e2 : ((E₂ + 2) * T ^ 20) ^ 3 = (E₂ + 2) ^ 3 * T ^ 60 := by ring
  rw [e1] at h1'
  rw [e2] at h2'
  linarith

/-- `2^{K N'} (2/(1-q))^{K(N' + 1)} ≤ exp(K (log 2 + log(2/(1-q))) (|C_N| s + 2))`. -/
theorem exp_factors_le {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) {K : ℕ} (hK : 1 ≤ K) {CN x : ℝ}
    (hs : 0 ≤ logLogLog x) :
    2 ^ (K * inertPerCluster K CN x) * ((2 / (1 - q)) ^ K *
        (2 / (1 - q)) ^ (K * inertPerCluster K CN x)) ≤
      Real.exp (K * (Real.log 2 + Real.log (2 / (1 - q))) * (|CN| * logLogLog x + 2)) := by
  have hb : 1 ≤ 2 / (1 - q) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hb0 : 0 < 2 / (1 - q) := by linarith
  have hlb : 0 ≤ Real.log (2 / (1 - q)) := Real.log_nonneg hb
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hN' := inertPerCluster_le (CN := CN) hK hs
  set N' := inertPerCluster K CN x
  rw [← pow_add, ← Real.rpow_natCast, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num),
    Real.rpow_def_of_pos hb0, ← Real.exp_add]
  apply Real.exp_le_exp.2
  push_cast
  have h1 := mul_le_mul_of_nonneg_left hN' (show 0 ≤ (K : ℝ) * Real.log 2 by positivity)
  have hN2 : (N' : ℝ) + 1 ≤ |CN| * logLogLog x + 2 := by linarith
  have h2 := mul_le_mul_of_nonneg_left hN2
    (show 0 ≤ (K : ℝ) * Real.log (2 / (1 - q)) by positivity)
  have h3 : 0 ≤ (K : ℝ) * Real.log 2 := by positivity
  nlinarith

/-- The endpoint bound is at most `exp(A (s² + 1))`. -/
theorem endBound_le_exp {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) {K : ℕ} (hK : 1 ≤ K)
    {CN c E₂ : ℝ} (hc : 0 < c) (hE₂ : 0 ≤ E₂) {x : ℝ} (hT : 1 ≤ logLog x)
    (hs : 0 ≤ logLogLog x) :
    endBound q K CN c E₂ x ≤ Real.exp ((K * (Real.log 2 + Real.log (2 / (1 - q))) *
      (|CN| + 2) + 60 + |Real.log ((2 / c + 1) ^ 3 + (E₂ + 2) ^ 3)|) *
        (logLogLog x ^ 2 + 1)) := by
  set s := logLogLog x
  set T := logLog x
  have hT0 : 0 < T := by linarith
  set Cs := (2 / c + 1) ^ 3 + (E₂ + 2) ^ 3 with hCs
  have hc2 : 0 ≤ 2 / c := by positivity
  have hCs1 : 1 ≤ Cs := by
    have : 1 ≤ (2 / c + 1) ^ 3 := one_le_pow₀ (by linarith)
    have : 0 ≤ (E₂ + 2) ^ 3 := by positivity
    linarith
  have hT60 : T ^ 60 = Real.exp (60 * s) := by
    have : T = Real.exp s := (exp_logLogLog hT0).symm
    rw [this, ← Real.exp_nat_mul]; norm_num
  have hSB := slotBound_le_mul hc hE₂ hT
  have hexp := exp_factors_le hq hq₁ hK (CN := CN) hs
  have hpos : 0 ≤ slotBound c E₂ x := (zero_le_one).trans (slotBound_pos hc hE₂ hT0.le)
  have hend : endBound q K CN c E₂ x ≤
      Real.exp (K * (Real.log 2 + Real.log (2 / (1 - q))) * (|CN| * s + 2)) *
        (Real.exp (Real.log Cs) * Real.exp (60 * s)) := by
    unfold endBound normBound
    rw [Real.exp_log (by linarith), ← hT60]
    calc 2 ^ (K * inertPerCluster K CN x) * (2 / (1 - q)) ^ K *
          ((2 / (1 - q)) ^ (K * inertPerCluster K CN x) * slotBound c E₂ x)
        = 2 ^ (K * inertPerCluster K CN x) * ((2 / (1 - q)) ^ K *
            (2 / (1 - q)) ^ (K * inertPerCluster K CN x)) * slotBound c E₂ x := by ring
      _ ≤ _ := mul_le_mul hexp hSB hpos (by positivity)
  refine hend.trans ?_
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hs2 : s ≤ s ^ 2 + 1 := by nlinarith [sq_nonneg (s - 1)]
  have hs1 : 1 ≤ s ^ 2 + 1 := by nlinarith
  set l := K * (Real.log 2 + Real.log (2 / (1 - q))) with hl
  have hb : 1 ≤ 2 / (1 - q) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hKl : 0 ≤ l := by
    have := Real.log_nonneg hb
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  have hCN : 0 ≤ |CN| := abs_nonneg _
  have e2 : |CN| * s + 2 ≤ (|CN| + 2) * (s ^ 2 + 1) := by nlinarith
  have e3 : l * (|CN| * s + 2) ≤ l * ((|CN| + 2) * (s ^ 2 + 1)) :=
    mul_le_mul_of_nonneg_left e2 hKl
  have e4 : 60 * s ≤ 60 * (s ^ 2 + 1) := by linarith
  have e5 : Real.log Cs ≤ |Real.log Cs| * (s ^ 2 + 1) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hs1)
  have : (l * (|CN| + 2) + 60 + |Real.log Cs|) * (s ^ 2 + 1) =
      l * ((|CN| + 2) * (s ^ 2 + 1)) + 60 * (s ^ 2 + 1) + |Real.log Cs| * (s ^ 2 + 1) := by ring
  linarith

/-! ### Pointwise inputs at one scale -/

/-- Candidate primes lie in `primesIoc 1 (exp(L^{0.45}))`. -/
theorem candidatePrimes_subset {x : ℝ} (hL : 1 ≤ Real.log x) :
    candidatePrimes x ⊆ primesIoc 1 (Real.exp (Real.log x ^ (45 / 100 : ℝ))) := fun p hp => by
  obtain ⟨hpp, -, hle⟩ := mem_candidatePrimes hL hp
  exact mem_primesIoc_one.2 ⟨hpp, hle⟩

/-- `∑_P log p / p ≤ L^{0.45} + E`, by Mertens' first theorem. -/
theorem sum_candidate_log_le {E x : ℝ} (hL : 1 ≤ Real.log x)
    (hE : ∀ y z : ℝ, 1 ≤ y → y ≤ z →
      |∑ p ∈ primesIoc y z, Real.log p / p - Real.log (z / y)| ≤ E) :
    ∑ p ∈ candidatePrimes x, Real.log p / p ≤ Real.log x ^ (45 / 100 : ℝ) + E := by
  have hz : (1 : ℝ) ≤ Real.exp (Real.log x ^ (45 / 100 : ℝ)) := Real.one_le_exp (by positivity)
  have h := hE 1 _ le_rfl hz
  rw [div_one, Real.log_exp, abs_le] at h
  refine (sum_le_sum_of_subset_of_nonneg (candidatePrimes_subset hL) fun p hp _ => ?_).trans
    (by linarith [h.2])
  have := (mem_primesIoc_one.1 hp).1.one_lt.le
  have : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast this)
  positivity

/-- `∑_P 1/p ≤ log(L^{0.45}/log 2) + E/log 2 + 1/2`, by Mertens' second theorem. -/
theorem sum_candidate_inv_le {E x : ℝ} (hL : 1 ≤ Real.log x)
    (hE : ∀ y z : ℝ, 2 ≤ y → y ≤ z →
      |∑ p ∈ primesIoc y z, (1 : ℝ) / p - Real.log (Real.log z / Real.log y)| ≤ E / Real.log y) :
    ∑ p ∈ candidatePrimes x, (1 : ℝ) / p ≤
      Real.log (Real.log x ^ (45 / 100 : ℝ) / Real.log 2) + E / Real.log 2 + 1 / 2 := by
  have hL45 : 1 ≤ Real.log x ^ (45 / 100 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hz : (2 : ℝ) ≤ Real.exp (Real.log x ^ (45 / 100 : ℝ)) := by
    have := Real.add_one_le_exp (Real.log x ^ (45 / 100 : ℝ)); linarith
  have h := hE 2 _ le_rfl hz
  rw [Real.log_exp, abs_le] at h
  have hsplit := sum_primesIoc_add (fun p => (1 : ℝ) / p) (show (1 : ℝ) ≤ 2 by norm_num) hz
  have h12 : ∑ p ∈ primesIoc 1 2, (1 : ℝ) / p ≤ 1 / 2 := by
    have : primesIoc 1 2 = {2} := by
      ext p
      rw [mem_primesIoc, mem_singleton]
      constructor
      · rintro ⟨hp, h1, h2⟩
        have := hp.two_le
        have : p ≤ 2 := by exact_mod_cast h2
        omega
      · rintro rfl; norm_num
    rw [this, sum_singleton]; norm_num
  refine (sum_le_sum_of_subset_of_nonneg (candidatePrimes_subset hL) fun p _ _ => by
    positivity).trans ?_
  linarith [h.2]

/-- The grid reaches `M`: `M ≤ x^γ (1 + δ)^A` for `A = ⌈2 log(M + 1)/δ⌉`. -/
theorem gridPt_ge {x γ δ : ℝ} (hxγ : 1 ≤ x ^ γ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) :
    (N : ℝ) ≤ gridPt x γ δ ⌈2 * Real.log (N + 1) / δ⌉₊ := by
  unfold gridPt
  set A := ⌈2 * Real.log (N + 1) / δ⌉₊
  have hexp : Real.exp (δ / 2) ≤ 1 + δ := by
    have h := Real.abs_exp_sub_one_sub_id_le (show |δ / 2| ≤ 1 by
      rw [abs_of_pos (by positivity)]; linarith)
    rw [abs_le] at h
    nlinarith
  have hA : 2 * Real.log (N + 1) / δ ≤ A := Nat.le_ceil _
  have h1 : (N : ℝ) + 1 ≤ (1 + δ) ^ A := by
    calc (N : ℝ) + 1 = Real.exp (Real.log (N + 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (A * (δ / 2)) := by
          apply Real.exp_le_exp.2
          rw [div_le_iff₀ hδ0] at hA
          nlinarith
      _ = Real.exp (δ / 2) ^ A := by rw [← Real.exp_nat_mul]
      _ ≤ (1 + δ) ^ A := pow_le_pow_left₀ (by positivity) hexp A
  have : (1 + δ) ^ A ≤ x ^ γ * (1 + δ) ^ A := le_mul_of_one_le_left (by positivity) hxγ
  linarith

/-- The `P`-numbers are rare: `w^θ ∏_P (1 - p^{-θ})⁻¹ ≤ (c₃ / log Y) w` for `w ≥ x^γ`, with
`θ = 1 - L^{-0.45}`, once `γ L^{0.55}` beats `2e ∑_P 1/p + log(log Y / c₃)`. -/
theorem rankin_small {x γ c₃ S₀ : ℝ} (hx : 1 < x) (hL : 1 ≤ Real.log x)
    (hL28 : 2 ≤ Real.log x ^ (28 / 100 : ℝ))
    (hc₃ : 0 < c₃) (hlogY : 0 < Real.log (proxyCutoff x))
    (hS : ∑ p ∈ candidatePrimes x, (1 : ℝ) / p ≤ S₀)
    (hbig : 2 * Real.exp 1 * S₀ + Real.log (Real.log (proxyCutoff x) / c₃) ≤
      γ * Real.log x ^ (55 / 100 : ℝ))
    (w : ℝ) (hw : x ^ γ ≤ w) :
    w ^ (1 - Real.log x ^ (-(45 / 100) : ℝ)) *
        ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-(1 - Real.log x ^ (-(45 / 100) : ℝ))))⁻¹ ≤
      c₃ / Real.log (proxyCutoff x) * w := by
  set η := Real.log x ^ (-(45 / 100) : ℝ) with hη
  have hL0 : 0 < Real.log x := by linarith
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
  have hxγ : 0 < x ^ γ := by positivity
  have hw0 : 0 < w := lt_of_lt_of_le hxγ hw
  -- `w^{1-η} ≤ w exp(-γ L^{0.55})`
  have hwθ : w ^ (1 - η) ≤ w * Real.exp (-(γ * Real.log x ^ (55 / 100 : ℝ))) := by
    rw [Real.rpow_sub hw0, Real.rpow_one, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hw0.le
    rw [← Real.rpow_neg hw0.le]
    calc w ^ (-η) ≤ (x ^ γ) ^ (-η) := Real.rpow_le_rpow_of_nonpos hxγ hw (by linarith)
      _ = Real.exp (-(γ * Real.log x ^ (55 / 100 : ℝ))) := by
          rw [← Real.rpow_mul (by linarith), Real.rpow_def_of_pos (by linarith)]
          congr 1
          have e : Real.log x * η = Real.log x ^ (55 / 100 : ℝ) := by
            rw [hη, ← Real.rpow_one_add' hL0.le (by norm_num)]; norm_num
          calc Real.log x * (γ * -η) = -(γ * (Real.log x * η)) := by ring
            _ = _ := by rw [e]
  -- `p^{-θ} ≤ e/p` on the candidate primes
  have hpθ : ∀ p ∈ candidatePrimes x, (p : ℝ) ^ (-(1 - η)) ≤ Real.exp 1 * (1 / p) := by
    intro p hp
    obtain ⟨hpp, hlo, hle⟩ := mem_candidatePrimes hL hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    rw [show -(1 - η) = η + -1 by ring, Real.rpow_add hp0, Real.rpow_neg_one, ← div_eq_mul_inv,
      mul_one_div]
    refine div_le_div_of_nonneg_right ?_ hp0.le
    rw [Real.rpow_def_of_pos hp0]
    apply Real.exp_le_exp.2
    have hlogp : Real.log p ≤ Real.log x ^ (45 / 100 : ℝ) := by
      rw [← Real.log_exp (Real.log x ^ (45 / 100 : ℝ))]
      exact Real.log_le_log hp0 hle
    calc Real.log p * η ≤ Real.log x ^ (45 / 100 : ℝ) * η :=
          mul_le_mul_of_nonneg_right hlogp hη0.le
      _ = 1 := by
          rw [hη, ← Real.rpow_add hL0]; norm_num
  have hhalf : ∀ p ∈ candidatePrimes x, (p : ℝ) ^ (-(1 - η)) ≤ 1 / 2 := by
    intro p hp
    obtain ⟨hpp, hlo, -⟩ := mem_candidatePrimes hL hp
    have hp6 : (6 : ℝ) ≤ p := by
      have h2 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have h3 : Real.exp 2 ≤ Real.exp (Real.log x ^ (28 / 100 : ℝ)) := Real.exp_le_exp.2 hL28
      have h4 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    have := hpθ p hp
    have : Real.exp 1 * (1 / p) ≤ 1 / 2 := by
      have := Real.exp_one_lt_d9
      rw [mul_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hPiθ : ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-(1 - η)))⁻¹ ≤
      Real.exp (2 * Real.exp 1 * S₀) := by
    refine (prod_inv_one_sub_le_exp _ _ (fun p hp => by positivity) hhalf).trans ?_
    apply Real.exp_le_exp.2
    have : ∑ p ∈ candidatePrimes x, (p : ℝ) ^ (-(1 - η)) ≤ Real.exp 1 * S₀ := by
      rw [← mul_le_mul_iff_of_pos_left (show (0 : ℝ) < 1 by norm_num)]
      calc 1 * ∑ p ∈ candidatePrimes x, (p : ℝ) ^ (-(1 - η))
          ≤ ∑ p ∈ candidatePrimes x, Real.exp 1 * (1 / p) := by
            rw [one_mul]; exact sum_le_sum hpθ
        _ = Real.exp 1 * ∑ p ∈ candidatePrimes x, (1 : ℝ) / p := by rw [mul_sum]
        _ ≤ 1 * (Real.exp 1 * S₀) := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left hS (Real.exp_pos 1).le
    linarith
  have hPiθ0 : 0 ≤ ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-(1 - η)))⁻¹ :=
    prod_nonneg fun p hp => by have := hhalf p hp; rw [inv_nonneg]; linarith
  calc w ^ (1 - η) * ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-(1 - η)))⁻¹
      ≤ w * Real.exp (-(γ * Real.log x ^ (55 / 100 : ℝ))) * Real.exp (2 * Real.exp 1 * S₀) :=
        mul_le_mul hwθ hPiθ hPiθ0 (by positivity)
    _ = w * Real.exp (2 * Real.exp 1 * S₀ - γ * Real.log x ^ (55 / 100 : ℝ)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ w * Real.exp (-Real.log (Real.log (proxyCutoff x) / c₃)) := by
        gcongr; linarith
    _ = c₃ / Real.log (proxyCutoff x) * w := by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div, mul_comm]

end Erdos408.TypeII
