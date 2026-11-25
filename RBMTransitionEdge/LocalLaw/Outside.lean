module

public import RBMTransitionEdge.LocalLaw.LocalLaw
public import RBMTransitionEdge.LocalLaw.Far
public import RBMTransitionEdge.Det.Density

@[expose] public section

/-!
# Outside the spectrum

The improved averaged bound outside the spectrum and the spectral inclusion of Lemma 2.9 [lem_loc],
the edge inputs of (2.24) [eq:rigidity].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `N^a ≥ C` for all large `N`, when `a > 0`. -/
private lemma Outside_ev (C a : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C ≤ (N : ℝ) ^ a := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop C)

/-- `‖Λ‖ ≤ 1/10` for `Λ = lam D N A` once `N^{δ_A} ≥ 20` and `‖A‖ ≤ N^{-δ_A}`. -/
private lemma Outside_lam_small (D N : ℕ) (δA : ℝ) (hN : 1 ≤ N) (h20 : (20 : ℝ) ≤ (N : ℝ) ^ δA)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : opNorm A ≤ (N : ℝ) ^ (-δA)) :
    opNorm (lam D N A) ≤ 1 / 10 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := opNorm_lam_le D N A
  have h4 : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
    rw [Real.rpow_neg hN0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h20
  linarith

/-- The normalized trace of a difference. -/
private lemma Outside_ntr_sub {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P - Q) = ntr P - ntr Q := by
  simp [ntr, Matrix.trace_sub, mul_sub]

/-- `|⟨R B⟩| ≤ |x|_∞` for `B = Σ_a c_a E_a` with `|c_a| ≤ 1` and `x = blockTr R`, since
`⟨R B⟩ = D⁻¹ Σ_a c_a x_a`. -/
private lemma Outside_ntr_le_blockTr (D N : ℕ) (hD : 1 ≤ D) (R : Matrix (Idx D N) (Idx D N) ℂ)
    (c : Fin D → ℂ) (hc : ∀ a, ‖c a‖ ≤ 1) :
    ‖ntr (R * ∑ a, c a • Ea D N a)‖ ≤ ‖blockTr D N R‖ := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have e : ntr (R * ∑ a, c a • Ea D N a) = (D : ℂ)⁻¹ * ∑ a, c a * blockTr D N R a := by
    unfold blockTr
    have h1 : ∀ a, ntr (R * (c a • Ea D N a)) = c a * ntr (Ea D N a * R) := by
      intro a
      simp only [Matrix.mul_smul, ntr, Matrix.trace_smul, smul_eq_mul]
      rw [Matrix.trace_mul_comm R (Ea D N a)]
      ring
    rw [Matrix.mul_sum]
    have h2 : ntr (∑ a, R * (c a • Ea D N a)) = ∑ a, ntr (R * (c a • Ea D N a)) := by
      simp [ntr, Matrix.trace_sum, Finset.mul_sum]
    rw [h2]
    simp only [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    field_simp
  rw [e, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ a, c a * blockTr D N R a‖ ≤ D * ‖blockTr D N R‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖c a * blockTr D N R a‖ ≤ ∑ _a : Fin D, ‖blockTr D N R‖ := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul]
          calc ‖c a‖ * ‖blockTr D N R a‖ ≤ 1 * ‖blockTr D N R‖ :=
                mul_le_mul (hc a) (norm_le_pi_norm (blockTr D N R) a) (norm_nonneg _)
                  zero_le_one
            _ = ‖blockTr D N R‖ := one_mul _
      _ = D * ‖blockTr D N R‖ := by simp
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  calc (D : ℝ)⁻¹ * ‖∑ a, c a * blockTr D N R a‖ ≤ (D : ℝ)⁻¹ * (D * ‖blockTr D N R‖) := by gcongr
    _ = ‖blockTr D N R‖ := by field_simp

/-- Outside the spectrum `|Im m(z)| ≤ K |η| / √(κ + |η|)` on both half planes, from the bound
for `Im z > 0` (the square-root density (A.1) [square_root_density]) and the reflection
`m(z̄) = conj m(z)` of Definition 2.7 [defn_Mm]. -/
private lemma Outside_mExt_im_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (τ K : ℝ) (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian)
    (hsq : ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im → z.re ∉ Set.Icc (Eminus Λ) (Eplus Λ) →
      (mSol Λ z).im ≤ K * (z.im / Real.sqrt (kappa Λ z.re + z.im)))
    (z : ℂ) (hz : ‖z‖ ≤ τ⁻¹) (hz0 : z.im ≠ 0) (hre : z.re ∉ Set.Icc (Eminus Λ) (Eplus Λ)) :
    |(mExt Λ z).im| ≤ K * (|z.im| / Real.sqrt (kappa Λ z.re + |z.im|)) := by
  rcases lt_or_gt_of_ne hz0 with h | h
  · have h' : 0 < (star z).im := by simpa using h
    have hs := mSol_spec Λ hΛ (star z) h'
    have e : mExt Λ z = star (mSol Λ (star z)) := by simp [mExt, h, h.not_gt]
    have hb := hsq (star z) (by simpa using hz) h' (by simpa using hre)
    rw [e, abs_of_neg h]
    have e2 : (star (mSol Λ (star z))).im = -(mSol Λ (star z)).im := by simp
    rw [e2, abs_neg, abs_of_pos hs.1]
    simpa using hb
  · have hs := mSol_spec Λ hΛ z h
    have e : mExt Λ z = mSol Λ z := by simp [mExt, h]
    have hb := hsq z hz h hre
    rw [e, abs_of_pos hs.1, abs_of_pos h]
    exact hb

/-- Scalar form of the reduction in `aver_local_outside`: with `|Im m| ≤ K e / s`, `s² = κ + e`,
`K ≥ 1`, one has `Ψ²/s ≤ 2K (1/(n(κ+e)) + 1/((ne)² s))` for `Ψ = √(|Im m|/(ne)) + 1/(ne)`. -/
private lemma Outside_psi_sq_le (n e s K κ mi : ℝ) (hn : 0 < n) (he : 0 < e) (hs : 0 < s)
    (hK : 1 ≤ K) (hs2 : s ^ 2 = κ + e) (hmi0 : 0 ≤ mi) (hmi : mi ≤ K * (e / s)) :
    (Real.sqrt (mi / (n * e)) + 1 / (n * e)) ^ 2 / s ≤
      2 * K * (1 / (n * (κ + e)) + 1 / ((n * e) ^ 2 * s)) := by
  have hne : 0 < n * e := mul_pos hn he
  have hx : 0 ≤ mi / (n * e) := div_nonneg hmi0 hne.le
  have hy : 0 ≤ 1 / (n * e) := by positivity
  have h1 : (Real.sqrt (mi / (n * e)) + 1 / (n * e)) ^ 2 ≤
      2 * (mi / (n * e)) + 2 * (1 / (n * e)) ^ 2 := by
    have := Real.sq_sqrt hx
    nlinarith [sq_nonneg (Real.sqrt (mi / (n * e)) - 1 / (n * e))]
  have h2 : mi / (n * e) ≤ K / (n * s) := by
    rw [div_le_iff₀ hne]
    calc mi ≤ K * (e / s) := hmi
      _ = K / (n * s) * (n * e) := by field_simp
  have h3 : (Real.sqrt (mi / (n * e)) + 1 / (n * e)) ^ 2 ≤
      2 * (K / (n * s)) + 2 * (1 / (n * e)) ^ 2 := by linarith
  rw [div_le_iff₀ hs]
  refine h3.trans ?_
  have hs0 : s ≠ 0 := hs.ne'
  have e1 : 2 * K * (1 / (n * (κ + e)) + 1 / ((n * e) ^ 2 * s)) * s =
      2 * (K / (n * s)) + 2 * K * (1 / (n * e)) ^ 2 := by
    rw [← hs2]
    field_simp
  rw [e1]
  have : 2 * (1 / (n * e)) ^ 2 ≤ 2 * K * (1 / (n * e)) ^ 2 := by
    have : 0 ≤ (1 / (n * e)) ^ 2 := sq_nonneg _
    nlinarith
  linarith

/-- The exclusion inequality of the spectral inclusion in the variables `r = N^{1/3}`,
`q = N^{a/8}`, `η = q/r²`, `κ ≥ q⁸/r²` (that is `κ ≥ N^{-2/3+a}`): the bound
`q² (1/(r³(κ+η)) + 1/((r³η)²√(κ+η))) + K η/√(κ+η)` is below `1/(D r³ η)` once `q² > D (K+2)`. -/
private lemma Outside_R6_alg (D K r q η κ : ℝ) (hD : 0 < D) (hK : 0 ≤ K) (hr : 0 < r)
    (hq : 1 ≤ q) (hη : η = q / r ^ 2) (hκ : q ^ 8 / r ^ 2 ≤ κ) (hbig : D * (K + 2) < q ^ 2) :
    q ^ 2 * (1 / (r ^ 3 * (κ + η)) + 1 / ((r ^ 3 * η) ^ 2 * Real.sqrt (κ + η))) +
      K * (η / Real.sqrt (κ + η)) < 1 / (D * r ^ 3 * η) := by
  have hq0 : 0 < q := by linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hκ0 : 0 < q ^ 8 / r ^ 2 := by positivity
  have hκη : q ^ 8 / r ^ 2 ≤ κ + η := by linarith
  have hs2 : Real.sqrt (κ + η) ^ 2 = κ + η := Real.sq_sqrt (by linarith)
  have hspos : 0 < Real.sqrt (κ + η) := Real.sqrt_pos.mpr (by linarith)
  have hs : q ^ 4 / r ≤ Real.sqrt (κ + η) := by
    refine Real.le_sqrt_of_sq_le ?_
    have : (q ^ 4 / r) ^ 2 = q ^ 8 / r ^ 2 := by field_simp
    rw [this]; exact hκη
  have hqr : 0 < q ^ 4 / r := by positivity
  -- the three terms
  have t1 : K * (η / Real.sqrt (κ + η)) ≤ K / (r * q ^ 3) := by
    have : η / Real.sqrt (κ + η) ≤ η / (q ^ 4 / r) :=
      div_le_div_of_nonneg_left hη0.le hqr hs
    have e : η / (q ^ 4 / r) = 1 / (r * q ^ 3) := by rw [hη]; field_simp
    calc K * (η / Real.sqrt (κ + η)) ≤ K * (1 / (r * q ^ 3)) := by
          rw [← e]; exact mul_le_mul_of_nonneg_left this hK
      _ = K / (r * q ^ 3) := by ring
  have t2 : q ^ 2 * (1 / (r ^ 3 * (κ + η))) ≤ 1 / (r * q ^ 3) := by
    have h1 : r ^ 3 * (q ^ 8 / r ^ 2) ≤ r ^ 3 * (κ + η) :=
      mul_le_mul_of_nonneg_left hκη (by positivity)
    have h2 : 1 / (r ^ 3 * (κ + η)) ≤ 1 / (r ^ 3 * (q ^ 8 / r ^ 2)) :=
      one_div_le_one_div_of_le (by positivity) h1
    have e : q ^ 2 * (1 / (r ^ 3 * (q ^ 8 / r ^ 2))) = 1 / (r * q ^ 6) := by field_simp
    have h3 : 1 / (r * q ^ 6) ≤ 1 / (r * q ^ 3) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq (by norm_num)) hr.le
    calc q ^ 2 * (1 / (r ^ 3 * (κ + η))) ≤ q ^ 2 * (1 / (r ^ 3 * (q ^ 8 / r ^ 2))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 / (r * q ^ 6) := e
      _ ≤ 1 / (r * q ^ 3) := h3
  have t3 : q ^ 2 * (1 / ((r ^ 3 * η) ^ 2 * Real.sqrt (κ + η))) ≤ 1 / (r * q ^ 3) := by
    have e1 : (r ^ 3 * η) ^ 2 = r ^ 2 * q ^ 2 := by rw [hη]; field_simp
    have h1 : (r ^ 3 * η) ^ 2 * (q ^ 4 / r) ≤ (r ^ 3 * η) ^ 2 * Real.sqrt (κ + η) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    have h2 : 1 / ((r ^ 3 * η) ^ 2 * Real.sqrt (κ + η)) ≤ 1 / ((r ^ 3 * η) ^ 2 * (q ^ 4 / r)) :=
      one_div_le_one_div_of_le (by positivity) h1
    have e : q ^ 2 * (1 / ((r ^ 3 * η) ^ 2 * (q ^ 4 / r))) = 1 / (r * q ^ 4) := by
      rw [e1]; field_simp
    have h3 : 1 / (r * q ^ 4) ≤ 1 / (r * q ^ 3) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq (by norm_num)) hr.le
    calc q ^ 2 * (1 / ((r ^ 3 * η) ^ 2 * Real.sqrt (κ + η)))
        ≤ q ^ 2 * (1 / ((r ^ 3 * η) ^ 2 * (q ^ 4 / r))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 / (r * q ^ 4) := e
      _ ≤ 1 / (r * q ^ 3) := h3
  have hfin : (K + 2) / (r * q ^ 3) < 1 / (D * r ^ 3 * η) := by
    have e2 : 1 / (D * r ^ 3 * η) = 1 / (D * r * q) := by rw [hη]; field_simp
    rw [e2, div_lt_div_iff₀ (by positivity) (by positivity)]
    have h1 : (K + 2) * (D * r * q) = D * (K + 2) * (r * q) := by ring
    have h2 : 1 * (r * q ^ 3) = q ^ 2 * (r * q) := by ring
    rw [h1, h2]
    exact mul_lt_mul_of_pos_right hbig (by positivity)
  have hsum : q ^ 2 * (1 / (r ^ 3 * (κ + η)) + 1 / ((r ^ 3 * η) ^ 2 * Real.sqrt (κ + η))) +
      K * (η / Real.sqrt (κ + η)) ≤ (K + 2) / (r * q ^ 3) := by
    rw [mul_add]
    have : (K + 2) / (r * q ^ 3) = K / (r * q ^ 3) + 1 / (r * q ^ 3) + 1 / (r * q ^ 3) := by
      ring
    rw [this]
    linarith
  exact lt_of_le_of_lt hsum hfin

/-- `N^{-2/3+a/8} = q/r²`, `N^{-2/3+a} = q⁸/r²`, `N = r³`, `N^{a/4} = q²` for `r = N^{1/3}`,
`q = N^{a/8}`: the substitution that turns the exponents of the spectral inclusion into the
variables of `Outside_R6_alg`. -/
private lemma Outside_pow_sub (N a : ℝ) (hN : 0 < N) :
    N = (N ^ (1 / 3 : ℝ)) ^ 3 ∧ N ^ (-(2 / 3 : ℝ) + a / 8) = N ^ (a / 8) / (N ^ (1 / 3 : ℝ)) ^ 2 ∧
      N ^ (-(2 / 3 : ℝ) + a) = (N ^ (a / 8)) ^ 8 / (N ^ (1 / 3 : ℝ)) ^ 2 ∧
      N ^ (a / 4) = (N ^ (a / 8)) ^ 2 := by
  have h3 : (N ^ (1 / 3 : ℝ)) ^ 3 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  have h2 : (N ^ (1 / 3 : ℝ)) ^ 2 = N ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  have h8 : (N ^ (a / 8)) ^ 8 = N ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  have h2' : (N ^ (a / 8)) ^ 2 = N ^ (a / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
    ring_nf
  refine ⟨h3.symm, ?_, ?_, h2'.symm⟩
  · rw [h2, Real.rpow_add hN, Real.rpow_neg hN.le]
    ring
  · rw [h2, h8, Real.rpow_add hN, Real.rpow_neg hN.le]
    ring

/-- The exclusion inequality of the spectral inclusion, in the exponents of the statement: for
`κ ≥ N^{-2/3+a}`, `η = N^{-2/3+a/8}` and `N^{a/4} > D (K+2)`,
`N^{a/4} (1/(N(κ+η)) + 1/((Nη)²√(κ+η))) + K η/√(κ+η) < 1/(D N η)`. -/
private lemma Outside_R6 (D K N a κ : ℝ) (hD : 0 < D) (hK : 0 ≤ K) (hN : 1 ≤ N) (ha : 0 < a)
    (hκ : N ^ (-(2 / 3 : ℝ) + a) ≤ κ) (hbig : D * (K + 2) < N ^ (a / 4)) :
    N ^ (a / 4) * (1 / (N * (κ + N ^ (-(2 / 3 : ℝ) + a / 8))) +
        1 / ((N * N ^ (-(2 / 3 : ℝ) + a / 8)) ^ 2 * Real.sqrt (κ + N ^ (-(2 / 3 : ℝ) + a / 8)))) +
      K * (N ^ (-(2 / 3 : ℝ) + a / 8) / Real.sqrt (κ + N ^ (-(2 / 3 : ℝ) + a / 8))) <
      1 / (D * N * N ^ (-(2 / 3 : ℝ) + a / 8)) := by
  have hN0 : 0 < N := by linarith
  obtain ⟨e3, eη, eκ, e4⟩ := Outside_pow_sub N a hN0
  have hr : 0 < N ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hq : 1 ≤ N ^ (a / 8) := Real.one_le_rpow hN (by positivity)
  have key := Outside_R6_alg D K (N ^ (1 / 3 : ℝ)) (N ^ (a / 8)) (N ^ (-(2 / 3 : ℝ) + a / 8)) κ
    hD hK hr hq eη (by rw [← eκ]; exact hκ) (by rw [← e4]; exact hbig)
  rw [← e3, ← e4] at key
  exact key

/-- The eigenvectors of a Hermitian matrix are unit vectors: `Σ_i |v_k(i)|² = 1`. -/
private lemma Outside_col_norm {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) (k : ι) : ∑ i, ‖(hX.eigenvectorBasis k) i‖ ^ 2 = 1 := by
  have h := hX.eigenvectorBasis.orthonormal.1 k
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  exact h

/-- A nonzero `λ_k(X)` is an eigenvalue of the Hermitian matrix `X`. -/
private lemma Outside_eigK_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (k : ℕ) (h : eigK X k ≠ 0) : ∃ (hX : X.IsHermitian) (i : ι), hX.eigenvalues i = eigK X k := by
  unfold eigK at h ⊢
  split_ifs at h ⊢ with hk
  · unfold eigs at h ⊢
    split_ifs at h ⊢ with hX
    · exact ⟨hX, (Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨k - 1, hk⟩,
        by simp [Matrix.IsHermitian.eigenvalues]⟩
    · exact absurd rfl h
  · exact absurd rfl h

/-- `Im⟨G(λ + iη)⟩ ≥ (nη)⁻¹` for an eigenvalue `λ` of a Hermitian matrix of size `n`: by the
spectral decomposition of the resolvent, `Im G_{ii} = Σ_k |v_k(i)|² η/|λ_k - z|²`, and the term
`k = i₀` already contributes `|v_{i₀}(i)|²/η`. -/
private lemma Outside_im_ntr {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) (i₀ : ι) (η : ℝ) (hη : 0 < η) :
    1 / ((Fintype.card ι : ℝ) * η) ≤
      (ntr (res X ((hX.eigenvalues i₀ : ℂ) + (η : ℂ) * Complex.I))).im := by
  set z : ℂ := (hX.eigenvalues i₀ : ℂ) + (η : ℂ) * Complex.I with hz
  have hz0 : 0 < z.im := by simp [hz, hη]
  have key : ∀ i k, ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i k *
      starRingEnd ℂ ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i k) /
        ((hX.eigenvalues k : ℂ) - z)).im =
      Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i k) *
        (η / Complex.normSq ((hX.eigenvalues k : ℂ) - z)) := by
    intro i k
    rw [Complex.mul_conj, div_eq_mul_inv, Complex.im_ofReal_mul, Complex.inv_im]
    simp [hz]
  have hn : ∀ i k, 0 ≤ Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i k) *
      (η / Complex.normSq ((hX.eigenvalues k : ℂ) - z)) :=
    fun i k => mul_nonneg (Complex.normSq_nonneg _) (div_nonneg hη.le (Complex.normSq_nonneg _))
  have hw : Complex.normSq ((hX.eigenvalues i₀ : ℂ) - z) = η ^ 2 := by
    rw [hz, Complex.normSq_apply]
    simp
    ring
  have hdiag : ∀ i, Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i i₀) / η ≤
      (res X z i i).im := by
    intro i
    rw [res_eq_sum_eig X hX z hz0 i i, Complex.im_sum]
    simp only [key]
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun k _ => hn i k) (Finset.mem_univ i₀))
    rw [hw]
    field_simp
  have hcol : ∑ i, Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i i₀) = 1 := by
    rw [← Outside_col_norm hX i₀]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_norm_sq]
    rfl
  have htr : (ntr (res X z)).im = ((Fintype.card ι : ℝ))⁻¹ * ∑ i, (res X z i i).im := by
    unfold ntr Matrix.trace
    rw [show ((Fintype.card ι : ℂ))⁻¹ = ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) by push_cast; rfl,
      Complex.im_ofReal_mul, Complex.im_sum]
    rfl
  rw [htr]
  have hsum : 1 / η ≤ ∑ i, (res X z i i).im := by
    calc 1 / η = ∑ i, Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i i₀) / η := by
          rw [← Finset.sum_div, hcol]
      _ ≤ _ := Finset.sum_le_sum fun i _ => hdiag i
  have e : 1 / ((Fintype.card ι : ℝ) * η) = ((Fintype.card ι : ℝ))⁻¹ * (1 / η) := by
    rw [one_div, mul_inv, one_div]
  rw [e]
  exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- The block projections sum to the identity. -/
private lemma Outside_sum_Ea (D N : ℕ) : ∑ a : Fin D, Ea D N a = 1 := by
  ext p q
  simp [Ea, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]

/-- An eigenvalue `λ` of `X = H' + Λ` with `|λ| < 4`, outside `[E⁻, E⁺]` and with
`κ_λ ≥ N^{-2/3+a}` is excluded by the averaged bound outside the spectrum at `B = I`: the point
`z = λ + iN^{-2/3+a/8}` has `Im⟨G(z)⟩ ≥ (D N η)⁻¹`, while the bound gives
`Im⟨G(z)⟩ ≤ Im m + |⟨G - M⟩| < (D N η)⁻¹`. -/
private lemma Outside_no_outlier (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ w : ℂ, ‖w‖ ≤ ((1 : ℝ) / 5)⁻¹ → 0 < w.im →
      w.re ∉ Set.Icc (Eminus (lam D N A)) (Eplus (lam D N A)) →
      (mSol (lam D N A) w).im ≤ K * (w.im / Real.sqrt (kappa (lam D N A) w.re + w.im)))
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hbig : (D : ℝ) * (K + 2) < (N : ℝ) ^ (a / 4))
    (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : X.IsHermitian) (i : Idx D N)
    (h4 : |hX.eigenvalues i| < 4)
    (hout : hX.eigenvalues i ∉ Set.Icc (Eminus (lam D N A)) (Eplus (lam D N A)))
    (hκ : (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ kappa (lam D N A) (hX.eigenvalues i))
    (haver : ∀ z ∈ specDom (1 / 5) N, z.re ∉ Set.Icc (Eminus (lam D N A)) (Eplus (lam D N A)) →
      ‖ntr ((res X z - MExt (lam D N A) z) * ∑ a, (fun _ : Fin D => (1 : ℂ)) a • Ea D N a)‖ ≤
        (N : ℝ) ^ (a / 4) * (1 / ((N : ℝ) * (kappa (lam D N A) z.re + |z.im|)) +
          1 / (((N : ℝ) * |z.im|) ^ 2 * Real.sqrt (kappa (lam D N A) z.re + |z.im|)))) :
    False := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hΛh := lam_isHermitian D N A
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  set l₀ : ℝ := hX.eigenvalues i with hl₀
  set η : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) + a / 8) with hη
  have hη0 : 0 < η := Real.rpow_pos_of_pos hN0 _
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  set z : ℂ := (l₀ : ℂ) + (η : ℂ) * Complex.I with hz
  have hzre : z.re = l₀ := by simp [hz]
  have hzim : z.im = η := by simp [hz]
  have hz0 : 0 < z.im := by rw [hzim]; exact hη0
  have hzD : z ∈ specDom (1 / 5) N := by
    refine ⟨?_, ?_⟩
    · have := Complex.norm_le_abs_re_add_abs_im z
      rw [hzre, hzim, abs_of_pos hη0] at this
      have h5 : ((1 : ℝ) / 5)⁻¹ = 5 := by norm_num
      rw [h5]
      linarith [abs_lt.mp h4]
    · rw [hzim, abs_of_pos hη0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hre : z.re ∉ Set.Icc (Eminus (lam D N A)) (Eplus (lam D N A)) := by
    rw [hzre]; exact hout
  have hb := haver z hzD hre
  have hI : 1 / ((Fintype.card (Idx D N) : ℝ) * η) ≤ (ntr (res X z)).im :=
    Outside_im_ntr hX i η hη0
  have hcard : (Fintype.card (Idx D N) : ℝ) = D * N := by
    simp [Fintype.card_prod, Fintype.card_fin]
  rw [hcard] at hI
  have hmM := (MExt_spec (lam D N A) hΛh z hz0.ne').1
  have hmim : (mExt (lam D N A) z).im ≤
      K * (z.im / Real.sqrt (kappa (lam D N A) z.re + z.im)) := by
    have e : mExt (lam D N A) z = mSol (lam D N A) z := by simp [mExt, hz0]
    rw [e]
    exact hK z hzD.1 hz0 hre
  have e1 : ntr ((res X z - MExt (lam D N A) z) * ∑ a, (fun _ : Fin D => (1 : ℂ)) a • Ea D N a) =
      ntr (res X z) - mExt (lam D N A) z := by
    simp only [one_smul, Outside_sum_Ea, Matrix.mul_one, Outside_ntr_sub]
    rw [← hmM]
  rw [e1] at hb
  have h1 : (ntr (res X z)).im - (mExt (lam D N A) z).im ≤
      ‖ntr (res X z) - mExt (lam D N A) z‖ := by
    have := Complex.abs_im_le_norm (ntr (res X z) - mExt (lam D N A) z)
    rw [Complex.sub_im] at this
    exact (le_abs_self _).trans this
  rw [hzre, hzim, abs_of_pos hη0] at hb
  rw [hzre, hzim] at hmim
  have hR := Outside_R6 D K N a (kappa (lam D N A) l₀) (by exact_mod_cast hD) hK0 hN1 ha hκ hbig
  rw [← hη] at hR
  linarith

/-- The improved averaged bound outside the spectrum (completing the step from (2.23)
[eq:aver_local] to (2.24) [eq:rigidity] in Lemma 2.9 [lem_loc]): for `B = Σ_a c_a E_a` with
`|c_a| ≤ 1`, outside an event of probability `≤ N^{-D'}`,
`|⟨(G - M) B⟩| ≤ N^{τ'} (1/(N(κ+|η|)) + 1/((N|η|)² √(κ+|η|)))` for all `z ∈ 𝐃(τ)` with
`Re z ∉ [E⁻, E⁺]` at once. -/
theorem aver_local_outside (D : ℕ) (hD : 1 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ c : Fin D → ℂ, (∀ a, ‖c a‖ ≤ 1) →
        μ {h | ∃ z ∈ specDom τ N, z.re ∉ Set.Icc (Eminus (lam D N A)) (Eplus (lam D N A)) ∧
            (N : ℝ) ^ τ' * (1 / ((N : ℝ) * (kappa (lam D N A) z.re + |z.im|)) +
              1 / (((N : ℝ) * |z.im|) ^ 2 * Real.sqrt (kappa (lam D N A) z.re + |z.im|))) <
            ‖ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *
              ∑ a, c a • Ea D N a)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  obtain ⟨K, hK0, hK⟩ := square_root_density τ hτ
  obtain ⟨N₁, hN₁⟩ := blockTr_local D hD δA τ hδA hτ C (τ' / 2) (by positivity) D' hD'
  obtain ⟨N₂, hN₂⟩ := Outside_ev (2 * max K 1) (τ' / 2) (by positivity)
  obtain ⟨N₃, hN₃⟩ := Outside_ev 20 δA hδA
  refine ⟨max (max N₁ N₂) (max N₃ 1), fun N hN θ hθ0 hθ1 μ hμ A hA c hc => ?_⟩
  have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3' : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hΛh := lam_isHermitian D N A
  have hΛ1 := Outside_lam_small D N δA hN1 (hN₃ N hN3') A hA
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN1⟩)⟩
  refine le_trans (measure_mono ?_) (hN₁ N hN1' θ hθ0 hθ1 μ hμ A hA)
  rintro h ⟨z, hz, hzre, hlt⟩
  refine ⟨z, hz, ?_⟩
  have hzim : 0 < |z.im| := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hz.2
  have hz0 : z.im ≠ 0 := abs_pos.mp hzim
  have hκ : 0 ≤ kappa (lam D N A) z.re := le_min (abs_nonneg _) (abs_nonneg _)
  have hspos : 0 < Real.sqrt (kappa (lam D N A) z.re + |z.im|) :=
    Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (kappa (lam D N A) z.re + |z.im|) ^ 2 = kappa (lam D N A) z.re + |z.im| :=
    Real.sq_sqrt (by linarith)
  have hmi := Outside_mExt_im_le τ K (lam D N A) hΛh
    (fun w hw hw0 hwre => ((hK (Idx D N) (lam D N A) hΛh hΛ1).2 w hw hw0).2 hwre |>.2) z hz.1 hz0
    hzre
  have hK1 : 1 ≤ max K 1 := le_max_right _ _
  have hpsi := Outside_psi_sq_le (N : ℝ) |z.im| _ (max K 1) (kappa (lam D N A) z.re)
    |(mExt (lam D N A) z).im| hN0 hzim hspos hK1 hs2 (abs_nonneg _)
    (hmi.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  -- the bracket `T` of the bound
  set T : ℝ := 1 / ((N : ℝ) * (kappa (lam D N A) z.re + |z.im|)) +
    1 / (((N : ℝ) * |z.im|) ^ 2 * Real.sqrt (kappa (lam D N A) z.re + |z.im|)) with hT
  have hT0 : 0 ≤ T := by positivity
  have hmin : min (psiIso (lam D N A) N z ^ 2 / Real.sqrt (kappa (lam D N A) z.re + |z.im|))
      (psiIso (lam D N A) N z) ≤ 2 * max K 1 * T :=
    (min_le_left _ _).trans hpsi
  have hbd := Outside_ntr_le_blockTr D N hD
    (res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) c hc
  have hN2 : 2 * max K 1 ≤ (N : ℝ) ^ (τ' / 2) := hN₂ N hN2'
  have hpow : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
    rw [← Real.rpow_add hN0]
    ring_nf
  have hpw0 : 0 < (N : ℝ) ^ (τ' / 2) := Real.rpow_pos_of_pos hN0 _
  calc (N : ℝ) ^ (τ' / 2) * min (psiIso (lam D N A) N z ^ 2 /
        Real.sqrt (kappa (lam D N A) z.re + |z.im|)) (psiIso (lam D N A) N z)
      ≤ (N : ℝ) ^ (τ' / 2) * (2 * max K 1 * T) := mul_le_mul_of_nonneg_left hmin hpw0.le
    _ ≤ (N : ℝ) ^ (τ' / 2) * ((N : ℝ) ^ (τ' / 2) * T) := by
        gcongr
    _ = (N : ℝ) ^ τ' * T := by rw [hpow]; ring
    _ < ‖ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *
          ∑ a, c a • Ea D N a)‖ := hlt
    _ ≤ _ := hbd

/-- Spectral inclusion: outside an event of probability `≤ N^{-D'}`, every eigenvalue of `X`
lies in `[E⁻ - N^{-2/3+τ'}, E⁺ + N^{-2/3+τ'}]` (the edge input of (2.24) [eq:rigidity]). -/
theorem spec_inclusion (D : ℕ) (hD : 1 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
        μ {h | Eplus (lam D N A) + (N : ℝ) ^ (-(2 / 3 : ℝ) + τ') <
              eigK (Matrix.of h + lam D N A) 1 ∨
            eigK (Matrix.of h + lam D N A) (D * N) <
              Eminus (lam D N A) - (N : ℝ) ^ (-(2 / 3 : ℝ) + τ')} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  -- the exponent is capped at `1`: the event at `τ'` lies in the event at `a = min τ' 1`
  set a : ℝ := min τ' 1 with ha
  have ha0 : 0 < a := lt_min hτ' one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  have haτ : a ≤ τ' := min_le_left _ _
  obtain ⟨K, hK0, hK⟩ := square_root_density (1 / 5) (by norm_num)
  obtain ⟨Ce, hCe0, hCe⟩ := edge_close_to_edge_sc
  obtain ⟨N₁, hN₁⟩ := far_no_eigenvalue D hD δA hδA C (D' + 1) (by linarith)
  obtain ⟨N₂, hN₂⟩ := aver_local_outside D hD δA (1 / 5) hδA (by norm_num) C (a / 4)
    (by positivity) (D' + 1) (by linarith)
  obtain ⟨N₃, hN₃⟩ := Outside_ev 20 δA hδA
  obtain ⟨N₄, hN₄⟩ := Outside_ev (4 * Ce) δA hδA
  obtain ⟨N₅, hN₅⟩ := Outside_ev ((D : ℝ) * (K + 2) + 1) (a / 4) (by positivity)
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ 2), fun N hN θ hθ0 hθ1 μ hμ A hA => ?_⟩
  have hN1' : N₁ ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hN)
  have hN2' : N₂ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hN)
  have hN3' : N₃ ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hN)
  have hN4' : N₄ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hN)
  have hN5' : N₅ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2le : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2le
  have hΛh := lam_isHermitian D N A
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN1⟩)⟩
  have hΛ1 := Outside_lam_small D N δA hN1 (hN₃ N hN3') A hA
  have hDN : 1 ≤ D * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- the edges: `E⁺ ≥ 3/2` and `E⁻ ≤ -3/2`
  have hedge : Eplus (lam D N A) ≥ 3 / 2 ∧ Eminus (lam D N A) ≤ -(3 / 2) := by
    have h1 := hCe (Idx D N) (lam D N A) hΛh hΛ1
    have h2 := opNorm_lam_le D N A
    have h3 : (N : ℝ) ^ (-δA) ≤ 1 / (4 * Ce) := by
      rw [Real.rpow_neg hN0.le, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) (hN₄ N hN4')
    have h4 : Ce * opNorm (lam D N A) ≤ 1 / 2 := by
      calc Ce * opNorm (lam D N A) ≤ Ce * (2 * (1 / (4 * Ce))) := by
            gcongr
            linarith
        _ = 1 / 2 := by field_simp; norm_num
    have h5 := abs_le.mp (le_trans (le_add_of_nonneg_right (abs_nonneg _)) (h1.trans h4))
    have h6 := abs_le.mp (le_trans (le_add_of_nonneg_left (abs_nonneg _)) (h1.trans h4))
    constructor <;> linarith [h5.1, h5.2, h6.1, h6.2]
  have hbig : (D : ℝ) * (K + 2) < (N : ℝ) ^ (a / 4) := by
    have := hN₅ N hN5'
    linarith
  have hc : ∀ b : Fin D, ‖(fun _ : Fin D => (1 : ℂ)) b‖ ≤ 1 := fun b => by simp
  have hfar := hN₁ N hN1' θ hθ0 hθ1 μ hμ A hA
  have hav := hN₂ N hN2' θ hθ0 hθ1 μ hμ A hA (fun _ => 1) hc
  have htwo : ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
    rw [← ENNReal.ofReal_add (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)]
    apply ENNReal.ofReal_le_ofReal
    have e : (N : ℝ) ^ (-(D' + 1)) = (N : ℝ) ^ (-D') * (N : ℝ)⁻¹ := by
      rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
    have hinv : (N : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hN2r
    have hp : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg hN0.le _
    rw [e]
    nlinarith
  refine le_trans (measure_mono ?_) (le_trans (measure_union_le _ _)
    (le_trans (add_le_add hfar hav) htwo))
  intro h hP
  by_contra hnot
  simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hnot
  obtain ⟨hF, hV⟩ := hnot
  have hfar' : ∀ k : ℕ, 1 ≤ k → k ≤ D * N → |eigK (Matrix.of h + lam D N A) k| < 4 := by
    intro k hk1 hk2
    by_contra hcon
    exact hF k hk1 hk2 (not_lt.mp hcon)
  have hsq : ∀ w : ℂ, ‖w‖ ≤ ((1 : ℝ) / 5)⁻¹ → 0 < w.im →
      w.re ∉ Set.Icc (Eminus (lam D N A)) (Eplus (lam D N A)) →
      (mSol (lam D N A) w).im ≤ K * (w.im / Real.sqrt (kappa (lam D N A) w.re + w.im)) :=
    fun w hw hw0 hwre => (((hK (Idx D N) (lam D N A) hΛh hΛ1).2 w hw hw0).2 hwre).2
  have haver : ∀ z ∈ specDom (1 / 5) N,
      z.re ∉ Set.Icc (Eminus (lam D N A)) (Eplus (lam D N A)) →
      ‖ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *
          ∑ a, (fun _ : Fin D => (1 : ℂ)) a • Ea D N a)‖ ≤
        (N : ℝ) ^ (a / 4) * (1 / ((N : ℝ) * (kappa (lam D N A) z.re + |z.im|)) +
          1 / (((N : ℝ) * |z.im|) ^ 2 * Real.sqrt (kappa (lam D N A) z.re + |z.im|))) :=
    fun z hz hre => hV z hz hre
  have hεle : (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + τ') :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hεpos : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ) + τ') := Real.rpow_pos_of_pos hN0 _
  rcases hP with hP | hP
  · -- upper edge
    have hne : eigK (Matrix.of h + lam D N A) 1 ≠ 0 := by
      intro h0
      rw [h0] at hP
      linarith [hedge.1]
    obtain ⟨hX, i, hi⟩ := Outside_eigK_mem _ 1 hne
    have h4 := hfar' 1 le_rfl hDN
    rw [← hi] at h4 hP
    refine Outside_no_outlier D N hD hN1 A K hK0.le hsq a ha0 ha1 hbig _ hX i h4 ?_ ?_ haver
    · intro hmem
      linarith [hmem.2]
    · refine le_min ?_ ?_
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith [hedge.1, hedge.2])]
        linarith [hedge.1, hedge.2]
  · -- lower edge
    have hne : eigK (Matrix.of h + lam D N A) (D * N) ≠ 0 := by
      intro h0
      rw [h0] at hP
      linarith [hedge.2]
    obtain ⟨hX, i, hi⟩ := Outside_eigK_mem _ (D * N) hne
    have h4 := hfar' (D * N) hDN le_rfl
    rw [← hi] at h4 hP
    refine Outside_no_outlier D N hD hN1 A K hK0.le hsq a ha0 ha1 hbig _ hX i h4 ?_ ?_ haver
    · intro hmem
      linarith [hmem.1]
    · refine le_min ?_ ?_
      · rw [abs_of_pos (by linarith [hedge.1, hedge.2])]
        linarith [hedge.1, hedge.2]
      · rw [abs_of_neg (by linarith)]
        linarith


end RBMTransitionEdge

end
