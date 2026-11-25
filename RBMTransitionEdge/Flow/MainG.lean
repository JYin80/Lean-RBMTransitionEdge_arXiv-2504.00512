module

public import RBMTransitionEdge.Flow.LemFlow3

@[expose] public section

/-!
# Lemma 3.12 for the Gaussian-divisible law

Lemma 3.12 [main_lemma_G], (3.35) [main_G_es], for the block-OU law at a time `s` with
`1 - e^{-s} ∈ [N^{-ε_g}/2, N^{-ε_g}]` of the law of `H_{t₀}` of (4.1) [defVt], from Lemma 3.11
[lem_flow_3] at the terminal point of the characteristic flow.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Scalar tools -/

/-- `C N^α ≤ N^β` for all large `N` when `α < β`. -/
private lemma MG_ev_pow (C α β : ℝ) (hαβ : α < β) :
    ∀ᶠ N : ℕ in Filter.atTop, C * (N : ℝ) ^ α ≤ (N : ℝ) ^ β := by
  have t : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (β - α)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [t.eventually_ge_atTop C, Filter.eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have e : (N : ℝ) ^ β = (N : ℝ) ^ (β - α) * (N : ℝ) ^ α := by
    rw [← Real.rpow_add hNpos]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hNpos.le _)

/-- `x/2 ≤ log(1 + x)` for `x ∈ [0, 1]`. -/
private lemma MG_log (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x / 2 ≤ Real.log (1 + x) := by
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x by linarith)
  have h2 : x / 2 ≤ 1 - (1 + x)⁻¹ := by
    have e : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    rw [e, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  linarith

/-- `(N^a)² = N^{2a}`. -/
private lemma MG_sq (N a : ℝ) (hN : 0 < N) : (N ^ a) ^ 2 = N ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; norm_num; ring_nf

/-- `t Λ(A) = Λ(t A)` for real `t`. -/
private lemma MG_lam_smul (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    (t : ℂ) • lam D N A = lam D N ((t : ℂ) • A) := by
  ext p q
  simp only [lam, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [mul_add, Complex.conj_ofReal]

/-- The lower bound `κ + η ≥ (c ∧ 1) N^{-2/3+6ε_g}` at `E = γ_k`, from
`κ ≥ c 𝔯^{2/3} N^{-2/3}` ((2.21) [eq:kappa_gamma_k]) and `η ≥ N^{-2/3+9ε_g} 𝔯^{-1/3}`. -/
private lemma MG_sum_lb (N r ck εg η κ : ℝ) (hN : 1 ≤ N) (hr : 1 ≤ r) (hck : 0 < ck)
    (hη : N ^ (-(2 / 3 : ℝ) + 9 * εg) * r ^ (-(1 / 3 : ℝ)) ≤ η)
    (hκ : ck * (r ^ (2 / 3 : ℝ) * N ^ (-(2 / 3 : ℝ))) ≤ κ) :
    min ck 1 * N ^ (-(2 / 3 : ℝ) + 6 * εg) ≤ κ + η := by
  have hN0 : 0 < N := by linarith
  have hr0 : 0 < r := by linarith
  have hη0 : 0 ≤ η := le_trans (by positivity) hη
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  have hP : 0 ≤ N ^ (-(2 / 3 : ℝ) + 6 * εg) := by positivity
  have hm1 : min ck 1 ≤ ck := min_le_left _ _
  have hm2 : min ck 1 ≤ 1 := min_le_right _ _
  by_cases hrN : N ^ (9 * εg) ≤ r
  · have h1 : N ^ (6 * εg) ≤ r ^ (2 / 3 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hrN (show (0 : ℝ) ≤ 2 / 3 by norm_num)
      rwa [← Real.rpow_mul hN0.le, show 9 * εg * (2 / 3) = 6 * εg by ring] at this
    have h2 : N ^ (-(2 / 3 : ℝ) + 6 * εg) = N ^ (6 * εg) * N ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have h3 : N ^ (6 * εg) * N ^ (-(2 / 3 : ℝ)) ≤ r ^ (2 / 3 : ℝ) * N ^ (-(2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_right hm1 (show 0 ≤ N ^ (6 * εg) * N ^ (-(2 / 3 : ℝ)) by
      positivity)]
  · have hrN' : r ≤ N ^ (9 * εg) := (lt_of_not_ge hrN).le
    have h1 : N ^ (-(3 * εg)) ≤ r ^ (-(1 / 3 : ℝ)) := by
      have := Real.rpow_le_rpow_of_nonpos hr0 hrN' (show -(1 / 3 : ℝ) ≤ 0 by norm_num)
      rwa [← Real.rpow_mul hN0.le, show 9 * εg * (-(1 / 3)) = -(3 * εg) by ring] at this
    have h2 : N ^ (-(2 / 3 : ℝ) + 6 * εg) = N ^ (-(2 / 3 : ℝ) + 9 * εg) * N ^ (-(3 * εg)) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have h3 : N ^ (-(2 / 3 : ℝ) + 9 * εg) * N ^ (-(3 * εg)) ≤
        N ^ (-(2 / 3 : ℝ) + 9 * εg) * r ^ (-(1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_right hm2 (show 0 ≤ N ^ (-(2 / 3 : ℝ) + 9 * εg) *
      N ^ (-(3 * εg)) by positivity)]

/-- `N η √κ ≥ √c N^{9ε_g}` at `E = γ_k`, from `κ ≥ c 𝔯^{2/3} N^{-2/3}` ((2.21)
[eq:kappa_gamma_k]) and `η ≥ N^{-2/3+9ε_g} 𝔯^{-1/3}`. -/
private lemma MG_prod_lb (N r ck εg η κ : ℝ) (hN : 1 ≤ N) (hr : 1 ≤ r) (hck : 0 < ck)
    (hη : N ^ (-(2 / 3 : ℝ) + 9 * εg) * r ^ (-(1 / 3 : ℝ)) ≤ η)
    (hκ : ck * (r ^ (2 / 3 : ℝ) * N ^ (-(2 / 3 : ℝ))) ≤ κ) :
    Real.sqrt ck * N ^ (9 * εg) ≤ N * η * Real.sqrt κ := by
  have hN0 : 0 < N := by linarith
  have hr0 : 0 < r := by linarith
  have hs : Real.sqrt ck * r ^ (1 / 3 : ℝ) * N ^ (-(1 / 3 : ℝ)) ≤ Real.sqrt κ := by
    rw [Real.le_sqrt (by positivity) (le_trans (by positivity) hκ)]
    have e : (Real.sqrt ck * r ^ (1 / 3 : ℝ) * N ^ (-(1 / 3 : ℝ))) ^ 2 =
        ck * (r ^ (2 / 3 : ℝ) * N ^ (-(2 / 3 : ℝ))) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hck.le, MG_sq r _ hr0, MG_sq N _ hN0]
      norm_num [mul_assoc]
    rw [e]; exact hκ
  have e2 : N * (N ^ (-(2 / 3 : ℝ) + 9 * εg) * r ^ (-(1 / 3 : ℝ))) *
      (Real.sqrt ck * r ^ (1 / 3 : ℝ) * N ^ (-(1 / 3 : ℝ))) = Real.sqrt ck * N ^ (9 * εg) := by
    have a1 : r ^ (-(1 / 3 : ℝ)) * r ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hr0]; norm_num
    have a2 : N * N ^ (-(2 / 3 : ℝ) + 9 * εg) * N ^ (-(1 / 3 : ℝ)) = N ^ (9 * εg) := by
      calc N * N ^ (-(2 / 3 : ℝ) + 9 * εg) * N ^ (-(1 / 3 : ℝ)) =
            N ^ (1 : ℝ) * N ^ (-(2 / 3 : ℝ) + 9 * εg) * N ^ (-(1 / 3 : ℝ)) := by
            rw [Real.rpow_one]
        _ = N ^ (1 + (-(2 / 3 : ℝ) + 9 * εg) + -(1 / 3 : ℝ)) := by
            rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
        _ = _ := by ring_nf
    calc _ = Real.sqrt ck * (N * N ^ (-(2 / 3 : ℝ) + 9 * εg) * N ^ (-(1 / 3 : ℝ))) *
          (r ^ (-(1 / 3 : ℝ)) * r ^ (1 / 3 : ℝ)) := by ring
      _ = _ := by rw [a1, a2, mul_one]
  rw [← e2]
  have h0 : 0 ≤ N ^ (-(2 / 3 : ℝ) + 9 * εg) * r ^ (-(1 / 3 : ℝ)) := by positivity
  have h1 : 0 ≤ Real.sqrt ck * r ^ (1 / 3 : ℝ) * N ^ (-(1 / 3 : ℝ)) := by positivity
  have hη0 : 0 ≤ η := le_trans h0 hη
  calc _ ≤ N * η * (Real.sqrt ck * r ^ (1 / 3 : ℝ) * N ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη hN0.le) h1
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (mul_nonneg hN0.le hη0)

/-! ### The base point of the characteristic flow -/

/-- The base point of the characteristic flow (3.10) [eq:deterflow] for the terminal point `z`
(proof of Lemma 3.12 [main_lemma_G]): with `Λ₀ = e^{S/2} Λ` and `z₀ = z_{-S}`, `Im z₀ > 0`,
`m(z₀, Λ₀) = e^{-S/2} m(z, Λ)`, `t_c - t₀ = (t_c - t_f) + S`, the flow from `(z₀, Λ₀)` and from
`(z̄₀, Λ₀)` reaches `z` and `z̄` at time `S` with `Λ_S = Λ`, and `Im m_S = Im m(z, Λ)`. -/
private lemma MG_flow {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (S : ℝ) (hS : 0 ≤ S) :
    0 < (charFlowZ Λ z (-S)).im ∧
      mExt (((Real.exp (S / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z (-S)) =
        (Real.exp (-S / 2) : ℂ) * mExt Λ z ∧
      flowTc (((Real.exp (S / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z (-S)) = flowTc Λ z + S ∧
      charFlowZ (((Real.exp (S / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z (-S)) S = z ∧
      charFlowZ (((Real.exp (S / 2) : ℝ) : ℂ) • Λ) (star (charFlowZ Λ z (-S))) S = star z ∧
      ((Real.exp (-S / 2) : ℝ) : ℂ) • (((Real.exp (S / 2) : ℝ) : ℂ) • Λ) = Λ ∧
      flowIm (((Real.exp (S / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z (-S)) S = (mExt Λ z).im ∧
      0 < (mExt Λ z).im ∧ 0 < flowTc Λ z := by
  have hι : 0 < (mExt Λ z).im := by
    have : mExt Λ z = mSol Λ z := by simp [mExt, hz]
    rw [this]; exact (mSol_spec Λ hΛ z hz).1
  have hq : 0 < flowTc Λ z := by
    unfold flowTc; exact Real.log_pos (by have := div_pos hz hι; linarith)
  have hs : -S < Real.log (1 + z.im / (mExt Λ z).im) := by
    have : flowTc Λ z = Real.log (1 + z.im / (mExt Λ z).im) := rfl
    linarith
  have e0 : -(-S) / 2 = S / 2 := by ring
  obtain ⟨hpos, -, hm⟩ := charFlow_M Λ hΛ z hz (-S) hs
  rw [e0] at hm
  have htc := flowTc_flow Λ hΛ z hz (-S) (by linarith)
  rw [e0] at htc
  have hcomp := charFlowZ_comp Λ hΛ z hz S S hS
  rw [sub_self, show charFlowZ Λ z 0 = z by simp [charFlowZ]] at hcomp
  have hsm : ((Real.exp (-S / 2) : ℝ) : ℂ) • (((Real.exp (S / 2) : ℝ) : ℂ) • Λ) = Λ := by
    rw [smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, show -S / 2 + S / 2 = 0 by ring,
      Real.exp_zero, Complex.ofReal_one, one_smul]
  refine ⟨hpos, hm, ?_, hcomp, ?_, hsm, ?_, hι, hq⟩
  · rw [htc]; ring
  · rw [charFlowZ_conj _ _ hpos, hcomp]
  · unfold flowIm; rw [hsm, hcomp]

/-! ### The scalar rows of the proof of Lemma 3.12 -/

/-- At `E = γ_k`, with `Im m ≥ C⁻¹ √(κ + η)` ((A.1) [square_root_density]),
`κ ≥ c 𝔯^{2/3} N^{-2/3}` ((2.21) [eq:kappa_gamma_k]) and `N^{-2/3+9ε_g} 𝔯^{-1/3} ≤ η ≤ N^{-9ε_g}`:
`Im m ≥ N^{-1/3+2ε_g}/3`, `η ≤ 2 N^{-ε_g} Im m` and `N η Im m ≥ N^{7ε_g}` for large `N`. -/
private lemma MG_im (N r ck εg η κ ι Csr : ℝ) (hN : 1 ≤ N) (hr : 1 ≤ r) (hck : 0 < ck)
    (hCsr : 0 < Csr)
    (hη : N ^ (-(2 / 3 : ℝ) + 9 * εg) * r ^ (-(1 / 3 : ℝ)) ≤ η) (hηhi : η ≤ N ^ (-(9 * εg)))
    (hκ : ck * (r ^ (2 / 3 : ℝ) * N ^ (-(2 / 3 : ℝ))) ≤ κ)
    (hι : Csr⁻¹ * Real.sqrt (κ + η) ≤ ι)
    (e5 : Csr / (3 * Real.sqrt (min ck 1)) * N ^ (-(1 / 3 : ℝ) + 2 * εg) ≤
      N ^ (-(1 / 3 : ℝ) + 3 * εg))
    (e6 : Csr / 2 * N ^ (-(9 * εg) * (1 / 2)) ≤ N ^ (-εg))
    (e7 : Csr / Real.sqrt ck * N ^ (7 * εg) ≤ N ^ (9 * εg)) :
    (1 / 3 : ℝ) * N ^ (-(1 / 3 : ℝ) + 2 * εg) ≤ ι ∧ η ≤ 2 * N ^ (-εg) * ι ∧
      N ^ (7 * εg) ≤ N * η * ι := by
  have hN0 : 0 < N := by linarith
  have hr0 : 0 < r := by linarith
  have hη0 : 0 ≤ η := le_trans (by positivity) hη
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  have hmn : 0 < min ck 1 := lt_min hck one_pos
  have hsmn : 0 < Real.sqrt (min ck 1) := Real.sqrt_pos.2 hmn
  have hsck : 0 < Real.sqrt ck := Real.sqrt_pos.2 hck
  have hCi : 0 < Csr⁻¹ := inv_pos.2 hCsr
  have hsum := MG_sum_lb N r ck εg η κ hN hr hck hη hκ
  have h3 : (1 / 3 : ℝ) * N ^ (-(1 / 3 : ℝ) + 2 * εg) ≤ ι := by
    have hsq : Real.sqrt (min ck 1) * N ^ (-(1 / 3 : ℝ) + 3 * εg) ≤ Real.sqrt (κ + η) := by
      rw [Real.le_sqrt (by positivity) (by positivity), mul_pow, Real.sq_sqrt hmn.le,
        MG_sq _ _ hN0]
      convert hsum using 3; ring
    have h1 : Csr⁻¹ * (Real.sqrt (min ck 1) * N ^ (-(1 / 3 : ℝ) + 3 * εg)) ≤ ι :=
      le_trans (mul_le_mul_of_nonneg_left hsq hCi.le) hι
    have this := mul_le_mul_of_nonneg_left e5 (mul_pos hCi hsmn).le
    have e : Csr⁻¹ * Real.sqrt (min ck 1) * (Csr / (3 * Real.sqrt (min ck 1))) = 1 / 3 := by
      field_simp
    have h2 : (1 / 3 : ℝ) * N ^ (-(1 / 3 : ℝ) + 2 * εg) ≤
        Csr⁻¹ * (Real.sqrt (min ck 1) * N ^ (-(1 / 3 : ℝ) + 3 * εg)) :=
      calc _ = Csr⁻¹ * Real.sqrt (min ck 1) * (Csr / (3 * Real.sqrt (min ck 1)) *
            N ^ (-(1 / 3 : ℝ) + 2 * εg)) := by rw [← mul_assoc, e]
        _ ≤ Csr⁻¹ * Real.sqrt (min ck 1) * N ^ (-(1 / 3 : ℝ) + 3 * εg) := this
        _ = _ := by ring
    exact le_trans h2 h1
  have hιpos : 0 < ι := lt_of_lt_of_le (by positivity) h3
  have hsη : Real.sqrt η ≤ N ^ (-(9 * εg) * (1 / 2)) := by
    rw [Real.rpow_mul hN0.le, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hηhi
  have h1 : Csr⁻¹ * Real.sqrt η ≤ ι :=
    le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_add_of_nonneg_left hκ0)) hCi.le) hι
  have h3' : Real.sqrt η ≤ Csr * ι := by
    have := mul_le_mul_of_nonneg_left h1 hCsr.le
    rwa [← mul_assoc, mul_inv_cancel₀ hCsr.ne', one_mul] at this
  have h4 : Csr * Real.sqrt η ≤ 2 * N ^ (-εg) := by
    have := mul_le_mul_of_nonneg_left hsη hCsr.le
    have e : Csr * N ^ (-(9 * εg) * (1 / 2)) = 2 * (Csr / 2 * N ^ (-(9 * εg) * (1 / 2))) := by
      ring
    rw [e] at this
    linarith
  have hηι : η ≤ 2 * N ^ (-εg) * ι :=
    calc η = Real.sqrt η * Real.sqrt η := (Real.mul_self_sqrt hη0).symm
      _ ≤ Real.sqrt η * (Csr * ι) := mul_le_mul_of_nonneg_left h3' (Real.sqrt_nonneg _)
      _ = (Csr * Real.sqrt η) * ι := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h4 hιpos.le
  have hp := MG_prod_lb N r ck εg η κ hN hr hck hη hκ
  have h5 : Csr⁻¹ * Real.sqrt κ ≤ ι :=
    le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_add_of_nonneg_right hη0)) hCi.le) hι
  have h6 : Csr⁻¹ * (Real.sqrt ck * N ^ (9 * εg)) ≤ N * η * ι :=
    calc _ ≤ Csr⁻¹ * (N * η * Real.sqrt κ) := mul_le_mul_of_nonneg_left hp hCi.le
      _ = N * η * (Csr⁻¹ * Real.sqrt κ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h5 (mul_nonneg hN0.le hη0)
  have h7 : N ^ (7 * εg) ≤ Csr⁻¹ * (Real.sqrt ck * N ^ (9 * εg)) := by
    have := mul_le_mul_of_nonneg_left e7 (mul_pos hCi hsck).le
    have e : Csr⁻¹ * Real.sqrt ck * (Csr / Real.sqrt ck) = 1 := by field_simp
    calc _ = Csr⁻¹ * Real.sqrt ck * (Csr / Real.sqrt ck * N ^ (7 * εg)) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ Csr⁻¹ * Real.sqrt ck * N ^ (9 * εg) := this
      _ = _ := by ring
  exact ⟨h3, hηι, le_trans h7 h6⟩

/-- The base point `z₀ = z_{-S}` in the proof of Lemma 3.12 [main_lemma_G], with
`u = 1 - e^{-S} ∈ [N^{-ε_g}/2, N^{-ε_g}]`, `v = e^{S/2}`, `w = e^{-S/2}`,
`Im z₀ = v (η + Im m) - w Im m` and `Im m(z₀, Λ₀) = w Im m`: `v ≤ 2`, `Im z₀ ≥ N^{-1/3+ε_g}/6`,
`Im z₀ ≥ N^{-1+1/10}`, and `Im z₀ / Im m(z₀, Λ₀) ∈ [N^{-ε_g}/6, 6 N^{-ε_g}]`. -/
private lemma MG_base (N εg u v w η ι : ℝ) (hN : 1 ≤ N) (hu₁ : N ^ (-εg) / 2 ≤ u)
    (hu₂ : u ≤ N ^ (-εg)) (hu12 : u ≤ 1 / 2) (hv0 : 0 < v) (hw0 : 0 < w) (hvw : v * w = 1)
    (hww : w * w = 1 - u) (hι3 : (1 / 3 : ℝ) * N ^ (-(1 / 3 : ℝ) + 2 * εg) ≤ ι)
    (hηι : η ≤ 2 * N ^ (-εg) * ι) (hη : 0 < η)
    (e8 : 6 * N ^ (-1 + 1 / 10 : ℝ) ≤ N ^ (-(1 / 3 : ℝ) + εg)) :
    v ≤ 2 ∧ 6⁻¹ * N ^ (-(1 / 3 : ℝ) + εg) ≤ v * (η + ι) - w * ι ∧
      N ^ (-1 + 1 / 10 : ℝ) ≤ v * (η + ι) - w * ι ∧
      6⁻¹ * N ^ (-εg) ≤ (v * (η + ι) - w * ι) / (w * ι) ∧
      (v * (η + ι) - w * ι) / (w * ι) ≤ 6 * N ^ (-εg) := by
  have hN0 : 0 < N := by linarith
  have hn : 0 < N ^ (-εg) := Real.rpow_pos_of_pos hN0 _
  have hu0 : 0 < u := by linarith
  have hιpos : 0 < ι := lt_of_lt_of_le (by positivity) hι3
  have hw1 : w ≤ 1 := by nlinarith
  have hw2 : 1 / 2 ≤ w := by nlinarith
  have hv2 : v ≤ 2 := by nlinarith
  have hvwu : u ≤ v - w := by
    have e : w * (v - w - u) = (1 - w) * (1 - w * w) := by
      linear_combination hvw - w * hww
    have h0 : 0 ≤ w * (v - w - u) := by
      rw [e]; exact mul_nonneg (by linarith) (by nlinarith)
    have := nonneg_of_mul_nonneg_right h0 hw0
    linarith
  have hP : u * ι ≤ v * (η + ι) - w * ι := by nlinarith
  have hlo : 6⁻¹ * N ^ (-(1 / 3 : ℝ) + εg) ≤ v * (η + ι) - w * ι := by
    have e : N ^ (-(1 / 3 : ℝ) + εg) = N ^ (-εg) * N ^ (-(1 / 3 : ℝ) + 2 * εg) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have h1 : N ^ (-εg) / 2 * ((1 / 3 : ℝ) * N ^ (-(1 / 3 : ℝ) + 2 * εg)) ≤ u * ι :=
      mul_le_mul hu₁ hι3 (by positivity) hu0.le
    rw [e]; nlinarith
  refine ⟨hv2, hlo, by linarith, ?_, ?_⟩
  · rw [le_div_iff₀ (mul_pos hw0 hιpos)]
    have h1 : N ^ (-εg) / 2 * ι ≤ u * ι := mul_le_mul_of_nonneg_right hu₁ hιpos.le
    have h2 : 6⁻¹ * N ^ (-εg) * (w * ι) ≤ N ^ (-εg) / 2 * ι := by
      have : 6⁻¹ * N ^ (-εg) * (w * ι) = (6⁻¹ * w) * (N ^ (-εg) * ι) := by ring
      rw [this]; nlinarith [mul_pos hn hιpos]
    linarith
  · rw [div_le_iff₀ (mul_pos hw0 hιpos)]
    have e : (v * (η + ι) - w * ι) * w = η + u * ι := by
      have : (v * (η + ι) - w * ι) * w = (v * w) * (η + ι) - (w * w) * ι := by ring
      rw [this, hvw, hww]; ring
    have h1 : η + u * ι ≤ 6 * N ^ (-εg) * (w * ι) * w := by
      have : 6 * N ^ (-εg) * (w * ι) * w = 6 * N ^ (-εg) * ι * (w * w) := by ring
      rw [this, hww]
      have h2 : u * ι ≤ N ^ (-εg) * ι := mul_le_mul_of_nonneg_right hu₂ hιpos.le
      nlinarith [mul_pos hn hιpos]
    rw [← e] at h1
    exact le_of_mul_le_mul_right h1 hw0

/-- The output of (3.33) [flow_3_result_2] at the terminal point in the proof of Lemma 3.12
[main_lemma_G]: with `t_c - t_f = log(1 + η/Im m)` and `η ≤ 2 N^{-ε_g} Im m ≤ Im m`,
`N^{τ'/2} N^{-ε_g} / (N (t_c - t_f)² (Im m)²) ≤ N^{τ'} N^{-1-ε_g} η^{-2}` once
`4 N^{τ'/2} ≤ N^{τ'}`. -/
private lemma MG_final (N εg τ' η ι : ℝ) (hN : 1 ≤ N) (hη : 0 < η) (hι : 0 < ι)
    (hηι : η ≤ 2 * N ^ (-εg) * ι) (hn : 2 * N ^ (-εg) ≤ 1)
    (e9 : 4 * N ^ (τ' / 2) ≤ N ^ τ') :
    N ^ (τ' / 2) * (N ^ (-min εg εg) / (N * Real.log (1 + η / ι) ^ 2 * ι ^ 2)) ≤
      N ^ τ' * (N ^ (-1 - εg) * (η ^ 2)⁻¹) := by
  have hN0 : 0 < N := by linarith
  rw [min_self]
  have hx0 : 0 ≤ η / ι := (div_pos hη hι).le
  have hx1 : η / ι ≤ 1 := by
    rw [div_le_one hι]; nlinarith
  have hq := MG_log (η / ι) hx0 hx1
  have hqι : η / 2 ≤ Real.log (1 + η / ι) * ι := by
    have := mul_le_mul_of_nonneg_right hq hι.le
    rwa [div_mul_eq_mul_div, div_mul_cancel₀ _ hι.ne'] at this
  have hd : N * η ^ 2 / 4 ≤ N * Real.log (1 + η / ι) ^ 2 * ι ^ 2 := by
    have h1 : (η / 2) ^ 2 ≤ (Real.log (1 + η / ι) * ι) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hqι 2
    nlinarith
  have hY : N ^ (-εg) / (N * Real.log (1 + η / ι) ^ 2 * ι ^ 2) ≤
      4 * (N ^ (-1 - εg) * (η ^ 2)⁻¹) := by
    have e : 4 * (N ^ (-1 - εg) * (η ^ 2)⁻¹) = N ^ (-εg) / (N * η ^ 2 / 4) := by
      rw [show (-1 - εg) = -1 + -εg by ring, Real.rpow_add hN0, Real.rpow_neg_one]
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hd
  have hX : 0 ≤ N ^ (-1 - εg) * (η ^ 2)⁻¹ := by positivity
  calc _ ≤ N ^ (τ' / 2) * (4 * (N ^ (-1 - εg) * (η ^ 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left hY (by positivity)
    _ = (4 * N ^ (τ' / 2)) * (N ^ (-1 - εg) * (η ^ 2)⁻¹) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right e9 hX

/-! ### Lemma 3.12 with `ε_{g0} = δ_A/10 ∧ 1/10` -/

/-- Lemma 3.12 [main_lemma_G], (3.35) [main_G_es], for the block-OU law at a time `s` with
`1 - e^{-s} ∈ [N^{-ε_g}/2, N^{-ε_g}]` of the law of `H_{t₀}`, `θ = e^{-s} e^{-t₀} + 1 - e^{-s}`,
`C = 9`, at every `ε_g ∈ (0, δ_A/10 ∧ 1/10]`. -/
private lemma MG_main (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) (εg : ℝ)
    (hεg : 0 < εg) (hεg₀ : εg ≤ min (δA / 10) (1 / 10)) (τ' : ℝ) (hτ' : 0 < τ') :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (L : EntryLaws C) (t₀ s : ℝ), 0 ≤ t₀ → t₀ ≤ 1 →
      (N : ℝ) ^ (-εg) / 2 ≤ 1 - Real.exp (-s) → 1 - Real.exp (-s) ≤ (N : ℝ) ^ (-εg) →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      (N : ℝ) ^ ((1 / 3 : ℝ) + εA) * rk D N k ^ (-(1 / 3 : ℝ)) ≤ hsNorm A →
      ∀ z : ℂ, z.re = quant (rho (lam D N A)) (D * N) k →
      (N : ℝ) ^ (-(2 / 3 : ℝ) + 9 * εg) * rk D N k ^ (-(1 / 3 : ℝ)) ≤ z.im →
      z.im ≤ (N : ℝ) ^ (-(9 * εg)) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        hsNorm (ELmat (blockOULaw D N (ouMatLaw D N L t₀) s) (lam D N A) z₁ z₂ -
            KTheta (lam D N A) (Real.exp (-s) * Real.exp (-t₀) + 1 - Real.exp (-s)) z₁ z₂) ≤
          (N : ℝ) ^ τ' * ((N : ℝ) ^ (-1 - εg) * (z.im ^ 2)⁻¹) := by
  obtain ⟨Csr, hCsr, hsr⟩ := square_root_density (1 / 4) (by norm_num)
  obtain ⟨ck, Ck, hck, -, Nk, hNk⟩ := kappa_gamma_k D hD δA hδA
  obtain ⟨Ce, hCe, hedge⟩ := edge_close_to_edge_sc
  have hεg1 : εg ≤ δA / 10 := le_trans hεg₀ (min_le_left _ _)
  have hεg2 : εg ≤ 1 / 10 := le_trans hεg₀ (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := flowL2_exp_paper D hD (δA / 2) (1 / 10) εg εg 6 7 (by positivity)
    (by norm_num) hεg hεg (by linarith) (by linarith) (by norm_num) (by norm_num) C (τ' / 2)
    (by positivity)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_ge_atTop (max (max N₁ Nk) 2)).and
    ((MG_ev_pow 2 (-εg) 0 (by linarith)).and
    ((MG_ev_pow 2 (-δA) (-(δA / 2)) (by linarith)).and
    ((MG_ev_pow (20 + 20 * Ce) (-δA) 0 (by linarith)).and
    ((MG_ev_pow (Csr / (3 * Real.sqrt (min ck 1))) (-(1 / 3 : ℝ) + 2 * εg)
      (-(1 / 3 : ℝ) + 3 * εg) (by linarith)).and
    ((MG_ev_pow (Csr / 2) (-(9 * εg) * (1 / 2)) (-εg) (by linarith)).and
    ((MG_ev_pow (Csr / Real.sqrt ck) (7 * εg) (9 * εg) (by linarith)).and
    ((MG_ev_pow 6 (-1 + 1 / 10) (-(1 / 3 : ℝ) + εg) (by linarith)).and
    (MG_ev_pow 4 (τ' / 2) τ' (by linarith))))))))))
  refine ⟨N₀, fun N hN L t₀ s ht₀ ht₁ hu₁ hu₂ A hA k hk1 hk2 _ z hzre hzlo hzhi z₁ z₂ h₁ h₂ => ?_⟩
  obtain ⟨hNN, e2, e3, e4, e5, e6, e7, e8, e9⟩ := hN₀ N hN
  rw [Real.rpow_zero] at e2 e4
  have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNN
  have hNk' : Nk ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hNN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hne : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  -- (2.21) [eq:kappa_gamma_k] at `k` and at `DN + 1 - k`
  obtain ⟨hkA, -, -, -⟩ := hNk N hNk' A hA k hk1 hk2
  obtain ⟨-, -, hkB, -⟩ := hNk N hNk' A hA (D * N + 1 - k) (by omega) (by omega)
  rw [show D * N + 1 - (D * N + 1 - k) = k by omega] at hkB
  clear hNk
  rw [← hzre] at hkA hkB
  have hr1 : (1 : ℝ) ≤ rk D N k := by unfold rk; exact_mod_cast le_min hk1 (by omega)
  have hrk : rk D N k ≤ (k : ℝ) := by unfold rk; exact_mod_cast min_le_left _ _
  have hrk' : rk D N k ≤ ((D * N + 1 - k : ℕ) : ℝ) := by
    unfold rk; exact_mod_cast min_le_right _ _
  have hr0 : 0 < rk D N k := by linarith
  -- `‖Λ‖ ≤ 1/10` and the edges
  have hΛ : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hNδ : 0 < (N : ℝ) ^ (-δA) := Real.rpow_pos_of_pos hNpos _
  have hCeN : 0 ≤ Ce * (N : ℝ) ^ (-δA) := by positivity
  have hlam2 : opNorm (lam D N A) ≤ 2 * (N : ℝ) ^ (-δA) := by
    have := opNorm_lam_le D N A; linarith
  have e4' : (20 + 20 * Ce) * (N : ℝ) ^ (-δA) =
      20 * (N : ℝ) ^ (-δA) + 20 * (Ce * (N : ℝ) ^ (-δA)) := by ring
  have hℓ : opNorm (lam D N A) ≤ 1 / 10 := by linarith
  have hEd := hedge (Idx D N) (lam D N A) hΛ hℓ
  clear hedge
  have hEd' : Ce * opNorm (lam D N A) ≤ 1 / 10 := by
    have : Ce * opNorm (lam D N A) ≤ Ce * (2 * (N : ℝ) ^ (-δA)) :=
      mul_le_mul_of_nonneg_left hlam2 hCe.le
    have e : Ce * (2 * (N : ℝ) ^ (-δA)) = 2 * (Ce * (N : ℝ) ^ (-δA)) := by ring
    linarith
  have hEp : Eplus (lam D N A) ≤ 21 / 10 := by
    have h := abs_nonneg (2 + Eminus (lam D N A))
    have := (abs_le.1 (show |2 - Eplus (lam D N A)| ≤ 1 / 10 by linarith)).1
    linarith
  have hEm : -(21 / 10) ≤ Eminus (lam D N A) := by
    have h := abs_nonneg (2 - Eplus (lam D N A))
    have := (abs_le.1 (show |2 + Eminus (lam D N A)| ≤ 1 / 10 by linarith)).1
    linarith
  -- `κ(γ_k) ≥ c 𝔯(k)^{2/3} N^{-2/3}`
  have hN23 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hkap1 : ck * (rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤
      Eplus (lam D N A) - z.re := by
    refine le_trans ?_ hkA
    gcongr
  have hkap2 : ck * (rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤
      z.re - Eminus (lam D N A) := by
    refine le_trans ?_ hkB
    gcongr
  have hkpos : 0 < ck * (rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by positivity
  have hγmem : z.re ∈ Set.Icc (Eminus (lam D N A)) (Eplus (lam D N A)) :=
    ⟨by linarith, by linarith⟩
  have hκ : ck * (rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤
      kappa (lam D N A) z.re := by
    unfold kappa
    exact le_min (le_trans hkap1 (le_abs_self _)) (le_trans hkap2 (le_abs_self _))
  -- the terminal point `z`
  have hz : 0 < z.im := lt_of_lt_of_le (by positivity) hzlo
  have hη1 : z.im ≤ 1 := hzhi.trans (Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith))
  have hre : |z.re| ≤ 21 / 10 := abs_le.2 ⟨by linarith [hγmem.1], by linarith [hγmem.2]⟩
  have hzn : ‖z‖ ≤ 31 / 10 :=
    (Complex.norm_le_abs_re_add_abs_im z).trans (by rw [abs_of_pos hz]; linarith)
  have hmS : mExt (lam D N A) z = mSol (lam D N A) z := by simp [mExt, hz]
  have hmn1 : ‖mExt (lam D N A) z‖ < 1 := by
    rw [hmS]; exact (mSol_apriori (lam D N A) hΛ hℓ z hz).2.1
  have hιlo : Csr⁻¹ * Real.sqrt (kappa (lam D N A) z.re + z.im) ≤ (mExt (lam D N A) z).im := by
    rw [hmS]
    exact (((hsr (Idx D N) (lam D N A) hΛ hℓ).2 z (by norm_num; linarith) hz).1 hγmem).1
  clear hsr
  obtain ⟨hι3, hηι, hNηι⟩ := MG_im N (rk D N k) ck εg z.im (kappa (lam D N A) z.re)
    (mExt (lam D N A) z).im Csr hNr hr1 hck hCsr hzlo hzhi hκ hιlo e5 e6 e7
  -- the horizon `S = s`
  have hnε : 0 < (N : ℝ) ^ (-εg) := Real.rpow_pos_of_pos hNpos _
  have hs0 : 0 < s := by
    by_contra h
    have : 1 ≤ Real.exp (-s) := Real.one_le_exp (by linarith)
    linarith
  have hvw : Real.exp (s / 2) * Real.exp (-s / 2) = 1 := by
    rw [← Real.exp_add, show s / 2 + -s / 2 = 0 by ring, Real.exp_zero]
  have hww : Real.exp (-s / 2) * Real.exp (-s / 2) = 1 - (1 - Real.exp (-s)) := by
    rw [← Real.exp_add, show -s / 2 + -s / 2 = -s by ring]; ring
  obtain ⟨hv2, hlo, hsd, hrl, hru⟩ := MG_base N εg (1 - Real.exp (-s)) (Real.exp (s / 2))
    (Real.exp (-s / 2)) z.im (mExt (lam D N A) z).im hNr hu₁ hu₂ (by linarith) (Real.exp_pos _)
    (Real.exp_pos _) hvw hww hι3 hηι hz e8
  -- the base point `z₀ = z_{-s}`, `Λ₀ = e^{s/2} Λ`
  obtain ⟨hz₀, hm₀, htc₀, hland, hlandc, hsm, hfI, hιpos, hq⟩ :=
    MG_flow (lam D N A) hΛ z hz s hs0.le
  have hlamA : lam D N (((Real.exp (s / 2) : ℝ) : ℂ) • A) =
      ((Real.exp (s / 2) : ℝ) : ℂ) • lam D N A := (MG_lam_smul D N A _).symm
  have hz₀eq : charFlowZ (lam D N A) z (-s) = ((Real.exp (s / 2) : ℝ) : ℂ) *
      (z + mExt (lam D N A) z) - ((Real.exp (-s / 2) : ℝ) : ℂ) * mExt (lam D N A) z := by
    unfold charFlowZ
    rw [show -(-s) / 2 = s / 2 by ring]
  have hz₀im : (charFlowZ (lam D N A) z (-s)).im = Real.exp (s / 2) *
      (z.im + (mExt (lam D N A) z).im) - Real.exp (-s / 2) * (mExt (lam D N A) z).im := by
    rw [hz₀eq]
    simp only [Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
  have hm₀im : (mExt (((Real.exp (s / 2) : ℝ) : ℂ) • lam D N A)
      (charFlowZ (lam D N A) z (-s))).im = Real.exp (-s / 2) * (mExt (lam D N A) z).im := by
    rw [hm₀]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hz₀n : ‖charFlowZ (lam D N A) z (-s)‖ ≤ 10 := by
    rw [hz₀eq]
    have hw1 : Real.exp (-s / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    calc _ ≤ ‖((Real.exp (s / 2) : ℝ) : ℂ) * (z + mExt (lam D N A) z)‖ +
          ‖((Real.exp (-s / 2) : ℝ) : ℂ) * mExt (lam D N A) z‖ := norm_sub_le _ _
      _ ≤ Real.exp (s / 2) * (‖z‖ + ‖mExt (lam D N A) z‖) +
          Real.exp (-s / 2) * ‖mExt (lam D N A) z‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
          gcongr
          exact norm_add_le _ _
      _ ≤ 2 * (31 / 10 + 1) + 1 * 1 := by gcongr
      _ ≤ 10 := by norm_num
  -- admissibility (`flowAdm`) of the base point
  have hadm : flowAdm D N (δA / 2) (1 / 10) εg εg 6 7 (((Real.exp (s / 2) : ℝ) : ℂ) • A)
      (charFlowZ (lam D N A) z (-s)) s := by
    unfold flowAdm specDom
    simp only [Set.mem_ofPred_eq]
    rw [hlamA, htc₀, hland, hfI, hm₀im, hz₀im]
    refine ⟨?_, ⟨by norm_num; exact hz₀n, ?_⟩, lt_of_lt_of_le (by positivity) hlo, hlo, hrl, hru,
      hs0.le, by linarith, hNηι⟩
    · rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hA0 : 0 ≤ opNorm A := norm_nonneg _
      calc Real.exp (s / 2) * opNorm A ≤ 2 * opNorm A := mul_le_mul_of_nonneg_right hv2 hA0
        _ ≤ 2 * (N : ℝ) ^ (-δA) := by linarith
        _ ≤ _ := e3
    · rw [abs_of_pos (lt_of_lt_of_le (by positivity) hlo)]; exact hsd
  -- (3.33) [flow_3_result_2] at the base point, read at the terminal point
  have hpick : ∀ w : ℂ, (w = z ∨ w = star z) → ∃ w' : ℂ,
      (w' = charFlowZ (lam D N A) z (-s) ∨ w' = star (charFlowZ (lam D N A) z (-s))) ∧
        charFlowZ (((Real.exp (s / 2) : ℝ) : ℂ) • lam D N A) w' s = w := by
    rintro w (rfl | rfl)
    · exact ⟨_, Or.inl rfl, hland⟩
    · exact ⟨_, Or.inr rfl, hlandc⟩
  obtain ⟨w₁, hw₁, hl₁⟩ := hpick z₁ h₁
  obtain ⟨w₂, hw₂, hl₂⟩ := hpick z₂ h₂
  have hmain := hN₁ N hN1' L t₀ ht₀ ht₁ _ _ s hadm w₁ w₂ hw₁ hw₂
  rw [hlamA] at hmain
  simp only [flowKmat] at hmain
  rw [hsm, hl₁, hl₂, htc₀, hfI, show flowTc (lam D N A) z + s - s = flowTc (lam D N A) z by ring]
    at hmain
  refine le_trans hmain ?_
  exact MG_final N εg τ' z.im (mExt (lam D N A) z).im hNr hz hιpos hηι (by linarith) e9

/-- Lemma 3.12 [main_lemma_G] for the Gaussian-divisible law: the block-OU law, at a time `s`
with `1 - e^{-s} ∈ [N^{-ε_g}/2, N^{-ε_g}]`, of the law of `H_{t₀}`, `t₀ ∈ [0, 1]`, built on
entry laws with constants `C`; with `C = 9` in (3.35) [main_G_es]:
`‖E L - K_θ‖₂ ≤ N^{τ'} N^{-1-ε_g} η^{-2}` at `E = γ_k`, for
`N^{-2/3+9ε_g} 𝔯(k)^{-1/3} ≤ η ≤ N^{-9ε_g}`, `θ = e^{-s} e^{-t₀} + 1 - e^{-s}`, every `k`
under (2.4) [eq:condA1]. -/
theorem main_lemma_G_theta (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (C : ℕ → ℝ) :
    ∃ εg₀ : ℝ, 0 < εg₀ ∧ ∀ εg : ℝ, 0 < εg → εg ≤ εg₀ → ∀ τ' : ℝ, 0 < τ' →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (L : EntryLaws C) (t₀ s : ℝ), 0 ≤ t₀ → t₀ ≤ 1 →
      (N : ℝ) ^ (-εg) / 2 ≤ 1 - Real.exp (-s) → 1 - Real.exp (-s) ≤ (N : ℝ) ^ (-εg) →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      (N : ℝ) ^ ((1 / 3 : ℝ) + εA) * rk D N k ^ (-(1 / 3 : ℝ)) ≤ hsNorm A →
      ∀ z : ℂ, z.re = quant (rho (lam D N A)) (D * N) k →
      (N : ℝ) ^ (-(2 / 3 : ℝ) + 9 * εg) * rk D N k ^ (-(1 / 3 : ℝ)) ≤ z.im →
      z.im ≤ (N : ℝ) ^ (-(9 * εg)) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        hsNorm (ELmat (blockOULaw D N (ouMatLaw D N L t₀) s) (lam D N A) z₁ z₂ -
            KTheta (lam D N A) (Real.exp (-s) * Real.exp (-t₀) + 1 - Real.exp (-s)) z₁ z₂) ≤
          (N : ℝ) ^ τ' * ((N : ℝ) ^ (-1 - εg) * (z.im ^ 2)⁻¹) := by
  exact ⟨min (δA / 10) (1 / 10), lt_min (by positivity) (by norm_num),
    fun εg hεg hεg₀ τ' hτ' => MG_main D hD δA εA hδA C εg hεg hεg₀ τ' hτ'⟩

end RBMTransitionEdge

end
