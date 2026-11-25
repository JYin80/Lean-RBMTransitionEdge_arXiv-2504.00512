module

public import RBMTransitionEdge.Det.QuantSpacing
public import RBMTransitionEdge.Flow.KeyLemma
public import RBMTransitionEdge.LocalLaw.Rigidity
public import RBMTransitionEdge.Main.Statements

@[expose] public section

/-!
# Theorem 2.1

(3.4) [eq:extend:main_evector1] for the law of `H_t` of (4.1) [defVt], `t ∈ [0, 1/2]`, every `k`
under (2.4) [eq:condA1] and every unit eigenvector in a window around `k`, from Lemma 3.3
[key_lemma_delocalized_eigenvector] and rigidity; and Theorem 2.1 [mix] at `t = 0`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Scalar tools -/

/-- `x ≤ N^a` for all large `N` when `a > 0`. -/
private lemma Mix_ev (x a : ℝ) (ha : 0 < a) : ∀ᶠ N : ℕ in Filter.atTop, x ≤ (N : ℝ) ^ a :=
  ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop x

/-- `1 ≤ 𝔯(k)` of (1.4) [eq:rk] for `1 ≤ k ≤ DN`. -/
private lemma Mix_rk_one (D N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ D * N) : 1 ≤ rk D N k := by
  unfold rk
  have : 1 ≤ min k (D * N + 1 - k) := by omega
  exact_mod_cast this

/-- `𝔯` of (1.4) [eq:rk] is `1`-Lipschitz on `⟦1, DN⟧`. -/
private lemma Mix_rk_lip (D N i k : ℕ) (hi : i ≤ D * N) (hk : k ≤ D * N) :
    rk D N k ≤ rk D N i + |(i : ℝ) - k| := by
  unfold rk
  have h : min k (D * N + 1 - k) ≤ min i (D * N + 1 - i) + (i - k) + (k - i) := by omega
  have h' : ((min k (D * N + 1 - k) : ℕ) : ℝ) ≤
      ((min i (D * N + 1 - i) + (i - k) + (k - i) : ℕ) : ℝ) := by exact_mod_cast h
  refine h'.trans (le_of_eq ?_)
  push_cast
  rcases le_total i k with hik | hik
  · rw [Nat.sub_eq_zero_of_le hik, Nat.cast_sub hik, abs_of_nonpos (by
      have : (i : ℝ) ≤ k := by exact_mod_cast hik
      linarith)]
    push_cast; ring
  · rw [Nat.sub_eq_zero_of_le hik, Nat.cast_sub hik, abs_of_nonneg (by
      have : (k : ℝ) ≤ i := by exact_mod_cast hik
      linarith)]
    push_cast; ring

/-- For `|i - k| ≤ N^c`: `𝔯(i)^{-1/3} ≤ 2 N^c 𝔯(k)^{-1/3}`. -/
private lemma Mix_rk_pow (D N i k : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ D * N) (hk1 : 1 ≤ k)
    (hk : k ≤ D * N) (c : ℝ) (hc : 0 ≤ c) (hN : (1 : ℝ) ≤ N) (hik : |(i : ℝ) - k| ≤ (N : ℝ) ^ c) :
    rk D N i ^ (-(1 / 3 : ℝ)) ≤ 2 * (N : ℝ) ^ c * rk D N k ^ (-(1 / 3 : ℝ)) := by
  have hri := Mix_rk_one D N i hi1 hi
  have hrk := Mix_rk_one D N k hk1 hk
  have hNc : 1 ≤ (N : ℝ) ^ c := Real.one_le_rpow hN hc
  have hlip := Mix_rk_lip D N i k hi hk
  have h2 : 0 < 2 * (N : ℝ) ^ c := by positivity
  have hle : rk D N k / (2 * (N : ℝ) ^ c) ≤ rk D N i := by
    rw [div_le_iff₀ h2]; nlinarith
  have h1 : rk D N i ^ (-(1 / 3 : ℝ)) ≤ (rk D N k / (2 * (N : ℝ) ^ c)) ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
  rw [Real.div_rpow (by positivity) h2.le, Real.rpow_neg h2.le, div_inv_eq_mul] at h1
  have h3 : (2 * (N : ℝ) ^ c) ^ (1 / 3 : ℝ) ≤ 2 * (N : ℝ) ^ c := by
    calc (2 * (N : ℝ) ^ c) ^ (1 / 3 : ℝ) ≤ (2 * (N : ℝ) ^ c) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 2 * (N : ℝ) ^ c := Real.rpow_one _
  have h4 : 0 ≤ rk D N k ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
  calc rk D N i ^ (-(1 / 3 : ℝ)) ≤ rk D N k ^ (-(1 / 3 : ℝ)) * (2 * (N : ℝ) ^ c) ^ (1 / 3 : ℝ) := h1
    _ ≤ rk D N k ^ (-(1 / 3 : ℝ)) * (2 * (N : ℝ) ^ c) := mul_le_mul_of_nonneg_left h3 h4
    _ = 2 * (N : ℝ) ^ c * rk D N k ^ (-(1 / 3 : ℝ)) := by ring

/-- `|γ_k| ≤ 21/10` for the quantile of (2.20) [eq:gammak] under `‖A‖ ≤ N^{-δ_A}`, from (2.21)
[eq:kappa_gamma_k] and (A.2) [edge_close_to_edge_sc]. -/
private lemma Mix_gamma_abs (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N → |quant (rho (lam D N A)) (D * N) k| ≤ 21 / 10 := by
  obtain ⟨Ce, hCe, hedge⟩ := edge_close_to_edge_sc
  obtain ⟨c, C, hc, hC, N₁, h⟩ := kappa_gamma_k D hD δA hδA
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (Mix_ev (20 * (1 + Ce)) δA hδA)
  refine ⟨max (max N₁ N₂) 1, fun N hN A hA k hk hkN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNN₁ : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNN₂ : N₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hℓ : opNorm (lam D N A) ≤ 1 / (10 * (1 + Ce)) := by
    refine (opNorm_lam_le D N A).trans ?_
    have h1 : opNorm A ≤ 1 / (20 * (1 + Ce)) := by
      refine hA.trans ?_
      rw [Real.rpow_neg hNpos.le, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) (hN₂ N hNN₂)
    calc 2 * opNorm A ≤ 2 * (1 / (20 * (1 + Ce))) := by gcongr
      _ = 1 / (10 * (1 + Ce)) := by field_simp; ring
  have hℓ10 : opNorm (lam D N A) ≤ 1 / 10 := by
    refine hℓ.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hE := hedge (Idx D N) (lam D N A) hΛ hℓ10
  have hCℓ : Ce * opNorm (lam D N A) ≤ 1 / 10 := by
    calc Ce * opNorm (lam D N A) ≤ Ce * (1 / (10 * (1 + Ce))) := by gcongr
      _ ≤ 1 / 10 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hk' : 1 ≤ D * N + 1 - k := by omega
  have hk'' : D * N + 1 - k ≤ D * N := by omega
  have hkk : D * N + 1 - (D * N + 1 - k) = k := by omega
  obtain ⟨a1, -, -, -⟩ := h N hNN₁ A hA k hk hkN
  obtain ⟨-, -, b3, -⟩ := h N hNN₁ A hA (D * N + 1 - k) hk' hk''
  rw [hkk] at b3
  have p1 : 0 ≤ c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by positivity
  have p2 : 0 ≤ c * (((D * N + 1 - k : ℕ) : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
    positivity
  have a0 := abs_nonneg (2 - Eplus (lam D N A))
  have a3 := abs_nonneg (2 + Eminus (lam D N A))
  have h2 := (abs_le.1 (show |2 - Eplus (lam D N A)| ≤ 1 / 10 by linarith)).1
  have h3 := (abs_le.1 (show |2 + Eminus (lam D N A)| ≤ 1 / 10 by linarith)).1
  rw [abs_le]; constructor <;> linarith

/-- Markov's inequality in the form `μ{ε ≤ f} ≤ ε⁻¹ ∫ f` for `f ≥ 0` and `ε > 0`. -/
private lemma Mix_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf0 : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) (ε : ℝ) (hε : 0 < ε) :
    μ {x | ε ≤ f x} ≤ ENNReal.ofReal ((∫ x, f x ∂μ) / ε) := by
  have h := mul_meas_ge_le_integral_of_nonneg hf0 hfi ε
  rw [← ofReal_measureReal (measure_ne_top μ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hε]
  linarith

/-! ### The trace `tr(Im G B Im G B)` -/

/-- `z̄ z = ‖z‖²` as a complex number. -/
private lemma Mix_star_mul (z : ℂ) : star z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- `Im G = η G G^*` for Hermitian `X`, `z = E + iη`, `η > 0`. -/
private lemma Mix_imRes {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    (2 * Complex.I)⁻¹ • (res X z - res X (star z)) = (z.im : ℂ) • (res X z * (res X z)ᴴ) := by
  obtain ⟨h1, h2⟩ := res_mul_sub X hX z hz
  have hs : res X (star z) = (res X z)ᴴ := res_conj X hX z hz
  have hX' : (X - z • (1 : Matrix ι ι ℂ))ᴴ = X - star z • (1 : Matrix ι ι ℂ) := by
    rw [Matrix.conjTranspose_sub, hX.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  have k1 : (X - star z • (1 : Matrix ι ι ℂ)) * (res X z)ᴴ = 1 := by
    have := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, hX', Matrix.conjTranspose_one] at this
  have e : res X z - (res X z)ᴴ = (z - star z) • (res X z * (res X z)ᴴ) := by
    have e1 : res X z * ((X - star z • (1 : Matrix ι ι ℂ)) - (X - z • (1 : Matrix ι ι ℂ))) *
        (res X z)ᴴ = res X z - (res X z)ᴴ := by
      rw [mul_sub, sub_mul, mul_assoc, k1, mul_one, h2, one_mul]
    rw [← e1]
    have : (X - star z • (1 : Matrix ι ι ℂ)) - (X - z • (1 : Matrix ι ι ℂ)) =
        (z - star z) • (1 : Matrix ι ι ℂ) := by
      rw [sub_smul]
      abel
    rw [this, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [hs, e, smul_smul]
  have hz2 : z - star z = (2 * Complex.I) * (z.im : ℂ) := by
    rw [Complex.star_def, Complex.sub_conj]
    push_cast
    ring
  rw [hz2, inv_mul_cancel_left₀ (by simp)]

/-- `tr(C C) = Σ_{ij} |C_{ij}|²` (real part) for Hermitian `C`. -/
private lemma Mix_trace_sq {ι : Type*} [Fintype ι] (C : Matrix ι ι ℂ) (hC : C.IsHermitian) :
    (C * C).trace.re = ∑ i, ∑ j, ‖C i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : C i j = star (C j i) := (hC.apply i j).symm
  rw [h, Mix_star_mul, norm_star]
  norm_cast

/-- `tr(Im G B Im G B) ≥ 0` for Hermitian `X`, Hermitian `B` and `Im z > 0`
(the right side of (3.5) [eq:bdd_spec] is nonnegative). -/
private lemma Mix_tr_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (B : Matrix ι ι ℂ) (hB : B.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (((2 * Complex.I)⁻¹ • (res X z - res X (star z))) * B *
        ((2 * Complex.I)⁻¹ • (res X z - res X (star z))) * B).trace.re := by
  rw [Mix_imRes X hX z hz]
  set G := res X z with hG
  set C : Matrix ι ι ℂ := Gᴴ * B * G with hC
  have hCh : C.IsHermitian := by
    unfold Matrix.IsHermitian
    simp [hC, Matrix.conjTranspose_mul, hB.eq, mul_assoc]
  have htr : ((z.im : ℂ) • (G * Gᴴ) * B * ((z.im : ℂ) • (G * Gᴴ)) * B).trace =
      ((z.im ^ 2 : ℝ) : ℂ) * (C * C).trace := by
    have e1 : (z.im : ℂ) • (G * Gᴴ) * B * ((z.im : ℂ) • (G * Gᴴ)) * B =
        ((z.im ^ 2 : ℝ) : ℂ) • (G * (Gᴴ * B * G * Gᴴ * B)) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      push_cast
      simp only [mul_assoc, sq]
    have e2 : (G * (Gᴴ * B * G * Gᴴ * B)).trace = (C * C).trace := by
      rw [Matrix.trace_mul_comm]
      simp only [hC, mul_assoc]
    rw [e1, Matrix.trace_smul, e2, smul_eq_mul]
  rw [htr, Complex.re_ofReal_mul, Mix_trace_sq C hCh]
  positivity

/-! ### Integrability -/

/-- A continuous function of `G(z) = (h + Λ - z)⁻¹`, `Im z > 0`, is integrable for a finite law
of Hermitian arrays: it is a.e. a continuous function of the array, and `|G_{kl}| ≤ η⁻¹`
confines `G` to a compact set. -/
private lemma Mix_int {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) [IsFiniteMeasure μ]
    (hherm : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (Φ : Matrix (Idx D N) (Idx D N) ℂ → ℂ)
    (hΦ : Continuous Φ) : Integrable (fun h => Φ (res (Matrix.of h + Λ) z)) μ := by
  have hc : Continuous (fun h : Idx D N → Idx D N → ℂ => res (Matrix.of (symArr h) + Λ) z) :=
    continuous_pi fun k => continuous_pi fun l =>
      (contDiff_res_symArr Λ hΛ z hz.ne' k l 0).continuous
  have hm : AEStronglyMeasurable (fun h => Φ (res (Matrix.of h + Λ) z)) μ :=
    (hΦ.comp hc).aestronglyMeasurable.congr (by
      filter_upwards [hherm] with h hh
      simp only [Function.comp, symArr_of_isHermitian h hh])
  set S : Set (Matrix (Idx D N) (Idx D N) ℂ) :=
    Set.univ.pi (fun _ => Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) z.im⁻¹)) with hS
  have hSc : IsCompact S :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn hΦ.continuousOn
  refine Integrable.of_bound hm B ?_
  filter_upwards [hherm] with h hh
  refine hB _ fun k _ l _ => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_apply_le_opNorm _ k l).trans (opNorm_res_le _ (hh.add hΛ) z hz)

/-- Every entry of `L(z₁, z₂)` of (3.1) [def_ML], `z₁, z₂ ∈ {z, z̄}`, is integrable for a finite
law of Hermitian arrays. -/
private lemma Mix_Lmat_int {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) [IsFiniteMeasure μ]
    (hherm : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (x y : Fin D) :
    Integrable (fun h => Lmat Λ h z₁ z₂ x y) μ := by
  have hg : ∀ w : ℂ, (w = z ∨ w = star z) →
      ∃ g : Matrix (Idx D N) (Idx D N) ℂ → Matrix (Idx D N) (Idx D N) ℂ, Continuous g ∧
        ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
          res (Matrix.of h + Λ) w = g (res (Matrix.of h + Λ) z) := by
    rintro w (rfl | rfl)
    · exact ⟨id, continuous_id, fun h _ => rfl⟩
    · exact ⟨Matrix.conjTranspose, continuous_id.matrix_conjTranspose,
        fun h hh => res_conj _ (hh.add hΛ) z hz⟩
  obtain ⟨g₁, hg₁, e₁⟩ := hg z₁ h₁
  obtain ⟨g₂, hg₂, e₂⟩ := hg z₂ h₂
  have hΦ : Continuous fun G : Matrix (Idx D N) (Idx D N) ℂ =>
      (D : ℂ) * ntr (g₁ G * Ea D N x * g₂ G * Ea D N y) := by
    unfold ntr
    exact continuous_const.mul (continuous_const.mul
      ((((hg₁.matrix_mul continuous_const).matrix_mul hg₂).matrix_mul
        continuous_const).matrix_trace))
  refine (Mix_int μ hherm Λ hΛ z hz _ hΦ).congr ?_
  filter_upwards [hherm] with h hh
  simp only [Lmat, e₁ h hh, e₂ h hh]

/-! ### The block weights `β = e_a - D⁻¹ 𝟙` -/

/-- The weights `β_x = 1(x = a) - D⁻¹`, so that `E_a - D⁻¹ I = Σ_x β_x E_x`. -/
private def Mix_bf (D : ℕ) (a x : Fin D) : ℝ := (if x = a then 1 else 0) - (D : ℝ)⁻¹

/-- `E_a - D⁻¹ I = Σ_x β_x E_x` with `β_x = 1(x = a) - D⁻¹`, since `Σ_x E_x = I`. -/
private lemma Mix_B_eq (D N : ℕ) (a : Fin D) :
    Ea D N a - ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) =
      ∑ x, ((Mix_bf D a x : ℝ) : ℂ) • Ea D N x := by
  ext p q
  simp only [Mix_bf, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, Ea,
    Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq
    simp only [ite_true, mul_one]
    rw [Finset.sum_eq_single p.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases hpa : p.1 = a <;> simp [hpa]
  · simp [hpq]

/-- `Σ_x β_x = 0` and `Σ_x |β_x| ≤ 2` for `β_x = 1(x = a) - D⁻¹`. -/
private lemma Mix_beta (D : ℕ) (hD : 1 ≤ D) (a : Fin D) :
    ∑ x : Fin D, Mix_bf D a x = 0 ∧ ∑ x : Fin D, |Mix_bf D a x| ≤ 2 := by
  simp only [Mix_bf]
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have hs : ∑ x : Fin D, (D : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hD0]
  have hi : ∑ x : Fin D, (if x = a then (1 : ℝ) else 0) = 1 := by simp
  refine ⟨by rw [Finset.sum_sub_distrib, hi, hs, sub_self], ?_⟩
  calc ∑ x : Fin D, |(if x = a then 1 else 0) - (D : ℝ)⁻¹|
      ≤ ∑ x : Fin D, ((if x = a then (1 : ℝ) else 0) + (D : ℝ)⁻¹) := by
        refine Finset.sum_le_sum fun x _ => (abs_sub _ _).trans (le_of_eq ?_)
        rw [abs_of_nonneg (by split_ifs <;> norm_num), abs_of_nonneg (by positivity)]
    _ = 2 := by rw [Finset.sum_add_distrib, hi, hs]; norm_num

/-- `|Σ_{x,y} β_x β_y M_{xy}| ≤ 4 b` when `Σ_x β_x = 0`, `Σ_x |β_x| ≤ 2` and
`|M_{xy} - m₀| ≤ b` for all `x, y`. -/
private lemma Mix_quad_le {D : ℕ} (β : Fin D → ℝ) (hβ0 : ∑ x, β x = 0) (hβ1 : ∑ x, |β x| ≤ 2)
    (M : Fin D → Fin D → ℂ) (m₀ : ℂ) (b : ℝ) (hb : 0 ≤ b) (hM : ∀ x y, ‖M x y - m₀‖ ≤ b) :
    ‖∑ x, ∑ y, (β x : ℂ) * (β y : ℂ) * M x y‖ ≤ 4 * b := by
  have hβc : ∑ x, (β x : ℂ) = 0 := by exact_mod_cast hβ0
  have e1 : ∑ x, ∑ y, (β x : ℂ) * (β y : ℂ) * M x y =
      ∑ x, ∑ y, (β x : ℂ) * (β y : ℂ) * (M x y - m₀) := by
    have h0 : ∑ x, ∑ y, (β x : ℂ) * (β y : ℂ) * m₀ = 0 := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, hβc, mul_zero, zero_mul, Finset.sum_const_zero]
    simp only [mul_sub, Finset.sum_sub_distrib, h0, sub_zero]
  rw [e1]
  have hs0 : 0 ≤ ∑ x, |β x| := Finset.sum_nonneg fun x _ => abs_nonneg _
  calc ‖∑ x, ∑ y, (β x : ℂ) * (β y : ℂ) * (M x y - m₀)‖
      ≤ ∑ x, ∑ y, |β x| * |β y| * b := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hM x y) (by positivity)
    _ = (∑ x, |β x|) ^ 2 * b := by
        rw [sq, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ 2 ^ 2 * b := by gcongr
    _ = 4 * b := by norm_num

/-- `E_a - D⁻¹ I` is Hermitian. -/
private lemma Mix_B_herm (D N : ℕ) (a : Fin D) :
    (Ea D N a - ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ)).IsHermitian := by
  rw [Mix_B_eq]
  refine Matrix.IsHermitian.ext fun p q => ?_
  simp only [Mix_bf, Matrix.sum_apply, Matrix.smul_apply, Ea, Matrix.diagonal_apply, smul_eq_mul,
    star_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hpq : p = q
  · subst hpq; split_ifs <;> simp
  · simp [hpq, Ne.symm hpq]

/-! ### The expectation of `η² tr(Im G B Im G B)` -/

/-- `tr(Im G B Im G B)` (real part) for `G = (h + Λ - z)⁻¹` and `B = E_a - D⁻¹ I`: the right
side of (3.5) [eq:bdd_spec] without the factor `η²`. -/
private def Mix_T {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (a : Fin D)
    (h : Idx D N → Idx D N → ℂ) : ℝ :=
  (((2 * Complex.I)⁻¹ • (res (Matrix.of h + Λ) z - res (Matrix.of h + Λ) (star z))) *
      (Ea D N a - ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
      ((2 * Complex.I)⁻¹ • (res (Matrix.of h + Λ) z - res (Matrix.of h + Λ) (star z))) *
      (Ea D N a - ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ))).trace.re

/-- (3.6) [eq:bdd_spec2] in bound form: if `|(E L - K)_{xy}| ≤ e` and
`|K_{xy} - K_{00}| ≤ b` for the four pairs `(z₁, z₂) ∈ {z, z̄}²`, then `tr(Im G B Im G B)` is
integrable, a.s. nonnegative, and its expectation is at most `4N(e + b)`. -/
private lemma Mix_expect {D N : ℕ} (hD : 1 ≤ D) (μ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ] (hherm : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (K : ℂ → ℂ → Matrix (Fin D) (Fin D) ℂ) (e b : ℝ)
    (hE : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → ∀ x y : Fin D,
      ‖ELmat μ Λ z₁ z₂ x y - K z₁ z₂ x y‖ ≤ e)
    (hK : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → ∀ x y : Fin D,
      ‖K z₁ z₂ x y - K z₁ z₂ ⟨0, hD⟩ ⟨0, hD⟩‖ ≤ b) (a : Fin D) :
    Integrable (Mix_T Λ z a) μ ∧ 0 ≤ᵐ[μ] Mix_T Λ z a ∧
      ∫ h, Mix_T Λ z a h ∂μ ≤ N * (4 * (e + b)) := by
  obtain ⟨hβ0, hβ1⟩ := Mix_beta D hD a
  set F : (Idx D N → Idx D N → ℂ) → ℂ := fun h =>
    (N : ℂ) * ∑ x, ∑ y, (Mix_bf D a x : ℂ) * (Mix_bf D a y : ℂ) * ((1 / 4 : ℂ) *
      (Lmat Λ h z (star z) x y + Lmat Λ h (star z) z x y - Lmat Λ h z z x y -
        Lmat Λ h (star z) (star z) x y)) with hF
  have hT : ∀ h, Mix_T Λ z a h = RCLike.re (F h) := by
    intro h
    simp only [Mix_T, hF]
    rw [Mix_B_eq, trImGB_eq]
    rfl
  have hzz : z = z ∨ z = star z := Or.inl rfl
  have hzs : star z = z ∨ star z = star z := Or.inr rfl
  have i1 := fun x y => Mix_Lmat_int μ hherm Λ hΛ z hz _ _ hzz hzs x y
  have i2 := fun x y => Mix_Lmat_int μ hherm Λ hΛ z hz _ _ hzs hzz x y
  have i3 := fun x y => Mix_Lmat_int μ hherm Λ hΛ z hz _ _ hzz hzz x y
  have i4 := fun x y => Mix_Lmat_int μ hherm Λ hΛ z hz _ _ hzs hzs x y
  have hLi : ∀ x y, Integrable (fun h => (Mix_bf D a x : ℂ) * (Mix_bf D a y : ℂ) *
      ((1 / 4 : ℂ) * (Lmat Λ h z (star z) x y + Lmat Λ h (star z) z x y - Lmat Λ h z z x y -
        Lmat Λ h (star z) (star z) x y))) μ := fun x y =>
    ((((i1 x y).add (i2 x y)).sub (i3 x y)).sub (i4 x y)).const_mul _ |>.const_mul _
  have hFi : Integrable F μ :=
    (integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => hLi x y).const_mul _
  have hTe : Mix_T Λ z a = fun h => RCLike.re (F h) := funext hT
  refine ⟨hTe ▸ hFi.re, ?_, ?_⟩
  · filter_upwards [hherm] with h hh
    exact Mix_tr_nonneg _ (hh.add hΛ) _ (Mix_B_herm D N a) z hz
  have hint : ∫ h, F h ∂μ = (N : ℂ) * ∑ x, ∑ y, (Mix_bf D a x : ℂ) * (Mix_bf D a y : ℂ) *
      ((1 / 4 : ℂ) * (ELmat μ Λ z (star z) x y + ELmat μ Λ (star z) z x y - ELmat μ Λ z z x y -
        ELmat μ Λ (star z) (star z) x y)) := by
    simp only [hF]
    rw [integral_const_mul, integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
      hLi x y]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_finsetSum _ fun y _ => hLi x y]
    refine Finset.sum_congr rfl fun y _ => ?_
    have j1 : Integrable (fun h => Lmat Λ h z (star z) x y + Lmat Λ h (star z) z x y) μ :=
      (i1 x y).add (i2 x y)
    have j2 : Integrable (fun h => Lmat Λ h z (star z) x y + Lmat Λ h (star z) z x y -
        Lmat Λ h z z x y) μ := j1.sub (i3 x y)
    rw [integral_const_mul, integral_const_mul, integral_sub j2 (i4 x y),
      integral_sub j1 (i3 x y), integral_add (i1 x y) (i2 x y)]
    simp only [ELmat, Matrix.of_apply]
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE z z hzz hzz ⟨0, hD⟩ ⟨0, hD⟩)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hK z z hzz hzz ⟨0, hD⟩ ⟨0, hD⟩)
  have hM : ∀ x y : Fin D, ‖(1 / 4 : ℂ) * (ELmat μ Λ z (star z) x y + ELmat μ Λ (star z) z x y -
      ELmat μ Λ z z x y - ELmat μ Λ (star z) (star z) x y) - (1 / 4 : ℂ) *
      (K z (star z) ⟨0, hD⟩ ⟨0, hD⟩ + K (star z) z ⟨0, hD⟩ ⟨0, hD⟩ - K z z ⟨0, hD⟩ ⟨0, hD⟩ -
        K (star z) (star z) ⟨0, hD⟩ ⟨0, hD⟩)‖ ≤ e + b := by
    intro x y
    have hA : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        ‖ELmat μ Λ z₁ z₂ x y - K z₁ z₂ ⟨0, hD⟩ ⟨0, hD⟩‖ ≤ e + b := fun z₁ z₂ h₁ h₂ => by
      have e1 : ELmat μ Λ z₁ z₂ x y - K z₁ z₂ ⟨0, hD⟩ ⟨0, hD⟩ =
          (ELmat μ Λ z₁ z₂ x y - K z₁ z₂ x y) + (K z₁ z₂ x y - K z₁ z₂ ⟨0, hD⟩ ⟨0, hD⟩) := by ring
      rw [e1]
      exact (norm_add_le _ _).trans (add_le_add (hE z₁ z₂ h₁ h₂ x y) (hK z₁ z₂ h₁ h₂ x y))
    have e2 : (1 / 4 : ℂ) * (ELmat μ Λ z (star z) x y + ELmat μ Λ (star z) z x y -
        ELmat μ Λ z z x y - ELmat μ Λ (star z) (star z) x y) - (1 / 4 : ℂ) *
        (K z (star z) ⟨0, hD⟩ ⟨0, hD⟩ + K (star z) z ⟨0, hD⟩ ⟨0, hD⟩ - K z z ⟨0, hD⟩ ⟨0, hD⟩ -
          K (star z) (star z) ⟨0, hD⟩ ⟨0, hD⟩) = (1 / 4 : ℂ) *
        ((ELmat μ Λ z (star z) x y - K z (star z) ⟨0, hD⟩ ⟨0, hD⟩) +
          (ELmat μ Λ (star z) z x y - K (star z) z ⟨0, hD⟩ ⟨0, hD⟩) -
          (ELmat μ Λ z z x y - K z z ⟨0, hD⟩ ⟨0, hD⟩) -
          (ELmat μ Λ (star z) (star z) x y - K (star z) (star z) ⟨0, hD⟩ ⟨0, hD⟩)) := by ring
    rw [e2, norm_mul]
    have h14 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
    rw [h14]
    have a1 := hA z (star z) hzz hzs
    have a2 := hA (star z) z hzs hzz
    have a3 := hA z z hzz hzz
    have a4 := hA (star z) (star z) hzs hzs
    have t1 := norm_sub_le (ELmat μ Λ z (star z) x y - K z (star z) ⟨0, hD⟩ ⟨0, hD⟩ +
        (ELmat μ Λ (star z) z x y - K (star z) z ⟨0, hD⟩ ⟨0, hD⟩) -
        (ELmat μ Λ z z x y - K z z ⟨0, hD⟩ ⟨0, hD⟩))
      (ELmat μ Λ (star z) (star z) x y - K (star z) (star z) ⟨0, hD⟩ ⟨0, hD⟩)
    have t2 := norm_sub_le (ELmat μ Λ z (star z) x y - K z (star z) ⟨0, hD⟩ ⟨0, hD⟩ +
        (ELmat μ Λ (star z) z x y - K (star z) z ⟨0, hD⟩ ⟨0, hD⟩))
      (ELmat μ Λ z z x y - K z z ⟨0, hD⟩ ⟨0, hD⟩)
    have t3 := norm_add_le (ELmat μ Λ z (star z) x y - K z (star z) ⟨0, hD⟩ ⟨0, hD⟩)
      (ELmat μ Λ (star z) z x y - K (star z) z ⟨0, hD⟩ ⟨0, hD⟩)
    nlinarith
  have hq := Mix_quad_le (Mix_bf D a) hβ0 hβ1 _ _ (e + b) (by linarith) hM
  rw [hTe, integral_re hFi, hint]
  refine (RCLike.re_le_norm _).trans ?_
  rw [norm_mul, RCLike.norm_natCast]
  exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg N)

/-! ### The window and the constants -/

/-- On the rigidity event of (2.24) [eq:rigidity] at `τ' = ξ`, an index `i` with `|i - k| ≤ N^c`
has `|λ_i - γ_k| ≤ η = N^{-2/3+ε_L} 𝔯(k)^{-1/3}`, by the quantile spacing near `k`. -/
private lemma Mix_win (D N i k : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ D * N) (hk1 : 1 ≤ k) (hk : k ≤ D * N)
    (hN : (1 : ℝ) ≤ N) (c ξ εL Cq ev γi γk : ℝ) (hc : 0 ≤ c) (hCq : 0 ≤ Cq)
    (hik : |(i : ℝ) - k| ≤ (N : ℝ) ^ c)
    (hrig : |ev - γi| ≤ (N : ℝ) ^ ξ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N i ^ (-(1 / 3 : ℝ))))
    (hq : |γi - γk| ≤ Cq * (N : ℝ) ^ c * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))))
    (h4 : 4 ≤ (N : ℝ) ^ (εL / 2)) (hC : 2 * Cq ≤ (N : ℝ) ^ (εL / 2)) (hξc : ξ + c ≤ εL / 2)
    (hcε : c ≤ εL / 2) :
    |ev - γk| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * rk D N k ^ (-(1 / 3 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hr := Mix_rk_pow D N i k hi1 hi hk1 hk c hc hN hik
  set Q : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ)) with hQ
  have hQ0 : 0 ≤ Q := by
    have := Mix_rk_one D N k hk1 hk
    positivity
  have hξ0 : 0 ≤ (N : ℝ) ^ ξ := Real.rpow_nonneg hN0.le _
  have hN23 : 0 ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hN0.le _
  have e1 : (N : ℝ) ^ ξ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (2 * (N : ℝ) ^ c * rk D N k ^ (-(1 / 3 : ℝ))))
      = 2 * (N : ℝ) ^ (ξ + c) * Q := by
    rw [Real.rpow_add hN0, hQ]; ring
  have hA : |ev - γi| ≤ 2 * (N : ℝ) ^ (εL / 2) * Q := by
    refine hrig.trans ?_
    calc (N : ℝ) ^ ξ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N i ^ (-(1 / 3 : ℝ)))
        ≤ (N : ℝ) ^ ξ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) *
            (2 * (N : ℝ) ^ c * rk D N k ^ (-(1 / 3 : ℝ)))) := by gcongr
      _ = 2 * (N : ℝ) ^ (ξ + c) * Q := e1
      _ ≤ 2 * (N : ℝ) ^ (εL / 2) * Q := by gcongr
  have hB : |γi - γk| ≤ Cq * (N : ℝ) ^ (εL / 2) * Q := by
    refine hq.trans ?_
    gcongr
  have hE : (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * rk D N k ^ (-(1 / 3 : ℝ)) =
      (N : ℝ) ^ (εL / 2) * (N : ℝ) ^ (εL / 2) * Q := by
    rw [← Real.rpow_add hN0, hQ, ← mul_assoc, ← Real.rpow_add hN0]
    congr 2; ring
  rw [hE]
  have hsum : (2 + Cq) * (N : ℝ) ^ (εL / 2) ≤ (N : ℝ) ^ (εL / 2) * (N : ℝ) ^ (εL / 2) := by
    have hp : 0 ≤ (N : ℝ) ^ (εL / 2) := Real.rpow_nonneg hN0.le _
    nlinarith
  calc |ev - γk| ≤ |ev - γi| + |γi - γk| := abs_sub_le _ _ _
    _ ≤ 2 * (N : ℝ) ^ (εL / 2) * Q + Cq * (N : ℝ) ^ (εL / 2) * Q := add_le_add hA hB
    _ = (2 + Cq) * (N : ℝ) ^ (εL / 2) * Q := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum hQ0

/-- The final count of the proof of (3.4) [eq:extend:main_evector1]: the rigidity term `N^{-1}`
and the `D` Markov terms `N^{2c} · 4η² · 4N(N^{-1-c_L} η^{-2} + C N/‖A‖²_HS)` add up to at most
`N^{-c}`, for `4c ≤ c_L`, `6c ≤ ε_A`, `ε_L ≤ ε_A/4` and `N η ≤ N^{ε_L - ε_A} ‖A‖_HS` (the last
from (2.4) [eq:condA1]). -/
private lemma Mix_final (N D : ℕ) (hN : (1 : ℝ) ≤ N) (c cL εL εA Cf η hs : ℝ) (hc : 0 < c)
    (hccL : 4 * c ≤ cL) (hcA : 3 * c ≤ εA / 2) (hεL : εL ≤ εA / 4) (hc2 : c ≤ 1 / 2)
    (hη : 0 < η) (hs0 : 0 < hs) (hCf : 0 < Cf)
    (hNη : (N : ℝ) * η ≤ (N : ℝ) ^ (εL - εA) * hs)
    (h1 : 48 * (D : ℝ) ≤ (N : ℝ) ^ c) (h2 : 48 * (D : ℝ) * Cf ≤ (N : ℝ) ^ εA)
    (h3 : 3 ≤ (N : ℝ) ^ (1 / 2 : ℝ)) :
    (N : ℝ) ^ (-(1 : ℝ)) + D * (4 * η ^ 2 * (N * (4 * ((N : ℝ) ^ (-1 - cL) * (η ^ 2)⁻¹ +
        Cf * N / hs ^ 2))) / ((N : ℝ) ^ (-c)) ^ 2) ≤ (N : ℝ) ^ (-c) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  set x : ℝ := (N : ℝ) ^ c with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 c
  have hxi : (N : ℝ) ^ (-c) = x⁻¹ := Real.rpow_neg hN0.le c
  -- the two terms of the Markov bound
  have eA : 4 * η ^ 2 * (N * (4 * ((N : ℝ) ^ (-1 - cL) * (η ^ 2)⁻¹ + Cf * N / hs ^ 2))) =
      16 * ((N : ℝ) ^ (-cL) + Cf * ((N * η) / hs) ^ 2) := by
    have : (N : ℝ) ^ (-1 - cL) = (N : ℝ) ^ (-cL) * (N : ℝ)⁻¹ := by
      rw [show -1 - cL = -cL + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    rw [this]
    field_simp
    ring
  have hB : ((N * η) / hs) ^ 2 ≤ ((N : ℝ) ^ (εL - εA)) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rwa [div_le_iff₀ hs0]
  have hT1 : (N : ℝ) ^ (-cL) * x ^ 2 ≤ x⁻¹ * x⁻¹ := by
    have : (N : ℝ) ^ (-cL) * x ^ 2 = (N : ℝ) ^ (-cL + 2 * c) := by
      rw [Real.rpow_add hN0, hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      norm_num [mul_comm]
    rw [this, ← hxi, ← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hT2 : ((N : ℝ) ^ (εL - εA)) ^ 2 * x ^ 2 ≤ x⁻¹ * (N : ℝ) ^ (-εA) := by
    have : ((N : ℝ) ^ (εL - εA)) ^ 2 * x ^ 2 = (N : ℝ) ^ (2 * (εL - εA) + 2 * c) := by
      rw [← mul_pow, hx, ← Real.rpow_add hN0, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      norm_num
      ring_nf
    rw [this, ← hxi, ← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hV : 4 * η ^ 2 * (N * (4 * ((N : ℝ) ^ (-1 - cL) * (η ^ 2)⁻¹ + Cf * N / hs ^ 2))) /
      ((N : ℝ) ^ (-c)) ^ 2 ≤ 16 * (x⁻¹ * x⁻¹) + 16 * Cf * (x⁻¹ * (N : ℝ) ^ (-εA)) := by
    rw [eA, hxi, inv_pow, div_inv_eq_mul]
    have hp : 0 ≤ (N : ℝ) ^ (-cL) := Real.rpow_nonneg hN0.le _
    nlinarith [mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ Cf * x ^ 2)]
  -- each of the three terms is at most `N^{-c}/3`
  have hA1 : 16 * (D : ℝ) * x⁻¹ ≤ 1 / 3 := by
    rw [mul_inv_le_iff₀ hx0]; linarith
  have hεA : (N : ℝ) ^ (-εA) = ((N : ℝ) ^ εA)⁻¹ := Real.rpow_neg hN0.le εA
  have hNε : 0 < (N : ℝ) ^ εA := Real.rpow_pos_of_pos hN0 εA
  have hA2 : 16 * (D : ℝ) * Cf * (N : ℝ) ^ (-εA) ≤ 1 / 3 := by
    rw [hεA, mul_inv_le_iff₀ hNε]; linarith
  have hA3 : (N : ℝ) ^ (-(1 : ℝ)) ≤ x⁻¹ / 3 := by
    have e : (N : ℝ) ^ (-(1 : ℝ)) = x⁻¹ * (N : ℝ) ^ (-(1 - c)) := by
      rw [← hxi, ← Real.rpow_add hN0]; congr 1; ring
    have h12 : (N : ℝ) ^ (-(1 - c)) ≤ ((N : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
      rw [← Real.rpow_neg hN0.le]
      exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    have h13 : ((N : ℝ) ^ (1 / 2 : ℝ))⁻¹ ≤ 1 / 3 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h3
    rw [e]
    have : 0 < x⁻¹ := inv_pos.mpr hx0
    nlinarith
  have hxi0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hNe0 : 0 ≤ (N : ℝ) ^ (-εA) := Real.rpow_nonneg hN0.le _
  calc (N : ℝ) ^ (-(1 : ℝ)) + D * (4 * η ^ 2 * (N * (4 * ((N : ℝ) ^ (-1 - cL) * (η ^ 2)⁻¹ +
        Cf * N / hs ^ 2))) / ((N : ℝ) ^ (-c)) ^ 2)
      ≤ x⁻¹ / 3 + D * (16 * (x⁻¹ * x⁻¹) + 16 * Cf * (x⁻¹ * (N : ℝ) ^ (-εA))) :=
        add_le_add hA3 (mul_le_mul_of_nonneg_left hV hD0)
    _ = x⁻¹ / 3 + x⁻¹ * (16 * (D : ℝ) * x⁻¹) + x⁻¹ * (16 * (D : ℝ) * Cf * (N : ℝ) ^ (-εA)) := by
        ring
    _ ≤ x⁻¹ / 3 + x⁻¹ * (1 / 3) + x⁻¹ * (1 / 3) := by gcongr
    _ = (N : ℝ) ^ (-c) := by rw [hxi]; ring

/-- (3.4) [eq:extend:main_evector1] for the law of `H_t` of (4.1) [defVt], every `t ∈ [0, 1/2]`
and every `k` under (2.4) [eq:condA1], for all unit eigenvectors (worst case): outside
probability `N^{-c}`, `|u^*(E_a - D⁻¹) w| < N^{-c}` for all unit eigenvectors `u, w` of
`λ_i, λ_j`, `|i - k|, |j - k| ≤ N^c`, and all `a`. -/
theorem evec_window (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (C : ℕ → ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t →
      t ≤ 1 / 2 → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      (N : ℝ) ^ ((1 / 3 : ℝ) + εA) * rk D N k ^ (-(1 / 3 : ℝ)) ≤ hsNorm A →
        ouMatLaw D N L t {h | ∃ i j : ℕ, 1 ≤ i ∧ i ≤ D * N ∧ 1 ≤ j ∧ j ≤ D * N ∧
            |(i : ℝ) - k| ≤ (N : ℝ) ^ c ∧ |(j : ℝ) - k| ≤ (N : ℝ) ^ c ∧
            ∃ u w : Idx D N → ℂ, IsUnitEigvec (Matrix.of h + lam D N A)
              (eigK (Matrix.of h + lam D N A) i) u ∧
            IsUnitEigvec (Matrix.of h + lam D N A) (eigK (Matrix.of h + lam D N A) j) w ∧
            ∃ a : Fin D, (N : ℝ) ^ (-c) ≤
              ‖star u ⬝ᵥ ((Ea D N a - ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *ᵥ w)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-c)) := by
  set εL : ℝ := min εA 1 / 4 with hεL
  have hεL0 : 0 < εL := by have := lt_min hεA one_pos; rw [hεL]; positivity
  have hεLA : εL ≤ εA / 4 := by have := min_le_left εA 1; rw [hεL]; linarith
  have hεL1 : εL ≤ 1 / 4 := by have := min_le_right εA 1; rw [hεL]; linarith
  obtain ⟨cL, hcL, NK, hKL⟩ :=
    key_lemma_theta D hD δA εA εL 1 hδA hεA hεL0 (by linarith) le_rfl C
  set c : ℝ := min (cL / 4) (εL / 100) with hc
  have hc0 : 0 < c := lt_min (by linarith) (by linarith)
  have hccL : c ≤ cL / 4 := min_le_left _ _
  have hcε : c ≤ εL / 100 := min_le_right _ _
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  obtain ⟨NR, hR⟩ := rigidity D (by omega) δA hδA C' (εL / 4) (by positivity) 1 one_pos
  obtain ⟨cq, Cq, hcq, hCq, NQ, hQ⟩ := quant_spacing D hD δA c hδA hc0 (by linarith)
  obtain ⟨Cf, hCf, NF, hF⟩ := flat_KTheta D hD δA (1 / 4) hδA (by norm_num)
  obtain ⟨NG, hG⟩ := Mix_gamma_abs D hD δA hδA
  have hev : ∀ᶠ N : ℕ in Filter.atTop, (NK ≤ N ∧ NR ≤ N ∧ NQ ≤ N ∧ NF ≤ N ∧ NG ≤ N ∧ 1 ≤ N) ∧
      4 ≤ (N : ℝ) ^ (εL / 2) ∧ 2 * Cq ≤ (N : ℝ) ^ (εL / 2) ∧ 48 * (D : ℝ) ≤ (N : ℝ) ^ c ∧
      48 * (D : ℝ) * Cf ≤ (N : ℝ) ^ εA ∧ 3 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop NK, Filter.eventually_ge_atTop NR,
      Filter.eventually_ge_atTop NQ, Filter.eventually_ge_atTop NF, Filter.eventually_ge_atTop NG,
      Filter.eventually_ge_atTop 1, Mix_ev 4 (εL / 2) (by positivity),
      Mix_ev (2 * Cq) (εL / 2) (by positivity), Mix_ev (48 * D) c hc0,
      Mix_ev (48 * D * Cf) εA hεA, Mix_ev 3 (1 / 2) (by norm_num)]
      with N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9, h10, h11⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨c, hc0, N₀, ?_⟩
  intro N hN L t ht0 ht1 A hA k hk hkN hhs
  obtain ⟨⟨hNK, hNR, hNQ, hNF, hNG, hN1⟩, h4, hCq2, h48, h48f, h3⟩ := hN₀ N hN
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hD1 : 1 ≤ D := by omega
  have hμ := hC' N L t ht0
  have := hμ.prob
  have hθ0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hθ1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hΛ := lam_isHermitian D N A
  have hrk := Mix_rk_one D N k hk hkN
  set η : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * rk D N k ^ (-(1 / 3 : ℝ)) with hη
  have hηpos : 0 < η := by
    have : 0 < rk D N k := by linarith
    positivity
  set z : ℂ := ⟨quant (rho (lam D N A)) (D * N) k, η⟩ with hz
  have hzre : z.re = quant (rho (lam D N A)) (D * N) k := rfl
  have hzim : z.im = η := rfl
  have hzpos : 0 < z.im := hηpos
  -- Lemma 3.3 at `z`, and (A.11) for `K_θ`
  have hkey := hKL N hNK L t ht0 ht1 A hA k hk hkN hhs z hzre (by rw [hzim, inv_one, one_mul])
    (by rw [hzim, one_mul])
  have hη1 : η ≤ 1 := by
    have a1 : (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
    have a2 : rk D N k ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hrk (by norm_num)
    exact (mul_le_mul a1 a2 (Real.rpow_nonneg (by linarith) _) zero_le_one).trans (by norm_num)
  have hz4 : ‖z‖ ≤ (1 / 4 : ℝ)⁻¹ := by
    have hγ := hG N hNG A hA k hk hkN
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    rw [hzre, hzim, abs_of_pos hηpos]
    norm_num
    linarith
  have hflat := hF N hNF A hA z hz4 hzpos
  have hs0 : 0 < hsNorm A := lt_of_lt_of_le (by positivity) hhs
  have hexp := fun a => Mix_expect hD1 (ouMatLaw D N L t) hμ.herm (lam D N A) hΛ z hzpos
    (fun z₁ z₂ => KTheta (lam D N A) (Real.exp (-t)) z₁ z₂) ((N : ℝ) ^ (-1 - cL) * (z.im ^ 2)⁻¹)
    (Cf * N / hsNorm A ^ 2) (fun z₁ z₂ h₁ h₂ x y => hkey z₁ z₂ h₁ h₂ x y)
    (fun z₁ z₂ h₁ h₂ x y => by
      have := (hflat z₁ z₂ h₁ h₂ (Real.exp (-t)) hθ0 hθ1).2 x y ⟨0, hD1⟩ ⟨0, hD1⟩
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact this) a
  -- the rigidity event (2.24) [eq:rigidity] at `τ' = ε_L/4`
  have hrig := hR N hNR (Real.exp (-t)) hθ0 hθ1 (ouMatLaw D N L t) hμ A hA
  -- the bad event lies in the rigidity event, the non-Hermitian event and the Markov events
  have hsub : {h : Idx D N → Idx D N → ℂ | ∃ i j : ℕ, 1 ≤ i ∧ i ≤ D * N ∧ 1 ≤ j ∧ j ≤ D * N ∧
      |(i : ℝ) - k| ≤ (N : ℝ) ^ c ∧ |(j : ℝ) - k| ≤ (N : ℝ) ^ c ∧
      ∃ u w : Idx D N → ℂ, IsUnitEigvec (Matrix.of h + lam D N A)
        (eigK (Matrix.of h + lam D N A) i) u ∧
      IsUnitEigvec (Matrix.of h + lam D N A) (eigK (Matrix.of h + lam D N A) j) w ∧
      ∃ a : Fin D, (N : ℝ) ^ (-c) ≤
        ‖star u ⬝ᵥ ((Ea D N a - ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *ᵥ w)‖} ⊆
      {h : Idx D N → Idx D N → ℂ | ∃ k : ℕ, 1 ≤ k ∧ k ≤ D * N ∧
          (N : ℝ) ^ (εL / 4) * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) <
            |eigK (Matrix.of h + lam D N A) k - quant (rho (lam D N A)) (D * N) k|} ∪
        {h : Idx D N → Idx D N → ℂ | ¬ (Matrix.of h).IsHermitian} ∪
        ⋃ a : Fin D, {h : Idx D N → Idx D N → ℂ |
          ((N : ℝ) ^ (-c)) ^ 2 ≤ 4 * z.im ^ 2 * Mix_T (lam D N A) z a h} := by
    rintro h ⟨i, j, hi1, hi2, hj1, hj2, hik, hjk, u, w, hu, hw, a, ha⟩
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_lt,
      not_not, not_and, not_le] at hnot
    obtain ⟨⟨hnR, hh⟩, hnX⟩ := hnot
    have hX := hh.add hΛ
    have hwin : ∀ i : ℕ, 1 ≤ i → i ≤ D * N → |(i : ℝ) - k| ≤ (N : ℝ) ^ c →
        |eigK (Matrix.of h + lam D N A) i - z.re| ≤ z.im := by
      intro i hi1 hi2 hik
      rw [hzre, hzim]
      exact Mix_win D N i k hi1 hi2 hk hkN hN1r c (εL / 4) εL Cq _ _ _ hc0.le hCq.le hik
        (hnR i hi1 hi2) (hQ N hNQ A hA i k hi1 hi2 hk hkN hik).1 h4 hCq2 (by linarith)
        (by linarith)
    have hpl := evec_proj_le (Matrix.of h + lam D N A) hX _ (Mix_B_herm D N a) z hzpos u w _ _
      hu hw (hwin i hi1 hi2 hik) (hwin j hj1 hj2 hjk)
    refine absurd ?_ (not_le.mpr (hnX a))
    calc ((N : ℝ) ^ (-c)) ^ 2
        ≤ ‖star u ⬝ᵥ ((Ea D N a - ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *ᵥ w)‖ ^ 2 :=
          pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) ha 2
      _ ≤ 4 * z.im ^ 2 * Mix_T (lam D N A) z a h := hpl
  -- Markov on each `4 η² tr(Im G B_a Im G B_a)`
  set V : ℝ := 4 * z.im ^ 2 * (N * (4 * ((N : ℝ) ^ (-1 - cL) * (z.im ^ 2)⁻¹ +
    Cf * N / hsNorm A ^ 2))) / ((N : ℝ) ^ (-c)) ^ 2 with hV
  have hε : 0 < ((N : ℝ) ^ (-c)) ^ 2 := by positivity
  have hmark : ∀ a : Fin D, ouMatLaw D N L t {h : Idx D N → Idx D N → ℂ |
      ((N : ℝ) ^ (-c)) ^ 2 ≤ 4 * z.im ^ 2 * Mix_T (lam D N A) z a h} ≤ ENNReal.ofReal V := by
    intro a
    obtain ⟨hi, hn, hb⟩ := hexp a
    refine (Mix_markov _ (fun h => 4 * z.im ^ 2 * Mix_T (lam D N A) z a h) ?_ (hi.const_mul _)
      _ hε).trans (ENNReal.ofReal_le_ofReal ?_)
    · filter_upwards [hn] with h hh
      exact mul_nonneg (by positivity) hh
    · rw [hV, integral_const_mul]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) hε.le
  have hV0 : 0 ≤ V := by
    rw [hV]
    have : 0 ≤ (N : ℝ) ^ (-1 - cL) := Real.rpow_nonneg hNpos.le _
    positivity
  have hNη : (N : ℝ) * z.im ≤ (N : ℝ) ^ (εL - εA) * hsNorm A := by
    rw [hzim, hη]
    have e : (N : ℝ) * ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * rk D N k ^ (-(1 / 3 : ℝ))) =
        (N : ℝ) ^ (εL - εA) * ((N : ℝ) ^ ((1 / 3 : ℝ) + εA) * rk D N k ^ (-(1 / 3 : ℝ))) := by
      have e1 : (N : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) = (N : ℝ) ^ (1 + (-(2 / 3 : ℝ) + εL)) := by
        rw [Real.rpow_add hNpos 1, Real.rpow_one]
      rw [← mul_assoc, e1, ← mul_assoc, ← Real.rpow_add hNpos]
      congr 2; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hhs (Real.rpow_nonneg hNpos.le _)
  have hfin := Mix_final N D hN1r c cL εL εA Cf z.im (hsNorm A) hc0 (by linarith) (by linarith)
    hεLA (by linarith) hzpos hs0 hCf hNη h48 h48f h3
  calc ouMatLaw D N L t _ ≤ ouMatLaw D N L t _ := measure_mono hsub
    _ ≤ ouMatLaw D N L t {h : Idx D N → Idx D N → ℂ | ∃ k : ℕ, 1 ≤ k ∧ k ≤ D * N ∧
          (N : ℝ) ^ (εL / 4) * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) <
            |eigK (Matrix.of h + lam D N A) k - quant (rho (lam D N A)) (D * N) k|} +
        ouMatLaw D N L t {h : Idx D N → Idx D N → ℂ | ¬ (Matrix.of h).IsHermitian} +
        ∑ a : Fin D, ouMatLaw D N L t {h : Idx D N → Idx D N → ℂ |
          ((N : ℝ) ^ (-c)) ^ 2 ≤ 4 * z.im ^ 2 * Mix_T (lam D N A) z a h} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _)
          (measure_iUnion_fintype_le _ _))
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(1 : ℝ))) + 0 + ∑ _a : Fin D, ENNReal.ofReal V := by
        rw [ae_iff.mp hμ.herm]
        exact add_le_add (add_le_add hrig le_rfl) (Finset.sum_le_sum fun a _ => hmark a)
    _ = ENNReal.ofReal ((N : ℝ) ^ (-(1 : ℝ)) + D * V) := by
        rw [add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_add (Real.rpow_nonneg hNpos.le _) (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg D), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-c)) := ENNReal.ofReal_le_ofReal hfin

/-! ### The map `w ↦ H` -/

/-- Every entry of the Wigner matrix `wig n c` is a measurable function of the coordinates. -/
private lemma Mix_meas_wig (n : ℕ) (i j : Fin n) :
    Measurable fun c : Coords n => wig n c i j := by
  unfold wig
  by_cases h1 : i = j
  · simp only [h1, ite_true]
    exact measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_pi_apply j).comp measurable_fst))
  · by_cases h2 : i < j
    · simp only [h1, h2, ite_true, ite_false]
      exact measurable_const.mul
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd))
    · simp only [h1, h2, ite_false]
      exact measurable_const.mul ((continuous_star (R := ℂ)).measurable.comp
        ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)))

/-- The block matrix `H` of (1.3) [matrix_H], as an array, is a measurable function of the
coordinates of its blocks. -/
private lemma Mix_meas_phi (D N : ℕ) :
    Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) := by
  have hb : ∀ p q : Idx D N, Measurable fun w : Fin D → Coords N => blockH D N w p q := by
    intro p q
    by_cases h : p.1 = q.1
    · simp only [blockH, h, ↓reduceIte]
      exact (Mix_meas_wig N p.2 q.2).comp (measurable_pi_apply q.1)
    · simp only [blockH, h, ↓reduceIte]
      exact measurable_const
  exact measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => hb p q

/-- Theorem 2.1 [mix]. -/
theorem mix : MixStatement := by
  intro D hD δA εA hδA hεA C
  obtain ⟨c, hc, N₀, h⟩ := evec_window D hD δA εA hδA hεA C
  refine ⟨c, hc, N₀, fun N hN L A hA k hk hkN hhs => ?_⟩
  have h0 := h N hN L 0 le_rfl (by norm_num) A hA k hk hkN hhs
  rw [ouMatLaw_zero] at h0
  refine le_trans (le_trans (measure_mono ?_)
    (Measure.le_map_apply (Mix_meas_phi D N).aemeasurable _)) h0
  rintro w ⟨u, hu, a, ha⟩
  have e : Matrix.of (Matrix.of.symm (blockH D N w)) + lam D N A = HLam D N A w := by
    rw [Equiv.apply_symm_apply]; rfl
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, e]
  have hkk : |(k : ℝ) - k| ≤ (N : ℝ) ^ c := by
    rw [sub_self, abs_zero]; exact Real.rpow_nonneg (Nat.cast_nonneg N) _
  refine ⟨k, k, hk, hkN, hk, hkN, hkk, hkk, u, u, hu, hu, a, ?_⟩
  rw [← blockMass_sub_eq u hu.2 a, Complex.norm_real, Real.norm_eq_abs]
  exact ha

end RBMTransitionEdge

end
