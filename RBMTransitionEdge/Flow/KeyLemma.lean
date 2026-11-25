module

public import RBMTransitionEdge.Flow.Comparison
public import RBMTransitionEdge.Flow.MainG

@[expose] public section

/-!
# Lemma 3.3 for the law of `H_t`

Lemma 3.3 [key_lemma_delocalized_eigenvector], (3.3) [main_EGG], for the law of `H_t` of (4.1)
[defVt], `t ∈ [0, 1/2]`, with `K_θ`, `θ = e^{-t}`: Lemma 3.12 [main_lemma_G] for a
Gaussian-divisible law with matched moments, then Lemma 3.13 [main_lemma_com].
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Scalar tools -/

/-- `x ≤ N^a` for all large `N` when `a > 0`. -/
private lemma KL_ev_pow (x a : ℝ) (ha : 0 < a) : ∀ᶠ N : ℕ in Filter.atTop, x ≤ (N : ℝ) ^ a :=
  ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop x

/-- `1 ≤ 𝔯(k) ≤ DN` of (1.4) [eq:rk] for `1 ≤ k ≤ DN`. -/
private lemma KL_rk (D N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ D * N) :
    1 ≤ rk D N k ∧ rk D N k ≤ (D : ℝ) * N := by
  unfold rk
  constructor
  · have : 1 ≤ min k (D * N + 1 - k) := by omega
    exact_mod_cast this
  · have : min k (D * N + 1 - k) ≤ D * N := by omega
    have h : ((min k (D * N + 1 - k) : ℕ) : ℝ) ≤ ((D * N : ℕ) : ℝ) := by exact_mod_cast this
    simpa using h

/-- An entry of a `D × D` matrix is at most its Hilbert-Schmidt norm. -/
private lemma KL_entry_le_hs {D : ℕ} (X : Matrix (Fin D) (Fin D) ℂ) (a b : Fin D) :
    ‖X a b‖ ≤ hsNorm X := by
  unfold hsNorm
  apply Real.le_sqrt_of_sq_le
  have h1 : ‖X a b‖ ^ 2 ≤ ∑ j, ‖X a j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖X a j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ b)
  have h2 : ∑ j, ‖X a j‖ ^ 2 ≤ ∑ i, ∑ j, ‖X i j‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖ ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ a)
  linarith

/-- `|γ_k| ≤ 21/10` for the quantile of (2.20) [eq:gammak] under `‖A‖ ≤ N^{-δ_A}`, from (2.21)
[eq:kappa_gamma_k] and the closeness of the edges to `±2`. -/
private lemma KL_gamma_abs (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N → |quant (rho (lam D N A)) (D * N) k| ≤ 21 / 10 := by
  obtain ⟨Ce, hCe, hedge⟩ := edge_close_to_edge_sc
  obtain ⟨c, C, hc, hC, N₁, h⟩ := kappa_gamma_k D hD δA hδA
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (KL_ev_pow (20 * (1 + Ce)) δA hδA)
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

/-- The parameters of the Gaussian-divisible form in Lemma 3.3 [key_lemma_delocalized_eigenvector]:
for `θ ∈ [e^{-1/2}, 1]` and `σ ∈ (0, 1/3]`, `s = -log(1 - θσ)` and
`t₀ = -log(θ(1 - σ)/(1 - θσ))` satisfy `t₀ ∈ [0, 1]`, `1 - e^{-s} = θσ ∈ [σ/2, σ]` and
`e^{-s} e^{-t₀} + 1 - e^{-s} = θ`. -/
private lemma KL_params (θ σ : ℝ) (hθ : Real.exp (-(1 / 2)) ≤ θ) (hθ1 : θ ≤ 1) (hσ0 : 0 < σ)
    (hσ3 : σ ≤ 1 / 3) :
    0 ≤ -Real.log (θ * (1 - σ) / (1 - θ * σ)) ∧ -Real.log (θ * (1 - σ) / (1 - θ * σ)) ≤ 1 ∧
    σ / 2 ≤ 1 - Real.exp (-(-Real.log (1 - θ * σ))) ∧
    1 - Real.exp (-(-Real.log (1 - θ * σ))) ≤ σ ∧
    Real.exp (-(-Real.log (1 - θ * σ))) * Real.exp (-(-Real.log (θ * (1 - σ) / (1 - θ * σ)))) +
      1 - Real.exp (-(-Real.log (1 - θ * σ))) = θ := by
  have he0 : 0 < Real.exp (-(1 / 2)) := Real.exp_pos _
  have he1 : 1 / 2 ≤ Real.exp (-(1 / 2)) := by
    linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
  have he2 : Real.exp (-(1 / 2)) ≤ 2 / 3 := by
    have h1 : 3 / 2 ≤ Real.exp (1 / 2) := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    have h2 : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [mul_le_mul_of_nonneg_left h1 he0.le]
  have hθ0 : 1 / 2 ≤ θ := he1.trans hθ
  have hden : 0 < 1 - θ * σ := by nlinarith
  have hden1 : 1 - θ * σ ≤ 1 := by nlinarith
  have hnum : 0 < θ * (1 - σ) := by
    have : 0 < 1 - σ := by linarith
    positivity
  have hr0 : 0 < θ * (1 - σ) / (1 - θ * σ) := div_pos hnum hden
  have hes : Real.exp (-(-Real.log (1 - θ * σ))) = 1 - θ * σ := by
    rw [neg_neg, Real.exp_log hden]
  have het : Real.exp (-(-Real.log (θ * (1 - σ) / (1 - θ * σ)))) =
      θ * (1 - σ) / (1 - θ * σ) := by
    rw [neg_neg, Real.exp_log hr0]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : θ * (1 - σ) / (1 - θ * σ) ≤ 1 := by
      rw [div_le_one hden]; nlinarith
    have := Real.log_nonpos hr0.le this
    linarith
  · have hge : θ * (1 - σ) ≤ θ * (1 - σ) / (1 - θ * σ) := by
      rw [le_div_iff₀ hden]; nlinarith
    have hexp : Real.exp (-1) ≤ θ * (1 - σ) / (1 - θ * σ) := by
      have : Real.exp (-1) = Real.exp (-(1 / 2)) * Real.exp (-(1 / 2)) := by
        rw [← Real.exp_add]; norm_num
      rw [this]
      nlinarith
    have := (Real.le_log_iff_exp_le hr0).2 hexp
    linarith
  · rw [hes]; nlinarith
  · rw [hes]; nlinarith
  · rw [hes, het]; field_simp; ring

set_option maxHeartbeats 1000000 in
/-- Lemma 3.3 [key_lemma_delocalized_eigenvector] for the law of `H_t` of (4.1) [defVt],
`θ = e^{-t}`, `t ∈ [0, 1/2]`, with `K_θ` (equal to `K` of (3.2) [def_K] at `t = 0`), for every
`k` under (2.4) [eq:condA1]: at `E = γ_k` and `η ∈ [c⁻¹ η_k, c η_k]`,
`η_k = N^{-2/3+ε_L} 𝔯(k)^{-1/3}`, `|(E L - K_θ)_{ab}| ≤ N^{-1-c_L} η^{-2}`. -/
theorem key_lemma_theta (D : ℕ) (hD : 2 ≤ D) (δA εA εL c : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hεL : 0 < εL) (hεL' : εL < 2 / 3) (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∃ cL : ℝ, 0 < cL ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t →
      t ≤ 1 / 2 → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      (N : ℝ) ^ ((1 / 3 : ℝ) + εA) * rk D N k ^ (-(1 / 3 : ℝ)) ≤ hsNorm A →
      ∀ z : ℂ, z.re = quant (rho (lam D N A)) (D * N) k →
      c⁻¹ * ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * rk D N k ^ (-(1 / 3 : ℝ))) ≤ z.im →
      z.im ≤ c * ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * rk D N k ^ (-(1 / 3 : ℝ))) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → ∀ a b : Fin D,
        ‖ELmat (ouMatLaw D N L t) (lam D N A) z₁ z₂ a b -
            KTheta (lam D N A) (Real.exp (-t)) z₁ z₂ a b‖ ≤
          (N : ℝ) ^ (-1 - cL) * (z.im ^ 2)⁻¹ := by
  obtain ⟨C', K₀, hmm⟩ := moment_matching C
  obtain ⟨C'', hmix⟩ := entryLaws_mix C'
  obtain ⟨εg₀, hεg₀, hG⟩ := main_lemma_G_theta D hD δA εA hδA hεA C'
  set εg : ℝ := min εg₀ (min (εL / 10) ((2 / 3 - εL) / 10)) with hεg
  have hεg0 : 0 < εg := lt_min hεg₀ (lt_min (by linarith) (by linarith))
  have hεg1 : εg ≤ εg₀ := min_le_left _ _
  have hεg2 : εg ≤ εL / 10 := (min_le_right _ _).trans (min_le_left _ _)
  have hεg3 : εg ≤ (2 / 3 - εL) / 10 := (min_le_right _ _).trans (min_le_right _ _)
  have hτ'0 : 0 < εg / 4 := by positivity
  obtain ⟨N₁, hN₁⟩ := hG εg hεg0 hεg1 (εg / 4) hτ'0
  set τ : ℝ := min (εL / 2) (1 / 4) with hτ
  have hτ0 : 0 < τ := lt_min (by linarith) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := main_lemma_com_theta D (by omega) δA τ εg |K₀| hδA hτ0 hεg0
    (by linarith) C C'' (εg / 4) hτ'0
  obtain ⟨N₃, hN₃⟩ := KL_gamma_abs D hD δA hδA
  have hc0 : 0 < c := by linarith
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
  have hev : ∀ᶠ N : ℕ in Filter.atTop, (N₁ ≤ N ∧ N₂ ≤ N ∧ N₃ ≤ N ∧ 1 ≤ N) ∧
      3 ≤ (N : ℝ) ^ εg ∧ c ≤ (N : ℝ) ^ (εL / 10) ∧ c ≤ (N : ℝ) ^ ((2 / 3 - εL) / 10) ∧
      c * D ≤ (N : ℝ) ^ (εL / 2) ∧ 2 ≤ (N : ℝ) ^ (εg / 4) := by
    filter_upwards [Filter.eventually_ge_atTop N₁, Filter.eventually_ge_atTop N₂,
      Filter.eventually_ge_atTop N₃, Filter.eventually_ge_atTop 1, KL_ev_pow 3 εg hεg0,
      KL_ev_pow c (εL / 10) (by linarith), KL_ev_pow c ((2 / 3 - εL) / 10) (by linarith),
      KL_ev_pow (c * D) (εL / 2) (by linarith), KL_ev_pow 2 (εg / 4) hτ'0]
      with N h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨εg / 2, by positivity, N₀, ?_⟩
  intro N hN L t ht0 ht1 A hA k hk hkN hhs z hz hlo hhi z₁ z₂ hz₁ hz₂ a b
  obtain ⟨⟨hNN₁, hNN₂, hNN₃, hN1⟩, hN3, hNc1, hNc2, hNcD, hN2⟩ := hN₀ N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  obtain ⟨hrk1, hrkD⟩ := KL_rk D N k hk hkN
  have hrk0 : 0 < rk D N k := by linarith
  -- the window of `main_lemma_G_theta`
  have hlo' : (N : ℝ) ^ (-(2 / 3 : ℝ) + 9 * εg) * rk D N k ^ (-(1 / 3 : ℝ)) ≤ z.im := by
    refine le_trans ?_ hlo
    have hpow1 : (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) =
        (N : ℝ) ^ (-(2 / 3 : ℝ) + 9 * εg) * (N : ℝ) ^ (εL - 9 * εg) := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    have hpow2 : c ≤ (N : ℝ) ^ (εL - 9 * εg) :=
      hNc1.trans (Real.rpow_le_rpow_of_exponent_le hN1r (by linarith))
    have hX : 0 ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + 9 * εg) * rk D N k ^ (-(1 / 3 : ℝ)) := by positivity
    have h1 : 1 ≤ c⁻¹ * (N : ℝ) ^ (εL - 9 * εg) := by
      rw [le_inv_mul_iff₀ hc0]; linarith
    calc (N : ℝ) ^ (-(2 / 3 : ℝ) + 9 * εg) * rk D N k ^ (-(1 / 3 : ℝ))
        ≤ (c⁻¹ * (N : ℝ) ^ (εL - 9 * εg)) *
          ((N : ℝ) ^ (-(2 / 3 : ℝ) + 9 * εg) * rk D N k ^ (-(1 / 3 : ℝ))) :=
          le_mul_of_one_le_left hX h1
      _ = c⁻¹ * ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * rk D N k ^ (-(1 / 3 : ℝ))) := by
          rw [hpow1]; ring
  have hhi' : z.im ≤ (N : ℝ) ^ (-(9 * εg)) := by
    refine hhi.trans ?_
    have hr : rk D N k ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hrk1 (by norm_num)
    have hNe : 0 ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) := by positivity
    calc c * ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * rk D N k ^ (-(1 / 3 : ℝ)))
        ≤ c * ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * 1) := by gcongr
      _ ≤ (N : ℝ) ^ ((2 / 3 - εL) / 10) * (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_right hNc2 hNe
      _ = (N : ℝ) ^ ((2 / 3 - εL) / 10 + (-(2 / 3 : ℝ) + εL)) := by
          rw [← Real.rpow_add hNpos]
      _ ≤ (N : ℝ) ^ (-(9 * εg)) :=
          Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  -- the point `z` lies in the spectral domain
  have hzim : 0 < z.im := by
    refine lt_of_lt_of_le ?_ hlo
    have : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * rk D N k ^ (-(1 / 3 : ℝ)) := by positivity
    positivity
  have hzdom : z ∈ specDom τ N := by
    refine ⟨?_, ?_⟩
    · have hγ := hN₃ N hNN₃ A hA k hk hkN
      have him1 : z.im ≤ 1 :=
        hhi'.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith))
      have hτ4 : (4 : ℝ) ≤ τ⁻¹ :=
        calc (4 : ℝ) = (1 / 4 : ℝ)⁻¹ := by norm_num
          _ ≤ τ⁻¹ := inv_anti₀ hτ0 (min_le_right _ _)
      refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
      rw [hz, abs_of_pos hzim]
      linarith
    · rw [abs_of_pos hzim]
      have hu : 0 < (N : ℝ) ^ (-1 + εL / 2) := Real.rpow_pos_of_pos hNpos _
      have hτe : (N : ℝ) ^ (-1 + τ) ≤ (N : ℝ) ^ (-1 + εL / 2) :=
        Real.rpow_le_rpow_of_exponent_le hN1r (by linarith [min_le_left (εL / 2) (1 / 4)])
      refine hτe.trans (le_trans ?_ hlo)
      have hDN : ((D : ℝ) * N) ^ (-(1 / 3 : ℝ)) ≤ rk D N k ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hrk0 hrkD (by norm_num)
      have hDm : (D : ℝ)⁻¹ ≤ (D : ℝ) ^ (-(1 / 3 : ℝ)) := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
      have hmul : ((D : ℝ) * N) ^ (-(1 / 3 : ℝ)) =
          (D : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(1 / 3 : ℝ)) :=
        Real.mul_rpow hD0.le hNpos.le
      have e1 : (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * (N : ℝ) ^ (-(1 / 3 : ℝ)) =
          (N : ℝ) ^ (εL / 2) * (N : ℝ) ^ (-1 + εL / 2) := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; congr 1; ring
      have hP : 1 ≤ c⁻¹ * (D : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (εL / 2) := by
        calc (1 : ℝ) = c⁻¹ * (D : ℝ)⁻¹ * (c * D) := by field_simp
          _ ≤ c⁻¹ * (D : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (εL / 2) := by gcongr
      have hNa : 0 ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) := by positivity
      calc (N : ℝ) ^ (-1 + εL / 2)
          ≤ (c⁻¹ * (D : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (εL / 2)) * (N : ℝ) ^ (-1 + εL / 2) :=
            le_mul_of_one_le_left hu.le hP
        _ = c⁻¹ * ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL) *
              ((D : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(1 / 3 : ℝ)))) := by
            rw [mul_assoc, mul_assoc, ← e1]; ring
        _ ≤ c⁻¹ * ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * rk D N k ^ (-(1 / 3 : ℝ))) := by
            rw [← hmul]; gcongr
  -- the mixture parameters
  have hσ0 : 0 < (N : ℝ) ^ (-εg) := Real.rpow_pos_of_pos hNpos _
  have hσ3 : (N : ℝ) ^ (-εg) ≤ 1 / 3 := by
    rw [Real.rpow_neg hNpos.le]
    calc ((N : ℝ) ^ εg)⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) hN3
      _ = 1 / 3 := by norm_num
  have hσ12 : (N : ℝ) ^ (-εg) ≤ 1 / 2 := by linarith
  obtain ⟨L₀, h1, h2, h3, h4⟩ := hmm L ((N : ℝ) ^ (-εg)) hσ0 hσ12
  obtain ⟨L₁, ho, hd⟩ := hmix L₀ ((N : ℝ) ^ (-εg)) hσ0 hσ12
  have heq := ouMatLaw_mix_eq D N L₀ L₁ ((N : ℝ) ^ (-εg)) t hσ0 hσ12 ht0 ho hd
  have hθ1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hθ2 : Real.exp (-(1 / 2)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := KL_params (Real.exp (-t)) ((N : ℝ) ^ (-εg)) hθ2 hθ1 hσ0 hσ3
  have hK : K₀ * (N : ℝ) ^ (-εg) ≤ |K₀| * (N : ℝ) ^ (-εg) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hσ0.le
  have hmain := hN₁ N hNN₁ L₀ _ _ hp1 hp2 hp3 hp4 A hA k hk hkN hhs z hz hlo' hhi' z₁ z₂ hz₁ hz₂
  rw [hp5] at hmain
  have hcom := hN₂ N hNN₂ L L₁
    (fun a b hab => by rw [ho]; exact (h1 a b hab).symm)
    (fun a b hab => by rw [ho, norm_sub_rev]; exact (h2 a b hab).trans hK)
    (fun a ha => by rw [hd]; exact (h3 a ha).symm)
    (by rw [hd, abs_sub_comm]; exact h4.trans hK)
    t ht0 (by linarith) A hA z hzdom z₁ z₂ hz₁ hz₂ a b
  have hsum : ELmat (ouMatLaw D N L t) (lam D N A) z₁ z₂ a b -
      KTheta (lam D N A) (Real.exp (-t)) z₁ z₂ a b =
      (ELmat (ouMatLaw D N L t) (lam D N A) z₁ z₂ a b -
        ELmat (ouMatLaw D N L₁ t) (lam D N A) z₁ z₂ a b) +
      (ELmat (blockOULaw D N (ouMatLaw D N L₀ (-Real.log (Real.exp (-t) * (1 - (N : ℝ) ^ (-εg)) /
          (1 - Real.exp (-t) * (N : ℝ) ^ (-εg))))) (-Real.log (1 - Real.exp (-t) *
          (N : ℝ) ^ (-εg)))) (lam D N A) z₁ z₂ a b -
        KTheta (lam D N A) (Real.exp (-t)) z₁ z₂ a b) := by
    rw [heq]; ring
  have hb2 := (KL_entry_le_hs _ a b).trans hmain
  rw [Matrix.sub_apply] at hb2
  rw [hsum]
  refine (norm_add_le _ _).trans ?_
  have hw : 0 ≤ (z.im ^ 2)⁻¹ := by positivity
  set Y : ℝ := (N : ℝ) ^ (εg / 4) * (N : ℝ) ^ (-1 - εg) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hYe : Y = (N : ℝ) ^ (-1 - 3 * εg / 4) := by
    rw [hY, ← Real.rpow_add hNpos]; congr 1; ring
  have hY2 : (N : ℝ) ^ (εg / 4) * Y = (N : ℝ) ^ (-1 - εg / 2) := by
    rw [hYe, ← Real.rpow_add hNpos]; congr 1; ring
  have hfin : 2 * (Y * (z.im ^ 2)⁻¹) ≤ (N : ℝ) ^ (-1 - εg / 2) * (z.im ^ 2)⁻¹ := by
    rw [← hY2]
    nlinarith [mul_le_mul_of_nonneg_right hN2 hY0, mul_nonneg hY0 hw]
  have hc1 : (N : ℝ) ^ (εg / 4) * ((N : ℝ) ^ (-1 - εg) * (z.im ^ 2)⁻¹) = Y * (z.im ^ 2)⁻¹ := by
    rw [hY]; ring
  rw [hc1] at hcom hb2
  linarith
end RBMTransitionEdge

end
