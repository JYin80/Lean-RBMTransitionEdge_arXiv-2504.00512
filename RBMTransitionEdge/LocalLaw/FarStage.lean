module

public import RBMTransitionEdge.LocalLaw.FarDet
public import RBMTransitionEdge.LocalLaw.FluctNet
public import RBMTransitionEdge.LocalLaw.Uniform

@[expose] public section

/-!
# One step of the continuity argument far from the spectrum

The far level `{4 ≤ |E| ≤ N^{δ₁}, ℓ_N ≤ η ≤ 2}`, its control parameter, and one step of the
bootstrap on it, for the far region of Lemma 2.9 [lem_loc].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- One level `{4 ≤ |E| ≤ N^{δ₁}, ℓ_N ≤ η ≤ 2}` of the continuity argument far from the
spectrum. -/
def farLev (δ₁ : ℝ) (ℓ : ℕ → ℝ) (N : ℕ) : Set ℂ :=
  {z | 4 ≤ |z.re| ∧ |z.re| ≤ (N : ℝ) ^ δ₁ ∧ ℓ N ≤ z.im ∧ z.im ≤ 2}

/-- The control parameter `√(1/N + φ/(Nη)) + 1/(Nη)` far from the spectrum: the control
parameter `Ψ_φ` of the fluctuation bounds with `Im m/(Nη)` replaced by its bound `1/N`. -/
def psiFar (N : ℕ) (z : ℂ) (φ : ℝ) : ℝ :=
  Real.sqrt (1 / (N : ℝ) + φ / ((N : ℝ) * z.im)) + 1 / ((N : ℝ) * z.im)

/-! ### Elementary facts on the far level -/

/-- Membership of `E + iη` in the far level. -/
private lemma FarStage_mem_line (δ₁ : ℝ) (ℓ : ℕ → ℝ) (N : ℕ) (E η : ℝ) :
    ((E : ℂ) + (η : ℂ) * Complex.I) ∈ farLev δ₁ ℓ N ↔
      4 ≤ |E| ∧ |E| ≤ (N : ℝ) ^ δ₁ ∧ ℓ N ≤ η ∧ η ≤ 2 := by
  simp [farLev]

/-- A nonempty far level has `N ≥ 1`, since `N^{δ₁} ≥ 4`. -/
private lemma FarStage_one_le {δ₁ : ℝ} {ℓ : ℕ → ℝ} {N : ℕ} {z : ℂ} (hz : z ∈ farLev δ₁ ℓ N) :
    (1 : ℝ) ≤ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exfalso
    have h1 : (4 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ δ₁ := hz.1.trans hz.2.1
    rw [Nat.cast_zero] at h1
    have := Real.zero_rpow_le_one δ₁
    linarith
  · exact_mod_cast hN

/-- On a far level with `ℓ_N ≥ N^{-1+τ}`, `τ > 0`: `η ≥ N^{-1+τ} ≥ N⁻¹ > 0`. -/
private lemma FarStage_im {δ₁ τ : ℝ} {ℓ : ℕ → ℝ} (hτ : 0 < τ)
    (hℓ : ∀ N : ℕ, (N : ℝ) ^ (-1 + τ) ≤ ℓ N) {N : ℕ} {z : ℂ} (hz : z ∈ farLev δ₁ ℓ N) :
    ((N : ℝ))⁻¹ ≤ z.im ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im ∧ 0 < z.im := by
  have hN := FarStage_one_le hz
  have h1 : (N : ℝ) ^ (-1 + τ) ≤ z.im := (hℓ N).trans hz.2.2.1
  have h2 : ((N : ℝ))⁻¹ ≤ (N : ℝ) ^ (-1 + τ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have h3 : 0 < ((N : ℝ))⁻¹ := inv_pos.mpr (by linarith)
  exact ⟨h2.trans h1, h1, lt_of_lt_of_le h3 (h2.trans h1)⟩

/-- `N^a ≥ C` for all large `N`, when `a > 0`. -/
private lemma FarStage_ev (C a : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C ≤ (N : ℝ) ^ a := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop C)

/-! ### Operator norms and block traces -/

/-- The operator norm of a difference. -/
private lemma FarStage_opNorm_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ) : opNorm (X - Y) ≤ opNorm X + opNorm Y := by
  unfold opNorm
  rw [map_sub]
  exact norm_sub_le _ _

open scoped Matrix.Norms.L2Operator in
/-- The block projections are contractions: `‖E_a‖ ≤ 1`. -/
private lemma FarStage_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  unfold opNorm Ea
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- The block traces are additive. -/
private lemma FarStage_blockTr_sub (D N : ℕ) (P Q : Matrix (Idx D N) (Idx D N) ℂ) :
    blockTr D N (P - Q) = blockTr D N P - blockTr D N Q := by
  funext a
  simp only [blockTr, Pi.sub_apply, Matrix.mul_sub, ntr, Matrix.trace_sub]
  ring

/-- `M(z) = MSol(z)` for `Im z > 0`. -/
private lemma FarStage_MExt_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (z : ℂ) (hz : 0 < z.im) : MExt Λ z = MSol Λ z := by
  simp [MExt, MSol, mExt, hz]

/-! ### The control parameter far from the spectrum -/

/-- `ψ_F ≥ 0`. -/
private lemma FarStage_psiFar_nonneg (N : ℕ) (z : ℂ) (φ : ℝ) (hz : 0 < z.im) :
    0 ≤ psiFar N z φ := by
  unfold psiFar
  have : 0 ≤ 1 / ((N : ℝ) * z.im) := by
    have := Nat.cast_nonneg (α := ℝ) N
    positivity
  exact add_nonneg (Real.sqrt_nonneg _) this

/-- `ψ_F² ≥ 1/N` for `φ ≥ 0`. -/
private lemma FarStage_psiFar_sq_ge (N : ℕ) (hN : (1 : ℝ) ≤ N) (z : ℂ) (φ : ℝ) (hz : 0 < z.im)
    (hφ : 0 ≤ φ) : ((N : ℝ))⁻¹ ≤ psiFar N z φ ^ 2 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have h1 : 0 ≤ φ / ((N : ℝ) * z.im) := by positivity
  have h2 : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
  have h3 : Real.sqrt (1 / (N : ℝ)) ≤ psiFar N z φ := by
    unfold psiFar
    have : Real.sqrt (1 / (N : ℝ)) ≤ Real.sqrt (1 / (N : ℝ) + φ / ((N : ℝ) * z.im)) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  have h4 : Real.sqrt (1 / (N : ℝ)) ^ 2 = ((N : ℝ))⁻¹ := by
    rw [Real.sq_sqrt (by positivity), one_div]
  rw [← h4]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2

/-- `ψ_F` increases in `φ` and in `1/η`. -/
private lemma FarStage_psiFar_mono (N : ℕ) (hN : (1 : ℝ) ≤ N) (z z' : ℂ) (φ φ' : ℝ)
    (hz' : 0 < z'.im) (hzz : z'.im ≤ z.im) (hφ : 0 ≤ φ) (hφφ : φ ≤ φ') :
    psiFar N z φ ≤ psiFar N z' φ' := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hz : 0 < z.im := lt_of_lt_of_le hz' hzz
  have hd : (N : ℝ) * z'.im ≤ (N : ℝ) * z.im := mul_le_mul_of_nonneg_left hzz hN0.le
  have hd0 : 0 < (N : ℝ) * z'.im := mul_pos hN0 hz'
  have h1 : 1 / ((N : ℝ) * z.im) ≤ 1 / ((N : ℝ) * z'.im) :=
    one_div_le_one_div_of_le hd0 hd
  have h2 : φ / ((N : ℝ) * z.im) ≤ φ' / ((N : ℝ) * z'.im) :=
    div_le_div₀ (hφ.trans hφφ) hφφ hd0 hd
  unfold psiFar
  have := Real.sqrt_le_sqrt (show 1 / (N : ℝ) + φ / ((N : ℝ) * z.im) ≤
    1 / (N : ℝ) + φ' / ((N : ℝ) * z'.im) by linarith)
  linarith

/-- `Ψ_φ ≤ ψ_F` where `Im m ≤ η/7`: then `Im m/(Nη) ≤ 1/(7N) ≤ 1/N`. -/
private lemma FarStage_psi_le {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (N : ℕ) (hN : (1 : ℝ) ≤ N) (z : ℂ) (φ : ℝ) (hz : 0 < z.im)
    (hm : (mExt Λ z).im ≤ z.im / 7) : psiPhi Λ N z φ ≤ psiFar N z φ := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hd0 : 0 < (N : ℝ) * z.im := mul_pos hN0 hz
  have h1 : ((mExt Λ z).im + φ) / ((N : ℝ) * z.im) ≤
      1 / (N : ℝ) + φ / ((N : ℝ) * z.im) := by
    rw [add_div]
    have : (mExt Λ z).im / ((N : ℝ) * z.im) ≤ 1 / (N : ℝ) := by
      rw [div_le_div_iff₀ hd0 hN0]
      nlinarith
    linarith
  unfold psiPhi psiFar
  have := Real.sqrt_le_sqrt h1
  linarith

/-- The size of the bound far from the spectrum: for `N ≥ 1`, `0 ≤ τ ≤ 1`, `0 ≤ δ₁`, `k ≥ 0`
with `(k + 14) δ₁ ≤ τ/2`, `η ≥ N^{-1+τ}` and `0 ≤ φ ≤ N^{2δ₁}`:
`N^{kδ₁} (1 + φ)⁶ ψ_F² ≤ 384 N^{-τ/2}`. -/
private lemma FarStage_bound (N : ℕ) (hN : (1 : ℝ) ≤ N) (τ δ₁ k : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hδ₁ : 0 ≤ δ₁) (hk : (k + 14) * δ₁ ≤ τ / 2) (z : ℂ) (hη : (N : ℝ) ^ (-1 + τ) ≤ z.im)
    (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ : φ ≤ (N : ℝ) ^ (2 * δ₁)) :
    (N : ℝ) ^ (k * δ₁) * (1 + φ) ^ 6 * psiFar N z φ ^ 2 ≤ 384 * (N : ℝ) ^ (-τ / 2) := by
  have hN0 : (0 : ℝ) < N := by linarith
  set u : ℝ := (N : ℝ) ^ δ₁ with hu
  set v : ℝ := (N : ℝ) ^ (-τ) with hv
  have hu1 : 1 ≤ u := Real.one_le_rpow hN hδ₁
  have hv0 : 0 < v := Real.rpow_pos_of_pos hN0 _
  have hv1 : v ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hu2 : (N : ℝ) ^ (2 * δ₁) = u ^ 2 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    ring_nf
  have hNη : 1 / ((N : ℝ) * z.im) ≤ v := by
    have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = v⁻¹ := by
      rw [hv, ← Real.rpow_neg hN0.le, neg_neg]
      conv_lhs => arg 1; rw [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hN0]
      ring_nf
    have h2 : v⁻¹ ≤ (N : ℝ) * z.im := by
      rw [← h1]
      exact mul_le_mul_of_nonneg_left hη hN0.le
    rw [one_div]
    calc ((N : ℝ) * z.im)⁻¹ ≤ (v⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hv0) h2
      _ = v := inv_inv v
  have hzim : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hη
  have hd0 : 0 < (N : ℝ) * z.im := mul_pos hN0 hzim
  have hN1 : 1 / (N : ℝ) ≤ v := by
    rw [hv, one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hφη : φ / ((N : ℝ) * z.im) ≤ u ^ 2 * v := by
    rw [div_eq_mul_one_div]
    rw [hu2] at hφ
    exact mul_le_mul hφ hNη (by positivity) (by positivity)
  set X : ℝ := 1 / (N : ℝ) + φ / ((N : ℝ) * z.im) with hX
  set Y : ℝ := 1 / ((N : ℝ) * z.im) with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hpsi : psiFar N z φ ^ 2 ≤ 6 * u ^ 2 * v := by
    have e : psiFar N z φ = Real.sqrt X + Y := rfl
    rw [e]
    have hs : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0
    have h1 : (Real.sqrt X + Y) ^ 2 ≤ 2 * X + 2 * Y ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt X - Y)]
    have h2 : Y ^ 2 ≤ v := by nlinarith
    have hu2' : 1 ≤ u ^ 2 := by nlinarith
    nlinarith
  have hφ6 : (1 + φ) ^ 6 ≤ 64 * u ^ 12 := by
    rw [hu2] at hφ
    have h1 : 1 + φ ≤ 2 * u ^ 2 := by nlinarith
    calc (1 + φ) ^ 6 ≤ (2 * u ^ 2) ^ 6 := pow_le_pow_left₀ (by linarith) h1 6
      _ = 64 * u ^ 12 := by ring
  have hpow : (N : ℝ) ^ (k * δ₁) * u ^ 14 * v ≤ (N : ℝ) ^ (-τ / 2) := by
    have e : (N : ℝ) ^ (k * δ₁) * u ^ 14 * v = (N : ℝ) ^ ((k + 14) * δ₁ - τ) := by
      rw [hu, hv, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0,
        ← Real.rpow_add hN0]
      ring_nf
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hNk : 0 ≤ (N : ℝ) ^ (k * δ₁) := Real.rpow_nonneg hN0.le _
  calc (N : ℝ) ^ (k * δ₁) * (1 + φ) ^ 6 * psiFar N z φ ^ 2
      ≤ (N : ℝ) ^ (k * δ₁) * (64 * u ^ 12) * (6 * u ^ 2 * v) := by
        gcongr
    _ = 384 * ((N : ℝ) ^ (k * δ₁) * u ^ 14 * v) := by ring
    _ ≤ 384 * (N : ℝ) ^ (-τ / 2) := by gcongr

/-- `(1 + |z|)^r ≤ (3/2)^r N^{δ₁ r}` on a far level with `η ≥ 0`, for `r ≥ 0`. -/
private lemma FarStage_zpow {δ₁ : ℝ} {ℓ : ℕ → ℝ} {N : ℕ} {z : ℂ} (hz : z ∈ farLev δ₁ ℓ N)
    (hz0 : 0 ≤ z.im) (r : ℝ) (hr : 0 ≤ r) :
    (1 + ‖z‖) ^ r ≤ (3 / 2 : ℝ) ^ r * (N : ℝ) ^ (δ₁ * r) := by
  have hN := FarStage_one_le hz
  have h2 : |z.im| ≤ 2 := by rw [abs_of_nonneg hz0]; exact hz.2.2.2
  have h := (farZ_norm_le δ₁ N z hz.1 hz.2.1 h2).2
  calc (1 + ‖z‖) ^ r ≤ (3 / 2 * (N : ℝ) ^ δ₁) ^ r :=
        Real.rpow_le_rpow (by positivity) h hr
    _ = (3 / 2 : ℝ) ^ r * (N : ℝ) ^ (δ₁ * r) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by linarith) _),
          ← Real.rpow_mul (by linarith)]

/-! ### The deterministic step far from the spectrum -/

/-- The linear inequality far from the spectrum: if `|x|_∞ ≤ 1` and the averaged errors
`1(‖R_x̃‖ ≤ 1) |⟨E_a R_x̃ H̲G⟩|` are at most `b` for every block, then
`|x|_∞ ≤ (551/451) D b`. -/
private lemma FarStage_dich (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : opNorm (lam D N A) ≤ 1 / 10)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (hE : 4 ≤ |z.re|) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ a : Fin D,
      (if opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z))) ≤ 1
        then ‖ntr (Ea D N a * resX (lam D N A) z (sigTheta D θ *ᵥ
          blockTr D N (res (H + lam D N A) z)) * hgUnder D N θ H (lam D N A) z)‖
        else 0) ≤ b)
    (hx : ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 1) :
    ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 551 / 451 * (D * b) := by
  obtain ⟨-, hR, h3, -, -⟩ := blockTr_far D N θ hθ0 hθ1 A hA H hH z hz hE hx
  have hR1 : opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ
      blockTr D N (res (H + lam D N A) z))) ≤ 1 := hR.trans (by norm_num)
  have hbt : ‖blockTr D N (resX (lam D N A) z (sigTheta D θ *ᵥ
      blockTr D N (res (H + lam D N A) z)) * hgUnder D N θ H (lam D N A) z)‖ ≤ D * b := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
    have ha := hb a
    simp only [hR1, ↓reduceIte] at ha
    simp only [blockTr]
    rw [norm_mul, Complex.norm_natCast, ← Matrix.mul_assoc]
    exact mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg D)
  calc _ ≤ _ := h3
    _ ≤ 551 / 451 * (D * b) := by gcongr

/-- The heights `η_g = 2 - g (2 - η₀)/(2N⁵)` of the points of a vertical line, `g ≤ 2N⁵`. -/
private def FarStage_eta (η₀ : ℝ) (N g : ℕ) : ℝ :=
  2 - (g : ℝ) * ((2 - η₀) / (2 * (N : ℝ) ^ 5))

/-- The heights run from `η_0 = 2` down to `η_{2N⁵} = η₀`, in steps of
`(2 - η₀)/(2N⁵) ≤ N⁻⁵`. -/
private lemma FarStage_eta_spec (η₀ : ℝ) (N : ℕ) (hN : (1 : ℝ) ≤ N) (h0 : 0 < η₀)
    (h2 : η₀ ≤ 2) :
    FarStage_eta η₀ N 0 = 2 ∧ FarStage_eta η₀ N (2 * N ^ 5) = η₀ ∧
      (∀ g ≤ 2 * N ^ 5, η₀ ≤ FarStage_eta η₀ N g ∧ FarStage_eta η₀ N g ≤ 2) ∧
      (∀ g : ℕ, FarStage_eta η₀ N (g + 1) ≤ FarStage_eta η₀ N g ∧
        FarStage_eta η₀ N g - FarStage_eta η₀ N (g + 1) ≤ (((N : ℝ))⁻¹) ^ 5) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hP : (0 : ℝ) < 2 * (N : ℝ) ^ 5 := by positivity
  set d : ℝ := (2 - η₀) / (2 * (N : ℝ) ^ 5) with hd
  have hd0 : 0 ≤ d := div_nonneg (by linarith) hP.le
  have hnd : ((2 * N ^ 5 : ℕ) : ℝ) * d = 2 - η₀ := by
    rw [hd]
    push_cast
    field_simp
  refine ⟨by simp [FarStage_eta], ?_, ?_, ?_⟩
  · simp only [FarStage_eta]
    rw [← hd, hnd]
    ring
  · intro g hg
    have hg' : (g : ℝ) ≤ ((2 * N ^ 5 : ℕ) : ℝ) := by exact_mod_cast hg
    have h1 : (g : ℝ) * d ≤ ((2 * N ^ 5 : ℕ) : ℝ) * d := mul_le_mul_of_nonneg_right hg' hd0
    have h3 : 0 ≤ (g : ℝ) * d := mul_nonneg (Nat.cast_nonneg g) hd0
    simp only [FarStage_eta]
    rw [← hd]
    constructor <;> linarith
  · intro g
    have e : FarStage_eta η₀ N g - FarStage_eta η₀ N (g + 1) = d := by
      simp only [FarStage_eta]
      push_cast
      ring
    have hdle : d ≤ (((N : ℝ))⁻¹) ^ 5 := by
      rw [hd, inv_pow, div_le_iff₀ hP]
      field_simp
      linarith
    constructor <;> linarith

/-- One step along a vertical line: for Hermitian `H`, `Λ` with `‖Λ‖ ≤ 1/10`, `N ≥ 3`,
`Im z, Im z' ≥ N⁻¹` and `|z - z'| ≤ N⁻⁵`, the block traces `x = blockTr(G - M)` move by at
most `5 N⁻³` (`‖G(z) - G(z')‖ ≤ |z - z'|/(Im z Im z')` and the Lipschitz bound of `M`). -/
private lemma FarStage_step (D N : ℕ) (hD : 1 ≤ D) (hN : (3 : ℝ) ≤ N)
    (Λ H : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (hΛ1 : opNorm Λ ≤ 1 / 10)
    (hH : H.IsHermitian) (z z' : ℂ) (hz : ((N : ℝ))⁻¹ ≤ z.im) (hz' : ((N : ℝ))⁻¹ ≤ z'.im)
    (hzz : ‖z - z'‖ ≤ (((N : ℝ))⁻¹) ^ 5) :
    ‖blockTr D N (res (H + Λ) z - MExt Λ z) - blockTr D N (res (H + Λ) z' - MExt Λ z')‖ ≤
      5 * (((N : ℝ))⁻¹) ^ 3 := by
  have hN1 : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN1⟩)⟩
  set r : ℝ := ((N : ℝ))⁻¹ with hr
  have hN0 : (0 : ℝ) < N := by linarith
  have hr0 : 0 < r := inv_pos.mpr hN0
  have hrN : r * N = 1 := by rw [hr]; field_simp
  have hz0 : 0 < z.im := lt_of_lt_of_le hr0 hz
  have hz0' : 0 < z'.im := lt_of_lt_of_le hr0 hz'
  rw [← FarStage_blockTr_sub]
  refine (blockTr_norm_le D N _).trans ?_
  have e : res (H + Λ) z - MExt Λ z - (res (H + Λ) z' - MExt Λ z') =
      (res (H + Λ) z - res (H + Λ) z') - (MSol Λ z - MSol Λ z') := by
    rw [FarStage_MExt_eq Λ z hz0, FarStage_MExt_eq Λ z' hz0']
    abel
  rw [e]
  refine (FarStage_opNorm_sub_le _ _).trans ?_
  have hG := opNorm_res_sub_le (H + Λ) (hH.add hΛ) z z' hz0 hz0'
  have hM := (MSol_lipschitz Λ hΛ hΛ1 r hr0 z z' hz hz').2
  have hG' : ‖z - z'‖ / (z.im * z'.im) ≤ r ^ 3 := by
    rw [div_le_iff₀ (mul_pos hz0 hz0')]
    have h1 : r * r ≤ z.im * z'.im := mul_le_mul hz hz' hr0.le hz0.le
    have h2 : r ^ 5 ≤ r ^ 3 * (r * r) := by ring_nf; exact le_rfl
    nlinarith [pow_pos hr0 3]
  have hM' : 25 / 16 * (1 + r⁻¹) * ‖z - z'‖ ≤ 4 * r ^ 3 := by
    have hri : r⁻¹ = N := by rw [hr, inv_inv]
    rw [hri]
    have h1 : 25 / 16 * (1 + (N : ℝ)) * ‖z - z'‖ ≤ 25 / 16 * (1 + (N : ℝ)) * r ^ 5 :=
      mul_le_mul_of_nonneg_left hzz (by positivity)
    have h2 : 25 / 16 * (1 + (N : ℝ)) * r ^ 5 ≤ 4 * r ^ 3 := by
      have e2 : 25 / 16 * (1 + (N : ℝ)) * r ^ 5 = 25 / 16 * (r + r * N) * r ^ 4 := by ring
      rw [e2, hrN]
      have hr1 : r ≤ 1 / 3 := by
        rw [hr, ← one_div]
        exact one_div_le_one_div_of_le (by norm_num) hN
      have : r ^ 4 ≤ r ^ 3 * r := by ring_nf; exact le_rfl
      nlinarith [pow_pos hr0 3, pow_pos hr0 4]
    linarith
  linarith

/-- The march down one vertical line (deterministic): for Hermitian `H`, `Λ` with
`‖Λ‖ ≤ 1/10`, `N ≥ 3`, `ℓ_N ≥ N⁻¹`, `E + iη₀` on the far level, and a bound `β` on the far
level that is non-increasing in `η`, at least `5 N⁻³` and at most `1/2`: if at every point
`E + iη_g` of the line `|x|_∞ ≤ 1` implies `|x|_∞ ≤ β`, then `|x(E + iη₀)|_∞ ≤ β(E + iη₀)`. -/
private lemma FarStage_march (D N : ℕ) (hD : 1 ≤ D) (hN : (3 : ℝ) ≤ N)
    (Λ H : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (hΛ1 : opNorm Λ ≤ 1 / 10)
    (hH : H.IsHermitian) (δ₁ : ℝ) (ℓ : ℕ → ℝ) (hℓ : ((N : ℝ))⁻¹ ≤ ℓ N) (β : ℂ → ℝ)
    (hmono : ∀ E η η' : ℝ, ((E : ℂ) + (η : ℂ) * Complex.I) ∈ farLev δ₁ ℓ N → η ≤ η' →
      η' ≤ 2 → β ((E : ℂ) + (η' : ℂ) * Complex.I) ≤ β ((E : ℂ) + (η : ℂ) * Complex.I))
    (hs : ∀ z ∈ farLev δ₁ ℓ N, 5 * (((N : ℝ))⁻¹) ^ 3 ≤ β z)
    (h1 : ∀ z ∈ farLev δ₁ ℓ N, 2 * β z ≤ 1)
    (E η₀ : ℝ) (hz : ((E : ℂ) + (η₀ : ℂ) * Complex.I) ∈ farLev δ₁ ℓ N)
    (hgood : ∀ g ≤ 2 * N ^ 5,
      ‖blockTr D N (res (H + Λ) ((E : ℂ) + (FarStage_eta η₀ N g : ℂ) * Complex.I) -
        MExt Λ ((E : ℂ) + (FarStage_eta η₀ N g : ℂ) * Complex.I))‖ ≤ 1 →
      ‖blockTr D N (res (H + Λ) ((E : ℂ) + (FarStage_eta η₀ N g : ℂ) * Complex.I) -
        MExt Λ ((E : ℂ) + (FarStage_eta η₀ N g : ℂ) * Complex.I))‖ ≤
        β ((E : ℂ) + (FarStage_eta η₀ N g : ℂ) * Complex.I)) :
    ‖blockTr D N (res (H + Λ) ((E : ℂ) + (η₀ : ℂ) * Complex.I) -
      MExt Λ ((E : ℂ) + (η₀ : ℂ) * Complex.I))‖ ≤ β ((E : ℂ) + (η₀ : ℂ) * Complex.I) := by
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hN1'
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN1⟩)⟩
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hE4, hEN, hℓη, hη2⟩ := (FarStage_mem_line δ₁ ℓ N E η₀).mp hz
  have hη0 : ((N : ℝ))⁻¹ ≤ η₀ := hℓ.trans hℓη
  have hη0' : 0 < η₀ := lt_of_lt_of_le (inv_pos.mpr hN0) hη0
  obtain ⟨he0, hen, herange, hestep⟩ := FarStage_eta_spec η₀ N hN1' hη0' hη2
  set n : ℕ := 2 * N ^ 5 with hn
  set z : ℕ → ℂ := fun g => (E : ℂ) + (FarStage_eta η₀ N g : ℂ) * Complex.I with hzdef
  have hzmem : ∀ g ≤ n, z g ∈ farLev δ₁ ℓ N := fun g hg =>
    (FarStage_mem_line δ₁ ℓ N E _).mpr
      ⟨hE4, hEN, hℓη.trans (herange g hg).1, (herange g hg).2⟩
  have hzim : ∀ g, (z g).im = FarStage_eta η₀ N g := fun g => by simp [hzdef]
  have hstep : ∀ g < n, ‖blockTr D N (res (H + Λ) (z (g + 1)) - MExt Λ (z (g + 1))) -
      blockTr D N (res (H + Λ) (z g) - MExt Λ (z g))‖ ≤ 5 * (((N : ℝ))⁻¹) ^ 3 := by
    intro g hg
    refine FarStage_step D N hD hN Λ H hΛ hΛ1 hH _ _ ?_ ?_ ?_
    · rw [hzim]; exact hη0.trans (herange (g + 1) hg).1
    · rw [hzim]; exact hη0.trans (herange g hg.le).1
    · have e : z (g + 1) - z g =
          ((FarStage_eta η₀ N (g + 1) - FarStage_eta η₀ N g : ℝ) : ℂ) * Complex.I := by
        simp only [hzdef]
        push_cast
        ring
      rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith [(hestep g).1])]
      linarith [(hestep g).2]
  have hx0 : ‖blockTr D N (res (H + Λ) (z 0) - MExt Λ (z 0))‖ ≤ 1 := by
    have hz0im : (z 0).im = 2 := by rw [hzim, he0]
    have hz0re : (z 0).re = E := by simp [hzdef]
    refine (blockTr_norm_le D N _).trans ((FarStage_opNorm_sub_le _ _).trans ?_)
    have hG := opNorm_res_le (H + Λ) (hH.add hΛ) (z 0) (by rw [hz0im]; norm_num)
    have hM := (MExt_far Λ hΛ hΛ1 (z 0) (by rw [hz0im]; norm_num) (by rw [hz0re]; exact hE4)).2.1
    rw [hz0im] at hG
    linarith
  have key := march_down n (fun g => blockTr D N (res (H + Λ) (z g) - MExt Λ (z g)))
    (fun g => β (z g)) (5 * (((N : ℝ))⁻¹) ^ 3) hstep
    (fun g hg => hmono E _ _ (hzmem (g + 1) hg) (hestep g).1 (herange g hg.le).2)
    (fun g hg => hs _ (hzmem (g + 1) hg))
    (fun g hg hx2 => hgood g hg (by linarith [h1 _ (hzmem g hg)]))
    (hgood 0 (Nat.zero_le _) hx0) n le_rfl
  have hzn : z n = (E : ℂ) + (η₀ : ℂ) * Complex.I := by simp only [hzdef, hen]
  simpa only [hzn] using key

/-- `Ψ_φ ≥ 0` for `Im z > 0`. -/
private lemma FarStage_psiPhi_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (N : ℕ) (z : ℂ) (φ : ℝ) (hz : 0 < z.im) : 0 ≤ psiPhi Λ N z φ := by
  unfold psiPhi
  have : 0 ≤ 1 / ((N : ℝ) * z.im) := by
    have := Nat.cast_nonneg (α := ℝ) N
    positivity
  exact add_nonneg (Real.sqrt_nonneg _) this

/-! ### Counting events -/

/-- A union bound over `k ≤ N⁶` events of probability `≤ N^{-(D'+6)}`. -/
private lemma FarStage_count (N k : ℕ) (hN : (1 : ℝ) ≤ N) (hk : (k : ℝ) ≤ (N : ℝ) ^ 6)
    (D' : ℝ) : (k : ENNReal) * ENNReal.ofReal ((N : ℝ) ^ (-(D' + 6))) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  have hN0 : (0 : ℝ) < N := by linarith
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h6 : (N : ℝ) ^ (6 : ℝ) = (N : ℝ) ^ (6 : ℕ) := by
    exact_mod_cast Real.rpow_natCast (N : ℝ) 6
  have e : (N : ℝ) ^ (-(D' + 6)) = (N : ℝ) ^ (-D') * ((N : ℝ) ^ (6 : ℕ))⁻¹ := by
    have h6' : (N : ℝ) ^ (-6 : ℝ) = ((N : ℝ) ^ (6 : ℕ))⁻¹ := by rw [Real.rpow_neg hN0.le, h6]
    rw [show -(D' + 6) = -D' + -6 by ring, Real.rpow_add hN0, h6']
  rw [e]
  have hp : 0 < (N : ℝ) ^ (6 : ℕ) := by positivity
  have hq : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg hN0.le _
  calc (k : ℝ) * ((N : ℝ) ^ (-D') * ((N : ℝ) ^ (6 : ℕ))⁻¹)
      = (N : ℝ) ^ (-D') * ((k : ℝ) / (N : ℝ) ^ (6 : ℕ)) := by ring
    _ ≤ (N : ℝ) ^ (-D') * 1 :=
        mul_le_mul_of_nonneg_left ((div_le_one hp).mpr hk) hq
    _ = (N : ℝ) ^ (-D') := mul_one _

/-- Two events of probability `≤ N^{-(D'+1)}` have total probability `≤ N^{-D'}`, `N ≥ 2`. -/
private lemma FarStage_two (N : ℕ) (hN : (2 : ℝ) ≤ N) (D' : ℝ) :
    ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hq : 0 ≤ (N : ℝ) ^ (-(D' + 1)) := Real.rpow_nonneg hN0.le _
  rw [← ENNReal.ofReal_add hq hq]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : (N : ℝ) ^ (-(D' + 1)) = (N : ℝ) ^ (-D') * ((N : ℝ))⁻¹ := by
    rw [show -(D' + 1) = -D' + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
  rw [e]
  have hq' : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg hN0.le _
  have h2 : 2 * ((N : ℝ))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN0]
    exact hN
  nlinarith

set_option maxHeartbeats 1000000 in
/-- One step of the continuity argument far from the spectrum, in the setting of Lemma 2.9
[lem_loc]: there is `K ≥ 1` such that, for a sequence of members (`LLSeq`), `0 < τ ≤ 1/4`,
`0 ≤ δ₁` with `K δ₁ ≤ τ`, a lower cut-off `ℓ_N ≥ N^{-1+τ}`, and an a priori bound
`|(G - M)_{st}| ≺ φ_N(z)` on `farLev δ₁ ℓ` with deterministic `N⁻¹ ≤ φ_N ≤ N^{2δ₁}`
non-increasing in `η` along vertical lines, with `ψ = psiFar`: the block traces satisfy
`|x|_∞ ≺ N^{Kδ₁/2} (1 + φ)⁶ ψ²`, and
`|(G - M)_{st}| ≺ N^{Kδ₁/4} (1 + φ)³ ψ + N^{Kδ₁/2} (1 + φ)⁶ ψ²`, in sup form over
`z ∈ farLev δ₁ ℓ`. -/
theorem far_stage : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (D : ℕ) (δA τ δ₁ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
      (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ),
      LLSeq D δA C θ μ A → 0 < τ → τ ≤ 1 / 4 → 0 ≤ δ₁ → K * δ₁ ≤ τ →
    ∀ ℓ : ℕ → ℝ, (∀ N : ℕ, (N : ℝ) ^ (-1 + τ) ≤ ℓ N) →
    ∀ φ : ℕ → ℂ → ℝ,
      (∀ N, ∀ z ∈ farLev δ₁ ℓ N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ (2 * δ₁)) →
      (∀ (N : ℕ) (E η η' : ℝ), ((E : ℂ) + (η : ℂ) * Complex.I) ∈ farLev δ₁ ℓ N → η ≤ η' →
        η' ≤ 2 → φ N ((E : ℂ) + (η' : ℂ) * Complex.I) ≤ φ N ((E : ℂ) + (η : ℂ) * Complex.I)) →
      aprioriLL D μ A (farLev δ₁ ℓ) φ →
    PrecS μ (U := fun N => {z // z ∈ farLev δ₁ ℓ N})
        (fun N w h => ‖blockTr D N (res (Matrix.of h + lam D N (A N)) w.1 -
          MExt (lam D N (A N)) w.1)‖)
        (fun N w _ => (N : ℝ) ^ (K * δ₁ / 2) * (1 + φ N w.1) ^ 6 *
          psiFar N w.1 (φ N w.1) ^ 2) ∧
      aprioriLL D μ A (farLev δ₁ ℓ)
        (fun N z => (N : ℝ) ^ (K * δ₁ / 4) * (1 + φ N z) ^ 3 * psiFar N z (φ N z) +
          (N : ℝ) ^ (K * δ₁ / 2) * (1 + φ N z) ^ 6 * psiFar N z (φ N z) ^ 2) := by
  obtain ⟨Kn, hKn1, hKn⟩ := fluct_net'
  refine ⟨4 * Kn + 56, by linarith, ?_⟩
  intro D δA τ δ₁ C θ μ A hseq hτ hτ4 hδ₁ hKδ ℓ hℓ φ hφ hmono hLL
  have hD := hseq.one_le_D
  have hZ : ∀ N, ∀ z ∈ farLev δ₁ ℓ N, ‖z‖ ≤ (N : ℝ) ^ (2 * δ₁) ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im := by
    intro N z hz
    obtain ⟨-, h2, h3⟩ := FarStage_im hτ hℓ hz
    exact ⟨(farZ_norm_le δ₁ N z hz.1 hz.2.1 (by rw [abs_of_pos h3]; exact hz.2.2.2)).1, h2⟩
  have hKn' : Kn * (2 * δ₁) ≤ τ := by nlinarith
  obtain ⟨hIso, hAvg⟩ := hKn D δA τ (2 * δ₁) C θ μ A hseq hτ (by positivity) hKn'
    (farLev δ₁ ℓ) hZ φ hφ hLL 1 le_rfl
  have hφ0 : ∀ N, ∀ z ∈ farLev δ₁ ℓ N, 0 ≤ φ N z := fun N z hz =>
    (inv_nonneg.mpr (Nat.cast_nonneg N)).trans (hφ N z hz).1
  set c : ℝ := 551 / 451 * D * (3 / 2 : ℝ) ^ (2 * Kn) with hc
  have hc1 : 1 ≤ c := by
    have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ (2 * Kn) := Real.one_le_rpow (by norm_num) (by linarith)
    have h2 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have h3 : (1 : ℝ) ≤ 551 / 451 * D := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ 551 / 451 * D * (3 / 2 : ℝ) ^ (2 * Kn) := mul_le_mul h3 h1 zero_le_one (by linarith)
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨NΛ, hNΛ⟩ := FarStage_ev 20 δA hseq.pos
  have hΛsmall : ∀ N : ℕ, NΛ ≤ N → (1 : ℝ) ≤ N → opNorm (lam D N (A N)) ≤ 1 / 10 := by
    intro N hN hN1
    have hN0 : (0 : ℝ) < N := by linarith
    have h1 := opNorm_lam_le D N (A N)
    have h2 := hseq.small N
    have h3 : (20 : ℝ) ≤ (N : ℝ) ^ δA := hNΛ N hN
    have h4 : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
      rw [Real.rpow_neg hN0.le, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) h3
    linarith
  -- the bound `β ≤ N^{τ'} N^{Kδ₁/2} (1 + φ)⁶ ψ_F²`
  have hβle : ∀ a τ' : ℝ, a ≤ τ' → ∀ N : ℕ, (1 : ℝ) ≤ N → c ≤ (N : ℝ) ^ (a / 2) →
      ∀ z ∈ farLev δ₁ ℓ N,
      c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁) * (1 + φ N z) ^ 6 *
          psiFar N z (φ N z) ^ 2 ≤
        (N : ℝ) ^ τ' * ((N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 2) * (1 + φ N z) ^ 6 *
          psiFar N z (φ N z) ^ 2) := by
    intro a τ' haτ' N hN1 hcN z hz
    have hN0 : (0 : ℝ) < N := by linarith
    have hQ : 0 ≤ (1 + φ N z) ^ 6 * psiFar N z (φ N z) ^ 2 := by
      have := hφ0 N z hz
      positivity
    have hNa : 0 ≤ (N : ℝ) ^ (a / 2) := Real.rpow_nonneg hN0.le _
    have hNk : 0 ≤ (N : ℝ) ^ (2 * Kn * δ₁) := Real.rpow_nonneg hN0.le _
    have h1 : c * (N : ℝ) ^ (a / 2) ≤ (N : ℝ) ^ τ' := by
      calc c * (N : ℝ) ^ (a / 2) ≤ (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (a / 2) :=
            mul_le_mul_of_nonneg_right hcN hNa
        _ = (N : ℝ) ^ a := by rw [← Real.rpow_add hN0]; ring_nf
        _ ≤ (N : ℝ) ^ τ' := Real.rpow_le_rpow_of_exponent_le hN1 haτ'
    have h2 : (N : ℝ) ^ (2 * Kn * δ₁) ≤ (N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
    have h3 : c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁) ≤
        (N : ℝ) ^ τ' * (N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 2) :=
      mul_le_mul h1 h2 hNk (Real.rpow_nonneg hN0.le _)
    calc c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁) * (1 + φ N z) ^ 6 *
          psiFar N z (φ N z) ^ 2
        = (c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁)) *
            ((1 + φ N z) ^ 6 * psiFar N z (φ N z) ^ 2) := by ring
      _ ≤ ((N : ℝ) ^ τ' * (N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 2)) *
            ((1 + φ N z) ^ 6 * psiFar N z (φ N z) ^ 2) := mul_le_mul_of_nonneg_right h3 hQ
      _ = _ := by ring
  -- the march on one event, at a fixed point of the far level
  have core : ∀ a : ℝ, 0 < a → a ≤ τ / 8 → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ z ∈ farLev δ₁ ℓ N,
        2 * (c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁) * (1 + φ N z) ^ 6 *
          psiFar N z (φ N z) ^ 2) ≤ 1 ∧
        opNorm (lam D N (A N)) ≤ 1 / 10 ∧
        μ N {h | ¬ ((Matrix.of h).IsHermitian ∧
          ‖blockTr D N (res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z)‖ ≤
            c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁) * (1 + φ N z) ^ 6 *
              psiFar N z (φ N z) ^ 2)} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
    intro a ha haτ D' hD'
    obtain ⟨N₁, hN₁⟩ := hAvg (a / 2) (by positivity) (D' + 6) (by linarith)
    obtain ⟨N₂, hN₂⟩ := FarStage_ev (768 * c) (τ / 4) (by positivity)
    refine ⟨max (max N₁ N₂) (max NΛ (3 * D + 3)), fun N hN z hz => ?_⟩
    have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hNΛ' : NΛ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    have hN3D : 3 * D + 3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast (show 3 ≤ N by omega)
    have hNr : (1 : ℝ) ≤ N := by linarith
    have hN0 : (0 : ℝ) < N := by linarith
    have hΛ1 := hΛsmall N hNΛ' hNr
    have hΛh := lam_isHermitian D N (A N)
    have hθ := hseq.theta N
    have hℓN : ((N : ℝ))⁻¹ ≤ ℓ N := by
      have h2 : ((N : ℝ))⁻¹ ≤ (N : ℝ) ^ (-1 + τ) := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      exact h2.trans (hℓ N)
    have hβ1 : ∀ z ∈ farLev δ₁ ℓ N, 2 * (c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁) *
        (1 + φ N z) ^ 6 * psiFar N z (φ N z) ^ 2) ≤ 1 := by
      intro z hz
      have hb := FarStage_bound N hNr τ δ₁ (2 * Kn) hτ.le (by linarith) hδ₁ (by nlinarith) z
        (FarStage_im hτ hℓ hz).2.1 (φ N z) (hφ0 N z hz) (hφ N z hz).2
      have hNa : 0 ≤ (N : ℝ) ^ (a / 2) := Real.rpow_nonneg hN0.le _
      have e1 : (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (-τ / 2) ≤ ((N : ℝ) ^ (τ / 4))⁻¹ := by
        rw [← Real.rpow_add hN0, ← Real.rpow_neg hN0.le]
        exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      have h768 := hN₂ N hN2
      have ht : 0 < (N : ℝ) ^ (τ / 4) := Real.rpow_pos_of_pos hN0 _
      calc 2 * (c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁) * (1 + φ N z) ^ 6 *
            psiFar N z (φ N z) ^ 2)
          = 2 * c * (N : ℝ) ^ (a / 2) * ((N : ℝ) ^ (2 * Kn * δ₁) * (1 + φ N z) ^ 6 *
            psiFar N z (φ N z) ^ 2) := by ring
        _ ≤ 2 * c * (N : ℝ) ^ (a / 2) * (384 * (N : ℝ) ^ (-τ / 2)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = 768 * c * ((N : ℝ) ^ (a / 2) * (N : ℝ) ^ (-τ / 2)) := by ring
        _ ≤ 768 * c * ((N : ℝ) ^ (τ / 4))⁻¹ := mul_le_mul_of_nonneg_left e1 (by positivity)
        _ ≤ 1 := by
            rw [← div_eq_mul_inv, div_le_one ht]
            exact h768
    refine ⟨hβ1 z hz, hΛ1, ?_⟩
    have hβs : ∀ z ∈ farLev δ₁ ℓ N, 5 * (((N : ℝ))⁻¹) ^ 3 ≤ c * (N : ℝ) ^ (a / 2) *
        (N : ℝ) ^ (2 * Kn * δ₁) * (1 + φ N z) ^ 6 * psiFar N z (φ N z) ^ 2 := by
      intro z hz
      have hz0 := (FarStage_im hτ hℓ hz).2.2
      have hp := FarStage_psiFar_sq_ge N hNr z (φ N z) hz0 (hφ0 N z hz)
      have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (a / 2) := Real.one_le_rpow hNr (by positivity)
      have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * Kn * δ₁) := Real.one_le_rpow hNr (by positivity)
      have h3 : (1 : ℝ) ≤ (1 + φ N z) ^ 6 := one_le_pow₀ (by linarith [hφ0 N z hz])
      have h4 : (1 : ℝ) ≤ c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁) * (1 + φ N z) ^ 6 :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hc1 h1) h2) h3
      have h5 : psiFar N z (φ N z) ^ 2 ≤ c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁) *
          (1 + φ N z) ^ 6 * psiFar N z (φ N z) ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) h4
      have hr : ((N : ℝ))⁻¹ ≤ 1 / 3 := by
        rw [← one_div]
        exact one_div_le_one_div_of_le (by norm_num) hN3
      have hr0 : 0 < ((N : ℝ))⁻¹ := inv_pos.mpr hN0
      have hr2 : (((N : ℝ))⁻¹) ^ 2 ≤ 1 / 9 := by nlinarith
      have h6 : 5 * (((N : ℝ))⁻¹) ^ 3 ≤ ((N : ℝ))⁻¹ := by
        have := mul_le_mul_of_nonneg_left hr2 hr0.le
        nlinarith
      linarith
    have hβmono : ∀ E η η' : ℝ, ((E : ℂ) + (η : ℂ) * Complex.I) ∈ farLev δ₁ ℓ N → η ≤ η' →
        η' ≤ 2 →
        c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁) *
            (1 + φ N ((E : ℂ) + (η' : ℂ) * Complex.I)) ^ 6 *
            psiFar N ((E : ℂ) + (η' : ℂ) * Complex.I)
              (φ N ((E : ℂ) + (η' : ℂ) * Complex.I)) ^ 2 ≤
          c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁) *
            (1 + φ N ((E : ℂ) + (η : ℂ) * Complex.I)) ^ 6 *
            psiFar N ((E : ℂ) + (η : ℂ) * Complex.I)
              (φ N ((E : ℂ) + (η : ℂ) * Complex.I)) ^ 2 := by
      intro E η η' hmem hηη hη2
      obtain ⟨hE4, hEN, hℓη, -⟩ := (FarStage_mem_line δ₁ ℓ N E η).mp hmem
      have hmem' : ((E : ℂ) + (η' : ℂ) * Complex.I) ∈ farLev δ₁ ℓ N :=
        (FarStage_mem_line δ₁ ℓ N E η').mpr ⟨hE4, hEN, hℓη.trans hηη, hη2⟩
      have hφφ := hmono N E η η' hmem hηη hη2
      have hz0 := (FarStage_im hτ hℓ hmem).2.2
      have hp := FarStage_psiFar_mono N hNr ((E : ℂ) + (η' : ℂ) * Complex.I)
        ((E : ℂ) + (η : ℂ) * Complex.I) _ _ hz0 (by simpa using hηη) (hφ0 N _ hmem') hφφ
      have hp0 := FarStage_psiFar_nonneg N ((E : ℂ) + (η' : ℂ) * Complex.I)
        (φ N ((E : ℂ) + (η' : ℂ) * Complex.I)) ((FarStage_im hτ hℓ hmem').2.2)
      have h6 : (1 + φ N ((E : ℂ) + (η' : ℂ) * Complex.I)) ^ 6 ≤
          (1 + φ N ((E : ℂ) + (η : ℂ) * Complex.I)) ^ 6 :=
        pow_le_pow_left₀ (by linarith [hφ0 N _ hmem']) (by linarith) 6
      have h2 := pow_le_pow_left₀ hp0 hp 2
      have hpre : 0 ≤ c * (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (2 * Kn * δ₁) :=
        mul_nonneg (mul_nonneg hc0 (Real.rpow_nonneg hN0.le _)) (Real.rpow_nonneg hN0.le _)
      have h60 : 0 ≤ (1 + φ N ((E : ℂ) + (η' : ℂ) * Complex.I)) ^ 6 := by
        have := hφ0 N _ hmem'
        positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left h6 hpre) h2 (sq_nonneg _)
        (mul_nonneg hpre (h60.trans h6))
    have hnull : μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := ae_iff.mp (hseq.mem N).herm
    obtain ⟨hE4, hEN, hℓη, hη2⟩ := (FarStage_mem_line δ₁ ℓ N z.re z.im).mp
      (by rw [Complex.re_add_im]; exact hz)
    have hη0' : 0 < z.im := (FarStage_im hτ hℓ hz).2.2
    obtain ⟨-, -, herange, -⟩ := FarStage_eta_spec z.im N hNr hη0' hη2
    have hmemg : ∀ g : Fin (2 * N ^ 5 + 1),
        ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I) ∈ farLev δ₁ ℓ N := fun g =>
      (FarStage_mem_line δ₁ ℓ N _ _).mpr ⟨hE4, hEN,
        hℓη.trans (herange g (Nat.lt_succ_iff.mp g.isLt)).1,
        (herange g (Nat.lt_succ_iff.mp g.isLt)).2⟩
    set S : Fin (2 * N ^ 5 + 1) × Fin D → Set (Idx D N → Idx D N → ℂ) := fun p =>
        {h | (N : ℝ) ^ (a / 2) *
          ((1 + ‖(z.re : ℂ) + (FarStage_eta z.im N p.1 : ℂ) * Complex.I‖) ^ (2 * Kn) *
            (1 + φ N ((z.re : ℂ) + (FarStage_eta z.im N p.1 : ℂ) * Complex.I)) ^ 6 *
            psiPhi (lam D N (A N)) N ((z.re : ℂ) + (FarStage_eta z.im N p.1 : ℂ) * Complex.I)
              (φ N ((z.re : ℂ) + (FarStage_eta z.im N p.1 : ℂ) * Complex.I)) ^ 2) <
          (if opNorm (resX (lam D N (A N))
              ((z.re : ℂ) + (FarStage_eta z.im N p.1 : ℂ) * Complex.I)
              (sigTheta D (θ N) *ᵥ blockTr D N (res (Matrix.of h + lam D N (A N))
                ((z.re : ℂ) + (FarStage_eta z.im N p.1 : ℂ) * Complex.I)))) ≤ 1 then
            ‖ntr (Ea D N p.2 * resX (lam D N (A N))
              ((z.re : ℂ) + (FarStage_eta z.im N p.1 : ℂ) * Complex.I)
              (sigTheta D (θ N) *ᵥ blockTr D N (res (Matrix.of h + lam D N (A N))
                ((z.re : ℂ) + (FarStage_eta z.im N p.1 : ℂ) * Complex.I))) *
              hgUnder D N (θ N) (Matrix.of h) (lam D N (A N))
                ((z.re : ℂ) + (FarStage_eta z.im N p.1 : ℂ) * Complex.I))‖
          else 0)} with hSdef
    have hS : ∀ p, μ N (S p) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 6))) := fun p =>
      hN₁ N hN1 (⟨_, hmemg p.1⟩, ⟨Ea D N p.2, FarStage_opNorm_Ea D N p.2⟩)
    refine le_trans (measure_mono (t := {h | ¬ (Matrix.of h).IsHermitian} ∪ ⋃ p, S p)
      ?_) ?_
    · intro h hh
      by_contra hcon
      simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_ofPred_eq,
        not_not] at hcon
      obtain ⟨hHerm, hgoodp⟩ := hcon
      apply hh
      refine ⟨hHerm, ?_⟩
      have hm := FarStage_march D N hD hN3 (lam D N (A N)) (Matrix.of h) hΛh hΛ1 hHerm δ₁ ℓ hℓN
        _ hβmono hβs hβ1 z.re z.im (by rw [Complex.re_add_im]; exact hz) ?_
      · simpa only [Complex.re_add_im] using hm
      intro g hg hx1
      have hgm := hmemg ⟨g, Nat.lt_succ_of_le hg⟩
      have hgim := (FarStage_im hτ hℓ hgm).2.2
      have hgim' : 0 ≤ ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I).im := hgim.le
      have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, by exact_mod_cast hNr⟩)⟩
      have hmf := MExt_far (lam D N (A N)) hΛh hΛ1 _ hgim hgm.1
      have hpsi := FarStage_psi_le (lam D N (A N)) N hNr _
        (φ N ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I)) hgim hmf.2.2
      have hpsi2 := pow_le_pow_left₀ (FarStage_psiPhi_nonneg _ _ _ _ hgim) hpsi 2
      have hzp := FarStage_zpow hgm hgim' (2 * Kn) (by linarith)
      have hNa : 0 ≤ (N : ℝ) ^ (a / 2) := Real.rpow_nonneg hN0.le _
      have hP6 : 0 ≤ (1 + φ N ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I)) ^ 6 := by
        have := hφ0 N _ hgm
        positivity
      have hb0 : 0 ≤ (N : ℝ) ^ (a / 2) *
          ((1 + ‖(z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I‖) ^ (2 * Kn) *
            (1 + φ N ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I)) ^ 6 *
            psiPhi (lam D N (A N)) N ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I)
              (φ N ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I)) ^ 2) := by
        have : 0 ≤ (1 + ‖(z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I‖) ^ (2 * Kn) :=
          Real.rpow_nonneg (by positivity) _
        positivity
      have hd := FarStage_dich D N (θ N) hθ.1 hθ.2 (A N) hΛ1 (Matrix.of h) hHerm _ hgim hgm.1
        _ hb0 (fun a' => not_lt.mp (hgoodp (⟨g, Nat.lt_succ_of_le hg⟩, a'))) hx1
      refine hd.trans ?_
      have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
      have e : δ₁ * (2 * Kn) = 2 * Kn * δ₁ := by ring
      rw [e] at hzp
      have hk : 0 ≤ (1 + ‖(z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I‖) ^ (2 * Kn) :=
        Real.rpow_nonneg (by positivity) _
      calc 551 / 451 * (D * ((N : ℝ) ^ (a / 2) *
            ((1 + ‖(z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I‖) ^ (2 * Kn) *
            (1 + φ N ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I)) ^ 6 *
            psiPhi (lam D N (A N)) N ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I)
              (φ N ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I)) ^ 2)))
          ≤ 551 / 451 * (D * ((N : ℝ) ^ (a / 2) *
            ((3 / 2 : ℝ) ^ (2 * Kn) * (N : ℝ) ^ (2 * Kn * δ₁) *
            (1 + φ N ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I)) ^ 6 *
            psiFar N ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I)
              (φ N ((z.re : ℂ) + (FarStage_eta z.im N g : ℂ) * Complex.I)) ^ 2))) := by
            gcongr
        _ = _ := by rw [hc]; ring
    · calc μ N ({h | ¬ (Matrix.of h).IsHermitian} ∪ ⋃ p, S p)
          ≤ μ N {h | ¬ (Matrix.of h).IsHermitian} + μ N (⋃ p, S p) := measure_union_le _ _
        _ ≤ 0 + ∑ p : Fin (2 * N ^ 5 + 1) × Fin D, ENNReal.ofReal ((N : ℝ) ^ (-(D' + 6))) :=
            add_le_add (le_of_eq hnull)
              ((measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun p _ => hS p))
        _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
            rw [zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            refine FarStage_count N _ hNr ?_ D'
            simp only [Fintype.card_prod, Fintype.card_fin]
            push_cast
            have hD3 : (3 : ℝ) * D ≤ N := by exact_mod_cast (show 3 * D ≤ N by omega)
            have hN5 : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ hNr
            have hD1 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
            calc (2 * (N : ℝ) ^ 5 + 1) * D ≤ (3 * (N : ℝ) ^ 5) * D :=
                  mul_le_mul_of_nonneg_right (by linarith) hD1
              _ = (N : ℝ) ^ 5 * (3 * D) := by ring
              _ ≤ (N : ℝ) ^ 5 * N := mul_le_mul_of_nonneg_left hD3 (by positivity)
              _ = (N : ℝ) ^ 6 := by ring
  refine ⟨?_, ?_⟩
  · intro τ' hτ' D' hD'
    have ha : 0 < min τ' (τ / 8) := lt_min hτ' (by positivity)
    obtain ⟨N₀, hN₀⟩ := core (min τ' (τ / 8)) ha (min_le_right _ _) D' hD'
    obtain ⟨N₃, hN₃⟩ := FarStage_ev c (min τ' (τ / 8) / 2) (by positivity)
    refine ⟨max (max N₀ N₃) 1, fun N hN w => ?_⟩
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
    obtain ⟨-, -, hμ⟩ := hN₀ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
      w.val w.property
    refine le_trans (measure_mono ?_) hμ
    intro h hh hgood
    have hb := hβle (min τ' (τ / 8)) τ' (min_le_left _ _) N hNr
      (hN₃ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)) w.val w.property
    exact absurd hh (not_lt.mpr (hgood.2.trans hb))
  · intro τ' hτ' D' hD'
    have ha : 0 < min τ' (τ / 8) := lt_min hτ' (by positivity)
    obtain ⟨N₀, hN₀⟩ := core (min τ' (τ / 8)) ha (min_le_right _ _) (D' + 1) (by linarith)
    obtain ⟨N₁, hN₁⟩ := hIso (min τ' (τ / 8) / 2) (by positivity) (D' + 1) (by linarith)
    obtain ⟨N₃, hN₃⟩ := FarStage_ev c (min τ' (τ / 8) / 2) (by positivity)
    obtain ⟨N₄, hN₄⟩ := FarStage_ev ((3 / 2 : ℝ) ^ Kn) (min τ' (τ / 8) / 2) (by positivity)
    refine ⟨max (max N₀ N₁) (max (max N₃ N₄) 2), fun N hN w => ?_⟩
    have hN0' : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN3' : N₃ ≤ N :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hN
    have hN4' : N₄ ≤ N :=
      le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hN
    have hN2 : (2 : ℝ) ≤ N := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hNr : (1 : ℝ) ≤ N := by linarith
    have hN0 : (0 : ℝ) < N := by linarith
    rcases w with ⟨⟨z, hz⟩, ⟨u, hu⟩, ⟨v, hv⟩⟩
    obtain ⟨hβ1, hΛ1, hμ⟩ := hN₀ N hN0' z hz
    have hμ2 := hN₁ N hN1' (⟨z, hz⟩, ⟨u, hu⟩, ⟨v, hv⟩)
    have h3 := (measure_union_le _ _).trans ((add_le_add hμ hμ2).trans (FarStage_two N hN2 D'))
    refine le_trans (measure_mono ?_) h3
    intro h hh
    by_contra hcon
    simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, not_not, not_lt] at hcon
    obtain ⟨⟨hHerm, hxβ⟩, hiso⟩ := hcon
    have hzim := (FarStage_im hτ hℓ hz).2.2
    have hθ := hseq.theta N
    have hx1 : ‖blockTr D N (res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z)‖ ≤ 1 :=
      by linarith
    obtain ⟨-, hR, -, h4, -⟩ := blockTr_far D N (θ N) hθ.1 hθ.2 (A N) hΛ1 (Matrix.of h) hHerm z
      hzim hz.1 hx1
    have hR1 : opNorm (resX (lam D N (A N)) z (sigTheta D (θ N) *ᵥ
        blockTr D N (res (Matrix.of h + lam D N (A N)) z))) ≤ 1 := hR.trans (by norm_num)
    simp only [hR1, ↓reduceIte] at hiso
    have hform := h4 u v hu hv
    have hb := hβle (min τ' (τ / 8)) τ' (min_le_left _ _) N hNr (hN₃ N hN3') z hz
    have hx0 := norm_nonneg (blockTr D N (res (Matrix.of h + lam D N (A N)) z -
      MExt (lam D N (A N)) z))
    have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, by exact_mod_cast hNr⟩)⟩
    have hmf := MExt_far (lam D N (A N)) (lam_isHermitian D N (A N)) hΛ1 z hzim hz.1
    have hpsi := FarStage_psi_le (lam D N (A N)) N hNr z (φ N z) hzim hmf.2.2
    have hzp := FarStage_zpow hz hzim.le Kn (by linarith)
    have hNa : 0 ≤ (N : ℝ) ^ (min τ' (τ / 8) / 2) := Real.rpow_nonneg hN0.le _
    have hP3 : 0 ≤ (1 + φ N z) ^ 3 := by
      have := hφ0 N z hz
      positivity
    have hpp := FarStage_psiPhi_nonneg (lam D N (A N)) N z (φ N z) hzim
    have hpf := FarStage_psiFar_nonneg N z (φ N z) hzim
    have hk0 : 0 ≤ (1 + ‖z‖) ^ Kn := Real.rpow_nonneg (by positivity) _
    have hiso' : (N : ℝ) ^ (min τ' (τ / 8) / 2) * ((1 + ‖z‖) ^ Kn * (1 + φ N z) ^ 3 *
        psiPhi (lam D N (A N)) N z (φ N z)) ≤
        (N : ℝ) ^ τ' * ((N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 4) * (1 + φ N z) ^ 3 *
          psiFar N z (φ N z)) := by
      have hc4 := hN₄ N hN4'
      have h5 : (N : ℝ) ^ (δ₁ * Kn) ≤ (N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 4) :=
        Real.rpow_le_rpow_of_exponent_le hNr (by nlinarith)
      have h6 : (N : ℝ) ^ (min τ' (τ / 8) / 2) * (N : ℝ) ^ (min τ' (τ / 8) / 2) ≤
          (N : ℝ) ^ τ' := by
        rw [← Real.rpow_add hN0]
        exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith [min_le_left τ' (τ / 8)])
      have h7 : (1 + ‖z‖) ^ Kn ≤ (N : ℝ) ^ (min τ' (τ / 8) / 2) *
          (N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 4) :=
        hzp.trans (mul_le_mul hc4 h5 (Real.rpow_nonneg hN0.le _) hNa)
      calc (N : ℝ) ^ (min τ' (τ / 8) / 2) * ((1 + ‖z‖) ^ Kn * (1 + φ N z) ^ 3 *
            psiPhi (lam D N (A N)) N z (φ N z))
          ≤ (N : ℝ) ^ (min τ' (τ / 8) / 2) * (((N : ℝ) ^ (min τ' (τ / 8) / 2) *
            (N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 4)) * (1 + φ N z) ^ 3 * psiFar N z (φ N z)) := by
            gcongr
        _ = ((N : ℝ) ^ (min τ' (τ / 8) / 2) * (N : ℝ) ^ (min τ' (τ / 8) / 2)) *
            ((N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 4) * (1 + φ N z) ^ 3 * psiFar N z (φ N z)) := by
            ring
        _ ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 4) * (1 + φ N z) ^ 3 *
            psiFar N z (φ N z)) := mul_le_mul_of_nonneg_right h6 (by positivity)
    simp only [Set.mem_ofPred_eq] at hh
    refine absurd hh (not_lt.mpr ?_)
    calc ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ v)‖
        ≤ 100 / 551 * ‖blockTr D N (res (Matrix.of h + lam D N (A N)) z -
            MExt (lam D N (A N)) z)‖ + ‖star u ⬝ᵥ ((resX (lam D N (A N)) z (sigTheta D (θ N) *ᵥ
              blockTr D N (res (Matrix.of h + lam D N (A N)) z)) *
              hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z) *ᵥ v)‖ := hform
      _ ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 2) * (1 + φ N z) ^ 6 *
            psiFar N z (φ N z) ^ 2) +
          (N : ℝ) ^ τ' * ((N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 4) * (1 + φ N z) ^ 3 *
            psiFar N z (φ N z)) := by
          have : 100 / 551 * ‖blockTr D N (res (Matrix.of h + lam D N (A N)) z -
              MExt (lam D N (A N)) z)‖ ≤ ‖blockTr D N (res (Matrix.of h + lam D N (A N)) z -
              MExt (lam D N (A N)) z)‖ := by linarith
          linarith
      _ = (N : ℝ) ^ τ' * ((N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 4) * (1 + φ N z) ^ 3 *
            psiFar N z (φ N z) + (N : ℝ) ^ ((4 * Kn + 56) * δ₁ / 2) * (1 + φ N z) ^ 6 *
            psiFar N z (φ N z) ^ 2) := by ring

end RBMTransitionEdge

end
