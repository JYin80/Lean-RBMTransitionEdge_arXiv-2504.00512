module

public import RBMTransitionEdge.Flow.LargeEtaExp
public import RBMTransitionEdge.Flow.LemFlow2

@[expose] public section

/-!
# Lemmas 3.8–3.10 in the paper's form

(3.27) [flow_1_result_2] and (3.29) [flow_3G_res_2] of Lemmas 3.8 [lem_flow_1] and 3.9
[lem_flow_2] on the grid, and (3.30) [flow_1G_res], (3.31) [flow_1G_res_2] of Lemma 3.10
[lem_flow_1.5] at one time.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Operator-norm and trace tools -/

section LFE_Op

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `opNorm` is the `L²` operator norm. -/
private lemma LFE_op_eq (A : Matrix ι ι ℂ) : opNorm A = ‖A‖ := rfl

/-- `‖AB‖ ≤ ‖A‖ ‖B‖`. -/
private lemma LFE_op_mul (A B : Matrix ι ι ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  simpa only [LFE_op_eq] using norm_mul_le A B

/-- `‖A‖ ≥ 0`. -/
private lemma LFE_op_nonneg (A : Matrix ι ι ℂ) : 0 ≤ opNorm A := norm_nonneg _

/-- `‖1‖ ≤ 1`. -/
private lemma LFE_op_one : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

/-- `|⟨A⟩| ≤ ‖A‖`. -/
private lemma LFE_ntr_le [Nonempty ι] (A : Matrix ι ι ℂ) : ‖ntr A‖ ≤ opNorm A := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, opNorm A := Finset.sum_le_sum fun i _ => norm_apply_le_opNorm A i i
    _ = _ := by simp

end LFE_Op

/-- `⟨AB⟩ = ⟨BA⟩`. -/
private lemma LFE_ntr_comm {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    ntr (A * B) = ntr (B * A) := by
  simp only [ntr, Matrix.trace_mul_comm A B]

/-- `‖E_a‖ ≤ 1` for the block projection. -/
private lemma LFE_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

section LFE_P

open scoped Matrix.Norms.L2Operator

/-- `‖P_θ‖ ≤ 1` for `θ ∈ [0, 1]`: `P_θ = θ I + (1 - θ) J/D` with `J/D` an orthogonal projection. -/
private lemma LFE_P_norm (D : ℕ) [NeZero D] (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    opNorm (PTheta D θ) ≤ 1 := by
  have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne D)
  set Q : Matrix (Fin D) (Fin D) ℂ := Matrix.of fun _ _ => ((1 / D : ℝ) : ℂ) with hQ
  have hQQ : Qᴴ * Q = Q := by
    ext i j
    simp only [hQ, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    field_simp
  have hQ1 : opNorm Q ≤ 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self Q
    rw [hQQ] at h
    have h0 : 0 ≤ ‖Q‖ := norm_nonneg _
    rw [LFE_op_eq]
    nlinarith
  have hP : PTheta D θ = (θ : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) + ((1 - θ : ℝ) : ℂ) • Q := by
    ext i j
    simp only [PTheta, hQ, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    push_cast
    ring
  rw [hP]
  refine (opNorm_add_le _ _).trans ?_
  rw [opNorm_smul, opNorm_smul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h0,
    Real.norm_of_nonneg (by linarith)]
  have := LFE_op_one (ι := Fin D)
  nlinarith

end LFE_P

/-- The Hermitian part of a Hermitian array is the array. -/
private lemma LFE_hermPart_eq {ι : Type*} (H : ι → ι → ℂ) (hH : (Matrix.of H).IsHermitian) :
    hermPart H = H := by
  funext i j
  have h1 : star (H j i) = H i j := by
    have := congrFun (congrFun hH i) j
    simpa [Matrix.conjTranspose_apply] using this
  simp only [hermPart, h1]
  ring

/-- The Hermitian part of an array is Hermitian. -/
private lemma LFE_hermPart_herm {ι : Type*} (H : ι → ι → ℂ) :
    (Matrix.of (hermPart H)).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, hermPart, star_div₀, star_add,
    star_star]
  simp [add_comm]

/-- `t Λ(A) = Λ(t A)` for real `t`. -/
private lemma LFE_lam_smul (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    (t : ℂ) • lam D N A = lam D N ((t : ℂ) • A) := by
  ext p q
  simp only [lam, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [mul_add, Complex.conj_ofReal]

/-- A real multiple of a Hermitian matrix is Hermitian. -/
private lemma LFE_herm_smul {ι : Type*} (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (c : ℝ) :
    (((c : ℝ) : ℂ) • Λ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hΛ.eq]
  simp

/-- `C N^α ≤ N^β` for all large `N` when `α < β`. -/
private lemma LFE_ev_pow (C α β : ℝ) (hαβ : α < β) :
    ∀ᶠ N : ℕ in Filter.atTop, C * (N : ℝ) ^ α ≤ (N : ℝ) ^ β := by
  have t : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (β - α)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [t.eventually_ge_atTop C, Filter.eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have e : (N : ℝ) ^ β = (N : ℝ) ^ (β - α) * (N : ℝ) ^ α := by
    rw [← Real.rpow_add hNpos]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hNpos.le _)

/-! ### The closed-form flow on `[0, S]` -/

/-- Along the closed-form flow (3.10) [eq:deterflow] on `[0, S]`, `S < t_c - t₀`, `‖Λ‖ ≤ 1/10`:
`η_s > 0`, `Im m_s = e^{s/2} Im m ∈ (0, 1)`, `η_s Im m_s` is at least its value at `S`,
`t_c - t_s = (t_c - t₀) - s` and `η_s ≥ (t_c - t_s) Im m_s`. -/
private lemma LFE_flow (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (s : ℝ) (hs0 : 0 ≤ s) (hsS : s ≤ S) :
    0 < (charFlowZ (lam D N A) z s).im ∧
      flowIm (lam D N A) z s = Real.exp (s / 2) * (mExt (lam D N A) z).im ∧
      0 < (mExt (lam D N A) z).im ∧
      flowIm (lam D N A) z s < 1 ∧
      (charFlowZ (lam D N A) z S).im * flowIm (lam D N A) z S ≤
        (charFlowZ (lam D N A) z s).im * flowIm (lam D N A) z s ∧
      flowTc (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z s) =
        flowTc (lam D N A) z - s ∧
      (flowTc (lam D N A) z - s) * flowIm (lam D N A) z s ≤ (charFlowZ (lam D N A) z s).im := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  set Λ := lam D N A with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N A
  have hι : 0 < (mExt Λ z).im := by
    have : mExt Λ z = mSol Λ z := by simp [mExt, hz]
    rw [this]
    exact (mSol_spec Λ hΛ z hz).1
  set m := mExt Λ z with hmdef
  have hs : s < flowTc Λ z := lt_of_le_of_lt hsS hS
  have hflow : ∀ r, r ≤ S → 0 < (charFlowZ Λ z r).im ∧
      mExt (((Real.exp (-r / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z r) =
        ((Real.exp (r / 2) : ℝ) : ℂ) * m := fun r hr =>
    ⟨(charFlow_M Λ hΛ z hz r (lt_of_le_of_lt hr hS)).1,
      (charFlow_M Λ hΛ z hz r (lt_of_le_of_lt hr hS)).2.2⟩
  have hIm : ∀ r, (charFlowZ Λ z r).im =
      Real.exp (-r / 2) * (z.im + m.im) - Real.exp (r / 2) * m.im := by
    intro r
    simp only [charFlowZ, Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rfl
  have hflowIm : ∀ r, r ≤ S → flowIm Λ z r = Real.exp (r / 2) * m.im := by
    intro r hr
    unfold flowIm
    rw [(hflow r hr).2]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hee : ∀ r : ℝ, Real.exp (-r / 2) * Real.exp (r / 2) = 1 := fun r => by
    rw [← Real.exp_add, show -r / 2 + r / 2 = 0 by ring, Real.exp_zero]
  have hprod : ∀ r, r ≤ S → (charFlowZ Λ z r).im * flowIm Λ z r =
      m.im * (z.im + m.im) - m.im ^ 2 * Real.exp (r / 2) ^ 2 := by
    intro r hr
    rw [hIm, hflowIm r hr]
    linear_combination (m.im * (z.im + m.im)) * hee r
  have hnorm : opNorm (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) ≤ 1 / 10 := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-s / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h0 : 0 ≤ opNorm Λ := norm_nonneg _
    nlinarith
  have hpos := (hflow s hsS).1
  have hapr := mSol_apriori _ (LFE_herm_smul Λ hΛ (Real.exp (-s / 2))) hnorm _ hpos
  have hms : ‖((Real.exp (s / 2) : ℝ) : ℂ) * m‖ < 1 := by
    have h1 : mExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s) =
        mSol (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s) := by simp [mExt, hpos]
    rw [← (hflow s hsS).2, h1]
    exact hapr.2.1
  have htc := flowTc_flow Λ hΛ z hz s hs
  refine ⟨hpos, hflowIm s hsS, hι, ?_, ?_, htc, ?_⟩
  · rw [hflowIm s hsS]
    have hms' : Real.exp (s / 2) * ‖m‖ < 1 := by
      rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hms
    have : m.im ≤ ‖m‖ := (Complex.im_le_norm m)
    nlinarith [Real.exp_pos (s / 2), norm_nonneg m]
  · rw [hprod S le_rfl, hprod s hsS]
    have : Real.exp (s / 2) ^ 2 ≤ Real.exp (S / 2) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.2 (by linarith)) 2
    nlinarith [sq_nonneg m.im]
  · have hteta := charFlow_teta Λ hΛ z hz s hs
    have hιs : 0 < flowIm Λ z s := by rw [hflowIm s hsS]; exact mul_pos (Real.exp_pos _) hι
    have e1 : (charFlowZ Λ z s).im / flowIm Λ z s =
        Real.exp (flowTc Λ z - s) - 1 := hteta
    have h2 : flowTc Λ z - s ≤ Real.exp (flowTc Λ z - s) - 1 := by
      linarith [Real.add_one_le_exp (flowTc Λ z - s)]
    rw [← e1, le_div_iff₀ hιs] at h2
    exact h2

/-- The admissible start of `flowAdm` for large `N`: `‖Λ‖ ≤ 1/10`, `|z| ≤ τ⁻¹`, `|m| < 1`,
`0 < t_c - t₀ ≤ 1`, and `η_s > N⁻¹`, `N η_s Im m_s ≥ N^{C₀ ε_g}` on `[0, S]`. -/
private lemma LFE_adm (D N : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ N) (δA τ τe εg c C₀ : ℝ) (hεg : 0 < εg)
    (hC₀ : 0 < C₀) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ)
    (hadm : flowAdm D N δA τ τe εg c C₀ A z S)
    (hAN : 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10) (hcN : c * (N : ℝ) ^ (-εg) ≤ 1) :
    opNorm (lam D N A) ≤ 1 / 10 ∧ ‖z‖ ≤ τ⁻¹ ∧ 0 < z.im ∧ ‖mExt (lam D N A) z‖ < 1 ∧
      0 < flowTc (lam D N A) z ∧ flowTc (lam D N A) z ≤ 1 ∧ 0 ≤ S ∧
      S < flowTc (lam D N A) z ∧
      ∀ s, 0 ≤ s → s ≤ S → (N : ℝ)⁻¹ < (charFlowZ (lam D N A) z s).im ∧
        (N : ℝ) ^ (C₀ * εg) ≤ N * (charFlowZ (lam D N A) z s).im * flowIm (lam D N A) z s := by
  obtain ⟨hA, hzD, hz, -, hlo, hhi, hS0, hSt, hNS⟩ := hadm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hΛ : opNorm (lam D N A) ≤ 1 / 10 := by
    have := opNorm_lam_le D N A
    linarith
  have hNe : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, by omega⟩)⟩
  have hι : 0 < (mExt (lam D N A) z).im := by
    have : mExt (lam D N A) z = mSol (lam D N A) z := by simp [mExt, hz]
    rw [this]
    exact (mSol_spec _ (lam_isHermitian D N A) z hz).1
  have hm : ‖mExt (lam D N A) z‖ < 1 := by
    have : mExt (lam D N A) z = mSol (lam D N A) z := by simp [mExt, hz]
    rw [this]
    exact (mSol_apriori _ (lam_isHermitian D N A) hΛ z hz).2.1
  have hq0 : 0 < flowTc (lam D N A) z := by
    unfold flowTc
    exact Real.log_pos (by have := div_pos hz hι; linarith)
  have hq1 : flowTc (lam D N A) z ≤ 1 := by
    unfold flowTc
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + z.im / (mExt (lam D N A) z).im by
      have := div_pos hz hι; linarith)
    linarith
  refine ⟨hΛ, hzD.1, hz, hm, hq0, hq1, hS0, hSt, fun s hs0 hsS => ?_⟩
  obtain ⟨hηs, hιeq, hι0, hιs1, hmono, -, -⟩ :=
    LFE_flow D N hD (by omega) A hΛ z hz S hSt s hs0 hsS
  have hbig : (N : ℝ) ^ (C₀ * εg) ≤
      N * (charFlowZ (lam D N A) z s).im * flowIm (lam D N A) z s := by
    have := mul_le_mul_of_nonneg_left hmono hNpos.le
    calc (N : ℝ) ^ (C₀ * εg) ≤ N * (charFlowZ (lam D N A) z S).im * flowIm (lam D N A) z S :=
          hNS
      _ ≤ _ := by nlinarith
  have hιspos : 0 < flowIm (lam D N A) z s := by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
  have hNe1 : (1 : ℝ) ≤ (N : ℝ) ^ (C₀ * εg) := Real.one_le_rpow hN1 (by positivity)
  refine ⟨?_, hbig⟩
  rw [inv_lt_iff_one_lt_mul₀ hNpos]
  have : (N : ℝ) * (charFlowZ (lam D N A) z s).im * flowIm (lam D N A) z s <
      N * (charFlowZ (lam D N A) z s).im := by
    have h1 : 0 < (N : ℝ) * (charFlowZ (lam D N A) z s).im := mul_pos hNpos hηs
    nlinarith
  linarith

/-- `flowAdm` passes from the horizon `S` to every horizon `r ∈ [0, S]`: `N η_r Im m_r` is at least
its value at `S`. -/
private lemma LFE_adm_mono (D N : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ N) (δA τ τe εg c C₀ : ℝ)
    (hεg : 0 < εg) (hC₀ : 0 < C₀) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ)
    (hadm : flowAdm D N δA τ τe εg c C₀ A z S)
    (hAN : 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10) (hcN : c * (N : ℝ) ^ (-εg) ≤ 1) (r : ℝ) (hr0 : 0 ≤ r)
    (hrS : r ≤ S) : flowAdm D N δA τ τe εg c C₀ A z r := by
  obtain ⟨-, -, -, -, -, -, -, hSt, hη⟩ :=
    LFE_adm D N hD hN δA τ τe εg c C₀ hεg hC₀ A z S hadm hAN hcN
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -, -⟩ := hadm
  exact ⟨h1, h2, h3, h4, h5, h6, hr0, lt_of_le_of_lt hrS hSt, (hη r hr0 hrS).2⟩

/-- At time `0` the flowed objects are the objects at the start. -/
private lemma LFE_zero {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z z₁ z₂ z₃ : ℂ)
    (H : Idx D N → Idx D N → ℂ) :
    flowLmat Λ z₁ z₂ 0 H = Lmat Λ H z₁ z₂ ∧ flowKmat Λ θ z₁ z₂ 0 = KTheta Λ θ z₁ z₂ ∧
      flowLten3 Λ z₁ z₂ z₃ 0 H = Lten3 Λ H z₁ z₂ z₃ ∧
      flowKten3 Λ θ z₁ z₂ z₃ 0 = KTheta3 Λ θ z₁ z₂ z₃ ∧
      flowIm Λ z 0 = (mExt Λ z).im ∧ charFlowZ Λ z 0 = z := by
  have hz : ∀ w : ℂ, charFlowZ Λ w 0 = w := fun w => by simp [charFlowZ]
  have he : ((Real.exp (-0 / 2) : ℝ) : ℂ) • Λ = Λ := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, hz z⟩
  · simp only [flowLmat, hz, he]
  · simp only [flowKmat, hz, he]
    congr 1
    simp
  · simp only [flowLten3, hz, he]
  · simp only [flowKten3, hz, he]
    congr 1
    simp
  · simp only [flowIm, hz, he]

/-! ### The start of the flow: the window of `flowAdm` and the factor `(1 - M̂ P_θ)⁻¹` -/

/-- From the window `η / Im m ∈ [c⁻¹ N^{-ε_g}, c N^{-ε_g}]` with `c N^{-ε_g} ≤ 1`:
`q₀ = log(1 + η/Im m)` satisfies `q₀ ≠ 0`, `q₀ ≤ c N^{-ε_g}` and `q₀⁻¹ ≤ 2 c N^{ε_g}`. -/
private lemma LFE_q0 (N : ℕ) (hN : 1 ≤ N) (εg c x : ℝ) (hc : 1 ≤ c)
    (hlo : c⁻¹ * (N : ℝ) ^ (-εg) ≤ x) (hhi : x ≤ c * (N : ℝ) ^ (-εg))
    (hcN : c * (N : ℝ) ^ (-εg) ≤ 1) :
    Real.log (1 + x) ≠ 0 ∧ Real.log (1 + x) ≤ c * (N : ℝ) ^ (-εg) ∧
      (Real.log (1 + x))⁻¹ ≤ 2 * c * (N : ℝ) ^ εg := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcpos : 0 < c := by linarith
  have hx0 : 0 < x := by
    have := inv_pos.2 hcpos
    have := Real.rpow_pos_of_pos hNpos (-εg)
    have : 0 < c⁻¹ * (N : ℝ) ^ (-εg) := by positivity
    linarith
  refine ⟨(Real.log_pos (by linarith)).ne', ?_, ?_⟩
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)
    linarith
  · have hx1 : x ≤ 1 := hhi.trans hcN
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x by linarith)
    have h2 : x / 2 ≤ Real.log (1 + x) := by
      refine le_trans ?_ h1
      rw [show 1 - (1 + x)⁻¹ = x / (1 + x) by field_simp; ring]
      exact div_le_div_of_nonneg_left hx0.le (by positivity) (by linarith)
    have hNεpos : 0 < (N : ℝ) ^ εg := Real.rpow_pos_of_pos hNpos _
    have h3 : c⁻¹ * (N : ℝ) ^ (-εg) / 2 ≤ Real.log (1 + x) := le_trans (by linarith) h2
    have hpos : 0 < c⁻¹ * (N : ℝ) ^ (-εg) / 2 := by
      have := inv_pos.2 hcpos; have := Real.rpow_pos_of_pos hNpos (-εg); positivity
    calc (Real.log (1 + x))⁻¹ ≤ (c⁻¹ * (N : ℝ) ^ (-εg) / 2)⁻¹ := inv_anti₀ hpos h3
      _ = 2 * c * (N : ℝ) ^ εg := by
          rw [Real.rpow_neg hNpos.le]
          have := hcpos.ne'; have := hNεpos.ne'
          field_simp

/-- At the start `1 - M̂ P_θ` is invertible and `‖(1 - M̂ P_θ)⁻¹‖ ≤ 1 + q₀⁻¹`, from
`‖q₀ K_θ‖ ≤ 1` (`tOp_norm_le`) and `‖P_θ‖ ≤ 1`, since `(1 - M̂ P_θ)⁻¹ = 1 + K_θ P_θ`. -/
private lemma LFE_U_le (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (w₁ w₂ : ℂ)
    (h₁ : w₁ = z ∨ w₁ = star z) (h₂ : w₂ = z ∨ w₂ = star z) (hq : 0 < flowTc (lam D N A) z) :
    (1 - Mhat (lam D N A) w₁ w₂ * PTheta D θ).det ≠ 0 ∧
      opNorm (1 - Mhat (lam D N A) w₁ w₂ * PTheta D θ)⁻¹ ≤ 1 + (flowTc (lam D N A) z)⁻¹ := by
  obtain ⟨hdet, hop, -⟩ := tOp_norm_le D N A z hz θ hθ₀ hθ₁ w₁ w₂ h₁ h₂
  set q := flowTc (lam D N A) z with hqd
  set X := Mhat (lam D N A) w₁ w₂ with hX
  set P := PTheta D θ with hP
  have hK : opNorm (KTheta (lam D N A) θ w₁ w₂) ≤ q⁻¹ := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] at hop
    calc opNorm (KTheta (lam D N A) θ w₁ w₂) =
        q⁻¹ * (q * opNorm (KTheta (lam D N A) θ w₁ w₂)) := by field_simp
      _ ≤ q⁻¹ * 1 := mul_le_mul_of_nonneg_left hop (inv_nonneg.2 hq.le)
      _ = _ := mul_one _
  refine ⟨hdet, ?_⟩
  have hUnit : IsUnit (1 - X * P).det := isUnit_iff_ne_zero.2 hdet
  have hUe : (1 - X * P)⁻¹ = 1 + KTheta (lam D N A) θ w₁ w₂ * P := by
    simp only [KTheta, ← hX, ← hP]
    have h1 : (1 - X * P)⁻¹ * (1 - X * P) = 1 := Matrix.nonsing_inv_mul _ hUnit
    rw [Matrix.mul_assoc]
    calc (1 - X * P)⁻¹ = (1 - X * P)⁻¹ * (1 - X * P) + (1 - X * P)⁻¹ * (X * P) := by
          rw [← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]
      _ = 1 + (1 - X * P)⁻¹ * (X * P) := by rw [h1]
  rw [hUe]
  have hPn := LFE_P_norm D θ hθ₀ hθ₁
  refine (opNorm_add_le _ _).trans ?_
  have h2 := LFE_op_mul (KTheta (lam D N A) θ w₁ w₂) P
  have h3 := LFE_op_nonneg (KTheta (lam D N A) θ w₁ w₂)
  have h4 := LFE_op_one (ι := Fin D)
  have h5 : opNorm (KTheta (lam D N A) θ w₁ w₂) * opNorm P ≤ q⁻¹ :=
    (mul_le_mul_of_nonneg_left hPn h3).trans (by rw [mul_one]; exact hK)
  linarith

/-- The start bound of `lemma_G_large_two` in the scale of the flow: if
`‖L₀ - K_θ‖₂ ≤ N^{τ₂} N⁻¹ η⁻² ‖(1 - M̂ P_θ)⁻¹‖`, then `q₀² ‖L₀ - K_θ‖₂ ≤ 4 c N^{τ₂} N^{ε_g} /
(N (Im m)²)`, using `q₀ Im m ≤ η` and `q₀⁻¹ ≤ 2 c N^{ε_g}`. -/
private lemma LFE_start2 (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (w₁ w₂ : ℂ)
    (h₁ : w₁ = z ∨ w₁ = star z) (h₂ : w₂ = z ∨ w₂ = star z) (c εg τ₂ X : ℝ)
    (hq : 0 < flowTc (lam D N A) z) (hq1 : flowTc (lam D N A) z ≤ 1)
    (hι : 0 < (mExt (lam D N A) z).im)
    (hqι : flowTc (lam D N A) z * (mExt (lam D N A) z).im ≤ z.im)
    (hqinv : (flowTc (lam D N A) z)⁻¹ ≤ 2 * c * (N : ℝ) ^ εg)
    (hle : X ≤ (N : ℝ) ^ τ₂ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
      opNorm (1 - Mhat (lam D N A) w₁ w₂ * PTheta D θ)⁻¹)) :
    flowTc (lam D N A) z ^ 2 * X ≤
      4 * c * (N : ℝ) ^ τ₂ * (N : ℝ) ^ εg / (N * (mExt (lam D N A) z).im ^ 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set q₀ := flowTc (lam D N A) z with hq₀
  set ι₀ := (mExt (lam D N A) z).im with hι₀
  have hU := (LFE_U_le D N A z hz θ hθ₀ hθ₁ w₁ w₂ h₁ h₂ hq).2
  have hq0inv1 : 1 ≤ q₀⁻¹ := (one_le_inv₀ hq).2 hq1
  have hNt : 0 < (N : ℝ) ^ τ₂ := Real.rpow_pos_of_pos hNpos _
  calc q₀ ^ 2 * X
      ≤ q₀ ^ 2 * ((N : ℝ) ^ τ₂ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
        opNorm (1 - Mhat (lam D N A) w₁ w₂ * PTheta D θ)⁻¹)) :=
        mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    _ ≤ q₀ ^ 2 * ((N : ℝ) ^ τ₂ * ((N : ℝ)⁻¹ * ((q₀ * ι₀) ^ 2)⁻¹ * (1 + q₀⁻¹))) := by
        have hR0 := LFE_op_nonneg (1 - Mhat (lam D N A) w₁ w₂ * PTheta D θ)⁻¹
        have hinv : (z.im ^ 2)⁻¹ ≤ ((q₀ * ι₀) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hqι 2)
        gcongr
    _ = (N : ℝ) ^ τ₂ * (1 + q₀⁻¹) / (N * ι₀ ^ 2) := by
        field_simp
    _ ≤ (N : ℝ) ^ τ₂ * (2 * (2 * c * (N : ℝ) ^ εg)) / (N * ι₀ ^ 2) := by
        gcongr
        linarith
    _ = 4 * c * (N : ℝ) ^ τ₂ * (N : ℝ) ^ εg / (N * ι₀ ^ 2) := by ring

/-- The preimage of a set of starting arrays has `gridLawA` measure at most its `μ₀` measure. -/
private lemma LFE_fst_le (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] (B : Set (Idx D N → Idx D N → ℂ)) :
    gridLawA D N K μ₀ {ω | ω.1 ∈ B} ≤ μ₀ B := by
  have h := Measure.le_map_apply (μ := gridLawA D N K μ₀) measurable_fst.aemeasurable B
  have e : (gridLawA D N K μ₀).map Prod.fst = μ₀ := by
    unfold gridLawA
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [e] at h
  exact h

/-- `n` events of probability at most `N^{-D'-1}` have total probability at most `N^{-D'}`,
for `n ≤ N`. -/
private lemma LFE_budget (N : ℕ) (hN : 1 ≤ N) (n : ℕ) (hn : n ≤ N) (D' : ℝ) :
    (n : ℝ) * (N : ℝ) ^ (-(D' + 1)) ≤ (N : ℝ) ^ (-D') := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (N : ℝ) ^ (-(D' + 1)) = (N : ℝ) ^ (-D') / N := by
    rw [show -(D' + 1) = -D' - 1 by ring, Real.rpow_sub_one hNpos.ne']
  rw [e, mul_div_assoc', div_le_iff₀ hNpos]
  have := Real.rpow_nonneg hNpos.le (-D')
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  nlinarith

/-- The final inequality for the paper form (3.27) [flow_1_result_2]: from the start bound
`q₀² X₀ ≤ 4 c N^{τ₂} N^{ε_g} / (N ι₀²)` and `ι_k = E ι₀`, `1 ≤ E ≤ e^{1/2}`, the bound of the
conditional form is at most `N^{τ'} N^{ε_g} / (N q_k² ι_k²)`. -/
private lemma LFE_ar2 (N q₀ qk ι₀ E X₀ a b d c t : ℝ) (hN : 0 < N) (hqk : 0 < qk)
    (hι₀ : 0 < ι₀) (hE1 : 1 ≤ E) (hE : E ≤ Real.exp (1 / 2)) (ha : 0 ≤ a) (hb : 1 ≤ b)
    (hd : 1 ≤ d) (hc : 0 ≤ c)
    (hX : q₀ ^ 2 * X₀ ≤ 4 * c * b * d / (N * ι₀ ^ 2))
    (hfin : (4 * c * Real.exp (1 / 2) ^ 2 + 1) * (a * b) ≤ t) :
    a * ((q₀ / qk) ^ 2 * X₀ + 1 / (N * qk ^ 2 * (E * ι₀) ^ 2)) ≤
      t * (d / (N * qk ^ 2 * (E * ι₀) ^ 2)) := by
  set P := N * qk ^ 2 * (E * ι₀) ^ 2 with hP
  have hPpos : 0 < P := by positivity
  have hE2 : E ^ 2 ≤ Real.exp (1 / 2) ^ 2 := pow_le_pow_left₀ (by linarith) hE 2
  have h1 : (q₀ / qk) ^ 2 * X₀ ≤ 4 * c * Real.exp (1 / 2) ^ 2 * b * d / P := by
    rw [div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hPpos]
    have h2 := mul_le_mul_of_nonneg_right hX hPpos.le
    have e1 : 4 * c * b * d / (N * ι₀ ^ 2) * P = 4 * c * b * d * E ^ 2 * qk ^ 2 := by
      rw [hP]; field_simp
    rw [e1] at h2
    have h3 : 4 * c * b * d * E ^ 2 * qk ^ 2 ≤ 4 * c * Real.exp (1 / 2) ^ 2 * b * d * qk ^ 2 := by
      have : 0 ≤ 4 * c * b * d * qk ^ 2 := by positivity
      nlinarith
    nlinarith
  have h4 : 1 / P ≤ b * d / P := div_le_div_of_nonneg_right (by nlinarith) hPpos.le
  have h5 : a * ((q₀ / qk) ^ 2 * X₀ + 1 / P) ≤
      (4 * c * Real.exp (1 / 2) ^ 2 + 1) * (a * b) * (d / P) := by
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h4) ha
    have e2 : a * (4 * c * Real.exp (1 / 2) ^ 2 * b * d / P + b * d / P) =
        (4 * c * Real.exp (1 / 2) ^ 2 + 1) * (a * b) * (d / P) := by ring
    linarith
  exact h5.trans (mul_le_mul_of_nonneg_right hfin (by positivity))

/-- The final inequality for the paper form (3.29) [flow_3G_res_2]: from the start bound
`T₀ ≤ N^{τ₂} N⁻¹ η⁻³ N^{ε_g}`, `q₀ ι₀ ≤ η` and `ι_k = E ι₀`, `1 ≤ E ≤ e^{1/2}`, the bound of the
conditional form is at most `N^{τ'} N^{ε_g} / (N q_k³ ι_k³)`. -/
private lemma LFE_ar3 (N q₀ qk ι₀ η E T₀ a b d t : ℝ) (hN : 0 < N) (hq₀ : 0 < q₀) (hqk : 0 < qk)
    (hι₀ : 0 < ι₀) (hqι : q₀ * ι₀ ≤ η) (hE1 : 1 ≤ E) (hE : E ≤ Real.exp (1 / 2)) (ha : 0 ≤ a)
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : T₀ ≤ b * (N⁻¹ * (η ^ 3)⁻¹ * d))
    (hfin : (Real.exp (1 / 2) ^ 3 + 1) * (a * b) ≤ t) :
    a * ((q₀ / qk) ^ 3 * T₀ + d / (N * qk ^ 3 * (E * ι₀) ^ 3)) ≤
      t * (d / (N * qk ^ 3 * (E * ι₀) ^ 3)) := by
  set P := N * qk ^ 3 * (E * ι₀) ^ 3 with hP
  have hPpos : 0 < P := by positivity
  have hη : 0 < η := lt_of_lt_of_le (mul_pos hq₀ hι₀) hqι
  have hE3 : E ^ 3 ≤ Real.exp (1 / 2) ^ 3 := pow_le_pow_left₀ (by linarith) hE 3
  have hη3 : (q₀ * ι₀) ^ 3 ≤ η ^ 3 := pow_le_pow_left₀ (by positivity) hqι 3
  have h1 : (q₀ / qk) ^ 3 * T₀ ≤ Real.exp (1 / 2) ^ 3 * b * d / P := by
    have hT0 : (q₀ / qk) ^ 3 * T₀ ≤ (q₀ / qk) ^ 3 * (b * (N⁻¹ * (η ^ 3)⁻¹ * d)) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    have e1 : (q₀ / qk) ^ 3 * (b * (N⁻¹ * (η ^ 3)⁻¹ * d)) =
        b * d * E ^ 3 * (q₀ * ι₀) ^ 3 / (η ^ 3 * P) := by
      rw [hP]; field_simp
    have h2 : b * d * E ^ 3 * (q₀ * ι₀) ^ 3 / (η ^ 3 * P) ≤ b * d * E ^ 3 * η ^ 3 / (η ^ 3 * P) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hη3 (by positivity)) (by positivity)
    have e2 : b * d * E ^ 3 * η ^ 3 / (η ^ 3 * P) = E ^ 3 * b * d / P := by
      field_simp
    have h3 : E ^ 3 * b * d / P ≤ Real.exp (1 / 2) ^ 3 * b * d / P :=
      div_le_div_of_nonneg_right (by
        have : 0 ≤ b * d := by positivity
        nlinarith) hPpos.le
    linarith
  have h4 : d / P ≤ b * d / P := div_le_div_of_nonneg_right (by nlinarith) hPpos.le
  have h5 : a * ((q₀ / qk) ^ 3 * T₀ + d / P) ≤
      (Real.exp (1 / 2) ^ 3 + 1) * (a * b) * (d / P) := by
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h4) ha
    have e2 : a * (Real.exp (1 / 2) ^ 3 * b * d / P + b * d / P) =
        (Real.exp (1 / 2) ^ 3 + 1) * (a * b) * (d / P) := by ring
    linarith
  exact h5.trans (mul_le_mul_of_nonneg_right hfin (by positivity))

set_option maxHeartbeats 1000000 in
/-- Lemma 3.8 [lem_flow_1], (3.27) [flow_1_result_2], on the grid: on the grid of `flowL2_grid`,
`‖L_k - K_k‖₂ ≤ N^{τ'} N^{ε_g} / (N q_k² (Im m_k)²)` at all grid times `u_k ≤ S`, outside
probability `N^{-D'}`. -/
theorem flowL2_grid_paper (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∀ Cg : ℝ, 32 + D' ≤ Cg → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ K : ℕ, (N : ℝ) ^ Cg ≤ K → (K : ℝ) ≤ (N : ℝ) ^ (Cg + 1) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        gridLawA D N K μ₀ {ω | ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ' * ((N : ℝ) ^ εg /
              (N * (flowTc (lam D N A) z - k * (S / K)) ^ 2 *
                flowIm (lam D N A) z (k * (S / K)) ^ 2)) <
            hsNorm (flowLmat (lam D N A) z₁ z₂ (k * (S / K)) (gridStateA D N K (S / K) ω k) -
              flowKmat (lam D N A) θ z₁ z₂ (k * (S / K)))} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD' Cg hCg
  set τ₁ := τ' / 3 with hτ₁
  set τ₂ := min τ' εg / 3 with hτ₂
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₂0 : 0 < τ₂ := by have := lt_min hτ' hεg; positivity
  have hτ₂a : τ₂ ≤ τ' / 3 := by have := min_le_left τ' εg; linarith
  have hτ₂b : τ₂ < εg := by have := min_le_right τ' εg; linarith
  obtain ⟨Nl, hNl⟩ := flowL2_grid D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    τ₁ hτ₁0 (D' + 1) (by linarith) Cg (by linarith)
  obtain ⟨Ns, hNs⟩ := lemma_G_large_two D hD δA τ εg c hδA hτ hεg hεg₂ hc C τ₂ hτ₂0 (D' + 1)
    (by linarith)
  have hev : ∀ᶠ N : ℕ in Filter.atTop, Nl ≤ N ∧ Ns ≤ N ∧ 2 ≤ N ∧
      2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧ c * (N : ℝ) ^ (-εg) ≤ 1 ∧
      4 * c * (N : ℝ) ^ τ₂ ≤ (N : ℝ) ^ εg ∧
      (4 * c * Real.exp (1 / 2) ^ 2 + 1) * (N : ℝ) ^ (τ₁ + τ₂) ≤ (N : ℝ) ^ τ' := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    refine (Filter.eventually_ge_atTop Nl).and ((Filter.eventually_ge_atTop Ns).and
      ((Filter.eventually_ge_atTop 2).and
      (((t1.const_mul 2).eventually (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and
      (((t2.const_mul c).eventually (Iic_mem_nhds (by simp : c * 0 < 1))).and
      ((LFE_ev_pow _ _ _ hτ₂b).and (LFE_ev_pow _ _ _ (by linarith)))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ₀ hμ₀ A z S hadm K hK1 hK2 z₁ z₂ h₁ h₂ => ?_⟩
  obtain ⟨hNl', hNs', hN2, hAN, hcN, hY, hfin⟩ := hN₀ N hN
  have := hμ₀.prob
  have : NeZero D := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hΛ10, -, hz, -, hq0, hq1, hS0, hSt, -⟩ :=
    LFE_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  set q₀ := flowTc (lam D N A) z with hq₀
  set ι₀ := (mExt (lam D N A) z).im with hι₀
  obtain ⟨-, hιeq0, hι0, -, -, -, hqι0⟩ := LFE_flow D N hD1 hN1 A hΛ10 z hz S hSt 0 le_rfl hS0
  obtain ⟨-, -, -, -, -, hcz⟩ := LFE_zero (lam D N A) θ z z z z (fun _ _ => 0)
  rw [hcz, hιeq0, sub_zero, zero_div, Real.exp_zero, one_mul] at hqι0
  have hq0inv : q₀⁻¹ ≤ 2 * c * (N : ℝ) ^ εg :=
    (LFE_q0 N hN1 εg c _ hc hadm.2.2.2.2.1 hadm.2.2.2.2.2.1 hcN).2.2
  have hlow : c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im := by
    refine le_trans ?_ hadm.2.2.2.1
    have hcpos : 0 < c⁻¹ := inv_pos.2 (by linarith)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hNr (by linarith)) hcpos.le
  -- the start event
  set Bs := {H : Idx D N → Idx D N → ℂ | (N : ℝ) ^ τ₂ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
      opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) <
    hsNorm (Lmat (lam D N A) H z₁ z₂ - KTheta (lam D N A) θ z₁ z₂)} with hBs
  have hBsμ : μ₀ Bs ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) :=
    (hNs N hNs' θ hθ0 hθ1 μ₀ hμ₀ A hadm.1 z hadm.2.1 hz hlow hadm.2.2.2.2.1
      hadm.2.2.2.2.2.1 z₁ z₂ h₁ h₂).2
  have hAg := hNl N hNl' θ hθ0 hθ1 μ₀ hμ₀ A z S hadm K hK1 hK2 z₁ z₂ h₁ h₂
  have hK1' : 1 ≤ K := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ Cg := Real.one_le_rpow hNr (by linarith)
    exact_mod_cast this.trans hK1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1'
  have hNb : 1 ≤ (N : ℝ) ^ τ₂ := Real.one_le_rpow hNr hτ₂0.le
  have hNd : 1 ≤ (N : ℝ) ^ εg := Real.one_le_rpow hNr hεg.le
  have hNab : (N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₂ = (N : ℝ) ^ (τ₁ + τ₂) := (Real.rpow_add hNpos _ _).symm
  refine le_trans (measure_mono (t := {ω | N * flowTc (lam D N A) z ^ 2 *
      (mExt (lam D N A) z).im ^ 2 * hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0) z₁ z₂ -
        KTheta (lam D N A) θ z₁ z₂) ≤ (N : ℝ) ^ (2 * εg) ∧
      ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ₁ *
        ((flowTc (lam D N A) z / (flowTc (lam D N A) z - k * (S / K))) ^ 2 *
            hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0) z₁ z₂ -
              KTheta (lam D N A) θ z₁ z₂) +
          1 / (N * (flowTc (lam D N A) z - k * (S / K)) ^ 2 *
            flowIm (lam D N A) z (k * (S / K)) ^ 2)) <
        hsNorm (flowLmat (lam D N A) z₁ z₂ (k * (S / K)) (gridStateA D N K (S / K) ω k) -
          flowKmat (lam D N A) θ z₁ z₂ (k * (S / K)))} ∪ {ω | ω.1 ∈ Bs}) ?_) ?_
  · rintro ω ⟨k, hk, hlt⟩
    by_cases hB : ω.1 ∈ Bs
    · exact Or.inr hB
    · left
      have hle : hsNorm (Lmat (lam D N A) ω.1 z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) ≤
          (N : ℝ) ^ τ₂ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
            opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) := not_lt.1 hB
      have hX0 : 0 ≤ hsNorm (Lmat (lam D N A) ω.1 z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) :=
        Real.sqrt_nonneg _
      have hX := LFE_start2 D N A z hz θ hθ0 hθ1 z₁ z₂ h₁ h₂ c εg τ₂ _ hq0 hq1 hι0 hqι0 hq0inv hle
      have hu0 : 0 ≤ (k : ℝ) * (S / K) := by positivity
      have huS : (k : ℝ) * (S / K) ≤ S := by
        calc (k : ℝ) * (S / K) ≤ K * (S / K) :=
              mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) (div_nonneg hS0 hKpos.le)
          _ = S := by field_simp
      obtain ⟨-, hιk, -, -, -, -, -⟩ := LFE_flow D N hD1 hN1 A hΛ10 z hz S hSt _ hu0 huS
      have hqk : 0 < q₀ - k * (S / K) := by linarith
      have hE1 : 1 ≤ Real.exp ((k : ℝ) * (S / K) / 2) := Real.one_le_exp (by positivity)
      have hE : Real.exp ((k : ℝ) * (S / K) / 2) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.2 (by linarith)
      refine ⟨?_, k, hk, lt_of_le_of_lt ?_ hlt⟩
      · change (N : ℝ) * q₀ ^ 2 * ι₀ ^ 2 * _ ≤ _
        have e1 : (N : ℝ) * q₀ ^ 2 * ι₀ ^ 2 *
            hsNorm (Lmat (lam D N A) ω.1 z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) =
            (N * ι₀ ^ 2) * (q₀ ^ 2 *
              hsNorm (Lmat (lam D N A) ω.1 z₁ z₂ - KTheta (lam D N A) θ z₁ z₂)) := by ring
        have h2 := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ N * ι₀ ^ 2)
        have e2 : (N : ℝ) * ι₀ ^ 2 * (4 * c * (N : ℝ) ^ τ₂ * (N : ℝ) ^ εg / (N * ι₀ ^ 2)) =
            4 * c * (N : ℝ) ^ τ₂ * (N : ℝ) ^ εg := by
          have : ι₀ ≠ 0 := hι0.ne'
          field_simp
        have e3 : (N : ℝ) ^ (2 * εg) = (N : ℝ) ^ εg * (N : ℝ) ^ εg := by
          rw [← Real.rpow_add hNpos]; ring_nf
        change (N : ℝ) * q₀ ^ 2 * ι₀ ^ 2 *
          hsNorm (Lmat (lam D N A) ω.1 z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) ≤ _
        rw [e1, e3]
        rw [e2] at h2
        nlinarith
      · change (N : ℝ) ^ τ' * ((N : ℝ) ^ εg / (N * (q₀ - k * (S / K)) ^ 2 *
            flowIm (lam D N A) z (k * (S / K)) ^ 2)) ≥
          (N : ℝ) ^ τ₁ * ((q₀ / (q₀ - k * (S / K))) ^ 2 *
            hsNorm (Lmat (lam D N A) ω.1 z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) +
          1 / (N * (q₀ - k * (S / K)) ^ 2 * flowIm (lam D N A) z (k * (S / K)) ^ 2))
        rw [hιk]
        exact LFE_ar2 N q₀ _ ι₀ _ _ _ _ _ c _ hNpos hqk hι0 hE1 hE
          (Real.rpow_nonneg hNpos.le _) hNb hNd (by linarith) hX (by rw [hNab]; exact hfin)
  · refine (measure_union_le _ _).trans ?_
    refine (add_le_add hAg ((LFE_fst_le D N K μ₀ Bs).trans hBsμ)).trans ?_
    rw [← ENNReal.ofReal_add (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := LFE_budget N hN1 2 hN2 D'
    push_cast at this
    linarith

set_option maxHeartbeats 1000000 in
/-- Lemma 3.9 [lem_flow_2], (3.29) [flow_3G_res_2], on the grid: on the grid of `flowL2_grid`,
`‖L_{(1,2,3),k} - K_k‖₂ ≤ N^{τ'} N^{ε_g} / (N q_k³ (Im m_k)³)` at all grid times `u_k ≤ S`,
outside probability `N^{-D'}`. -/
theorem flowL3_grid_paper (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∀ Cg : ℝ, 33 + D' ≤ Cg → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ K : ℕ, (N : ℝ) ^ Cg ≤ K → (K : ℝ) ≤ (N : ℝ) ^ (Cg + 1) →
      ∀ z₁ z₂ z₃ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (z₃ = z ∨ z₃ = star z) →
        gridLawA D N K μ₀ {ω | ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ' * ((N : ℝ) ^ εg /
              (N * (flowTc (lam D N A) z - k * (S / K)) ^ 3 *
                flowIm (lam D N A) z (k * (S / K)) ^ 3)) <
            ten3Norm (flowLten3 (lam D N A) z₁ z₂ z₃ (k * (S / K)) (gridStateA D N K (S / K) ω k) -
              flowKten3 (lam D N A) θ z₁ z₂ z₃ (k * (S / K)))} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD' Cg hCg
  set τ₁ := τ' / 3 with hτ₁
  set τ₂ := min τ' εg / 3 with hτ₂
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₂0 : 0 < τ₂ := by have := lt_min hτ' hεg; positivity
  have hτ₂a : τ₂ ≤ τ' / 3 := by have := min_le_left τ' εg; linarith
  have hτ₂b : τ₂ < εg := by have := min_le_right τ' εg; linarith
  obtain ⟨Nl, hNl⟩ := flowL3_grid D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    τ₁ hτ₁0 (D' + 1) (by linarith) Cg (by linarith)
  obtain ⟨Ns, hNs⟩ := lemma_G_large_two D hD δA τ εg c hδA hτ hεg hεg₂ hc C τ₂ hτ₂0 (D' + 1)
    (by linarith)
  obtain ⟨Nt, hNt⟩ := lemma_G_large_three D hD δA τ εg c hδA hτ hεg hεg₂ hc C τ₂ hτ₂0 (D' + 1)
    (by linarith)
  have hev : ∀ᶠ N : ℕ in Filter.atTop, Nl ≤ N ∧ Ns ≤ N ∧ Nt ≤ N ∧ 6 ≤ N ∧
      2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧ c * (N : ℝ) ^ (-εg) ≤ 1 ∧
      4 * c * (N : ℝ) ^ τ₂ ≤ (N : ℝ) ^ εg ∧
      (Real.exp (1 / 2) ^ 3 + 1) * (N : ℝ) ^ (τ₁ + τ₂) ≤ (N : ℝ) ^ τ' := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    refine (Filter.eventually_ge_atTop Nl).and ((Filter.eventually_ge_atTop Ns).and
      ((Filter.eventually_ge_atTop Nt).and ((Filter.eventually_ge_atTop 6).and
      (((t1.const_mul 2).eventually (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and
      (((t2.const_mul c).eventually (Iic_mem_nhds (by simp : c * 0 < 1))).and
      ((LFE_ev_pow _ _ _ hτ₂b).and (LFE_ev_pow _ _ _ (by linarith))))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ₀ hμ₀ A z S hadm K hK1 hK2 z₁ z₂ z₃ h₁ h₂ h₃ => ?_⟩
  obtain ⟨hNl', hNs', hNt', hN6, hAN, hcN, hY, hfin⟩ := hN₀ N hN
  have := hμ₀.prob
  have : NeZero D := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hΛ10, -, hz, -, hq0, hq1, hS0, hSt, -⟩ :=
    LFE_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  set q₀ := flowTc (lam D N A) z with hq₀
  set ι₀ := (mExt (lam D N A) z).im with hι₀
  obtain ⟨-, hιeq0, hι0, -, -, -, hqι0⟩ := LFE_flow D N hD1 hN1 A hΛ10 z hz S hSt 0 le_rfl hS0
  obtain ⟨-, -, -, -, -, hcz⟩ := LFE_zero (lam D N A) θ z z z z (fun _ _ => 0)
  rw [hcz, hιeq0, sub_zero, zero_div, Real.exp_zero, one_mul] at hqι0
  have hq0inv : q₀⁻¹ ≤ 2 * c * (N : ℝ) ^ εg :=
    (LFE_q0 N hN1 εg c _ hc hadm.2.2.2.2.1 hadm.2.2.2.2.2.1 hcN).2.2
  have hlow : c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im := by
    refine le_trans ?_ hadm.2.2.2.1
    have hcpos : 0 < c⁻¹ := inv_pos.2 (by linarith)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hNr (by linarith)) hcpos.le
  set wz : Bool → ℂ := fun b => if b then star z else z with hwz
  have hwz1 : ∀ b, wz b = z ∨ wz b = star z := by
    intro b; cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hwz2 : ∀ w : ℂ, (w = z ∨ w = star z) → ∃ b, w = wz b := by
    rintro w (rfl | rfl)
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  -- the start events
  set Bs : Bool × Bool → Set (Idx D N → Idx D N → ℂ) := fun p =>
    {H | (N : ℝ) ^ τ₂ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
      opNorm (1 - Mhat (lam D N A) (wz p.1) (wz p.2) * PTheta D θ)⁻¹) <
    hsNorm (Lmat (lam D N A) H (wz p.1) (wz p.2) - KTheta (lam D N A) θ (wz p.1) (wz p.2))}
    with hBs
  have hBsμ : ∀ p, μ₀ (Bs p) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := fun p =>
    (hNs N hNs' θ hθ0 hθ1 μ₀ hμ₀ A hadm.1 z hadm.2.1 hz hlow hadm.2.2.2.2.1
      hadm.2.2.2.2.2.1 (wz p.1) (wz p.2) (hwz1 p.1) (hwz1 p.2)).2
  set B3 := {H : Idx D N → Idx D N → ℂ | (N : ℝ) ^ τ₂ * ((N : ℝ)⁻¹ * (z.im ^ 3)⁻¹ *
      (if z₁ = z₂ ∧ z₂ = z₃ then min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)
        else (N : ℝ) ^ εg)) <
    ten3Norm (Lten3 (lam D N A) H z₁ z₂ z₃ - KTheta3 (lam D N A) θ z₁ z₂ z₃)} with hB3
  have hB3μ : μ₀ B3 ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) :=
    hNt N hNt' θ hθ0 hθ1 μ₀ hμ₀ A hadm.1 z hadm.2.1 hz hlow hadm.2.2.2.2.1
      hadm.2.2.2.2.2.1 z₁ z₂ z₃ h₁ h₂ h₃
  have hAg := hNl N hNl' θ hθ0 hθ1 μ₀ hμ₀ A z S hadm K hK1 hK2 z₁ z₂ z₃ h₁ h₂ h₃
  have hK1' : 1 ≤ K := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ Cg := Real.one_le_rpow hNr (by linarith)
    exact_mod_cast this.trans hK1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1'
  have hNb : 1 ≤ (N : ℝ) ^ τ₂ := Real.one_le_rpow hNr hτ₂0.le
  have hNd : 1 ≤ (N : ℝ) ^ εg := Real.one_le_rpow hNr hεg.le
  have hNab : (N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₂ = (N : ℝ) ^ (τ₁ + τ₂) := (Real.rpow_add hNpos _ _).symm
  refine le_trans (measure_mono (t := {ω |
      (∀ w₁ w₂ : ℂ, (w₁ = z ∨ w₁ = star z) → (w₂ = z ∨ w₂ = star z) →
        N * flowTc (lam D N A) z ^ 2 * (mExt (lam D N A) z).im ^ 2 *
          hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0) w₁ w₂ -
            KTheta (lam D N A) θ w₁ w₂) ≤ (N : ℝ) ^ (2 * εg)) ∧
        ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ₁ *
          ((flowTc (lam D N A) z / (flowTc (lam D N A) z - k * (S / K))) ^ 3 *
              ten3Norm (Lten3 (lam D N A) (gridStateA D N K (S / K) ω 0) z₁ z₂ z₃ -
                KTheta3 (lam D N A) θ z₁ z₂ z₃) +
            (N : ℝ) ^ εg / (N * (flowTc (lam D N A) z - k * (S / K)) ^ 3 *
              flowIm (lam D N A) z (k * (S / K)) ^ 3)) <
          ten3Norm (flowLten3 (lam D N A) z₁ z₂ z₃ (k * (S / K))
              (gridStateA D N K (S / K) ω k) -
            flowKten3 (lam D N A) θ z₁ z₂ z₃ (k * (S / K)))} ∪ {ω | ω.1 ∈ B3} ∪
      ⋃ p : Bool × Bool, {ω | ω.1 ∈ Bs p}) ?_) ?_
  · rintro ω ⟨k, hk, hlt⟩
    by_cases hB : ω.1 ∈ B3 ∨ ∃ p, ω.1 ∈ Bs p
    · rcases hB with hB | ⟨p, hp⟩
      · exact Or.inl (Or.inr hB)
      · exact Or.inr (Set.mem_iUnion.2 ⟨p, hp⟩)
    · left; left
      push Not at hB
      obtain ⟨hB3n, hBsn⟩ := hB
      have hu0 : 0 ≤ (k : ℝ) * (S / K) := by positivity
      have huS : (k : ℝ) * (S / K) ≤ S := by
        calc (k : ℝ) * (S / K) ≤ K * (S / K) :=
              mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) (div_nonneg hS0 hKpos.le)
          _ = S := by field_simp
      obtain ⟨-, hιk, -, -, -, -, -⟩ := LFE_flow D N hD1 hN1 A hΛ10 z hz S hSt _ hu0 huS
      have hqk : 0 < q₀ - k * (S / K) := by linarith
      have hE1 : 1 ≤ Real.exp ((k : ℝ) * (S / K) / 2) := Real.one_le_exp (by positivity)
      have hE : Real.exp ((k : ℝ) * (S / K) / 2) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.2 (by linarith)
      refine ⟨?_, k, hk, lt_of_le_of_lt ?_ hlt⟩
      · intro w₁ w₂ hw₁ hw₂
        obtain ⟨b₁, rfl⟩ := hwz2 w₁ hw₁
        obtain ⟨b₂, rfl⟩ := hwz2 w₂ hw₂
        have hle : hsNorm (Lmat (lam D N A) ω.1 (wz b₁) (wz b₂) -
            KTheta (lam D N A) θ (wz b₁) (wz b₂)) ≤
            (N : ℝ) ^ τ₂ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
              opNorm (1 - Mhat (lam D N A) (wz b₁) (wz b₂) * PTheta D θ)⁻¹) :=
          not_lt.1 (hBsn (b₁, b₂))
        have hX := LFE_start2 D N A z hz θ hθ0 hθ1 (wz b₁) (wz b₂) hw₁ hw₂ c εg τ₂ _ hq0 hq1 hι0
          hqι0 hq0inv hle
        have e1 : (N : ℝ) * q₀ ^ 2 * ι₀ ^ 2 *
            hsNorm (Lmat (lam D N A) ω.1 (wz b₁) (wz b₂) - KTheta (lam D N A) θ (wz b₁) (wz b₂)) =
            (N * ι₀ ^ 2) * (q₀ ^ 2 * hsNorm (Lmat (lam D N A) ω.1 (wz b₁) (wz b₂) -
              KTheta (lam D N A) θ (wz b₁) (wz b₂))) := by ring
        have h2 := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ N * ι₀ ^ 2)
        have e2 : (N : ℝ) * ι₀ ^ 2 * (4 * c * (N : ℝ) ^ τ₂ * (N : ℝ) ^ εg / (N * ι₀ ^ 2)) =
            4 * c * (N : ℝ) ^ τ₂ * (N : ℝ) ^ εg := by
          have : ι₀ ≠ 0 := hι0.ne'
          field_simp
        have e3 : (N : ℝ) ^ (2 * εg) = (N : ℝ) ^ εg * (N : ℝ) ^ εg := by
          rw [← Real.rpow_add hNpos]; ring_nf
        change (N : ℝ) * q₀ ^ 2 * ι₀ ^ 2 * hsNorm (Lmat (lam D N A) ω.1 (wz b₁) (wz b₂) -
          KTheta (lam D N A) θ (wz b₁) (wz b₂)) ≤ _
        rw [e1, e3]
        rw [e2] at h2
        nlinarith
      · have hle : ten3Norm (Lten3 (lam D N A) ω.1 z₁ z₂ z₃ - KTheta3 (lam D N A) θ z₁ z₂ z₃) ≤
            (N : ℝ) ^ τ₂ * ((N : ℝ)⁻¹ * (z.im ^ 3)⁻¹ *
              (if z₁ = z₂ ∧ z₂ = z₃ then min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)
                else (N : ℝ) ^ εg)) := not_lt.1 hB3n
        have hif : (if z₁ = z₂ ∧ z₂ = z₃ then min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)
            else (N : ℝ) ^ εg) ≤ (N : ℝ) ^ εg := by
          split_ifs
          · exact min_le_right _ _
          · exact le_rfl
        have hT : ten3Norm (Lten3 (lam D N A) ω.1 z₁ z₂ z₃ - KTheta3 (lam D N A) θ z₁ z₂ z₃) ≤
            (N : ℝ) ^ τ₂ * ((N : ℝ)⁻¹ * (z.im ^ 3)⁻¹ * (N : ℝ) ^ εg) := by
          refine hle.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hif ?_) ?_)
          · have := pow_pos hz 3; positivity
          · positivity
        change (N : ℝ) ^ τ' * ((N : ℝ) ^ εg / (N * (q₀ - k * (S / K)) ^ 3 *
            flowIm (lam D N A) z (k * (S / K)) ^ 3)) ≥ (N : ℝ) ^ τ₁ *
            ((q₀ / (q₀ - k * (S / K))) ^ 3 *
              ten3Norm (Lten3 (lam D N A) ω.1 z₁ z₂ z₃ - KTheta3 (lam D N A) θ z₁ z₂ z₃) +
            (N : ℝ) ^ εg / (N * (q₀ - k * (S / K)) ^ 3 * flowIm (lam D N A) z (k * (S / K)) ^ 3))
        rw [hιk]
        exact LFE_ar3 N q₀ _ ι₀ z.im _ _ _ _ _ _ hNpos hq0 hqk hι0 hqι0 hE1 hE
          (Real.rpow_nonneg hNpos.le _) hNb hNd hT (by rw [hNab]; exact hfin)
  · have hx0 : 0 ≤ (N : ℝ) ^ (-(D' + 1)) := Real.rpow_nonneg hNpos.le _
    have hU : gridLawA D N K μ₀ (⋃ p : Bool × Bool, {ω | ω.1 ∈ Bs p}) ≤
        ENNReal.ofReal (4 * (N : ℝ) ^ (-(D' + 1))) := by
      refine (measure_iUnion_fintype_le _ _).trans ?_
      refine (Finset.sum_le_sum fun p _ => (LFE_fst_le D N K μ₀ (Bs p)).trans (hBsμ p)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by norm_num)]
      simp
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add ((measure_union_le _ _).trans
      (add_le_add hAg ((LFE_fst_le D N K μ₀ B3).trans hB3μ))) hU).trans ?_
    rw [← ENNReal.ofReal_add (Real.rpow_nonneg hNpos.le _) hx0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := LFE_budget N hN1 6 hN6 D'
    push_cast at this
    linarith

/-! ### Lemma 3.10: the one-resolvent expectation along the flow -/

/-- `G_s = (H + Λ_s - z_s)⁻¹` at the state `H` along the flow (3.10) [eq:deterflow]. -/
private abbrev LFE_G {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (s : ℝ)
    (H : Idx D N → Idx D N → ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s)

/-- `M_s = M(z_s, Λ_s)` along the flow (3.10) [eq:deterflow]. -/
private abbrev LFE_M {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (s : ℝ) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s)

/-- `⟨(G_s - M_s) E_a⟩` at the state `H`. -/
private abbrev LFE_d {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (s : ℝ)
    (H : Idx D N → Idx D N → ℂ) (a : Fin D) : ℂ :=
  ntr ((LFE_G Λ z s H - LFE_M Λ z s) * Ea D N a)

/-- `E⟨(G_s - M_s) E_a⟩` at the law (3.13) [eq:Gauss_div] at time `s`. -/
private abbrev LFE_v {D N : ℕ} (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (s : ℝ) (a : Fin D) : ℂ :=
  ∫ H, LFE_d Λ z s H a ∂(blockOULaw D N μ₀ s)

/-- The source term `Σ_a ⟨(G_s - M_s) E_a⟩ (L_s - K_s)_{ax}` of the one-loop equation, with
`L_s = L_{(1,1),s}` and `K_s = K_{θ_s}(z_s, z_s)`. -/
private abbrev LFE_f {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z : ℂ) (s : ℝ)
    (H : Idx D N → Idx D N → ℂ) (x : Fin D) : ℂ :=
  ∑ a, LFE_d Λ z s H a * (flowLmat Λ z z s H a x - flowKmat Λ θ z z s a x)

/-- The expectation of the source term at the law (3.13) [eq:Gauss_div] at time `s`. -/
private abbrev LFE_e {D N : ℕ} (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z : ℂ) (s : ℝ) (x : Fin D) : ℂ :=
  ∫ H, LFE_f Λ θ z s H x ∂(blockOULaw D N μ₀ s)

/-- The loop list `[(E_x, z)]`, whose loop is `⟨E_x G⟩`. -/
private abbrev LFE_l1 {D N : ℕ} (z : ℂ) (x : Fin D) : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ) :=
  [(Ea D N x, z)]

/-- The one-resolvent loop along the flow at the Hermitian part of an array. -/
private lemma LFE_loop1 {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (x : Fin D) (r : ℝ)
    (h : Idx D N → Idx D N → ℂ) :
    flowLoop Λ (LFE_l1 z x) r h =
      ntr (res (Matrix.of (hermPart h) + ((Real.exp (-r / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z r) *
        Ea D N x) := by
  simp only [flowLoop, chainB, LFE_l1, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Matrix.mul_one]
  exact LFE_ntr_comm _ _

/-- `⟨·⟩` is continuous. -/
private lemma LFE_ntr_cont {ι : Type*} [Fintype ι] : Continuous fun M : Matrix ι ι ℂ => ntr M := by
  unfold ntr
  exact continuous_const.mul (continuous_id.matrix_trace)

/-- `⟨A - B⟩ = ⟨A⟩ - ⟨B⟩`. -/
private lemma LFE_ntr_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    ntr (A - B) = ntr A - ntr B := by
  simp only [ntr, Matrix.trace_sub, mul_sub]

/-- `⟨c A⟩ = c ⟨A⟩`. -/
private lemma LFE_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (A : Matrix ι ι ℂ) :
    ntr (c • A) = c * ntr A := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

/-- Matrix inversion is measurable. -/
private lemma LFE_inv_meas {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : Matrix ι ι ℂ => A⁻¹) := by
  have : (fun A : Matrix ι ι ℂ => A⁻¹) = fun A => Ring.inverse A.det • A.adjugate := by
    funext A; exact Matrix.inv_def A
  rw [this]
  have h1 : Continuous (fun A : Matrix ι ι ℂ => A.adjugate) := continuous_id.matrix_adjugate
  have h2 : Continuous (fun A : Matrix ι ι ℂ => A.det) := continuous_id.matrix_det
  have h3 : Measurable (fun A : Matrix ι ι ℂ => Ring.inverse A.det) := by
    simp only [Ring.inverse_eq_inv']
    exact h2.measurable.inv
  exact h3.smul h1.measurable

/-- `H ↦ φ((H + Λ - w)⁻¹)` is measurable for continuous `φ`. -/
private lemma LFE_res_meas {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (w : ℂ)
    (φ : Matrix (Idx D N) (Idx D N) ℂ → ℂ) (hφ : Continuous φ) :
    Measurable fun H : Idx D N → Idx D N → ℂ => φ (res (Matrix.of H + Λ) w) := by
  unfold res
  have : Continuous fun H : Idx D N → Idx D N → ℂ =>
      Matrix.of H + Λ - w • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
    have : Continuous fun H : Idx D N → Idx D N → ℂ => (Matrix.of H : Matrix _ _ ℂ) :=
      continuous_id
    fun_prop
  exact hφ.measurable.comp (LFE_inv_meas.comp this.measurable)

/-- The Hermitian arrays form a measurable set. -/
private lemma LFE_herm_meas {D N : ℕ} :
    MeasurableSet {H : Idx D N → Idx D N → ℂ | (Matrix.of H).IsHermitian} := by
  have : {H : Idx D N → Idx D N → ℂ | (Matrix.of H).IsHermitian} =
      ⋂ i, ⋂ j, {H | star (H j i) = H i j} := by
    ext H
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Matrix.IsHermitian.ext_iff, Matrix.of_apply]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  have h1 : Continuous fun H : Idx D N → Idx D N → ℂ => star (H j i) := by fun_prop
  have h2 : Continuous fun H : Idx D N → Idx D N → ℂ => H i j := by fun_prop
  exact measurableSet_eq_fun h1.measurable h2.measurable

/-- A measurable function bounded on Hermitian arrays is integrable for a law of Hermitian
arrays. -/
private lemma LFE_int {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ H ∂μ, (Matrix.of H).IsHermitian) (f : (Idx D N → Idx D N → ℂ) → ℂ)
    (hf : Measurable f) (B : ℝ) (hB : ∀ H, (Matrix.of H).IsHermitian → ‖f H‖ ≤ B) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B (hμ.mono fun H hH => hB H hH)

/-- `‖x‖⁴ ≤ Σ_i ‖x_i‖⁴` for the sup norm. -/
private lemma LFE_pi_pow4 {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (x : ι → E) :
    ‖x‖ ^ 4 ≤ ∑ i, ‖x i‖ ^ 4 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim x 0]
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖)
      Finset.univ_nonempty
    have h : ‖x‖ ≤ ‖x i₀‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hi₀ i (Finset.mem_univ _)
    calc ‖x‖ ^ 4 ≤ ‖x i₀‖ ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h 4
      _ ≤ ∑ i, ‖x i‖ ^ 4 := Finset.single_le_sum (f := fun i => ‖x i‖ ^ 4)
          (fun i _ => by positivity) (Finset.mem_univ i₀)

/-- The fourth moment of `1 + ‖H‖` for a class member: `E(1 + ‖H‖)⁴ ≤ 8 + 8 D² |C₄|`, from
(2.3) [eq:highmoment]. -/
private lemma LFE_mom (D N : ℕ) (hN : 1 ≤ N) (C : ℕ → ℝ) (θ : ℝ)
    (μ : Measure (Idx D N → Idx D N → ℂ)) (hμ : LLClass D N C θ μ) :
    Integrable (fun H : Idx D N → Idx D N → ℂ => (1 + ‖H‖) ^ 4) μ ∧
      ∫ H, (1 + ‖H‖) ^ 4 ∂μ ≤ 8 + 8 * (D : ℝ) ^ 2 * |C 4| := by
  have := hμ.prob
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set g : (Idx D N → Idx D N → ℂ) → ℝ := fun H => 8 + 8 * ∑ i, ∑ j, ‖H i j‖ ^ 4 with hg
  have hgi : Integrable g μ :=
    (integrable_const 8).add ((integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hμ.integrable 4 i j).const_mul 8)
  have hpt : ∀ H : Idx D N → Idx D N → ℂ, (1 + ‖H‖) ^ 4 ≤ g H := by
    intro H
    have h1 : ‖H‖ ^ 4 ≤ ∑ i, ∑ j, ‖H i j‖ ^ 4 :=
      (LFE_pi_pow4 H).trans (Finset.sum_le_sum fun i _ => LFE_pi_pow4 (H i))
    have h0 := norm_nonneg H
    have h2 : (1 + ‖H‖) ^ 4 ≤ 8 * (1 + ‖H‖ ^ 4) := by
      nlinarith [sq_nonneg (‖H‖ - 1), sq_nonneg (‖H‖ + 1), sq_nonneg ‖H‖,
        mul_nonneg h0 (sq_nonneg (‖H‖ - 1)), sq_nonneg (‖H‖ ^ 2 - 1)]
    simp only [hg]
    linarith
  have hm : Continuous fun H : Idx D N → Idx D N → ℂ => (1 + ‖H‖) ^ 4 := by fun_prop
  have hint : Integrable (fun H : Idx D N → Idx D N → ℂ => (1 + ‖H‖) ^ 4) μ :=
    hgi.mono' hm.aestronglyMeasurable (ae_of_all _ fun H => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt H)
  refine ⟨hint, (integral_mono hint hgi hpt).trans ?_⟩
  have hmom : ∀ i j : Idx D N, ∫ H, ‖H i j‖ ^ 4 ∂μ ≤ |C 4| * ((N : ℝ) ^ 2)⁻¹ := by
    intro i j
    refine (hμ.moments 4 i j).trans ?_
    have e : (N : ℝ) ^ (-(((4 : ℕ) : ℝ) / 2)) = ((N : ℝ) ^ 2)⁻¹ := by
      rw [show -(((4 : ℕ) : ℝ) / 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hNpos.le,
        Real.rpow_natCast]
    rw [e]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hcalc : ∫ H, g H ∂μ = 8 + 8 * ∑ i, ∑ j, ∫ H, ‖H i j‖ ^ 4 ∂μ := by
    simp only [hg]
    rw [integral_add (integrable_const 8) ((integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hμ.integrable 4 i j).const_mul 8), integral_const,
      integral_const_mul, integral_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => hμ.integrable 4 i j]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hμ.integrable 4 i j]
  rw [hcalc]
  have hsum : ∑ i : Idx D N, ∑ j : Idx D N, ∫ H, ‖H i j‖ ^ 4 ∂μ ≤
      ∑ _i : Idx D N, ∑ _j : Idx D N, |C 4| * ((N : ℝ) ^ 2)⁻¹ :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hmom i j
  have hcard : ∑ _i : Idx D N, ∑ _j : Idx D N, |C 4| * ((N : ℝ) ^ 2)⁻¹ =
      (D : ℝ) ^ 2 * |C 4| := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp
  linarith

/-- The block GUE array as a continuous real-linear map of the coordinates. -/
private def LFE_arrL (D N : ℕ) : (Fin D → Coords N) →L[ℝ] (Idx D N → Idx D N → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => Matrix.of.symm (blockH D N w)
      map_add' := fun v w => by
        ext p q
        simp only [blockH, Pi.add_apply, wig_add, Matrix.add_apply, Matrix.of_symm_apply]
        split_ifs <;> simp
      map_smul' := fun c w => by
        ext p q
        simp only [blockH, Pi.smul_apply, wig_smul, Matrix.smul_apply, Matrix.of_symm_apply,
          RingHom.id_apply]
        split_ifs <;> simp [Complex.real_smul] }

/-- Along the flow at a Hermitian state: `‖G_s‖ ≤ η_s⁻¹` and `‖M_s‖ ≤ 5/4`, so
`|⟨(G_s - M_s) E_a⟩| ≤ η_s⁻¹ + 5/4`, `|⟨G_s E_a⟩| ≤ η_s⁻¹` and `|L_{ab}| ≤ D η_s⁻²`. -/
private lemma LFE_res_bds (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (s : ℝ)
    (hs : s < flowTc (lam D N A) z) (hs0 : 0 ≤ s) (H : Idx D N → Idx D N → ℂ)
    (hH : (Matrix.of H).IsHermitian) (a b : Fin D) :
    opNorm (LFE_G (lam D N A) z s H) ≤ (charFlowZ (lam D N A) z s).im⁻¹ ∧
      opNorm (LFE_M (lam D N A) z s) ≤ 5 / 4 ∧
      ‖LFE_d (lam D N A) z s H a‖ ≤ (charFlowZ (lam D N A) z s).im⁻¹ + 5 / 4 ∧
      ‖ntr (LFE_G (lam D N A) z s H * Ea D N a)‖ ≤ (charFlowZ (lam D N A) z s).im⁻¹ ∧
      ‖flowLmat (lam D N A) z z s H a b‖ ≤ D * ((charFlowZ (lam D N A) z s).im⁻¹) ^ 2 := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hΛs := LFE_herm_smul _ hΛ (Real.exp (-s / 2))
  have hX : (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A).IsHermitian := hH.add hΛs
  have hη := (charFlow_M _ hΛ z hz s hs).1
  have hG := opNorm_res_le _ hX _ hη
  have hnorm : opNorm (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) ≤ 1 / 10 := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-s / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h0 : 0 ≤ opNorm (lam D N A) := LFE_op_nonneg _
    nlinarith
  have hM : opNorm (LFE_M (lam D N A) z s) ≤ 5 / 4 := by
    have hapr := (mSol_apriori _ hΛs hnorm _ hη).2.2
    have e : LFE_M (lam D N A) z s =
        MSol (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z s) := by
      simp [LFE_M, MExt, MSol, mExt, hη]
    rw [e]
    have h0 := LFE_op_nonneg (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
    have : (1 - 2 * opNorm (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A))⁻¹ ≤ 5 / 4 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hE := LFE_opNorm_Ea D N a
  have hEb := LFE_opNorm_Ea D N b
  have hinv : 0 ≤ (charFlowZ (lam D N A) z s).im⁻¹ := inv_nonneg.2 hη.le
  have hG0 := LFE_op_nonneg (LFE_G (lam D N A) z s H)
  refine ⟨hG, hM, ?_, ?_, ?_⟩
  · refine (LFE_ntr_le _).trans ((LFE_op_mul _ _).trans ?_)
    have h1 := opNorm_add_le (LFE_G (lam D N A) z s H) (-LFE_M (lam D N A) z s)
    have h2 : opNorm (-LFE_M (lam D N A) z s) = opNorm (LFE_M (lam D N A) z s) := by
      rw [show -LFE_M (lam D N A) z s = (-1 : ℂ) • LFE_M (lam D N A) z s by simp, opNorm_smul]
      simp
    rw [← sub_eq_add_neg, h2] at h1
    have h3 := LFE_op_nonneg (LFE_G (lam D N A) z s H - LFE_M (lam D N A) z s)
    calc opNorm (LFE_G (lam D N A) z s H - LFE_M (lam D N A) z s) * opNorm (Ea D N a)
        ≤ opNorm (LFE_G (lam D N A) z s H - LFE_M (lam D N A) z s) * 1 :=
          mul_le_mul_of_nonneg_left hE h3
      _ ≤ _ := by linarith
  · refine (LFE_ntr_le _).trans ((LFE_op_mul _ _).trans ?_)
    calc opNorm (LFE_G (lam D N A) z s H) * opNorm (Ea D N a)
        ≤ (charFlowZ (lam D N A) z s).im⁻¹ * 1 := mul_le_mul hG hE (LFE_op_nonneg _) hinv
      _ = _ := mul_one _
  · simp only [flowLmat, Lmat]
    rw [norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine (LFE_ntr_le _).trans ?_
    have p3 := LFE_op_nonneg (Ea D N a)
    have p4 := LFE_op_nonneg (Ea D N b)
    calc opNorm (LFE_G (lam D N A) z s H * Ea D N a * LFE_G (lam D N A) z s H * Ea D N b)
        ≤ opNorm (LFE_G (lam D N A) z s H) * opNorm (Ea D N a) *
            opNorm (LFE_G (lam D N A) z s H) * opNorm (Ea D N b) := by
          refine (LFE_op_mul _ _).trans ?_
          refine mul_le_mul_of_nonneg_right ((LFE_op_mul _ _).trans ?_) p4
          exact mul_le_mul_of_nonneg_right (LFE_op_mul _ _) hG0
      _ ≤ (charFlowZ (lam D N A) z s).im⁻¹ * 1 * (charFlowZ (lam D N A) z s).im⁻¹ * 1 := by
          gcongr
      _ = _ := by ring

/-- Along the flow, `‖q_s K_{θ_s}(z_s, z_s)‖ ≤ 1` (`tOp_norm_le` at the flowed point), so
`|(K_s)_{ab}| ≤ q_s⁻¹`. -/
private lemma LFE_K_le (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (s : ℝ) (hs0 : 0 ≤ s)
    (hs : s < flowTc (lam D N A) z) (a b : Fin D) :
    ‖flowKmat (lam D N A) θ z z s a b‖ ≤ (flowTc (lam D N A) z - s)⁻¹ := by
  have hΛ := lam_isHermitian D N A
  have hηs := (charFlow_M _ hΛ z hz s hs).1
  have he0 : 0 < Real.exp (-s) := Real.exp_pos _
  have he1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hθ0' : 0 ≤ Real.exp (-s) * θ + 1 - Real.exp (-s) := by nlinarith
  have hθ1' : Real.exp (-s) * θ + 1 - Real.exp (-s) ≤ 1 := by nlinarith
  obtain ⟨-, hop, -⟩ := tOp_norm_le D N (((Real.exp (-s / 2) : ℝ) : ℂ) • A)
    (charFlowZ (lam D N A) z s) hηs _ hθ0' hθ1' _ _ (Or.inl rfl) (Or.inl rfl)
  have hlam : lam D N (((Real.exp (-s / 2) : ℝ) : ℂ) • A) =
      ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A := (LFE_lam_smul D N A _).symm
  rw [hlam, flowTc_flow _ hΛ z hz s hs] at hop
  have hq : 0 < flowTc (lam D N A) z - s := by linarith
  rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] at hop
  refine (norm_apply_le_opNorm _ a b).trans ?_
  change opNorm (KTheta _ _ _ _) ≤ _
  calc opNorm (KTheta (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
        (Real.exp (-s) * θ + 1 - Real.exp (-s)) (charFlowZ (lam D N A) z s)
          (charFlowZ (lam D N A) z s)) =
      (flowTc (lam D N A) z - s)⁻¹ * ((flowTc (lam D N A) z - s) * opNorm (KTheta
        (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) (Real.exp (-s) * θ + 1 - Real.exp (-s))
          (charFlowZ (lam D N A) z s) (charFlowZ (lam D N A) z s))) := by field_simp
    _ ≤ (flowTc (lam D N A) z - s)⁻¹ * 1 := mul_le_mul_of_nonneg_left hop (inv_nonneg.2 hq.le)
    _ = _ := mul_one _

/-- The size of the derivatives of the one-resolvent loop:
`c (DN + 1)⁴ e^{q} K² ‖E‖ (η_S ∧ 1)^{-7} ≤ |c| 16 D⁴ e (4 + τ⁻¹)² N^{11}` when `q ≤ 1`,
`K ≤ 4 + τ⁻¹`, `‖E‖ ≤ 1` and `η_S ∧ 1 ≥ N⁻¹`. -/
private lemma LFE_ar_B (c D N e K P m τ : ℝ) (hD : 1 ≤ D) (hN : 2 ≤ N) (he : e ≤ Real.exp 1)
    (he0 : 0 ≤ e) (hK0 : 0 ≤ K) (hK : K ≤ 4 + τ⁻¹) (hP0 : 0 ≤ P) (hP : P ≤ 1)
    (hm : N⁻¹ ≤ m) :
    c * (D * N + 1) ^ 4 * e * K ^ 2 * P * (m ^ 7)⁻¹ ≤
      (|c| * (16 * D ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2) * N ^ 11 := by
  have hNpos : 0 < N := by linarith
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.2 hNpos) hm
  have h7 : (m ^ 7)⁻¹ ≤ N ^ 7 := by
    rw [inv_le_comm₀ (pow_pos hmpos _) (by positivity), ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hNpos.le) hm _
  have hDN : D * N + 1 ≤ 2 * D * N := by nlinarith
  have hDN4 : (D * N + 1) ^ 4 ≤ 16 * D ^ 4 * N ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hDN 4
    nlinarith
  have hc : c ≤ |c| := le_abs_self _
  have hK2 : K ^ 2 ≤ (4 + τ⁻¹) ^ 2 := pow_le_pow_left₀ hK0 hK 2
  have hm0 : 0 ≤ (m ^ 7)⁻¹ := inv_nonneg.2 (pow_nonneg hmpos.le _)
  calc c * (D * N + 1) ^ 4 * e * K ^ 2 * P * (m ^ 7)⁻¹
      ≤ |c| * (D * N + 1) ^ 4 * e * K ^ 2 * P * (m ^ 7)⁻¹ := by gcongr
    _ ≤ |c| * (16 * D ^ 4 * N ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2 * 1 * N ^ 7 := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 3200000 in
-- The integrability side conditions of the expansion are handled in one proof.
/-- One step of the one-loop equation of Lemma 3.10 [lem_flow_1.5] in law: for `0 ≤ s`,
`0 < h`, `s + h ≤ S`, with `u_a(r) = E⟨(G_r - M_r) E_a⟩` at the law (3.13) [eq:Gauss_div] at
time `r`, `|u_x(s + h) - u_x(s) - h (u_x(s)/2 + Σ_a u_a(s) (K_s)_{ax} + e_x(s))| ≤ K N^{15} h²`,
where `e_x(s) = E Σ_a ⟨(G_s - M_s) E_a⟩ (L_s - K_s)_{ax}` and `K` depends on `D`, `τ`, `C`. -/
private lemma LFE_step (D : ℕ) (hD : 1 ≤ D) (τ : ℝ) (hτ : 0 < τ) (C : ℕ → ℝ) :
    ∃ Kst : ℝ, 0 ≤ Kst ∧ ∀ N : ℕ, 2 ≤ N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), opNorm (lam D N A) ≤ 1 / 10 →
      ‖z‖ ≤ τ⁻¹ → 0 < z.im → ‖mExt (lam D N A) z‖ < 1 → flowTc (lam D N A) z ≤ 1 → 0 ≤ S →
      S < flowTc (lam D N A) z →
      (∀ s, 0 ≤ s → s ≤ S → (N : ℝ)⁻¹ < (charFlowZ (lam D N A) z s).im) →
      ∀ s h : ℝ, 0 ≤ s → 0 < h → s + h ≤ S → ∀ x : Fin D,
        ‖LFE_v μ₀ (lam D N A) z (s + h) x - LFE_v μ₀ (lam D N A) z s x -
          (h : ℂ) * ((1 / 2 : ℂ) * LFE_v μ₀ (lam D N A) z s x +
            (∑ a, LFE_v μ₀ (lam D N A) z s a * flowKmat (lam D N A) θ z z s a x) +
            LFE_e μ₀ (lam D N A) θ z s x)‖ ≤ Kst * (N : ℝ) ^ 15 * h ^ 2 := by
  obtain ⟨cR, hcR⟩ := flowLoop_regular
  obtain ⟨KG, hKG⟩ := gaussStepA_expansion_t
  obtain ⟨C', hC'⟩ := llClass_blockOU D C
  set Mom : ℝ := 8 + 8 * (D : ℝ) ^ 2 * |C' 4| with hMom
  set Bc : ℝ := |cR 1| * (16 * (D : ℝ) ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2 with hBc
  set K0 : ℝ := |KG| * Bc * (16 * (D : ℝ) ^ 4) * Mom with hK0
  have hMom0 : 0 ≤ Mom := by positivity
  have hBc0 : 0 ≤ Bc := by positivity
  have hK00 : 0 ≤ K0 := by positivity
  refine ⟨K0 + 1, by positivity, ?_⟩
  intro N hN2 θ hθ0 hθ1 μ₀ hμ₀ A z S hΛ10 hzτ hz hm1 hq1 hS0 hSt hη s h hs0 hh hsh x
  have : NeZero D := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  have hN1 : 1 ≤ N := by omega
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN1⟩)⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hD1r : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have := hμ₀.prob
  have hΛ : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hSpos : 0 < S := by linarith
  have hsS : s ≤ S := by linarith
  have hh1 : h ≤ 1 := by linarith
  have hs1 : s < flowTc (lam D N A) z := by linarith
  have hsI : s ∈ Set.Icc 0 S := ⟨hs0, hsS⟩
  have hshI : s + h ∈ Set.Icc 0 S := ⟨by linarith, hsh⟩
  have hl : ∀ f ∈ LFE_l1 (N := N) z x, f.2 = z ∨ f.2 = star z := by
    intro f hf
    simp only [LFE_l1, List.mem_cons, List.not_mem_nil, or_false] at hf
    rw [hf]; exact Or.inl rfl
  obtain ⟨Ft, hder, hreg⟩ := hcR D N (lam D N A) hΛ z hz (LFE_l1 z x) hl S hS0 hSt
  set F : ℝ → (Idx D N → Idx D N → ℂ) → ℂ := fun r v => flowLoop (lam D N A) (LFE_l1 z x) r v
    with hF
  have hsub : Set.Icc s (s + h) ⊆ Set.Icc 0 S := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hexp := hKG D N F Ft _ h s hh hh1
    (fun r hr => ⟨(hreg r (hsub hr)).1, (hreg r (hsub hr)).2.1⟩)
    (fun r hr v => (hder r (hsub hr) v).mono hsub)
    (fun r hr j hj1 hj4 v => (hreg r (hsub hr)).2.2.1 j hj1 hj4 v)
    (fun r hr r' hr' v => (hreg r (hsub hr)).2.2.2 r' (hsub hr') v)
  -- the size `B` of the derivatives
  have hB0 := (norm_nonneg _).trans ((hreg s hsI).2.2.1 1 le_rfl (by norm_num) 0).1
  have hBeq : cR (LFE_l1 (N := N) z x).length * ((D : ℝ) * N + 1) ^ 4 *
      Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      ((LFE_l1 (N := N) z x).map fun f => opNorm f.1).prod *
      ((min 1 (charFlowZ (lam D N A) z S).im) ^ ((LFE_l1 (N := N) z x).length + 6))⁻¹ =
      cR 1 * ((D : ℝ) * N + 1) ^ 4 * Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      opNorm (Ea D N x) * ((min 1 (charFlowZ (lam D N A) z S).im) ^ 7)⁻¹ := by
    simp only [LFE_l1, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
  rw [hBeq] at hB0 hexp
  have hηS := hη S hS0 le_rfl
  have hBle := LFE_ar_B (cR 1) D N (Real.exp (flowTc (lam D N A) z))
    (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A))
    (opNorm (Ea D N x)) (min 1 (charFlowZ (lam D N A) z S).im) τ hD1r hNr
    (Real.exp_le_exp.2 hq1) (Real.exp_pos _).le
    (by have h1 := norm_nonneg z; have h2 := norm_nonneg (mExt (lam D N A) z)
        have h3 := LFE_op_nonneg (lam D N A); linarith only [h1, h2, h3])
    (by linarith only [hzτ, hm1, hΛ10]) (LFE_op_nonneg _) (LFE_opNorm_Ea D N x)
    (le_min (inv_le_one_of_one_le₀ (by linarith)) hηS.le)
  rw [← hBc] at hBle
  set B := cR 1 * ((D : ℝ) * N + 1) ^ 4 * Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      opNorm (Ea D N x) * ((min 1 (charFlowZ (lam D N A) z S).im) ^ 7)⁻¹ with hB
  clear_value B
  -- the loop at Hermitian states
  have hFH : ∀ (r : ℝ) (H : Idx D N → Idx D N → ℂ), (Matrix.of H).IsHermitian →
      F r H = ntr (LFE_G (lam D N A) z r H * Ea D N x) := by
    intro r H hH
    simp only [hF]
    rw [LFE_loop1, LFE_hermPart_eq H hH]
  -- `|F r v| ≤ N` on `[0, S]`
  have hFb : ∀ r ∈ Set.Icc 0 S, ∀ v, ‖F r v‖ ≤ N := by
    intro r hr v
    have hrq : r < flowTc (lam D N A) z := lt_of_le_of_lt hr.2 hSt
    have hb := (LFE_res_bds D N hD hN1 A hΛ10 z hz r hrq hr.1 (hermPart v)
      (LFE_hermPart_herm v) x x).2.2.2.1
    have hηr := hη r hr.1 hr.2
    have hη0 : 0 < (charFlowZ (lam D N A) z r).im :=
      lt_trans (inv_pos.2 hNpos) hηr
    simp only [hF]
    rw [LFE_loop1]
    refine hb.trans ?_
    rw [inv_le_comm₀ hη0 hNpos]
    exact hηr.le
  -- the identity of M9 for one resolvent (`gen_loop1`)
  have hid : ∀ H : Idx D N → Idx D N → ℂ, (Matrix.of H).IsHermitian →
      Ft s H + genA (F s) H = (1 / 2 : ℂ) * ntr (LFE_G (lam D N A) z s H * Ea D N x) +
        ∑ a, LFE_d (lam D N A) z s H a * flowLmat (lam D N A) z z s H a x := by
    intro H hH
    have hd1 : HasDerivWithinAt (fun r => ntr (LFE_G (lam D N A) z r H * Ea D N x))
        (Ft s H) (Set.Icc 0 S) s :=
      (hder s hsI H).congr (fun r _ => (hFH r H hH).symm) (hFH s H hH).symm
    have hd2 := gen_loop1 D N A z hz s hs1 z (Or.inl rfl) H hH x
    have huniq := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc hSpos s hsI) hd1
      hd2.hasDerivWithinAt
    have hgen : genA (fun h => ntr (res (Matrix.of (hermPart h) +
        ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z s) * Ea D N x)) H =
        genA (F s) H := by
      congr 1
      funext v
      simp only [hF]
      rw [LFE_loop1]
    rw [huniq, hgen]
    simp only [flowLmat]
    ring
  -- the laws at times `s` and `s + h`
  have hcls := hC' N θ μ₀ s hθ0 hθ1 hs0 hμ₀
  have hclsh := hC' N θ μ₀ (s + h) hθ0 hθ1 (by linarith) hμ₀
  have := hcls.prob
  have := hclsh.prob
  set μs := blockOULaw D N μ₀ s with hμs
  set μsh := blockOULaw D N μ₀ (s + h) with hμsh
  -- measurability
  have hGm : ∀ (r : ℝ) (φ : Matrix (Idx D N) (Idx D N) ℂ → ℂ), Continuous φ →
      Measurable fun H : Idx D N → Idx D N → ℂ => φ (LFE_G (lam D N A) z r H) :=
    fun r φ hφ => LFE_res_meas _ _ φ hφ
  have hd_m : ∀ (r : ℝ) (a : Fin D), Measurable fun H => LFE_d (lam D N A) z r H a :=
    fun r a => hGm r (fun G => ntr ((G - LFE_M (lam D N A) z r) * Ea D N a))
      (LFE_ntr_cont.comp ((continuous_id.sub continuous_const).matrix_mul continuous_const))
  have hg_m : Measurable fun H => ntr (LFE_G (lam D N A) z s H * Ea D N x) :=
    hGm s (fun G => ntr (G * Ea D N x))
      (LFE_ntr_cont.comp (continuous_id.matrix_mul continuous_const))
  have hL_m : ∀ a : Fin D, Measurable fun H => flowLmat (lam D N A) z z s H a x := by
    intro a
    have e : (fun H => flowLmat (lam D N A) z z s H a x) = fun H =>
        (fun G : Matrix (Idx D N) (Idx D N) ℂ => (D : ℂ) * ntr (G * Ea D N a * G * Ea D N x))
          (LFE_G (lam D N A) z s H) := by
      funext H; rfl
    rw [e]
    exact hGm s _ (continuous_const.mul (LFE_ntr_cont.comp
      (((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id).matrix_mul
        continuous_const)))
  -- bounds at Hermitian states at time `s`
  have hηs := hη s hs0 hsS
  have hηs0 : 0 < (charFlowZ (lam D N A) z s).im := lt_trans (inv_pos.2 hNpos) hηs
  have hηinv : (charFlowZ (lam D N A) z s).im⁻¹ ≤ N := by
    rw [inv_le_comm₀ hηs0 hNpos]; exact hηs.le
  have hbd : ∀ H : Idx D N → Idx D N → ℂ, (Matrix.of H).IsHermitian → ∀ a : Fin D,
      ‖LFE_d (lam D N A) z s H a‖ ≤ N + 5 / 4 ∧
        ‖ntr (LFE_G (lam D N A) z s H * Ea D N x)‖ ≤ N ∧
        ‖flowLmat (lam D N A) z z s H a x‖ ≤ D * (N : ℝ) ^ 2 := by
    intro H hH a
    obtain ⟨-, -, h1, h2, h3⟩ := LFE_res_bds D N hD hN1 A hΛ10 z hz s hs1 hs0 H hH a x
    have h2' := LFE_res_bds D N hD hN1 A hΛ10 z hz s hs1 hs0 H hH x x
    refine ⟨by linarith, h2'.2.2.2.1.trans hηinv, h3.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 hηs0.le) hηinv 2)
      (Nat.cast_nonneg _)
  have hK : ∀ a : Fin D, ‖flowKmat (lam D N A) θ z z s a x‖ ≤ (flowTc (lam D N A) z - s)⁻¹ :=
    fun a => LFE_K_le D N A z hz θ hθ0 hθ1 s hs0 hs1 a x
  -- integrability at time `s`
  have hd_i : ∀ a : Fin D, Integrable (fun H => LFE_d (lam D N A) z s H a) μs := fun a =>
    LFE_int μs hcls.herm _ (hd_m s a) _ fun H hH => (hbd H hH a).1
  have hg_i : Integrable (fun H => ntr (LFE_G (lam D N A) z s H * Ea D N x)) μs :=
    LFE_int μs hcls.herm _ hg_m _ fun H hH => (hbd H hH x).2.1
  have hdL_i : ∀ a : Fin D, Integrable (fun H =>
      LFE_d (lam D N A) z s H a * flowLmat (lam D N A) z z s H a x) μs := fun a =>
    LFE_int μs hcls.herm _ ((hd_m s a).mul (hL_m a)) ((N + 5 / 4) * (D * (N : ℝ) ^ 2))
      fun H hH => by
        rw [norm_mul]
        exact mul_le_mul (hbd H hH a).1 (hbd H hH a).2.2 (norm_nonneg _) (by positivity)
  have hf_i : Integrable (fun H => LFE_f (lam D N A) θ z s H x) μs := by
    have e : (fun H => LFE_f (lam D N A) θ z s H x) = fun H => ∑ a,
        (LFE_d (lam D N A) z s H a * flowLmat (lam D N A) z z s H a x -
          flowKmat (lam D N A) θ z z s a x * LFE_d (lam D N A) z s H a) := by
      funext H
      simp only [LFE_f]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [e]
    exact integrable_finsetSum _ fun a _ => (hdL_i a).sub ((hd_i a).const_mul _)
  -- `F (s + h)` is continuous and bounded
  have hFc : Continuous (F (s + h)) := (hreg (s + h) hshI).1.continuous
  have hFi : Integrable (F (s + h)) μsh :=
    Integrable.of_bound hFc.aestronglyMeasurable N (ae_of_all _ fun v => hFb _ hshI v)
  -- (i) `u_x(s + h) = E F(s + h) - ⟨M_{s+h} E_x⟩`
  have hv1 : LFE_v μ₀ (lam D N A) z (s + h) x =
      (∫ H, F (s + h) H ∂μsh) - ntr (LFE_M (lam D N A) z (s + h) * Ea D N x) := by
    have hae : (fun H => LFE_d (lam D N A) z (s + h) H x) =ᵐ[μsh]
        fun H => F (s + h) H - ntr (LFE_M (lam D N A) z (s + h) * Ea D N x) := by
      filter_upwards [hclsh.herm] with H hH
      rw [hFH _ H hH]
      simp only [LFE_d, Matrix.sub_mul, LFE_ntr_sub]
    change ∫ H, LFE_d (lam D N A) z (s + h) H x ∂μsh = _
    rw [integral_congr_ae hae, integral_sub hFi (integrable_const _), integral_const,
      probReal_univ, one_smul]
  -- (ii) one step in law
  have hstep := gridExpStepA D N μ₀ s h hs0 hh.le (F (s + h)) hFc.measurable N
    (fun v => hFb _ hshI v)
  set inner : (Idx D N → Idx D N → ℂ) → ℂ := fun H => ∫ X, F (s + h)
    (Real.exp (-h / 2) • H + Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X))
      ∂(gueBlocks D N) with hinner
  have hinner_m : StronglyMeasurable inner := by
    have hφ : Continuous fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
        F (s + h) (Real.exp (-h / 2) • p.1 + Real.sqrt (1 - Real.exp (-h)) • LFE_arrL D N p.2) :=
      hFc.comp ((continuous_const_smul _).comp continuous_fst |>.add
        ((continuous_const_smul _).comp ((LFE_arrL D N).continuous.comp continuous_snd)))
    exact hφ.stronglyMeasurable.integral_prod_right'
  have hinner_i : Integrable inner μs := by
    refine Integrable.of_bound hinner_m.aestronglyMeasurable N (ae_of_all _ fun H => ?_)
    refine (norm_integral_le_of_norm_le_const (ae_of_all _ fun X => hFb _ hshI _)).trans ?_
    simp
  -- (iii) the expansion, integrated
  set expl : (Idx D N → Idx D N → ℂ) → ℂ := fun H =>
    ntr (LFE_G (lam D N A) z s H * Ea D N x) + (h : ℂ) *
      ((1 / 2 : ℂ) * ntr (LFE_G (lam D N A) z s H * Ea D N x) +
        ∑ a, LFE_d (lam D N A) z s H a * flowLmat (lam D N A) z z s H a x) with hexpl
  have hexpl_i : Integrable expl μs :=
    hg_i.add ((hg_i.const_mul _).add (integrable_finsetSum _ fun a _ => hdL_i a) |>.const_mul _)
  have hmom := LFE_mom D N hN1 C' _ μs hcls
  set Rb : (Idx D N → Idx D N → ℂ) → ℝ := fun H =>
    |KG| * B * h ^ 2 * ((D : ℝ) * N + 1) ^ 4 * (1 + ‖H‖) ^ 4 with hRb
  have hRb_i : Integrable Rb μs := by
    have e : Rb = fun H => (|KG| * B * h ^ 2 * ((D : ℝ) * N + 1) ^ 4) * (1 + ‖H‖) ^ 4 := by
      funext H; rfl
    rw [e]; exact hmom.1.const_mul _
  have hpt : ∀ᵐ H ∂μs, ‖inner H - expl H‖ ≤ Rb H := by
    filter_upwards [hcls.herm] with H hH
    have e1 : inner H - expl H = inner H - F s H - (h : ℂ) * (Ft s H + genA (F s) H) := by
      rw [hid H hH, hFH s H hH, hexpl]
      ring
    rw [e1]
    refine (hexp H).trans ?_
    simp only [hRb]
    have h0 : 0 ≤ B * h ^ 2 * (1 + ‖H‖) ^ 4 * ((D : ℝ) * N + 1) ^ 4 := by positivity
    calc KG * B * h ^ 2 * (1 + ‖H‖) ^ 4 * ((D : ℝ) * N + 1) ^ 4
        = KG * (B * h ^ 2 * (1 + ‖H‖) ^ 4 * ((D : ℝ) * N + 1) ^ 4) := by ring
      _ ≤ |KG| * (B * h ^ 2 * (1 + ‖H‖) ^ 4 * ((D : ℝ) * N + 1) ^ 4) :=
          mul_le_mul_of_nonneg_right (le_abs_self KG) h0
      _ = _ := by ring
  have hdiff : ‖(∫ H, inner H ∂μs) - ∫ H, expl H ∂μs‖ ≤ K0 * (N : ℝ) ^ 15 * h ^ 2 := by
    rw [← integral_sub hinner_i hexpl_i]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (ae_of_all _ fun H => norm_nonneg _) hRb_i hpt).trans ?_
    have e : ∫ H, Rb H ∂μs = |KG| * B * h ^ 2 * ((D : ℝ) * N + 1) ^ 4 *
        ∫ H, (1 + ‖H‖) ^ 4 ∂μs := by
      simp only [hRb]; rw [integral_const_mul]
    rw [e]
    have hDN : ((D : ℝ) * N + 1) ^ 4 ≤ 16 * (D : ℝ) ^ 4 * (N : ℝ) ^ 4 := by
      have h1 : (D : ℝ) * N + 1 ≤ 2 * D * N := by nlinarith
      have := pow_le_pow_left₀ (by positivity) h1 4
      nlinarith
    have hI0 : 0 ≤ ∫ H, (1 + ‖H‖) ^ 4 ∂μs := integral_nonneg fun H => by positivity
    calc |KG| * B * h ^ 2 * ((D : ℝ) * N + 1) ^ 4 * ∫ H, (1 + ‖H‖) ^ 4 ∂μs
        ≤ |KG| * (Bc * (N : ℝ) ^ 11) * h ^ 2 * (16 * (D : ℝ) ^ 4 * (N : ℝ) ^ 4) * Mom := by
          gcongr
          exact hmom.2
      _ = K0 * (N : ℝ) ^ 15 * h ^ 2 := by rw [hK0]; ring
  -- (iv) the integral of the expansion
  set m : ℝ → ℂ := fun r => ntr (LFE_M (lam D N A) z r * Ea D N x) with hm
  have hgv : ∫ H, ntr (LFE_G (lam D N A) z s H * Ea D N x) ∂μs =
      LFE_v μ₀ (lam D N A) z s x + m s := by
    have hae : (fun H => ntr (LFE_G (lam D N A) z s H * Ea D N x)) =ᵐ[μs]
        fun H => LFE_d (lam D N A) z s H x + m s := by
      refine ae_of_all _ fun H => ?_
      simp only [hm, LFE_d, Matrix.sub_mul, LFE_ntr_sub]
      ring
    rw [integral_congr_ae hae, integral_add (hd_i x) (integrable_const _), integral_const,
      probReal_univ, one_smul]
  have hdLv : ∫ H, ∑ a, LFE_d (lam D N A) z s H a * flowLmat (lam D N A) z z s H a x ∂μs =
      (∑ a, LFE_v μ₀ (lam D N A) z s a * flowKmat (lam D N A) θ z z s a x) +
        LFE_e μ₀ (lam D N A) θ z s x := by
    have hpt2 : (fun H => ∑ a, LFE_d (lam D N A) z s H a * flowLmat (lam D N A) z z s H a x) =
        fun H => LFE_f (lam D N A) θ z s H x +
          ∑ a, flowKmat (lam D N A) θ z z s a x * LFE_d (lam D N A) z s H a := by
      funext H
      simp only [LFE_f, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [hpt2, integral_add hf_i (integrable_finsetSum _ fun a _ => (hd_i a).const_mul _),
      integral_finsetSum _ fun a _ => (hd_i a).const_mul _]
    simp only [integral_const_mul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hI2 : Integrable (fun H => (1 / 2 : ℂ) * ntr (LFE_G (lam D N A) z s H * Ea D N x) +
      ∑ a, LFE_d (lam D N A) z s H a * flowLmat (lam D N A) z z s H a x) μs :=
    (hg_i.const_mul _).add (integrable_finsetSum _ fun a _ => hdL_i a)
  have hI3 : Integrable (fun H => (h : ℂ) * ((1 / 2 : ℂ) *
      ntr (LFE_G (lam D N A) z s H * Ea D N x) +
      ∑ a, LFE_d (lam D N A) z s H a * flowLmat (lam D N A) z z s H a x)) μs := hI2.const_mul _
  have hI4 : Integrable (fun H => (1 / 2 : ℂ) * ntr (LFE_G (lam D N A) z s H * Ea D N x)) μs :=
    hg_i.const_mul _
  have hI5 : Integrable (fun H =>
      ∑ a, LFE_d (lam D N A) z s H a * flowLmat (lam D N A) z z s H a x) μs :=
    integrable_finsetSum _ fun a _ => hdL_i a
  have hexplv : ∫ H, expl H ∂μs = (LFE_v μ₀ (lam D N A) z s x + m s) + (h : ℂ) *
      ((1 / 2 : ℂ) * (LFE_v μ₀ (lam D N A) z s x + m s) +
        ((∑ a, LFE_v μ₀ (lam D N A) z s a * flowKmat (lam D N A) θ z z s a x) +
          LFE_e μ₀ (lam D N A) θ z s x)) := by
    simp only [hexpl]
    rw [integral_add hg_i hI3, integral_const_mul, integral_add hI4 hI5, integral_const_mul, hgv,
      hdLv]
  -- (v) the deterministic term `⟨M_r E_x⟩ = e^{r/2} ⟨M E_x⟩`
  have hmr : ∀ r, r < flowTc (lam D N A) z →
      m r = ((Real.exp (r / 2) : ℝ) : ℂ) * ntr (MExt (lam D N A) z * Ea D N x) := by
    intro r hr
    simp only [hm, LFE_M]
    rw [(charFlow_M _ hΛ z hz r hr).2.1, Matrix.smul_mul, LFE_ntr_smul]
  have hM0 : ‖ntr (MExt (lam D N A) z * Ea D N x)‖ ≤ 5 / 4 := by
    have hb := (LFE_res_bds D N hD hN1 A hΛ10 z hz 0 (by linarith) le_rfl 0
      (by simp) x x).2.1
    have e : LFE_M (lam D N A) z 0 = MExt (lam D N A) z := by
      simp [LFE_M, charFlowZ]
    rw [e] at hb
    refine (LFE_ntr_le _).trans ((LFE_op_mul _ _).trans ?_)
    have := LFE_opNorm_Ea D N x
    have := LFE_op_nonneg (MExt (lam D N A) z)
    nlinarith
  have hmterm : ‖m s + (h : ℂ) * ((1 / 2 : ℂ) * m s) - m (s + h)‖ ≤ h ^ 2 := by
    rw [hmr s hs1, hmr (s + h) (by linarith)]
    set m₀ := ntr (MExt (lam D N A) z * Ea D N x)
    have e : ((Real.exp (s / 2) : ℝ) : ℂ) * m₀ + (h : ℂ) * ((1 / 2 : ℂ) *
        (((Real.exp (s / 2) : ℝ) : ℂ) * m₀)) - ((Real.exp ((s + h) / 2) : ℝ) : ℂ) * m₀ =
        ((Real.exp (s / 2) * (1 + h / 2 - Real.exp (h / 2)) : ℝ) : ℂ) * m₀ := by
      have : Real.exp ((s + h) / 2) = Real.exp (s / 2) * Real.exp (h / 2) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : |1 + h / 2 - Real.exp (h / 2)| ≤ (h / 2) ^ 2 := by
      have := Real.abs_exp_sub_one_sub_id_le (show |h / 2| ≤ 1 by
        rw [abs_of_pos (by linarith)]; linarith)
      have e : 1 + h / 2 - Real.exp (h / 2) = -(Real.exp (h / 2) - 1 - h / 2) := by ring
      rw [e, abs_neg]
      exact this
    have h2 : Real.exp (s / 2) ≤ 2 := by
      have : Real.exp (s / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
      have h3 : Real.exp (1 / 2) ≤ 2 := by
        have := Real.exp_one_lt_d9
        have h4 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
          rw [sq, ← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
      linarith
    have h5 := norm_nonneg m₀
    have h6 : 0 ≤ |1 + h / 2 - Real.exp (h / 2)| := abs_nonneg _
    calc Real.exp (s / 2) * |1 + h / 2 - Real.exp (h / 2)| * ‖m₀‖
        ≤ 2 * (h / 2) ^ 2 * (5 / 4) := by
          gcongr
      _ ≤ h ^ 2 := by nlinarith
  -- assembly
  have hkey : LFE_v μ₀ (lam D N A) z (s + h) x - LFE_v μ₀ (lam D N A) z s x -
      (h : ℂ) * ((1 / 2 : ℂ) * LFE_v μ₀ (lam D N A) z s x +
        (∑ a, LFE_v μ₀ (lam D N A) z s a * flowKmat (lam D N A) θ z z s a x) +
        LFE_e μ₀ (lam D N A) θ z s x) =
      ((∫ H, inner H ∂μs) - ∫ H, expl H ∂μs) +
        (m s + (h : ℂ) * ((1 / 2 : ℂ) * m s) - m (s + h)) := by
    rw [hv1, hstep, hexplv]
    simp only [hm]
    ring
  rw [hkey]
  have hN15 : 1 ≤ (N : ℝ) ^ 15 := one_le_pow₀ (by linarith)
  calc ‖((∫ H, inner H ∂μs) - ∫ H, expl H ∂μs) +
        (m s + (h : ℂ) * ((1 / 2 : ℂ) * m s) - m (s + h))‖
      ≤ K0 * (N : ℝ) ^ 15 * h ^ 2 + h ^ 2 := (norm_add_le _ _).trans (add_le_add hdiff hmterm)
    _ ≤ (K0 + 1) * (N : ℝ) ^ 15 * h ^ 2 := by nlinarith [sq_nonneg h]

/-- `η_s ≤ 2 (t_c - t_s) Im m_s` along the flow when `t_c - t₀ ≤ 1`: `η_s / Im m_s = e^{q_s} - 1`
with `q_s = t_c - t_s ∈ (0, 1]` ((3.14) [t_eta]). -/
private lemma LFE_eta_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (hq1 : flowTc (lam D N A) z ≤ 1) (s : ℝ) (hs0 : 0 ≤ s)
    (hsS : s ≤ S) :
    (charFlowZ (lam D N A) z s).im ≤
      2 * (flowTc (lam D N A) z - s) * flowIm (lam D N A) z s := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  obtain ⟨-, hιeq, hι0, -, -, -, -⟩ := LFE_flow D N hD hN A hA z hz S hS s hs0 hsS
  have hιs : 0 < flowIm (lam D N A) z s := by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
  have hteta := charFlow_teta (lam D N A) (lam_isHermitian D N A) z hz s
    (lt_of_le_of_lt hsS hS)
  have e1 : (charFlowZ (lam D N A) z s).im / flowIm (lam D N A) z s =
      Real.exp (flowTc (lam D N A) z - s) - 1 := hteta
  set x := flowTc (lam D N A) z - s with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have hx1 : x ≤ 1 := by rw [hx]; linarith
  have h1 : Real.exp x - 1 ≤ 2 * x := by
    have := Real.abs_exp_sub_one_sub_id_le (show |x| ≤ 1 by rw [abs_of_nonneg hx0]; exact hx1)
    have h2 := (abs_le.1 this).2
    nlinarith
  rw [div_eq_iff hιs.ne'] at e1
  rw [e1]
  exact mul_le_mul_of_nonneg_right h1 hιs.le

/-- From high probability to expectation: if `|f| ≤ b` off a set of probability at most `p` and
`|f| ≤ M` almost surely, then `|E f| ≤ b + M p`. -/
private lemma LFE_expect_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℂ) (hf : AEStronglyMeasurable f μ) (Bad : Set Ω)
    (p b M : ℝ) (hp : 0 ≤ p) (hb : 0 ≤ b) (hM : 0 ≤ M) (hBad : μ Bad ≤ ENNReal.ofReal p)
    (hgood : ∀ᵐ ω ∂μ, ω ∉ Bad → ‖f ω‖ ≤ b) (hall : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ M) :
    ‖∫ ω, f ω ∂μ‖ ≤ b + M * p := by
  set T := toMeasurable μ Bad with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hTμ : μ T = μ Bad := measure_toMeasurable _
  have hint : Integrable f μ := Integrable.of_bound hf M hall
  have hg : Integrable (fun ω => b + T.indicator (fun _ => M) ω) μ :=
    (integrable_const b).add ((integrable_const M).indicator hTm)
  have hpt : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ b + T.indicator (fun _ => M) ω := by
    filter_upwards [hgood, hall] with ω h1 h2
    by_cases h : ω ∈ T
    · rw [Set.indicator_of_mem h]
      linarith
    · rw [Set.indicator_of_notMem h]
      have : ω ∉ Bad := fun h' => h (subset_toMeasurable μ Bad h')
      linarith [h1 this]
  have hreal : μ.real T ≤ p := by
    rw [Measure.real, hTμ]
    exact ENNReal.toReal_le_of_le_ofReal hp hBad
  calc ‖∫ ω, f ω ∂μ‖ ≤ ∫ ω, ‖f ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (b + T.indicator (fun _ => M) ω) ∂μ := integral_mono_ae hint.norm hg hpt
    _ = b + M * μ.real T := by
      rw [integral_add (integrable_const b) ((integrable_const M).indicator hTm),
        integral_const, integral_indicator_const _ hTm]
      simp [smul_eq_mul, mul_comm]
    _ ≤ b + M * p := by nlinarith

/-- An entry is bounded by the Hilbert–Schmidt norm. -/
private lemma LFE_hs_entry {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) (a b : Fin D) :
    ‖M a b‖ ≤ hsNorm M := by
  unfold hsNorm
  rw [← Real.sqrt_sq (norm_nonneg (M a b))]
  apply Real.sqrt_le_sqrt
  calc ‖M a b‖ ^ 2 ≤ ∑ j, ‖M a j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖M a j‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ b)
    _ ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ a)

/-- The grid states are measurable. -/
private lemma LFE_state_meas (D N K : ℕ) (h : ℝ) (k : ℕ) :
    Measurable fun ω : GridΩA D N K => gridStateA D N K h ω k :=
  (gridStateA_adapted D N K h k).mono ((gridFiltrA_mono D N K).2 k) le_rfl

/-- The source term is a measurable function of the state. -/
private lemma LFE_f_meas {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z : ℂ) (s : ℝ)
    (x : Fin D) : Measurable fun H => LFE_f Λ θ z s H x := by
  have e : (fun H => LFE_f Λ θ z s H x) = fun H =>
      (fun G : Matrix (Idx D N) (Idx D N) ℂ => ∑ a, ntr ((G - LFE_M Λ z s) * Ea D N a) *
        ((D : ℂ) * ntr (G * Ea D N a * G * Ea D N x) - flowKmat Λ θ z z s a x))
        (LFE_G Λ z s H) := by
    funext H; rfl
  rw [e]
  have hφ : Continuous fun G : Matrix (Idx D N) (Idx D N) ℂ => ∑ a, ntr ((G - LFE_M Λ z s) *
      Ea D N a) * ((D : ℂ) * ntr (G * Ea D N a * G * Ea D N x) - flowKmat Λ θ z z s a x) := by
    refine continuous_finsetSum _ fun a _ => ?_
    exact (LFE_ntr_cont.comp ((continuous_id.sub continuous_const).matrix_mul
      continuous_const)).mul ((continuous_const.mul (LFE_ntr_cont.comp
        (((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id).matrix_mul
          continuous_const))).sub continuous_const)
  exact LFE_res_meas _ _ _ hφ

set_option maxHeartbeats 1600000 in
-- The arithmetic conditions on `N` and the two exceptional sets are handled together.
/-- The source of the one-loop equation of Lemma 3.10 [lem_flow_1.5]: at every time `s ≤ S`,
`|E Σ_a ⟨(G_s - M_s) E_a⟩ (L_s - K_s)_{ax}| ≤ D N^{2τ₁} N^{ε_g} / (N² q_s³ (Im m_s)³) +
12 D² N³ N^{-10}`, from (3.27) [flow_1_result_2] (`flowL2_grid_paper`) for `(z, z)` and the
averaged local law (2.23) [eq:aver_local] (`flowGood_grid`) on one grid with horizon `s`. -/
private lemma LFE_src (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ₁ : ℝ, 0 < τ₁ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ s : ℝ, 0 ≤ s → s ≤ S → ∀ x : Fin D,
        ‖LFE_e μ₀ (lam D N A) θ z s x‖ ≤
          D * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁ * (N : ℝ) ^ εg /
            (N ^ 2 * (flowTc (lam D N A) z - s) ^ 3 * flowIm (lam D N A) z s ^ 3)) +
          12 * (D : ℝ) ^ 2 * (N : ℝ) ^ 3 * (N : ℝ) ^ (-(10 : ℝ)) := by
  intro τ₁ hτ₁
  obtain ⟨Ng, hNg⟩ := flowGood_grid D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    τ₁ hτ₁ 10 (by norm_num) 42 (by norm_num)
  obtain ⟨Nl, hNl⟩ := flowL2_grid_paper D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    τ₁ hτ₁ 10 (by norm_num) 42 (by norm_num)
  have hev : ∀ᶠ N : ℕ in Filter.atTop, Ng ≤ N ∧ Nl ≤ N ∧ 2 ≤ N ∧
      2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧ c * (N : ℝ) ^ (-εg) ≤ 1 := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    exact (Filter.eventually_ge_atTop Ng).and ((Filter.eventually_ge_atTop Nl).and
      ((Filter.eventually_ge_atTop 2).and
      (((t1.const_mul 2).eventually (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and
      ((t2.const_mul c).eventually (Iic_mem_nhds (by simp : c * 0 < 1))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ₀ hμ₀ A z S hadm s hs0 hsS x => ?_⟩
  obtain ⟨hNg', hNl', hN2, hAN, hcN⟩ := hN₀ N hN
  have := hμ₀.prob
  have : NeZero D := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hD1r : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  obtain ⟨hΛ10, -, hz, -, hq0, hq1, hS0, hSt, hη⟩ :=
    LFE_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  have hadms := LFE_adm_mono D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
    s hs0 hsS
  have hs1 : s < flowTc (lam D N A) z := lt_of_le_of_lt hsS hSt
  obtain ⟨hηs0, hιeq, hι0, hιs1, -, -, hqι⟩ := LFE_flow D N hD1 hN1 A hΛ10 z hz S hSt s hs0 hsS
  have hιs : 0 < flowIm (lam D N A) z s := by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
  have hqs : 0 < flowTc (lam D N A) z - s := by linarith
  have hηN := (hη s hs0 hsS).1
  have hηinv : (charFlowZ (lam D N A) z s).im⁻¹ ≤ N := by
    rw [inv_le_comm₀ hηs0 hNpos]; exact hηN.le
  have hqinv : (flowTc (lam D N A) z - s)⁻¹ ≤ 2 * N := by
    have hle := LFE_eta_le D N hD1 hN1 A hΛ10 z hz S hSt hq1 s hs0 hsS
    rw [inv_le_comm₀ hqs (by positivity)]
    have h1 : (2 * (N : ℝ))⁻¹ < (charFlowZ (lam D N A) z s).im / 2 := by
      rw [mul_inv]; linarith [inv_pos.2 (show (0 : ℝ) < 2 by norm_num)]
    have h2 : (charFlowZ (lam D N A) z s).im / 2 ≤ flowTc (lam D N A) z - s := by
      have : (charFlowZ (lam D N A) z s).im ≤ 2 * (flowTc (lam D N A) z - s) := by nlinarith
      linarith
    linarith
  -- the grid with horizon `s`
  set K : ℕ := ⌈(N : ℝ) ^ (42 : ℝ)⌉₊ with hKdef
  have hK1 : (N : ℝ) ^ (42 : ℝ) ≤ K := Nat.le_ceil _
  have hK2 : (K : ℝ) ≤ (N : ℝ) ^ ((42 : ℝ) + 1) := by
    have h1 : (K : ℝ) < (N : ℝ) ^ (42 : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (N : ℝ) ^ ((42 : ℝ) + 1) = (N : ℝ) ^ (42 : ℝ) * N := by
      rw [Real.rpow_add hNpos, Real.rpow_one]
    have h3 : 1 ≤ (N : ℝ) ^ (42 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rw [h2]; nlinarith
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) hK1
  have hKs : (K : ℝ) * (s / K) = s := by field_simp
  have hlaw := gridStateA_law D N K μ₀ (s / K) (div_nonneg hs0 hKpos.le) K le_rfl
  rw [hKs] at hlaw
  have hcls : LLClass D N _ _ (blockOULaw D N μ₀ s) :=
    (Classical.choose_spec (llClass_blockOU D C)) N θ μ₀ s hθ0 hθ1 hs0 hμ₀
  have hherm : ∀ᵐ ω ∂(gridLawA D N K μ₀),
      (Matrix.of (gridStateA D N K (s / K) ω K)).IsHermitian := by
    have h := hcls.herm
    rw [← hlaw] at h
    exact (ae_map_iff (LFE_state_meas D N K _ K).aemeasurable LFE_herm_meas).1 h
  have hint : LFE_e μ₀ (lam D N A) θ z s x =
      ∫ ω, LFE_f (lam D N A) θ z s (gridStateA D N K (s / K) ω K) x ∂(gridLawA D N K μ₀) := by
    change ∫ H, LFE_f (lam D N A) θ z s H x ∂(blockOULaw D N μ₀ s) = _
    rw [← hlaw, integral_map (LFE_state_meas D N K _ K).aemeasurable
      (LFE_f_meas _ θ z s x).aestronglyMeasurable]
  rw [hint]
  -- the two exceptional sets
  have hBg := hNg N hNg' θ hθ0 hθ1 μ₀ hμ₀ A z s hadms K (by exact_mod_cast hKpos)
    (by simpa using hK2)
  have hBl := hNl N hNl' θ hθ0 hθ1 μ₀ hμ₀ A z s hadms K hK1 hK2 z z (Or.inl rfl) (Or.inl rfl)
  set Bad := {ω : GridΩA D N K | ∃ k : ℕ, k ≤ K ∧
      ¬ flowGoodAt A z τ₁ (k * (s / K)) (gridStateA D N K (s / K) ω k)} ∪
    {ω : GridΩA D N K | ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ₁ * ((N : ℝ) ^ εg /
        (N * (flowTc (lam D N A) z - k * (s / K)) ^ 2 *
          flowIm (lam D N A) z (k * (s / K)) ^ 2)) <
      hsNorm (flowLmat (lam D N A) z z (k * (s / K)) (gridStateA D N K (s / K) ω k) -
        flowKmat (lam D N A) θ z z (k * (s / K)))} with hBad
  have hBadμ : gridLawA D N K μ₀ Bad ≤ ENNReal.ofReal (2 * (N : ℝ) ^ (-(10 : ℝ))) := by
    refine (measure_union_le _ _).trans ((add_le_add hBg hBl).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the bounds at Hermitian states
  have hbdH : ∀ H : Idx D N → Idx D N → ℂ, (Matrix.of H).IsHermitian → ∀ a : Fin D,
      ‖LFE_d (lam D N A) z s H a‖ ≤ 2 * N ∧
        ‖flowLmat (lam D N A) z z s H a x - flowKmat (lam D N A) θ z z s a x‖ ≤
          3 * D * (N : ℝ) ^ 2 := by
    intro H hH a
    obtain ⟨-, -, h1, -, h3⟩ := LFE_res_bds D N hD1 hN1 A hΛ10 z hz s hs1 hs0 H hH a x
    have hK := LFE_K_le D N A z hz θ hθ0 hθ1 s hs0 hs1 a x
    refine ⟨by linarith, (norm_sub_le _ _).trans ?_⟩
    have h4 : (D : ℝ) * ((charFlowZ (lam D N A) z s).im⁻¹) ^ 2 ≤ D * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 hηs0.le) hηinv 2)
        (Nat.cast_nonneg _)
    have h5 : 2 * (N : ℝ) ≤ 2 * D * (N : ℝ) ^ 2 := by nlinarith
    linarith
  have hall : ∀ᵐ ω ∂(gridLawA D N K μ₀),
      ‖LFE_f (lam D N A) θ z s (gridStateA D N K (s / K) ω K) x‖ ≤ 6 * (D : ℝ) ^ 2 * N ^ 3 := by
    filter_upwards [hherm] with ω hω
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖LFE_d (lam D N A) z s (gridStateA D N K (s / K) ω K) a *
          (flowLmat (lam D N A) z z s (gridStateA D N K (s / K) ω K) a x -
            flowKmat (lam D N A) θ z z s a x)‖
        ≤ ∑ _a : Fin D, 2 * (N : ℝ) * (3 * D * (N : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul]
          exact mul_le_mul (hbdH _ hω a).1 (hbdH _ hω a).2 (norm_nonneg _) (by positivity)
      _ = 6 * (D : ℝ) ^ 2 * N ^ 3 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hgood : ∀ᵐ ω ∂(gridLawA D N K μ₀), ω ∉ Bad →
      ‖LFE_f (lam D N A) θ z s (gridStateA D N K (s / K) ω K) x‖ ≤
        D * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁ * (N : ℝ) ^ εg /
          (N ^ 2 * (flowTc (lam D N A) z - s) ^ 3 * flowIm (lam D N A) z s ^ 3)) := by
    filter_upwards [hherm] with ω hω hnb
    simp only [hBad, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and,
      not_not, not_lt] at hnb
    obtain ⟨hg, hl⟩ := hnb
    have hg' := hg K le_rfl
    have hl' := hl K le_rfl
    rw [hKs] at hg' hl'
    set H := gridStateA D N K (s / K) ω K with hH
    set X := (N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁ * (N : ℝ) ^ εg /
      (N ^ 2 * (flowTc (lam D N A) z - s) ^ 3 * flowIm (lam D N A) z s ^ 3) with hX
    have hterm : ∀ a : Fin D, ‖LFE_d (lam D N A) z s H a *
        (flowLmat (lam D N A) z z s H a x - flowKmat (lam D N A) θ z z s a x)‖ ≤ X := by
      intro a
      rw [norm_mul]
      have h1 : ‖LFE_d (lam D N A) z s H a‖ ≤
          (N : ℝ) ^ τ₁ / (N * (charFlowZ (lam D N A) z s).im) := hg'.1 a
      have h2 : ‖flowLmat (lam D N A) z z s H a x - flowKmat (lam D N A) θ z z s a x‖ ≤
          (N : ℝ) ^ τ₁ * ((N : ℝ) ^ εg / (N * (flowTc (lam D N A) z - s) ^ 2 *
            flowIm (lam D N A) z s ^ 2)) :=
        (LFE_hs_entry _ a x).trans hl'
      refine (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans ?_
      set q := flowTc (lam D N A) z - s with hq
      set ι := flowIm (lam D N A) z s with hι
      set η := (charFlowZ (lam D N A) z s).im with hηd
      set P := (N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁ * (N : ℝ) ^ εg with hP
      have e1 : (N : ℝ) ^ τ₁ / (N * η) * ((N : ℝ) ^ τ₁ * ((N : ℝ) ^ εg / (N * q ^ 2 * ι ^ 2))) =
          P / ((N * η) * (N * q ^ 2 * ι ^ 2)) := by
        rw [hP]; field_simp
      rw [e1, hX]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      have : (N : ℝ) ^ 2 * q ^ 3 * ι ^ 3 = (N * (q * ι)) * (N * q ^ 2 * ι ^ 2) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqι hNpos.le) (by positivity)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖LFE_d (lam D N A) z s H a *
          (flowLmat (lam D N A) z z s H a x - flowKmat (lam D N A) θ z z s a x)‖
        ≤ ∑ _a : Fin D, X := Finset.sum_le_sum fun a _ => hterm a
      _ = D * X := by simp
  have hf := (LFE_f_meas (lam D N A) θ z s x).comp (LFE_state_meas D N K (s / K) K)
  refine (LFE_expect_le _ _ hf.aestronglyMeasurable Bad _ _ _ (by positivity) (by positivity)
    (by positivity) hBadμ hgood hall).trans (le_of_eq ?_)
  ring

/-- `‖w‖₂ ≤ Σ_x |w_x|`. -/
private lemma LFE_l2_le {D : ℕ} (w : EuclideanSpace ℂ (Fin D)) : ‖w‖ ≤ ∑ x, ‖w x‖ := by
  rw [EuclideanSpace.norm_eq]
  have h0 : 0 ≤ ∑ x, ‖w x‖ := Finset.sum_nonneg fun x _ => norm_nonneg _
  rw [← Real.sqrt_sq h0]
  exact Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun x _ => norm_nonneg _)

/-- The operator bound behind (3.67) [Tnorm] for one resolvent along the flow, in the form of one
Euler step: with `q_s = t_c - t₀ - s` and `K_s = K_{θ_s}(z_s, z_s)`,
`‖v + h (v/2 + K_sᵀ v)‖₂ ≤ (1 + h/q_s + h/2) ‖v‖₂` (`tOp1_norm_le` at the flowed point). -/
private lemma LFE_T1 (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (s : ℝ) (hs0 : 0 ≤ s)
    (hs : s < flowTc (lam D N A) z) (h : ℝ) (hh : 0 ≤ h) (v : Fin D → ℂ) :
    ‖(WithLp.toLp 2 (fun x => v x + (h : ℂ) * ((1 / 2 : ℂ) * v x +
        ∑ a, v a * flowKmat (lam D N A) θ z z s a x)) : EuclideanSpace ℂ (Fin D))‖ ≤
      (1 + h / (flowTc (lam D N A) z - s) + h / 2) *
        ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin D))‖ := by
  have hΛ := lam_isHermitian D N A
  have hηs := (charFlow_M _ hΛ z hz s hs).1
  have he0 : 0 < Real.exp (-s) := Real.exp_pos _
  have he1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hθ0' : 0 ≤ Real.exp (-s) * θ + 1 - Real.exp (-s) := by nlinarith
  have hθ1' : Real.exp (-s) * θ + 1 - Real.exp (-s) ≤ 1 := by nlinarith
  have hT := tOp1_norm_le D N (((Real.exp (-s / 2) : ℝ) : ℂ) • A) (charFlowZ (lam D N A) z s)
    hηs _ hθ0' hθ1' _ (Or.inl rfl) v
  have hlam : lam D N (((Real.exp (-s / 2) : ℝ) : ℂ) • A) =
      ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A := (LFE_lam_smul D N A _).symm
  rw [hlam, flowTc_flow _ hΛ z hz s hs] at hT
  set q := flowTc (lam D N A) z - s with hq
  have hqpos : 0 < q := by rw [hq]; linarith
  set K := flowKmat (lam D N A) θ z z s with hK
  set u : EuclideanSpace ℂ (Fin D) := WithLp.toLp 2 (fun x => (q : ℂ) * (∑ a, K a x * v a) -
    (1 / 2 : ℂ) * ((1 - q : ℝ) : ℂ) * v x) with hu
  have hun : ‖u‖ ≤ (1 + q) / 2 * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin D))‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    exact hT
  have e : (WithLp.toLp 2 (fun x => v x + (h : ℂ) * ((1 / 2 : ℂ) * v x +
      ∑ a, v a * K a x)) : EuclideanSpace ℂ (Fin D)) =
      ((1 + h / (2 * q) : ℝ) : ℂ) • (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin D)) +
        ((h / q : ℝ) : ℂ) • u := by
    ext x
    simp only [hu, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
    have hs : ∑ a, v a * K a x = ∑ a, K a x * v a :=
      Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [hs]
    push_cast
    field_simp
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg
    (by positivity), Real.norm_of_nonneg (by positivity)]
  have hv0 := norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin D))
  have h1 := mul_le_mul_of_nonneg_left hun (by positivity : (0 : ℝ) ≤ h / q)
  have e2 : (1 + h / (2 * q)) * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin D))‖ +
      h / q * ((1 + q) / 2 * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin D))‖) =
      (1 + h / q + h / 2) * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin D))‖ := by
    field_simp; ring
  linarith

/-- A discrete Grönwall bound: if `a_{k+1} ≤ (1 + h/q_k + h/2) a_k + β_k` with `q_k = q₀ - k h`,
`a, β ≥ 0`, then `q_K a_K ≤ e^{K h/2} (q₀ a₀ + Σ_{k<K} q_{k+1} β_k)`. -/
private lemma LFE_gron (K : ℕ) (h q₀ : ℝ) (hh : 0 < h) (hK : (K : ℝ) * h < q₀) (a β : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hβ : ∀ k, k < K → 0 ≤ β k)
    (hrec : ∀ k, k < K → a (k + 1) ≤ (1 + h / (q₀ - k * h) + h / 2) * a k + β k) :
    (q₀ - K * h) * a K ≤ Real.exp (K * h / 2) *
      (q₀ * a 0 + ∑ k ∈ Finset.range K, (q₀ - (k + 1) * h) * β k) := by
  have claim : ∀ n, n ≤ K → (q₀ - n * h) * Real.exp (-(n * h / 2)) * a n ≤
      q₀ * a 0 + ∑ k ∈ Finset.range n, (q₀ - (k + 1) * h) * β k := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hn' : n ≤ K := by omega
      have IH := ih hn'
      have hnK : ((n : ℝ) + 1) * h ≤ K * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh.le
      set qn := q₀ - n * h with hqn
      have hqn1 : 0 < qn - h := by rw [hqn]; nlinarith
      have hqnpos : 0 < qn := by linarith
      have e1 : q₀ - ((n + 1 : ℕ) : ℝ) * h = qn - h := by rw [hqn]; push_cast; ring
      have hexp1 : Real.exp (-(((n + 1 : ℕ) : ℝ) * h / 2)) * Real.exp (h / 2) =
          Real.exp (-((n : ℝ) * h / 2)) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have hexp2 : Real.exp (-(((n + 1 : ℕ) : ℝ) * h / 2)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * h := by positivity
                                  linarith)
      have hfac : (qn - h) * (1 + h / qn + h / 2) ≤ qn * Real.exp (h / 2) := by
        have e2 : (qn - h) * (1 + h / qn + h / 2) = qn * (1 + h / 2) - h ^ 2 / qn - h ^ 2 / 2 := by
          field_simp; ring
        rw [e2]
        have h3 : 1 + h / 2 ≤ Real.exp (h / 2) := by linarith [Real.add_one_le_exp (h / 2)]
        have h4 : 0 ≤ h ^ 2 / qn := by positivity
        nlinarith
      have hr := hrec n (by omega)
      rw [e1, Finset.sum_range_succ]
      have hE := Real.exp_pos (-(((n + 1 : ℕ) : ℝ) * h / 2))
      calc (qn - h) * Real.exp (-(((n + 1 : ℕ) : ℝ) * h / 2)) * a (n + 1)
          ≤ (qn - h) * Real.exp (-(((n + 1 : ℕ) : ℝ) * h / 2)) *
              ((1 + h / qn + h / 2) * a n + β n) :=
            mul_le_mul_of_nonneg_left hr (by positivity)
        _ = ((qn - h) * (1 + h / qn + h / 2)) * Real.exp (-(((n + 1 : ℕ) : ℝ) * h / 2)) * a n +
              (qn - h) * Real.exp (-(((n + 1 : ℕ) : ℝ) * h / 2)) * β n := by ring
        _ ≤ (qn * Real.exp (h / 2)) * Real.exp (-(((n + 1 : ℕ) : ℝ) * h / 2)) * a n +
              (qn - h) * 1 * β n := by
            gcongr
            · exact ha n
            · exact hβ n (by omega)
        _ = qn * Real.exp (-((n : ℝ) * h / 2)) * a n + (qn - h) * β n := by
            rw [mul_assoc qn, mul_comm (Real.exp (h / 2)), hexp1]; ring
        _ ≤ q₀ * a 0 + (∑ k ∈ Finset.range n, (q₀ - (k + 1) * h) * β k) + (qn - h) * β n := by
            linarith
        _ = _ := by rw [hqn]; ring
  have hc := claim K le_rfl
  have hE : Real.exp (K * h / 2) * Real.exp (-(K * h / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc (q₀ - K * h) * a K = Real.exp (K * h / 2) *
        ((q₀ - K * h) * Real.exp (-(K * h / 2)) * a K) := by
        rw [← mul_assoc, ← mul_assoc, mul_comm (Real.exp _) (q₀ - _), mul_assoc (q₀ - _),
          hE, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le

/-- `Σ_{k<K} h / q_k² ≤ 1 / q_K` for `q_k = q₀ - k h > 0`. -/
private lemma LFE_tele (K : ℕ) (h q₀ : ℝ) (hh : 0 < h) (hK : (K : ℝ) * h < q₀) :
    ∑ k ∈ Finset.range K, h / (q₀ - k * h) ^ 2 ≤ 1 / (q₀ - K * h) := by
  have claim : ∀ n, n ≤ K → ∑ k ∈ Finset.range n, h / (q₀ - k * h) ^ 2 ≤
      1 / (q₀ - n * h) - 1 / q₀ := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have IH := ih (by omega)
      have hnK : ((n : ℝ) + 1) * h ≤ K * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh.le
      have h1 : 0 < q₀ - ((n : ℝ) + 1) * h := by linarith
      have h2 : 0 < q₀ - (n : ℝ) * h := by nlinarith
      rw [Finset.sum_range_succ]
      have hstep : h / (q₀ - n * h) ^ 2 ≤ 1 / (q₀ - ((n : ℝ) + 1) * h) - 1 / (q₀ - n * h) := by
        rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
        have : (1 * (q₀ - ↑n * h) - (q₀ - (↑n + 1) * h) * 1) = h := by ring
        rw [this]
        have hle : (q₀ - ((n : ℝ) + 1) * h) * (q₀ - n * h) ≤ (q₀ - n * h) ^ 2 := by nlinarith
        nlinarith
      push_cast
      linarith
  have hK0 : 0 < q₀ := lt_of_le_of_lt (by positivity) hK
  have := claim K le_rfl
  have : 0 < 1 / q₀ := by positivity
  linarith

/-- The block-OU law at time `0` is the starting law. -/
private lemma LFE_bOU0 (D N : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] : blockOULaw D N μ₀ 0 = μ₀ := by
  unfold blockOULaw
  have e : (fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
      Real.exp (-(0 : ℝ) / 2) • p.1 + Real.sqrt (1 - Real.exp (-(0 : ℝ))) •
        Matrix.of.symm (blockH D N p.2)) = Prod.fst := by
    funext p
    simp
  rw [e, Measure.map_fst_prod, measure_univ, one_smul]

/-- At time `0`, `E⟨(G_0 - M_0) E_b⟩` is the expectation at the starting law. -/
private lemma LFE_v0 {D N : ℕ} (μ₀ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ₀]
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (b : Fin D) :
    LFE_v μ₀ Λ z 0 b = ∫ H, ntr ((res (Matrix.of H + Λ) z - MExt Λ z) * Ea D N b) ∂μ₀ := by
  have hz : charFlowZ Λ z 0 = z := by simp [charFlowZ]
  have he : ((Real.exp (-0 / 2) : ℝ) : ℂ) • Λ = Λ := by simp
  simp only [LFE_v, LFE_d, LFE_G, LFE_M, hz, he, LFE_bOU0]

/-- The sum of the Grönwall bound: with `q_k = q₀ - k h`, `ι_k ≥ ι₀ > 0`, `q₀ ≤ 1`,
`Σ_{k<K} q_{k+1} (h D (D P/(N² q_k³ ι_k³) + Y) + R) ≤ D² P/(N² ι₀³ q_K) + K h D Y + K R`. -/
private lemma LFE_sumbd (K : ℕ) (h q₀ ι₀ P N D Y R : ℝ) (ι : ℕ → ℝ) (hh : 0 < h)
    (hK : (K : ℝ) * h < q₀) (hq1 : q₀ ≤ 1) (hι₀ : 0 < ι₀) (hι : ∀ k, k < K → ι₀ ≤ ι k) (hP : 0 ≤ P)
    (hN : 0 < N) (hD : 0 ≤ D) (hY : 0 ≤ Y) (hR : 0 ≤ R) :
    ∑ k ∈ Finset.range K, (q₀ - (k + 1) * h) *
        (h * (D * (D * (P / (N ^ 2 * (q₀ - k * h) ^ 3 * ι k ^ 3)) + Y)) + R) ≤
      D ^ 2 * P / (N ^ 2 * ι₀ ^ 3) * (1 / (q₀ - K * h)) + K * h * D * Y + K * R := by
  have hterm : ∀ k ∈ Finset.range K, (q₀ - (k + 1) * h) *
      (h * (D * (D * (P / (N ^ 2 * (q₀ - k * h) ^ 3 * ι k ^ 3)) + Y)) + R) ≤
      D ^ 2 * P / (N ^ 2 * ι₀ ^ 3) * (h / (q₀ - k * h) ^ 2) + h * D * Y + R := by
    intro k hk
    have hkK : (k : ℝ) + 1 ≤ K := by
      have := Finset.mem_range.1 hk; exact_mod_cast this
    have hkh : ((k : ℝ) + 1) * h ≤ K * h := mul_le_mul_of_nonneg_right hkK hh.le
    have hq1' : 0 < q₀ - ((k : ℝ) + 1) * h := by linarith
    have hq0' : 0 < q₀ - (k : ℝ) * h := by nlinarith
    have hqle : q₀ - ((k : ℝ) + 1) * h ≤ q₀ - k * h := by linarith
    have hqle1 : q₀ - ((k : ℝ) + 1) * h ≤ 1 := by
      have : (0 : ℝ) ≤ ((k : ℝ) + 1) * h := by positivity
      linarith
    have hιk' := hι k (Finset.mem_range.1 hk)
    have hιk : 0 < ι k := lt_of_lt_of_le hι₀ hιk'
    have hι3 : ι₀ ^ 3 ≤ ι k ^ 3 := pow_le_pow_left₀ hι₀.le hιk' 3
    set q := q₀ - (k : ℝ) * h with hqd
    set q' := q₀ - ((k : ℝ) + 1) * h with hq'd
    have t1 : q' * (h * (D * (D * (P / (N ^ 2 * q ^ 3 * ι k ^ 3))))) ≤
        D ^ 2 * P / (N ^ 2 * ι₀ ^ 3) * (h / q ^ 2) := by
      have e1 : q' * (h * (D * (D * (P / (N ^ 2 * q ^ 3 * ι k ^ 3))))) =
          (q' / q) * (D ^ 2 * P * h / (N ^ 2 * q ^ 2 * ι k ^ 3)) := by
        field_simp
      have e2 : D ^ 2 * P / (N ^ 2 * ι₀ ^ 3) * (h / q ^ 2) =
          1 * (D ^ 2 * P * h / (N ^ 2 * q ^ 2 * ι₀ ^ 3)) := by
        field_simp
      rw [e1, e2]
      apply mul_le_mul ((div_le_one hq0').2 hqle) _ (by positivity) zero_le_one
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hι3 (by positivity))
    have t2 : q' * (h * Y * D) ≤ h * D * Y := by
      have : 0 ≤ h * D * Y := by positivity
      nlinarith
    have t3 : q' * R ≤ R := by nlinarith
    have e3 : q' * (h * (D * (D * (P / (N ^ 2 * q ^ 3 * ι k ^ 3)) + Y)) + R) =
        q' * (h * (D * (D * (P / (N ^ 2 * q ^ 3 * ι k ^ 3))))) + q' * (h * Y * D) + q' * R := by
      ring
    rw [e3]
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have ht := LFE_tele K h q₀ hh hK
  have hc : 0 ≤ D ^ 2 * P / (N ^ 2 * ι₀ ^ 3) := by positivity
  have := mul_le_mul_of_nonneg_left ht hc
  nlinarith

set_option maxHeartbeats 1000000 in
/-- The final inequality for (3.30) [flow_1G_res]: from the Grönwall bound
`q_S a ≤ E (q₀ D sup + D² A Q/(N² ι₀³ q_S) + Z)`, `E = e^{S/2} ∈ [1, e^{1/2}]`, `ι_S = E ι₀ ≤ 1`,
`q_S ≤ 1`, `q_S⁻¹ ≤ 2N` and `Z ≤ C_z/N⁷`, the bound `a ≤ t (q₀/q_S sup + Q/(N² q_S² ι_S³))`. -/
private lemma LFE_ar5 (N qS q₀ ι₀ E sup a A Q Z Cz D t : ℝ) (hN : 2 ≤ N) (hqS : 0 < qS)
    (hq0 : 0 ≤ q₀) (hι0 : 0 < ι₀) (hE1 : 1 ≤ E) (hE : E ≤ Real.exp (1 / 2)) (hιS : E * ι₀ ≤ 1)
    (hqS1 : qS ≤ 1) (hsup : 0 ≤ sup) (hD : 0 ≤ D) (hQ : 1 ≤ Q) (hA : 0 ≤ A) (hZ0 : 0 ≤ Z)
    (hqinv : qS⁻¹ ≤ 2 * N) (hZ : Z ≤ Cz / N ^ 7)
    (ha : qS * a ≤ E * (q₀ * (D * sup) + D ^ 2 * (A * Q) / (N ^ 2 * ι₀ ^ 3) * (1 / qS) + Z))
    (hA1 : Real.exp (1 / 2) * D ≤ t) (hA2 : 2 * Real.exp (1 / 2) ^ 4 * D ^ 2 * A ≤ t)
    (hA3 : 4 * Real.exp (1 / 2) * Cz ≤ N) (ht1 : 1 ≤ t) :
    a ≤ t * (q₀ / qS * sup + Q / (N ^ 2 * qS ^ 2 * (E * ι₀) ^ 3)) := by
  set e2 := Real.exp (1 / 2) with he2
  have hNpos : 0 < N := by linarith
  have hE0 : 0 < E := by linarith
  set W := Q / (N ^ 2 * qS ^ 2 * (E * ι₀) ^ 3) with hW
  have hWpos : 0 < W := by positivity
  have ha' : a ≤ E * q₀ * D * sup / qS + E ^ 4 * D ^ 2 * A * W + E * Z / qS := by
    have e : E * (q₀ * (D * sup) + D ^ 2 * (A * Q) / (N ^ 2 * ι₀ ^ 3) * (1 / qS) + Z) / qS =
        E * q₀ * D * sup / qS + E ^ 4 * D ^ 2 * A * W + E * Z / qS := by
      rw [hW]; field_simp
    rw [← e, le_div_iff₀ hqS]
    linarith
  have t1 : E * q₀ * D * sup / qS ≤ t * (q₀ / qS * sup) := by
    have : E * q₀ * D * sup / qS = (E * D) * (q₀ / qS * sup) := by field_simp
    rw [this]
    have hED : E * D ≤ t := le_trans (mul_le_mul_of_nonneg_right hE hD) hA1
    exact mul_le_mul_of_nonneg_right hED (by positivity)
  have t2 : E ^ 4 * D ^ 2 * A * W ≤ t / 2 * W := by
    have hE4 : E ^ 4 ≤ e2 ^ 4 := pow_le_pow_left₀ hE0.le hE 4
    have : E ^ 4 * D ^ 2 * A ≤ t / 2 := by
      have : E ^ 4 * D ^ 2 * A ≤ e2 ^ 4 * D ^ 2 * A := by
        have : 0 ≤ D ^ 2 * A := by positivity
        nlinarith
      linarith
    exact mul_le_mul_of_nonneg_right this hWpos.le
  have t3 : E * Z / qS ≤ t / 2 * W := by
    have hW2 : 1 / N ^ 2 ≤ W := by
      rw [hW, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : qS ^ 2 ≤ 1 := by nlinarith
      have h2 : (E * ι₀) ^ 3 ≤ 1 := pow_le_one₀ (by positivity) hιS
      have h3 : qS ^ 2 * (E * ι₀) ^ 3 ≤ 1 := by
        have := mul_le_mul h1 h2 (by positivity) zero_le_one
        linarith
      have h4 : 0 ≤ N ^ 2 := by positivity
      nlinarith
    have hCz : 0 ≤ Cz := by
      have : 0 ≤ Z := hZ0
      have h5 : 0 ≤ Cz / N ^ 7 := this.trans hZ
      have : 0 < N ^ 7 := by positivity
      exact (div_nonneg_iff.1 h5).elim (fun h => h.1) (fun h => by linarith [h.2])
    have h6 : E * Z / qS ≤ e2 * (Cz / N ^ 7) * (2 * N) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (mul_le_mul hE hZ hZ0 (by positivity)) hqinv (inv_nonneg.2 hqS.le)
        (by positivity)
    have h7 : e2 * (Cz / N ^ 7) * (2 * N) ≤ 1 / (2 * N ^ 2) := by
      have e7 : e2 * (Cz / N ^ 7) * (2 * N) = (e2 * Cz * (2 * N)) / N ^ 7 := by ring
      rw [e7, div_le_div_iff₀ (by positivity) (by positivity)]
      have : N ^ 7 = N ^ 4 * N * N ^ 2 := by ring
      rw [this]
      have hN4 : N ≤ N ^ 4 := by
        calc N = N ^ 1 := (pow_one N).symm
          _ ≤ N ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have : 4 * e2 * Cz ≤ N ^ 4 := hA3.trans hN4
      have h8 : 0 ≤ N * N ^ 2 := by positivity
      nlinarith
    have h9 : 1 / (2 * N ^ 2) ≤ t / 2 * W := by
      have : 1 / (2 * N ^ 2) = (1 / 2) * (1 / N ^ 2) := by field_simp
      rw [this]
      have : (1 / 2 : ℝ) * W ≤ t / 2 * W := by nlinarith
      nlinarith
    linarith
  have : t / 2 * W + t / 2 * W = t * W := by ring
  calc a ≤ E * q₀ * D * sup / qS + E ^ 4 * D ^ 2 * A * W + E * Z / qS := ha'
    _ ≤ t * (q₀ / qS * sup) + t / 2 * W + t / 2 * W := by linarith
    _ = t * (q₀ / qS * sup + W) := by ring

set_option maxHeartbeats 3200000 in
-- The arithmetic conditions on `N`, the grid and the recursion are handled together.
/-- The statement of `flowG1_exp`, proved from the one-step expansion `LFE_step`, the source
bound `LFE_src`, the operator bound `LFE_T1` and the discrete Grönwall bound `LFE_gron`. -/
private lemma LFE_main (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ a : Fin D,
        ‖∫ H, ntr ((res (Matrix.of H + ((Real.exp (-S / 2) : ℝ) : ℂ) • lam D N A)
              (charFlowZ (lam D N A) z S) -
            MExt (((Real.exp (-S / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z S)) *
              Ea D N a) ∂(blockOULaw D N μ₀ S)‖ ≤
          (N : ℝ) ^ τ' * (flowTc (lam D N A) z / (flowTc (lam D N A) z - S) *
              (⨆ b : Fin D, ‖∫ H, ntr ((res (Matrix.of H + lam D N A) z - MExt (lam D N A) z) *
                Ea D N b) ∂μ₀‖) +
            (N : ℝ) ^ εg / ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - S) ^ 2 *
              flowIm (lam D N A) z S ^ 3)) := by
  intro τ' hτ'
  set τ₁ := τ' / 4 with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  obtain ⟨Kst, hKst0, hKst⟩ := LFE_step D (by omega) τ hτ C
  obtain ⟨Ns, hNs⟩ := LFE_src D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C τ₁ hτ₁0
  set e2 := Real.exp (1 / 2) with he2
  set Cz : ℝ := 12 * (D : ℝ) ^ 3 + D * Kst with hCz
  have hev : ∀ᶠ N : ℕ in Filter.atTop, Ns ≤ N ∧ 2 ≤ N ∧
      2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧ c * (N : ℝ) ^ (-εg) ≤ 1 ∧
      (e2 * D) * (N : ℝ) ^ (0 : ℝ) ≤ (N : ℝ) ^ τ' ∧
      (2 * e2 ^ 4 * (D : ℝ) ^ 2) * (N : ℝ) ^ (τ₁ + τ₁) ≤ (N : ℝ) ^ τ' ∧
      4 * e2 * Cz ≤ (N : ℝ) := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    exact (Filter.eventually_ge_atTop Ns).and ((Filter.eventually_ge_atTop 2).and
      (((t1.const_mul 2).eventually (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and
      (((t2.const_mul c).eventually (Iic_mem_nhds (by simp : c * 0 < 1))).and
      ((LFE_ev_pow _ _ _ hτ').and ((LFE_ev_pow _ _ _ (by linarith)).and
      ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (4 * e2 * Cz)))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ₀ hμ₀ A z S hadm a => ?_⟩
  obtain ⟨hNs', hN2, hAN, hcN, hA1, hA2, hA3⟩ := hN₀ N hN
  rw [Real.rpow_zero, mul_one] at hA1
  have := hμ₀.prob
  have : NeZero D := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have ht1 : 1 ≤ (N : ℝ) ^ τ' := Real.one_le_rpow (by linarith) hτ'.le
  obtain ⟨hΛ10, hzτ, hz, hm1, hq0, hq1, hS0, hSt, hη⟩ :=
    LFE_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  set q₀ := flowTc (lam D N A) z with hq₀
  set ι₀ := (mExt (lam D N A) z).im with hι₀
  set sup := ⨆ b : Fin D, ‖∫ H, ntr ((res (Matrix.of H + lam D N A) z - MExt (lam D N A) z) *
    Ea D N b) ∂μ₀‖ with hsup
  have hsup_ge : ∀ b, ‖LFE_v μ₀ (lam D N A) z 0 b‖ ≤ sup := fun b => by
    rw [LFE_v0, hsup]
    exact le_ciSup (f := fun b : Fin D => ‖∫ H, ntr ((res (Matrix.of H + lam D N A) z -
      MExt (lam D N A) z) * Ea D N b) ∂μ₀‖) (Finite.bddAbove_range _) b
  have hsup0 : 0 ≤ sup := (norm_nonneg _).trans (hsup_ge a)
  obtain ⟨-, hιS, hι0, hιS1, -, -, -⟩ := LFE_flow D N hD1 hN1 A hΛ10 z hz S hSt S hS0 le_rfl
  have hqS : 0 < q₀ - S := by linarith
  change ‖LFE_v μ₀ (lam D N A) z S a‖ ≤ (N : ℝ) ^ τ' * (q₀ / (q₀ - S) * sup +
    (N : ℝ) ^ εg / ((N : ℝ) ^ 2 * (q₀ - S) ^ 2 * flowIm (lam D N A) z S ^ 3))
  have hιSpos : 0 < flowIm (lam D N A) z S := by rw [hιS]; exact mul_pos (Real.exp_pos _) hι0
  have hT0 : 0 ≤ (N : ℝ) ^ εg / ((N : ℝ) ^ 2 * (q₀ - S) ^ 2 * flowIm (lam D N A) z S ^ 3) := by
    positivity
  rcases hS0.eq_or_lt with hS | hSpos
  · -- the horizon `S = 0`
    subst hS
    have e1 : q₀ / (q₀ - 0) = 1 := by rw [sub_zero]; exact div_self hq0.ne'
    rw [e1, one_mul]
    calc ‖LFE_v μ₀ (lam D N A) z 0 a‖ ≤ sup := hsup_ge a
      _ ≤ (N : ℝ) ^ τ' * sup := le_mul_of_one_le_left hsup0 ht1
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- the expectation grid with `K = ⌈N^{25}⌉` steps
  set K : ℕ := ⌈(N : ℝ) ^ (25 : ℕ)⌉₊ with hKdef
  have hK1 : (N : ℝ) ^ (25 : ℕ) ≤ K := Nat.le_ceil _
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) hK1
  set h := S / K with hhdef
  have hhpos : 0 < h := div_pos hSpos hKpos
  have hKh : (K : ℝ) * h = S := by rw [hhdef]; field_simp
  have hKq : (K : ℝ) * h < q₀ := by rw [hKh]; exact hSt
  have hKh2 : (K : ℝ) * h ^ 2 ≤ 1 / (N : ℝ) ^ 25 := by
    have e : (K : ℝ) * h ^ 2 = S * (S / K) := by rw [hhdef]; field_simp
    rw [e]
    have hS1 : S ≤ 1 := by linarith
    calc S * (S / K) ≤ 1 * (1 / K) := mul_le_mul hS1
          (div_le_div_of_nonneg_right hS1 hKpos.le) (by positivity) zero_le_one
      _ = 1 / K := one_mul _
      _ ≤ 1 / (N : ℝ) ^ 25 := one_div_le_one_div_of_le (by positivity) hK1
  -- the vectors `W_k = (u_x(k h))_x`
  set W : ℕ → EuclideanSpace ℂ (Fin D) := fun k =>
    WithLp.toLp 2 (fun x => LFE_v μ₀ (lam D N A) z (k * h) x) with hW
  set P := (N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁ * (N : ℝ) ^ εg with hP
  set Y := 12 * (D : ℝ) ^ 2 * (N : ℝ) ^ 3 * (N : ℝ) ^ (-(10 : ℝ)) with hY
  set R := D * Kst * (N : ℝ) ^ 15 * h ^ 2 with hR
  set β : ℕ → ℝ := fun k => h * (D * (D * (P / ((N : ℝ) ^ 2 * (q₀ - k * h) ^ 3 *
    flowIm (lam D N A) z (k * h) ^ 3)) + Y)) + R with hβ
  have hP0 : 0 ≤ P := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hR0 : 0 ≤ R := by positivity
  have hgrid : ∀ k : ℕ, k ≤ K → 0 ≤ (k : ℝ) * h ∧ (k : ℝ) * h ≤ S := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    rw [← hKh]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hhpos.le
  have hβ0 : ∀ k, k < K → 0 ≤ β k := by
    intro k hk
    obtain ⟨hk0, hkS⟩ := hgrid k hk.le
    obtain ⟨-, hιk, -, -, -, -, -⟩ := LFE_flow D N hD1 hN1 A hΛ10 z hz S hSt _ hk0 hkS
    have hqk : 0 < q₀ - k * h := by linarith
    have hιk0 : 0 < flowIm (lam D N A) z (k * h) := by
      rw [hιk]; exact mul_pos (Real.exp_pos _) hι0
    simp only [hβ]
    positivity
  -- one step of the recursion
  have hrec : ∀ k, k < K → ‖W (k + 1)‖ ≤ (1 + h / (q₀ - k * h) + h / 2) * ‖W k‖ + β k := by
    intro k hk
    obtain ⟨hk0, hkS⟩ := hgrid k hk.le
    have hk1 : ((k + 1 : ℕ) : ℝ) * h = k * h + h := by push_cast; ring
    have hsh : (k : ℝ) * h + h ≤ S := by rw [← hk1]; exact (hgrid (k + 1) hk).2
    have hks : (k : ℝ) * h < q₀ := lt_of_le_of_lt hkS hSt
    have hstep := hKst N hN2 θ hθ0 hθ1 μ₀ hμ₀ A z S hΛ10 hzτ hz hm1 hq1 hS0 hSt
      (fun s hs0 hsS => (hη s hs0 hsS).1) (k * h) h hk0 hhpos hsh
    have hsrc := hNs N hNs' θ hθ0 hθ1 μ₀ hμ₀ A z S hadm (k * h) hk0 hkS
    set v : Fin D → ℂ := fun x => LFE_v μ₀ (lam D N A) z (k * h) x with hv
    set Yv : EuclideanSpace ℂ (Fin D) := WithLp.toLp 2 (fun x => v x + (h : ℂ) *
      ((1 / 2 : ℂ) * v x + ∑ b, v b * flowKmat (lam D N A) θ z z (k * h) b x)) with hYv
    set Ev : EuclideanSpace ℂ (Fin D) :=
      WithLp.toLp 2 (fun x => LFE_e μ₀ (lam D N A) θ z (k * h) x) with hEv
    have hdec : W (k + 1) = Yv + (h : ℂ) • Ev + (W (k + 1) - Yv - (h : ℂ) • Ev) := by abel
    rw [hdec]
    have hY1 : ‖Yv‖ ≤ (1 + h / (q₀ - k * h) + h / 2) * ‖W k‖ :=
      LFE_T1 D N A z hz θ hθ0 hθ1 (k * h) hk0 hks h hhpos.le v
    have hE1 : ‖(h : ℂ) • Ev‖ ≤ h * (D * (D * (P / ((N : ℝ) ^ 2 * (q₀ - k * h) ^ 3 *
        flowIm (lam D N A) z (k * h) ^ 3)) + Y)) := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hhpos.le]
      refine mul_le_mul_of_nonneg_left ((LFE_l2_le Ev).trans ?_) hhpos.le
      calc ∑ x, ‖Ev x‖ ≤ ∑ _x : Fin D, (D * (P / ((N : ℝ) ^ 2 * (q₀ - k * h) ^ 3 *
            flowIm (lam D N A) z (k * h) ^ 3)) + Y) :=
            Finset.sum_le_sum fun x _ => hsrc x
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hR1 : ‖W (k + 1) - Yv - (h : ℂ) • Ev‖ ≤ R := by
      refine (LFE_l2_le _).trans ?_
      calc ∑ x, ‖(W (k + 1) - Yv - (h : ℂ) • Ev) x‖ ≤ ∑ _x : Fin D, Kst * (N : ℝ) ^ 15 * h ^ 2 := by
            refine Finset.sum_le_sum fun x _ => ?_
            have e : (W (k + 1) - Yv - (h : ℂ) • Ev) x =
                LFE_v μ₀ (lam D N A) z (k * h + h) x - LFE_v μ₀ (lam D N A) z (k * h) x -
                  (h : ℂ) * ((1 / 2 : ℂ) * LFE_v μ₀ (lam D N A) z (k * h) x +
                    (∑ b, LFE_v μ₀ (lam D N A) z (k * h) b *
                      flowKmat (lam D N A) θ z z (k * h) b x) +
                    LFE_e μ₀ (lam D N A) θ z (k * h) x) := by
              simp only [hW, hYv, hEv, hv, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hk1]
              ring
            rw [e]
            exact hstep x
        _ = R := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hR]
          ring
    calc ‖Yv + (h : ℂ) • Ev + (W (k + 1) - Yv - (h : ℂ) • Ev)‖
        ≤ ‖Yv‖ + ‖(h : ℂ) • Ev‖ + ‖W (k + 1) - Yv - (h : ℂ) • Ev‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by simp only [hβ]; linarith
  have hg := LFE_gron K h q₀ hhpos hKq (fun k => ‖W k‖) β (fun k => norm_nonneg _) hβ0 hrec
  have hιk : ∀ k : ℕ, k < K → ι₀ ≤ flowIm (lam D N A) z (k * h) := by
    intro k hk
    obtain ⟨hk0, hkS⟩ := hgrid k hk.le
    obtain ⟨-, hιk, -, -, -, -, -⟩ := LFE_flow D N hD1 hN1 A hΛ10 z hz S hSt _ hk0 hkS
    rw [hιk]
    exact le_mul_of_one_le_left hι0.le (Real.one_le_exp (by positivity))
  have hsum := LFE_sumbd K h q₀ ι₀ P N D Y R (fun k => flowIm (lam D N A) z (k * h)) hhpos hKq
    hq1 hι0 hιk hP0 hNpos hD0 hY0 hR0
  -- the start
  have hW0 : ‖W 0‖ ≤ D * sup := by
    refine (LFE_l2_le _).trans ?_
    calc ∑ x, ‖W 0 x‖ ≤ ∑ _x : Fin D, sup := by
          refine Finset.sum_le_sum fun x _ => ?_
          have e : W 0 x = LFE_v μ₀ (lam D N A) z 0 x := by
            simp only [hW, PiLp.toLp_apply, Nat.cast_zero, zero_mul]
          rw [e]; exact hsup_ge x
      _ = D * sup := by simp
  -- the end
  have hWK : ‖LFE_v μ₀ (lam D N A) z S a‖ ≤ ‖W K‖ := by
    have e : W K a = LFE_v μ₀ (lam D N A) z S a := by
      simp only [hW, PiLp.toLp_apply, hKh]
    rw [← e]
    exact PiLp.norm_apply_le (W K) a
  -- the remainders
  have hN10 : (N : ℝ) ^ (-(10 : ℝ)) = 1 / (N : ℝ) ^ 10 := by
    rw [Real.rpow_neg hNpos.le, show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      one_div]
  set Z := (K : ℝ) * h * D * Y + K * R with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hZle : Z ≤ Cz / (N : ℝ) ^ 7 := by
    have h1 : (K : ℝ) * h * D * Y ≤ 12 * (D : ℝ) ^ 3 / (N : ℝ) ^ 7 := by
      rw [hKh, hY, hN10]
      have hS1 : S ≤ 1 := by linarith
      have e : 12 * (D : ℝ) ^ 3 / (N : ℝ) ^ 7 = D * (12 * (D : ℝ) ^ 2 * (N : ℝ) ^ 3 *
          (1 / (N : ℝ) ^ 10)) := by field_simp
      rw [e]
      have h0 : 0 ≤ (D : ℝ) * (12 * (D : ℝ) ^ 2 * (N : ℝ) ^ 3 * (1 / (N : ℝ) ^ 10)) := by
        positivity
      calc S * D * (12 * (D : ℝ) ^ 2 * (N : ℝ) ^ 3 * (1 / (N : ℝ) ^ 10))
          = S * (D * (12 * (D : ℝ) ^ 2 * (N : ℝ) ^ 3 * (1 / (N : ℝ) ^ 10))) := by ring
        _ ≤ 1 * (D * (12 * (D : ℝ) ^ 2 * (N : ℝ) ^ 3 * (1 / (N : ℝ) ^ 10))) :=
          mul_le_mul_of_nonneg_right hS1 h0
        _ = _ := one_mul _
    have h2 : (K : ℝ) * R ≤ D * Kst / (N : ℝ) ^ 7 := by
      have e : (K : ℝ) * R = D * Kst * (N : ℝ) ^ 15 * (K * h ^ 2) := by rw [hR]; ring
      rw [e]
      calc (D : ℝ) * Kst * (N : ℝ) ^ 15 * (K * h ^ 2)
          ≤ D * Kst * (N : ℝ) ^ 15 * (1 / (N : ℝ) ^ 25) :=
            mul_le_mul_of_nonneg_left hKh2 (by positivity)
        _ = D * Kst / (N : ℝ) ^ 10 := by field_simp
        _ ≤ D * Kst / (N : ℝ) ^ 7 := div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_right₀ (by linarith) (by norm_num))
    rw [hZ, hCz, add_div]
    exact add_le_add h1 h2
  -- `q_S⁻¹ ≤ 2N`
  have hqinv : (q₀ - S)⁻¹ ≤ 2 * N := by
    have hle := LFE_eta_le D N hD1 hN1 A hΛ10 z hz S hSt hq1 S hS0 le_rfl
    have hηN := (hη S hS0 le_rfl).1
    rw [inv_le_comm₀ hqS (by positivity)]
    have h1 : (2 * (N : ℝ))⁻¹ < (charFlowZ (lam D N A) z S).im / 2 := by
      rw [mul_inv]
      have : (2 : ℝ)⁻¹ * (N : ℝ)⁻¹ = (N : ℝ)⁻¹ / 2 := by ring
      rw [this]
      linarith only [hηN]
    have h2 : (charFlowZ (lam D N A) z S).im / 2 ≤ q₀ - S := by
      have h3 : 2 * (q₀ - S) * flowIm (lam D N A) z S ≤ 2 * (q₀ - S) :=
        mul_le_of_le_one_right (by linarith only [hqS]) hιS1.le
      linarith only [hle, h3]
    linarith only [h1, h2]
  have hsum2 : ∑ k ∈ Finset.range K, (q₀ - (k + 1) * h) * β k ≤
      D ^ 2 * P / ((N : ℝ) ^ 2 * ι₀ ^ 3) * (1 / (q₀ - S)) + Z := by
    rw [hZ, ← hKh, ← add_assoc]
    exact hsum
  have ha : (q₀ - S) * ‖LFE_v μ₀ (lam D N A) z S a‖ ≤ Real.exp (S / 2) *
      (q₀ * (D * sup) + D ^ 2 * P / ((N : ℝ) ^ 2 * ι₀ ^ 3) * (1 / (q₀ - S)) + Z) := by
    have h1 := mul_le_mul_of_nonneg_left hWK hqS.le
    rw [hKh] at hg
    refine h1.trans (hg.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le))
    have h2 := mul_le_mul_of_nonneg_left hW0 hq0.le
    linarith only [h2, hsum2]
  have hNA : (N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁ = (N : ℝ) ^ (τ₁ + τ₁) := (Real.rpow_add hNpos _ _).symm
  have hE1 : 1 ≤ Real.exp (S / 2) := Real.one_le_exp (by positivity)
  have hE : Real.exp (S / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
  have hιS' : Real.exp (S / 2) * ι₀ ≤ 1 := by rw [← hιS]; exact hιS1.le
  have hfin := LFE_ar5 N (q₀ - S) q₀ ι₀ (Real.exp (S / 2)) sup ‖LFE_v μ₀ (lam D N A) z S a‖
    ((N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁) ((N : ℝ) ^ εg) Z Cz D ((N : ℝ) ^ τ') hNr hqS hq0.le hι0 hE1 hE
    hιS' (by linarith) hsup0 hD0 (Real.one_le_rpow (by linarith) hεg.le) (by positivity) hZ0
    hqinv hZle ha hA1 (by rw [hNA]; linarith only [hA2]) hA3 ht1
  rw [hιS]
  exact hfin


/-- Lemma 3.10 [lem_flow_1.5], (3.30) [flow_1G_res], at one time: for every class member `μ₀` and
admissible `(z, S)`, at the law (3.13) [eq:Gauss_div] at time `S`,
`|E⟨(G_S - M_S) E_a⟩| ≤ N^{τ'} ((q₀/q_S) max_b |E⟨(G_0 - M_0) E_b⟩|`
`+ N^{ε_g}/(N² q_S² (Im m_S)³))`. -/
theorem flowG1_exp (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ a : Fin D,
        ‖∫ H, ntr ((res (Matrix.of H + ((Real.exp (-S / 2) : ℝ) : ℂ) • lam D N A)
              (charFlowZ (lam D N A) z S) -
            MExt (((Real.exp (-S / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z S)) *
              Ea D N a) ∂(blockOULaw D N μ₀ S)‖ ≤
          (N : ℝ) ^ τ' * (flowTc (lam D N A) z / (flowTc (lam D N A) z - S) *
              (⨆ b : Fin D, ‖∫ H, ntr ((res (Matrix.of H + lam D N A) z - MExt (lam D N A) z) *
                Ea D N b) ∂μ₀‖) +
            (N : ℝ) ^ εg / ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - S) ^ 2 *
              flowIm (lam D N A) z S ^ 3)) := by
  exact LFE_main D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C

/-- The final inequality for (3.31) [flow_1G_res_2]: with `q₀ ≤ c u`, `u = N^{-ε_g}`, `d u = 1`,
the start bound `sup ≤ b N⁻¹ ι₀⁻¹`, `ι_S = E ι₀`, `1 ≤ E ≤ e^{1/2}`, `η_S ≤ 2 q_S ι_S` and
`d² ≤ N η_S ι_S`, the right side of (3.30) [flow_1G_res] is at most `t u / (N q_S ι_S)`. -/
private lemma LFE_ar4 (N q₀ qS ι₀ E η sup a b c d u t : ℝ) (hN : 0 < N) (hq₀ : 0 ≤ q₀)
    (hqS : 0 < qS) (hι₀ : 0 < ι₀) (hE1 : 1 ≤ E) (hE : E ≤ Real.exp (1 / 2)) (ha : 0 ≤ a)
    (hb : 1 ≤ b) (hc : 0 ≤ c) (hu : 0 < u) (hdu : d * u = 1)
    (hq : q₀ ≤ c * u) (hsup : sup ≤ b * (N⁻¹ * ι₀⁻¹)) (hη : η ≤ 2 * qS * (E * ι₀))
    (hd2 : d ^ 2 ≤ N * η * (E * ι₀))
    (hfin : (c * Real.exp (1 / 2) + 2) * (a * b) ≤ t) :
    a * (q₀ / qS * sup + d / (N ^ 2 * qS ^ 2 * (E * ι₀) ^ 3)) ≤
      t * (u / (N * qS * (E * ι₀))) := by
  set ι := E * ι₀ with hι
  have hιpos : 0 < ι := by positivity
  set W := u / (N * qS * ι) with hW
  have hWpos : 0 < W := by positivity
  have hsup0 : 0 ≤ sup ∨ sup < 0 := le_or_gt 0 sup
  have h1 : q₀ / qS * sup ≤ c * Real.exp (1 / 2) * b * W := by
    rcases hsup0 with hs | hs
    · have hb' : b * (N⁻¹ * ι₀⁻¹) = b * E / (N * ι) := by rw [hι]; field_simp
      have t1 : q₀ / qS * sup ≤ (c * u) / qS * (b * E / (N * ι)) := by
        rw [← hb']
        exact mul_le_mul (div_le_div_of_nonneg_right hq hqS.le) hsup hs (by positivity)
      have e1 : (c * u) / qS * (b * E / (N * ι)) = c * E * b * W := by rw [hW]; field_simp
      have t2 : c * E * b * W ≤ c * Real.exp (1 / 2) * b * W := by
        have : 0 ≤ c * b * W := by positivity
        nlinarith
      linarith
    · have : q₀ / qS * sup ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (div_nonneg hq₀ hqS.le) hs.le
      have : 0 ≤ c * Real.exp (1 / 2) * b * W := by
        have := Real.exp_pos (1 / 2); positivity
      linarith
  have h2 : d / (N ^ 2 * qS ^ 2 * ι ^ 3) ≤ 2 * W := by
    have hηpos : 0 ≤ η := by
      have : 0 ≤ d ^ 2 := sq_nonneg d
      have h := hd2.trans' this
      by_contra hneg
      push Not at hneg
      have : N * η * ι < 0 := by
        have := mul_neg_of_pos_of_neg hN hneg
        exact mul_neg_of_neg_of_pos this hιpos
      linarith
    have hNq : d ^ 2 ≤ 2 * (N * qS * ι ^ 2) := by
      have := mul_le_mul_of_nonneg_left hη (by positivity : (0 : ℝ) ≤ N * ι)
      nlinarith
    have hd : d = d ^ 2 * u := by
      have : d ^ 2 * u = d * (d * u) := by ring
      rw [this, hdu, mul_one]
    rw [hW, hd, div_le_iff₀ (by positivity)]
    have e : 2 * (u / (N * qS * ι)) * (N ^ 2 * qS ^ 2 * ι ^ 3) = 2 * (N * qS * ι ^ 2) * u := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hNq hu.le
  have h3 : a * (q₀ / qS * sup + d / (N ^ 2 * qS ^ 2 * ι ^ 3)) ≤
      (c * Real.exp (1 / 2) + 2) * (a * b) * W := by
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) ha
    have hb2 : 2 * W ≤ 2 * b * W := by nlinarith
    have : a * (c * Real.exp (1 / 2) * b * W + 2 * W) ≤
        (c * Real.exp (1 / 2) + 2) * (a * b) * W := by
      have := mul_le_mul_of_nonneg_left hb2 ha
      nlinarith
    linarith
  exact h3.trans (mul_le_mul_of_nonneg_right hfin hWpos.le)

/-- Lemma 3.10 [lem_flow_1.5], (3.31) [flow_1G_res_2], at one time, for the law of `H_{t₀}` of
(4.1) [defVt], `t₀ ∈ [0, 1]`: at the law (3.13) [eq:Gauss_div] at time `S`,
`|E⟨(G_S - M_S) E_a⟩| ≤ N^{τ'} N^{-ε_g} / (N q_S Im m_S)`. -/
theorem flowG1_exp_paper (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4)
    (hC₀ : 6 < C₀) (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t₀ : ℝ), 0 ≤ t₀ → t₀ ≤ 1 →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ a : Fin D,
        ‖∫ H, ntr ((res (Matrix.of H + ((Real.exp (-S / 2) : ℝ) : ℂ) • lam D N A)
              (charFlowZ (lam D N A) z S) -
            MExt (((Real.exp (-S / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z S)) *
              Ea D N a) ∂(blockOULaw D N (ouMatLaw D N L t₀) S)‖ ≤
          (N : ℝ) ^ τ' * ((N : ℝ) ^ (-εg) /
            (N * (flowTc (lam D N A) z - S) * flowIm (lam D N A) z S)) := by
  intro τ' hτ'
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  set τ₁ := τ' / 3 with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  obtain ⟨N₁, hN₁⟩ := flowG1_exp D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C' τ₁ hτ₁0
  obtain ⟨N₂, hN₂⟩ := lemma_G_large_2_theta D hD δA τ τe εg c hδA hτ hτe hεg hεg₁ hεg₂ hc C
    τ₁ hτ₁0
  have hev : ∀ᶠ N : ℕ in Filter.atTop, N₁ ≤ N ∧ N₂ ≤ N ∧ 2 ≤ N ∧
      2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧ c * (N : ℝ) ^ (-εg) ≤ 1 ∧
      (c * Real.exp (1 / 2) + 2) * (N : ℝ) ^ (τ₁ + τ₁) ≤ (N : ℝ) ^ τ' := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    refine (Filter.eventually_ge_atTop N₁).and ((Filter.eventually_ge_atTop N₂).and
      ((Filter.eventually_ge_atTop 2).and
      (((t1.const_mul 2).eventually (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and
      (((t2.const_mul c).eventually (Iic_mem_nhds (by simp : c * 0 < 1))).and
      (LFE_ev_pow _ _ _ (by linarith))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN L t₀ ht0 ht1 A z S hadm a => ?_⟩
  obtain ⟨hN1', hN2', hN2, hAN, hcN, hfin⟩ := hN₀ N hN
  have : NeZero D := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hcl := hC' N L t₀ ht0
  have hθ0 : 0 ≤ Real.exp (-t₀) := (Real.exp_pos _).le
  have hθ1 : Real.exp (-t₀) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h1 := hN₁ N hN1' (Real.exp (-t₀)) hθ0 hθ1 _ hcl A z S hadm a
  have h2 := (hN₂ N hN2' L t₀ ht0 ht1 A hadm.1 z hadm.2.1 hadm.2.2.1 hadm.2.2.2.1
    hadm.2.2.2.2.1 hadm.2.2.2.2.2.1).1
  have hsup : (⨆ b : Fin D, ‖∫ H, ntr ((res (Matrix.of H + lam D N A) z - MExt (lam D N A) z) *
      Ea D N b) ∂(ouMatLaw D N L t₀)‖) ≤
      (N : ℝ) ^ τ₁ * ((N : ℝ)⁻¹ * ((mExt (lam D N A) z).im)⁻¹) := ciSup_le h2
  refine h1.trans ?_
  obtain ⟨hΛ10, -, hz, -, hq0, hq1, hS0, hSt, hη⟩ :=
    LFE_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  obtain ⟨-, hιS, hι0, -, -, -, -⟩ := LFE_flow D N hD1 hN1 A hΛ10 z hz S hSt S hS0 le_rfl
  have hηS := LFE_eta_le D N hD1 hN1 A hΛ10 z hz S hSt hq1 S hS0 le_rfl
  have hq0c := (LFE_q0 N hN1 εg c _ hc hadm.2.2.2.2.1 hadm.2.2.2.2.2.1 hcN).2.1
  have hqS : 0 < flowTc (lam D N A) z - S := by linarith
  have hE1 : 1 ≤ Real.exp (S / 2) := Real.one_le_exp (by positivity)
  have hE : Real.exp (S / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
  have hdu : (N : ℝ) ^ εg * (N : ℝ) ^ (-εg) = 1 := by
    rw [← Real.rpow_add hNpos, add_neg_cancel, Real.rpow_zero]
  have hd2 : ((N : ℝ) ^ εg) ^ 2 ≤
      N * (charFlowZ (lam D N A) z S).im * (Real.exp (S / 2) * (mExt (lam D N A) z).im) := by
    rw [← hιS]
    refine le_trans ?_ hadm.2.2.2.2.2.2.2.2
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by push_cast; nlinarith)
  rw [hιS] at hηS ⊢
  have hNab : (N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁ = (N : ℝ) ^ (τ₁ + τ₁) := (Real.rpow_add hNpos _ _).symm
  exact LFE_ar4 N (flowTc (lam D N A) z) _ _ _ _ _ _ _ c _ _ _ hNpos hq0.le hqS hι0 hE1 hE
    (Real.rpow_nonneg hNpos.le _) (Real.one_le_rpow hNr hτ₁0.le) (by linarith)
    (Real.rpow_pos_of_pos hNpos _) hdu hq0c hsup hηS hd2 (by rw [hNab]; exact hfin)

end RBMTransitionEdge

end
