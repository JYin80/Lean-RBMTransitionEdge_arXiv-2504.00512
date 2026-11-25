module

public import RBMTransitionEdge.Flow.LemFlowExp

@[expose] public section

/-!
# Lemma 3.11 at one time

The bound on `K_{(1,2,1)}` along the flow used in the proof of Lemma 3.11 [lem_flow_3], and
(3.32) [flow_3_result], (3.33) [flow_3_result_2] of Lemma 3.11 at one time for the laws of
`H_{t₀}` of (4.1) [defVt].
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Operator-norm tools -/

section LF3_Op

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `opNorm` is the `L²` operator norm. -/
private lemma LF3_op_eq (A : Matrix ι ι ℂ) : opNorm A = ‖A‖ := rfl

/-- `‖AB‖ ≤ ‖A‖ ‖B‖`. -/
private lemma LF3_op_mul (A B : Matrix ι ι ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  simpa only [LF3_op_eq] using norm_mul_le A B

/-- `‖A‖ ≥ 0`. -/
private lemma LF3_op_nonneg (A : Matrix ι ι ℂ) : 0 ≤ opNorm A := norm_nonneg _

/-- `‖A^*‖ = ‖A‖`. -/
private lemma LF3_op_conj (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  simpa only [LF3_op_eq] using Matrix.l2_opNorm_conjTranspose A

/-- An entry is bounded by the operator norm. -/
private lemma LF3_entry_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ opNorm A := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [h1, mul_one] at h
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  have h3 : ((EuclideanSpace.equiv ι ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)).ofLp i = A i j := by
    simp
  rw [h3] at h2
  exact h2.trans h

/-- `|⟨A⟩| ≤ ‖A‖`. -/
private lemma LF3_ntr_le [Nonempty ι] (A : Matrix ι ι ℂ) : ‖ntr A‖ ≤ opNorm A := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, opNorm A := Finset.sum_le_sum fun i _ => LF3_entry_le A i i
    _ = _ := by simp

omit [DecidableEq ι] in
/-- `⟨A^*⟩ = conj ⟨A⟩`. -/
private lemma LF3_ntr_conj (A : Matrix ι ι ℂ) : ntr Aᴴ = star (ntr A) := by
  simp [ntr, Matrix.trace_conjTranspose, star_mul']

omit [DecidableEq ι] in
/-- `⟨AB⟩ = ⟨BA⟩`. -/
private lemma LF3_ntr_comm (A B : Matrix ι ι ℂ) : ntr (A * B) = ntr (B * A) := by
  simp only [ntr, Matrix.trace_mul_comm A B]

end LF3_Op

/-- `‖E_a‖ ≤ 1` for the block projection. -/
private lemma LF3_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- `E_a^* = E_a`. -/
private lemma LF3_Ea_conj (D N : ℕ) (a : Fin D) : (Ea D N a)ᴴ = Ea D N a := by
  unfold Ea
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  simp only [Pi.star_apply]
  split_ifs <;> simp

/-- The Hermitian part of a Hermitian array is the array. -/
private lemma LF3_hermPart_eq {ι : Type*} (H : ι → ι → ℂ) (hH : (Matrix.of H).IsHermitian) :
    hermPart H = H := by
  funext i j
  have h1 : star (H j i) = H i j := by
    have := congrFun (congrFun hH i) j
    simpa [Matrix.conjTranspose_apply] using this
  simp only [hermPart, h1]
  ring

/-- `t Λ(A) = Λ(t A)` for real `t`. -/
private lemma LF3_lam_smul (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    (t : ℂ) • lam D N A = lam D N ((t : ℂ) • A) := by
  ext p q
  simp only [lam, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [mul_add, Complex.conj_ofReal]

/-- A real multiple of a Hermitian matrix is Hermitian. -/
private lemma LF3_herm_smul {ι : Type*} (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (c : ℝ) :
    (((c : ℝ) : ℂ) • Λ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hΛ.eq]
  simp

/-- The Hermitian part of an array is Hermitian. -/
private lemma LF3_hermPart_herm {ι : Type*} (H : ι → ι → ℂ) :
    (Matrix.of (hermPart H)).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, hermPart, star_div₀, star_add,
    star_star]
  simp [add_comm]

/-! ### The closed-form flow on `[0, S]` -/

/-- `C N^α ≤ N^β` for all large `N` when `α < β`. -/
private lemma LF3_ev_pow (C α β : ℝ) (hαβ : α < β) :
    ∀ᶠ N : ℕ in Filter.atTop, C * (N : ℝ) ^ α ≤ (N : ℝ) ^ β := by
  have t : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (β - α)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [t.eventually_ge_atTop C, Filter.eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have e : (N : ℝ) ^ β = (N : ℝ) ^ (β - α) * (N : ℝ) ^ α := by
    rw [← Real.rpow_add hNpos]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hNpos.le _)

/-- Along the closed-form flow (3.10) [eq:deterflow] on `[0, S]`, `S < t_c - t₀`, `‖Λ‖ ≤ 1/10`:
`η_s > 0`, `Im m_s = e^{s/2} Im m ∈ (0, 1)`, `η_s Im m_s` is at least its value at `S`,
`t_c - t_s = (t_c - t₀) - s` and `η_s ≥ (t_c - t_s) Im m_s`. -/
private lemma LF3_flow (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
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
  have hapr := mSol_apriori _ (LF3_herm_smul Λ hΛ (Real.exp (-s / 2))) hnorm _ hpos
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
private lemma LF3_adm (D N : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ N) (δA τ τe εg c C₀ : ℝ) (hεg : 0 < εg)
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
    LF3_flow D N hD (by omega) A hΛ z hz S hSt s hs0 hsS
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
private lemma LF3_adm_mono (D N : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ N) (δA τ τe εg c C₀ : ℝ)
    (hεg : 0 < εg) (hC₀ : 0 < C₀) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ)
    (hadm : flowAdm D N δA τ τe εg c C₀ A z S)
    (hAN : 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10) (hcN : c * (N : ℝ) ^ (-εg) ≤ 1) (r : ℝ) (hr0 : 0 ≤ r)
    (hrS : r ≤ S) : flowAdm D N δA τ τe εg c C₀ A z r := by
  obtain ⟨-, -, -, -, -, -, -, hSt, hη⟩ :=
    LF3_adm D N hD hN δA τ τe εg c C₀ hεg hC₀ A z S hadm hAN hcN
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -, -⟩ := hadm
  exact ⟨h1, h2, h3, h4, h5, h6, hr0, lt_of_le_of_lt hrS hSt, (hη r hr0 hrS).2⟩

/-- At time `0` the flowed objects are the objects at the start. -/
private lemma LF3_zero {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z z₁ z₂ z₃ : ℂ)
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

/-- `η_s ≤ 2 (t_c - t_s) Im m_s` along the flow when `t_c - t₀ ≤ 1`: `η_s / Im m_s = e^{q_s} - 1`
with `q_s = t_c - t_s ∈ (0, 1]` ((3.14) [t_eta]). -/
private lemma LF3_eta_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (hq1 : flowTc (lam D N A) z ≤ 1) (s : ℝ) (hs0 : 0 ≤ s)
    (hsS : s ≤ S) :
    (charFlowZ (lam D N A) z s).im ≤
      2 * (flowTc (lam D N A) z - s) * flowIm (lam D N A) z s := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  obtain ⟨-, hιeq, hι0, -, -, -, -⟩ := LF3_flow D N hD hN A hA z hz S hS s hs0 hsS
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

/-! ### Loops, flags and words along the flow -/

/-- The loop list `[(E_y, z₁), (E_x, z₂)]`, whose loop is `⟨E_y G₁ E_x G₂⟩ = D⁻¹ L_{xy}`. -/
private abbrev LF3_l {D N : ℕ} (z₁ z₂ : ℂ) (x y : Fin D) :
    List (Matrix (Idx D N) (Idx D N) ℂ × ℂ) :=
  [(Ea D N y, z₁), (Ea D N x, z₂)]

/-- `⟨A B C E⟩ = ⟨E A (B C)⟩`. -/
private lemma LF3_ntr4 {ι : Type*} [Fintype ι] (A B C E : Matrix ι ι ℂ) :
    ntr (A * B * C * E) = ntr (E * A * (B * C)) := by
  rw [LF3_ntr_comm]
  simp only [Matrix.mul_assoc]

/-- `L_{xy}` at the Hermitian part of an array is `D` times the loop of `LF3_l`. -/
private lemma LF3_Lmat_loop {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (x y : Fin D) (r : ℝ) (h : Idx D N → Idx D N → ℂ) :
    flowLmat Λ z₁ z₂ r (hermPart h) x y = (D : ℂ) * flowLoop Λ (LF3_l z₁ z₂ x y) r h := by
  simp only [flowLmat, Lmat, flowLoop, chainB, LF3_l, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Matrix.mul_one]
  rw [LF3_ntr4]

/-- `𝓛(cF) = c 𝓛F` for real `c` and `C²` functions `F`. -/
private lemma LF3_genA_smul {D N : ℕ} (F : (Idx D N → Idx D N → ℂ) → ℂ) (hF : ContDiff ℝ 2 F)
    (c : ℝ) (H : Idx D N → Idx D N → ℂ) :
    genA (fun h => (c : ℂ) * F h) H = (c : ℂ) * genA F H := by
  have e : (fun h => (c : ℂ) * F h) = c • F := by
    funext h
    simp [Complex.real_smul]
  rw [e]
  unfold genA
  rw [fderiv_const_smul (hF.differentiable (by norm_num) H) c]
  have e2 : ∀ w : Fin D → Coords N, iteratedFDeriv ℝ 2 (c • F) H
      ![Matrix.of.symm (blockH D N w), Matrix.of.symm (blockH D N w)] =
      (c : ℂ) * iteratedFDeriv ℝ 2 F H
        ![Matrix.of.symm (blockH D N w), Matrix.of.symm (blockH D N w)] := by
    intro w
    rw [iteratedFDeriv_const_smul_apply hF.contDiffAt]
    simp [Complex.real_smul]
  simp only [e2, integral_const_mul]
  simp only [FunLike.coe_smul, Pi.smul_apply, Complex.real_smul]
  ring

/-- `G^b`: `G^*` when `b` holds and `G` otherwise. -/
private abbrev LF3_pw {ι : Type*} (G : Matrix ι ι ℂ) (b : Bool) : Matrix ι ι ℂ :=
  if b then Gᴴ else G

/-- `‖G^b‖ = ‖G‖`. -/
private lemma LF3_op_pw {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (b : Bool) :
    opNorm (LF3_pw G b) = opNorm G := by
  cases b
  · rfl
  · exact LF3_op_conj G

/-- At the flowed points `z_{i,s} ∈ {z_s, z̄_s}`: `G(z_{i,s}) = G(z_s)^b` and
`M(z_{i,s}) = M(z_s)^b` for one flag `b`. -/
private lemma LF3_flag {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian) (zi : ℂ)
    (hi : zi = z ∨ zi = star z) :
    ∃ b : Bool,
      res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) zi s) =
        LF3_pw (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) b ∧
      MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) zi s) =
        LF3_pw (MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) b := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  rcases hi with rfl | rfl
  · exact ⟨false, rfl, rfl⟩
  · refine ⟨true, ?_, ?_⟩
    · have hΛ := lam_isHermitian D N A
      have hX : (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A).IsHermitian :=
        hH.add (LF3_herm_smul _ hΛ _)
      have hw := (charFlow_M (lam D N A) hΛ z hz s hs).1
      rw [charFlowZ_conj _ z hz s, Complex.star_def, res_conj _ hX _ hw]
      rfl
    · have hΛ := lam_isHermitian D N A
      have hw := (charFlow_M (lam D N A) hΛ z hz s hs).1
      rw [charFlowZ_conj _ z hz s, (mExt_conj _ (LF3_herm_smul _ hΛ _) _ hw.ne').2]
      rfl

/-- `|⟨(G^b - M^b) E⟩| = |⟨(G - M) E⟩|` for a Hermitian `E`. -/
private lemma LF3_ntr_pw_sub {ι : Type*} [Fintype ι] (G M E : Matrix ι ι ℂ)
    (hE : Eᴴ = E) (b : Bool) :
    ‖ntr ((LF3_pw G b - LF3_pw M b) * E)‖ = ‖ntr ((G - M) * E)‖ := by
  cases b
  · rfl
  · change ‖ntr ((Gᴴ - Mᴴ) * E)‖ = _
    have e : (Gᴴ - Mᴴ) * E = (E * (G - M))ᴴ := by
      rw [Matrix.conjTranspose_mul, hE, Matrix.conjTranspose_sub]
    rw [e, LF3_ntr_conj, norm_star, LF3_ntr_comm]

/-- The three-resolvent word as `resProd`. -/
private lemma LF3_word3 {ι : Type*} [Fintype ι] [DecidableEq ι] (G E₁ E₂ E₃ : Matrix ι ι ℂ)
    (b₁ b₂ b₃ : Bool) :
    LF3_pw G b₁ * E₁ * LF3_pw G b₂ * E₂ * LF3_pw G b₃ * E₃ =
      resProd (fun _ : Fin 3 => G) ![b₁, b₂, b₃] ![E₁, E₂, E₃] := by
  simp only [resProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.mul_one, Matrix.mul_assoc, LF3_pw]
  rfl

/-- The size `bndA4` of (A.53) [entprodG] for `p` equal resolvents: `Im m / η^{p-1}`, `p ≥ 2`. -/
private lemma LF3_bndA4 (p : ℕ) (hp : 2 ≤ p) (ι η : ℝ) :
    bndA4 (fun _ : Fin p => ι) (fun _ : Fin p => η) p = ι / η ^ (p - 1) := by
  have : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  simp [bndA4, hp]

/-- `|L_{ab}| ≤ D / η_s²` along the flow. -/
private lemma LF3_L_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (a b : Fin D) :
    ‖flowLmat (lam D N A) z₁ z₂ s H a b‖ ≤ D / (charFlowZ (lam D N A) z s).im ^ 2 := by
  have hNe : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  obtain ⟨b₁, hG₁, -⟩ := LF3_flag hD hN A z hz s hs H hH z₁ h₁
  obtain ⟨b₂, hG₂, -⟩ := LF3_flag hD hN A z hz s hs H hH z₂ h₂
  have hΛ := lam_isHermitian D N A
  have hX : (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A).IsHermitian :=
    hH.add (LF3_herm_smul _ hΛ _)
  have hη := (charFlow_M _ hΛ z hz s hs).1
  have hGn := opNorm_res_le _ hX _ hη
  set G := res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
    (charFlowZ (lam D N A) z s)
  simp only [flowLmat, Lmat]
  rw [hG₁, hG₂, norm_mul, Complex.norm_natCast, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (LF3_ntr_le _).trans ?_
  have e1 := LF3_opNorm_Ea D N a
  have e2 := LF3_opNorm_Ea D N b
  have g1 : opNorm (LF3_pw G b₁) ≤ (charFlowZ (lam D N A) z s).im⁻¹ := by
    rw [LF3_op_pw]; exact hGn
  have g2 : opNorm (LF3_pw G b₂) ≤ (charFlowZ (lam D N A) z s).im⁻¹ := by
    rw [LF3_op_pw]; exact hGn
  have p1 := LF3_op_nonneg (LF3_pw G b₁)
  have p2 := LF3_op_nonneg (LF3_pw G b₂)
  have p3 := LF3_op_nonneg (Ea D N a)
  have p4 := LF3_op_nonneg (Ea D N b)
  have hinv : 0 ≤ (charFlowZ (lam D N A) z s).im⁻¹ := inv_nonneg.2 hη.le
  calc opNorm (LF3_pw G b₁ * Ea D N a * LF3_pw G b₂ * Ea D N b)
      ≤ opNorm (LF3_pw G b₁) * opNorm (Ea D N a) * opNorm (LF3_pw G b₂) * opNorm (Ea D N b) := by
        refine (LF3_op_mul _ _).trans ?_
        refine mul_le_mul_of_nonneg_right ((LF3_op_mul _ _).trans ?_) p4
        exact mul_le_mul_of_nonneg_right (LF3_op_mul _ _) p2
    _ ≤ (charFlowZ (lam D N A) z s).im⁻¹ * 1 * (charFlowZ (lam D N A) z s).im⁻¹ * 1 := by
        gcongr
    _ = ((charFlowZ (lam D N A) z s).im ^ 2)⁻¹ := by ring

/-! ### Measurability, integrability and moments -/

/-- `⟨·⟩` is continuous. -/
private lemma LF3_ntr_cont {ι : Type*} [Fintype ι] : Continuous fun M : Matrix ι ι ℂ => ntr M := by
  unfold ntr
  exact continuous_const.mul (continuous_id.matrix_trace)

/-- Matrix inversion is measurable. -/
private lemma LF3_inv_meas {ι : Type*} [Fintype ι] [DecidableEq ι] :
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
private lemma LF3_res_meas {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (w : ℂ)
    (φ : Matrix (Idx D N) (Idx D N) ℂ → ℂ) (hφ : Continuous φ) :
    Measurable fun H : Idx D N → Idx D N → ℂ => φ (res (Matrix.of H + Λ) w) := by
  unfold res
  have : Continuous fun H : Idx D N → Idx D N → ℂ =>
      Matrix.of H + Λ - w • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
    have : Continuous fun H : Idx D N → Idx D N → ℂ => (Matrix.of H : Matrix _ _ ℂ) :=
      continuous_id
    fun_prop
  exact hφ.measurable.comp (LF3_inv_meas.comp this.measurable)

/-- The Hermitian arrays form a measurable set. -/
private lemma LF3_herm_meas {D N : ℕ} :
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
private lemma LF3_int {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ H ∂μ, (Matrix.of H).IsHermitian) (f : (Idx D N → Idx D N → ℂ) → ℂ)
    (hf : Measurable f) (B : ℝ) (hB : ∀ H, (Matrix.of H).IsHermitian → ‖f H‖ ≤ B) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B (hμ.mono fun H hH => hB H hH)

/-- `‖x‖⁴ ≤ Σ_i ‖x_i‖⁴` for the sup norm. -/
private lemma LF3_pi_pow4 {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (x : ι → E) :
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
private lemma LF3_mom (D N : ℕ) (hN : 1 ≤ N) (C : ℕ → ℝ) (θ : ℝ)
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
      (LF3_pi_pow4 H).trans (Finset.sum_le_sum fun i _ => LF3_pi_pow4 (H i))
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
private def LF3_arrL (D N : ℕ) : (Fin D → Coords N) →L[ℝ] (Idx D N → Idx D N → ℂ) :=
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

/-- `G_s = (H + Λ_s - z_s)⁻¹` at the state `H` along the flow (3.10) [eq:deterflow]. -/
private abbrev LF3_G {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (s : ℝ)
    (H : Idx D N → Idx D N → ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s)

/-- `M_s = M(z_s, Λ_s)` along the flow (3.10) [eq:deterflow]. -/
private abbrev LF3_M {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (s : ℝ) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s)

/-- `⟨(G_s - M_s) E_a⟩` at the state `H`. -/
private abbrev LF3_d {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (s : ℝ)
    (H : Idx D N → Idx D N → ℂ) (a : Fin D) : ℂ :=
  ntr ((LF3_G Λ z s H - LF3_M Λ z s) * Ea D N a)

/-- Along the flow at a Hermitian state: `‖G_s‖ ≤ η_s⁻¹` and `‖M_s‖ ≤ 5/4`, so
`|⟨(G_s - M_s) E_a⟩| ≤ η_s⁻¹ + 5/4`, `|⟨G_s E_a⟩| ≤ η_s⁻¹` and `|L_{ab}| ≤ D η_s⁻²`. -/
private lemma LF3_res_bds (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (s : ℝ)
    (hs : s < flowTc (lam D N A) z) (hs0 : 0 ≤ s) (H : Idx D N → Idx D N → ℂ)
    (hH : (Matrix.of H).IsHermitian) (a b : Fin D) :
    opNorm (LF3_G (lam D N A) z s H) ≤ (charFlowZ (lam D N A) z s).im⁻¹ ∧
      opNorm (LF3_M (lam D N A) z s) ≤ 5 / 4 ∧
      ‖LF3_d (lam D N A) z s H a‖ ≤ (charFlowZ (lam D N A) z s).im⁻¹ + 5 / 4 ∧
      ‖ntr (LF3_G (lam D N A) z s H * Ea D N a)‖ ≤ (charFlowZ (lam D N A) z s).im⁻¹ ∧
      ‖flowLmat (lam D N A) z z s H a b‖ ≤ D * ((charFlowZ (lam D N A) z s).im⁻¹) ^ 2 := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hΛs := LF3_herm_smul _ hΛ (Real.exp (-s / 2))
  have hX : (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A).IsHermitian := hH.add hΛs
  have hη := (charFlow_M _ hΛ z hz s hs).1
  have hG := opNorm_res_le _ hX _ hη
  have hnorm : opNorm (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) ≤ 1 / 10 := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-s / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h0 : 0 ≤ opNorm (lam D N A) := LF3_op_nonneg _
    nlinarith
  have hM : opNorm (LF3_M (lam D N A) z s) ≤ 5 / 4 := by
    have hapr := (mSol_apriori _ hΛs hnorm _ hη).2.2
    have e : LF3_M (lam D N A) z s =
        MSol (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z s) := by
      simp [LF3_M, MExt, MSol, mExt, hη]
    rw [e]
    have h0 := LF3_op_nonneg (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
    have : (1 - 2 * opNorm (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A))⁻¹ ≤ 5 / 4 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hE := LF3_opNorm_Ea D N a
  have hEb := LF3_opNorm_Ea D N b
  have hinv : 0 ≤ (charFlowZ (lam D N A) z s).im⁻¹ := inv_nonneg.2 hη.le
  have hG0 := LF3_op_nonneg (LF3_G (lam D N A) z s H)
  refine ⟨hG, hM, ?_, ?_, ?_⟩
  · refine (LF3_ntr_le _).trans ((LF3_op_mul _ _).trans ?_)
    have h1 := opNorm_add_le (LF3_G (lam D N A) z s H) (-LF3_M (lam D N A) z s)
    have h2 : opNorm (-LF3_M (lam D N A) z s) = opNorm (LF3_M (lam D N A) z s) := by
      rw [show -LF3_M (lam D N A) z s = (-1 : ℂ) • LF3_M (lam D N A) z s by simp, opNorm_smul]
      simp
    rw [← sub_eq_add_neg, h2] at h1
    have h3 := LF3_op_nonneg (LF3_G (lam D N A) z s H - LF3_M (lam D N A) z s)
    calc opNorm (LF3_G (lam D N A) z s H - LF3_M (lam D N A) z s) * opNorm (Ea D N a)
        ≤ opNorm (LF3_G (lam D N A) z s H - LF3_M (lam D N A) z s) * 1 :=
          mul_le_mul_of_nonneg_left hE h3
      _ ≤ _ := by linarith
  · refine (LF3_ntr_le _).trans ((LF3_op_mul _ _).trans ?_)
    calc opNorm (LF3_G (lam D N A) z s H) * opNorm (Ea D N a)
        ≤ (charFlowZ (lam D N A) z s).im⁻¹ * 1 := mul_le_mul hG hE (LF3_op_nonneg _) hinv
      _ = _ := mul_one _
  · simp only [flowLmat, Lmat]
    rw [norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine (LF3_ntr_le _).trans ?_
    have p3 := LF3_op_nonneg (Ea D N a)
    have p4 := LF3_op_nonneg (Ea D N b)
    calc opNorm (LF3_G (lam D N A) z s H * Ea D N a * LF3_G (lam D N A) z s H * Ea D N b)
        ≤ opNorm (LF3_G (lam D N A) z s H) * opNorm (Ea D N a) *
            opNorm (LF3_G (lam D N A) z s H) * opNorm (Ea D N b) := by
          refine (LF3_op_mul _ _).trans ?_
          refine mul_le_mul_of_nonneg_right ((LF3_op_mul _ _).trans ?_) p4
          exact mul_le_mul_of_nonneg_right (LF3_op_mul _ _) hG0
      _ ≤ (charFlowZ (lam D N A) z s).im⁻¹ * 1 * (charFlowZ (lam D N A) z s).im⁻¹ * 1 := by
          gcongr
      _ = _ := by ring

/-- From high probability to expectation: if `|f| ≤ b` off a set of probability at most `p` and
`|f| ≤ M` almost surely, then `|E f| ≤ b + M p`. -/
private lemma LF3_expect_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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
private lemma LF3_entry_hs {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) (a b : Fin D) :
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
private lemma LF3_state_meas (D N K : ℕ) (h : ℝ) (k : ℕ) :
    Measurable fun ω : GridΩA D N K => gridStateA D N K h ω k :=
  (gridStateA_adapted D N K h k).mono ((gridFiltrA_mono D N K).2 k) le_rfl

/-- The block-OU law at time `0` is the starting law. -/
private lemma LF3_bOU0 (D N : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] : blockOULaw D N μ₀ 0 = μ₀ := by
  unfold blockOULaw
  have e : (fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
      Real.exp (-(0 : ℝ) / 2) • p.1 + Real.sqrt (1 - Real.exp (-(0 : ℝ))) •
        Matrix.of.symm (blockH D N p.2)) = Prod.fst := by
    funext p
    simp
  rw [e, Measure.map_fst_prod, measure_univ, one_smul]

/-- The size `B` of the derivatives of a two-loop: `c (DN + 1)⁴ e^{q} K² ‖E‖² (η_S ∧ 1)^{-8}
≤ |c| (2D)⁴ N⁴ e (4 + τ⁻¹)² N⁸` when `q ≤ 1`, `K ≤ 4 + τ⁻¹`, `‖E‖² ≤ 1`, `η_S ∧ 1 ≥ N⁻¹`. -/
private lemma LF3_ar_B (c D N e K P m τ : ℝ) (hD : 1 ≤ D) (hN : 2 ≤ N) (he : e ≤ Real.exp 1)
    (he0 : 0 ≤ e) (hK0 : 0 ≤ K) (hK : K ≤ 4 + τ⁻¹) (hP0 : 0 ≤ P) (hP : P ≤ 1)
    (hm : N⁻¹ ≤ m) :
    c * (D * N + 1) ^ 4 * e * K ^ 2 * P * (m ^ 8)⁻¹ ≤
      |c| * ((2 * D) ^ 4 * N ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2 * N ^ 8 := by
  have hNpos : 0 < N := by linarith
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.2 hNpos) hm
  have h8 : (m ^ 8)⁻¹ ≤ N ^ 8 := by
    rw [inv_le_comm₀ (pow_pos hmpos _) (by positivity), ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hNpos.le) hm _
  have hDN : D * N + 1 ≤ 2 * D * N := by nlinarith
  have hDN4 : (D * N + 1) ^ 4 ≤ (2 * D) ^ 4 * N ^ 4 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hDN 4
  have hc : c ≤ |c| := le_abs_self _
  have hK2 : K ^ 2 ≤ (4 + τ⁻¹) ^ 2 := pow_le_pow_left₀ hK0 hK 2
  have hm0 : 0 ≤ (m ^ 8)⁻¹ := inv_nonneg.2 (pow_nonneg hmpos.le _)
  calc c * (D * N + 1) ^ 4 * e * K ^ 2 * P * (m ^ 8)⁻¹
      ≤ |c| * (D * N + 1) ^ 4 * e * K ^ 2 * P * (m ^ 8)⁻¹ := by gcongr
    _ ≤ |c| * ((2 * D) ^ 4 * N ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2 * 1 * N ^ 8 := by gcongr
    _ = _ := by ring

/-! ### The deterministic side along the flow -/

/-- `K_r = (1 - e^r X P_{θ_r})⁻¹ e^r X`, `θ_r = 1 - e^{-r}(1 - θ)`, the closed form of
`K_{θ_r}` along the flow with `X = M̂(z₁, z₂)` (3.18) [eq:whMK]. -/
private def LF3_R {D : ℕ} (X : Matrix (Fin D) (Fin D) ℂ) (θ r : ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  (1 - ((Real.exp r : ℝ) : ℂ) • X * PTheta D (1 - Real.exp (-r) * (1 - θ)))⁻¹ *
    (((Real.exp r : ℝ) : ℂ) • X)

/-- Along the flow on `[0, S]`: `K_{θ_t}(z_{1,t}, z_{2,t})` is the closed form `LF3_R`, it solves
`dK/dt = K² + K` entrywise, and `‖(t_c - t₀ - t) K_{θ_t}‖ ≤ 1`, so its entries are at most
`(t_c - t₀ - t)⁻¹`. -/
private lemma LF3_flowK (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (t : ℝ) (ht0 : 0 ≤ t)
    (htS : t ≤ S) :
    flowKmat (lam D N A) θ z₁ z₂ t = LF3_R (Mhat (lam D N A) z₁ z₂) θ t ∧
      (∀ a b : Fin D, HasDerivAt (fun r => LF3_R (Mhat (lam D N A) z₁ z₂) θ r a b)
        ((LF3_R (Mhat (lam D N A) z₁ z₂) θ t * LF3_R (Mhat (lam D N A) z₁ z₂) θ t +
          LF3_R (Mhat (lam D N A) z₁ z₂) θ t) a b) t) ∧
      ∀ a b : Fin D, ‖flowKmat (lam D N A) θ z₁ z₂ t a b‖ ≤ (flowTc (lam D N A) z - t)⁻¹ := by
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hΛ := lam_isHermitian D N A
  have ht : t < flowTc (lam D N A) z := lt_of_le_of_lt htS hS
  obtain ⟨hηt, -, -, -, -, htc, -⟩ := LF3_flow D N hD1 hN1 A hA z hz S hS t ht0 htS
  have hMh := Mhat_flow (lam D N A) hΛ z hz t ht z₁ z₂ h₁ h₂
  have hθt : Real.exp (-t) * θ + 1 - Real.exp (-t) = 1 - Real.exp (-t) * (1 - θ) := by ring
  have hK : flowKmat (lam D N A) θ z₁ z₂ t = LF3_R (Mhat (lam D N A) z₁ z₂) θ t := by
    simp only [flowKmat, KTheta, LF3_R, hMh, hθt]
  -- the operator bound at the flowed point
  set A' : Matrix (Fin N) (Fin N) ℂ := ((Real.exp (-t / 2) : ℝ) : ℂ) • A with hA'
  have hlam : lam D N A' = ((Real.exp (-t / 2) : ℝ) : ℂ) • lam D N A :=
    (LF3_lam_smul D N A _).symm
  have he0 : 0 < Real.exp (-t) := Real.exp_pos _
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hθ0' : 0 ≤ Real.exp (-t) * θ + 1 - Real.exp (-t) := by nlinarith
  have hθ1' : Real.exp (-t) * θ + 1 - Real.exp (-t) ≤ 1 := by nlinarith
  have hflag : ∀ zi : ℂ, (zi = z ∨ zi = star z) →
      (charFlowZ (lam D N A) zi t = charFlowZ (lam D N A) z t ∨
        charFlowZ (lam D N A) zi t = star (charFlowZ (lam D N A) z t)) := by
    rintro zi (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (charFlowZ_conj _ z hz t)
  obtain ⟨hdet, hop, -⟩ := tOp_norm_le D N A' (charFlowZ (lam D N A) z t) hηt
    (Real.exp (-t) * θ + 1 - Real.exp (-t)) hθ0' hθ1' (charFlowZ (lam D N A) z₁ t)
    (charFlowZ (lam D N A) z₂ t) (hflag z₁ h₁) (hflag z₂ h₂)
  rw [hlam, htc] at hop
  rw [hlam] at hdet
  refine ⟨hK, fun a b => ?_, fun a b => ?_⟩
  · have hU : (1 - ((Real.exp t : ℝ) : ℂ) • Mhat (lam D N A) z₁ z₂ *
        PTheta D (1 - Real.exp (-t) * (1 - θ))).det ≠ 0 := by
      rw [hMh, hθt] at hdet
      exact hdet
    exact kTheta_riccati D (Mhat (lam D N A) z₁ z₂) θ t hU a b
  · have hq : 0 < flowTc (lam D N A) z - t := by linarith
    have h1 := LF3_entry_le (((flowTc (lam D N A) z - t : ℝ) : ℂ) •
      flowKmat (lam D N A) θ z₁ z₂ t) a b
    have h2 := h1.trans hop
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hq] at h2
    have h3 := (le_div_iff₀' hq).2 h2
    rwa [one_div] at h3

/-- The entries of `M` as a vector of `ℂ^{D×D}` with the Euclidean norm. -/
private def LF3_vec {D : ℕ} : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin D × Fin D) where
  toFun M := WithLp.toLp 2 (fun p => M p.1 p.2)
  map_add' M M' := by ext p; simp
  map_smul' c M := by ext p; simp

/-- `‖vec M‖ = ‖M‖_HS`. -/
private lemma LF3_norm_vec {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) :
    ‖LF3_vec M‖ = hsNorm M := by
  rw [EuclideanSpace.norm_eq, hsNorm, Fintype.sum_prod_type]
  rfl

/-- `‖M‖_HS ≤ Σ_{x,y} |M_{xy}|`. -/
private lemma LF3_hs_le' {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) :
    hsNorm M ≤ ∑ x, ∑ y, ‖M x y‖ := by
  unfold hsNorm
  have h1 : ∑ x, ∑ y, ‖M x y‖ ^ 2 ≤ (∑ x, ∑ y, ‖M x y‖) ^ 2 := by
    calc ∑ x, ∑ y, ‖M x y‖ ^ 2 ≤ ∑ x, (∑ y, ‖M x y‖) ^ 2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_sq_le_sq_sum_of_nonneg fun y _ =>
            norm_nonneg _
      _ ≤ (∑ x, ∑ y, ‖M x y‖) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun x _ =>
          Finset.sum_nonneg fun y _ => norm_nonneg _
  have h0 : 0 ≤ ∑ x, ∑ y, ‖M x y‖ := Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => norm_nonneg _
  rw [Real.sqrt_le_left h0]
  exact h1

/-- `‖M‖_HS ≤ D² m` when every entry is at most `m`. -/
private lemma LF3_hs_entry {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) (m : ℝ)
    (hm : ∀ x y, ‖M x y‖ ≤ m) : hsNorm M ≤ D ^ 2 * m := by
  refine (LF3_hs_le' M).trans ?_
  calc ∑ x, ∑ y, ‖M x y‖ ≤ ∑ _x : Fin D, ∑ _y : Fin D, m :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hm x y
    _ = D ^ 2 * m := by simp; ring

/-- `‖Σ_j M_j‖_HS ≤ Σ_j ‖M_j‖_HS` and `‖A + B‖_HS ≤ ‖A‖_HS + ‖B‖_HS`. -/
private lemma LF3_hs_add {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) :
    hsNorm (A + B) ≤ hsNorm A + hsNorm B := by
  rw [← LF3_norm_vec, ← LF3_norm_vec, ← LF3_norm_vec, map_add]
  exact norm_add_le _ _

private lemma LF3_hs_smul {D : ℕ} (c : ℂ) (A : Matrix (Fin D) (Fin D) ℂ) :
    hsNorm (c • A) = ‖c‖ * hsNorm A := by
  rw [← LF3_norm_vec, ← LF3_norm_vec, map_smul, norm_smul]

/-- The operator bound (3.67) [Tnorm] along the flow: at `t ∈ [0, S]`,
`‖q_t (K_t V + V K_t) - (1 - q_t) V‖_HS ≤ (1 + q_t) ‖V‖_HS` with `K_t = K_{θ_t}(z_{1,t}, z_{2,t})`
and `q_t = t_c - t₀ - t`. -/
private lemma LF3_tOp (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (t : ℝ) (ht0 : 0 ≤ t)
    (htS : t ≤ S) (V : Matrix (Fin D) (Fin D) ℂ) :
    hsNorm (((flowTc (lam D N A) z - t : ℝ) : ℂ) • (flowKmat (lam D N A) θ z₁ z₂ t * V +
        V * flowKmat (lam D N A) θ z₁ z₂ t) - ((1 - (flowTc (lam D N A) z - t) : ℝ) : ℂ) • V) ≤
      (1 + (flowTc (lam D N A) z - t)) * hsNorm V := by
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  obtain ⟨hηt, -, -, -, -, htc, -⟩ := LF3_flow D N hD1 hN1 A hA z hz S hS t ht0 htS
  set A' : Matrix (Fin N) (Fin N) ℂ := ((Real.exp (-t / 2) : ℝ) : ℂ) • A with hA'
  have hlam : lam D N A' = ((Real.exp (-t / 2) : ℝ) : ℂ) • lam D N A :=
    (LF3_lam_smul D N A _).symm
  have he0 : 0 < Real.exp (-t) := Real.exp_pos _
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hθ0' : 0 ≤ Real.exp (-t) * θ + 1 - Real.exp (-t) := by nlinarith
  have hθ1' : Real.exp (-t) * θ + 1 - Real.exp (-t) ≤ 1 := by nlinarith
  have hflag : ∀ zi : ℂ, (zi = z ∨ zi = star z) →
      (charFlowZ (lam D N A) zi t = charFlowZ (lam D N A) z t ∨
        charFlowZ (lam D N A) zi t = star (charFlowZ (lam D N A) z t)) := by
    rintro zi (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (charFlowZ_conj _ z hz t)
  obtain ⟨-, -, hop⟩ := tOp_norm_le D N A' (charFlowZ (lam D N A) z t) hηt
    (Real.exp (-t) * θ + 1 - Real.exp (-t)) hθ0' hθ1' (charFlowZ (lam D N A) z₁ t)
    (charFlowZ (lam D N A) z₂ t) (hflag z₁ h₁) (hflag z₂ h₂)
  have := hop V
  rw [hlam, htc] at this
  exact this

/-- On the grid `q_j = q₀ - j h`, `q_j ≠ 0` for `j ≤ k`, `Σ_{j<k} h / q_j² ≤ 1 / q_k` and
`Σ_{j<k} h / q_j ≤ log(q₀ / q_k)`. -/
private lemma LF3_rsum (q₀ h : ℝ) (hh : 0 < h) (k : ℕ) (hk : k * h < q₀) :
    (∀ j : ℕ, j ≤ k → q₀ - j * h ≠ 0) ∧
    ∑ j ∈ Finset.range k, h * ((q₀ - j * h) ^ 2)⁻¹ ≤ (q₀ - k * h)⁻¹ ∧
      ∑ j ∈ Finset.range k, h / (q₀ - j * h) ≤ Real.log (q₀ / (q₀ - k * h)) := by
  have hpos : ∀ j : ℕ, j ≤ k → 0 < q₀ - j * h := fun j hj => by
    have : (j : ℝ) * h ≤ k * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh.le
    linarith
  refine ⟨fun j hj => (hpos j hj).ne', ?_, ?_⟩
  · have hR := riemann_rpow_le 0 h q₀ 2 hh (by norm_num) 0 k (Nat.zero_le k)
      (by rw [zero_add]; exact hk)
    rw [← Finset.range_eq_Ico] at hR
    simp only [zero_add] at hR
    have e1 : ∀ j ∈ Finset.range k, h * (q₀ - j * h) ^ (-(2 : ℝ)) = h * ((q₀ - j * h) ^ 2)⁻¹ := by
      intro j hj
      rw [Real.rpow_neg (hpos j (Finset.mem_range.1 hj).le).le,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [Finset.sum_congr rfl e1] at hR
    refine hR.trans (le_of_eq ?_)
    rw [show (1 - (2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  · have hR := riemann_inv_le_log 0 h q₀ hh 0 k (Nat.zero_le k) (by rw [zero_add]; exact hk)
    rw [← Finset.range_eq_Ico] at hR
    simpa using hR

/-- `log(e N) ≤ (1 + s⁻¹) N^s` for `N ≥ 1`, `s > 0`. -/
private lemma LF3_log_le (N s : ℝ) (hN : 1 ≤ N) (hs : 0 < s) :
    Real.log (Real.exp 1 * N) ≤ (1 + s⁻¹) * N ^ s := by
  have hNpos : 0 < N := by linarith
  rw [Real.log_mul (Real.exp_pos 1).ne' hNpos.ne', Real.log_exp]
  have h1 := Real.log_le_rpow_div hNpos.le hs
  have h2 : 1 ≤ N ^ s := Real.one_le_rpow hN hs.le
  rw [div_eq_mul_inv] at h1
  nlinarith [inv_pos.2 hs]


/-! ### Tensor norms and the three-resolvent words along the flow -/

/-- An entry of a tensor is bounded by its `ℓ²` norm. -/
private lemma LF3_t3_entry {D : ℕ} (T : Fin D → Fin D → Fin D → ℂ) (a b c : Fin D) :
    ‖T a b c‖ ≤ ten3Norm T := by
  unfold ten3Norm
  rw [← Real.sqrt_sq (norm_nonneg (T a b c))]
  apply Real.sqrt_le_sqrt
  calc ‖T a b c‖ ^ 2 ≤ ∑ c', ‖T a b c'‖ ^ 2 :=
        Finset.single_le_sum (f := fun c' => ‖T a b c'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ c)
    _ ≤ ∑ b', ∑ c', ‖T a b' c'‖ ^ 2 :=
        Finset.single_le_sum (f := fun b' => ∑ c', ‖T a b' c'‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ b)
    _ ≤ ∑ a', ∑ b', ∑ c', ‖T a' b' c'‖ ^ 2 :=
        Finset.single_le_sum (f := fun a' => ∑ b', ∑ c', ‖T a' b' c'‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
          (Finset.mem_univ a)

/-- The `ℓ²` norm of a tensor is at most the sum of the moduli of its entries. -/
private lemma LF3_t3_le_sum {D : ℕ} (T : Fin D → Fin D → Fin D → ℂ) :
    ten3Norm T ≤ ∑ a, ∑ b, ∑ c, ‖T a b c‖ := by
  unfold ten3Norm
  have h0 : 0 ≤ ∑ a, ∑ b, ∑ c, ‖T a b c‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      norm_nonneg _
  rw [Real.sqrt_le_left h0]
  calc ∑ a, ∑ b, ∑ c, ‖T a b c‖ ^ 2 ≤ ∑ a, ∑ b, (∑ c, ‖T a b c‖) ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          Finset.sum_sq_le_sq_sum_of_nonneg fun c _ => norm_nonneg _
    _ ≤ ∑ a, (∑ b, ∑ c, ‖T a b c‖) ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_sq_le_sq_sum_of_nonneg fun b _ =>
          Finset.sum_nonneg fun c _ => norm_nonneg _
    _ ≤ (∑ a, ∑ b, ∑ c, ‖T a b c‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun a _ =>
          Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => norm_nonneg _

/-- If every entry of a tensor is at most `m`, its `ℓ²` norm is at most `D³ m`. -/
private lemma LF3_t3_le {D : ℕ} (T : Fin D → Fin D → Fin D → ℂ) (m : ℝ)
    (hm : ∀ a b c, ‖T a b c‖ ≤ m) : ten3Norm T ≤ (D : ℝ) ^ 3 * m := by
  refine (LF3_t3_le_sum T).trans ?_
  calc ∑ a, ∑ b, ∑ c, ‖T a b c‖ ≤ ∑ _a : Fin D, ∑ _b : Fin D, ∑ _c : Fin D, m :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          Finset.sum_le_sum fun c _ => hm a b c
    _ = (D : ℝ) ^ 3 * m := by simp; ring

/-- On the good event at time `s`, the entries of `L_{(i,j,k),s}` with `z_i, z_j, z_k ∈ {z, z̄}`
satisfy (A.53) [entprodG] for three resolvents: `|L_{xya}| ≤ D N^{τ'} Im m_s / η_s²`. -/
private lemma LF3_L3_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z) (τ' : ℝ)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian)
    (hgood : flowGoodAt A z τ' s H) (z₁ z₂ z₃ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (h₃ : z₃ = z ∨ z₃ = star z) (x y a : Fin D) :
    ‖flowLten3 (lam D N A) z₁ z₂ z₃ s H x y a‖ ≤
      (D : ℝ) * ((N : ℝ) ^ τ' * (flowIm (lam D N A) z s /
        (charFlowZ (lam D N A) z s).im ^ 2)) := by
  obtain ⟨b₁, hG₁, -⟩ := LF3_flag hD hN A z hz s hs H hH z₁ h₁
  obtain ⟨b₂, hG₂, -⟩ := LF3_flag hD hN A z hz s hs H hH z₂ h₂
  obtain ⟨b₃, hG₃, -⟩ := LF3_flag hD hN A z hz s hs H hH z₃ h₃
  simp only [flowLten3, Lten3]
  rw [hG₁, hG₂, hG₃, norm_mul, Complex.norm_natCast, LF3_word3]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have h3 := hgood.2.1 3 (by norm_num) (by norm_num) ![b₁, b₂, b₃] ![x, y, a]
  rw [LF3_bndA4 3 (by norm_num)] at h3
  have e : (fun i : Fin 3 => Ea D N (![x, y, a] i)) = ![Ea D N x, Ea D N y, Ea D N a] := by
    funext i; fin_cases i <;> rfl
  rw [e] at h3
  exact h3

/-- `N^{ε_g} / (N q³ (Im m)³) ≤ Im m / η²` when `η ≤ 2 q Im m` and `8 N^{ε_g} ≤ N η Im m`. -/
private lemma LF3_ar_k (N e q ι η : ℝ) (hN : 0 < N) (hq : 0 < q) (hι : 0 < ι) (hη : 0 < η)
    (hηq : η ≤ 2 * q * ι) (he : 8 * e ≤ N * η * ι) :
    e / (N * q ^ 3 * ι ^ 3) ≤ ι / η ^ 2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : N * η * ι ≤ N * (2 * q * ι) * ι := by
    have := mul_le_mul_of_nonneg_left hηq hN.le
    nlinarith
  have h2 : e ≤ N * q * ι ^ 2 / 4 := by nlinarith
  have h3 : η ^ 2 ≤ 4 * q ^ 2 * ι ^ 2 := by nlinarith
  have h4 : e * η ^ 2 ≤ N * q * ι ^ 2 / 4 * η ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (sq_nonneg η)
  have h5 : N * q * ι ^ 2 / 4 * η ^ 2 ≤ N * q * ι ^ 2 / 4 * (4 * q ^ 2 * ι ^ 2) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  nlinarith

/-- The grid with `K = ⌈N^{C}⌉` steps: `N^{C} ≤ K ≤ N^{C+1}` and `K > 0` for `N ≥ 1`. -/
private lemma LF3_K (N : ℕ) (hN : 1 ≤ N) (Cg : ℝ) (hCg : 0 ≤ Cg) :
    (N : ℝ) ^ Cg ≤ (⌈(N : ℝ) ^ Cg⌉₊ : ℝ) ∧ (⌈(N : ℝ) ^ Cg⌉₊ : ℝ) ≤ (N : ℝ) ^ (Cg + 1) ∧
      (0 : ℝ) < (⌈(N : ℝ) ^ Cg⌉₊ : ℝ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hK1 : (N : ℝ) ^ Cg ≤ (⌈(N : ℝ) ^ Cg⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨hK1, ?_, lt_of_lt_of_le (by positivity) hK1⟩
  have h1 : (⌈(N : ℝ) ^ Cg⌉₊ : ℝ) < (N : ℝ) ^ Cg + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : (N : ℝ) ^ (Cg + 1) = (N : ℝ) ^ Cg * N := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  have h3 : 1 ≤ (N : ℝ) ^ Cg := Real.one_le_rpow hNr hCg
  by_cases hN1 : (N : ℝ) = 1
  · rw [h2, hN1, Real.one_rpow, mul_one]
    simp
  · have hN2 : (2 : ℝ) ≤ N := by
      have : (1 : ℕ) < N := by
        rcases Nat.lt_or_ge 1 N with h | h
        · exact h
        · exact absurd (by exact_mod_cast le_antisymm h hN) hN1
      exact_mod_cast this
    rw [h2]; nlinarith

/-- A set of measure less than `1` under a probability measure misses an almost sure property
somewhere: some `ω` lies outside the set and has the property. -/
private lemma LF3_exists_good {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Bad : Set Ω) (P : Ω → Prop) (hP : ∀ᵐ ω ∂μ, P ω) (p : ℝ)
    (hp : p < 1) (hBad : μ Bad ≤ ENNReal.ofReal p) : ∃ ω, ω ∉ Bad ∧ P ω := by
  by_contra hne
  push Not at hne
  have hae : ∀ᵐ ω ∂μ, ω ∈ Bad := hP.mono fun ω hω => by
    by_contra h
    exact hne ω h hω
  have h1 : μ Set.univ ≤ μ Bad := measure_mono_ae (hae.mono fun ω h _ => h)
  rw [measure_univ] at h1
  have h2 : (1 : ENNReal) ≤ ENNReal.ofReal p := h1.trans hBad
  have h3 : ENNReal.ofReal p < 1 := by
    rcases le_or_gt p 0 with h | h
    · rw [ENNReal.ofReal_of_nonpos h]; exact zero_lt_one
    · rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hp
  exact absurd h2 (not_le.2 h3)

set_option maxHeartbeats 1600000 in
-- The arithmetic conditions on `N` and the two exceptional sets are handled together.
/-- The bound on `K_{(1,2,1)}` along the flow used in the proof of Lemma 3.11 [lem_flow_3], from (3.29) [flow_3G_res_2] (`flowL3_grid_paper`) and the
good event (`flowGood_grid`) at one point of positive probability on a grid with horizon `S`. -/
private lemma LF3_k121 (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        ten3Norm (flowKten3 (lam D N A) θ z₁ z₂ z₁ S) ≤
          (N : ℝ) ^ τ' * (flowIm (lam D N A) z S / (charFlowZ (lam D N A) z S).im ^ 2) := by
  intro τ' hτ'
  set τ₁ := τ' / 2 with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  obtain ⟨N₁, hN₁⟩ := flowL3_grid_paper D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    τ₁ hτ₁0 1 one_pos 34 (by norm_num)
  obtain ⟨N₂, hN₂⟩ := flowGood_grid D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    τ₁ hτ₁0 1 one_pos 34 (by norm_num)
  have hev : ∀ᶠ N : ℕ in Filter.atTop, N₁ ≤ N ∧ N₂ ≤ N ∧ 3 ≤ N ∧
      2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧ c * (N : ℝ) ^ (-εg) ≤ 1 ∧
      8 * (N : ℝ) ^ εg ≤ (N : ℝ) ^ (C₀ * εg) ∧
      ((D : ℝ) ^ 3 * (D + 1)) * (N : ℝ) ^ τ₁ ≤ (N : ℝ) ^ τ' := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    exact (Filter.eventually_ge_atTop N₁).and ((Filter.eventually_ge_atTop N₂).and
      ((Filter.eventually_ge_atTop 3).and
      (((t1.const_mul 2).eventually (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and
      (((t2.const_mul c).eventually (Iic_mem_nhds (by simp : c * 0 < 1))).and
      ((LF3_ev_pow _ _ _ (by nlinarith)).and (LF3_ev_pow _ _ _ (by linarith)))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ₀ hμ₀ A z S hadm z₁ z₂ h₁ h₂ => ?_⟩
  obtain ⟨hN1', hN2', hN3, hAN, hcN, h8, hfin⟩ := hN₀ N hN
  have := hμ₀.prob
  have : NeZero D := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hΛ10, -, hz, -, -, hq1, hS0, hSt, hη⟩ :=
    LF3_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  obtain ⟨hηS, hιeq, hι0, -, -, -, -⟩ := LF3_flow D N hD1 hN1 A hΛ10 z hz S hSt S hS0 le_rfl
  have hιS : 0 < flowIm (lam D N A) z S := by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
  have hqS : 0 < flowTc (lam D N A) z - S := by linarith
  have hηle := LF3_eta_le D N hD1 hN1 A hΛ10 z hz S hSt hq1 S hS0 le_rfl
  -- the grid with `K = ⌈N^{34}⌉` steps on `[0, S]`
  obtain ⟨hK1, hK2, hKpos⟩ := LF3_K N hN1 34 (by norm_num)
  set K : ℕ := ⌈(N : ℝ) ^ (34 : ℝ)⌉₊ with hKdef
  have hKs : (K : ℝ) * (S / K) = S := by field_simp
  have hlaw := gridStateA_law D N K μ₀ (S / K) (div_nonneg hS0 hKpos.le) K le_rfl
  rw [hKs] at hlaw
  have hcls : LLClass D N _ _ (blockOULaw D N μ₀ S) :=
    (Classical.choose_spec (llClass_blockOU D C)) N θ μ₀ S hθ0 hθ1 hS0 hμ₀
  have hherm : ∀ᵐ ω ∂(gridLawA D N K μ₀),
      (Matrix.of (gridStateA D N K (S / K) ω K)).IsHermitian := by
    have h := hcls.herm
    rw [← hlaw] at h
    exact (ae_map_iff (LF3_state_meas D N K _ K).aemeasurable LF3_herm_meas).1 h
  have hB1 := hN₁ N hN1' θ hθ0 hθ1 μ₀ hμ₀ A z S hadm K hK1 hK2 z₁ z₂ z₁ h₁ h₂ h₁
  have hB2 := hN₂ N hN2' θ hθ0 hθ1 μ₀ hμ₀ A z S hadm K (by exact_mod_cast hKpos)
    (by simpa using hK2)
  set Bad := {ω : GridΩA D N K | ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ₁ * ((N : ℝ) ^ εg /
        (N * (flowTc (lam D N A) z - k * (S / K)) ^ 3 *
          flowIm (lam D N A) z (k * (S / K)) ^ 3)) <
      ten3Norm (flowLten3 (lam D N A) z₁ z₂ z₁ (k * (S / K)) (gridStateA D N K (S / K) ω k) -
        flowKten3 (lam D N A) θ z₁ z₂ z₁ (k * (S / K)))} ∪
    {ω : GridΩA D N K | ∃ k : ℕ, k ≤ K ∧
      ¬ flowGoodAt A z τ₁ (k * (S / K)) (gridStateA D N K (S / K) ω k)} with hBad
  have hN1e : (N : ℝ) ^ (-(1 : ℝ)) = (N : ℝ)⁻¹ := Real.rpow_neg_one _
  have hBadμ : gridLawA D N K μ₀ Bad ≤ ENNReal.ofReal (2 * (N : ℝ)⁻¹) := by
    refine (measure_union_le _ _).trans ((add_le_add hB1 hB2).trans ?_)
    rw [hN1e, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hp : 2 * (N : ℝ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hNpos]; linarith
  obtain ⟨ω, hω, hωH⟩ := LF3_exists_good _ Bad _ hherm _ hp hBadμ
  simp only [hBad, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and,
    not_lt] at hω
  obtain ⟨hl, hg⟩ := hω
  have hl' := hl K le_rfl
  have hg' := hg K le_rfl
  rw [hKs] at hl' hg'
  rw [not_not] at hg'
  set H := gridStateA D N K (S / K) ω K with hH
  set P := (N : ℝ) ^ τ₁ with hP
  set ι := flowIm (lam D N A) z S with hι
  set η := (charFlowZ (lam D N A) z S).im with hηd
  set q := flowTc (lam D N A) z - S with hq
  have hP0 : 0 ≤ P := by positivity
  -- the entries of `L_{(1,2,1)}` on the good event and the bound on `L - K`
  have hLe : ∀ x y a, ‖flowLten3 (lam D N A) z₁ z₂ z₁ S H x y a‖ ≤ D * (P * (ι / η ^ 2)) :=
    fun x y a => LF3_L3_le D N hD1 hN1 A z hz S hSt τ₁ H hωH hg' z₁ z₂ z₁ h₁ h₂ h₁ x y a
  have hadmS := hadm.2.2.2.2.2.2.2.2
  have he8 : 8 * (N : ℝ) ^ εg ≤ N * η * ι := h8.trans hadmS
  have hW : ten3Norm (flowLten3 (lam D N A) z₁ z₂ z₁ S H -
      flowKten3 (lam D N A) θ z₁ z₂ z₁ S) ≤ P * (ι / η ^ 2) :=
    hl'.trans (mul_le_mul_of_nonneg_left
      (LF3_ar_k N _ q ι η hNpos hqS hιS hηS hηle he8) hP0)
  have hKe : ∀ x y a, ‖flowKten3 (lam D N A) θ z₁ z₂ z₁ S x y a‖ ≤
      D * (P * (ι / η ^ 2)) + P * (ι / η ^ 2) := by
    intro x y a
    have e : flowKten3 (lam D N A) θ z₁ z₂ z₁ S x y a =
        flowLten3 (lam D N A) z₁ z₂ z₁ S H x y a -
          (flowLten3 (lam D N A) z₁ z₂ z₁ S H - flowKten3 (lam D N A) θ z₁ z₂ z₁ S) x y a := by
      simp
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (hLe x y a) ((LF3_t3_entry _ x y a).trans hW))
  refine (LF3_t3_le _ _ hKe).trans ?_
  have hX : 0 ≤ ι / η ^ 2 := by positivity
  calc (D : ℝ) ^ 3 * (D * (P * (ι / η ^ 2)) + P * (ι / η ^ 2))
      = ((D : ℝ) ^ 3 * (D + 1)) * P * (ι / η ^ 2) := by ring
    _ ≤ (N : ℝ) ^ τ' * (ι / η ^ 2) := mul_le_mul_of_nonneg_right hfin hX


/-! ### Lemma 3.11: the objects of the two-resolvent expectation along the flow -/

/-- The fluctuation term of (3.53) [ItowtL]:
`D Σ_a (⟨(G₁ - M₁) E_a⟩ L_{(1,2,1),xya} + ⟨(G₂ - M₂) E_a⟩ L_{(2,1,2),yxa})` at time `s`. -/
private abbrev LF3_err {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (s : ℝ)
    (H : Idx D N → Idx D N → ℂ) (x y : Fin D) : ℂ :=
  (D : ℂ) * ∑ a, (LF3_d Λ z₁ s H a * flowLten3 Λ z₁ z₂ z₁ s H x y a +
    LF3_d Λ z₂ s H a * flowLten3 Λ z₂ z₁ z₂ s H y x a)

/-- The drift `L + L² + err` of `L_{(1,2),s}` in (3.53) [ItowtL], at the state `H`. -/
private abbrev LF3_dr {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (s : ℝ)
    (H : Idx D N → Idx D N → ℂ) (x y : Fin D) : ℂ :=
  flowLmat Λ z₁ z₂ s H x y + (flowLmat Λ z₁ z₂ s H * flowLmat Λ z₁ z₂ s H) x y +
    LF3_err Λ z₁ z₂ s H x y

/-- The fluctuating part of the source: `((L - K)²)_{xy}` plus the fluctuation term with
`L_{(i,j,i)}` replaced by `L_{(i,j,i)} - K_{(i,j,i)}`. -/
private abbrev LF3_g {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ) (s : ℝ)
    (H : Idx D N → Idx D N → ℂ) (x y : Fin D) : ℂ :=
  ((flowLmat Λ z₁ z₂ s H - flowKmat Λ θ z₁ z₂ s) *
      (flowLmat Λ z₁ z₂ s H - flowKmat Λ θ z₁ z₂ s)) x y +
    (D : ℂ) * ∑ a, (LF3_d Λ z₁ s H a *
        (flowLten3 Λ z₁ z₂ z₁ s H x y a - flowKten3 Λ θ z₁ z₂ z₁ s x y a) +
      LF3_d Λ z₂ s H a * (flowLten3 Λ z₂ z₁ z₂ s H y x a - flowKten3 Λ θ z₂ z₁ z₂ s y x a))

/-- `E L_{(1,2),s}` at the law (3.13) [eq:Gauss_div] at time `s`. -/
private abbrev LF3_EL {D N : ℕ} (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (s : ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  ELmat (blockOULaw D N μ₀ s) (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z₁ s)
    (charFlowZ Λ z₂ s)

/-! ### Crude bounds and measurability -/

/-- `‖X₁E₁X₂E₂X₃E₃‖ ≤ r³` when `‖X_i‖ ≤ r` and `‖E_i‖ ≤ 1`. -/
private lemma LF3_op6 {ι : Type*} [Fintype ι] [DecidableEq ι] (X₁ X₂ X₃ E₁ E₂ E₃ : Matrix ι ι ℂ)
    (r : ℝ) (h₁ : opNorm X₁ ≤ r) (h₂ : opNorm X₂ ≤ r) (h₃ : opNorm X₃ ≤ r) (e₁ : opNorm E₁ ≤ 1)
    (e₂ : opNorm E₂ ≤ 1) (e₃ : opNorm E₃ ≤ 1) :
    opNorm (X₁ * E₁ * X₂ * E₂ * X₃ * E₃) ≤ r ^ 3 := by
  have hr : 0 ≤ r := (LF3_op_nonneg _).trans h₁
  have t1 : opNorm (X₁ * E₁) ≤ r :=
    (LF3_op_mul _ _).trans (by nlinarith [LF3_op_nonneg X₁, LF3_op_nonneg E₁])
  have t2 : opNorm (X₁ * E₁ * X₂) ≤ r ^ 2 :=
    (LF3_op_mul _ _).trans (by nlinarith [LF3_op_nonneg (X₁ * E₁), LF3_op_nonneg X₂])
  have t3 : opNorm (X₁ * E₁ * X₂ * E₂) ≤ r ^ 2 :=
    (LF3_op_mul _ _).trans (by nlinarith [LF3_op_nonneg (X₁ * E₁ * X₂), LF3_op_nonneg E₂])
  have t4 : opNorm (X₁ * E₁ * X₂ * E₂ * X₃) ≤ r ^ 3 :=
    (LF3_op_mul _ _).trans (by nlinarith [LF3_op_nonneg (X₁ * E₁ * X₂ * E₂), LF3_op_nonneg X₃])
  exact (LF3_op_mul _ _).trans
    (by nlinarith [LF3_op_nonneg (X₁ * E₁ * X₂ * E₂ * X₃), LF3_op_nonneg E₃, pow_nonneg hr 3])

/-- At a Hermitian state along the flow: `|⟨(G_i - M_i) E_a⟩| ≤ η_s⁻¹ + 5/4`,
`|L_{ab}| ≤ D η_s⁻²` and `|L_{(i,j,k),abc}| ≤ D η_s⁻³` for all flags in `{z, z̄}`. -/
private lemma LF3_crude (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (s : ℝ)
    (hs : s < flowTc (lam D N A) z) (hs0 : 0 ≤ s) (H : Idx D N → Idx D N → ℂ)
    (hH : (Matrix.of H).IsHermitian) :
    (∀ w : ℂ, (w = z ∨ w = star z) → ∀ a : Fin D,
      ‖LF3_d (lam D N A) w s H a‖ ≤ (charFlowZ (lam D N A) z s).im⁻¹ + 5 / 4) ∧
    (∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → ∀ a b : Fin D,
      ‖flowLmat (lam D N A) z₁ z₂ s H a b‖ ≤ D / (charFlowZ (lam D N A) z s).im ^ 2) ∧
    (∀ z₁ z₂ z₃ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (z₃ = z ∨ z₃ = star z) → ∀ a b c : Fin D,
      ‖flowLten3 (lam D N A) z₁ z₂ z₃ s H a b c‖ ≤ D / (charFlowZ (lam D N A) z s).im ^ 3) := by
  have hNe : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  refine ⟨fun w hw a => ?_, fun z₁ z₂ h₁ h₂ a b => LF3_L_le D N hD hN A z hz s hs H hH z₁ z₂
    h₁ h₂ a b, fun z₁ z₂ z₃ h₁ h₂ h₃ a b c => ?_⟩
  · obtain ⟨b, hG, hM⟩ := LF3_flag hD hN A z hz s hs H hH w hw
    have := (LF3_res_bds D N hD hN A hA z hz s hs hs0 H hH a a).2.2.1
    simp only [LF3_d, LF3_G, LF3_M] at this ⊢
    rw [hG, hM, LF3_ntr_pw_sub _ _ _ (LF3_Ea_conj D N a)]
    exact this
  · obtain ⟨b₁, hG₁, -⟩ := LF3_flag hD hN A z hz s hs H hH z₁ h₁
    obtain ⟨b₂, hG₂, -⟩ := LF3_flag hD hN A z hz s hs H hH z₂ h₂
    obtain ⟨b₃, hG₃, -⟩ := LF3_flag hD hN A z hz s hs H hH z₃ h₃
    have hΛ := lam_isHermitian D N A
    have hX : (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A).IsHermitian :=
      hH.add (LF3_herm_smul _ hΛ _)
    have hη := (charFlow_M _ hΛ z hz s hs).1
    have hGn := opNorm_res_le _ hX _ hη
    set G := res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
      (charFlowZ (lam D N A) z s)
    simp only [flowLten3, Lten3]
    rw [hG₁, hG₂, hG₃, norm_mul, Complex.norm_natCast, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine (LF3_ntr_le _).trans ?_
    have g : ∀ b' : Bool, opNorm (LF3_pw G b') ≤ (charFlowZ (lam D N A) z s).im⁻¹ := fun b' => by
      rw [LF3_op_pw]; exact hGn
    refine (LF3_op6 _ _ _ _ _ _ _ (g b₁) (g b₂) (g b₃) (LF3_opNorm_Ea D N a)
      (LF3_opNorm_Ea D N b) (LF3_opNorm_Ea D N c)).trans (le_of_eq ?_)
    rw [inv_pow]

/-- `H ↦ φ(G(w₁), G(w₂))` with `G(w) = (H + Λ - w)⁻¹` is measurable for continuous `φ`. -/
private lemma LF3_res2_meas {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (w₁ w₂ : ℂ)
    (φ : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ → ℂ) (hφ : Continuous φ) :
    Measurable fun H : Idx D N → Idx D N → ℂ =>
      φ (res (Matrix.of H + Λ) w₁, res (Matrix.of H + Λ) w₂) := by
  have : SecondCountableTopology (Matrix (Idx D N) (Idx D N) ℂ) :=
    (inferInstance : SecondCountableTopology (Idx D N → Idx D N → ℂ))
  have hm : ∀ w : ℂ, Measurable fun H : Idx D N → Idx D N → ℂ => res (Matrix.of H + Λ) w := by
    intro w
    unfold res
    have : Continuous fun H : Idx D N → Idx D N → ℂ =>
        Matrix.of H + Λ - w • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
      have : Continuous fun H : Idx D N → Idx D N → ℂ => (Matrix.of H : Matrix _ _ ℂ) :=
        continuous_id
      fun_prop
    exact LF3_inv_meas.comp this.measurable
  exact hφ.measurable.comp ((hm w₁).prodMk (hm w₂))

/-- `(G₁, G₂) ↦ c ⟨G₁ E G₂ F⟩` is continuous. -/
private lemma LF3_cont4 {ι : Type*} [Fintype ι] (E F : Matrix ι ι ℂ) (c : ℂ) :
    Continuous fun p : Matrix ι ι ℂ × Matrix ι ι ℂ => c * ntr (p.1 * E * p.2 * F) :=
  continuous_const.mul (LF3_ntr_cont.comp (((continuous_fst.matrix_mul continuous_const).matrix_mul
    continuous_snd).matrix_mul continuous_const))

/-- `(G₁, G₂) ↦ c ⟨G₁ E G₂ F G₁ J⟩` is continuous. -/
private lemma LF3_cont6 {ι : Type*} [Fintype ι] (E F J : Matrix ι ι ℂ) (c : ℂ) :
    Continuous fun p : Matrix ι ι ℂ × Matrix ι ι ℂ => c * ntr (p.1 * E * p.2 * F * p.1 * J) :=
  continuous_const.mul (LF3_ntr_cont.comp (((((continuous_fst.matrix_mul
    continuous_const).matrix_mul continuous_snd).matrix_mul continuous_const).matrix_mul
      continuous_fst).matrix_mul continuous_const))

/-- `G ↦ ⟨(G - M) E⟩` is continuous. -/
private lemma LF3_cont1 {ι : Type*} [Fintype ι] (M E : Matrix ι ι ℂ) :
    Continuous fun G : Matrix ι ι ℂ => ntr ((G - M) * E) :=
  LF3_ntr_cont.comp ((continuous_id.sub continuous_const).matrix_mul continuous_const)

/-- The entries of `L_{(1,2),s}`, the drift, the source and `⟨(G_i - M_i) E_a⟩` are measurable
functions of the state. -/
private lemma LF3_meas {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ)
    (s : ℝ) :
    (∀ a b : Fin D, Measurable (fun H => flowLmat Λ z₁ z₂ s H a b)) ∧
      (∀ x y : Fin D, Measurable (fun H => LF3_dr Λ z₁ z₂ s H x y)) ∧
      (∀ x y : Fin D, Measurable (fun H => LF3_g Λ θ z₁ z₂ s H x y)) ∧
      ∀ (w : ℂ) (a : Fin D), Measurable (fun H => LF3_d Λ w s H a) := by
  have mL : ∀ (u v : ℂ) (a b : Fin D), Measurable (fun H => flowLmat Λ u v s H a b) := by
    intro u v a b
    let φ : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ → ℂ :=
      fun p => (D : ℂ) * ntr (p.1 * Ea D N a * p.2 * Ea D N b)
    exact LF3_res2_meas (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ u s) (charFlowZ Λ v s) φ
      (LF3_cont4 _ _ _)
  have mT : ∀ (u v : ℂ) (a b c : Fin D), Measurable (fun H => flowLten3 Λ u v u s H a b c) := by
    intro u v a b c
    let φ : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ → ℂ :=
      fun p => (D : ℂ) * ntr (p.1 * Ea D N a * p.2 * Ea D N b * p.1 * Ea D N c)
    exact LF3_res2_meas (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ u s) (charFlowZ Λ v s) φ
      (LF3_cont6 _ _ _ _)
  have md : ∀ (w : ℂ) (a : Fin D), Measurable (fun H => LF3_d Λ w s H a) := by
    intro w a
    let φ : Matrix (Idx D N) (Idx D N) ℂ → ℂ :=
      fun G => ntr ((G - MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ w s)) * Ea D N a)
    exact LF3_res_meas (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ w s) φ (LF3_cont1 _ _)
  refine ⟨mL z₁ z₂, fun x y => ?_, fun x y => ?_, md⟩
  · have e : (fun H => LF3_dr Λ z₁ z₂ s H x y) = fun H => flowLmat Λ z₁ z₂ s H x y +
        (∑ a, flowLmat Λ z₁ z₂ s H x a * flowLmat Λ z₁ z₂ s H a y) +
        (D : ℂ) * ∑ a, (LF3_d Λ z₁ s H a * flowLten3 Λ z₁ z₂ z₁ s H x y a +
          LF3_d Λ z₂ s H a * flowLten3 Λ z₂ z₁ z₂ s H y x a) := by
      funext H; simp only [LF3_dr, LF3_err, Matrix.mul_apply]
    rw [e]
    exact ((mL z₁ z₂ x y).add (Finset.measurable_sum _ fun a _ =>
      (mL z₁ z₂ x a).mul (mL z₁ z₂ a y))).add (measurable_const.mul
        (Finset.measurable_sum _ fun a _ => ((md z₁ a).mul (mT z₁ z₂ x y a)).add
          ((md z₂ a).mul (mT z₂ z₁ y x a))))
  · have e : (fun H => LF3_g Λ θ z₁ z₂ s H x y) = fun H =>
        (∑ a, (flowLmat Λ z₁ z₂ s H x a - flowKmat Λ θ z₁ z₂ s x a) *
          (flowLmat Λ z₁ z₂ s H a y - flowKmat Λ θ z₁ z₂ s a y)) +
        (D : ℂ) * ∑ a, (LF3_d Λ z₁ s H a *
            (flowLten3 Λ z₁ z₂ z₁ s H x y a - flowKten3 Λ θ z₁ z₂ z₁ s x y a) +
          LF3_d Λ z₂ s H a *
            (flowLten3 Λ z₂ z₁ z₂ s H y x a - flowKten3 Λ θ z₂ z₁ z₂ s y x a)) := by
      funext H; simp only [LF3_g, Matrix.mul_apply, Matrix.sub_apply]
    rw [e]
    exact (Finset.measurable_sum _ fun a _ => ((mL z₁ z₂ x a).sub measurable_const).mul
      ((mL z₁ z₂ a y).sub measurable_const)).add (measurable_const.mul
        (Finset.measurable_sum _ fun a _ => ((md z₁ a).mul ((mT z₁ z₂ x y a).sub
          measurable_const)).add ((md z₂ a).mul ((mT z₂ z₁ y x a).sub measurable_const))))


/-! ### One step of the two-resolvent equation in law -/

set_option maxHeartbeats 1600000 in
-- The integrability side conditions of the expansion are handled in one proof.
/-- One step of the two-resolvent equation of Lemma 3.11 [lem_flow_3] in law: for `0 ≤ s`,
`0 < h`, `s + h ≤ S`, `|E L_{s+h} - E L_s - h E(L + L² + err)_s| ≤ K N^{16} h²` entrywise, with
the drift of (3.53) [ItowtL] (`gen_loop2`) and `K` depending on `D`, `τ`, `C`. -/
private lemma LF3_step (D : ℕ) (hD : 1 ≤ D) (τ : ℝ) (hτ : 0 < τ) (C : ℕ → ℝ) :
    ∃ Kst : ℝ, 0 ≤ Kst ∧ ∀ N : ℕ, 2 ≤ N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), opNorm (lam D N A) ≤ 1 / 10 →
      ‖z‖ ≤ τ⁻¹ → 0 < z.im → ‖mExt (lam D N A) z‖ < 1 → flowTc (lam D N A) z ≤ 1 → 0 ≤ S →
      S < flowTc (lam D N A) z →
      (∀ s, 0 ≤ s → s ≤ S → (N : ℝ)⁻¹ < (charFlowZ (lam D N A) z s).im) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      ∀ s h : ℝ, 0 ≤ s → 0 < h → s + h ≤ S → ∀ x y : Fin D,
        ‖LF3_EL μ₀ (lam D N A) z₁ z₂ (s + h) x y - LF3_EL μ₀ (lam D N A) z₁ z₂ s x y -
          (h : ℂ) * ∫ H, LF3_dr (lam D N A) z₁ z₂ s H x y ∂(blockOULaw D N μ₀ s)‖ ≤
          Kst * (N : ℝ) ^ 16 * h ^ 2 := by
  obtain ⟨cR, hcR⟩ := flowLoop_regular
  obtain ⟨KG, hKG⟩ := gaussStepA_expansion_t
  obtain ⟨C', hC'⟩ := llClass_blockOU D C
  set Mom : ℝ := 8 + 8 * (D : ℝ) ^ 2 * |C' 4| with hMom
  set Bc : ℝ := |cR 2| * (2 * (D : ℝ)) ^ 4 * Real.exp 1 * (4 + τ⁻¹) ^ 2 with hBc
  set K0 : ℝ := |KG| * Bc * (2 * (D : ℝ)) ^ 4 * Mom with hK0
  have hMom0 : 0 ≤ Mom := by positivity
  have hBc0 : 0 ≤ Bc := by positivity
  have hK00 : 0 ≤ K0 := by positivity
  refine ⟨D * K0, by positivity, ?_⟩
  intro N hN2 θ hθ0 hθ1 μ₀ hμ₀ A z S hΛ10 hzτ hz hm1 hq1 hS0 hSt hη z₁ z₂ h₁ h₂ s h hs0 hh hsh
    x y
  have : NeZero D := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  have hN1 : 1 ≤ N := by omega
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN1⟩)⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hD1r : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have := hμ₀.prob
  have hΛ : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hSpos : 0 < S := by linarith
  have hsS : s ≤ S := by linarith
  have hh1 : h ≤ 1 := by linarith
  have hs1 : s < flowTc (lam D N A) z := by linarith
  have hsI : s ∈ Set.Icc 0 S := ⟨hs0, hsS⟩
  have hshI : s + h ∈ Set.Icc 0 S := ⟨by linarith, hsh⟩
  have hl : ∀ f ∈ LF3_l (N := N) z₁ z₂ x y, f.2 = z ∨ f.2 = star z := by
    intro f hf
    simp only [LF3_l, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    exacts [h₁, h₂]
  obtain ⟨Ft, hder, hreg⟩ := hcR D N (lam D N A) hΛ z hz (LF3_l z₁ z₂ x y) hl S hS0 hSt
  set F : ℝ → (Idx D N → Idx D N → ℂ) → ℂ := fun r v =>
    flowLoop (lam D N A) (LF3_l z₁ z₂ x y) r v with hF
  have hsub : Set.Icc s (s + h) ⊆ Set.Icc 0 S := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hexp := hKG D N F Ft _ h s hh hh1
    (fun r hr => ⟨(hreg r (hsub hr)).1, (hreg r (hsub hr)).2.1⟩)
    (fun r hr v => (hder r (hsub hr) v).mono hsub)
    (fun r hr j hj1 hj4 v => (hreg r (hsub hr)).2.2.1 j hj1 hj4 v)
    (fun r hr r' hr' v => (hreg r (hsub hr)).2.2.2 r' (hsub hr') v)
  -- the size `B` of the derivatives
  have hB0 := (norm_nonneg _).trans ((hreg s hsI).2.2.1 1 le_rfl (by norm_num) 0).1
  have hBeq : cR (LF3_l (N := N) z₁ z₂ x y).length * ((D : ℝ) * N + 1) ^ 4 *
      Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      ((LF3_l (N := N) z₁ z₂ x y).map fun f => opNorm f.1).prod *
      ((min 1 (charFlowZ (lam D N A) z S).im) ^ ((LF3_l (N := N) z₁ z₂ x y).length + 6))⁻¹ =
      cR 2 * ((D : ℝ) * N + 1) ^ 4 * Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      (opNorm (Ea D N y) * opNorm (Ea D N x)) *
      ((min 1 (charFlowZ (lam D N A) z S).im) ^ 8)⁻¹ := by
    simp only [LF3_l, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
  rw [hBeq] at hB0 hexp
  have hηS := hη S hS0 le_rfl
  have hBle := LF3_ar_B (cR 2) D N (Real.exp (flowTc (lam D N A) z))
    (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A))
    (opNorm (Ea D N y) * opNorm (Ea D N x)) (min 1 (charFlowZ (lam D N A) z S).im) τ hD1r hNr
    (Real.exp_le_exp.2 hq1) (Real.exp_pos _).le
    (by have h1 := norm_nonneg z; have h2 := norm_nonneg (mExt (lam D N A) z)
        have h3 := LF3_op_nonneg (lam D N A); linarith only [h1, h2, h3])
    (by linarith only [hzτ, hm1, hΛ10])
    (mul_nonneg (LF3_op_nonneg _) (LF3_op_nonneg _))
    ((mul_le_mul (LF3_opNorm_Ea D N y) (LF3_opNorm_Ea D N x) (LF3_op_nonneg _)
      zero_le_one).trans_eq (one_mul 1))
    (le_min (inv_le_one_of_one_le₀ (by linarith)) hηS.le)
  set B := cR 2 * ((D : ℝ) * N + 1) ^ 4 * Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      (opNorm (Ea D N y) * opNorm (Ea D N x)) *
      ((min 1 (charFlowZ (lam D N A) z S).im) ^ 8)⁻¹ with hB
  clear_value B
  have hBle' : B ≤ Bc * (N : ℝ) ^ 12 := by
    refine hBle.trans (le_of_eq ?_)
    rw [hBc]; ring
  -- the loop at Hermitian states
  have hFH : ∀ (r : ℝ) (H : Idx D N → Idx D N → ℂ), (Matrix.of H).IsHermitian →
      flowLmat (lam D N A) z₁ z₂ r H x y = (D : ℂ) * F r H := by
    intro r H hH
    have := LF3_Lmat_loop (lam D N A) z₁ z₂ x y r H
    rwa [LF3_hermPart_eq H hH] at this
  -- `|F r v| ≤ N²` on `[0, S]`
  have hFb : ∀ r ∈ Set.Icc 0 S, ∀ v, ‖F r v‖ ≤ (N : ℝ) ^ 2 := by
    intro r hr v
    have hrq : r < flowTc (lam D N A) z := lt_of_le_of_lt hr.2 hSt
    have hb := LF3_L_le D N hD hN1 A z hz r hrq (hermPart v) (LF3_hermPart_herm v) z₁ z₂ h₁ h₂
      x y
    rw [LF3_Lmat_loop, norm_mul, Complex.norm_natCast] at hb
    have hηr := hη r hr.1 hr.2
    have hη0 : 0 < (charFlowZ (lam D N A) z r).im := lt_trans (inv_pos.2 hNpos) hηr
    have h1 : ‖F r v‖ ≤ 1 / (charFlowZ (lam D N A) z r).im ^ 2 := by
      have e : (D : ℝ) / (charFlowZ (lam D N A) z r).im ^ 2 =
          D * (1 / (charFlowZ (lam D N A) z r).im ^ 2) := by ring
      rw [e] at hb
      exact le_of_mul_le_mul_left hb hDpos
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ (N : ℝ) * (charFlowZ (lam D N A) z r).im := by
      rw [inv_lt_iff_one_lt_mul₀ hNpos] at hηr; linarith
    nlinarith
  -- the drift identity for two resolvents (`gen_loop2`)
  have hid : ∀ H : Idx D N → Idx D N → ℂ, (Matrix.of H).IsHermitian →
      (D : ℂ) * (Ft s H + genA (F s) H) = LF3_dr (lam D N A) z₁ z₂ s H x y := by
    intro H hH
    have hd1 : HasDerivWithinAt (fun r => flowLmat (lam D N A) z₁ z₂ r H x y)
        ((D : ℂ) * Ft s H) (Set.Icc 0 S) s :=
      ((hder s hsI H).const_mul (D : ℂ)).congr (fun r _ => hFH r H hH) (hFH s H hH)
    have hd2 : HasDerivAt (fun r : ℝ => flowLmat (lam D N A) z₁ z₂ r H x y)
        (flowLmat (lam D N A) z₁ z₂ s H x y +
          (flowLmat (lam D N A) z₁ z₂ s H * flowLmat (lam D N A) z₁ z₂ s H) x y +
          LF3_err (lam D N A) z₁ z₂ s H x y -
          genA (fun h => flowLmat (lam D N A) z₁ z₂ s (hermPart h) x y) H) s :=
      gen_loop2 D N A z hz s hs1 z₁ z₂ h₁ h₂ H hH x y
    have huniq := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc hSpos s hsI) hd1
      hd2.hasDerivWithinAt
    have hgen : genA (fun h => flowLmat (lam D N A) z₁ z₂ s (hermPart h) x y) H =
        (D : ℂ) * genA (F s) H := by
      have e : (fun h => flowLmat (lam D N A) z₁ z₂ s (hermPart h) x y) =
          fun h => ((D : ℝ) : ℂ) * flowLoop (lam D N A) (LF3_l z₁ z₂ x y) s h := by
        funext h
        rw [LF3_Lmat_loop]
        push_cast
        rfl
      rw [e, LF3_genA_smul _ ((hreg s hsI).1.of_le (by norm_num))]
      push_cast
      rfl
    simp only [LF3_dr]
    linear_combination huniq - hgen
  -- the laws at times `s` and `s + h`
  have hcls := hC' N θ μ₀ s hθ0 hθ1 hs0 hμ₀
  have hclsh := hC' N θ μ₀ (s + h) hθ0 hθ1 (by linarith) hμ₀
  have := hcls.prob
  have := hclsh.prob
  set μs := blockOULaw D N μ₀ s with hμs
  set μsh := blockOULaw D N μ₀ (s + h) with hμsh
  -- measurability and bounds at time `s`
  obtain ⟨mL, mdr, -, -⟩ := LF3_meas (lam D N A) θ z₁ z₂ s
  have hηs := hη s hs0 hsS
  have hηs0 : 0 < (charFlowZ (lam D N A) z s).im := lt_trans (inv_pos.2 hNpos) hηs
  have hηinv : (charFlowZ (lam D N A) z s).im⁻¹ ≤ N := by
    rw [inv_le_comm₀ hηs0 hNpos]; exact hηs.le
  have hcr := LF3_crude D N hD hN1 A hΛ10 z hz s hs1 hs0
  set Md : ℝ := 2 * (N : ℝ) with hMd
  set ML : ℝ := D * (N : ℝ) ^ 2 with hML
  set MT : ℝ := D * (N : ℝ) ^ 3 with hMT
  have hbd : ∀ H : Idx D N → Idx D N → ℂ, (Matrix.of H).IsHermitian →
      (∀ (w : ℂ), (w = z ∨ w = star z) → ∀ a, ‖LF3_d (lam D N A) w s H a‖ ≤ Md) ∧
      (∀ a b, ‖flowLmat (lam D N A) z₁ z₂ s H a b‖ ≤ ML) ∧
      (∀ (u v : ℂ), (u = z ∨ u = star z) → (v = z ∨ v = star z) → ∀ a b c,
        ‖flowLten3 (lam D N A) u v u s H a b c‖ ≤ MT) := by
    intro H hH
    obtain ⟨c1, c2, c3⟩ := hcr H hH
    refine ⟨fun w hw a => (c1 w hw a).trans (by rw [hMd]; linarith),
      fun a b => (c2 z₁ z₂ h₁ h₂ a b).trans ?_,
      fun u v hu hv a b c => (c3 u v u hu hv hu a b c).trans ?_⟩
    · rw [hML, div_eq_mul_inv, ← inv_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 hηs0.le) hηinv 2)
        (Nat.cast_nonneg _)
    · rw [hMT, div_eq_mul_inv, ← inv_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 hηs0.le) hηinv 3)
        (Nat.cast_nonneg _)
  set Mdr : ℝ := ML + D * ML ^ 2 + D * (D * (2 * (Md * MT))) with hMdr
  have hdrb : ∀ H : Idx D N → Idx D N → ℂ, (Matrix.of H).IsHermitian →
      ‖LF3_dr (lam D N A) z₁ z₂ s H x y‖ ≤ Mdr := by
    intro H hH
    obtain ⟨b1, b2, b3⟩ := hbd H hH
    have hML0 : 0 ≤ ML := by positivity
    have hMd0 : 0 ≤ Md := by positivity
    have hLL : ‖(flowLmat (lam D N A) z₁ z₂ s H * flowLmat (lam D N A) z₁ z₂ s H) x y‖ ≤
        D * ML ^ 2 := by
      rw [Matrix.mul_apply]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ a, ‖flowLmat (lam D N A) z₁ z₂ s H x a * flowLmat (lam D N A) z₁ z₂ s H a y‖
          ≤ ∑ _a : Fin D, ML ^ 2 := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_mul, sq]
            exact mul_le_mul (b2 x a) (b2 a y) (norm_nonneg _) hML0
        _ = D * ML ^ 2 := by simp
    have hE : ‖LF3_err (lam D N A) z₁ z₂ s H x y‖ ≤ D * (D * (2 * (Md * MT))) := by
      simp only [LF3_err]
      rw [norm_mul, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (Nat.cast_nonneg _)
      calc ∑ a, ‖LF3_d (lam D N A) z₁ s H a * flowLten3 (lam D N A) z₁ z₂ z₁ s H x y a +
            LF3_d (lam D N A) z₂ s H a * flowLten3 (lam D N A) z₂ z₁ z₂ s H y x a‖
          ≤ ∑ _a : Fin D, 2 * (Md * MT) := by
            refine Finset.sum_le_sum fun a _ => (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
            have t1 := mul_le_mul (b1 z₁ h₁ a) (b3 z₁ z₂ h₁ h₂ x y a) (norm_nonneg _) hMd0
            have t2 := mul_le_mul (b1 z₂ h₂ a) (b3 z₂ z₁ h₂ h₁ y x a) (norm_nonneg _) hMd0
            linarith
        _ = D * (2 * (Md * MT)) := by simp
    simp only [LF3_dr]
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (b2 x y) hLL)) hE)
  -- integrability at time `s`
  have hdr_i : Integrable (fun H => LF3_dr (lam D N A) z₁ z₂ s H x y) μs :=
    LF3_int μs hcls.herm _ (mdr x y) _ hdrb
  have hFc : ∀ r ∈ Set.Icc 0 S, Continuous (F r) := fun r hr => (hreg r hr).1.continuous
  have hFi : ∀ r ∈ Set.Icc 0 S, ∀ μ : Measure (Idx D N → Idx D N → ℂ), IsProbabilityMeasure μ →
      Integrable (F r) μ := fun r hr μ _ =>
    Integrable.of_bound (hFc r hr).aestronglyMeasurable _ (ae_of_all _ fun v => hFb r hr v)
  -- (i) the entries of `E L` through the loop
  have hEL : ∀ r ∈ Set.Icc 0 S, ∀ μ : Measure (Idx D N → Idx D N → ℂ),
      (∀ᵐ H ∂μ, (Matrix.of H).IsHermitian) → μ = blockOULaw D N μ₀ r →
      LF3_EL μ₀ (lam D N A) z₁ z₂ r x y = (D : ℂ) * ∫ H, F r H ∂μ := by
    intro r hr μ hμ e
    have hae : (fun H => flowLmat (lam D N A) z₁ z₂ r H x y) =ᵐ[μ] fun H => (D : ℂ) * F r H :=
      hμ.mono fun H hH => hFH r H hH
    change ∫ H, flowLmat (lam D N A) z₁ z₂ r H x y ∂(blockOULaw D N μ₀ r) = _
    rw [← e, integral_congr_ae hae, integral_const_mul]
  have hv1 := hEL (s + h) hshI μsh hclsh.herm rfl
  have hv0 := hEL s hsI μs hcls.herm rfl
  -- (ii) one step in law
  have hstep := gridExpStepA D N μ₀ s h hs0 hh.le (F (s + h)) (hFc _ hshI).measurable _
    (fun v => hFb _ hshI v)
  set inner : (Idx D N → Idx D N → ℂ) → ℂ := fun H => ∫ X, F (s + h)
    (Real.exp (-h / 2) • H + Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X))
      ∂(gueBlocks D N) with hinner
  have hinner_m : StronglyMeasurable inner := by
    have hφ : Continuous fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
        F (s + h) (Real.exp (-h / 2) • p.1 + Real.sqrt (1 - Real.exp (-h)) • LF3_arrL D N p.2) :=
      (hFc _ hshI).comp ((continuous_const_smul _).comp continuous_fst |>.add
        ((continuous_const_smul _).comp ((LF3_arrL D N).continuous.comp continuous_snd)))
    exact hφ.stronglyMeasurable.integral_prod_right'
  have hinner_i : Integrable inner μs := by
    refine Integrable.of_bound hinner_m.aestronglyMeasurable ((N : ℝ) ^ 2)
      (ae_of_all _ fun H => ?_)
    refine (norm_integral_le_of_norm_le_const (ae_of_all _ fun X => hFb _ hshI _)).trans ?_
    simp
  -- (iii) the expansion, integrated
  set expl : (Idx D N → Idx D N → ℂ) → ℂ := fun H =>
    F s H + (h : ℂ) * ((D : ℂ)⁻¹ * LF3_dr (lam D N A) z₁ z₂ s H x y) with hexpl
  have hexpl_i : Integrable expl μs :=
    (hFi s hsI μs inferInstance).add ((hdr_i.const_mul _).const_mul _)
  have hmom := LF3_mom D N hN1 C' _ μs hcls
  set Rb : (Idx D N → Idx D N → ℂ) → ℝ := fun H =>
    |KG| * B * h ^ 2 * ((D : ℝ) * N + 1) ^ 4 * (1 + ‖H‖) ^ 4 with hRb
  have hRb_i : Integrable Rb μs := by
    have e : Rb = fun H => (|KG| * B * h ^ 2 * ((D : ℝ) * N + 1) ^ 4) * (1 + ‖H‖) ^ 4 := by
      funext H; rfl
    rw [e]; exact hmom.1.const_mul _
  have hpt : ∀ᵐ H ∂μs, ‖inner H - expl H‖ ≤ Rb H := by
    filter_upwards [hcls.herm] with H hH
    have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
    have e1 : inner H - expl H = inner H - F s H - (h : ℂ) * (Ft s H + genA (F s) H) := by
      simp only [hexpl]
      rw [← hid H hH, ← mul_assoc ((D : ℂ)⁻¹), inv_mul_cancel₀ hD0, one_mul]
      ring
    rw [e1]
    refine (hexp H).trans ?_
    simp only [hRb]
    have h0 : 0 ≤ B * h ^ 2 * (1 + ‖H‖) ^ 4 * ((D : ℝ) * N + 1) ^ 4 := by
      have : 0 ≤ B := hB0
      positivity
    calc KG * B * h ^ 2 * (1 + ‖H‖) ^ 4 * ((D : ℝ) * N + 1) ^ 4
        = KG * (B * h ^ 2 * (1 + ‖H‖) ^ 4 * ((D : ℝ) * N + 1) ^ 4) := by ring
      _ ≤ |KG| * (B * h ^ 2 * (1 + ‖H‖) ^ 4 * ((D : ℝ) * N + 1) ^ 4) :=
          mul_le_mul_of_nonneg_right (le_abs_self KG) h0
      _ = _ := by ring
  have hdiff : ‖(∫ H, inner H ∂μs) - ∫ H, expl H ∂μs‖ ≤ K0 * (N : ℝ) ^ 16 * h ^ 2 := by
    rw [← integral_sub hinner_i hexpl_i]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (ae_of_all _ fun H => norm_nonneg _) hRb_i hpt).trans ?_
    have e : ∫ H, Rb H ∂μs = |KG| * B * h ^ 2 * ((D : ℝ) * N + 1) ^ 4 *
        ∫ H, (1 + ‖H‖) ^ 4 ∂μs := by
      simp only [hRb]; rw [integral_const_mul]
    rw [e]
    have hDN : ((D : ℝ) * N + 1) ^ 4 ≤ (2 * (D : ℝ)) ^ 4 * (N : ℝ) ^ 4 := by
      have h1 : (D : ℝ) * N + 1 ≤ 2 * D * N := by nlinarith
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1 4
    have hI0 : 0 ≤ ∫ H, (1 + ‖H‖) ^ 4 ∂μs := integral_nonneg fun H => by positivity
    have hB00 : 0 ≤ B := hB0
    calc |KG| * B * h ^ 2 * ((D : ℝ) * N + 1) ^ 4 * ∫ H, (1 + ‖H‖) ^ 4 ∂μs
        ≤ |KG| * (Bc * (N : ℝ) ^ 12) * h ^ 2 * ((2 * (D : ℝ)) ^ 4 * (N : ℝ) ^ 4) * Mom := by
          gcongr
          exact hmom.2
      _ = K0 * (N : ℝ) ^ 16 * h ^ 2 := by rw [hK0]; ring
  -- (iv) the integral of the expansion
  have hexplv : ∫ H, expl H ∂μs = (∫ H, F s H ∂μs) + (h : ℂ) * ((D : ℂ)⁻¹ *
      ∫ H, LF3_dr (lam D N A) z₁ z₂ s H x y ∂μs) := by
    simp only [hexpl]
    rw [integral_add (hFi s hsI μs inferInstance) ((hdr_i.const_mul _).const_mul _),
      integral_const_mul, integral_const_mul]
  -- assembly
  have hkey : LF3_EL μ₀ (lam D N A) z₁ z₂ (s + h) x y - LF3_EL μ₀ (lam D N A) z₁ z₂ s x y -
      (h : ℂ) * ∫ H, LF3_dr (lam D N A) z₁ z₂ s H x y ∂μs =
      (D : ℂ) * ((∫ H, inner H ∂μs) - ∫ H, expl H ∂μs) := by
    have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
    rw [hv1, hv0, hstep, hexplv]
    field_simp
    ring
  rw [hkey, norm_mul, Complex.norm_natCast]
  calc (D : ℝ) * ‖(∫ H, inner H ∂μs) - ∫ H, expl H ∂μs‖
      ≤ D * (K0 * (N : ℝ) ^ 16 * h ^ 2) := mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg _)
    _ = D * K0 * (N : ℝ) ^ 16 * h ^ 2 := by ring


/-! ### The deterministic step, the linear decomposition and the sources -/

/-- The one-step error of the Riccati equation `dK/dt = K² + K` of `K_{θ_t}(z_{1,t}, z_{2,t})`
along the flow: for `[u, u + h] ⊂ [0, S]`, `|K_{u+h} - K_u - h (K_u² + K_u)| ≤ L h²` entrywise,
with `L = (D ρ² + ρ)(1 + 2 D ρ)` and `ρ = (t_c - t₀ - S)⁻¹`. -/
private lemma LF3_Kd (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (θ : ℝ) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z)
    (u h : ℝ) (hu : 0 ≤ u) (hh : 0 ≤ h) (huh : u + h ≤ S) (a b : Fin D) :
    ‖(flowKmat (lam D N A) θ z₁ z₂ (u + h) - flowKmat (lam D N A) θ z₁ z₂ u -
        (h : ℂ) • (flowKmat (lam D N A) θ z₁ z₂ u * flowKmat (lam D N A) θ z₁ z₂ u +
          flowKmat (lam D N A) θ z₁ z₂ u)) a b‖ ≤
      ((D : ℝ) * (flowTc (lam D N A) z - S)⁻¹ ^ 2 + (flowTc (lam D N A) z - S)⁻¹) *
        (1 + 2 * D * (flowTc (lam D N A) z - S)⁻¹) * h ^ 2 := by
  set q₀ := flowTc (lam D N A) z with hq₀
  set ρ := (q₀ - S)⁻¹ with hρ
  set R := LF3_R (Mhat (lam D N A) z₁ z₂) θ with hRdef
  have hqS : 0 < q₀ - S := by linarith
  have hρ0 : 0 < ρ := inv_pos.2 hqS
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hfac : ∀ t ∈ Set.Icc 0 S, flowKmat (lam D N A) θ z₁ z₂ t = R t ∧
      (∀ c d : Fin D, HasDerivAt (fun r => R r c d) ((R t * R t + R t) c d) t) ∧
      ∀ c d : Fin D, ‖R t c d‖ ≤ ρ := by
    intro t ht
    obtain ⟨e1, e2, e3⟩ := LF3_flowK D N A hA z hz S hS θ hθ₀ hθ₁ z₁ z₂ h₁ h₂ t ht.1 ht.2
    refine ⟨e1, e2, fun c d => ?_⟩
    have e4 := e3 c d
    rw [e1] at e4
    refine e4.trans ?_
    exact inv_anti₀ hqS (by linarith [ht.2])
  have hRR : ∀ t ∈ Set.Icc 0 S, ∀ c d : Fin D, ‖(R t * R t) c d‖ ≤ D * ρ ^ 2 := by
    intro t ht c d
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ e, ‖R t c e * R t e d‖ ≤ ∑ _e : Fin D, ρ ^ 2 := by
          refine Finset.sum_le_sum fun e _ => ?_
          rw [norm_mul, sq]
          exact mul_le_mul ((hfac t ht).2.2 c e) ((hfac t ht).2.2 e d) (norm_nonneg _) hρ0.le
      _ = D * ρ ^ 2 := by simp
  have hP : ∀ t ∈ Set.Icc 0 S, ∀ c d : Fin D, ‖(R t * R t + R t) c d‖ ≤ D * ρ ^ 2 + ρ := by
    intro t ht c d
    rw [Matrix.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (hRR t ht c d) ((hfac t ht).2.2 c d))
  have hRlip : ∀ t ∈ Set.Icc 0 S, ∀ u ∈ Set.Icc 0 S, ∀ c d : Fin D,
      ‖R t c d - R u c d‖ ≤ (D * ρ ^ 2 + ρ) * |t - u| := by
    intro t ht u hu c d
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r => R r c d) (f' := fun r => (R r * R r + R r) c d)
      (fun x hx => ((hfac x hx).2.1 c d).hasDerivWithinAt) (fun x hx => hP x hx c d)
      (convex_Icc 0 S) hu ht
    simpa [Real.norm_eq_abs] using this
  have hRRlip : ∀ t ∈ Set.Icc 0 S, ∀ u ∈ Set.Icc 0 S,
      ‖(R t * R t) a b - (R u * R u) a b‖ ≤ D * (2 * ρ * ((D * ρ ^ 2 + ρ) * |t - u|)) := by
    intro t ht u hu
    simp only [Matrix.mul_apply, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ e, ‖R t a e * R t e b - R u a e * R u e b‖
        ≤ ∑ _e : Fin D, 2 * ρ * ((D * ρ ^ 2 + ρ) * |t - u|) := by
          refine Finset.sum_le_sum fun e _ => ?_
          have e1 : R t a e * R t e b - R u a e * R u e b =
              (R t a e - R u a e) * R t e b + R u a e * (R t e b - R u e b) := by ring
          rw [e1]
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          have l1 := hRlip t ht u hu a e
          have l2 := hRlip t ht u hu e b
          have b1 := (hfac t ht).2.2 e b
          have b2 := (hfac u hu).2.2 a e
          have hL0 : 0 ≤ (D * ρ ^ 2 + ρ) * |t - u| := by positivity
          nlinarith [norm_nonneg (R t a e - R u a e), norm_nonneg (R u a e),
            norm_nonneg (R t e b), norm_nonneg (R t e b - R u e b)]
      _ = D * (2 * ρ * ((D * ρ ^ 2 + ρ) * |t - u|)) := by simp
  set Kp : ℝ → ℂ := fun t => (R t * R t + R t) a b with hKp
  have hKplip : ∀ t ∈ Set.Icc 0 S, ∀ u ∈ Set.Icc 0 S,
      ‖Kp t - Kp u‖ ≤ ((D : ℝ) * ρ ^ 2 + ρ) * (1 + 2 * D * ρ) * |t - u| := by
    intro t ht u hu
    have e1 : Kp t - Kp u = ((R t * R t) a b - (R u * R u) a b) + (R t a b - R u a b) := by
      simp only [hKp, Matrix.add_apply]; ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have l1 := hRlip t ht u hu a b
    have l2 := hRRlip t ht u hu
    calc ‖(R t * R t) a b - (R u * R u) a b‖ + ‖R t a b - R u a b‖
        ≤ D * (2 * ρ * ((D * ρ ^ 2 + ρ) * |t - u|)) + (D * ρ ^ 2 + ρ) * |t - u| :=
          add_le_add l2 l1
      _ = _ := by ring
  have hsub : Set.Icc u (u + h) ⊆ Set.Icc 0 S := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have huI : u ∈ Set.Icc 0 S := ⟨hu, by linarith⟩
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := ((D : ℝ) * ρ ^ 2 + ρ) * (1 + 2 * D * ρ) * h)
    (f := fun r => R r a b - (r : ℂ) * Kp u)
    (f' := fun r => Kp r - Kp u)
    (fun x hx => by
      have h1 := (hfac x (hsub hx)).2.1 a b
      have h2 : HasDerivAt (fun r : ℝ => (r : ℂ) * Kp u) (1 * Kp u) x :=
        (hasDerivAt_id x).ofReal_comp.mul_const _ |>.congr_deriv (by simp)
      exact (h1.sub h2).hasDerivWithinAt.congr_deriv (by simp [hKp]))
    (fun x hx => by
      refine (hKplip x (hsub hx) u huI).trans ?_
      have : |x - u| ≤ h := by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
      have hL : 0 ≤ ((D : ℝ) * ρ ^ 2 + ρ) * (1 + 2 * D * ρ) := by positivity
      exact mul_le_mul_of_nonneg_left this hL)
    (convex_Icc u (u + h)) (⟨le_rfl, by linarith⟩ : u ∈ Set.Icc u (u + h))
    (⟨by linarith, le_rfl⟩ : u + h ∈ Set.Icc u (u + h))
  have hKu := (hfac u huI).1
  have hKuh := (hfac (u + h) ⟨by linarith, huh⟩).1
  rw [hKu, hKuh]
  have e2 : (R (u + h) - R u - (h : ℂ) • (R u * R u + R u)) a b =
      (R (u + h) a b - ((u + h : ℝ) : ℂ) * Kp u) - (R u a b - (u : ℂ) * Kp u) := by
    simp only [hKp, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [e2]
  refine hmv.trans (le_of_eq ?_)
  rw [show u + h - u = h by ring, Real.norm_eq_abs, abs_of_nonneg hh]
  ring

/-- The drift splits into its linear part and the sources: at a law of Hermitian arrays at
time `s`, `E(L + L² + err)_{xy} = (E L + K E L + E L K - K²)_{xy} + E g_{xy} +
D Σ_a (E⟨(G₁ - M₁) E_a⟩ K_{(1,2,1),xya} + E⟨(G₂ - M₂) E_a⟩ K_{(2,1,2),yxa})`, with
`K = K_{θ_s}(z_{1,s}, z_{2,s})`. -/
private lemma LF3_lin (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (s : ℝ)
    (hs : s < flowTc (lam D N A) z) (hs0 : 0 ≤ s) (θ : ℝ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure (blockOULaw D N μ₀ s)]
    (hμ : ∀ᵐ H ∂(blockOULaw D N μ₀ s), (Matrix.of H).IsHermitian) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (x y : Fin D) :
    ∫ H, LF3_dr (lam D N A) z₁ z₂ s H x y ∂(blockOULaw D N μ₀ s) =
      LF3_EL μ₀ (lam D N A) z₁ z₂ s x y +
        (flowKmat (lam D N A) θ z₁ z₂ s * LF3_EL μ₀ (lam D N A) z₁ z₂ s) x y +
        (LF3_EL μ₀ (lam D N A) z₁ z₂ s * flowKmat (lam D N A) θ z₁ z₂ s) x y -
        (flowKmat (lam D N A) θ z₁ z₂ s * flowKmat (lam D N A) θ z₁ z₂ s) x y +
        ((∫ H, LF3_g (lam D N A) θ z₁ z₂ s H x y ∂(blockOULaw D N μ₀ s)) +
          (D : ℂ) * ∑ a, ((∫ H, LF3_d (lam D N A) z₁ s H a ∂(blockOULaw D N μ₀ s)) *
              flowKten3 (lam D N A) θ z₁ z₂ z₁ s x y a +
            (∫ H, LF3_d (lam D N A) z₂ s H a ∂(blockOULaw D N μ₀ s)) *
              flowKten3 (lam D N A) θ z₂ z₁ z₂ s y x a)) := by
  set μ := blockOULaw D N μ₀ s with hμdef
  set Λ := lam D N A with hΛdef
  set L := fun H => flowLmat Λ z₁ z₂ s H with hL
  set K := flowKmat Λ θ z₁ z₂ s with hK
  set K₁ := flowKten3 Λ θ z₁ z₂ z₁ s with hK₁
  set K₂ := flowKten3 Λ θ z₂ z₁ z₂ s with hK₂
  obtain ⟨mL, -, mg, md⟩ := LF3_meas Λ θ z₁ z₂ s
  have hcr := LF3_crude D N hD hN A hA z hz s hs hs0
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hη := (charFlow_M _ (lam_isHermitian D N A) z hz s hs).1
  have hη1 : 0 ≤ (charFlowZ Λ z s).im⁻¹ + 5 / 4 := by have := inv_pos.2 hη; linarith
  -- integrability of the entries of `L`, of the source and of `⟨(G_i - M_i) E_a⟩`
  have iL : ∀ a b, Integrable (fun H => L H a b) μ := fun a b =>
    LF3_int μ hμ _ (mL a b) _ fun H hH => (hcr H hH).2.1 z₁ z₂ h₁ h₂ a b
  have id : ∀ (w : ℂ), (w = z ∨ w = star z) → ∀ a, Integrable (fun H => LF3_d Λ w s H a) μ :=
    fun w hw a => LF3_int μ hμ _ (md w a) _ fun H hH => (hcr H hH).1 w hw a
  have ig : Integrable (fun H => LF3_g Λ θ z₁ z₂ s H x y) μ := by
    refine LF3_int μ hμ _ (mg x y) ((∑ a : Fin D, ((D / (charFlowZ Λ z s).im ^ 2 + ‖K x a‖) *
        (D / (charFlowZ Λ z s).im ^ 2 + ‖K a y‖))) + D * ∑ a : Fin D,
          (((charFlowZ Λ z s).im⁻¹ + 5 / 4) * (D / (charFlowZ Λ z s).im ^ 3 + ‖K₁ x y a‖) +
            ((charFlowZ Λ z s).im⁻¹ + 5 / 4) * (D / (charFlowZ Λ z s).im ^ 3 + ‖K₂ y x a‖))) ?_
    intro H hH
    obtain ⟨c1, c2, c3⟩ := hcr H hH
    simp only [LF3_g, Matrix.mul_apply, Matrix.sub_apply]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun a _ => ?_)) ?_)
    · rw [norm_mul]
      exact mul_le_mul ((norm_sub_le _ _).trans (add_le_add (c2 z₁ z₂ h₁ h₂ x a) le_rfl))
        ((norm_sub_le _ _).trans (add_le_add (c2 z₁ z₂ h₁ h₂ a y) le_rfl)) (norm_nonneg _)
        (by positivity)
    · rw [norm_mul, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun a _ => (norm_add_le _ _).trans (add_le_add ?_ ?_)))
        (Nat.cast_nonneg _)
      · rw [norm_mul]
        exact mul_le_mul (c1 z₁ h₁ a) ((norm_sub_le _ _).trans
          (add_le_add (c3 z₁ z₂ z₁ h₁ h₂ h₁ x y a) le_rfl)) (norm_nonneg _) (by positivity)
      · rw [norm_mul]
        exact mul_le_mul (c1 z₂ h₂ a) ((norm_sub_le _ _).trans
          (add_le_add (c3 z₂ z₁ z₂ h₂ h₁ h₂ y x a) le_rfl)) (norm_nonneg _) (by positivity)
  -- the pointwise identity
  have hpt : ∀ H, LF3_dr Λ z₁ z₂ s H x y = L H x y - (K * K) x y + LF3_g Λ θ z₁ z₂ s H x y +
      ∑ a, (K x a * L H a y + L H x a * K a y + (D : ℂ) * (LF3_d Λ z₁ s H a * K₁ x y a +
        LF3_d Λ z₂ s H a * K₂ y x a)) := by
    intro H
    simp only [hL, LF3_dr, LF3_err, LF3_g, Matrix.mul_apply, Matrix.sub_apply]
    simp only [← hK, ← hK₁, ← hK₂]
    simp only [Finset.mul_sum, mul_add, mul_sub, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring
  -- integration
  have hEL : ∀ a b, LF3_EL μ₀ Λ z₁ z₂ s a b = ∫ H, L H a b ∂μ := fun a b => rfl
  have i1 : Integrable (fun H => L H x y - (K * K) x y) μ := (iL x y).sub (integrable_const _)
  have i1' : Integrable (fun H => L H x y - (K * K) x y + LF3_g Λ θ z₁ z₂ s H x y) μ := i1.add ig
  have iS : ∀ a, Integrable (fun H => K x a * L H a y + L H x a * K a y + (D : ℂ) *
      (LF3_d Λ z₁ s H a * K₁ x y a + LF3_d Λ z₂ s H a * K₂ y x a)) μ := fun a =>
    (((iL a y).const_mul _).add ((iL x a).mul_const _)).add
      ((((id z₁ h₁ a).mul_const _).add ((id z₂ h₂ a).mul_const _)).const_mul _)
  have i2 : Integrable (fun H => ∑ a, (K x a * L H a y + L H x a * K a y + (D : ℂ) *
      (LF3_d Λ z₁ s H a * K₁ x y a + LF3_d Λ z₂ s H a * K₂ y x a))) μ :=
    integrable_finsetSum _ fun a _ => iS a
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add i1' i2, integral_add i1 ig,
    integral_sub (iL x y) (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_finsetSum _ fun a _ => iS a]
  have e3 : ∀ a ∈ Finset.univ, ∫ H, (K x a * L H a y + L H x a * K a y + (D : ℂ) *
      (LF3_d Λ z₁ s H a * K₁ x y a + LF3_d Λ z₂ s H a * K₂ y x a)) ∂μ =
      K x a * LF3_EL μ₀ Λ z₁ z₂ s a y + LF3_EL μ₀ Λ z₁ z₂ s x a * K a y +
        (D : ℂ) * ((∫ H, LF3_d Λ z₁ s H a ∂μ) * K₁ x y a +
          (∫ H, LF3_d Λ z₂ s H a ∂μ) * K₂ y x a) := by
    intro a _
    have j1 : Integrable (fun H => K x a * L H a y) μ := (iL a y).const_mul _
    have j2 : Integrable (fun H => L H x a * K a y) μ := (iL x a).mul_const _
    have j3 : Integrable (fun H => LF3_d Λ z₁ s H a * K₁ x y a) μ := (id z₁ h₁ a).mul_const _
    have j4 : Integrable (fun H => LF3_d Λ z₂ s H a * K₂ y x a) μ := (id z₂ h₂ a).mul_const _
    have j12 : Integrable (fun H => K x a * L H a y + L H x a * K a y) μ := j1.add j2
    have j34 : Integrable (fun H => (D : ℂ) * (LF3_d Λ z₁ s H a * K₁ x y a +
        LF3_d Λ z₂ s H a * K₂ y x a)) μ := (j3.add j4).const_mul _
    rw [integral_add j12 j34, integral_add j1 j2, integral_const_mul, integral_mul_const,
      integral_const_mul, integral_add j3 j4, integral_mul_const, integral_mul_const, hEL, hEL]
  rw [Finset.sum_congr rfl e3, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← hEL x y]
  generalize ∫ H, LF3_g Λ θ z₁ z₂ s H x y ∂μ = Ig
  simp only [Matrix.mul_apply]
  ring

/-- `|E⟨(G(z̄_s) - M(z̄_s)) E_a⟩| = |E⟨(G(z_s) - M(z_s)) E_a⟩|` for a law of Hermitian arrays:
`G(z̄_s) = G(z_s)^*` and `M(z̄_s) = M(z_s)^*`. -/
private lemma LF3_dconj (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z)
    (μ : Measure (Idx D N → Idx D N → ℂ)) (hμ : ∀ᵐ H ∂μ, (Matrix.of H).IsHermitian) (w : ℂ)
    (hw : w = z ∨ w = star z) (a : Fin D) :
    ‖∫ H, LF3_d (lam D N A) w s H a ∂μ‖ = ‖∫ H, LF3_d (lam D N A) z s H a ∂μ‖ := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  rcases hw with rfl | rfl
  · rfl
  have hΛ := lam_isHermitian D N A
  have hwpos := (charFlow_M (lam D N A) hΛ z hz s hs).1
  have hae : (fun H => LF3_d (lam D N A) (star z) s H a) =ᵐ[μ]
      fun H => starRingEnd ℂ (LF3_d (lam D N A) z s H a) := by
    filter_upwards [hμ] with H hH
    have hX : (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A).IsHermitian :=
      hH.add (LF3_herm_smul _ hΛ _)
    simp only [LF3_d, LF3_G, LF3_M]
    rw [charFlowZ_conj _ z hz s, Complex.star_def, res_conj _ hX _ hwpos,
      ← Complex.star_def, (mExt_conj _ (LF3_herm_smul _ hΛ _) _ hwpos.ne').2]
    have e : ((res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
        (charFlowZ (lam D N A) z s))ᴴ - (MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s))ᴴ) * Ea D N a =
        (Ea D N a * (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s) - MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
            (charFlowZ (lam D N A) z s)))ᴴ := by
      rw [Matrix.conjTranspose_mul, LF3_Ea_conj, Matrix.conjTranspose_sub]
    rw [e, LF3_ntr_conj, LF3_ntr_comm, Complex.star_def]
  rw [integral_congr_ae hae, integral_conj, Complex.norm_conj]


/-- At a Hermitian state, `|⟨(G(z_{i,s}) - M(z_{i,s})) E_a⟩| = |⟨(G(z_s) - M(z_s)) E_a⟩|` for
`z_i ∈ {z, z̄}`. -/
private lemma LF3_d_eq (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian) (w : ℂ)
    (hw : w = z ∨ w = star z) (a : Fin D) :
    ‖LF3_d (lam D N A) w s H a‖ = ‖LF3_d (lam D N A) z s H a‖ := by
  obtain ⟨b, hG, hM⟩ := LF3_flag hD hN A z hz s hs H hH w hw
  simp only [LF3_d, LF3_G, LF3_M]
  rw [hG, hM, LF3_ntr_pw_sub _ _ _ (LF3_Ea_conj D N a)]

/-- The arithmetic of the fluctuating source on the good event:
`D β₂² + 2 D² β₀ β₃ ≤ (D + 2 D²) P² E² / (N² q⁴ ι⁴)` for `β₂ = P E/(N q² ι²)`,
`β₀ = P/(N η)`, `β₃ = P E/(N q³ ι³)`, `η ≥ q ι` and `E ≥ 1`. -/
private lemma LF3_ar_g (D N P E q ι η X Y : ℝ) (hD : 0 ≤ D) (hN : 0 < N) (hP : 0 ≤ P)
    (hE : 1 ≤ E) (hq : 0 < q) (hι : 0 < ι) (hη : 0 < η) (hqι : q * ι ≤ η)
    (hX : X ≤ D * (P * (E / (N * q ^ 2 * ι ^ 2))) ^ 2)
    (hY : Y ≤ D * (D * (2 * (P / (N * η) * (P * (E / (N * q ^ 3 * ι ^ 3))))))) :
    X + Y ≤ (D + 2 * D ^ 2) * (P * P * (E * E) / (N ^ 2 * q ^ 4 * ι ^ 4)) := by
  set W := P * P * (E * E) / (N ^ 2 * q ^ 4 * ι ^ 4) with hW
  have hW0 : 0 ≤ W := by positivity
  have h1 : (P * (E / (N * q ^ 2 * ι ^ 2))) ^ 2 = W := by rw [hW]; field_simp
  have h2 : P / (N * η) * (P * (E / (N * q ^ 3 * ι ^ 3))) ≤ W := by
    have e : P / (N * η) * (P * (E / (N * q ^ 3 * ι ^ 3))) =
        P * P * E / (N ^ 2 * (η * q ^ 3 * ι ^ 3)) := by field_simp
    rw [e, hW]
    have hden : N ^ 2 * (q ^ 3 * ι ^ 3 * (q * ι)) ≤ N ^ 2 * (η * q ^ 3 * ι ^ 3) := by
      have := mul_le_mul_of_nonneg_left hqι (by positivity : (0 : ℝ) ≤ q ^ 3 * ι ^ 3)
      nlinarith [pow_pos hN 2]
    calc P * P * E / (N ^ 2 * (η * q ^ 3 * ι ^ 3))
        ≤ P * P * E / (N ^ 2 * (q ^ 3 * ι ^ 3 * (q * ι))) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ P * P * (E * E) / (N ^ 2 * (q ^ 3 * ι ^ 3 * (q * ι))) := by
          gcongr
          nlinarith
      _ = P * P * (E * E) / (N ^ 2 * q ^ 4 * ι ^ 4) := by ring_nf
  rw [h1] at hX
  have : D * (D * (2 * (P / (N * η) * (P * (E / (N * q ^ 3 * ι ^ 3)))))) ≤ D * (D * (2 * W)) := by
    gcongr
  nlinarith

set_option maxHeartbeats 1600000 in
-- The arithmetic conditions on `N` and the four exceptional sets are handled together.
/-- The fluctuating source of Lemma 3.11 [lem_flow_3] in expectation: at every time `s ≤ S`,
`|E g_{xy}| ≤ (D + 2D²) N^{2τ₁} N^{2ε_g} / (N² q_s⁴ (Im m_s)⁴) + 48 D³ N⁴ N^{-10}`, from (3.27)
[flow_1_result_2], (3.29) [flow_3G_res_2] and the good event on one grid with horizon `s`. -/
private lemma LF3_srcG (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ₁ : ℝ, 0 < τ₁ → τ₁ ≤ 1 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ s : ℝ, 0 ≤ s → s ≤ S → ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      ∀ x y : Fin D,
        ‖∫ H, LF3_g (lam D N A) θ z₁ z₂ s H x y ∂(blockOULaw D N μ₀ s)‖ ≤
          (D + 2 * D ^ 2) * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁ * ((N : ℝ) ^ εg * (N : ℝ) ^ εg) /
            ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - s) ^ 4 * flowIm (lam D N A) z s ^ 4)) +
          12 * (D : ℝ) ^ 3 * (N : ℝ) ^ 4 * (4 * (N : ℝ) ^ (-(10 : ℝ))) := by
  intro τ₁ hτ₁ hτ₁1
  obtain ⟨Ng, hNg⟩ := flowGood_grid D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    τ₁ hτ₁ 10 (by norm_num) 44 (by norm_num)
  obtain ⟨Nl, hNl⟩ := flowL2_grid_paper D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    τ₁ hτ₁ 10 (by norm_num) 44 (by norm_num)
  obtain ⟨N3, hN3⟩ := flowL3_grid_paper D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    τ₁ hτ₁ 10 (by norm_num) 44 (by norm_num)
  obtain ⟨Nk, hNk⟩ := LF3_k121 D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C τ₁ hτ₁
  have hev : ∀ᶠ N : ℕ in Filter.atTop, Ng ≤ N ∧ Nl ≤ N ∧ N3 ≤ N ∧ Nk ≤ N ∧ 2 ≤ N ∧
      2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧ c * (N : ℝ) ^ (-εg) ≤ 1 := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    exact (Filter.eventually_ge_atTop Ng).and ((Filter.eventually_ge_atTop Nl).and
      ((Filter.eventually_ge_atTop N3).and ((Filter.eventually_ge_atTop Nk).and
      ((Filter.eventually_ge_atTop 2).and
      (((t1.const_mul 2).eventually (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and
      ((t2.const_mul c).eventually (Iic_mem_nhds (by simp : c * 0 < 1))))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ₀ hμ₀ A z S hadm s hs0 hsS z₁ z₂ h₁ h₂ x y => ?_⟩
  obtain ⟨hNg', hNl', hN3', hNk', hN2, hAN, hcN⟩ := hN₀ N hN
  have := hμ₀.prob
  have : NeZero D := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  have hD2r : (2 : ℝ) ≤ D := by exact_mod_cast hD
  obtain ⟨hΛ10, -, hz, -, -, hq1, hS0, hSt, hη⟩ :=
    LF3_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  have hadms := LF3_adm_mono D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
    s hs0 hsS
  have hs1 : s < flowTc (lam D N A) z := lt_of_le_of_lt hsS hSt
  obtain ⟨hηs0, hιeq, hι0, hιs1, -, -, hqι⟩ := LF3_flow D N hD1 hN1 A hΛ10 z hz S hSt s hs0 hsS
  have hιs : 0 < flowIm (lam D N A) z s := by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
  have hqs : 0 < flowTc (lam D N A) z - s := by linarith
  have hηN := (hη s hs0 hsS).1
  have hηinv : (charFlowZ (lam D N A) z s).im⁻¹ ≤ N := by
    rw [inv_le_comm₀ hηs0 hNpos]; exact hηN.le
  have hqinv : (flowTc (lam D N A) z - s)⁻¹ ≤ 2 * N := by
    have hle := LF3_eta_le D N hD1 hN1 A hΛ10 z hz S hSt hq1 s hs0 hsS
    rw [inv_le_comm₀ hqs (by positivity)]
    have h1 : (2 * (N : ℝ))⁻¹ < (charFlowZ (lam D N A) z s).im / 2 := by
      rw [mul_inv]; linarith [inv_pos.2 (show (0 : ℝ) < 2 by norm_num)]
    have h2 : (charFlowZ (lam D N A) z s).im / 2 ≤ flowTc (lam D N A) z - s := by
      have : (charFlowZ (lam D N A) z s).im ≤ 2 * (flowTc (lam D N A) z - s) := by nlinarith
      linarith
    linarith
  -- the grid with horizon `s`
  obtain ⟨hK1, hK2, hKpos⟩ := LF3_K N hN1 44 (by norm_num)
  set K : ℕ := ⌈(N : ℝ) ^ (44 : ℝ)⌉₊ with hKdef
  have hKs : (K : ℝ) * (s / K) = s := by field_simp
  have hlaw := gridStateA_law D N K μ₀ (s / K) (div_nonneg hs0 hKpos.le) K le_rfl
  rw [hKs] at hlaw
  have hcls : LLClass D N _ _ (blockOULaw D N μ₀ s) :=
    (Classical.choose_spec (llClass_blockOU D C)) N θ μ₀ s hθ0 hθ1 hs0 hμ₀
  have hherm : ∀ᵐ ω ∂(gridLawA D N K μ₀),
      (Matrix.of (gridStateA D N K (s / K) ω K)).IsHermitian := by
    have h := hcls.herm
    rw [← hlaw] at h
    exact (ae_map_iff (LF3_state_meas D N K _ K).aemeasurable LF3_herm_meas).1 h
  have hgm := (LF3_meas (lam D N A) θ z₁ z₂ s).2.2.1 x y
  have hint : ∫ H, LF3_g (lam D N A) θ z₁ z₂ s H x y ∂(blockOULaw D N μ₀ s) =
      ∫ ω, LF3_g (lam D N A) θ z₁ z₂ s (gridStateA D N K (s / K) ω K) x y
        ∂(gridLawA D N K μ₀) := by
    rw [← hlaw, integral_map (LF3_state_meas D N K _ K).aemeasurable hgm.aestronglyMeasurable]
  rw [hint]
  -- the four exceptional sets
  have hB1 := hNg N hNg' θ hθ0 hθ1 μ₀ hμ₀ A z s hadms K (by exact_mod_cast hKpos)
    (by simpa using hK2)
  have hB2 := hNl N hNl' θ hθ0 hθ1 μ₀ hμ₀ A z s hadms K hK1 hK2 z₁ z₂ h₁ h₂
  have hB3 := hN3 N hN3' θ hθ0 hθ1 μ₀ hμ₀ A z s hadms K hK1 hK2 z₁ z₂ z₁ h₁ h₂ h₁
  have hB4 := hN3 N hN3' θ hθ0 hθ1 μ₀ hμ₀ A z s hadms K hK1 hK2 z₂ z₁ z₂ h₂ h₁ h₂
  set B1 := {ω : GridΩA D N K | ∃ k : ℕ, k ≤ K ∧
      ¬ flowGoodAt A z τ₁ (k * (s / K)) (gridStateA D N K (s / K) ω k)} with hB1d
  set B2 := {ω : GridΩA D N K | ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ₁ * ((N : ℝ) ^ εg /
        (N * (flowTc (lam D N A) z - k * (s / K)) ^ 2 *
          flowIm (lam D N A) z (k * (s / K)) ^ 2)) <
      hsNorm (flowLmat (lam D N A) z₁ z₂ (k * (s / K)) (gridStateA D N K (s / K) ω k) -
        flowKmat (lam D N A) θ z₁ z₂ (k * (s / K)))} with hB2d
  set B3 := {ω : GridΩA D N K | ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ₁ * ((N : ℝ) ^ εg /
        (N * (flowTc (lam D N A) z - k * (s / K)) ^ 3 *
          flowIm (lam D N A) z (k * (s / K)) ^ 3)) <
      ten3Norm (flowLten3 (lam D N A) z₁ z₂ z₁ (k * (s / K)) (gridStateA D N K (s / K) ω k) -
        flowKten3 (lam D N A) θ z₁ z₂ z₁ (k * (s / K)))} with hB3d
  set B4 := {ω : GridΩA D N K | ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ₁ * ((N : ℝ) ^ εg /
        (N * (flowTc (lam D N A) z - k * (s / K)) ^ 3 *
          flowIm (lam D N A) z (k * (s / K)) ^ 3)) <
      ten3Norm (flowLten3 (lam D N A) z₂ z₁ z₂ (k * (s / K)) (gridStateA D N K (s / K) ω k) -
        flowKten3 (lam D N A) θ z₂ z₁ z₂ (k * (s / K)))} with hB4d
  have hBadμ : gridLawA D N K μ₀ (B1 ∪ B2 ∪ B3 ∪ B4) ≤
      ENNReal.ofReal (4 * (N : ℝ) ^ (-(10 : ℝ))) := by
    have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(10 : ℝ)) := by positivity
    calc gridLawA D N K μ₀ (B1 ∪ B2 ∪ B3 ∪ B4)
        ≤ gridLawA D N K μ₀ B1 + gridLawA D N K μ₀ B2 + gridLawA D N K μ₀ B3 +
            gridLawA D N K μ₀ B4 :=
          (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
            (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(10 : ℝ))) + ENNReal.ofReal ((N : ℝ) ^ (-(10 : ℝ))) +
            ENNReal.ofReal ((N : ℝ) ^ (-(10 : ℝ))) + ENNReal.ofReal ((N : ℝ) ^ (-(10 : ℝ))) :=
          add_le_add (add_le_add (add_le_add hB1 hB2) hB3) hB4
      _ = ENNReal.ofReal (4 * (N : ℝ) ^ (-(10 : ℝ))) := by
          rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) h0,
            ← ENNReal.ofReal_add (by positivity) h0]
          congr 1; ring
  -- the bounds on `K` and on `K_{(i,j,i)}`
  have hKb : ∀ a b : Fin D, ‖flowKmat (lam D N A) θ z₁ z₂ s a b‖ ≤ 2 * N := fun a b =>
    ((LF3_flowK D N A hΛ10 z hz S hSt θ hθ0 hθ1 z₁ z₂ h₁ h₂ s hs0 hsS).2.2 a b).trans hqinv
  have hPN : (N : ℝ) ^ τ₁ ≤ N := by
    calc (N : ℝ) ^ τ₁ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1r hτ₁1
      _ = N := Real.rpow_one _
  have hιη : flowIm (lam D N A) z s / (charFlowZ (lam D N A) z s).im ^ 2 ≤ (N : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ (N : ℝ) * (charFlowZ (lam D N A) z s).im := by
      rw [inv_lt_iff_one_lt_mul₀ hNpos] at hηN; linarith
    nlinarith
  have hK3 : ∀ (u v : ℂ), (u = z ∨ u = star z) → (v = z ∨ v = star z) → ∀ a b c,
      ‖flowKten3 (lam D N A) θ u v u s a b c‖ ≤ (N : ℝ) ^ 3 := by
    intro u v hu hv a b c
    refine (LF3_t3_entry _ a b c).trans ((hNk N hNk' θ hθ0 hθ1 μ₀ hμ₀ A z s hadms u v hu hv).trans
      ?_)
    calc (N : ℝ) ^ τ₁ * (flowIm (lam D N A) z s / (charFlowZ (lam D N A) z s).im ^ 2)
        ≤ N * (N : ℝ) ^ 2 := mul_le_mul hPN hιη (by positivity) (by positivity)
      _ = (N : ℝ) ^ 3 := by ring
  -- crude bound at Hermitian states
  have hall : ∀ᵐ ω ∂(gridLawA D N K μ₀),
      ‖LF3_g (lam D N A) θ z₁ z₂ s (gridStateA D N K (s / K) ω K) x y‖ ≤
        12 * (D : ℝ) ^ 3 * (N : ℝ) ^ 4 := by
    filter_upwards [hherm] with ω hω
    set H := gridStateA D N K (s / K) ω K
    obtain ⟨c1, c2, c3⟩ := LF3_crude D N hD1 hN1 A hΛ10 z hz s hs1 hs0 H hω
    have hd : ∀ (w : ℂ), (w = z ∨ w = star z) → ∀ a, ‖LF3_d (lam D N A) w s H a‖ ≤ 2 * N :=
      fun w hw a => (c1 w hw a).trans (by linarith)
    have hLK : ∀ a b, ‖flowLmat (lam D N A) z₁ z₂ s H a b - flowKmat (lam D N A) θ z₁ z₂ s a b‖ ≤
        2 * D * (N : ℝ) ^ 2 := by
      intro a b
      refine (norm_sub_le _ _).trans ?_
      have h1 : (D : ℝ) / (charFlowZ (lam D N A) z s).im ^ 2 ≤ D * (N : ℝ) ^ 2 := by
        rw [div_eq_mul_inv, ← inv_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 hηs0.le) hηinv 2)
          (Nat.cast_nonneg _)
      have h2 : 2 * (N : ℝ) ≤ D * (N : ℝ) ^ 2 := by nlinarith
      linarith [c2 z₁ z₂ h₁ h₂ a b, hKb a b]
    have hLK3 : ∀ (u v : ℂ), (u = z ∨ u = star z) → (v = z ∨ v = star z) → ∀ a b c,
        ‖flowLten3 (lam D N A) u v u s H a b c - flowKten3 (lam D N A) θ u v u s a b c‖ ≤
          2 * D * (N : ℝ) ^ 3 := by
      intro u v hu hv a b c
      refine (norm_sub_le _ _).trans ?_
      have h1 : (D : ℝ) / (charFlowZ (lam D N A) z s).im ^ 3 ≤ D * (N : ℝ) ^ 3 := by
        rw [div_eq_mul_inv, ← inv_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 hηs0.le) hηinv 3)
          (Nat.cast_nonneg _)
      have h2 : (N : ℝ) ^ 3 ≤ D * (N : ℝ) ^ 3 := le_mul_of_one_le_left (by positivity)
        (by linarith)
      linarith [c3 u v u hu hv hu a b c, hK3 u v hu hv a b c]
    simp only [LF3_g, Matrix.mul_apply]
    refine (norm_add_le _ _).trans ?_
    have t1 : ‖∑ a, (flowLmat (lam D N A) z₁ z₂ s H - flowKmat (lam D N A) θ z₁ z₂ s) x a *
        (flowLmat (lam D N A) z₁ z₂ s H - flowKmat (lam D N A) θ z₁ z₂ s) a y‖ ≤
        D * (2 * D * (N : ℝ) ^ 2) ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ a, ‖(flowLmat (lam D N A) z₁ z₂ s H - flowKmat (lam D N A) θ z₁ z₂ s) x a *
            (flowLmat (lam D N A) z₁ z₂ s H - flowKmat (lam D N A) θ z₁ z₂ s) a y‖
          ≤ ∑ _a : Fin D, (2 * D * (N : ℝ) ^ 2) ^ 2 := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_mul, sq]
            exact mul_le_mul (hLK x a) (hLK a y) (norm_nonneg _) (by positivity)
        _ = D * (2 * D * (N : ℝ) ^ 2) ^ 2 := by simp
    have t2 : ‖(D : ℂ) * ∑ a, (LF3_d (lam D N A) z₁ s H a *
          (flowLten3 (lam D N A) z₁ z₂ z₁ s H x y a - flowKten3 (lam D N A) θ z₁ z₂ z₁ s x y a) +
        LF3_d (lam D N A) z₂ s H a *
          (flowLten3 (lam D N A) z₂ z₁ z₂ s H y x a - flowKten3 (lam D N A) θ z₂ z₁ z₂ s y x a))‖ ≤
        D * (D * (2 * (2 * N * (2 * D * (N : ℝ) ^ 3)))) := by
      rw [norm_mul, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (Nat.cast_nonneg _)
      calc ∑ a, ‖LF3_d (lam D N A) z₁ s H a *
            (flowLten3 (lam D N A) z₁ z₂ z₁ s H x y a - flowKten3 (lam D N A) θ z₁ z₂ z₁ s x y a) +
          LF3_d (lam D N A) z₂ s H a *
            (flowLten3 (lam D N A) z₂ z₁ z₂ s H y x a - flowKten3 (lam D N A) θ z₂ z₁ z₂ s y x a)‖
          ≤ ∑ _a : Fin D, 2 * (2 * N * (2 * D * (N : ℝ) ^ 3)) := by
            refine Finset.sum_le_sum fun a _ => (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
            have u1 := mul_le_mul (hd z₁ h₁ a) (hLK3 z₁ z₂ h₁ h₂ x y a) (norm_nonneg _)
              (by positivity)
            have u2 := mul_le_mul (hd z₂ h₂ a) (hLK3 z₂ z₁ h₂ h₁ y x a) (norm_nonneg _)
              (by positivity)
            linarith
        _ = D * (2 * (2 * N * (2 * D * (N : ℝ) ^ 3))) := by simp
    calc _ ≤ D * (2 * D * (N : ℝ) ^ 2) ^ 2 + D * (D * (2 * (2 * N * (2 * D * (N : ℝ) ^ 3)))) :=
          add_le_add t1 t2
      _ = 12 * (D : ℝ) ^ 3 * (N : ℝ) ^ 4 := by ring
  -- the bound off the exceptional sets
  have hgood : ∀ᵐ ω ∂(gridLawA D N K μ₀), ω ∉ B1 ∪ B2 ∪ B3 ∪ B4 →
      ‖LF3_g (lam D N A) θ z₁ z₂ s (gridStateA D N K (s / K) ω K) x y‖ ≤
        (D + 2 * D ^ 2) * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁ * ((N : ℝ) ^ εg * (N : ℝ) ^ εg) /
          ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - s) ^ 4 * flowIm (lam D N A) z s ^ 4)) := by
    filter_upwards [hherm] with ω hω hnb
    simp only [hB1d, hB2d, hB3d, hB4d, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists,
      not_and, not_lt, not_not] at hnb
    obtain ⟨⟨⟨hg, hl⟩, h3⟩, h4⟩ := hnb
    have hg' := hg K le_rfl
    have hl' := hl K le_rfl
    have h3' := h3 K le_rfl
    have h4' := h4 K le_rfl
    rw [hKs] at hg' hl' h3' h4'
    set H := gridStateA D N K (s / K) ω K with hH
    set P := (N : ℝ) ^ τ₁ with hP
    set E := (N : ℝ) ^ εg with hE
    set q := flowTc (lam D N A) z - s with hq
    set ι := flowIm (lam D N A) z s with hι
    set η := (charFlowZ (lam D N A) z s).im with hηd
    have hd : ∀ (w : ℂ), (w = z ∨ w = star z) → ∀ a,
        ‖LF3_d (lam D N A) w s H a‖ ≤ P / (N * η) := fun w hw a => by
      rw [LF3_d_eq D N hD1 hN1 A z hz s hs1 H hω w hw a]
      exact hg'.1 a
    have hLK : ∀ a b, ‖(flowLmat (lam D N A) z₁ z₂ s H - flowKmat (lam D N A) θ z₁ z₂ s) a b‖ ≤
        P * (E / (N * q ^ 2 * ι ^ 2)) := fun a b => (LF3_entry_hs _ a b).trans hl'
    have t1 : ‖∑ a, (flowLmat (lam D N A) z₁ z₂ s H - flowKmat (lam D N A) θ z₁ z₂ s) x a *
        (flowLmat (lam D N A) z₁ z₂ s H - flowKmat (lam D N A) θ z₁ z₂ s) a y‖ ≤
        D * (P * (E / (N * q ^ 2 * ι ^ 2))) ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ a, ‖(flowLmat (lam D N A) z₁ z₂ s H - flowKmat (lam D N A) θ z₁ z₂ s) x a *
            (flowLmat (lam D N A) z₁ z₂ s H - flowKmat (lam D N A) θ z₁ z₂ s) a y‖
          ≤ ∑ _a : Fin D, (P * (E / (N * q ^ 2 * ι ^ 2))) ^ 2 := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_mul, sq]
            exact mul_le_mul (hLK x a) (hLK a y) (norm_nonneg _) (by positivity)
        _ = D * (P * (E / (N * q ^ 2 * ι ^ 2))) ^ 2 := by simp
    have t2 : ‖(D : ℂ) * ∑ a, (LF3_d (lam D N A) z₁ s H a *
          (flowLten3 (lam D N A) z₁ z₂ z₁ s H x y a - flowKten3 (lam D N A) θ z₁ z₂ z₁ s x y a) +
        LF3_d (lam D N A) z₂ s H a *
          (flowLten3 (lam D N A) z₂ z₁ z₂ s H y x a - flowKten3 (lam D N A) θ z₂ z₁ z₂ s y x a))‖ ≤
        D * (D * (2 * (P / (N * η) * (P * (E / (N * q ^ 3 * ι ^ 3)))))) := by
      rw [norm_mul, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (Nat.cast_nonneg _)
      calc ∑ a, ‖LF3_d (lam D N A) z₁ s H a *
            (flowLten3 (lam D N A) z₁ z₂ z₁ s H x y a - flowKten3 (lam D N A) θ z₁ z₂ z₁ s x y a) +
          LF3_d (lam D N A) z₂ s H a *
            (flowLten3 (lam D N A) z₂ z₁ z₂ s H y x a - flowKten3 (lam D N A) θ z₂ z₁ z₂ s y x a)‖
          ≤ ∑ _a : Fin D, 2 * (P / (N * η) * (P * (E / (N * q ^ 3 * ι ^ 3)))) := by
            refine Finset.sum_le_sum fun a _ => (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
            have v1 : ‖flowLten3 (lam D N A) z₁ z₂ z₁ s H x y a -
                flowKten3 (lam D N A) θ z₁ z₂ z₁ s x y a‖ ≤ P * (E / (N * q ^ 3 * ι ^ 3)) :=
              (LF3_t3_entry (flowLten3 (lam D N A) z₁ z₂ z₁ s H -
                flowKten3 (lam D N A) θ z₁ z₂ z₁ s) x y a).trans h3'
            have v2 : ‖flowLten3 (lam D N A) z₂ z₁ z₂ s H y x a -
                flowKten3 (lam D N A) θ z₂ z₁ z₂ s y x a‖ ≤ P * (E / (N * q ^ 3 * ι ^ 3)) :=
              (LF3_t3_entry (flowLten3 (lam D N A) z₂ z₁ z₂ s H -
                flowKten3 (lam D N A) θ z₂ z₁ z₂ s) y x a).trans h4'
            have u1 := mul_le_mul (hd z₁ h₁ a) v1 (norm_nonneg _) (by positivity)
            have u2 := mul_le_mul (hd z₂ h₂ a) v2 (norm_nonneg _) (by positivity)
            linarith
        _ = D * (2 * (P / (N * η) * (P * (E / (N * q ^ 3 * ι ^ 3))))) := by simp
    simp only [LF3_g, Matrix.mul_apply]
    refine (norm_add_le _ _).trans ?_
    exact LF3_ar_g D N P E q ι η _ _ (Nat.cast_nonneg _) hNpos (by positivity)
      (Real.one_le_rpow hN1r hεg.le) hqs hιs hηs0 hqι t1 t2
  refine (LF3_expect_le _ _ (hgm.comp (LF3_state_meas D N K (s / K) K)).aestronglyMeasurable
    (B1 ∪ B2 ∪ B3 ∪ B4) _ _ _ (by positivity) (by positivity) (by positivity) hBadμ hgood
    hall).trans (le_of_eq ?_)
  ring


/-! ### The discrete Grönwall bound and the final inequalities -/

/-- A discrete Grönwall bound: if `a_{k+1} ≤ (1 + 2h/q_k + h) a_k + β_k` with `q_k = q₀ - k h`,
`a, β ≥ 0`, then `q_K² a_K ≤ e^{K h} (q₀² a₀ + Σ_{k<K} q_{k+1}² β_k)`. -/
private lemma LF3_gron (K : ℕ) (h q₀ : ℝ) (hh : 0 < h) (hK : (K : ℝ) * h < q₀) (a β : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hβ : ∀ k, k < K → 0 ≤ β k)
    (hrec : ∀ k, k < K → a (k + 1) ≤ (1 + 2 * h / (q₀ - k * h) + h) * a k + β k) :
    (q₀ - K * h) ^ 2 * a K ≤ Real.exp (K * h) *
      (q₀ ^ 2 * a 0 + ∑ k ∈ Finset.range K, (q₀ - (k + 1) * h) ^ 2 * β k) := by
  have claim : ∀ n, n ≤ K → (q₀ - n * h) ^ 2 * Real.exp (-(n * h)) * a n ≤
      q₀ ^ 2 * a 0 + ∑ k ∈ Finset.range n, (q₀ - (k + 1) * h) ^ 2 * β k := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have IH := ih (by omega)
      have hnK : ((n : ℝ) + 1) * h ≤ K * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh.le
      set qn := q₀ - n * h with hqn
      have hqn1 : 0 < qn - h := by rw [hqn]; nlinarith
      have hqnpos : 0 < qn := by linarith
      have e1 : q₀ - ((n + 1 : ℕ) : ℝ) * h = qn - h := by rw [hqn]; push_cast; ring
      have hexp1 : Real.exp (-(((n + 1 : ℕ) : ℝ) * h)) * Real.exp h =
          Real.exp (-((n : ℝ) * h)) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have hexp2 : Real.exp (-(((n + 1 : ℕ) : ℝ) * h)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * h := by positivity
                                  linarith)
      have hfac : (qn - h) ^ 2 * (1 + 2 * h / qn + h) ≤ qn ^ 2 * Real.exp h := by
        have e2 : (qn - h) ^ 2 * (1 + 2 * h / qn + h) =
            qn ^ 2 * (1 + h) - 3 * h ^ 2 + 2 * h ^ 3 / qn - 2 * h ^ 2 * qn + h ^ 3 := by
          field_simp; ring
        rw [e2]
        have h3 : qn ^ 2 * (1 + h) ≤ qn ^ 2 * Real.exp h :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp h]) (sq_nonneg qn)
        have h4 : 2 * h ^ 3 / qn ≤ 2 * h ^ 2 := by
          rw [div_le_iff₀ hqnpos]; nlinarith
        have h5 : h ^ 3 ≤ h ^ 2 * qn := by nlinarith
        nlinarith [sq_nonneg h]
      have hr := hrec n (by omega)
      rw [e1, Finset.sum_range_succ]
      have hE := Real.exp_pos (-(((n + 1 : ℕ) : ℝ) * h))
      calc (qn - h) ^ 2 * Real.exp (-(((n + 1 : ℕ) : ℝ) * h)) * a (n + 1)
          ≤ (qn - h) ^ 2 * Real.exp (-(((n + 1 : ℕ) : ℝ) * h)) *
              ((1 + 2 * h / qn + h) * a n + β n) :=
            mul_le_mul_of_nonneg_left hr (by positivity)
        _ = ((qn - h) ^ 2 * (1 + 2 * h / qn + h)) * Real.exp (-(((n + 1 : ℕ) : ℝ) * h)) * a n +
              (qn - h) ^ 2 * Real.exp (-(((n + 1 : ℕ) : ℝ) * h)) * β n := by ring
        _ ≤ (qn ^ 2 * Real.exp h) * Real.exp (-(((n + 1 : ℕ) : ℝ) * h)) * a n +
              (qn - h) ^ 2 * 1 * β n := by
            gcongr
            · exact ha n
            · exact hβ n (by omega)
        _ = qn ^ 2 * Real.exp (-((n : ℝ) * h)) * a n + (qn - h) ^ 2 * β n := by
            rw [mul_assoc (qn ^ 2), mul_comm (Real.exp h), hexp1]; ring
        _ ≤ q₀ ^ 2 * a 0 + (∑ k ∈ Finset.range n, (q₀ - (k + 1) * h) ^ 2 * β k) +
              (qn - h) ^ 2 * β n := by linarith
        _ = _ := by rw [hqn]; ring
  have hc := claim K le_rfl
  have hE : Real.exp (K * h) * Real.exp (-(K * h)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc (q₀ - K * h) ^ 2 * a K = Real.exp (K * h) *
        ((q₀ - K * h) ^ 2 * Real.exp (-(K * h)) * a K) := by
        rw [← mul_assoc, ← mul_assoc, mul_comm (Real.exp _) ((q₀ - _) ^ 2),
          mul_assoc ((q₀ - _) ^ 2), hE, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le

/-- The sum of the Grönwall bound: with `q_k = q₀ - k h`, `ι_k ≥ ι₀ > 0`, `q₀ ≤ 1`,
`Σ_{k<K} q_{k+1}² (h (a/(q_k⁴ ι_k⁴) + b/(q_k³ ι_k²) + Y) + R)
≤ a/ι₀⁴ · q_K⁻¹ + b/ι₀² · log(q₀/q_K) + K h Y + K R`. -/
private lemma LF3_sumbd (K : ℕ) (h q₀ ι₀ a b Y R : ℝ) (ι : ℕ → ℝ) (hh : 0 < h)
    (hK : (K : ℝ) * h < q₀) (hq1 : q₀ ≤ 1) (hι₀ : 0 < ι₀) (hι : ∀ k, k < K → ι₀ ≤ ι k)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hY : 0 ≤ Y) (hR : 0 ≤ R) :
    ∑ k ∈ Finset.range K, (q₀ - (k + 1) * h) ^ 2 *
        (h * (a / ((q₀ - k * h) ^ 4 * ι k ^ 4) + b / ((q₀ - k * h) ^ 3 * ι k ^ 2) + Y) + R) ≤
      a / ι₀ ^ 4 * (q₀ - K * h)⁻¹ + b / ι₀ ^ 2 * Real.log (q₀ / (q₀ - K * h)) +
        K * h * Y + K * R := by
  obtain ⟨-, hs2, hs1⟩ := LF3_rsum q₀ h hh K hK
  have hterm : ∀ k ∈ Finset.range K, (q₀ - (k + 1) * h) ^ 2 *
      (h * (a / ((q₀ - k * h) ^ 4 * ι k ^ 4) + b / ((q₀ - k * h) ^ 3 * ι k ^ 2) + Y) + R) ≤
      a / ι₀ ^ 4 * (h * ((q₀ - k * h) ^ 2)⁻¹) + b / ι₀ ^ 2 * (h / (q₀ - k * h)) + h * Y + R := by
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
    set q := q₀ - (k : ℝ) * h with hqd
    set q' := q₀ - ((k : ℝ) + 1) * h with hq'd
    have hq'q : q' ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hq1'.le hqle 2
    have hq'1 : q' ^ 2 ≤ 1 := by nlinarith
    have t1 : q' ^ 2 * (h * (a / (q ^ 4 * ι k ^ 4))) ≤ a / ι₀ ^ 4 * (h * (q ^ 2)⁻¹) := by
      have e1 : q' ^ 2 * (h * (a / (q ^ 4 * ι k ^ 4))) =
          (q' ^ 2 / q ^ 2) * (a * h / (q ^ 2 * ι k ^ 4)) := by field_simp
      have e2 : a / ι₀ ^ 4 * (h * (q ^ 2)⁻¹) = 1 * (a * h / (q ^ 2 * ι₀ ^ 4)) := by field_simp
      rw [e1, e2]
      apply mul_le_mul ((div_le_one (by positivity)).2 hq'q) _ (by positivity) zero_le_one
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hι₀.le hιk' 4) (by positivity))
    have t2 : q' ^ 2 * (h * (b / (q ^ 3 * ι k ^ 2))) ≤ b / ι₀ ^ 2 * (h / q) := by
      have e1 : q' ^ 2 * (h * (b / (q ^ 3 * ι k ^ 2))) =
          (q' ^ 2 / q ^ 2) * (b * h / (q * ι k ^ 2)) := by field_simp
      have e2 : b / ι₀ ^ 2 * (h / q) = 1 * (b * h / (q * ι₀ ^ 2)) := by field_simp
      rw [e1, e2]
      apply mul_le_mul ((div_le_one (by positivity)).2 hq'q) _ (by positivity) zero_le_one
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hι₀.le hιk' 2) (by positivity))
    have t3 : q' ^ 2 * (h * Y) ≤ h * Y := by
      have : 0 ≤ h * Y := by positivity
      nlinarith
    have t4 : q' ^ 2 * R ≤ R := by nlinarith
    have e3 : q' ^ 2 * (h * (a / (q ^ 4 * ι k ^ 4) + b / (q ^ 3 * ι k ^ 2) + Y) + R) =
        q' ^ 2 * (h * (a / (q ^ 4 * ι k ^ 4))) + q' ^ 2 * (h * (b / (q ^ 3 * ι k ^ 2))) +
          q' ^ 2 * (h * Y) + q' ^ 2 * R := by ring
    rw [e3]
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e1 : ∑ k ∈ Finset.range K, a / ι₀ ^ 4 * (h * ((q₀ - k * h) ^ 2)⁻¹) =
      a / ι₀ ^ 4 * ∑ k ∈ Finset.range K, h * ((q₀ - k * h) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
  have e2 : ∑ k ∈ Finset.range K, b / ι₀ ^ 2 * (h / (q₀ - k * h)) =
      b / ι₀ ^ 2 * ∑ k ∈ Finset.range K, h / (q₀ - k * h) := (Finset.mul_sum _ _ _).symm
  rw [e1, e2]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left hs2 (by positivity : (0 : ℝ) ≤ a / ι₀ ^ 4)
  have h2 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ b / ι₀ ^ 2)
  have e3 : (K : ℝ) * (h * Y) = K * h * Y := by ring
  linarith

/-- `(P u/(N q ι)) (P ι/η²) ≤ P² u/(N q³ ι²)` for `η ≥ q ι > 0`. -/
private lemma LF3_ar_S (N P u q ι η : ℝ) (hN : 0 < N) (hP : 0 ≤ P) (hu : 0 ≤ u) (hq : 0 < q)
    (hι : 0 < ι) (hη : 0 < η) (hqι : q * ι ≤ η) :
    P * (u / (N * q * ι)) * (P * (ι / η ^ 2)) ≤ P * P * u / (N * q ^ 3 * ι ^ 2) := by
  have e : P * (u / (N * q * ι)) * (P * (ι / η ^ 2)) = P * P * u / (N * q * η ^ 2) := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have : (q * ι) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (by positivity) hqι 2
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ N * q)]

/-- The final inequality for (3.32) [flow_3_result]: from the Grönwall bound
`q_S² a ≤ E² (q₀² a₀ + α P v/(N² ι₀⁴) q_S⁻¹ + β P u/(N ι₀²) L + Z)`, `E = e^{S/2} ∈ [1, e^{1/2}]`,
`ι_S = E ι₀ ≤ 1`, `q_S ≤ 1`, `q_S⁻¹ ≤ 2N`, `L ≤ L_b` and `Z ≤ C_z/N⁶`, the bound
`a ≤ T ((q₀/q_S)² a₀ + u/(N q_S² ι_S²) + v/(N² q_S³ ι_S⁴))`. -/
private lemma LF3_ar_fin (N qS q₀ ι₀ E a₀ aS α β Pm u v Lg Lb Z Cz T : ℝ) (hN : 2 ≤ N)
    (hqS : 0 < qS) (hι0 : 0 < ι₀) (hE1 : 1 ≤ E) (hE : E ≤ Real.exp (1 / 2))
    (hιS : E * ι₀ ≤ 1) (hqS1 : qS ≤ 1) (ha₀ : 0 ≤ a₀) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hPm : 0 ≤ Pm)
    (hu : 0 ≤ u) (hv : 1 ≤ v) (hLg : Lg ≤ Lb) (hLg0 : 0 ≤ Lg) (hZ0 : 0 ≤ Z)
    (hqinv : qS⁻¹ ≤ 2 * N) (hZ : Z ≤ Cz / N ^ 6)
    (ha : qS ^ 2 * aS ≤ E ^ 2 * (q₀ ^ 2 * a₀ + α * Pm * v / N ^ 2 / ι₀ ^ 4 * qS⁻¹ +
      β * Pm * u / N / ι₀ ^ 2 * Lg + Z))
    (hT1 : Real.exp 1 ≤ T) (hT2 : 2 * Real.exp (1 / 2) ^ 6 * α * Pm ≤ T)
    (hT3 : Real.exp (1 / 2) ^ 4 * β * Pm * Lb ≤ T) (hT4 : 8 * Real.exp 1 * Cz ≤ N ^ 2)
    (hT : 1 ≤ T) :
    aS ≤ T * ((q₀ / qS) ^ 2 * a₀ + u / (N * qS ^ 2 * (E * ι₀) ^ 2) +
      v / (N ^ 2 * qS ^ 3 * (E * ι₀) ^ 4)) := by
  set e2 := Real.exp (1 / 2) with he2
  have hNpos : 0 < N := by linarith
  have hE0 : 0 < E := by linarith
  have he2sq : e2 ^ 2 = Real.exp 1 := by rw [he2, sq, ← Real.exp_add]; norm_num
  set ι := E * ι₀ with hι
  have hιpos : 0 < ι := by positivity
  set W₁ := u / (N * qS ^ 2 * ι ^ 2) with hW₁
  set W₂ := v / (N ^ 2 * qS ^ 3 * ι ^ 4) with hW₂
  have hW₁0 : 0 ≤ W₁ := by positivity
  have hW₂0 : 0 ≤ W₂ := by positivity
  have hι₀e : ι₀ = ι / E := by rw [hι]; field_simp
  have ha' : aS ≤ E ^ 2 * ((q₀ / qS) ^ 2 * a₀) + E ^ 6 * α * Pm * W₂ +
      E ^ 4 * β * Pm * Lg * W₁ + E ^ 2 * Z / qS ^ 2 := by
    have e : E ^ 2 * (q₀ ^ 2 * a₀ + α * Pm * v / N ^ 2 / ι₀ ^ 4 * qS⁻¹ +
        β * Pm * u / N / ι₀ ^ 2 * Lg + Z) / qS ^ 2 =
        E ^ 2 * ((q₀ / qS) ^ 2 * a₀) + E ^ 6 * α * Pm * W₂ + E ^ 4 * β * Pm * Lg * W₁ +
          E ^ 2 * Z / qS ^ 2 := by
      rw [hW₁, hW₂, hι₀e]; field_simp
    rw [← e, le_div_iff₀ (by positivity)]
    linarith
  have hE2 : E ^ 2 ≤ Real.exp 1 := by
    rw [← he2sq]; exact pow_le_pow_left₀ hE0.le hE 2
  have t1 : E ^ 2 * ((q₀ / qS) ^ 2 * a₀) ≤ T * ((q₀ / qS) ^ 2 * a₀) :=
    mul_le_mul_of_nonneg_right (hE2.trans hT1) (by positivity)
  have t2 : E ^ 6 * α * Pm * W₂ ≤ T / 2 * W₂ := by
    have hE6 : E ^ 6 ≤ e2 ^ 6 := pow_le_pow_left₀ hE0.le hE 6
    have : E ^ 6 * α * Pm ≤ T / 2 := by
      have : E ^ 6 * (α * Pm) ≤ e2 ^ 6 * (α * Pm) := mul_le_mul_of_nonneg_right hE6 (by positivity)
      nlinarith
    exact mul_le_mul_of_nonneg_right this hW₂0
  have t3 : E ^ 4 * β * Pm * Lg * W₁ ≤ T * W₁ := by
    have hE4 : E ^ 4 ≤ e2 ^ 4 := pow_le_pow_left₀ hE0.le hE 4
    have : E ^ 4 * β * Pm * Lg ≤ T := by
      have h1 : E ^ 4 * (β * Pm * Lg) ≤ e2 ^ 4 * (β * Pm * Lg) :=
        mul_le_mul_of_nonneg_right hE4 (by positivity)
      have h2 : e2 ^ 4 * β * Pm * Lg ≤ e2 ^ 4 * β * Pm * Lb :=
        mul_le_mul_of_nonneg_left hLg (by positivity)
      nlinarith
    exact mul_le_mul_of_nonneg_right this hW₁0
  have t4 : E ^ 2 * Z / qS ^ 2 ≤ T / 2 * W₂ := by
    have h1 : qS ^ 3 ≤ 1 := pow_le_one₀ hqS.le hqS1
    have h2 : ι ^ 4 ≤ 1 := pow_le_one₀ hιpos.le hιS
    have h3 : N ^ 2 * qS ^ 3 * ι ^ 4 ≤ N ^ 2 := by
      have := mul_le_mul h1 h2 (by positivity) zero_le_one
      have h4 : 0 ≤ N ^ 2 := by positivity
      calc N ^ 2 * qS ^ 3 * ι ^ 4 = N ^ 2 * (qS ^ 3 * ι ^ 4) := by ring
        _ ≤ N ^ 2 * 1 := mul_le_mul_of_nonneg_left (by linarith) h4
        _ = N ^ 2 := mul_one _
    have hW2 : 1 / N ^ 2 ≤ W₂ :=
      calc 1 / N ^ 2 ≤ v / N ^ 2 := div_le_div_of_nonneg_right hv (by positivity)
        _ ≤ W₂ := div_le_div_of_nonneg_left (by linarith) (by positivity) h3
    have hCz : 0 ≤ Cz := by
      have h5 : 0 ≤ Cz / N ^ 6 := hZ0.trans hZ
      have : 0 < N ^ 6 := by positivity
      exact (div_nonneg_iff.1 h5).elim (fun h => h.1) (fun h => by linarith [h.2])
    have hq2 : (qS ^ 2)⁻¹ ≤ 4 * N ^ 2 := by
      rw [← inv_pow]
      calc qS⁻¹ ^ 2 ≤ (2 * N) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hqS.le) hqinv 2
        _ = 4 * N ^ 2 := by ring
    have h6 : E ^ 2 * Z / qS ^ 2 ≤ Real.exp 1 * (Cz / N ^ 6) * (4 * N ^ 2) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (mul_le_mul hE2 hZ hZ0 (by positivity)) hq2 (by positivity)
        (by positivity)
    have h7 : Real.exp 1 * (Cz / N ^ 6) * (4 * N ^ 2) ≤ 1 / 2 * (1 / N ^ 2) := by
      have e7 : Real.exp 1 * (Cz / N ^ 6) * (4 * N ^ 2) = (8 * Real.exp 1 * Cz) / (2 * N ^ 4) := by
        field_simp; ring
      have e8 : (1 : ℝ) / 2 * (1 / N ^ 2) = N ^ 2 / (2 * N ^ 4) := by field_simp
      rw [e7, e8]
      exact div_le_div_of_nonneg_right hT4 (by positivity)
    have h9 : 1 / 2 * (1 / N ^ 2) ≤ T / 2 * W₂ :=
      mul_le_mul (by linarith) hW2 (by positivity) (by positivity)
    linarith
  have : T / 2 * W₂ + T / 2 * W₂ = T * W₂ := by ring
  calc aS ≤ E ^ 2 * ((q₀ / qS) ^ 2 * a₀) + E ^ 6 * α * Pm * W₂ + E ^ 4 * β * Pm * Lg * W₁ +
        E ^ 2 * Z / qS ^ 2 := ha'
    _ ≤ T * ((q₀ / qS) ^ 2 * a₀) + T / 2 * W₂ + T * W₁ + T / 2 * W₂ := by linarith
    _ = T * ((q₀ / qS) ^ 2 * a₀ + W₁ + W₂) := by ring


/-- One step of the linear recursion for `Δ = E L - K` in the Hilbert–Schmidt norm: if
`E(L + L² + err) = E L + K E L + E L K - K² + S` entrywise, the step of `E L` is `h E(L + L² + err)`
up to `m₁`, the step of `K` is `h (K² + K)` up to `m₂`, `|S_{xy}| ≤ E_k` and the operator of
(3.62) [eq:TtV] has norm `≤ 1 + q` ((3.67) [Tnorm]), then
`‖Δ'‖₂ ≤ (1 + 2h/q + h) ‖Δ‖₂ + h D² E_k + D² (m₁ + m₂)`. -/
private lemma LF3_rec {D : ℕ} (EL EL' Kk Kk' Sm : Matrix (Fin D) (Fin D) ℂ)
    (Idr : Fin D → Fin D → ℂ) (h q m₁ m₂ Ek : ℝ) (hh : 0 ≤ h) (hq : 0 < q)
    (hT : hsNorm (((q : ℝ) : ℂ) • (Kk * (EL - Kk) + (EL - Kk) * Kk) -
      ((1 - q : ℝ) : ℂ) • (EL - Kk)) ≤ (1 + q) * hsNorm (EL - Kk))
    (hlin : ∀ x y, Idr x y = EL x y + (Kk * EL) x y + (EL * Kk) x y - (Kk * Kk) x y + Sm x y)
    (hstep : ∀ x y, ‖EL' x y - EL x y - (h : ℂ) * Idr x y‖ ≤ m₁)
    (hkd : ∀ x y, ‖(Kk' - Kk - (h : ℂ) • (Kk * Kk + Kk)) x y‖ ≤ m₂)
    (hS : ∀ x y, ‖Sm x y‖ ≤ Ek) :
    hsNorm (EL' - Kk') ≤ (1 + 2 * h / q + h) * hsNorm (EL - Kk) +
      (h * ((D : ℝ) ^ 2 * Ek) + (D : ℝ) ^ 2 * (m₁ + m₂)) := by
  set Dk := EL - Kk with hDk
  set T := ((q : ℝ) : ℂ) • (Kk * Dk + Dk * Kk) - ((1 - q : ℝ) : ℂ) • Dk with hTd
  set X := Dk + (h : ℂ) • (Dk + Kk * Dk + Dk * Kk) with hX
  set Rm := (EL' - Kk') - X - (h : ℂ) • Sm with hRm
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have eX : X = ((1 + h / q : ℝ) : ℂ) • Dk + ((h / q : ℝ) : ℂ) • T := by
    ext a b
    simp only [hX, hTd, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  have hXb : hsNorm X ≤ (1 + 2 * h / q + h) * hsNorm Dk := by
    rw [eX]
    refine (LF3_hs_add _ _).trans ?_
    rw [LF3_hs_smul, LF3_hs_smul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ h / q)
    have e : (1 + h / q) * hsNorm Dk + h / q * ((1 + q) * hsNorm Dk) =
        (1 + 2 * h / q + h) * hsNorm Dk := by field_simp; ring
    linarith
  have hSb : hsNorm ((h : ℂ) • Sm) ≤ h * ((D : ℝ) ^ 2 * Ek) := by
    rw [LF3_hs_smul, Complex.norm_real, Real.norm_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left (LF3_hs_entry _ _ hS) hh
  have eR : ∀ x y, Rm x y = (EL' x y - EL x y - (h : ℂ) * Idr x y) -
      (Kk' - Kk - (h : ℂ) • (Kk * Kk + Kk)) x y := by
    intro x y
    rw [hlin x y]
    simp only [hRm, hX, hDk, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_sub, Matrix.sub_mul, smul_eq_mul]
    ring
  have hRb : hsNorm Rm ≤ (D : ℝ) ^ 2 * (m₁ + m₂) := by
    refine LF3_hs_entry _ _ fun x y => ?_
    rw [eR x y]
    exact (norm_sub_le _ _).trans (add_le_add (hstep x y) (hkd x y))
  have hdec : EL' - Kk' = X + (h : ℂ) • Sm + Rm := by rw [hRm]; abel
  rw [hdec]
  refine (LF3_hs_add _ _).trans ?_
  have := LF3_hs_add X ((h : ℂ) • Sm)
  linarith


/-- `(D ρ² + ρ)(1 + 2 D ρ) ≤ 30 D² N^{16}` for `D, N ≥ 1` and `0 < ρ ≤ 2N`. -/
private lemma LF3_ar_Kd (D N ρ : ℝ) (hD : 1 ≤ D) (hN : 1 ≤ N) (hρ0 : 0 < ρ) (hρ : ρ ≤ 2 * N) :
    (D * ρ ^ 2 + ρ) * (1 + 2 * D * ρ) ≤ 30 * D ^ 2 * N ^ 16 := by
  have h0 : ρ ^ 2 ≤ 4 * N ^ 2 := by nlinarith
  have h1 : D * ρ ^ 2 + ρ ≤ 6 * D * N ^ 2 := by nlinarith
  have h2 : 1 + 2 * D * ρ ≤ 5 * D * N := by nlinarith
  have h3 : N ^ 3 ≤ N ^ 16 := pow_le_pow_right₀ hN (by norm_num)
  calc (D * ρ ^ 2 + ρ) * (1 + 2 * D * ρ) ≤ (6 * D * N ^ 2) * (5 * D * N) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 30 * D ^ 2 * N ^ 3 := by ring
    _ ≤ 30 * D ^ 2 * N ^ 16 := by gcongr

set_option maxHeartbeats 6400000 in
-- The arithmetic conditions on `N`, the grid and the recursion are handled together.
/-- The statement of `flowL2_exp`, from the one-step expansion `LF3_step`, the decomposition
`LF3_lin`, the sources `LF3_srcG`, (3.31) [flow_1G_res_2] (`flowG1_exp_paper`), the bound of
`LF3_k121`, the operator bound (3.67) [Tnorm] (`LF3_tOp`) and the discrete Grönwall bound
`LF3_gron`, on an expectation grid of `⌈N^{30}⌉` steps. -/
private lemma LF3_main (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t₀ : ℝ), 0 ≤ t₀ → t₀ ≤ 1 →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        hsNorm (ELmat (blockOULaw D N (ouMatLaw D N L t₀) S)
              (((Real.exp (-S / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z₁ S)
              (charFlowZ (lam D N A) z₂ S) -
            flowKmat (lam D N A) (Real.exp (-t₀)) z₁ z₂ S) ≤
          (N : ℝ) ^ τ' * ((flowTc (lam D N A) z / (flowTc (lam D N A) z - S)) ^ 2 *
              hsNorm (ELmat (ouMatLaw D N L t₀) (lam D N A) z₁ z₂ -
                KTheta (lam D N A) (Real.exp (-t₀)) z₁ z₂) +
            (N : ℝ) ^ (-εg) / (N * (flowTc (lam D N A) z - S) ^ 2 * flowIm (lam D N A) z S ^ 2) +
            (N : ℝ) ^ (2 * εg) /
              ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - S) ^ 3 * flowIm (lam D N A) z S ^ 4)) := by
  intro τ' hτ'
  set τ₁ := min τ' 1 / 4 with hτ₁
  have hτ₁0 : 0 < τ₁ := by have := lt_min hτ' one_pos; positivity
  have hτ₁1 : τ₁ ≤ 1 := by have := min_le_right τ' 1; linarith
  have hτ₁τ : τ₁ ≤ τ' / 4 := by have := min_le_left τ' 1; linarith
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  obtain ⟨Kst, hKst0, hKst⟩ := LF3_step D (by omega) τ hτ C'
  obtain ⟨Ns, hNs⟩ := LF3_srcG D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C' τ₁ hτ₁0
    hτ₁1
  obtain ⟨Ng1, hNg1⟩ := flowG1_exp_paper D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    τ₁ hτ₁0
  obtain ⟨Nk, hNk⟩ := LF3_k121 D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C' τ₁ hτ₁0
  set e2 := Real.exp (1 / 2) with he2
  set α : ℝ := (D : ℝ) ^ 2 * (D + 2 * D ^ 2) with hα
  set β : ℝ := (D : ℝ) ^ 2 * (2 * D ^ 2) with hβ
  set Cz : ℝ := 48 * (D : ℝ) ^ 5 + D ^ 2 * (Kst + 30 * D ^ 2) with hCz
  have hev : ∀ᶠ N : ℕ in Filter.atTop, Ns ≤ N ∧ Ng1 ≤ N ∧ Nk ≤ N ∧ 2 ≤ N ∧
      2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧ c * (N : ℝ) ^ (-εg) ≤ 1 ∧
      Real.exp 1 * (N : ℝ) ^ (0 : ℝ) ≤ (N : ℝ) ^ τ' ∧
      (2 * e2 ^ 6 * α) * (N : ℝ) ^ (τ₁ + τ₁) ≤ (N : ℝ) ^ τ' ∧
      (e2 ^ 4 * β * (1 + τ₁⁻¹)) * (N : ℝ) ^ (τ₁ + τ₁ + τ₁) ≤ (N : ℝ) ^ τ' ∧
      8 * Real.exp 1 * Cz ≤ (N : ℝ) := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    exact (Filter.eventually_ge_atTop Ns).and ((Filter.eventually_ge_atTop Ng1).and
      ((Filter.eventually_ge_atTop Nk).and ((Filter.eventually_ge_atTop 2).and
      (((t1.const_mul 2).eventually (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and
      (((t2.const_mul c).eventually (Iic_mem_nhds (by simp : c * 0 < 1))).and
      ((LF3_ev_pow _ _ _ hτ').and ((LF3_ev_pow _ _ _ (by linarith)).and
      ((LF3_ev_pow _ _ _ (by linarith)).and
      ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _)))))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN L t₀ ht0 ht1 A z S hadm z₁ z₂ h₁ h₂ => ?_⟩
  obtain ⟨hNs', hNg1', hNk', hN2, hAN, hcN, hA1, hA2, hA3, hA4⟩ := hN₀ N hN
  rw [Real.rpow_zero, mul_one] at hA1
  have hθ0 : 0 ≤ Real.exp (-t₀) := (Real.exp_pos _).le
  have hθ1 : Real.exp (-t₀) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hcl : LLClass D N C' (Real.exp (-t₀)) (ouMatLaw D N L t₀) := hC' N L t₀ ht0
  have := hcl.prob
  have : NeZero D := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hD1r : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hT1 : 1 ≤ (N : ℝ) ^ τ' := Real.one_le_rpow hN1r hτ'.le
  obtain ⟨hΛ10, hzτ, hz, hm1, hq0, hq1, hS0, hSt, hη⟩ :=
    LF3_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  obtain ⟨-, hιS, hι0, hιS1, -, -, -⟩ := LF3_flow D N hD1 hN1 A hΛ10 z hz S hSt S hS0 le_rfl
  have hqS : 0 < flowTc (lam D N A) z - S := by linarith
  have hEgN : (N : ℝ) ^ εg * (N : ℝ) ^ εg = (N : ℝ) ^ (2 * εg) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  -- the start and the objects at time `0`
  have hst : ∀ r : ℝ, r = 0 → LF3_EL (ouMatLaw D N L t₀) (lam D N A) z₁ z₂ r -
      flowKmat (lam D N A) (Real.exp (-t₀)) z₁ z₂ r =
      ELmat (ouMatLaw D N L t₀) (lam D N A) z₁ z₂ - KTheta (lam D N A) (Real.exp (-t₀)) z₁ z₂ := by
    intro r hr
    subst hr
    have hz0 : ∀ w : ℂ, charFlowZ (lam D N A) w 0 = w := fun w => by simp [charFlowZ]
    have he : ((Real.exp (-0 / 2) : ℝ) : ℂ) • lam D N A = lam D N A := by simp
    rw [(LF3_zero (lam D N A) (Real.exp (-t₀)) z z₁ z₂ z₁ 0).2.1]
    simp only [LF3_EL, hz0, he, LF3_bOU0]
  set a₀ := hsNorm (ELmat (ouMatLaw D N L t₀) (lam D N A) z₁ z₂ -
    KTheta (lam D N A) (Real.exp (-t₀)) z₁ z₂) with ha₀d
  have ha₀ : 0 ≤ a₀ := Real.sqrt_nonneg _
  have hP0 : (0 : ℝ) ≤ (N : ℝ) ^ (-εg) / (N * (flowTc (lam D N A) z - S) ^ 2 *
      flowIm (lam D N A) z S ^ 2) := by positivity
  have hP1 : (0 : ℝ) ≤ (N : ℝ) ^ (2 * εg) / ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - S) ^ 3 *
      flowIm (lam D N A) z S ^ 4) := by positivity
  change hsNorm (LF3_EL (ouMatLaw D N L t₀) (lam D N A) z₁ z₂ S -
    flowKmat (lam D N A) (Real.exp (-t₀)) z₁ z₂ S) ≤ _
  rcases hS0.eq_or_lt with hS | hSpos
  · -- the horizon `S = 0`
    rw [hst S hS.symm, ← ha₀d, ← hS, sub_zero, div_self hq0.ne', one_pow, one_mul]
    calc a₀ ≤ (N : ℝ) ^ τ' * a₀ := le_mul_of_one_le_left ha₀ hT1
      _ ≤ _ := mul_le_mul_of_nonneg_left (by rw [← hS, sub_zero] at hP0 hP1; linarith)
          (by positivity)
  -- the expectation grid with `K = ⌈N^{30}⌉` steps
  set q₀ := flowTc (lam D N A) z with hq₀
  set ι₀ := (mExt (lam D N A) z).im with hι₀
  set K : ℕ := ⌈(N : ℝ) ^ (30 : ℕ)⌉₊ with hKdef
  have hK1 : (N : ℝ) ^ (30 : ℕ) ≤ K := Nat.le_ceil _
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) hK1
  set h := S / K with hhdef
  have hhpos : 0 < h := div_pos hSpos hKpos
  have hKh : (K : ℝ) * h = S := by rw [hhdef]; field_simp
  have hKq : (K : ℝ) * h < q₀ := by rw [hKh]; exact hSt
  have hS1 : S ≤ 1 := by linarith
  have hKh2 : (K : ℝ) * h ^ 2 ≤ 1 / (N : ℝ) ^ 30 := by
    have e : (K : ℝ) * h ^ 2 = S * (S / K) := by rw [hhdef]; field_simp
    rw [e]
    calc S * (S / K) ≤ 1 * (1 / K) := mul_le_mul hS1
          (div_le_div_of_nonneg_right hS1 hKpos.le) (by positivity) zero_le_one
      _ = 1 / K := one_mul _
      _ ≤ 1 / (N : ℝ) ^ 30 := one_div_le_one_div_of_le (by positivity) hK1
  have hgrid : ∀ k : ℕ, k ≤ K → 0 ≤ (k : ℝ) * h ∧ (k : ℝ) * h ≤ S := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    rw [← hKh]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hhpos.le
  -- `q_S⁻¹ ≤ 2N` and the constant of the deterministic step
  have hqinv : (q₀ - S)⁻¹ ≤ 2 * N := by
    have hle := LF3_eta_le D N hD1 hN1 A hΛ10 z hz S hSt hq1 S hS0 le_rfl
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
  set ρ := (q₀ - S)⁻¹ with hρ
  have hρ0 : 0 < ρ := inv_pos.2 hqS
  set Kd := ((D : ℝ) * ρ ^ 2 + ρ) * (1 + 2 * D * ρ) with hKd
  have hKd30 : Kd ≤ 30 * (D : ℝ) ^ 2 * (N : ℝ) ^ 16 :=
    LF3_ar_Kd (D : ℝ) N ρ hD1r hN1r hρ0 hqinv
  -- the bounds of the recursion
  set P := (N : ℝ) ^ τ₁ with hP
  set Eg := (N : ℝ) ^ εg with hEg
  set u := (N : ℝ) ^ (-εg) with hu
  set Y := 12 * (D : ℝ) ^ 3 * (N : ℝ) ^ 4 * (4 * (N : ℝ) ^ (-(10 : ℝ))) with hY
  set aC := (D : ℝ) ^ 2 * ((D + 2 * D ^ 2) * (P * P * (Eg * Eg) / (N : ℝ) ^ 2)) with haC
  set bC := (D : ℝ) ^ 2 * (2 * D ^ 2 * (P * P * u / N)) with hbC
  set R := (D : ℝ) ^ 2 * (Kst * (N : ℝ) ^ 16 * h ^ 2 + Kd * h ^ 2) with hR
  set Δ : ℕ → Matrix (Fin D) (Fin D) ℂ := fun k =>
    LF3_EL (ouMatLaw D N L t₀) (lam D N A) z₁ z₂ (k * h) -
      flowKmat (lam D N A) (Real.exp (-t₀)) z₁ z₂ (k * h) with hΔ
  set βk : ℕ → ℝ := fun k => h * (aC / ((q₀ - k * h) ^ 4 * flowIm (lam D N A) z (k * h) ^ 4) +
    bC / ((q₀ - k * h) ^ 3 * flowIm (lam D N A) z (k * h) ^ 2) + (D : ℝ) ^ 2 * Y) + R with hβk
  have hP0' : 0 ≤ P := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have haC0 : 0 ≤ aC := by positivity
  have hbC0 : 0 ≤ bC := by positivity
  have hR0 : 0 ≤ R := by positivity
  have hβ0 : ∀ k, k < K → 0 ≤ βk k := by
    intro k hk
    obtain ⟨hk0, hkS⟩ := hgrid k hk.le
    obtain ⟨-, hιk, -, -, -, -, -⟩ := LF3_flow D N hD1 hN1 A hΛ10 z hz S hSt _ hk0 hkS
    have hqk : 0 < q₀ - k * h := by linarith
    have hιk0 : 0 < flowIm (lam D N A) z (k * h) := by
      rw [hιk]; exact mul_pos (Real.exp_pos _) hι0
    simp only [hβk]
    positivity
  -- one step of the recursion
  have hrec : ∀ k, k < K → hsNorm (Δ (k + 1)) ≤
      (1 + 2 * h / (q₀ - k * h) + h) * hsNorm (Δ k) + βk k := by
    intro k hk
    obtain ⟨hk0, hkS⟩ := hgrid k hk.le
    have hk1 : ((k + 1 : ℕ) : ℝ) * h = k * h + h := by push_cast; ring
    have hsh : (k : ℝ) * h + h ≤ S := by rw [← hk1]; exact (hgrid (k + 1) hk).2
    have hks : (k : ℝ) * h < q₀ := lt_of_le_of_lt hkS hSt
    have hadmk := LF3_adm_mono D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
      _ hk0 hkS
    obtain ⟨hηk, hιk, -, -, -, -, hqιk⟩ := LF3_flow D N hD1 hN1 A hΛ10 z hz S hSt _ hk0 hkS
    have hιk0 : 0 < flowIm (lam D N A) z (k * h) := by
      rw [hιk]; exact mul_pos (Real.exp_pos _) hι0
    have hqk : 0 < q₀ - k * h := by linarith
    have hclk : LLClass D N _ _ (blockOULaw D N (ouMatLaw D N L t₀) (k * h)) :=
      (Classical.choose_spec (llClass_blockOU D C')) N _ _ _ hθ0 hθ1 hk0 hcl
    have := hclk.prob
    -- the ingredients at the grid time `u_k = k h`
    have hstep := fun x y => hKst N hN2 _ hθ0 hθ1 _ hcl A z S hΛ10 hzτ hz hm1 hq1 hS0 hSt
      (fun s hs0 hsS => (hη s hs0 hsS).1) z₁ z₂ h₁ h₂ (k * h) h hk0 hhpos hsh x y
    have hkd := fun x y => LF3_Kd D N A hΛ10 z hz S hSt _ hθ0 hθ1 z₁ z₂ h₁ h₂ (k * h) h hk0
      hhpos.le hsh x y
    have hlin := fun x y => LF3_lin D N hD1 hN1 A hΛ10 z hz (k * h) hks hk0 (Real.exp (-t₀))
      (ouMatLaw D N L t₀) hclk.herm z₁ z₂ h₁ h₂ x y
    have hsrc := fun x y => hNs N hNs' _ hθ0 hθ1 _ hcl A z S hadm (k * h) hk0 hkS z₁ z₂ h₁ h₂ x y
    have hEd : ∀ (w : ℂ), (w = z ∨ w = star z) → ∀ a : Fin D,
        ‖∫ H, LF3_d (lam D N A) w (k * h) H a ∂(blockOULaw D N (ouMatLaw D N L t₀) (k * h))‖ ≤
          P * (u / (N * (q₀ - k * h) * flowIm (lam D N A) z (k * h))) := by
      intro w hw a
      rw [LF3_dconj D N hD1 hN1 A z hz (k * h) hks _ hclk.herm w hw a]
      exact hNg1 N hNg1' L t₀ ht0 ht1 A z (k * h) hadmk a
    have hKt : ∀ (v w : ℂ), (v = z ∨ v = star z) → (w = z ∨ w = star z) → ∀ a b c : Fin D,
        ‖flowKten3 (lam D N A) (Real.exp (-t₀)) v w v (k * h) a b c‖ ≤
          P * (flowIm (lam D N A) z (k * h) / (charFlowZ (lam D N A) z (k * h)).im ^ 2) :=
      fun v w hv hw a b c => (LF3_t3_entry _ a b c).trans
        (hNk N hNk' _ hθ0 hθ1 _ hcl A z (k * h) hadmk v w hv hw)
    have hT := LF3_tOp D N A hΛ10 z hz S hSt _ hθ0 hθ1 z₁ z₂ h₁ h₂ (k * h) hk0 hkS
      (LF3_EL (ouMatLaw D N L t₀) (lam D N A) z₁ z₂ (k * h) -
        flowKmat (lam D N A) (Real.exp (-t₀)) z₁ z₂ (k * h))
    -- the source matrix and its entries
    set Sm : Matrix (Fin D) (Fin D) ℂ := Matrix.of fun x y =>
      (∫ H, LF3_g (lam D N A) (Real.exp (-t₀)) z₁ z₂ (k * h) H x y
          ∂(blockOULaw D N (ouMatLaw D N L t₀) (k * h))) +
        (D : ℂ) * ∑ a, ((∫ H, LF3_d (lam D N A) z₁ (k * h) H a
            ∂(blockOULaw D N (ouMatLaw D N L t₀) (k * h))) *
            flowKten3 (lam D N A) (Real.exp (-t₀)) z₁ z₂ z₁ (k * h) x y a +
          (∫ H, LF3_d (lam D N A) z₂ (k * h) H a
            ∂(blockOULaw D N (ouMatLaw D N L t₀) (k * h))) *
            flowKten3 (lam D N A) (Real.exp (-t₀)) z₂ z₁ z₂ (k * h) y x a) with hSm
    set q := q₀ - k * h with hq
    set ι := flowIm (lam D N A) z (k * h) with hι
    set η := (charFlowZ (lam D N A) z (k * h)).im with hηd
    have hSb : ∀ x y, ‖Sm x y‖ ≤ (aC / ((D : ℝ) ^ 2 * (q ^ 4 * ι ^ 4)) +
        bC / ((D : ℝ) ^ 2 * (q ^ 3 * ι ^ 2)) + Y) := by
      intro x y
      simp only [hSm, Matrix.of_apply]
      refine (norm_add_le _ _).trans ?_
      have h1 := hsrc x y
      have h2 : ‖(D : ℂ) * ∑ a, ((∫ H, LF3_d (lam D N A) z₁ (k * h) H a
            ∂(blockOULaw D N (ouMatLaw D N L t₀) (k * h))) *
            flowKten3 (lam D N A) (Real.exp (-t₀)) z₁ z₂ z₁ (k * h) x y a +
          (∫ H, LF3_d (lam D N A) z₂ (k * h) H a
            ∂(blockOULaw D N (ouMatLaw D N L t₀) (k * h))) *
            flowKten3 (lam D N A) (Real.exp (-t₀)) z₂ z₁ z₂ (k * h) y x a)‖ ≤
          D * (D * (2 * (P * P * u / (N * q ^ 3 * ι ^ 2)))) := by
        rw [norm_mul, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) hD0
        have hone : P * (u / (N * q * ι)) * (P * (ι / η ^ 2)) ≤ P * P * u / (N * q ^ 3 * ι ^ 2) :=
          LF3_ar_S N P u q ι η hNpos hP0' (by positivity) hqk hιk0 hηk hqιk
        calc ∑ a, ‖(∫ H, LF3_d (lam D N A) z₁ (k * h) H a
              ∂(blockOULaw D N (ouMatLaw D N L t₀) (k * h))) *
              flowKten3 (lam D N A) (Real.exp (-t₀)) z₁ z₂ z₁ (k * h) x y a +
            (∫ H, LF3_d (lam D N A) z₂ (k * h) H a
              ∂(blockOULaw D N (ouMatLaw D N L t₀) (k * h))) *
              flowKten3 (lam D N A) (Real.exp (-t₀)) z₂ z₁ z₂ (k * h) y x a‖
            ≤ ∑ _a : Fin D, 2 * (P * P * u / (N * q ^ 3 * ι ^ 2)) := by
              refine Finset.sum_le_sum fun a _ => (norm_add_le _ _).trans ?_
              rw [norm_mul, norm_mul]
              have v1 := mul_le_mul (hEd z₁ h₁ a) (hKt z₁ z₂ h₁ h₂ x y a) (norm_nonneg _)
                (by positivity)
              have v2 := mul_le_mul (hEd z₂ h₂ a) (hKt z₂ z₁ h₂ h₁ y x a) (norm_nonneg _)
                (by positivity)
              linarith
          _ = D * (2 * (P * P * u / (N * q ^ 3 * ι ^ 2))) := by simp
      have hDpos : (0 : ℝ) < D := by linarith
      have e1 : (D + 2 * (D : ℝ) ^ 2) * (P * P * (Eg * Eg) / ((N : ℝ) ^ 2 * q ^ 4 * ι ^ 4)) =
          aC / ((D : ℝ) ^ 2 * (q ^ 4 * ι ^ 4)) := by
        rw [haC]; field_simp
      have e2 : (D : ℝ) * (D * (2 * (P * P * u / (N * q ^ 3 * ι ^ 2)))) =
          bC / ((D : ℝ) ^ 2 * (q ^ 3 * ι ^ 2)) := by
        rw [hbC]; field_simp
      rw [← e1, ← e2]
      linarith
    have hrec1 := LF3_rec _ _ _ _ Sm (fun x y => ∫ H, LF3_dr (lam D N A) z₁ z₂ (k * h) H x y
        ∂(blockOULaw D N (ouMatLaw D N L t₀) (k * h))) h q (Kst * (N : ℝ) ^ 16 * h ^ 2)
      (Kd * h ^ 2) _ hhpos.le hqk hT (fun x y => hlin x y) (fun x y => hstep x y)
      (fun x y => hkd x y) hSb
    have hΔk1 : Δ (k + 1) = LF3_EL (ouMatLaw D N L t₀) (lam D N A) z₁ z₂ (k * h + h) -
        flowKmat (lam D N A) (Real.exp (-t₀)) z₁ z₂ (k * h + h) := by
      simp only [hΔ, hk1]
    have hDpos : (0 : ℝ) < D := by linarith
    have ekey : (D : ℝ) ^ 2 * (aC / ((D : ℝ) ^ 2 * (q ^ 4 * ι ^ 4)) +
        bC / ((D : ℝ) ^ 2 * (q ^ 3 * ι ^ 2)) + Y) =
        aC / (q ^ 4 * ι ^ 4) + bC / (q ^ 3 * ι ^ 2) + (D : ℝ) ^ 2 * Y := by
      field_simp
    rw [ekey] at hrec1
    rw [hΔk1]
    exact hrec1
  have hg := LF3_gron K h q₀ hhpos hKq (fun k => hsNorm (Δ k)) βk
    (fun k => Real.sqrt_nonneg _) hβ0 hrec
  have hιk : ∀ k : ℕ, k < K → ι₀ ≤ flowIm (lam D N A) z (k * h) := by
    intro k hk
    obtain ⟨hk0, hkS⟩ := hgrid k hk.le
    obtain ⟨-, hιk, -, -, -, -, -⟩ := LF3_flow D N hD1 hN1 A hΛ10 z hz S hSt _ hk0 hkS
    rw [hιk]
    exact le_mul_of_one_le_left hι0.le (Real.one_le_exp (by positivity))
  have hsum := LF3_sumbd K h q₀ ι₀ aC bC ((D : ℝ) ^ 2 * Y) R
    (fun k => flowIm (lam D N A) z (k * h)) hhpos hKq hq1 hι0 hιk haC0 hbC0 (by positivity) hR0
  -- the start and the end of the grid
  have hΔ0 : Δ 0 = ELmat (ouMatLaw D N L t₀) (lam D N A) z₁ z₂ -
      KTheta (lam D N A) (Real.exp (-t₀)) z₁ z₂ := hst _ (by simp)
  have hΔK : Δ K = LF3_EL (ouMatLaw D N L t₀) (lam D N A) z₁ z₂ S -
      flowKmat (lam D N A) (Real.exp (-t₀)) z₁ z₂ S := by
    simp only [hΔ, hKh]
  rw [hΔ0, hΔK, hKh] at hg
  rw [hKh] at hsum
  -- the remainders
  set Z := S * ((D : ℝ) ^ 2 * Y) + K * R with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hN10 : (N : ℝ) ^ (-(10 : ℝ)) = 1 / (N : ℝ) ^ 10 := by
    rw [Real.rpow_neg hNpos.le, show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      one_div]
  have hZle : Z ≤ Cz / (N : ℝ) ^ 6 := by
    have h1 : S * ((D : ℝ) ^ 2 * Y) ≤ 48 * (D : ℝ) ^ 5 / (N : ℝ) ^ 6 := by
      have e : 48 * (D : ℝ) ^ 5 / (N : ℝ) ^ 6 = (D : ℝ) ^ 2 * Y := by
        rw [hY, hN10]; field_simp; ring
      rw [e]
      exact mul_le_of_le_one_left (by positivity) hS1
    have h2 : (K : ℝ) * R ≤ D ^ 2 * (Kst + 30 * D ^ 2) / (N : ℝ) ^ 6 := by
      have e : (K : ℝ) * R = D ^ 2 * (Kst * (N : ℝ) ^ 16 + Kd) * (K * h ^ 2) := by
        rw [hR]; ring
      rw [e]
      have hb : (D : ℝ) ^ 2 * (Kst * (N : ℝ) ^ 16 + Kd) ≤
          D ^ 2 * (Kst + 30 * D ^ 2) * (N : ℝ) ^ 16 := by
        have : Kst * (N : ℝ) ^ 16 + Kd ≤ (Kst + 30 * D ^ 2) * (N : ℝ) ^ 16 := by
          rw [add_mul]; linarith
        calc (D : ℝ) ^ 2 * (Kst * (N : ℝ) ^ 16 + Kd) ≤ D ^ 2 * ((Kst + 30 * D ^ 2) *
              (N : ℝ) ^ 16) := mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by ring
      have hKd0 : 0 ≤ Kd := by positivity
      calc (D : ℝ) ^ 2 * (Kst * (N : ℝ) ^ 16 + Kd) * (K * h ^ 2)
          ≤ D ^ 2 * (Kst + 30 * D ^ 2) * (N : ℝ) ^ 16 * (1 / (N : ℝ) ^ 30) :=
            mul_le_mul hb hKh2 (by positivity) (by positivity)
        _ = D ^ 2 * (Kst + 30 * D ^ 2) / (N : ℝ) ^ 14 := by field_simp
        _ ≤ D ^ 2 * (Kst + 30 * D ^ 2) / (N : ℝ) ^ 6 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (pow_le_pow_right₀ hN1r (by norm_num))
    rw [hZ, hCz, add_div]
    exact add_le_add h1 h2
  -- the logarithm
  have hratio : 1 ≤ q₀ / (q₀ - S) := by rw [le_div_iff₀ hqS]; linarith
  have hLg0 : 0 ≤ Real.log (q₀ / (q₀ - S)) := Real.log_nonneg hratio
  have hLg : Real.log (q₀ / (q₀ - S)) ≤ (1 + τ₁⁻¹) * P := by
    refine le_trans ?_ (LF3_log_le N τ₁ hN1r hτ₁0)
    apply Real.log_le_log (by linarith)
    have h1 : q₀ / (q₀ - S) ≤ (q₀ - S)⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_of_le_one_left (by positivity) hq1
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    calc q₀ / (q₀ - S) ≤ (q₀ - S)⁻¹ := h1
      _ ≤ 2 * N := hqinv
      _ ≤ Real.exp 1 * N := mul_le_mul_of_nonneg_right h2 hNpos.le
  -- assembly
  have hE1 : 1 ≤ Real.exp (S / 2) := Real.one_le_exp (by positivity)
  have hE : Real.exp (S / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
  have hιS' : Real.exp (S / 2) * ι₀ ≤ 1 := by rw [← hιS]; exact hιS1.le
  have hES : Real.exp S = Real.exp (S / 2) ^ 2 := by rw [sq, ← Real.exp_add]; ring_nf
  have ha : (q₀ - S) ^ 2 * hsNorm (LF3_EL (ouMatLaw D N L t₀) (lam D N A) z₁ z₂ S -
      flowKmat (lam D N A) (Real.exp (-t₀)) z₁ z₂ S) ≤ Real.exp (S / 2) ^ 2 *
      (q₀ ^ 2 * a₀ + α * (P * P) * (Eg * Eg) / (N : ℝ) ^ 2 / ι₀ ^ 4 * (q₀ - S)⁻¹ +
        β * (P * P) * u / N / ι₀ ^ 2 * Real.log (q₀ / (q₀ - S)) + Z) := by
    rw [← hES]
    refine hg.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    have e1 : α * (P * P) * (Eg * Eg) / (N : ℝ) ^ 2 / ι₀ ^ 4 = aC / ι₀ ^ 4 := by
      rw [hα, haC]; ring
    have e2 : β * (P * P) * u / N / ι₀ ^ 2 = bC / ι₀ ^ 2 := by rw [hβ, hbC]; ring
    rw [e1, e2, hZ]
    linarith only [hsum]
  have hPP : P * P = (N : ℝ) ^ (τ₁ + τ₁) := (Real.rpow_add hNpos _ _).symm
  have hPPP : P * P * ((1 + τ₁⁻¹) * P) = (1 + τ₁⁻¹) * (N : ℝ) ^ (τ₁ + τ₁ + τ₁) := by
    rw [Real.rpow_add hNpos, Real.rpow_add hNpos]; ring
  have hfin := LF3_ar_fin N (q₀ - S) q₀ ι₀ (Real.exp (S / 2)) a₀ _ α β (P * P) u (Eg * Eg)
    (Real.log (q₀ / (q₀ - S))) ((1 + τ₁⁻¹) * P) Z Cz ((N : ℝ) ^ τ') hNr hqS hι0 hE1 hE hιS'
    (by linarith) ha₀ (by positivity) (by positivity) (by positivity) (by positivity)
    (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1r hεg.le)
      (Real.one_le_rpow hN1r hεg.le)) hLg hLg0 hZ0 hqinv hZle ha hA1
    (by rw [hPP]; linarith only [hA2]) (by
      have : e2 ^ 4 * β * (P * P) * ((1 + τ₁⁻¹) * P) =
          (e2 ^ 4 * β * (1 + τ₁⁻¹)) * (N : ℝ) ^ (τ₁ + τ₁ + τ₁) := by
        rw [mul_assoc (e2 ^ 4 * β), hPPP]; ring
      rw [this]; exact hA3)
    (hA4.trans (le_self_pow₀ hN1r (by norm_num))) hT1
  rw [← hιS, hEgN] at hfin
  exact hfin

/-- Lemma 3.11 [lem_flow_3], (3.32) [flow_3_result], at one time, for the law of `H_{t₀}` of
(4.1) [defVt], `t₀ ∈ [0, 1]`, `θ = e^{-t₀}`: at the law (3.13) [eq:Gauss_div] at time `S`,
`‖E L_S - K_S‖₂ ≤ N^{τ'} ((q₀/q_S)² ‖E L_0 - K_θ‖₂ + N^{-ε_g}/(N q_S² (Im m_S)²) +
N^{2ε_g}/(N² q_S³ (Im m_S)⁴))`. -/
theorem flowL2_exp (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t₀ : ℝ), 0 ≤ t₀ → t₀ ≤ 1 →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        hsNorm (ELmat (blockOULaw D N (ouMatLaw D N L t₀) S)
              (((Real.exp (-S / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z₁ S)
              (charFlowZ (lam D N A) z₂ S) -
            flowKmat (lam D N A) (Real.exp (-t₀)) z₁ z₂ S) ≤
          (N : ℝ) ^ τ' * ((flowTc (lam D N A) z / (flowTc (lam D N A) z - S)) ^ 2 *
              hsNorm (ELmat (ouMatLaw D N L t₀) (lam D N A) z₁ z₂ -
                KTheta (lam D N A) (Real.exp (-t₀)) z₁ z₂) +
            (N : ℝ) ^ (-εg) / (N * (flowTc (lam D N A) z - S) ^ 2 * flowIm (lam D N A) z S ^ 2) +
            (N : ℝ) ^ (2 * εg) /
              ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - S) ^ 3 * flowIm (lam D N A) z S ^ 4)) := by
  exact LF3_main D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C


/-- The final inequality for (3.33) [flow_3_result_2]: with `q₀ ι₀ ≤ η₀`, `ι_S = E ι₀`,
`1 ≤ E ≤ e^{1/2}`, the start bound `a₀ ≤ P N⁻¹ η₀⁻² u_m`, the bound (3.32) [flow_3_result]
`a ≤ P ((q₀/q_S)² a₀ + u_e/(N q_S² ι_S²) + v/(N² q_S³ ι_S⁴))`, `u_e ≤ u_m`,
`v/(N q_S ι_S²) ≤ u_m` and `(e + 2) P² ≤ T`, the bound `a ≤ T u_m/(N q_S² ι_S²)`. -/
private lemma LF3_ar_p (N q₀ qS ι₀ η₀ E a₀ aS P um ue v T : ℝ) (hN : 0 < N) (hq₀ : 0 ≤ q₀)
    (hqS : 0 < qS) (hι₀ : 0 < ι₀) (hη₀ : 0 < η₀) (hqη : q₀ * ι₀ ≤ η₀) (hE1 : 1 ≤ E)
    (hE : E ≤ Real.exp (1 / 2)) (hP : 1 ≤ P) (hue : 0 ≤ ue) (hum : ue ≤ um)
    (ha₀ : a₀ ≤ P * (N⁻¹ * (η₀ ^ 2)⁻¹ * um))
    (haS : aS ≤ P * ((q₀ / qS) ^ 2 * a₀ + ue / (N * qS ^ 2 * (E * ι₀) ^ 2) +
      v / (N ^ 2 * qS ^ 3 * (E * ι₀) ^ 4)))
    (hv : v / (N * qS * (E * ι₀) ^ 2) ≤ um) (hfin : (Real.exp 1 + 2) * (P * P) ≤ T) :
    aS ≤ T * (um / (N * qS ^ 2 * (E * ι₀) ^ 2)) := by
  set ι := E * ι₀ with hι
  have hE0 : 0 < E := by linarith
  have hιpos : 0 < ι := by positivity
  set W := um / (N * qS ^ 2 * ι ^ 2) with hW
  have hum0 : 0 ≤ um := hue.trans hum
  have hW0 : 0 ≤ W := by positivity
  have hE2 : E ^ 2 ≤ Real.exp 1 := by
    have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [sq, ← Real.exp_add]; norm_num
    rw [← this]; exact pow_le_pow_left₀ hE0.le hE 2
  -- the first term
  have t1 : (q₀ / qS) ^ 2 * a₀ ≤ P * Real.exp 1 * W := by
    have hq2 : (q₀ / qS) ^ 2 * (N⁻¹ * (η₀ ^ 2)⁻¹ * um) ≤ Real.exp 1 * W := by
      have hq0η : q₀ ^ 2 * ι₀ ^ 2 ≤ η₀ ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hqη 2
        nlinarith
      have e : (q₀ / qS) ^ 2 * (N⁻¹ * (η₀ ^ 2)⁻¹ * um) =
          (q₀ ^ 2 * ι₀ ^ 2 / η₀ ^ 2) * (E ^ 2 * W) := by
        rw [hW, hι]; field_simp
      rw [e]
      have h1 : q₀ ^ 2 * ι₀ ^ 2 / η₀ ^ 2 ≤ 1 := (div_le_one (by positivity)).2 hq0η
      have h2 : E ^ 2 * W ≤ Real.exp 1 * W := mul_le_mul_of_nonneg_right hE2 hW0
      calc (q₀ ^ 2 * ι₀ ^ 2 / η₀ ^ 2) * (E ^ 2 * W) ≤ 1 * (E ^ 2 * W) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ Real.exp 1 * W := by linarith
    calc (q₀ / qS) ^ 2 * a₀ ≤ (q₀ / qS) ^ 2 * (P * (N⁻¹ * (η₀ ^ 2)⁻¹ * um)) :=
          mul_le_mul_of_nonneg_left ha₀ (by positivity)
      _ = P * ((q₀ / qS) ^ 2 * (N⁻¹ * (η₀ ^ 2)⁻¹ * um)) := by ring
      _ ≤ P * (Real.exp 1 * W) := mul_le_mul_of_nonneg_left hq2 (by linarith)
      _ = P * Real.exp 1 * W := by ring
  -- the second and the third terms
  have t2 : ue / (N * qS ^ 2 * ι ^ 2) ≤ W := div_le_div_of_nonneg_right hum (by positivity)
  have t3 : v / (N ^ 2 * qS ^ 3 * ι ^ 4) ≤ W := by
    have e : v / (N ^ 2 * qS ^ 3 * ι ^ 4) =
        (v / (N * qS * ι ^ 2)) * (1 / (N * qS ^ 2 * ι ^ 2)) := by
      field_simp
    rw [e, hW, div_eq_mul_one_div um]
    exact mul_le_mul_of_nonneg_right hv (by positivity)
  have hsum : (q₀ / qS) ^ 2 * a₀ + ue / (N * qS ^ 2 * ι ^ 2) + v / (N ^ 2 * qS ^ 3 * ι ^ 4) ≤
      (P * Real.exp 1 + 2) * W := by linarith
  calc aS ≤ P * ((q₀ / qS) ^ 2 * a₀ + ue / (N * qS ^ 2 * ι ^ 2) +
        v / (N ^ 2 * qS ^ 3 * ι ^ 4)) := haS
    _ ≤ P * ((P * Real.exp 1 + 2) * W) := mul_le_mul_of_nonneg_left hsum (by linarith)
    _ ≤ (Real.exp 1 + 2) * (P * P) * W := by
        have : P * ((P * Real.exp 1 + 2) * W) = (P * P * Real.exp 1 + 2 * P) * W := by ring
        rw [this]
        apply mul_le_mul_of_nonneg_right _ hW0
        nlinarith [Real.exp_pos 1]
    _ ≤ T * W := mul_le_mul_of_nonneg_right hfin hW0

set_option maxHeartbeats 1600000 in
-- The arithmetic conditions on `N` are handled together.
/-- The statement of `flowL2_exp_paper`, from `flowL2_exp` and (3.25) [largG_Ex]
(`lemma_G_large_2_theta`) at the start. -/
private lemma LF3_paper (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4)
    (hC₀ : 6 < C₀) (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t₀ : ℝ), 0 ≤ t₀ → t₀ ≤ 1 →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        hsNorm (ELmat (blockOULaw D N (ouMatLaw D N L t₀) S)
              (((Real.exp (-S / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z₁ S)
              (charFlowZ (lam D N A) z₂ S) -
            flowKmat (lam D N A) (Real.exp (-t₀)) z₁ z₂ S) ≤
          (N : ℝ) ^ τ' * ((N : ℝ) ^ (-min τe εg) /
            (N * (flowTc (lam D N A) z - S) ^ 2 * flowIm (lam D N A) z S ^ 2)) := by
  intro τ' hτ'
  set τ₁ := τ' / 3 with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  obtain ⟨N₁, hN₁⟩ := LF3_main D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C τ₁ hτ₁0
  obtain ⟨N₂, hN₂⟩ := lemma_G_large_2_theta D hD δA τ τe εg c hδA hτ hτe hεg hεg₁ hεg₂ hc C
    τ₁ hτ₁0
  have hev : ∀ᶠ N : ℕ in Filter.atTop, N₁ ≤ N ∧ N₂ ≤ N ∧ 2 ≤ N ∧
      2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧ c * (N : ℝ) ^ (-εg) ≤ 1 ∧
      2 * (N : ℝ) ^ (2 * εg) ≤ (N : ℝ) ^ ((C₀ - 1) * εg) ∧
      (Real.exp 1 + 2) * (N : ℝ) ^ (τ₁ + τ₁) ≤ (N : ℝ) ^ τ' := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    exact (Filter.eventually_ge_atTop N₁).and ((Filter.eventually_ge_atTop N₂).and
      ((Filter.eventually_ge_atTop 2).and
      (((t1.const_mul 2).eventually (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and
      (((t2.const_mul c).eventually (Iic_mem_nhds (by simp : c * 0 < 1))).and
      ((LF3_ev_pow _ _ _ (by nlinarith)).and (LF3_ev_pow _ _ _ (by linarith)))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN L t₀ ht0 ht1 A z S hadm z₁ z₂ h₁ h₂ => ?_⟩
  obtain ⟨hN1', hN2', hN2, hAN, hcN, hA, hfin⟩ := hN₀ N hN
  have : NeZero D := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 := hN₁ N hN1' L t₀ ht0 ht1 A z S hadm z₁ z₂ h₁ h₂
  have h2 := (hN₂ N hN2' L t₀ ht0 ht1 A hadm.1 z hadm.2.1 hadm.2.2.1 hadm.2.2.2.1
    hadm.2.2.2.2.1 hadm.2.2.2.2.2.1).2 z₁ z₂ h₁ h₂
  obtain ⟨hΛ10, -, hz, -, hq0, hq1, hS0, hSt, hη⟩ :=
    LF3_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  obtain ⟨hηS, hιS, hι0, -, -, -, -⟩ := LF3_flow D N hD1 hN1 A hΛ10 z hz S hSt S hS0 le_rfl
  have hηle := LF3_eta_le D N hD1 hN1 A hΛ10 z hz S hSt hq1 S hS0 le_rfl
  have hqS : 0 < flowTc (lam D N A) z - S := by linarith
  have hE1 : 1 ≤ Real.exp (S / 2) := Real.one_le_exp (by positivity)
  have hE : Real.exp (S / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
  -- `q₀ Im m ≤ η` at the start
  have hqη : flowTc (lam D N A) z * (mExt (lam D N A) z).im ≤ z.im := by
    have hx : 0 < z.im / (mExt (lam D N A) z).im := div_pos hz hι0
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + z.im / (mExt (lam D N A) z).im by linarith)
    have hle : flowTc (lam D N A) z ≤ z.im / (mExt (lam D N A) z).im := by
      unfold flowTc; linarith
    calc flowTc (lam D N A) z * (mExt (lam D N A) z).im
        ≤ z.im / (mExt (lam D N A) z).im * (mExt (lam D N A) z).im :=
          mul_le_mul_of_nonneg_right hle hι0.le
      _ = z.im := by field_simp
  -- `N^{-ε_g} ≤ N^{-(τ_e ∧ ε_g)}`
  have hum : (N : ℝ) ^ (-εg) ≤ (N : ℝ) ^ (-min τe εg) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by have := min_le_right τe εg; linarith)
  -- `N^{2ε_g}/(N q_S ι_S²) ≤ N^{-ε_g}`
  have hv : (N : ℝ) ^ (2 * εg) / (N * (flowTc (lam D N A) z - S) *
      (Real.exp (S / 2) * (mExt (lam D N A) z).im) ^ 2) ≤ (N : ℝ) ^ (-min τe εg) := by
    refine le_trans ?_ hum
    rw [← hιS]
    have hadmS : (N : ℝ) ^ (C₀ * εg) ≤
        N * (charFlowZ (lam D N A) z S).im * flowIm (lam D N A) z S := hadm.2.2.2.2.2.2.2.2
    have hιSpos : 0 < flowIm (lam D N A) z S := by rw [hιS]; positivity
    have hden : (N : ℝ) ^ (C₀ * εg) / 2 ≤ N * (flowTc (lam D N A) z - S) *
        flowIm (lam D N A) z S ^ 2 := by
      have := mul_le_mul_of_nonneg_left hηle (by positivity : (0 : ℝ) ≤ N * flowIm (lam D N A) z S)
      nlinarith
    have hsplit : (N : ℝ) ^ ((C₀ - 1) * εg) = (N : ℝ) ^ (C₀ * εg) * (N : ℝ) ^ (-εg) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    have hC0 : 0 < (N : ℝ) ^ (C₀ * εg) := by positivity
    rw [div_le_iff₀ (by positivity)]
    calc (N : ℝ) ^ (2 * εg) ≤ (N : ℝ) ^ ((C₀ - 1) * εg) / 2 := by linarith
      _ = (N : ℝ) ^ (-εg) * ((N : ℝ) ^ (C₀ * εg) / 2) := by rw [hsplit]; ring
      _ ≤ (N : ℝ) ^ (-εg) * (N * (flowTc (lam D N A) z - S) * flowIm (lam D N A) z S ^ 2) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
  have hPP : (N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁ = (N : ℝ) ^ (τ₁ + τ₁) := (Real.rpow_add hNpos _ _).symm
  rw [hιS] at h1 ⊢
  exact LF3_ar_p N _ _ _ z.im (Real.exp (S / 2)) _ _ ((N : ℝ) ^ τ₁) _ _ _ ((N : ℝ) ^ τ')
    hNpos hq0.le hqS hι0 hz hqη hE1 hE (Real.one_le_rpow hNr hτ₁0.le) (by positivity) hum
    (by simpa [mul_assoc] using h2) h1 hv (by rw [hPP]; exact hfin)

/-- Lemma 3.11 [lem_flow_3], (3.33) [flow_3_result_2], at one time, for the law of `H_{t₀}` of
(4.1) [defVt], `t₀ ∈ [0, 1]`, `θ = e^{-t₀}`: at the law (3.13) [eq:Gauss_div] at time `S`,
`‖E L_S - K_S‖₂ ≤ N^{τ'} N^{-(τ_e ∧ ε_g)} / (N q_S² (Im m_S)²)`. -/
theorem flowL2_exp_paper (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4)
    (hC₀ : 6 < C₀) (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t₀ : ℝ), 0 ≤ t₀ → t₀ ≤ 1 →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        hsNorm (ELmat (blockOULaw D N (ouMatLaw D N L t₀) S)
              (((Real.exp (-S / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z₁ S)
              (charFlowZ (lam D N A) z₂ S) -
            flowKmat (lam D N A) (Real.exp (-t₀)) z₁ z₂ S) ≤
          (N : ℝ) ^ τ' * ((N : ℝ) ^ (-min τe εg) /
            (N * (flowTc (lam D N A) z - S) ^ 2 * flowIm (lam D N A) z S ^ 2)) := by
  exact LF3_paper D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C

end RBMTransitionEdge

end
