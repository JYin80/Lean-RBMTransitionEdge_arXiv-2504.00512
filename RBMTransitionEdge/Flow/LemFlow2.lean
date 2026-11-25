module

public import RBMTransitionEdge.Flow.LargeEta
public import RBMTransitionEdge.Flow.LemFlow1

@[expose] public section

/-!
# Lemma 3.9 on the grid: the three-resolvent loop along the flow

`L_{(1,2,3),s}` and `K_{θ_s}` along the flow, the drift of the three-resolvent equation in one grid
step on the good event, its martingale part, and (3.28) [flow_3G_res] on one grid in a conditional
form: the bound holds on the event that the initial two-resolvent loops are already close to
`K_θ`; the paper form (3.29) [flow_3G_res_2] is a separate statement.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `L_{(1,2,3),s}` along the flow at the state `H`. -/
def flowLten3 {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ) (s : ℝ)
    (H : Idx D N → Idx D N → ℂ) : Fin D → Fin D → Fin D → ℂ :=
  Lten3 (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) H (charFlowZ Λ z₁ s) (charFlowZ Λ z₂ s)
    (charFlowZ Λ z₃ s)

/-- `K_{θ_s}(z_{1,s}, z_{2,s}, z_{3,s})` along the flow, `θ_s = e^{-s} θ + 1 - e^{-s}`. -/
def flowKten3 {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ z₃ : ℂ) (s : ℝ) :
    Fin D → Fin D → Fin D → ℂ :=
  KTheta3 (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (Real.exp (-s) * θ + 1 - Real.exp (-s))
    (charFlowZ Λ z₁ s) (charFlowZ Λ z₂ s) (charFlowZ Λ z₃ s)

/-! ### Operator-norm tools -/

section LF2_Op

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `opNorm` is the `L²` operator norm. -/
private lemma LF2_op_eq (A : Matrix ι ι ℂ) : opNorm A = ‖A‖ := rfl

/-- `‖AB‖ ≤ ‖A‖ ‖B‖`. -/
private lemma LF2_op_mul (A B : Matrix ι ι ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  simpa only [LF2_op_eq] using norm_mul_le A B

/-- `‖A‖ ≥ 0`. -/
private lemma LF2_op_nonneg (A : Matrix ι ι ℂ) : 0 ≤ opNorm A := norm_nonneg _

/-- `‖A^*‖ = ‖A‖`. -/
private lemma LF2_op_conj (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  simpa only [LF2_op_eq] using Matrix.l2_opNorm_conjTranspose A

/-- An entry is bounded by the operator norm. -/
private lemma LF2_entry_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ opNorm A := by
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
private lemma LF2_ntr_le [Nonempty ι] (A : Matrix ι ι ℂ) : ‖ntr A‖ ≤ opNorm A := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, opNorm A := Finset.sum_le_sum fun i _ => LF2_entry_le A i i
    _ = _ := by simp

/-- `⟨A^*⟩ = conj ⟨A⟩`. -/
private lemma LF2_ntr_conj (A : Matrix ι ι ℂ) : ntr Aᴴ = star (ntr A) := by
  simp [ntr, Matrix.trace_conjTranspose, star_mul']

/-- `⟨AB⟩ = ⟨BA⟩`. -/
private lemma LF2_ntr_comm (A B : Matrix ι ι ℂ) : ntr (A * B) = ntr (B * A) := by
  simp only [ntr, Matrix.trace_mul_comm A B]

end LF2_Op

/-- `‖E_a‖ ≤ 1` for the block projection. -/
private lemma LF2_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- `E_a^* = E_a`. -/
private lemma LF2_Ea_conj (D N : ℕ) (a : Fin D) : (Ea D N a)ᴴ = Ea D N a := by
  unfold Ea
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  simp only [Pi.star_apply]
  split_ifs <;> simp

/-- The Hermitian part of a Hermitian array is the array. -/
private lemma LF2_hermPart_eq {ι : Type*} (H : ι → ι → ℂ) (hH : (Matrix.of H).IsHermitian) :
    hermPart H = H := by
  funext i j
  have h1 : star (H j i) = H i j := by
    have := congrFun (congrFun hH i) j
    simpa [Matrix.conjTranspose_apply] using this
  simp only [hermPart, h1]
  ring

/-- `t Λ(A) = Λ(t A)` for real `t`. -/
private lemma LF2_lam_smul (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    (t : ℂ) • lam D N A = lam D N ((t : ℂ) • A) := by
  ext p q
  simp only [lam, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [mul_add, Complex.conj_ofReal]

/-- A real multiple of a Hermitian matrix is Hermitian. -/
private lemma LF2_herm_smul {ι : Type*} (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (c : ℝ) :
    (((c : ℝ) : ℂ) • Λ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hΛ.eq]
  simp

/-! ### The closed-form flow on `[0, S]` -/

/-- Along the closed-form flow (3.10) [eq:deterflow] on `[0, S]`, `S < t_c - t₀`, `‖Λ‖ ≤ 1/10`:
`η_s > 0`, `Im m_s = e^{s/2} Im m ∈ (0, 1)`, `η_s Im m_s` is at least its value at `S`,
`t_c - t_s = (t_c - t₀) - s` and `η_s ≥ (t_c - t_s) Im m_s`. -/
private lemma LF2_flow (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
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
  have hapr := mSol_apriori _ (LF2_herm_smul Λ hΛ (Real.exp (-s / 2))) hnorm _ hpos
  have hms : ‖((Real.exp (s / 2) : ℝ) : ℂ) * m‖ < 1 := by
    have h1 : mExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s) =
        mSol (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s) := by simp [mExt, hpos]
    rw [← (hflow s hsS).2, h1]
    exact hapr.2.1
  have hms' : Real.exp (s / 2) * ‖m‖ < 1 := by
    rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hms
  have htc := flowTc_flow Λ hΛ z hz s hs
  refine ⟨hpos, hflowIm s hsS, hι, ?_, ?_, htc, ?_⟩
  · rw [hflowIm s hsS]
    have : m.im ≤ ‖m‖ := (Complex.im_le_norm m)
    have h5 : 1 ≤ Real.exp (s / 2) := Real.one_le_exp (by linarith)
    nlinarith [Real.exp_pos (s / 2), norm_nonneg m]
  · rw [hprod S le_rfl, hprod s hsS]
    have : Real.exp (s / 2) ^ 2 ≤ Real.exp (S / 2) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.2 (by linarith)) 2
    nlinarith [sq_nonneg m.im]
  · -- `η_s / Im m_s = e^{q_s} - 1 ≥ q_s`
    have hteta := charFlow_teta Λ hΛ z hz s hs
    have hιs : 0 < flowIm Λ z s := by rw [hflowIm s hsS]; exact mul_pos (Real.exp_pos _) hι
    have e1 : (charFlowZ Λ z s).im / flowIm Λ z s =
        Real.exp (flowTc Λ z - s) - 1 := hteta
    have h2 : flowTc Λ z - s ≤ Real.exp (flowTc Λ z - s) - 1 := by
      linarith [Real.add_one_le_exp (flowTc Λ z - s)]
    rw [← e1, le_div_iff₀ hιs] at h2
    exact h2

/-- The admissible start of `flowAdm` for large `N`: `‖Λ‖ ≤ 1/10`, `|z| ≤ τ⁻¹`, `|m| < 1`,
`0 < t_c - t₀ ≤ 1`, and `η_s > N⁻¹` on `[0, S]`. -/
private lemma LF2_adm (D N : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ N) (δA τ τe εg c C₀ : ℝ) (hεg : 0 < εg)
    (hC₀ : 0 < C₀) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ)
    (hadm : flowAdm D N δA τ τe εg c C₀ A z S)
    (hAN : 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10) (hcN : c * (N : ℝ) ^ (-εg) ≤ 1) :
    opNorm (lam D N A) ≤ 1 / 10 ∧ ‖z‖ ≤ τ⁻¹ ∧ 0 < z.im ∧ ‖mExt (lam D N A) z‖ < 1 ∧
      0 < flowTc (lam D N A) z ∧ flowTc (lam D N A) z ≤ 1 ∧ 0 ≤ S ∧
      S < flowTc (lam D N A) z ∧
      ∀ s, 0 ≤ s → s ≤ S → (N : ℝ)⁻¹ < (charFlowZ (lam D N A) z s).im ∧
        (N : ℝ) ^ (C₀ * εg) ≤ N * (charFlowZ (lam D N A) z s).im * flowIm (lam D N A) z s := by
  obtain ⟨hA, hzD, hz, -, hlo, hhi, hS0, hSt, hNS⟩ := hadm
  have hNe : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, by omega⟩)⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hΛ : opNorm (lam D N A) ≤ 1 / 10 := by
    have := opNorm_lam_le D N A
    linarith
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
  obtain ⟨hηs, -, -, hιs1, hmono, -, -⟩ :=
    LF2_flow D N hD (by omega) A hΛ z hz S hSt s hs0 hsS
  obtain ⟨-, hιeq, hι0, -, -, -, -⟩ := LF2_flow D N hD (by omega) A hΛ z hz S hSt s hs0 hsS
  have hιspos : 0 < flowIm (lam D N A) z s := by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
  have hNe1 : (1 : ℝ) ≤ (N : ℝ) ^ (C₀ * εg) := Real.one_le_rpow hN1 (by positivity)
  have hbig : (N : ℝ) ^ (C₀ * εg) ≤
      N * (charFlowZ (lam D N A) z s).im * flowIm (lam D N A) z s := by
    have := mul_le_mul_of_nonneg_left hmono hNpos.le
    calc (N : ℝ) ^ (C₀ * εg) ≤ N * (charFlowZ (lam D N A) z S).im * flowIm (lam D N A) z S :=
          hNS
      _ ≤ _ := by nlinarith
  refine ⟨?_, hbig⟩
  rw [inv_lt_iff_one_lt_mul₀ hNpos]
  have : (N : ℝ) * (charFlowZ (lam D N A) z s).im * flowIm (lam D N A) z s <
      N * (charFlowZ (lam D N A) z s).im := by
    have h1 : 0 < (N : ℝ) * (charFlowZ (lam D N A) z s).im := mul_pos hNpos hηs
    nlinarith
  linarith

/-- `𝓛(cF) = c 𝓛F` for real `c` and `C²` functions `F`. -/
private lemma LF2_genA_smul {D N : ℕ} (F : (Idx D N → Idx D N → ℂ) → ℂ) (hF : ContDiff ℝ 2 F)
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
private abbrev LF2_pw {ι : Type*} (G : Matrix ι ι ℂ) (b : Bool) : Matrix ι ι ℂ :=
  if b then Gᴴ else G

/-- `‖G^b‖ = ‖G‖`. -/
private lemma LF2_op_pw {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (b : Bool) :
    opNorm (LF2_pw G b) = opNorm G := by
  cases b
  · rfl
  · exact LF2_op_conj G

/-- At the flowed points `z_{i,s} ∈ {z_s, z̄_s}`: `G(z_{i,s}) = G(z_s)^b` and
`M(z_{i,s}) = M(z_s)^b` for one flag `b`. -/
private lemma LF2_flag {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian) (zi : ℂ)
    (hi : zi = z ∨ zi = star z) :
    ∃ b : Bool,
      res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) zi s) =
        LF2_pw (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) b ∧
      MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) zi s) =
        LF2_pw (MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) b := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  rcases hi with rfl | rfl
  · exact ⟨false, rfl, rfl⟩
  · refine ⟨true, ?_, ?_⟩
    · have hΛ := lam_isHermitian D N A
      have hX : (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A).IsHermitian :=
        hH.add (LF2_herm_smul _ hΛ _)
      have hw := (charFlow_M (lam D N A) hΛ z hz s hs).1
      rw [charFlowZ_conj _ z hz s, Complex.star_def, res_conj _ hX _ hw]
      rfl
    · have hΛ := lam_isHermitian D N A
      have hw := (charFlow_M (lam D N A) hΛ z hz s hs).1
      rw [charFlowZ_conj _ z hz s, (mExt_conj _ (LF2_herm_smul _ hΛ _) _ hw.ne').2]
      rfl

/-- `|⟨(G^b - M^b) E⟩| = |⟨(G - M) E⟩|` for a Hermitian `E`. -/
private lemma LF2_ntr_pw_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (G M E : Matrix ι ι ℂ)
    (hE : Eᴴ = E) (b : Bool) :
    ‖ntr ((LF2_pw G b - LF2_pw M b) * E)‖ = ‖ntr ((G - M) * E)‖ := by
  cases b
  · rfl
  · change ‖ntr ((Gᴴ - Mᴴ) * E)‖ = _
    have e : (Gᴴ - Mᴴ) * E = (E * (G - M))ᴴ := by
      rw [Matrix.conjTranspose_mul, hE, Matrix.conjTranspose_sub]
    rw [e, LF2_ntr_conj, norm_star, LF2_ntr_comm]

/-- The three-resolvent word as `resProd`. -/
private lemma LF2_word3 {ι : Type*} [Fintype ι] [DecidableEq ι] (G E₁ E₂ E₃ : Matrix ι ι ℂ)
    (b₁ b₂ b₃ : Bool) :
    LF2_pw G b₁ * E₁ * LF2_pw G b₂ * E₂ * LF2_pw G b₃ * E₃ =
      resProd (fun _ : Fin 3 => G) ![b₁, b₂, b₃] ![E₁, E₂, E₃] := by
  simp only [resProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.mul_one, Matrix.mul_assoc, LF2_pw]
  rfl

/-- The size `bndA4` of (A.53) [entprodG] for `p` equal resolvents: `Im m / η^{p-1}`, `p ≥ 2`. -/
private lemma LF2_bndA4 (p : ℕ) (hp : 2 ≤ p) (ι η : ℝ) :
    bndA4 (fun _ : Fin p => ι) (fun _ : Fin p => η) p = ι / η ^ (p - 1) := by
  have : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  simp [bndA4, hp]

/-- `|L_{ab}| ≤ D / η_s²` along the flow. -/
private lemma LF2_L_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (a b : Fin D) :
    ‖flowLmat (lam D N A) z₁ z₂ s H a b‖ ≤ D / (charFlowZ (lam D N A) z s).im ^ 2 := by
  have hNe : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  obtain ⟨b₁, hG₁, -⟩ := LF2_flag hD hN A z hz s hs H hH z₁ h₁
  obtain ⟨b₂, hG₂, -⟩ := LF2_flag hD hN A z hz s hs H hH z₂ h₂
  have hΛ := lam_isHermitian D N A
  have hX : (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A).IsHermitian :=
    hH.add (LF2_herm_smul _ hΛ _)
  have hη := (charFlow_M _ hΛ z hz s hs).1
  have hGn := opNorm_res_le _ hX _ hη
  set G := res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
    (charFlowZ (lam D N A) z s)
  simp only [flowLmat, Lmat]
  rw [hG₁, hG₂, norm_mul, Complex.norm_natCast, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (LF2_ntr_le _).trans ?_
  have e1 := LF2_opNorm_Ea D N a
  have e2 := LF2_opNorm_Ea D N b
  have g1 : opNorm (LF2_pw G b₁) ≤ (charFlowZ (lam D N A) z s).im⁻¹ := by
    rw [LF2_op_pw]; exact hGn
  have g2 : opNorm (LF2_pw G b₂) ≤ (charFlowZ (lam D N A) z s).im⁻¹ := by
    rw [LF2_op_pw]; exact hGn
  have p1 := LF2_op_nonneg (LF2_pw G b₁)
  have p2 := LF2_op_nonneg (LF2_pw G b₂)
  have p3 := LF2_op_nonneg (Ea D N a)
  have p4 := LF2_op_nonneg (Ea D N b)
  have hinv : 0 ≤ (charFlowZ (lam D N A) z s).im⁻¹ := inv_nonneg.2 hη.le
  calc opNorm (LF2_pw G b₁ * Ea D N a * LF2_pw G b₂ * Ea D N b)
      ≤ opNorm (LF2_pw G b₁) * opNorm (Ea D N a) * opNorm (LF2_pw G b₂) * opNorm (Ea D N b) := by
        refine (LF2_op_mul _ _).trans ?_
        refine mul_le_mul_of_nonneg_right ((LF2_op_mul _ _).trans ?_) p4
        exact mul_le_mul_of_nonneg_right (LF2_op_mul _ _) p2
    _ ≤ (charFlowZ (lam D N A) z s).im⁻¹ * 1 * (charFlowZ (lam D N A) z s).im⁻¹ * 1 := by
        gcongr
    _ = ((charFlowZ (lam D N A) z s).im ^ 2)⁻¹ := by ring

/-- The block-diagonal GUE array is Hermitian. -/
private lemma LF2_blockH_herm (D N : ℕ) (w : Fin D → Coords N) : (blockH D N w).IsHermitian := by
  have h := HLam_isHermitian D N 0 w
  have e : lam D N (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
    funext p q; simp [lam]
  simpa [HLam, e] using h

/-- A real combination `a H + b X` of a Hermitian array and a block GUE array is Hermitian. -/
private lemma LF2_state_herm {D N : ℕ} (a b : ℝ) (H : Idx D N → Idx D N → ℂ)
    (hH : (Matrix.of H).IsHermitian) (X : Fin D → Coords N) :
    (Matrix.of (a • H + b • Matrix.of.symm (blockH D N X))).IsHermitian := by
  have e : Matrix.of (a • H + b • Matrix.of.symm (blockH D N X)) =
      ((a : ℝ) : ℂ) • Matrix.of H + ((b : ℝ) : ℂ) • blockH D N X := by
    ext i j
    simp [Complex.real_smul]
  rw [e]
  exact (LF2_herm_smul _ hH a).add (LF2_herm_smul _ (LF2_blockH_herm D N X) b)

/-- `N^{3τ} = (N^τ)³`. -/
private lemma LF2_rpow3 (x τ : ℝ) (hx : 0 ≤ x) : x ^ (3 * τ) = (x ^ τ) ^ 3 := by
  rw [mul_comm, Real.rpow_mul hx, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `η_s ≤ e (t_c - t₀ - s) Im m_s` along the flow on `[0, S]`, `t_c - t₀ ≤ 1`. -/
private lemma LF2_flow_up (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (hq1 : flowTc (lam D N A) z ≤ 1) (s : ℝ) (hs0 : 0 ≤ s)
    (hsS : s ≤ S) :
    (charFlowZ (lam D N A) z s).im ≤
      Real.exp 1 * (flowTc (lam D N A) z - s) * flowIm (lam D N A) z s := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hs : s < flowTc (lam D N A) z := lt_of_le_of_lt hsS hS
  obtain ⟨-, hιeq, hι0, -, -, -, -⟩ := LF2_flow D N hD hN A hA z hz S hS s hs0 hsS
  have hιs : 0 < flowIm (lam D N A) z s := by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
  have hteta := charFlow_teta (lam D N A) hΛ z hz s hs
  have e1 : (charFlowZ (lam D N A) z s).im / flowIm (lam D N A) z s =
      Real.exp (flowTc (lam D N A) z - s) - 1 := hteta
  set x := flowTc (lam D N A) z - s with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have hx1 : x ≤ 1 := by rw [hx]; linarith
  have h1 : Real.exp x - 1 ≤ Real.exp 1 * x := by
    have h2 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
    have h3 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have h4 : Real.exp x - 1 ≤ x * Real.exp x := by nlinarith [Real.exp_pos x]
    have h5 : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.2 hx1
    nlinarith
  rw [← e1, div_le_iff₀ hιs] at h1
  linarith

/-! ### The three-resolvent loop as a loop along the flow -/

/-- The loop list `[(E_w, z₁), (E_x, z₂), (E_y, z₃)]`, whose loop is
`⟨E_w G₁ E_x G₂ E_y G₃⟩ = D⁻¹ L_{xyw}`. -/
private abbrev LF2_l {D N : ℕ} (z₁ z₂ z₃ : ℂ) (x y w : Fin D) :
    List (Matrix (Idx D N) (Idx D N) ℂ × ℂ) :=
  [(Ea D N w, z₁), (Ea D N x, z₂), (Ea D N y, z₃)]

/-- `⟨A B C E F G⟩ = ⟨G A (B C (E F))⟩`. -/
private lemma LF2_ntr6 {ι : Type*} [Fintype ι] (A B C E F G : Matrix ι ι ℂ) :
    ntr (A * B * C * E * F * G) = ntr (G * A * (B * (C * (E * F)))) := by
  rw [LF2_ntr_comm]
  simp only [Matrix.mul_assoc]

/-- `L_{xyw}` at the Hermitian part of an array is `D` times the loop of `LF2_l`. -/
private lemma LF2_Lten_loop {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ)
    (x y w : Fin D) (r : ℝ) (h : Idx D N → Idx D N → ℂ) :
    flowLten3 Λ z₁ z₂ z₃ r (hermPart h) x y w =
      (D : ℂ) * flowLoop Λ (LF2_l z₁ z₂ z₃ x y w) r h := by
  simp only [flowLten3, Lten3, flowLoop, chainB, LF2_l, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Matrix.mul_one]
  rw [LF2_ntr6]
  simp only [Matrix.mul_assoc]

/-- `L_{xyw}` at a Hermitian array is `D` times the loop of `LF2_l`. -/
private lemma LF2_Lten_loop' {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ)
    (x y w : Fin D) (r : ℝ) (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian) :
    flowLten3 Λ z₁ z₂ z₃ r H x y w = (D : ℂ) * flowLoop Λ (LF2_l z₁ z₂ z₃ x y w) r H := by
  have := LF2_Lten_loop Λ z₁ z₂ z₃ x y w r H
  rwa [LF2_hermPart_eq H hH] at this

/-- The four-resolvent word as `resProd`. -/
private lemma LF2_word4 {ι : Type*} [Fintype ι] [DecidableEq ι] (G E₁ E₂ E₃ E₄ : Matrix ι ι ℂ)
    (b₁ b₂ b₃ b₄ : Bool) :
    LF2_pw G b₁ * E₁ * LF2_pw G b₂ * E₂ * LF2_pw G b₃ * E₃ * LF2_pw G b₄ * E₄ =
      resProd (fun _ : Fin 4 => G) ![b₁, b₂, b₃, b₄] ![E₁, E₂, E₃, E₄] := by
  simp only [resProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.mul_one, Matrix.mul_assoc, LF2_pw]
  rfl

/-- The fluctuation term of the three-resolvent equation (`gen_loop3`):
`D Σ_a Σ_i ⟨(G_i - M_i) E_a⟩ ℒ^{(i)}_{xywa}`. -/
private def LF2_err {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ) (s : ℝ)
    (H : Idx D N → Idx D N → ℂ) (x y w : Fin D) : ℂ :=
  let Λs : Matrix (Idx D N) (Idx D N) ℂ := ((Real.exp (-s / 2) : ℝ) : ℂ) • Λ
  let G₁ := res (Matrix.of H + Λs) (charFlowZ Λ z₁ s)
  let G₂ := res (Matrix.of H + Λs) (charFlowZ Λ z₂ s)
  let G₃ := res (Matrix.of H + Λs) (charFlowZ Λ z₃ s)
  (D : ℂ) * (∑ a, (ntr ((G₁ - MExt Λs (charFlowZ Λ z₁ s)) * Ea D N a) * ((D : ℂ) *
      ntr (G₁ * Ea D N a * G₁ * Ea D N x * G₂ * Ea D N y * G₃ * Ea D N w)) +
    ntr ((G₂ - MExt Λs (charFlowZ Λ z₂ s)) * Ea D N a) * ((D : ℂ) *
      ntr (G₁ * Ea D N x * G₂ * Ea D N a * G₂ * Ea D N y * G₃ * Ea D N w)) +
    ntr ((G₃ - MExt Λs (charFlowZ Λ z₃ s)) * Ea D N a) * ((D : ℂ) *
      ntr (G₁ * Ea D N x * G₂ * Ea D N y * G₃ * Ea D N a * G₃ * Ea D N w))))

/-- The fluctuation term for abstract `G`, `M` and Hermitian `E_a`, from bounds `β₁` on
`|⟨(G^b - M^b) E_a⟩|` and `β₂` on the four-resolvent words. -/
private lemma LF2_err_abs {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ℕ) (hD : 1 ≤ D)
    (G M : Matrix ι ι ℂ) (E : Fin D → Matrix ι ι ℂ) (b₁ b₂ b₃ : Bool) (β₁ β₂ : ℝ)
    (hfl : ∀ (b : Bool) (a : Fin D), ‖ntr ((LF2_pw G b - LF2_pw M b) * E a)‖ ≤ β₁)
    (hw : ∀ (c₁ c₂ c₃ c₄ : Bool) (a₁ a₂ a₃ a₄ : Fin D),
      ‖(D : ℂ) * ntr (LF2_pw G c₁ * E a₁ * LF2_pw G c₂ * E a₂ * LF2_pw G c₃ * E a₃ *
        LF2_pw G c₄ * E a₄)‖ ≤ β₂)
    (x y w : Fin D) :
    ‖(D : ℂ) * (∑ a, (ntr ((LF2_pw G b₁ - LF2_pw M b₁) * E a) * ((D : ℂ) *
        ntr (LF2_pw G b₁ * E a * LF2_pw G b₁ * E x * LF2_pw G b₂ * E y * LF2_pw G b₃ * E w)) +
      ntr ((LF2_pw G b₂ - LF2_pw M b₂) * E a) * ((D : ℂ) *
        ntr (LF2_pw G b₁ * E x * LF2_pw G b₂ * E a * LF2_pw G b₂ * E y * LF2_pw G b₃ * E w)) +
      ntr ((LF2_pw G b₃ - LF2_pw M b₃) * E a) * ((D : ℂ) *
        ntr (LF2_pw G b₁ * E x * LF2_pw G b₂ * E y * LF2_pw G b₃ * E a * LF2_pw G b₃ * E w))))‖ ≤
      D * (D * (3 * (β₁ * β₂))) := by
  have hβ₁0 : 0 ≤ β₁ := (norm_nonneg _).trans (hfl false ⟨0, hD⟩)
  have hterm : ∀ a : Fin D,
      ‖ntr ((LF2_pw G b₁ - LF2_pw M b₁) * E a) * ((D : ℂ) *
        ntr (LF2_pw G b₁ * E a * LF2_pw G b₁ * E x * LF2_pw G b₂ * E y * LF2_pw G b₃ * E w)) +
      ntr ((LF2_pw G b₂ - LF2_pw M b₂) * E a) * ((D : ℂ) *
        ntr (LF2_pw G b₁ * E x * LF2_pw G b₂ * E a * LF2_pw G b₂ * E y * LF2_pw G b₃ * E w)) +
      ntr ((LF2_pw G b₃ - LF2_pw M b₃) * E a) * ((D : ℂ) *
        ntr (LF2_pw G b₁ * E x * LF2_pw G b₂ * E y * LF2_pw G b₃ * E a * LF2_pw G b₃ * E w))‖ ≤
        3 * (β₁ * β₂) := by
    intro a
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_mul, norm_mul (ntr ((LF2_pw G b₂ - LF2_pw M b₂) * E a)),
      norm_mul (ntr ((LF2_pw G b₃ - LF2_pw M b₃) * E a))]
    have t1 := mul_le_mul (hfl b₁ a) (hw b₁ b₁ b₂ b₃ a x y w) (norm_nonneg _) hβ₁0
    have t2 := mul_le_mul (hfl b₂ a) (hw b₁ b₂ b₂ b₃ x a y w) (norm_nonneg _) hβ₁0
    have t3 := mul_le_mul (hfl b₃ a) (hw b₁ b₂ b₃ b₃ x y a w) (norm_nonneg _) hβ₁0
    linarith
  rw [norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => hterm a).trans ?_
  simp

/-- On the good event: `|⟨(G_i - M_i) E_a⟩| ≤ N^{τ'}/(N η_s)` (2.23) [eq:aver_local] and the
four-resolvent words are at most `D N^{τ'} Im m_s / η_s³` (A.53) [entprodG], so the fluctuation
term is at most `3 D³ N^{2τ'} Im m_s / (N η_s⁴)`. -/
private lemma LF2_err_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z) (τ' : ℝ)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian)
    (hgood : flowGoodAt A z τ' s H) (z₁ z₂ z₃ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (h₃ : z₃ = z ∨ z₃ = star z) (x y w : Fin D) :
    ‖LF2_err (lam D N A) z₁ z₂ z₃ s H x y w‖ ≤
      3 * D ^ 3 * ((N : ℝ) ^ τ') ^ 2 * flowIm (lam D N A) z s /
        (N * (charFlowZ (lam D N A) z s).im ^ 4) := by
  have hNe : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  obtain ⟨b₁, hG₁, hM₁⟩ := LF2_flag hD hN A z hz s hs H hH z₁ h₁
  obtain ⟨b₂, hG₂, hM₂⟩ := LF2_flag hD hN A z hz s hs H hH z₂ h₂
  obtain ⟨b₃, hG₃, hM₃⟩ := LF2_flag hD hN A z hz s hs H hH z₃ h₃
  have hηpos : 0 < (charFlowZ (lam D N A) z s).im :=
    (charFlow_M _ (lam_isHermitian D N A) z hz s hs).1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hfl : ∀ (b : Bool) (a : Fin D),
      ‖ntr ((LF2_pw (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) b -
        LF2_pw (MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) b) * Ea D N a)‖ ≤
        (N : ℝ) ^ τ' / (N * (charFlowZ (lam D N A) z s).im) := fun b a => by
    rw [LF2_ntr_pw_sub _ _ _ (LF2_Ea_conj D N a)]
    exact hgood.1 a
  have hw : ∀ (c₁ c₂ c₃ c₄ : Bool) (a₁ a₂ a₃ a₄ : Fin D),
      ‖(D : ℂ) * ntr (LF2_pw (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) c₁ * Ea D N a₁ *
        LF2_pw (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) c₂ * Ea D N a₂ *
        LF2_pw (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) c₃ * Ea D N a₃ *
        LF2_pw (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) c₄ * Ea D N a₄)‖ ≤
        (D : ℝ) * ((N : ℝ) ^ τ' * (flowIm (lam D N A) z s /
          (charFlowZ (lam D N A) z s).im ^ 3)) := by
    intro c₁ c₂ c₃ c₄ a₁ a₂ a₃ a₄
    rw [norm_mul, Complex.norm_natCast, LF2_word4]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h4 := hgood.2.1 4 (by norm_num) (by norm_num) ![c₁, c₂, c₃, c₄] ![a₁, a₂, a₃, a₄]
    rw [LF2_bndA4 4 (by norm_num)] at h4
    have e : (fun i : Fin 4 => Ea D N (![a₁, a₂, a₃, a₄] i)) =
        ![Ea D N a₁, Ea D N a₂, Ea D N a₃, Ea D N a₄] := by
      funext i; fin_cases i <;> rfl
    rw [e] at h4
    exact h4
  have key := LF2_err_abs D hD _ _ (Ea D N) b₁ b₂ b₃ _ _ hfl hw x y w
  unfold LF2_err
  simp only
  rw [hG₁, hG₂, hG₃, hM₁, hM₂, hM₃]
  refine key.trans (le_of_eq ?_)
  field_simp

/-- `|L_{(1,2,3),xyw}| ≤ D / η_s³` along the flow. -/
private lemma LF2_Lten_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian) (z₁ z₂ z₃ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (h₃ : z₃ = z ∨ z₃ = star z)
    (a b c : Fin D) :
    ‖flowLten3 (lam D N A) z₁ z₂ z₃ s H a b c‖ ≤ D / (charFlowZ (lam D N A) z s).im ^ 3 := by
  have hNe : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  obtain ⟨b₁, hG₁, -⟩ := LF2_flag hD hN A z hz s hs H hH z₁ h₁
  obtain ⟨b₂, hG₂, -⟩ := LF2_flag hD hN A z hz s hs H hH z₂ h₂
  obtain ⟨b₃, hG₃, -⟩ := LF2_flag hD hN A z hz s hs H hH z₃ h₃
  have hΛ := lam_isHermitian D N A
  have hX : (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A).IsHermitian :=
    hH.add (LF2_herm_smul _ hΛ _)
  have hη := (charFlow_M _ hΛ z hz s hs).1
  have hGn := opNorm_res_le _ hX _ hη
  set G := res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
    (charFlowZ (lam D N A) z s)
  simp only [flowLten3, Lten3]
  rw [hG₁, hG₂, hG₃, norm_mul, Complex.norm_natCast, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (LF2_ntr_le _).trans ?_
  have e1 := LF2_opNorm_Ea D N a
  have e2 := LF2_opNorm_Ea D N b
  have e3 := LF2_opNorm_Ea D N c
  have g : ∀ bb : Bool, opNorm (LF2_pw G bb) ≤ (charFlowZ (lam D N A) z s).im⁻¹ := fun bb => by
    rw [LF2_op_pw]; exact hGn
  have p : ∀ bb : Bool, 0 ≤ opNorm (LF2_pw G bb) := fun bb => LF2_op_nonneg _
  have pa := LF2_op_nonneg (Ea D N a)
  have pb := LF2_op_nonneg (Ea D N b)
  have pc := LF2_op_nonneg (Ea D N c)
  have hinv : 0 ≤ (charFlowZ (lam D N A) z s).im⁻¹ := inv_nonneg.2 hη.le
  calc opNorm (LF2_pw G b₁ * Ea D N a * LF2_pw G b₂ * Ea D N b * LF2_pw G b₃ * Ea D N c)
      ≤ opNorm (LF2_pw G b₁) * opNorm (Ea D N a) * opNorm (LF2_pw G b₂) * opNorm (Ea D N b) *
          opNorm (LF2_pw G b₃) * opNorm (Ea D N c) := by
        refine (LF2_op_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ pc)
        refine (LF2_op_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ (p b₃))
        refine (LF2_op_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ pb)
        refine (LF2_op_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ (p b₂))
        exact LF2_op_mul _ _
    _ ≤ (charFlowZ (lam D N A) z s).im⁻¹ * 1 * (charFlowZ (lam D N A) z s).im⁻¹ * 1 *
          (charFlowZ (lam D N A) z s).im⁻¹ * 1 := by
        exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (g b₁) e1 pa hinv)
          (g b₂) (p b₂) (by positivity)) e2 pb (by positivity)) (g b₃) (p b₃) (by positivity)) e3 pc
          (by positivity)
    _ = ((charFlowZ (lam D N A) z s).im ^ 3)⁻¹ := by ring

/-! ### Real inequalities behind the drift bound -/

/-- The size `B` of the derivatives of a three-loop: `c (DN + 1)⁴ e^{q} K² ‖E‖³ (η_S ∧ 1)^{-9}
≤ |c| (2D)⁴ N⁴ e (4 + τ⁻¹)² N⁹` when `q ≤ 1`, `K ≤ 4 + τ⁻¹`, `‖E‖³ ≤ 1`, `η_S ∧ 1 ≥ N⁻¹`. -/
private lemma LF2_ar_B (c D N e K P m τ : ℝ) (hD : 1 ≤ D) (hN : 2 ≤ N) (he : e ≤ Real.exp 1)
    (he0 : 0 ≤ e) (hK0 : 0 ≤ K) (hK : K ≤ 4 + τ⁻¹) (hP0 : 0 ≤ P) (hP : P ≤ 1)
    (hm : N⁻¹ ≤ m) :
    c * (D * N + 1) ^ 4 * e * K ^ 2 * P * (m ^ 9)⁻¹ ≤
      |c| * ((2 * D) ^ 4 * N ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2 * N ^ 9 := by
  have hNpos : 0 < N := by linarith
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.2 hNpos) hm
  have h9 : (m ^ 9)⁻¹ ≤ N ^ 9 := by
    rw [inv_le_comm₀ (pow_pos hmpos _) (by positivity), ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hNpos.le) hm _
  have hDN : D * N + 1 ≤ 2 * D * N := by nlinarith
  have hDN4 : (D * N + 1) ^ 4 ≤ (2 * D) ^ 4 * N ^ 4 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hDN 4
  have hc : c ≤ |c| := le_abs_self _
  have hK2 : K ^ 2 ≤ (4 + τ⁻¹) ^ 2 := pow_le_pow_left₀ hK0 hK 2
  have hm0 : 0 ≤ (m ^ 9)⁻¹ := inv_nonneg.2 (pow_nonneg hmpos.le _)
  calc c * (D * N + 1) ^ 4 * e * K ^ 2 * P * (m ^ 9)⁻¹
      ≤ |c| * (D * N + 1) ^ 4 * e * K ^ 2 * P * (m ^ 9)⁻¹ := by gcongr
    _ ≤ |c| * ((2 * D) ^ 4 * N ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2 * 1 * N ^ 9 := by gcongr
    _ = _ := by ring

/-- The remainder of the expansion: `D K B h² (1 + ‖H‖)⁴ (DN + 1)⁴ ≤ C₁ N^{17} h²`. -/
private lemma LF2_ar_R (KG c D N h Hn B R τ : ℝ) (hD : 1 ≤ D) (hN : 2 ≤ N) (hB0 : 0 ≤ B)
    (hB : B ≤ |c| * ((2 * D) ^ 4 * N ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2 * N ^ 9)
    (hHn0 : 0 ≤ Hn) (hHn : Hn ≤ 1)
    (hR : R ≤ KG * B * h ^ 2 * (1 + Hn) ^ 4 * (D * N + 1) ^ 4) :
    D * R ≤ (D * |KG| * |c| * Real.exp 1 * (4 + τ⁻¹) ^ 2 * 16 * (2 * D) ^ 8) * N ^ 17 * h ^ 2 := by
  have hDN : D * N + 1 ≤ 2 * D * N := by nlinarith
  have hDN4 : (D * N + 1) ^ 4 ≤ (2 * D) ^ 4 * N ^ 4 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hDN 4
  have hH4 : (1 + Hn) ^ 4 ≤ 16 := by
    have : (1 + Hn) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    norm_num at this ⊢; linarith
  have hKG : KG ≤ |KG| := le_abs_self _
  have h1 : R ≤ |KG| * (|c| * ((2 * D) ^ 4 * N ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2 * N ^ 9) *
      h ^ 2 * 16 * ((2 * D) ^ 4 * N ^ 4) := by
    refine hR.trans ?_
    calc KG * B * h ^ 2 * (1 + Hn) ^ 4 * (D * N + 1) ^ 4
        ≤ |KG| * B * h ^ 2 * (1 + Hn) ^ 4 * (D * N + 1) ^ 4 := by gcongr
      _ ≤ _ := by gcongr
  calc D * R ≤ D * (|KG| * (|c| * ((2 * D) ^ 4 * N ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2 * N ^ 9) *
      h ^ 2 * 16 * ((2 * D) ^ 4 * N ^ 4)) := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = _ := by ring

/-- `x^{3/2} = x √x` and `x^{1/2} = √x` for `x ≥ 0`. -/
private lemma LF2_rpow32 (x : ℝ) (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x ∧ x ^ (1 / 2 : ℝ) = Real.sqrt x := by
  refine ⟨?_, (Real.sqrt_eq_rpow x).symm⟩
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- For `b ≤ a ≤ 1`, `a > 0`, `h = a² - b²`: `0 ≤ a³ - b³ ≤ (3/2) h`, and
`b³ - a³ + (3/2) h a = (a - b)² (a + 2b)/2` lies in `[0, h²/a²]`. -/
private lemma LF2_ar_ab (a b h : ℝ) (ha0 : 0 < a) (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1)
    (hh : h = a ^ 2 - b ^ 2) :
    0 ≤ a ^ 2 * a - b ^ 2 * b ∧ a ^ 2 * a - b ^ 2 * b ≤ 3 / 2 * h ∧
      0 ≤ b ^ 2 * b - a ^ 2 * a + 3 / 2 * h * a ∧
      a ^ 2 * (b ^ 2 * b - a ^ 2 * a + 3 / 2 * h * a) ≤ h ^ 2 := by
  subst hh
  have hc : b ^ 2 * b - a ^ 2 * a + 3 / 2 * (a ^ 2 - b ^ 2) * a =
      (1 / 2) * (a - b) ^ 2 * (a + 2 * b) := by ring
  have hc0 : 0 ≤ (1 / 2) * (a - b) ^ 2 * (a + 2 * b) := by positivity
  have hab : 0 ≤ a - b := by linarith
  refine ⟨?_, ?_, by rw [hc]; exact hc0, ?_⟩
  · have : 0 ≤ (a - b) * (a ^ 2 + a * b + b ^ 2) := mul_nonneg hab (by positivity)
    nlinarith
  · have e : a ^ 2 * a - b ^ 2 * b = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
    have e2 : 3 / 2 * (a ^ 2 - b ^ 2) = (a - b) * (3 / 2 * (a + b)) := by ring
    rw [e, e2]
    have h2 : a ^ 2 + a * b + b ^ 2 ≤ 3 / 2 * (a + b) := by nlinarith
    exact mul_le_mul_of_nonneg_left h2 hab
  · rw [hc]
    have h1 : a ^ 2 * ((1 / 2) * (a - b) ^ 2 * (a + 2 * b)) ≤
        a * ((1 / 2) * (a - b) ^ 2 * (a + 2 * b)) := by
      have : a ^ 2 ≤ a := by nlinarith
      exact mul_le_mul_of_nonneg_right this hc0
    refine h1.trans ?_
    have e : (a ^ 2 - b ^ 2) ^ 2 = (a - b) ^ 2 * (a + b) ^ 2 := by ring
    rw [e]
    have h2 : a * (a + 2 * b) ≤ 2 * (a + b) ^ 2 := by nlinarith
    have h3 : 0 ≤ (a - b) ^ 2 := sq_nonneg _
    nlinarith

/-- For `a = √q`, `b = √(q - h)`, `0 < h ≤ q ≤ 1`: `0 ≤ q a - (q - h) b ≤ (3/2) h` and
`0 ≤ (q - h) b - q a + (3/2) h a`, `q ((q - h) b - q a + (3/2) h a) ≤ h²`. -/
private lemma LF2_ar_sqrt (q h : ℝ) (hh : 0 < h) (hqh : h ≤ q) (hq1 : q ≤ 1) :
    0 ≤ q * Real.sqrt q - (q - h) * Real.sqrt (q - h) ∧
      q * Real.sqrt q - (q - h) * Real.sqrt (q - h) ≤ 3 / 2 * h ∧
      0 ≤ (q - h) * Real.sqrt (q - h) - q * Real.sqrt q + 3 / 2 * h * Real.sqrt q ∧
      q * ((q - h) * Real.sqrt (q - h) - q * Real.sqrt q + 3 / 2 * h * Real.sqrt q) ≤ h ^ 2 := by
  have ha2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt (by linarith)
  have hb2 : Real.sqrt (q - h) ^ 2 = q - h := Real.sq_sqrt (by linarith)
  have hba : Real.sqrt (q - h) ≤ Real.sqrt q := Real.sqrt_le_sqrt (by linarith)
  have ha1 : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1
  have hapos : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
  have key := LF2_ar_ab (Real.sqrt q) (Real.sqrt (q - h)) h hapos (Real.sqrt_nonneg _) hba ha1
    (by rw [ha2, hb2]; ring)
  rw [ha2, hb2] at key
  exact key

/-- `q^{3/2} |err| ≤ t³ / (N q^{5/2} ι³)` from `|err| ≤ 3 D³ t² ι / (N η⁴)`, `q ι ≤ η` and
`3 D³ ≤ t`. -/
private lemma LF2_ar_err (q ι η D N t er : ℝ) (hq : 0 < q) (hι : 0 < ι) (hN : 0 < N)
    (ht : 0 < t) (hqι : q * ι ≤ η) (hD : 3 * D ^ 3 ≤ t) (her0 : 0 ≤ er)
    (her : er ≤ 3 * D ^ 3 * t ^ 2 * ι / (N * η ^ 4)) :
    q * Real.sqrt q * er ≤ t ^ 3 / (N * (q ^ 2 * Real.sqrt q) * ι ^ 3) := by
  have hη : 0 < η := lt_of_lt_of_le (mul_pos hq hι) hqι
  set a := Real.sqrt q with ha
  have hapos : 0 < a := Real.sqrt_pos.2 hq
  have ha2 : a ^ 2 = q := Real.sq_sqrt hq.le
  have h1 : q * a * er ≤ q * a * (3 * D ^ 3 * t ^ 2 * ι / (N * η ^ 4)) :=
    mul_le_mul_of_nonneg_left her (by positivity)
  refine h1.trans ?_
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (q * ι) ^ 4 ≤ η ^ 4 := pow_le_pow_left₀ (by positivity) hqι 4
  have h4 : 3 * D ^ 3 * t ^ 2 ≤ t ^ 3 := by
    have := mul_le_mul_of_nonneg_right hD (sq_nonneg t)
    nlinarith
  calc q * a * (3 * D ^ 3 * t ^ 2 * ι) * (N * (q ^ 2 * a) * ι ^ 3)
      = (3 * D ^ 3 * t ^ 2) * (N * (q * ι) ^ 4) := by rw [← ha2]; ring
    _ ≤ t ^ 3 * (N * η ^ 4) := by
        apply mul_le_mul h4 _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left h3 hN.le

/-- `D / η^k ≤ D N^k` for `η > N⁻¹`. -/
private lemma LF2_ar_L (D N η : ℝ) (k : ℕ) (hD : 0 ≤ D) (hN : 0 < N) (hη : 0 < η)
    (hηN : N⁻¹ < η) : D / η ^ k ≤ D * N ^ k := by
  rw [div_le_iff₀ (pow_pos hη k)]
  have : 1 ≤ N * η := by rw [inv_lt_iff_one_lt_mul₀ hN] at hηN; linarith
  have h2 : 1 ≤ (N * η) ^ k := one_le_pow₀ this
  rw [mul_pow] at h2
  nlinarith [pow_nonneg hN.le k]

/-- The terms of order `h²` of the drift: `C₁ N^{17} h² + h² (eN + 3) D N³ + (3/2) h² · 3 D³ N⁵
≤ h² N^{20}` for `N ≥ C₁ + D (e + 3) + 5 D³`, `N ≥ 1`. -/
private lemma LF2_ar_fin (C₁ D N h : ℝ) (hD0 : 0 ≤ D) (hN1' : 1 ≤ N)
    (hNC : C₁ + D * (Real.exp 1 + 3) + 5 * D ^ 3 ≤ N) :
    C₁ * N ^ 17 * h ^ 2 + h ^ 2 * (Real.exp 1 * N + 3) * (D * N ^ 3) +
      h * (3 / 2 * h) * (3 * D ^ 3 * N ^ 5) ≤ h ^ 2 * N ^ (20 : ℝ) := by
  rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have p3 : N ^ 4 ≤ N ^ 17 := pow_le_pow_right₀ hN1' (by norm_num)
  have p5 : N ^ 5 ≤ N ^ 17 := pow_le_pow_right₀ hN1' (by norm_num)
  have p18 : N ^ 18 ≤ N ^ 20 := pow_le_pow_right₀ hN1' (by norm_num)
  have he := Real.exp_pos 1
  have he3 : Real.exp 1 * N + 3 ≤ (Real.exp 1 + 3) * N := by nlinarith
  have k1a : (Real.exp 1 * N + 3) * (D * N ^ 3) ≤ ((Real.exp 1 + 3) * N) * (D * N ^ 3) :=
    mul_le_mul_of_nonneg_right he3 (mul_nonneg hD0 (pow_nonneg (by linarith) 3))
  have k1c : (D * (Real.exp 1 + 3)) * N ^ 4 ≤ (D * (Real.exp 1 + 3)) * N ^ 17 :=
    mul_le_mul_of_nonneg_left p3 (mul_nonneg hD0 (by positivity))
  have k1 : h ^ 2 * ((Real.exp 1 * N + 3) * (D * N ^ 3)) ≤
      h ^ 2 * ((D * (Real.exp 1 + 3)) * N ^ 17) := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg h)
    have e : ((Real.exp 1 + 3) * N) * (D * N ^ 3) = (D * (Real.exp 1 + 3)) * N ^ 4 := by
      ring
    linarith
  have k2 : h ^ 2 * ((9 / 2) * D ^ 3 * N ^ 5) ≤ h ^ 2 * ((5 * D ^ 3) * N ^ 17) := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg h)
    have := mul_le_mul_of_nonneg_left p5
      (mul_nonneg (by norm_num) (pow_nonneg hD0 3) : (0 : ℝ) ≤ 5 * D ^ 3)
    have : (9 / 2) * D ^ 3 * N ^ 5 ≤ 5 * D ^ 3 * N ^ 5 := by
      have := pow_nonneg hD0 3; have := pow_nonneg (by linarith : (0 : ℝ) ≤ N) 5; nlinarith
    linarith
  have k3 : (C₁ + D * (Real.exp 1 + 3) + 5 * D ^ 3) * N ^ 17 ≤ N ^ 20 := by
    have := mul_le_mul_of_nonneg_right hNC (pow_nonneg (by linarith) 17 : (0 : ℝ) ≤ N ^ 17)
    have e : N * N ^ 17 = N ^ 18 := by ring
    linarith
  have k4 := mul_le_mul_of_nonneg_left k3 (sq_nonneg h)
  have e1 : h ^ 2 * (Real.exp 1 * N + 3) * (D * N ^ 3) =
      h ^ 2 * ((Real.exp 1 * N + 3) * (D * N ^ 3)) := by ring
  have e2 : h * (3 / 2 * h) * (3 * D ^ 3 * N ^ 5) = h ^ 2 * ((9 / 2) * D ^ 3 * N ^ 5) := by
    ring
  rw [e1, e2]
  linarith

set_option maxHeartbeats 1000000 in
/-- The drift of the three-resolvent equation in one grid step: on the good event at time `s`,
for `L̃ = q_s^{3/2} L_{(1,2,3),s}` and `L̃_{(i,j)} = q_s L_{(i,j),s}`, a step `h ≤ N^{-31}` gives
`|E_X L̃(s + h) - L̃ - h q_s⁻¹ ((3/2)(q_s - 1) L̃ + Σ_a (L̃_{(1,2),xa} L̃_{ayw} +
L̃_{(2,3),ya} L̃_{xaw} + L̃_{(3,1),wa} L̃_{xya}))| ≤
h N^{3τ'} / (N q_s^{5/2} (Im m_s)³) + h² N^{20}`. -/
theorem flowL3_drift (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ s h : ℝ, 0 ≤ s → 0 < h → s + h ≤ S → h ≤ (N : ℝ) ^ (-(31 : ℝ)) →
      ∀ H : Idx D N → Idx D N → ℂ, (Matrix.of H).IsHermitian → flowGoodAt A z τ' s H →
      ∀ z₁ z₂ z₃ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (z₃ = z ∨ z₃ = star z) → ∀ x y w : Fin D,
        let q := flowTc (lam D N A) z - s
        let L₃ := flowLten3 (lam D N A) z₁ z₂ z₃ s H
        ‖(∫ X, (((flowTc (lam D N A) z - (s + h)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
              flowLten3 (lam D N A) z₁ z₂ z₃ (s + h) (Real.exp (-h / 2) • H +
                Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X)) x y w
              ∂(gueBlocks D N)) -
            ((q ^ (3 / 2 : ℝ) : ℝ) : ℂ) * L₃ x y w -
            (h : ℂ) * ((q ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((3 / 2 : ℂ) * ((q - 1 : ℝ) : ℂ) * L₃ x y w +
              (q : ℂ) * ∑ a, (flowLmat (lam D N A) z₁ z₂ s H x a * L₃ a y w +
                flowLmat (lam D N A) z₂ z₃ s H y a * L₃ x a w +
                flowLmat (lam D N A) z₃ z₁ s H w a * L₃ x y a))‖ ≤
          h * ((N : ℝ) ^ (3 * τ') /
              (N * q ^ (5 / 2 : ℝ) * flowIm (lam D N A) z s ^ 3)) +
            h ^ 2 * (N : ℝ) ^ (20 : ℝ) := by
  intro τ' hτ'
  obtain ⟨cR, hcR⟩ := flowLoop_regular
  obtain ⟨KG, hKG⟩ := gaussStepA_expansion_t
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = (D : ℝ) * |KG| * |cR 3| * Real.exp 1 * (4 + τ⁻¹) ^ 2 * 16 *
      (2 * D) ^ 8 := ⟨_, rfl⟩
  have hev : ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N ∧ 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧
      c * (N : ℝ) ^ (-εg) ≤ 1 ∧ 3 * (D : ℝ) ^ 3 ≤ (N : ℝ) ^ τ' ∧
      C₁ + D * (Real.exp 1 + 3) + 5 * (D : ℝ) ^ 3 ≤ N := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    have t3 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ τ') Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hτ').comp tendsto_natCast_atTop_atTop
    refine (Filter.eventually_ge_atTop 2).and (((t1.const_mul 2).eventually
      (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and (((t2.const_mul c).eventually
      (Iic_mem_nhds (by simp : c * 0 < 1))).and ((t3.eventually_ge_atTop _).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop _))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN A z S hadm s h hs0 hh hsh hhN H hH hgood z₁ z₂ z₃ h₁ h₂ h₃ x y w => ?_⟩
  obtain ⟨hN2, hAN, hcN, hDτ, hNC⟩ := hN₀ N hN
  dsimp only
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  haveI : NeZero D := ⟨by omega⟩
  haveI : NeZero N := ⟨by omega⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hΛ10, hzτ, hz, hm1, hq0, hq1, hS0, hSt, hη⟩ :=
    LF2_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  have hSpos : 0 < S := by linarith
  have hsS : s ≤ S := by linarith
  have hsq : s < flowTc (lam D N A) z := by linarith
  obtain ⟨hηs, hιeq, hι0, hιs1, -, -, hqι⟩ := LF2_flow D N hD1 hN1 A hΛ10 z hz S hSt s hs0 hsS
  have hιs : 0 < flowIm (lam D N A) z s := by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
  have hh1 : h ≤ 1 :=
    hhN.trans (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num))
  have hΛ : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hlf : ∀ f ∈ LF2_l (N := N) z₁ z₂ z₃ x y w, f.2 = z ∨ f.2 = star z := by
    intro f hf
    simp only [LF2_l, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    exacts [h₁, h₂, h₃]
  obtain ⟨Ft, hder, hreg⟩ := hcR D N (lam D N A) hΛ z hz (LF2_l z₁ z₂ z₃ x y w) hlf S hS0 hSt
  have hsub : Set.Icc s (s + h) ⊆ Set.Icc 0 S := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hexp := hKG D N (fun r v => flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x y w) r v) Ft _ h s hh
    hh1 (fun r hr => ⟨(hreg r (hsub hr)).1, (hreg r (hsub hr)).2.1⟩)
    (fun r hr v => (hder r (hsub hr) v).mono hsub)
    (fun r hr j hj1 hj4 v => (hreg r (hsub hr)).2.2.1 j hj1 hj4 v)
    (fun r hr r' hr' v => (hreg r (hsub hr)).2.2.2 r' (hsub hr') v) H
  have hφ : ∀ (r : ℝ) (H' : Idx D N → Idx D N → ℂ), (Matrix.of H').IsHermitian →
      flowLten3 (lam D N A) z₁ z₂ z₃ r H' x y w =
        (D : ℂ) * flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x y w) r H' :=
    fun r H' hH' => LF2_Lten_loop' _ _ _ _ _ _ _ _ _ hH'
  have hsI : s ∈ Set.Icc 0 S := ⟨hs0, hsS⟩
  have hd1 : HasDerivWithinAt (fun r => flowLten3 (lam D N A) z₁ z₂ z₃ r H x y w)
      ((D : ℂ) * Ft s H) (Set.Icc 0 S) s :=
    ((hder s hsI H).const_mul (D : ℂ)).congr (fun r _ => hφ r H hH) (hφ s H hH)
  have hd2 := gen_loop3 D N A z hz s hsq z₁ z₂ z₃ h₁ h₂ h₃ H hH x y w
  have huniq := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc hSpos s hsI) hd1
    hd2.hasDerivWithinAt
  have hgen : genA (fun h => Lten3 (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) (hermPart h)
        (charFlowZ (lam D N A) z₁ s) (charFlowZ (lam D N A) z₂ s) (charFlowZ (lam D N A) z₃ s)
        x y w) H =
      (D : ℂ) * genA (flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x y w) s) H := by
    have e : (fun h => Lten3 (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) (hermPart h)
        (charFlowZ (lam D N A) z₁ s) (charFlowZ (lam D N A) z₂ s) (charFlowZ (lam D N A) z₃ s)
        x y w) =
        fun h => ((D : ℝ) : ℂ) * flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x y w) s h := by
      funext h
      have := LF2_Lten_loop (lam D N A) z₁ z₂ z₃ x y w s h
      simp only [flowLten3] at this
      rw [this]
      push_cast
      rfl
    rw [e, LF2_genA_smul _ ((hreg s hsI).1.of_le (by norm_num))]
    push_cast
    rfl
  -- the weights
  set q := flowTc (lam D N A) z - s with hq
  have hqpos : 0 < q := by rw [hq]; linarith
  have hqh : h ≤ q := by rw [hq]; linarith
  have hq1' : q ≤ 1 := by rw [hq]; linarith
  obtain ⟨hp1, hp2⟩ := LF2_rpow32 q hqpos.le
  obtain ⟨hp3, -⟩ := LF2_rpow32 (q - h) (by linarith)
  have hp4 : (flowTc (lam D N A) z - (s + h)) = q - h := by rw [hq]; ring
  have hp5 : q ^ (5 / 2 : ℝ) = q ^ 2 * Real.sqrt q := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add' hqpos.le (by norm_num),
      Real.sqrt_eq_rpow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hp4, hp1, hp2, hp3, hp5]
  obtain ⟨hs1, hs2, hs3, hs4⟩ := LF2_ar_sqrt q h hh hqh hq1'
  set α := Real.sqrt q with hα
  set β := Real.sqrt (q - h) with hβ
  -- the integral
  have hint : (∫ X, (((q - h) * β : ℝ) : ℂ) *
        flowLten3 (lam D N A) z₁ z₂ z₃ (s + h) (Real.exp (-h / 2) • H +
          Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X)) x y w
        ∂(gueBlocks D N)) =
      (((q - h) * β : ℝ) : ℂ) * ((D : ℂ) *
        ∫ X, flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x y w) (s + h) (Real.exp (-h / 2) • H +
          Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X)) ∂(gueBlocks D N)) := by
    rw [integral_const_mul, integral_congr_ae (Filter.Eventually.of_forall fun X =>
      hφ _ _ (LF2_state_herm _ _ H hH X)), integral_const_mul]
  rw [hint]
  set E := ∫ X, flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x y w) (s + h) (Real.exp (-h / 2) • H +
    Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X)) ∂(gueBlocks D N) with hE
  set Fs := flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x y w) s H with hFs
  set gA := genA (flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x y w) s) H with hgA
  set R := E - Fs - h * (Ft s H + gA) with hR
  set Lx := flowLten3 (lam D N A) z₁ z₂ z₃ s H x y w with hLx
  set SL := ∑ a, (flowLmat (lam D N A) z₁ z₂ s H x a * flowLten3 (lam D N A) z₁ z₂ z₃ s H a y w +
    flowLmat (lam D N A) z₂ z₃ s H y a * flowLten3 (lam D N A) z₁ z₂ z₃ s H x a w +
    flowLmat (lam D N A) z₃ z₁ s H w a * flowLten3 (lam D N A) z₁ z₂ z₃ s H x y a) with hSL
  set er := LF2_err (lam D N A) z₁ z₂ z₃ s H x y w with her
  have hLF : Lx = (D : ℂ) * Fs := hφ s H hH
  have hder' : (D : ℂ) * Ft s H = (3 / 2 : ℂ) * Lx + SL + er -
      (D : ℂ) * genA (flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x y w) s) H := by
    rw [huniq, ← hgen]
    rfl
  set P' := (q - h) * β with hP'
  set P := q * α with hP
  set c₁ := (P' - P + 3 / 2 * h * α) + 3 / 2 * h * (P' - P) with hc₁
  have ekey : ((P' : ℝ) : ℂ) * ((D : ℂ) * E) - ((P : ℝ) : ℂ) * Lx -
        (h : ℂ) * ((α : ℝ) : ℂ) * ((3 / 2 : ℂ) * ((q - 1 : ℝ) : ℂ) * Lx + (q : ℂ) * SL) =
      ((P' : ℝ) : ℂ) * ((D : ℂ) * R) + (h : ℂ) * ((P' : ℝ) : ℂ) * er + ((c₁ : ℝ) : ℂ) * Lx +
        (h : ℂ) * (((P' - P) : ℝ) : ℂ) * SL := by
    have hPa : ((P : ℝ) : ℂ) = (q : ℂ) * (α : ℂ) := by rw [hP]; push_cast; ring
    rw [hc₁]
    push_cast
    rw [hPa]
    linear_combination (↑P' : ℂ) * (D : ℂ) * hR - (↑P' : ℂ) * hLF + (↑P' : ℂ) * (h : ℂ) * hder'
  rw [ekey]
  clear_value E Fs gA R SL er c₁ P P'
  -- bounds
  have hb0 : 0 ≤ β := Real.sqrt_nonneg _
  have ha0 : 0 ≤ α := Real.sqrt_nonneg _
  have hP'0 : 0 ≤ P' := by rw [hP']; exact mul_nonneg (by linarith) hb0
  have hP'1 : P' ≤ 1 := by
    have : β ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    rw [hP']
    calc (q - h) * β ≤ 1 * 1 := mul_le_mul (by linarith only [hq1', hh]) this hb0 zero_le_one
      _ = 1 := one_mul 1
  have hP'P : P' ≤ P := by linarith only [hs1]
  have hHn : ‖H‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => hgood.2.2 i j
  -- the remainder of the expansion
  have hηS := (hη S hS0 le_rfl).1
  have hBle := LF2_ar_B (cR 3) D N (Real.exp (flowTc (lam D N A) z))
    (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A))
    (opNorm (Ea D N w) * (opNorm (Ea D N x) * opNorm (Ea D N y)))
    (min 1 (charFlowZ (lam D N A) z S).im) τ
    (by exact_mod_cast hD1) hNr (Real.exp_le_exp.2 hq1) (Real.exp_pos _).le
    (by have h1 := norm_nonneg z; have h2 := norm_nonneg (mExt (lam D N A) z)
        have h3 := LF2_op_nonneg (lam D N A); linarith only [h1, h2, h3])
    (by linarith only [hzτ, hm1, hΛ10])
    (mul_nonneg (LF2_op_nonneg _) (mul_nonneg (LF2_op_nonneg _) (LF2_op_nonneg _)))
    ((mul_le_mul (LF2_opNorm_Ea D N w) ((mul_le_mul (LF2_opNorm_Ea D N x) (LF2_opNorm_Ea D N y)
      (LF2_op_nonneg _) zero_le_one).trans_eq (one_mul 1)) (mul_nonneg (LF2_op_nonneg _)
      (LF2_op_nonneg _)) zero_le_one).trans_eq (one_mul 1))
    (le_min (inv_le_one_of_one_le₀ (by linarith)) hηS.le)
  have hB0 : 0 ≤ cR (LF2_l (N := N) z₁ z₂ z₃ x y w).length * ((D : ℝ) * N + 1) ^ 4 *
      Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      ((LF2_l (N := N) z₁ z₂ z₃ x y w).map fun f => opNorm f.1).prod *
      ((min 1 (charFlowZ (lam D N A) z S).im) ^
        ((LF2_l (N := N) z₁ z₂ z₃ x y w).length + 6))⁻¹ :=
    (norm_nonneg _).trans ((hreg s hsI).2.2.1 1 le_rfl (by norm_num) H).1
  have hBeq : cR (LF2_l (N := N) z₁ z₂ z₃ x y w).length * ((D : ℝ) * N + 1) ^ 4 *
      Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      ((LF2_l (N := N) z₁ z₂ z₃ x y w).map fun f => opNorm f.1).prod *
      ((min 1 (charFlowZ (lam D N A) z S).im) ^
        ((LF2_l (N := N) z₁ z₂ z₃ x y w).length + 6))⁻¹ =
      cR 3 * ((D : ℝ) * N + 1) ^ 4 * Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      (opNorm (Ea D N w) * (opNorm (Ea D N x) * opNorm (Ea D N y))) *
      ((min 1 (charFlowZ (lam D N A) z S).im) ^ 9)⁻¹ := by
    simp only [LF2_l, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
  rw [hBeq] at hB0 hexp
  have hR17 : (D : ℝ) * ‖R‖ ≤ C₁ * (N : ℝ) ^ 17 * h ^ 2 := by
    rw [hC₁]
    exact LF2_ar_R KG (cR 3) D N h ‖H‖ _ ‖R‖ τ (by exact_mod_cast hD1) hNr hB0 hBle
      (norm_nonneg _) hHn hexp
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  -- the fluctuation term
  have herr := LF2_err_le D N hD1 hN1 A z hz s hsq τ' H hH hgood z₁ z₂ z₃ h₁ h₂ h₃ x y w
  rw [← her] at herr
  have herrq : P * ‖er‖ ≤ (N : ℝ) ^ (3 * τ') /
      (N * (q ^ 2 * α) * flowIm (lam D N A) z s ^ 3) := by
    rw [LF2_rpow3 _ _ hNpos.le, hP]
    exact LF2_ar_err q (flowIm (lam D N A) z s) (charFlowZ (lam D N A) z s).im D N
      ((N : ℝ) ^ τ') ‖er‖ hqpos hιs hNpos (Real.rpow_pos_of_pos hNpos _) hqι hDτ
      (norm_nonneg _) herr
  -- `q ≥ (eN)⁻¹`
  have hqN : 1 ≤ Real.exp 1 * N * q := by
    have hup := LF2_flow_up D N hD1 hN1 A hΛ10 z hz S hSt hq1 S hS0 le_rfl
    obtain ⟨-, hιeqS, -, hιS1, -, -, -⟩ := LF2_flow D N hD1 hN1 A hΛ10 z hz S hSt S hS0 le_rfl
    have hιS : 0 < flowIm (lam D N A) z S := by rw [hιeqS]; exact mul_pos (Real.exp_pos _) hι0
    have h1 := hηS
    rw [inv_lt_iff_one_lt_mul₀ hNpos] at h1
    have he := Real.exp_pos 1
    have h2 : flowTc (lam D N A) z - S ≤ q := by rw [hq]; linarith
    have hx : 0 ≤ Real.exp 1 * (flowTc (lam D N A) z - S) := mul_nonneg he.le (by linarith)
    have h3 := mul_le_mul_of_nonneg_left hup hNpos.le
    have h4 : Real.exp 1 * (flowTc (lam D N A) z - S) * flowIm (lam D N A) z S ≤
        Real.exp 1 * (flowTc (lam D N A) z - S) := by
      have := mul_le_mul_of_nonneg_left hιS1.le hx
      linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hNpos.le
    have h6 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 he.le) hNpos.le
    linarith
  -- the terms of order `h²`
  have hLb : ∀ a b : Fin D, ‖flowLmat (lam D N A) z₁ z₂ s H a b‖ ≤ D * (N : ℝ) ^ 2 ∧
      ‖flowLmat (lam D N A) z₂ z₃ s H a b‖ ≤ D * (N : ℝ) ^ 2 ∧
      ‖flowLmat (lam D N A) z₃ z₁ s H a b‖ ≤ D * (N : ℝ) ^ 2 := by
    intro a b
    have hk := LF2_ar_L D N _ 2 (Nat.cast_nonneg D) hNpos hηs (hη s hs0 hsS).1
    exact ⟨(LF2_L_le D N hD1 hN1 A z hz s hsq H hH z₁ z₂ h₁ h₂ a b).trans hk,
      (LF2_L_le D N hD1 hN1 A z hz s hsq H hH z₂ z₃ h₂ h₃ a b).trans hk,
      (LF2_L_le D N hD1 hN1 A z hz s hsq H hH z₃ z₁ h₃ h₁ a b).trans hk⟩
  have hL3b : ∀ a b c : Fin D, ‖flowLten3 (lam D N A) z₁ z₂ z₃ s H a b c‖ ≤ D * (N : ℝ) ^ 3 :=
    fun a b c => (LF2_Lten_le D N hD1 hN1 A z hz s hsq H hH z₁ z₂ z₃ h₁ h₂ h₃ a b c).trans
      (LF2_ar_L D N _ 3 (Nat.cast_nonneg D) hNpos hηs (hη s hs0 hsS).1)
  have hSLb : ‖SL‖ ≤ 3 * D ^ 3 * (N : ℝ) ^ 5 := by
    rw [hSL]
    refine (norm_sum_le _ _).trans ?_
    have hX : 0 ≤ (D : ℝ) * (N : ℝ) ^ 2 := by positivity
    calc ∑ a, ‖flowLmat (lam D N A) z₁ z₂ s H x a * flowLten3 (lam D N A) z₁ z₂ z₃ s H a y w +
          flowLmat (lam D N A) z₂ z₃ s H y a * flowLten3 (lam D N A) z₁ z₂ z₃ s H x a w +
          flowLmat (lam D N A) z₃ z₁ s H w a * flowLten3 (lam D N A) z₁ z₂ z₃ s H x y a‖
        ≤ ∑ _a : Fin D, 3 * ((D * (N : ℝ) ^ 2) * (D * (N : ℝ) ^ 3)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
          rw [norm_mul, norm_mul, norm_mul]
          have t1 := mul_le_mul (hLb x a).1 (hL3b a y w) (norm_nonneg _) hX
          have t2 := mul_le_mul (hLb y a).2.1 (hL3b x a w) (norm_nonneg _) hX
          have t3 := mul_le_mul (hLb w a).2.2 (hL3b x y a) (norm_nonneg _) hX
          linarith
      _ = 3 * D ^ 3 * (N : ℝ) ^ 5 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hc₁b : |c₁| ≤ h ^ 2 * (Real.exp 1 * N + 3) := by
    have he := Real.exp_pos 1
    have hc₁' : P' - P + 3 / 2 * h * α ≤ h ^ 2 * (Real.exp 1 * N) := by
      have h3 : (P' - P + 3 / 2 * h * α) * 1 ≤
          (P' - P + 3 / 2 * h * α) * (Real.exp 1 * N * q) := mul_le_mul_of_nonneg_left hqN hs3
      have h4 := mul_le_mul_of_nonneg_left hs4 (by positivity : (0 : ℝ) ≤ Real.exp 1 * N)
      linarith
    have k1 : 3 / 2 * h * (P - P') ≤ 3 / 2 * h * (3 / 2 * h) :=
      mul_le_mul_of_nonneg_left hs2 (by positivity)
    have k2 : 0 ≤ 3 / 2 * h * (P - P') := mul_nonneg (by positivity) hs1
    have k3 : 0 ≤ h ^ 2 * (Real.exp 1 * N) := by positivity
    have k4 : 0 ≤ h ^ 2 := sq_nonneg h
    rw [hc₁, abs_le]
    constructor <;> linarith only [hs3, hc₁', k1, k2, k3, k4]
  -- assembly
  have hnorm1 : ‖((P' : ℝ) : ℂ) * ((D : ℂ) * R)‖ ≤ C₁ * (N : ℝ) ^ 17 * h ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP'0,
      Complex.norm_natCast]
    calc P' * (D * ‖R‖) ≤ 1 * (C₁ * (N : ℝ) ^ 17 * h ^ 2) :=
          mul_le_mul hP'1 hR17 (by positivity) zero_le_one
      _ = _ := one_mul _
  have hnorm2 : ‖(h : ℂ) * ((P' : ℝ) : ℂ) * er‖ ≤ h * ((N : ℝ) ^ (3 * τ') /
      (N * (q ^ 2 * α) * flowIm (lam D N A) z s ^ 3)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hh, abs_of_nonneg hP'0, mul_assoc]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ herrq) hh.le
    exact mul_le_mul_of_nonneg_right hP'P (norm_nonneg _)
  have hnorm3 : ‖((c₁ : ℝ) : ℂ) * Lx‖ ≤ h ^ 2 * (Real.exp 1 * N + 3) * (D * (N : ℝ) ^ 3) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hc₁b (hL3b x y w) (norm_nonneg _) (by positivity)
  have hnorm4 : ‖(h : ℂ) * (((P' - P) : ℝ) : ℂ) * SL‖ ≤
      h * (3 / 2 * h) * (3 * D ^ 3 * (N : ℝ) ^ 5) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hh, abs_of_nonpos (by linarith)]
    refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hh.le) hSLb (norm_nonneg _)
      (by positivity)
  have hfin := LF2_ar_fin C₁ D N h (Nat.cast_nonneg D) (by linarith) hNC
  calc ‖((P' : ℝ) : ℂ) * ((D : ℂ) * R) + (h : ℂ) * ((P' : ℝ) : ℂ) * er + ((c₁ : ℝ) : ℂ) * Lx +
        (h : ℂ) * (((P' - P) : ℝ) : ℂ) * SL‖
      ≤ ‖((P' : ℝ) : ℂ) * ((D : ℂ) * R)‖ + ‖(h : ℂ) * ((P' : ℝ) : ℂ) * er‖ +
        ‖((c₁ : ℝ) : ℂ) * Lx‖ + ‖(h : ℂ) * (((P' - P) : ℝ) : ℂ) * SL‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ C₁ * (N : ℝ) ^ 17 * h ^ 2 + h * ((N : ℝ) ^ (3 * τ') /
          (N * (q ^ 2 * α) * flowIm (lam D N A) z s ^ 3)) +
        h ^ 2 * (Real.exp 1 * N + 3) * (D * (N : ℝ) ^ 3) +
        h * (3 / 2 * h) * (3 * D ^ 3 * (N : ℝ) ^ 5) :=
        add_le_add (add_le_add (add_le_add hnorm1 hnorm2) hnorm3) hnorm4
    _ ≤ _ := by linarith

/-! ### Gaussian and grid tools for the martingale part -/

/-- The map `(x, y) ↦ x + y i` as a continuous linear map. -/
private def LF2_RealPairToC : ℝ × ℝ →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I

/-- `cGauss` is a Gaussian law. -/
private instance LF2_cGauss_isGaussian : IsGaussian (cGauss : Measure ℂ) := by
  have : (cGauss : Measure ℂ) =
      ((gaussianReal 0 (1 / 2 : ℝ≥0)).prod (gaussianReal 0 (1 / 2 : ℝ≥0))).map
        LF2_RealPairToC := by
    have e : (LF2_RealPairToC : ℝ × ℝ → ℂ) =
        fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      funext p; simp [LF2_RealPairToC, Complex.real_smul]
    rw [e]
    rfl
  rw [this]
  infer_instance

/-- A product of copies of a Gaussian law is Gaussian. -/
private instance LF2_isGaussian_pi {ι X : Type*} [Fintype ι] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [CompleteSpace X] (μ : Measure X) [IsGaussian μ] :
    IsGaussian (Measure.pi fun _ : ι => μ) := by
  have hind : iIndepFun (fun (i : ι) (ω : ι → X) => (id : X → X) (ω i))
      (Measure.pi fun _ : ι => μ) :=
    iIndepFun_pi (X := fun _ => (id : X → X)) (fun i => aemeasurable_id)
  have hg : ∀ i : ι, HasGaussianLaw (fun ω : ι → X => ω i) (Measure.pi fun _ : ι => μ) :=
    fun i => ⟨(measurable_pi_apply i).aemeasurable, by
      rw [(measurePreserving_eval (fun _ : ι => μ) i).map_eq]; infer_instance⟩
  have h2 := (iIndepFun.hasGaussianLaw hg hind).isGaussian_map
  simpa using h2

/-- The law of the GUE blocks is Gaussian. -/
private instance LF2_gueBlocks_isGaussian (D N : ℕ) : IsGaussian (gueBlocks D N) := by
  have : IsGaussian (gueLaw N) := by unfold gueLaw; infer_instance
  unfold gueBlocks
  infer_instance

/-- `‖x‖^p` is integrable under the GUE blocks. -/
private lemma LF2_int_pow (D N p : ℕ) :
    Integrable (fun x : Fin D → Coords N => ‖x‖ ^ p) (gueBlocks D N) :=
  (IsGaussian.memLp_id (gueBlocks D N) p (by simp)).integrable_norm_pow'

/-- `x ↦ -x` preserves the GUE blocks. -/
private lemma LF2_gueBlocks_neg (D N : ℕ) :
    MeasurePreserving (fun x : Fin D → Coords N => -x) (gueBlocks D N) (gueBlocks D N) := by
  refine ⟨measurable_neg, ?_⟩
  have := Measure.pi_map_pi (μ := fun _ : Fin D => gueLaw N) (f := fun _ x => -x)
    (fun _ => measurable_neg.aemeasurable)
  simp only [gueLaw_map_neg] at this
  exact this

/-- An odd function has integral `0` under the GUE blocks. -/
private lemma LF2_gueBlocks_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (D N : ℕ)
    (f : (Fin D → Coords N) → E) (hf : ∀ x, f (-x) = -f x) :
    ∫ x, f x ∂(gueBlocks D N) = 0 := by
  have h := (LF2_gueBlocks_neg D N).integral_comp (MeasurableEquiv.neg _).measurableEmbedding f
  simp only [hf, integral_neg] at h
  have : (2 : ℝ) • ∫ x, f x ∂(gueBlocks D N) = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; simp
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

/-- `‖x‖⁴ ≤ Σ_i ‖x_i‖⁴` for the sup norm of a finite product. -/
private lemma LF2_pi_pow4 {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (x : ι → E) :
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

/-- `‖(u, v)‖⁴ ≤ ‖u‖⁴ + ‖v‖⁴` for the sup norm of a product. -/
private lemma LF2_prod_pow4 {E G : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup G]
    (p : E × G) : ‖p‖ ^ 4 ≤ ‖p.1‖ ^ 4 + ‖p.2‖ ^ 4 := by
  rw [Prod.norm_def]
  rcases le_total ‖p.1‖ ‖p.2‖ with h | h
  · rw [max_eq_right h]; have := pow_nonneg (norm_nonneg p.1) 4; linarith
  · rw [max_eq_left h]; have := pow_nonneg (norm_nonneg p.2) 4; linarith

/-- The fourth moment of the GUE blocks: `E‖X‖⁴ ≤ (DN + DN²)(m₄ + m₄')`, with `m₄` and `m₄'` the
fourth absolute moments of `N(0, 1)` and of the standard complex Gaussian. -/
private lemma LF2_moment4 (D N : ℕ) :
    ∫ x, ‖x‖ ^ 4 ∂(gueBlocks D N) ≤ ((D : ℝ) * N + D * N * N) *
      ((∫ y, ‖y‖ ^ 4 ∂(gaussianReal 0 1)) + ∫ z, ‖z‖ ^ 4 ∂(cGauss : Measure ℂ)) := by
  set γ := gueBlocks D N with hγ
  set mR := ∫ y, ‖y‖ ^ 4 ∂(gaussianReal 0 1) with hmR
  set mC := ∫ z, ‖z‖ ^ 4 ∂(cGauss : Measure ℂ) with hmC
  have hmR0 : 0 ≤ mR := integral_nonneg fun y => by positivity
  have hmC0 : 0 ≤ mC := integral_nonneg fun z => by positivity
  have iR : Integrable (fun y : ℝ => ‖y‖ ^ 4) (gaussianReal 0 1) :=
    (IsGaussian.memLp_id (gaussianReal 0 1) 4 (by simp)).integrable_norm_pow'
  have iC : Integrable (fun z : ℂ => ‖z‖ ^ 4) (cGauss : Measure ℂ) :=
    (IsGaussian.memLp_id (cGauss : Measure ℂ) 4 (by simp)).integrable_norm_pow'
  have mpD : ∀ (a : Fin D) (i : Fin N), MeasurePreserving
      (fun x : Fin D → Coords N => (x a).1 i) γ (gaussianReal 0 1) := by
    intro a i
    have h2 : MeasurePreserving (Prod.fst : Coords N → Fin N → ℝ) (gueLaw N)
        (Measure.pi fun _ : Fin N => gaussianReal 0 1) := measurePreserving_fst
    exact (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).comp
      (h2.comp (measurePreserving_eval (fun _ : Fin D => gueLaw N) a))
  have mpA : ∀ (a : Fin D) (i j : Fin N), MeasurePreserving
      (fun x : Fin D → Coords N => (x a).2 i j) γ (cGauss : Measure ℂ) := by
    intro a i j
    have h2 : MeasurePreserving (Prod.snd : Coords N → Fin N → Fin N → ℂ) (gueLaw N)
        (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (cGauss : Measure ℂ)) :=
      measurePreserving_snd
    have h3 := measurePreserving_eval
      (fun _ : Fin N => Measure.pi fun _ : Fin N => (cGauss : Measure ℂ)) i
    have h4 := measurePreserving_eval (fun _ : Fin N => (cGauss : Measure ℂ)) j
    exact h4.comp (h3.comp (h2.comp (measurePreserving_eval (fun _ : Fin D => gueLaw N) a)))
  have iDc : ∀ (a : Fin D) (i : Fin N),
      Integrable (fun x : Fin D → Coords N => ‖(x a).1 i‖ ^ 4) γ :=
    fun a i => (mpD a i).integrable_comp_of_integrable (g := fun y : ℝ => ‖y‖ ^ 4) iR
  have iAc : ∀ (a : Fin D) (i j : Fin N),
      Integrable (fun x : Fin D → Coords N => ‖(x a).2 i j‖ ^ 4) γ :=
    fun a i j => (mpA a i j).integrable_comp_of_integrable (g := fun z : ℂ => ‖z‖ ^ 4) iC
  have eD : ∀ (a : Fin D) (i : Fin N), ∫ x, ‖(x a).1 i‖ ^ 4 ∂γ = mR := by
    intro a i
    have := integral_map (μ := γ) (mpD a i).measurable.aemeasurable
      (continuous_norm.pow 4).aestronglyMeasurable (f := fun y : ℝ => ‖y‖ ^ 4)
    rw [(mpD a i).map_eq] at this
    exact this.symm
  have eA : ∀ (a : Fin D) (i j : Fin N), ∫ x, ‖(x a).2 i j‖ ^ 4 ∂γ = mC := by
    intro a i j
    have := integral_map (μ := γ) (mpA a i j).measurable.aemeasurable
      (continuous_norm.pow 4).aestronglyMeasurable (f := fun z : ℂ => ‖z‖ ^ 4)
    rw [(mpA a i j).map_eq] at this
    exact this.symm
  have hpt : ∀ x : Fin D → Coords N, ‖x‖ ^ 4 ≤
      ∑ a, ((∑ i, ‖(x a).1 i‖ ^ 4) + ∑ i, ∑ j, ‖(x a).2 i j‖ ^ 4) := by
    intro x
    refine (LF2_pi_pow4 x).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (LF2_prod_pow4 (x a)).trans (add_le_add (LF2_pi_pow4 _) ?_)
    exact (LF2_pi_pow4 _).trans (Finset.sum_le_sum fun i _ => LF2_pi_pow4 _)
  have iS : ∀ a : Fin D, Integrable (fun x : Fin D → Coords N =>
      (∑ i, ‖(x a).1 i‖ ^ 4) + ∑ i, ∑ j, ‖(x a).2 i j‖ ^ 4) γ := fun a =>
    (integrable_finsetSum _ fun i _ => iDc a i).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iAc a i j)
  calc ∫ x, ‖x‖ ^ 4 ∂γ ≤ ∫ x, ∑ a, ((∑ i, ‖(x a).1 i‖ ^ 4) + ∑ i, ∑ j, ‖(x a).2 i j‖ ^ 4) ∂γ :=
        integral_mono (LF2_int_pow D N 4) (integrable_finsetSum _ fun a _ => iS a) hpt
    _ = ∑ a : Fin D, ((∑ i : Fin N, mR) + ∑ i : Fin N, ∑ j : Fin N, mC) := by
        rw [integral_finsetSum _ fun a _ => iS a]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_add (integrable_finsetSum _ fun i _ => iDc a i)
          (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iAc a i j),
          integral_finsetSum _ fun i _ => iDc a i,
          integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iAc a i j]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => eD a i
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum _ fun j _ => iAc a i j]
          exact Finset.sum_congr rfl fun j _ => eA a i j
    _ = (D : ℝ) * N * mR + D * N * N * mC := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ ((D : ℝ) * N + D * N * N) * (mR + mC) := by
        have h1 : (0 : ℝ) ≤ D * N * mC := by positivity
        have h2 : (0 : ℝ) ≤ D * N * N * mR := by positivity
        have e : ((D : ℝ) * N + D * N * N) * (mR + mC) =
            (D : ℝ) * N * mR + D * N * N * mC + (D * N * mC + D * N * N * mR) := by ring
        linarith

/-- The increment `X_{k+1}` has the law `gueBlocks D N` under the grid law. -/
private lemma LF2_incr_law (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] (k : ℕ) (hk : k < K) :
    MeasurePreserving (fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩) (gridLawA D N K μ₀)
      (gueBlocks D N) :=
  (measurePreserving_eval (fun _ : Fin K => gueBlocks D N) ⟨k, hk⟩).comp measurePreserving_snd

/-- The increment `X_{k+1}` is `𝓕_{k+1}`-measurable. -/
private lemma LF2_incr_meas (D N K k : ℕ) (hk : k < K) :
    Measurable[gridFiltrA D N K (k + 1)] fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩ := by
  have e : (fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩) = (fun u : GridΩA D N K => u.2 ⟨k, hk⟩) ∘
      (fun ω : GridΩA D N K =>
        (ω.1, fun j : Fin K => if (j : ℕ) < k + 1 then ω.2 j else 0)) := by
    funext ω
    simp
  rw [e]
  exact ((measurable_pi_apply _).comp measurable_snd).comp (comap_measurable _)

/-- The generating map of `𝓕_k`: the initial array and the increments `X_{j+1}`, `j < k`. -/
private def LF2_mask (D N K k : ℕ) (ω : GridΩA D N K) : GridΩA D N K :=
  (ω.1, fun j : Fin K => if (j : ℕ) < k then ω.2 j else 0)

private lemma LF2_mask_measurable (D N K k : ℕ) : Measurable (LF2_mask D N K k) := by
  unfold LF2_mask
  refine measurable_fst.prodMk (measurable_pi_iff.mpr fun j => ?_)
  by_cases hj : (j : ℕ) < k
  · simp only [hj, ↓reduceIte]
    fun_prop
  · simp [hj]

/-- `H_j` depends only on the generating map of `𝓕_k`, `j ≤ k`. -/
private lemma LF2_state_mask (D N K : ℕ) (h : ℝ) (k : ℕ) (ω : GridΩA D N K) :
    ∀ j, j ≤ k → gridStateA D N K h (LF2_mask D N K k ω) j = gridStateA D N K h ω j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    simp only [gridStateA, h1]
    congr 2
    by_cases hjK : j < K
    · simp only [hjK, ↓reduceDIte, LF2_mask]
      have : j < k := by omega
      simp [this]
    · simp [hjK]

/-- Every grid state is measurable. -/
private lemma LF2_state_meas (D N K : ℕ) (h : ℝ) (k : ℕ) :
    Measurable fun ω : GridΩA D N K => gridStateA D N K h ω k :=
  (gridStateA_adapted D N K h k).mono ((gridFiltrA_mono D N K).2 k) le_rfl

/-- The one-step conditional expectation of `Γ(H_k, X_{k+1})` integrates out `X_{k+1}`, for a
measurable `Γ` with `|Γ(H, x)| ≤ C (1 + ‖x‖)`. -/
private lemma LF2_condExp (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] (h : ℝ) (k : ℕ) (hk : k < K)
    (Γ : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) → ℝ) (hΓ : Measurable Γ) (C : ℝ)
    (hC : ∀ p, |Γ p| ≤ C * (1 + ‖p.2‖)) :
    (gridLawA D N K μ₀)[fun ω => Γ (gridStateA D N K h ω k, ω.2 ⟨k, hk⟩) | gridFiltrA D N K k]
      =ᵐ[gridLawA D N K μ₀]
      fun ω => ∫ x, Γ (gridStateA D N K h ω k, x) ∂(gueBlocks D N) := by
  set μ := gridLawA D N K μ₀ with hμ
  set γ := gueBlocks D N with hγ
  have hm : gridFiltrA D N K k ≤ _ := (gridFiltrA_mono D N K).2 k
  set V : GridΩA D N K → Fin D → Coords N := fun ω => ω.2 ⟨k, hk⟩ with hV
  have hVm : Measurable V := (measurable_pi_apply _).comp measurable_snd
  have hmV : μ.map V = γ := (LF2_incr_law D N K μ₀ k hk).map_eq
  have hind : ProbabilityTheory.IndepFun (LF2_mask D N K k) V μ :=
    (ProbabilityTheory.IndepFun_iff_Indep _ _ _).2 (gridIncrA_indep D N K μ₀ k hk)
  have hC0 : 0 ≤ C := by
    have := hC (0, 0)
    have h2 : 0 ≤ C * (1 + ‖((0 : Idx D N → Idx D N → ℂ), (0 : Fin D → Coords N)).2‖) :=
      (abs_nonneg _).trans this
    simp at h2
    exact h2
  have hi1 : Integrable (fun x : Fin D → Coords N => ‖x‖) (gueBlocks D N) := by
    have h1 := LF2_int_pow D N 1
    simp only [pow_one] at h1
    exact h1
  have hint1 : Integrable (fun x : Fin D → Coords N => C * (1 + ‖x‖)) γ :=
    ((integrable_const 1).add hi1).const_mul C
  have hHk := LF2_state_meas D N K h k
  have hf : Integrable (fun ω => Γ (gridStateA D N K h ω k, V ω)) μ := by
    refine Integrable.mono' ((LF2_incr_law D N K μ₀ k hk).integrable_comp_of_integrable hint1)
      (hΓ.comp (hHk.prodMk hVm)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hC _
  have hGm : StronglyMeasurable fun H : Idx D N → Idx D N → ℂ => ∫ x, Γ (H, x) ∂γ :=
    hΓ.stronglyMeasurable.integral_prod_right'
  have hGb : ∀ H, ‖∫ x, Γ (H, x) ∂γ‖ ≤ ∫ x, C * (1 + ‖x‖) ∂γ := fun H =>
    norm_integral_le_of_norm_le hint1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hC _)
  have hgm : Measurable[gridFiltrA D N K k] fun ω =>
      ∫ x, Γ (gridStateA D N K h ω k, x) ∂γ :=
    hGm.measurable.comp (gridStateA_adapted D N K h k)
  have hgi : Integrable (fun ω => ∫ x, Γ (gridStateA D N K h ω k, x) ∂γ) μ :=
    Integrable.of_bound (hgm.mono hm le_rfl).aestronglyMeasurable _
      (ae_of_all _ fun ω => hGb _)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun s _ _ => hgi.integrableOn)
    (fun s hs _ => ?_) hgm.stronglyMeasurable.aestronglyMeasurable).symm
  obtain ⟨T, hT, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
  -- freezing with the generating map
  set A := LF2_mask D N K k with hA
  have hAm : Measurable A := LF2_mask_measurable D N K k
  have hΓ' : Measurable fun p : GridΩA D N K × (Fin D → Coords N) =>
      Γ (gridStateA D N K h p.1 k, p.2) :=
    hΓ.comp ((hHk.comp measurable_fst).prodMk measurable_snd)
  have hpair := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hAm.aemeasurable
    hVm.aemeasurable).1 hind
  have hZ : Measurable fun ω => (A ω, V ω) := hAm.prodMk hVm
  have hGm' : StronglyMeasurable fun u : GridΩA D N K =>
      ∫ v, Γ (gridStateA D N K h u k, v) ∂(μ.map V) :=
    hΓ'.stronglyMeasurable.integral_prod_right'
  have hint : IntegrableOn (fun p : GridΩA D N K × (Fin D → Coords N) =>
      Γ (gridStateA D N K h p.1 k, p.2)) (T ×ˢ (Set.univ : Set (Fin D → Coords N)))
      ((μ.map A).prod (μ.map V)) := by
    refine Integrable.integrableOn ?_
    have hmp : MeasurePreserving (Prod.snd : GridΩA D N K × (Fin D → Coords N) → _)
        ((μ.map A).prod (μ.map V)) (μ.map V) := measurePreserving_snd
    rw [hmV] at hmp ⊢
    refine Integrable.mono' (hmp.integrable_comp_of_integrable hint1)
      hΓ'.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    exact hC _
  have e1 : ∀ ω, gridStateA D N K h ω k = gridStateA D N K h (A ω) k := fun ω =>
    (LF2_state_mask D N K h k ω k le_rfl).symm
  have h1 : ∫ ω in A ⁻¹' T, Γ (gridStateA D N K h ω k, V ω) ∂μ =
      ∫ z in T ×ˢ (Set.univ : Set (Fin D → Coords N)),
        Γ (gridStateA D N K h z.1 k, z.2) ∂((μ.map A).prod (μ.map V)) := by
    have hpre : (fun ω => (A ω, V ω)) ⁻¹' (T ×ˢ (Set.univ : Set (Fin D → Coords N))) =
        A ⁻¹' T := by
      ext; simp
    rw [← hpair, setIntegral_map (hT.prod MeasurableSet.univ) hΓ'.aestronglyMeasurable
      hZ.aemeasurable, hpre]
    simp only [← e1]
  change ∫ ω in A ⁻¹' T, ∫ x, Γ (gridStateA D N K h ω k, x) ∂γ ∂μ =
    ∫ ω in A ⁻¹' T, Γ (gridStateA D N K h ω k, V ω) ∂μ
  rw [h1, setIntegral_prod _ hint]
  simp only [Measure.restrict_univ]
  rw [setIntegral_map hT hGm'.aestronglyMeasurable hAm.aemeasurable, hmV]
  refine setIntegral_congr_fun (hAm hT) fun ω _ => ?_
  simp only [← e1]

/-- The block GUE array `Matrix.of.symm (blockH D N w)` as a real-linear map of `w`. -/
private def LF2_arrLin (D N : ℕ) : (Fin D → Coords N) →ₗ[ℝ] (Idx D N → Idx D N → ℂ) where
  toFun w := Matrix.of.symm (blockH D N w)
  map_add' v w := by
    ext p q
    simp only [blockH, Pi.add_apply, wig_add, Matrix.add_apply, Matrix.of_symm_apply]
    split_ifs <;> simp
  map_smul' c w := by
    ext p q
    simp only [blockH, Pi.smul_apply, wig_smul, Matrix.smul_apply, Matrix.of_symm_apply,
      RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul]

/-- The block GUE array as a continuous real-linear map of the coordinates. -/
private def LF2_arrL (D N : ℕ) : (Fin D → Coords N) →L[ℝ] (Idx D N → Idx D N → ℂ) :=
  LinearMap.toContinuousLinearMap (LF2_arrLin D N)

private lemma LF2_arrL_apply (D N : ℕ) (w : Fin D → Coords N) :
    LF2_arrL D N w = Matrix.of.symm (blockH D N w) := rfl

/-- An entry of `wig n c` is bounded by the sup norm of the coordinates `c`. -/
private lemma LF2_wig_norm_le (n : ℕ) (c : Coords n) (i j : Fin n) : ‖wig n c i j‖ ≤ ‖c‖ := by
  have hn : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Fin.pos i) (by norm_num)
  have h1 : ‖c.1 i‖ ≤ ‖c‖ := (norm_le_pi_norm c.1 i).trans (norm_fst_le c)
  have h2 : ∀ a b, ‖c.2 a b‖ ≤ ‖c‖ := fun a b =>
    ((norm_le_pi_norm (c.2 a) b).trans (norm_le_pi_norm c.2 a)).trans (norm_snd_le c)
  unfold wig
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmain : ‖(if i = j then ((c.1 i : ℝ) : ℂ) else if i < j then c.2 i j
      else star (c.2 j i))‖ ≤ ‖c‖ := by
    split_ifs
    · simpa using h1
    · exact h2 i j
    · rw [norm_star]
      exact h2 j i
  calc _ ≤ 1 * ‖c‖ := mul_le_mul hn hmain (norm_nonneg _) zero_le_one
    _ = ‖c‖ := one_mul _

/-- The array of a block coordinate vector has sup norm at most that of the coordinates. -/
private lemma LF2_arr_norm_le (D N : ℕ) (w : Fin D → Coords N) :
    ‖Matrix.of.symm (blockH D N w)‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun p =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun q => ?_
  simp only [blockH, Matrix.of_symm_apply]
  split_ifs
  · exact (LF2_wig_norm_le N (w p.1) p.2 q.2).trans (norm_le_pi_norm w p.1)
  · simp

/-- Taylor's formula of order `n` with the remainder bounded by `B ‖y‖^{n+1}`. -/
private lemma LF2_taylor {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] (f : E → W) (n : ℕ)
    (hf : ContDiff ℝ (n + 1) f) (B : ℝ) (hB : ∀ z, ‖iteratedFDeriv ℝ (n + 1) f z‖ ≤ B)
    (x y : E) :
    ‖f (x + y) - ∑ k ∈ Finset.range (n + 1),
        ((k.factorial : ℝ))⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y)‖ ≤ B * ‖y‖ ^ (n + 1) := by
  rw [map_add_eq_sum_add_integral_iteratedFDeriv (fun t _ => hf.contDiffAt), add_sub_cancel_left]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
  have hint : ‖∫ t in (0 : ℝ)..1,
      (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ ≤
        B * ‖y‖ ^ (n + 1) * |1 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have h1 : ‖(1 - t) ^ n‖ ≤ 1 := by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      exact pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
    have h2 : ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ ≤ B * ‖y‖ ^ (n + 1) := by
      refine ((iteratedFDeriv ℝ (n + 1) f (x + t • y)).le_opNorm _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul_of_nonneg_right (hB _) (by positivity)
    rw [norm_smul]
    calc ‖(1 - t) ^ n‖ * ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖
        ≤ 1 * (B * ‖y‖ ^ (n + 1)) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = B * ‖y‖ ^ (n + 1) := one_mul _
  rw [sub_zero, abs_one, mul_one] at hint
  rw [norm_smul]
  have hfac : ‖((n.factorial : ℝ))⁻¹‖ ≤ 1 := by
    rw [norm_inv, Real.norm_natCast]
    exact inv_le_one_of_one_le₀
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n))
  calc ‖((n.factorial : ℝ))⁻¹‖ * ‖∫ t in (0 : ℝ)..1,
        (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖
      ≤ 1 * (B * ‖y‖ ^ (n + 1)) := mul_le_mul hfac hint (norm_nonneg _) zero_le_one
    _ = B * ‖y‖ ^ (n + 1) := one_mul _

/-- First-order Taylor: `|f(H + v) - f(H) - Df(H)[v]| ≤ B ‖v‖²` when `‖D²f‖ ≤ B`. -/
private lemma LF2_taylor1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℂ)
    (hf : ContDiff ℝ 2 f) (B : ℝ) (hB : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ B) (x y : E) :
    ‖f (x + y) - f x - fderiv ℝ f x y‖ ≤ B * ‖y‖ ^ 2 := by
  have h := LF2_taylor f 1 hf B hB x y
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, one_smul, iteratedFDeriv_zero_apply,
    iteratedFDeriv_one_apply] at h
  have e : f (x + y) - f x - fderiv ℝ f x y = f (x + y) - (f x + fderiv ℝ f x y) := by ring
  rw [e]
  simpa using h

/-- The time difference `F(r₂, ·) - F(r₁, ·)` is `B |r₂ - r₁|`-Lipschitz when `∂_s F` is
`C¹` in the array with `‖D ∂_s F‖ ≤ B`. -/
private lemma LF2_tdiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F Ft : ℝ → E → ℂ) (S B : ℝ)
    (hder : ∀ s ∈ Set.Icc 0 S, ∀ v, HasDerivWithinAt (fun r => F r v) (Ft s v) (Set.Icc 0 S) s)
    (hreg : ∀ s ∈ Set.Icc 0 S, Differentiable ℝ (Ft s) ∧ ∀ v, ‖fderiv ℝ (Ft s) v‖ ≤ B)
    (r₁ r₂ : ℝ) (hr₁ : r₁ ∈ Set.Icc 0 S) (hr₂ : r₂ ∈ Set.Icc 0 S) (H₁ H₂ : E) :
    ‖(F r₂ H₁ - F r₁ H₁) - (F r₂ H₂ - F r₁ H₂)‖ ≤ B * ‖H₁ - H₂‖ * |r₂ - r₁| := by
  have hlip : ∀ s ∈ Set.Icc 0 S, ‖Ft s H₁ - Ft s H₂‖ ≤ B * ‖H₁ - H₂‖ := by
    intro s hs
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => (hreg s hs).1 x)
      (fun x _ => (hreg s hs).2 x) convex_univ (Set.mem_univ H₂) (Set.mem_univ H₁)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun r => F r H₁ - F r H₂) (f' := fun r => Ft r H₁ - Ft r H₂)
    (fun x hx => (hder x hx H₁).sub (hder x hx H₂)) hlip (convex_Icc 0 S) hr₁ hr₂
  rw [Real.norm_eq_abs] at this
  calc ‖(F r₂ H₁ - F r₁ H₁) - (F r₂ H₂ - F r₁ H₂)‖
      = ‖(F r₂ H₁ - F r₂ H₂) - (F r₁ H₁ - F r₁ H₂)‖ := by ring_nf
    _ ≤ _ := this

/-! ### The stopping time of the good event -/

/-- The matrix inverse is measurable. -/
private lemma LF2_inv_meas {ι : Type*} [Fintype ι] [DecidableEq ι] :
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

/-- `H ↦ G = (H + Λ - w)⁻¹` is measurable. -/
private lemma LF2_res_meas {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (w : ℂ) :
    Measurable fun H : Idx D N → Idx D N → ℂ => res (Matrix.of H + Λ) w := by
  unfold res
  have : Continuous fun H : Idx D N → Idx D N → ℂ =>
      Matrix.of H + Λ - w • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
    have : Continuous fun H : Idx D N → Idx D N → ℂ => (Matrix.of H : Matrix _ _ ℂ) :=
      continuous_id
    fun_prop
  exact LF2_inv_meas.comp this.measurable

/-- `G ↦ ⟨Π G^{b_i} B_i⟩` is continuous. -/
private lemma LF2_resProd_cont {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} (b : Fin p → Bool)
    (B : Fin p → Matrix ι ι ℂ) :
    Continuous fun G : Matrix ι ι ℂ => ntr (resProd (fun _ => G) b B) := by
  have hntr : Continuous fun M : Matrix ι ι ℂ => ntr M := by
    unfold ntr
    exact continuous_const.mul (continuous_id.matrix_trace)
  refine hntr.comp ?_
  unfold resProd
  simp only [List.ofFn_eq_map]
  refine continuous_list_prod _ fun i _ => ?_
  cases b i
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact continuous_id.matrix_mul continuous_const
  · simp only [↓reduceIte]
    exact continuous_id.matrix_conjTranspose.matrix_mul continuous_const

/-- The good event at one time is a measurable set of arrays. -/
private lemma LF2_good_meas {D N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' s : ℝ) :
    MeasurableSet {H : Idx D N → Idx D N → ℂ | flowGoodAt A z τ' s H} := by
  have hG := LF2_res_meas (D := D) (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
    (charFlowZ (lam D N A) z s)
  have hntr : Continuous fun M : Matrix (Idx D N) (Idx D N) ℂ => ntr M := by
    unfold ntr
    exact continuous_const.mul (continuous_id.matrix_trace)
  unfold flowGoodAt
  rw [Set.ofPred_and, Set.ofPred_and]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun a => measurableSet_le ?_ measurable_const
    have : Continuous fun G : Matrix (Idx D N) (Idx D N) ℂ =>
        ‖ntr ((G - MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) * Ea D N a)‖ :=
      (hntr.comp ((continuous_id.sub continuous_const).matrix_mul continuous_const)).norm
    exact this.measurable.comp hG
  · simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun b => MeasurableSet.iInter fun a =>
        measurableSet_le ?_ measurable_const
    exact (LF2_resProd_cont b _).norm.measurable.comp hG
  · simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    exact measurableSet_le (by fun_prop) measurable_const

/-- The Hermitian arrays form a measurable set. -/
private lemma LF2_herm_meas {ι : Type*} [Fintype ι] :
    MeasurableSet {H : ι → ι → ℂ | (Matrix.of H).IsHermitian} := by
  have : {H : ι → ι → ℂ | (Matrix.of H).IsHermitian} = ⋂ i, ⋂ j, {H | star (H j i) = H i j} := by
    ext H
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Matrix.IsHermitian.ext_iff, Matrix.of_apply]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  have h1 : Continuous fun H : ι → ι → ℂ => star (H j i) := by fun_prop
  have h2 : Continuous fun H : ι → ι → ℂ => H i j := by fun_prop
  exact measurableSet_eq_fun h1.measurable h2.measurable

/-- Grid time `j ≤ K` is bad when the state there is not Hermitian or not in the good event. -/
private def LF2_bad {D N K : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' h : ℝ)
    (ω : GridΩA D N K) (j : ℕ) : Prop :=
  j ≤ K ∧ ¬ ((Matrix.of (gridStateA D N K h ω j)).IsHermitian ∧
    flowGoodAt A z τ' (j * h) (gridStateA D N K h ω j))

/-- The first bad grid time, `⊤` if there is none. -/
private def LF2_sig {D N K : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' h : ℝ)
    (ω : GridΩA D N K) : WithTop ℕ :=
  if hex : ∃ j, LF2_bad A z τ' h ω j then ((Nat.find hex : ℕ) : WithTop ℕ) else ⊤

/-- `k < σ` iff no grid time `j ≤ k` is bad. -/
private lemma LF2_sig_lt {D N K : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' h : ℝ)
    (ω : GridΩA D N K) (k : ℕ) :
    (k : WithTop ℕ) < LF2_sig A z τ' h ω ↔ ∀ j, j ≤ k → ¬ LF2_bad A z τ' h ω j := by
  unfold LF2_sig
  split_ifs with hex
  · rw [show ((k : ℕ) : WithTop ℕ) < ((Nat.find hex : ℕ) : WithTop ℕ) ↔ k < Nat.find hex by
      norm_cast, Nat.lt_find_iff]
  · push Not at hex
    refine ⟨fun _ j _ => hex j, fun _ => ?_⟩
    rw [Nat.cast_withTop]
    exact WithTop.coe_lt_top k

/-- The first bad grid time is a stopping time. -/
private lemma LF2_sig_stop (D N K : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' h : ℝ) :
    IsStoppingTime (gridFiltrationA D N K) (LF2_sig (D := D) (N := N) (K := K) A z τ' h) := by
  intro i
  have e : {ω : GridΩA D N K | LF2_sig A z τ' h ω ≤ WithTop.some i} =
      ⋃ j ∈ Finset.range (i + 1), {ω | LF2_bad A z τ' h ω j} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    rw [← not_lt, ← Nat.cast_withTop, LF2_sig_lt]
    push Not
    exact ⟨fun ⟨j, hj, hb⟩ => ⟨j, by omega, hb⟩, fun ⟨j, hj, hb⟩ => ⟨j, by omega, hb⟩⟩
  rw [e]
  refine Finset.measurableSet_biUnion _ fun j hj => ?_
  have hji : j ≤ i := by have := Finset.mem_range.1 hj; omega
  have hP : MeasurableSet {H : Idx D N → Idx D N → ℂ |
      (Matrix.of H).IsHermitian ∧ flowGoodAt A z τ' (j * h) H} :=
    LF2_herm_meas.inter (LF2_good_meas A z τ' (j * h))
  have hm : Measurable[gridFiltrA D N K j] fun ω : GridΩA D N K => gridStateA D N K h ω j :=
    gridStateA_adapted D N K h j
  by_cases hjK : j ≤ K
  · have e2 : {ω : GridΩA D N K | LF2_bad A z τ' h ω j} =
        (fun ω => gridStateA D N K h ω j) ⁻¹' {H : Idx D N → Idx D N → ℂ |
          (Matrix.of H).IsHermitian ∧ flowGoodAt A z τ' (j * h) H}ᶜ := by
      ext ω
      simp [LF2_bad, hjK]
    rw [e2]
    exact (gridFiltrA_mono D N K).1 hji _ (hm hP.compl)
  · have e2 : {ω : GridΩA D N K | LF2_bad A z τ' h ω j} = ∅ := by
      ext ω
      simp [LF2_bad, hjK]
    rw [e2]
    exact @MeasurableSet.empty _ ((gridFiltrationA D N K) i)

/-! ### The quadratic variation on the good event: (3.56) [eq:quad_var], (3.57)
[eq:quad_integrand] -/

/-- `(G^b)^* = G^{¬b}`. -/
private lemma LF2_pw_conj {ι : Type*} (G : Matrix ι ι ℂ) (b : Bool) :
    (LF2_pw G b)ᴴ = LF2_pw G (!b) := by
  cases b <;> simp [LF2_pw]

/-- The Hermitian part of an array is Hermitian. -/
private lemma LF2_hermPart_herm {ι : Type*} (H : ι → ι → ℂ) :
    (Matrix.of (hermPart H)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [Matrix.of_apply, hermPart, star_div₀, star_add, star_star, star_ofNat]
  ring

/-- The grid states of a Hermitian start are Hermitian. -/
private lemma LF2_states_herm (D N K : ℕ) (h : ℝ) (ω : GridΩA D N K)
    (hω : (Matrix.of ω.1).IsHermitian) (k : ℕ) :
    (Matrix.of (gridStateA D N K h ω k)).IsHermitian := by
  induction k with
  | zero => exact hω
  | succ k ih =>
    by_cases hk : k < K
    · have e : gridStateA D N K h ω (k + 1) = Real.exp (-h / 2) • gridStateA D N K h ω k +
          Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N (ω.2 ⟨k, hk⟩)) := by
        simp [gridStateA, hk]
      rw [e]
      exact LF2_state_herm _ _ _ ih _
    · have e : gridStateA D N K h ω (k + 1) = Real.exp (-h / 2) • gridStateA D N K h ω k := by
        simp [gridStateA, hk]
      rw [e]
      have : Matrix.of (Real.exp (-h / 2) • gridStateA D N K h ω k) =
          ((Real.exp (-h / 2) : ℝ) : ℂ) • Matrix.of (gridStateA D N K h ω k) := by
        ext i j; simp [Complex.real_smul]
      rw [this]
      exact LF2_herm_smul _ ih _

/-! ### The second-order part of one step -/

/-- A continuous function with `‖φ x‖ ≤ a + b ‖x‖²` is integrable under the GUE blocks. -/
private lemma LF2_int_of_le {D N : ℕ} {W : Type*} [NormedAddCommGroup W]
    (φ : (Fin D → Coords N) → W) (hφ : Continuous φ) (a b : ℝ)
    (hb : ∀ x, ‖φ x‖ ≤ a + b * ‖x‖ ^ 2) : Integrable φ (gueBlocks D N) :=
  Integrable.mono' ((integrable_const a).add ((LF2_int_pow D N 2).const_mul b))
    hφ.aestronglyMeasurable (ae_of_all _ hb)

/-- The second-order part of one step of the flow: for `‖H‖ ≤ 1`, `0 < h ≤ 1`, `s = √(1 - e^{-h})`,
`Y(x) = e^{-h/2} H + s X(x)`, `f` with `‖Df‖, ‖D²f‖ ≤ B` and `f' - f` that is `B h`-Lipschitz:
`|f'(Y(x)) - E f'(Y) - s Df(H)[X(x)]| ≤ B h (2 + 2 E‖X‖² + E‖X‖ + 2 ‖x‖² + ‖x‖)`. -/
private lemma LF2_second {D N : ℕ} (f f' : (Idx D N → Idx D N → ℂ) → ℂ) (B h Mf : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hf : ContDiff ℝ 2 f) (hf'c : Continuous f')
    (hB1 : ∀ v, ‖fderiv ℝ f v‖ ≤ B) (hB2 : ∀ v, ‖iteratedFDeriv ℝ 2 f v‖ ≤ B)
    (hMf : ∀ v, ‖f v‖ ≤ Mf) (hMf' : ∀ v, ‖f' v‖ ≤ Mf)
    (hg : ∀ Y₁ Y₂, ‖(f' Y₁ - f Y₁) - (f' Y₂ - f Y₂)‖ ≤ B * ‖Y₁ - Y₂‖ * h)
    (H : Idx D N → Idx D N → ℂ) (hH : ‖H‖ ≤ 1) (x : Fin D → Coords N) :
    ‖f' (Real.exp (-h / 2) • H + Real.sqrt (1 - Real.exp (-h)) • LF2_arrL D N x) -
        (∫ x', f' (Real.exp (-h / 2) • H + Real.sqrt (1 - Real.exp (-h)) • LF2_arrL D N x')
          ∂(gueBlocks D N)) -
        (Real.sqrt (1 - Real.exp (-h)) : ℂ) * fderiv ℝ f H (LF2_arrL D N x)‖ ≤
      B * h * (2 + 2 * (∫ x', ‖x'‖ ^ 2 ∂(gueBlocks D N)) + (∫ x', ‖x'‖ ∂(gueBlocks D N)) +
        2 * ‖x‖ ^ 2 + ‖x‖) := by
  set γ := gueBlocks D N with hγ
  set ρ := Real.exp (-h / 2) with hρ
  set s := Real.sqrt (1 - Real.exp (-h)) with hs
  set arr := LF2_arrL D N with harr
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB1 H)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 ≤ h := by
    have he : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [hs, Real.sq_sqrt (by linarith)]
    linarith [Real.add_one_le_exp (-h)]
  have hs1 : s ≤ 1 := by
    rw [hs]; refine Real.sqrt_le_one.mpr ?_; linarith [Real.exp_pos (-h)]
  have hρ1 : |ρ - 1| ≤ h / 2 := by
    have he : Real.exp (-h / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [hρ, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith [Real.add_one_le_exp (-h / 2)]
  have harrn : ∀ w, ‖arr w‖ ≤ ‖w‖ := fun w => LF2_arr_norm_le D N w
  set Y : (Fin D → Coords N) → Idx D N → Idx D N → ℂ := fun w => ρ • H + s • arr w with hY
  have hYc : Continuous Y := continuous_const.add (arr.continuous.const_smul s)
  have hYH : ∀ w, Y w - H = (ρ - 1) • H + s • arr w := fun w => by
    simp only [hY, sub_smul, one_smul]; abel
  have hYHn : ∀ w, ‖Y w - H‖ ^ 2 ≤ h * (1 + 2 * ‖w‖ ^ 2) := by
    intro w
    rw [hYH]
    have h1 : ‖(ρ - 1) • H + s • arr w‖ ≤ h / 2 + s * ‖w‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        calc |ρ - 1| * ‖H‖ ≤ h / 2 * 1 := mul_le_mul hρ1 hH (norm_nonneg _) (by linarith)
          _ = h / 2 := mul_one _
      · rw [norm_smul, Real.norm_of_nonneg hs0]
        exact mul_le_mul_of_nonneg_left (harrn w) hs0
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (h / 2 + s * ‖w‖) ^ 2 ≤ 2 * ((h / 2) ^ 2 + s ^ 2 * ‖w‖ ^ 2) := by
      nlinarith [sq_nonneg (h / 2 - s * ‖w‖)]
    have h4 : s ^ 2 * ‖w‖ ^ 2 ≤ h * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hs2 (sq_nonneg _)
    nlinarith
  -- the Taylor remainder and the time difference
  set T : (Fin D → Coords N) → ℂ := fun w => f (Y w) - f H - fderiv ℝ f H (Y w - H) with hT
  have hTb : ∀ w, ‖T w‖ ≤ B * h * (1 + 2 * ‖w‖ ^ 2) := by
    intro w
    have := LF2_taylor1 f hf B hB2 H (Y w - H)
    rw [add_sub_cancel] at this
    calc ‖T w‖ ≤ B * ‖Y w - H‖ ^ 2 := this
      _ ≤ B * (h * (1 + 2 * ‖w‖ ^ 2)) := mul_le_mul_of_nonneg_left (hYHn w) hB0
      _ = _ := by ring
  set G : (Fin D → Coords N) → ℂ := fun w => f' (Y w) - f (Y w) with hG
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous fun w => fderiv ℝ f H (arr w) :=
    (fderiv ℝ f H).continuous.comp arr.continuous
  have hTc : Continuous T :=
    ((hfc.comp hYc).sub continuous_const).sub ((fderiv ℝ f H).continuous.comp
      (hYc.sub continuous_const))
  have hGc : Continuous G := (hf'c.comp hYc).sub (hfc.comp hYc)
  have hTi : Integrable T γ := LF2_int_of_le T hTc (B * h) (B * h * 2) fun w => by
    have := hTb w; nlinarith
  have hGi : Integrable G γ := LF2_int_of_le G hGc (2 * Mf) 0 fun w => by
    have h1 := hMf' (Y w); have h2 := hMf (Y w)
    simp only [zero_mul, add_zero]
    exact (norm_sub_le _ _).trans (by linarith)
  have hdfi : Integrable (fun w => fderiv ℝ f H (arr w)) γ :=
    LF2_int_of_le _ hdfc (B) B fun w => by
      have h1 : ‖fderiv ℝ f H (arr w)‖ ≤ B * ‖w‖ :=
        ((fderiv ℝ f H).le_opNorm _).trans (mul_le_mul (hB1 H) (harrn w) (norm_nonneg _) hB0)
      nlinarith [sq_nonneg (‖w‖ - 1)]
  have hmean : ∫ w, fderiv ℝ f H (arr w) ∂γ = 0 :=
    LF2_gueBlocks_odd D N _ fun w => by simp [map_neg]
  have hpt : ∀ w, f' (Y w) = T w + G w + (f H + fderiv ℝ f H ((ρ - 1) • H)) +
      (s : ℂ) * fderiv ℝ f H (arr w) := by
    intro w
    simp only [hT, hG, hYH, map_add, map_smul, Complex.real_smul]
    ring
  have hint : ∫ w, f' (Y w) ∂γ = (∫ w, T w ∂γ) + (∫ w, G w ∂γ) +
      (f H + fderiv ℝ f H ((ρ - 1) • H)) := by
    have i1 : Integrable (fun w => T w + G w) γ := hTi.add hGi
    have i2 : Integrable (fun w => T w + G w + (f H + fderiv ℝ f H ((ρ - 1) • H))) γ :=
      i1.add (integrable_const _)
    have i3 : Integrable (fun w => (s : ℂ) * fderiv ℝ f H (arr w)) γ := hdfi.const_mul _
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add i2 i3,
      integral_add i1 (integrable_const _), integral_add hTi hGi, integral_const_mul, hmean]
    simp
  -- the identity and the bound
  have key : f' (Y x) - ∫ w, f' (Y w) ∂γ - (s : ℂ) * fderiv ℝ f H (arr x) =
      (T x - ∫ w, T w ∂γ) + ∫ w, (G x - G w) ∂γ := by
    rw [hint, integral_sub (integrable_const _) hGi, hpt x]
    simp
    ring
  have hM1 : Integrable (fun w : Fin D → Coords N => ‖w‖) γ := by
    have := LF2_int_pow D N 1; simp only [pow_one] at this; exact this
  have hM2 := LF2_int_pow D N 2
  rw [key]
  have b1 : ‖T x - ∫ w, T w ∂γ‖ ≤ B * h * (1 + 2 * ‖x‖ ^ 2) +
      B * h * (1 + 2 * ∫ w, ‖w‖ ^ 2 ∂γ) := by
    refine (norm_sub_le _ _).trans (add_le_add (hTb x) ?_)
    have hgi : Integrable (fun w : Fin D → Coords N => B * h * (1 + 2 * ‖w‖ ^ 2)) γ :=
      ((integrable_const 1).add (hM2.const_mul 2)).const_mul (B * h)
    refine (norm_integral_le_of_norm_le hgi (ae_of_all _ hTb)).trans (le_of_eq ?_)
    have hi2 : Integrable (fun w : Fin D → Coords N => 2 * ‖w‖ ^ 2) γ := hM2.const_mul 2
    rw [integral_const_mul, integral_add (integrable_const 1) hi2, integral_const_mul]
    simp
  have b2 : ‖∫ w, (G x - G w) ∂γ‖ ≤ B * h * (‖x‖ + ∫ w, ‖w‖ ∂γ) := by
    have hle : ∀ w, ‖G x - G w‖ ≤ B * h * (‖x‖ + ‖w‖) := by
      intro w
      refine (hg (Y x) (Y w)).trans ?_
      have h1 : ‖Y x - Y w‖ ≤ ‖x‖ + ‖w‖ := by
        have e : Y x - Y w = s • (arr x - arr w) := by simp only [hY, smul_sub]; abel
        rw [e, norm_smul, Real.norm_of_nonneg hs0, ← map_sub]
        calc s * ‖arr (x - w)‖ ≤ 1 * ‖x - w‖ :=
              mul_le_mul hs1 (harrn _) (norm_nonneg _) zero_le_one
          _ ≤ ‖x‖ + ‖w‖ := by rw [one_mul]; exact norm_sub_le _ _
      calc B * ‖Y x - Y w‖ * h ≤ B * (‖x‖ + ‖w‖) * h := by gcongr
        _ = _ := by ring
    have hgi : Integrable (fun w : Fin D → Coords N => B * h * (‖x‖ + ‖w‖)) γ :=
      ((integrable_const ‖x‖).add hM1).const_mul (B * h)
    refine (norm_integral_le_of_norm_le hgi (ae_of_all _ hle)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add (integrable_const _) hM1]
    simp
  calc ‖(T x - ∫ w, T w ∂γ) + ∫ w, (G x - G w) ∂γ‖
      ≤ ‖T x - ∫ w, T w ∂γ‖ + ‖∫ w, (G x - G w) ∂γ‖ := norm_add_le _ _
    _ ≤ B * h * (1 + 2 * ‖x‖ ^ 2) + B * h * (1 + 2 * ∫ w, ‖w‖ ^ 2 ∂γ) +
        B * h * (‖x‖ + ∫ w, ‖w‖ ∂γ) := add_le_add b1 b2
    _ = _ := by ring

/-- `{k < σ}` is `𝓕_k`-measurable. -/
private lemma LF2_sig_lt_meas (D N K : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' h : ℝ)
    (k : ℕ) :
    MeasurableSet[gridFiltrA D N K k]
      {ω : GridΩA D N K | (k : WithTop ℕ) < LF2_sig A z τ' h ω} := by
  have e : {ω : GridΩA D N K | (k : WithTop ℕ) < LF2_sig A z τ' h ω} =
      ⋂ j ∈ Finset.range (k + 1), {ω | LF2_bad A z τ' h ω j}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff,
      LF2_sig_lt]
    exact ⟨fun h1 j hj => h1 j (by omega), fun h1 j hj => h1 j (by omega)⟩
  rw [e]
  refine Finset.measurableSet_biInter _ fun j hj => ?_
  have hjk : j ≤ k := by have := Finset.mem_range.1 hj; omega
  refine MeasurableSet.compl ?_
  have hP : MeasurableSet {H : Idx D N → Idx D N → ℂ |
      (Matrix.of H).IsHermitian ∧ flowGoodAt A z τ' (j * h) H} :=
    LF2_herm_meas.inter (LF2_good_meas A z τ' (j * h))
  by_cases hjK : j ≤ K
  · have e2 : {ω : GridΩA D N K | LF2_bad A z τ' h ω j} =
        (fun ω => gridStateA D N K h ω j) ⁻¹' {H : Idx D N → Idx D N → ℂ |
          (Matrix.of H).IsHermitian ∧ flowGoodAt A z τ' (j * h) H}ᶜ := by
      ext ω
      simp [LF2_bad, hjK]
    rw [e2]
    exact (gridFiltrA_mono D N K).1 hjk _ (gridStateA_adapted D N K h j hP.compl)
  · have e2 : {ω : GridΩA D N K | LF2_bad A z τ' h ω j} = ∅ := by
      ext ω
      simp [LF2_bad, hjK]
    rw [e2]
    exact @MeasurableSet.empty _ (gridFiltrA D N K k)

/-- `ℓ(c w) = c ℓ(w)` for a real-linear `ℓ` and real `c`. -/
private lemma LF2_ell_mul (ℓ : ℂ →L[ℝ] ℝ) (c : ℝ) (w : ℂ) : ℓ ((c : ℂ) * w) = c * ℓ w := by
  rw [← Complex.real_smul, map_smul, smul_eq_mul]

/-! ### The quadratic variation on the good event: eight-resolvent loops -/

/-- The eight-resolvent word as `resProd`. -/
private lemma LF2_word8 {D N : ℕ} (G : Matrix (Idx D N) (Idx D N) ℂ) (c : Fin 8 → Bool)
    (a : Fin 8 → Fin D) :
    LF2_pw G (c 0) * Ea D N (a 0) * LF2_pw G (c 1) * Ea D N (a 1) * LF2_pw G (c 2) *
        Ea D N (a 2) * LF2_pw G (c 3) * Ea D N (a 3) * LF2_pw G (c 4) * Ea D N (a 4) *
        LF2_pw G (c 5) * Ea D N (a 5) * LF2_pw G (c 6) * Ea D N (a 6) * LF2_pw G (c 7) *
        Ea D N (a 7) =
      resProd (fun _ : Fin 8 => G) c (fun i => Ea D N (a i)) := by
  simp only [resProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.mul_one, Matrix.mul_assoc, LF2_pw]
  rfl

/-- One cut-open three-loop `G^u E_p G^v E_r G^t E_s G^u`. -/
private abbrev LF2_Wsh {D N : ℕ} (G : Matrix (Idx D N) (Idx D N) ℂ) (u v t : Bool)
    (p r s : Fin D) : Matrix (Idx D N) (Idx D N) ℂ :=
  LF2_pw G u * Ea D N p * LF2_pw G v * Ea D N r * LF2_pw G t * Ea D N s * LF2_pw G u

/-- `(G^u E_p G^v E_r G^t E_s G^u)^* = G^{¬u} E_s G^{¬t} E_r G^{¬v} E_p G^{¬u}`. -/
private lemma LF2_Wsh_conj {D N : ℕ} (G : Matrix (Idx D N) (Idx D N) ℂ) (u v t : Bool)
    (p r s : Fin D) : (LF2_Wsh G u v t p r s)ᴴ = LF2_Wsh G (!u) (!t) (!v) s r p := by
  simp only [LF2_Wsh, Matrix.conjTranspose_mul, LF2_Ea_conj, LF2_pw_conj, Matrix.mul_assoc]

/-- `‖(a₁ + a₂ + a₃) + (a₄ + a₅ + a₆) + (a₇ + a₈ + a₉)‖ ≤ 9 β` when every `‖a_i‖ ≤ β`. -/
private lemma LF2_norm9 (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : ℂ) (β : ℝ) (h₁ : ‖a₁‖ ≤ β) (h₂ : ‖a₂‖ ≤ β)
    (h₃ : ‖a₃‖ ≤ β) (h₄ : ‖a₄‖ ≤ β) (h₅ : ‖a₅‖ ≤ β) (h₆ : ‖a₆‖ ≤ β) (h₇ : ‖a₇‖ ≤ β)
    (h₈ : ‖a₈‖ ≤ β) (h₉ : ‖a₉‖ ≤ β) :
    ‖(a₁ + a₂ + a₃) + (a₄ + a₅ + a₆) + (a₇ + a₈ + a₉)‖ ≤ 9 * β := by
  have t1 := norm_add₃_le (a := a₁ + a₂ + a₃) (b := a₄ + a₅ + a₆) (c := a₇ + a₈ + a₉)
  have t2 := norm_add₃_le (a := a₁) (b := a₂) (c := a₃)
  have t3 := norm_add₃_le (a := a₄) (b := a₅) (c := a₆)
  have t4 := norm_add₃_le (a := a₇) (b := a₈) (c := a₉)
  linarith

/-- The eight-resolvent loops of the quadratic variation: for `W = Σ_{r ≤ 3} W_r` with the three
cut-open loops `W_r` of `⟨G₁ E_x G₂ E_y G₃ E_w⟩`, `|⟨W E_a W^* E_a⟩|` is at most nine times a bound
on the words of eight resolvents. -/
private lemma LF2_quad_abs {D N : ℕ} (G : Matrix (Idx D N) (Idx D N) ℂ) (b₁ b₂ b₃ : Bool)
    (x y w a : Fin D) (β : ℝ)
    (hβ : ∀ (c : Fin 8 → Bool) (e : Fin 8 → Fin D),
      ‖ntr (resProd (fun _ : Fin 8 => G) c (fun i => Ea D N (e i)))‖ ≤ β) :
    ‖ntr ((LF2_Wsh G b₁ b₂ b₃ x y w + LF2_Wsh G b₂ b₃ b₁ y w x + LF2_Wsh G b₃ b₁ b₂ w x y) *
      Ea D N a * (LF2_Wsh G b₁ b₂ b₃ x y w + LF2_Wsh G b₂ b₃ b₁ y w x +
        LF2_Wsh G b₃ b₁ b₂ w x y)ᴴ * Ea D N a)‖ ≤ 9 * β := by
  have hw : ∀ (u v t u' v' t' : Bool) (p r s p' r' s' : Fin D),
      ‖ntr (LF2_Wsh G u v t p r s * Ea D N a * LF2_Wsh G u' v' t' p' r' s' * Ea D N a)‖ ≤ β := by
    intro u v t u' v' t' p r s p' r' s'
    have h1 := hβ ![u, v, t, u, u', v', t', u'] ![p, r, s, a, p', r', s', a]
    rw [← LF2_word8] at h1
    have e : LF2_Wsh G u v t p r s * Ea D N a * LF2_Wsh G u' v' t' p' r' s' * Ea D N a =
        LF2_pw G u * Ea D N p * LF2_pw G v * Ea D N r * LF2_pw G t * Ea D N s * LF2_pw G u *
          Ea D N a * LF2_pw G u' * Ea D N p' * LF2_pw G v' * Ea D N r' * LF2_pw G t' *
          Ea D N s' * LF2_pw G u' * Ea D N a := by
      simp only [LF2_Wsh, Matrix.mul_assoc]
    rw [e]
    exact h1
  have hb : ∀ (u v t u' v' t' : Bool) (p r s p' r' s' : Fin D),
      ‖ntr (LF2_Wsh G u v t p r s * Ea D N a * (LF2_Wsh G u' v' t' p' r' s')ᴴ * Ea D N a)‖ ≤ β := by
    intro u v t u' v' t' p r s p' r' s'
    rw [LF2_Wsh_conj]
    exact hw _ _ _ _ _ _ _ _ _ _ _ _
  have hadd : ∀ M₁ M₂ : Matrix (Idx D N) (Idx D N) ℂ, ntr (M₁ + M₂) = ntr M₁ + ntr M₂ := by
    intro M₁ M₂; simp [ntr, Matrix.trace_add, mul_add]
  have hexp : ∀ W₁ W₂ W₃ : Matrix (Idx D N) (Idx D N) ℂ,
      (W₁ + W₂ + W₃) * Ea D N a * (W₁ + W₂ + W₃)ᴴ * Ea D N a =
      ((W₁ * Ea D N a * W₁ᴴ * Ea D N a + W₁ * Ea D N a * W₂ᴴ * Ea D N a +
        W₁ * Ea D N a * W₃ᴴ * Ea D N a) +
      (W₂ * Ea D N a * W₁ᴴ * Ea D N a + W₂ * Ea D N a * W₂ᴴ * Ea D N a +
        W₂ * Ea D N a * W₃ᴴ * Ea D N a)) +
      (W₃ * Ea D N a * W₁ᴴ * Ea D N a + W₃ * Ea D N a * W₂ᴴ * Ea D N a +
        W₃ * Ea D N a * W₃ᴴ * Ea D N a) := by
    intro W₁ W₂ W₃
    simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  rw [hexp]
  simp only [hadd]
  exact LF2_norm9 _ _ _ _ _ _ _ _ _ β (hb _ _ _ _ _ _ _ _ _ _ _ _) (hb _ _ _ _ _ _ _ _ _ _ _ _)
    (hb _ _ _ _ _ _ _ _ _ _ _ _) (hb _ _ _ _ _ _ _ _ _ _ _ _) (hb _ _ _ _ _ _ _ _ _ _ _ _)
    (hb _ _ _ _ _ _ _ _ _ _ _ _) (hb _ _ _ _ _ _ _ _ _ _ _ _) (hb _ _ _ _ _ _ _ _ _ _ _ _)
    (hb _ _ _ _ _ _ _ _ _ _ _ _)

/-- `|⟨E_w G₁ E_x G₂ E_y G₃⟩| ≤ η_r⁻³` at every array, on `[0, S]`. -/
private lemma LF2_f_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (r : ℝ) (hr : r < flowTc (lam D N A) z) (z₁ z₂ z₃ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (h₃ : z₃ = z ∨ z₃ = star z)
    (x y w : Fin D) (H : Idx D N → Idx D N → ℂ) :
    ‖flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x y w) r H‖ ≤
      ((charFlowZ (lam D N A) z r).im ^ 3)⁻¹ := by
  have h1 := LF2_Lten_le D N hD hN A z hz r hr (hermPart H) (LF2_hermPart_herm H) z₁ z₂ z₃ h₁ h₂
    h₃ x y w
  rw [LF2_Lten_loop, norm_mul, Complex.norm_natCast] at h1
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_eq_mul_inv] at h1
  exact le_of_mul_le_mul_left h1 hD0

/-- The cut-open loop `W` of `loop_quadVar` for a loop of three resolvents. -/
private lemma LF2_W3 {D N : ℕ} (H : Idx D N → Idx D N → ℂ)
    (f₀ f₁ f₂ : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ) :
    (∑ i : Fin [f₀, f₁, f₂].length,
      res (Matrix.of H + ([f₀, f₁, f₂].get i).2.1) ([f₀, f₁, f₂].get i).2.2 *
        chainB H ([f₀, f₁, f₂].rotate (i + 1))) =
      res (Matrix.of H + f₀.2.1) f₀.2.2 * chainB H [f₁, f₂, f₀] +
        res (Matrix.of H + f₁.2.1) f₁.2.2 * chainB H [f₂, f₀, f₁] +
        res (Matrix.of H + f₂.2.1) f₂.2.2 * chainB H [f₀, f₁, f₂] := by
  change ∑ i : Fin 3, _ = _
  rw [Fin.sum_univ_three]
  simp [List.rotate]

/-- The quadratic variation (3.56) [eq:quad_var] on the good event for three resolvents, with
(A.53) [entprodG] for eight resolvents:
`E_X |D⟨E_w G₁ E_x G₂ E_y G₃⟩[X]|² ≤ 9 N^{τ'} Im m_r / (N² η_r⁷)`. -/
private lemma LF2_var (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (r : ℝ) (hr : r < flowTc (lam D N A) z) (τ' : ℝ)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian)
    (hgood : flowGoodAt A z τ' r H) (z₁ z₂ z₃ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (h₃ : z₃ = z ∨ z₃ = star z) (x y w : Fin D) :
    ∫ v, ‖fderiv ℝ (flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x y w) r) H
        (Matrix.of.symm (blockH D N v))‖ ^ 2 ∂(gueBlocks D N) ≤
      9 * ((N : ℝ) ^ τ' * (flowIm (lam D N A) z r / (charFlowZ (lam D N A) z r).im ^ 7)) /
        (N : ℝ) ^ 2 := by
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hΛ := lam_isHermitian D N A
  set Λs := ((Real.exp (-r / 2) : ℝ) : ℂ) • lam D N A with hΛs
  have hΛsH : Λs.IsHermitian := LF2_herm_smul _ hΛ _
  have him : ∀ zi : ℂ, (zi = z ∨ zi = star z) → (charFlowZ (lam D N A) zi r).im ≠ 0 := by
    have hη := (charFlow_M _ hΛ z hz r hr).1
    rintro zi (rfl | rfl)
    · exact hη.ne'
    · rw [charFlowZ_conj _ z hz r]; simpa using hη.ne'
  have hl : ∀ f ∈ [(Ea D N w, Λs, charFlowZ (lam D N A) z₁ r),
      (Ea D N x, Λs, charFlowZ (lam D N A) z₂ r), (Ea D N y, Λs, charFlowZ (lam D N A) z₃ r)],
      f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact ⟨hΛsH, him z₁ h₁⟩
    · exact ⟨hΛsH, him z₂ h₂⟩
    · exact ⟨hΛsH, him z₃ h₃⟩
  have hq := loop_quadVar _ hl H hH
  simp only at hq
  have hfl : flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x y w) r = fun h => ntr (chainB (hermPart h)
      [(Ea D N w, Λs, charFlowZ (lam D N A) z₁ r), (Ea D N x, Λs, charFlowZ (lam D N A) z₂ r),
        (Ea D N y, Λs, charFlowZ (lam D N A) z₃ r)]) :=
    rfl
  rw [hfl, hq, LF2_W3]
  obtain ⟨b₁, hG₁, -⟩ := LF2_flag hD1 hN1 A z hz r hr H hH z₁ h₁
  obtain ⟨b₂, hG₂, -⟩ := LF2_flag hD1 hN1 A z hz r hr H hH z₂ h₂
  obtain ⟨b₃, hG₃, -⟩ := LF2_flag hD1 hN1 A z hz r hr H hH z₃ h₃
  set G := res (Matrix.of H + Λs) (charFlowZ (lam D N A) z r) with hG
  have hW : res (Matrix.of H + Λs) (charFlowZ (lam D N A) z₁ r) *
        chainB H [(Ea D N x, Λs, charFlowZ (lam D N A) z₂ r),
          (Ea D N y, Λs, charFlowZ (lam D N A) z₃ r), (Ea D N w, Λs, charFlowZ (lam D N A) z₁ r)] +
      res (Matrix.of H + Λs) (charFlowZ (lam D N A) z₂ r) *
        chainB H [(Ea D N y, Λs, charFlowZ (lam D N A) z₃ r),
          (Ea D N w, Λs, charFlowZ (lam D N A) z₁ r), (Ea D N x, Λs, charFlowZ (lam D N A) z₂ r)] +
      res (Matrix.of H + Λs) (charFlowZ (lam D N A) z₃ r) *
        chainB H [(Ea D N w, Λs, charFlowZ (lam D N A) z₁ r),
          (Ea D N x, Λs, charFlowZ (lam D N A) z₂ r), (Ea D N y, Λs, charFlowZ (lam D N A) z₃ r)] =
      LF2_Wsh G b₁ b₂ b₃ x y w + LF2_Wsh G b₂ b₃ b₁ y w x + LF2_Wsh G b₃ b₁ b₂ w x y := by
    simp only [chainB, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Matrix.mul_one]
    rw [hG₁, hG₂, hG₃]
    simp only [LF2_Wsh, Matrix.mul_assoc]
  rw [hW]
  have hβ : ∀ (c : Fin 8 → Bool) (e : Fin 8 → Fin D),
      ‖ntr (resProd (fun _ : Fin 8 => G) c (fun i => Ea D N (e i)))‖ ≤
        (N : ℝ) ^ τ' * (flowIm (lam D N A) z r / (charFlowZ (lam D N A) z r).im ^ 7) := by
    intro c e
    have h8 := hgood.2.1 8 (by norm_num) (by norm_num) c e
    rwa [LF2_bndA4 8 (by norm_num)] at h8
  have hterm : ∀ a : Fin D,
      (ntr ((LF2_Wsh G b₁ b₂ b₃ x y w + LF2_Wsh G b₂ b₃ b₁ y w x + LF2_Wsh G b₃ b₁ b₂ w x y) *
        Ea D N a * (LF2_Wsh G b₁ b₂ b₃ x y w + LF2_Wsh G b₂ b₃ b₁ y w x +
          LF2_Wsh G b₃ b₁ b₂ w x y)ᴴ * Ea D N a)).re ≤
      9 * ((N : ℝ) ^ τ' * (flowIm (lam D N A) z r / (charFlowZ (lam D N A) z r).im ^ 7)) :=
    fun a => (Complex.re_le_norm _).trans (LF2_quad_abs G b₁ b₂ b₃ x y w a _ hβ)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  calc ((D : ℝ) * N ^ 2)⁻¹ * ∑ a, (ntr (_ * Ea D N a * _ * Ea D N a)).re
      ≤ ((D : ℝ) * N ^ 2)⁻¹ * ∑ _a : Fin D,
          9 * ((N : ℝ) ^ τ' * (flowIm (lam D N A) z r / (charFlowZ (lam D N A) z r).im ^ 7)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hterm a) (by positivity)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- `(c s)² · 9 N^{t} ι / (N² η⁷) ≤ 9 D² h N^{t} / (N² q⁴ ι⁶)` for `c² ≤ q³ D²`, `s² ≤ h`,
`q ι ≤ η`. -/
private lemma LF2_ar_var (c s q ι η D h N t : ℝ) (hcq : c ^ 2 ≤ q ^ 3 * D ^ 2) (hs : s ^ 2 ≤ h)
    (hq : 0 < q) (hι : 0 < ι) (hN : 0 < N) (ht : 0 ≤ t) (hqι : q * ι ≤ η) :
    (c * s) ^ 2 * (9 * (t * (ι / η ^ 7)) / N ^ 2) ≤
      9 * D ^ 2 * h * t / (N ^ 2 * q ^ 4 * ι ^ 6) := by
  have hη : 0 < η := lt_of_lt_of_le (mul_pos hq hι) hqι
  have h1 : (c * s) ^ 2 ≤ q ^ 3 * D ^ 2 * h := by
    rw [mul_pow]
    exact mul_le_mul hcq hs (sq_nonneg s) (by positivity)
  have h2 : ι / η ^ 7 ≤ ι / (q * ι) ^ 7 :=
    div_le_div_of_nonneg_left hι.le (pow_pos (mul_pos hq hι) 7)
      (pow_le_pow_left₀ (mul_pos hq hι).le hqι 7)
  have h3 : 0 ≤ 9 * (t * (ι / η ^ 7)) / N ^ 2 := by positivity
  calc (c * s) ^ 2 * (9 * (t * (ι / η ^ 7)) / N ^ 2)
      ≤ q ^ 3 * D ^ 2 * h * (9 * (t * (ι / (q * ι) ^ 7)) / N ^ 2) := by
        refine mul_le_mul h1 ?_ h3 (le_trans (sq_nonneg _) h1)
        gcongr
    _ = 9 * D ^ 2 * h * t / (N ^ 2 * q ^ 4 * ι ^ 6) := by
        field_simp

set_option maxHeartbeats 1600000 in
-- The proof assembles the Azuma and Doob parts of one component in a single declaration.
/-- One real component of the martingale part for three resolvents on the grid: outside a set of
probability at most `2K e^{-ℓ²/2} + K v / ε²`, for every Hermitian start and every `n ≤ K` at which
the good event has held before `n`, the real part (or the imaginary part) of the `(x₁, x₂, x₃)`
entry of `Σ_{j<n} q_{j+1}^{3/2} (L_{j+1} - E_j L_{j+1})`, `L = L_{(1,2,3)}`, is at most
`ℓ (Σ_{k<n} c_k)^{1/2} + ε` in absolute value; `c_k = 9 D² h N^{τ'} / (N² q_k⁴ (Im m_k)⁶)` from the
quadratic variation and `v` bounds the second moments of the second-order parts. -/
private lemma LF2_comp (D N K : ℕ) [NeZero D] [NeZero N] (hK : 1 ≤ K)
    (μ₀ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ₀]
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ) (hA : opNorm (lam D N A) ≤ 1 / 10)
    (hz : 0 < z.im) (hSpos : 0 < S) (hSt : S < flowTc (lam D N A) z)
    (hq1 : flowTc (lam D N A) z ≤ 1)
    (hηN : ∀ s, 0 ≤ s → s ≤ S → (N : ℝ)⁻¹ < (charFlowZ (lam D N A) z s).im) (τ' : ℝ)
    (z₁ z₂ z₃ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z)
    (h₃ : z₃ = z ∨ z₃ = star z) (x₁ x₂ x₃ : Fin D)
    (ℓ : ℂ →L[ℝ] ℝ) (hℓ : ∀ w, |ℓ w| ≤ ‖w‖) (Ft : ℝ → (Idx D N → Idx D N → ℂ) → ℂ) (B : ℝ)
    (hder : ∀ s ∈ Set.Icc 0 S, ∀ v, HasDerivWithinAt
      (fun r => flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x₁ x₂ x₃) r v) (Ft s v) (Set.Icc 0 S) s)
    (hreg : ∀ s ∈ Set.Icc 0 S, ContDiff ℝ 4 (flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x₁ x₂ x₃) s) ∧
      ContDiff ℝ 4 (Ft s) ∧ (∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ v,
        ‖iteratedFDeriv ℝ j (flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x₁ x₂ x₃) s) v‖ ≤ B ∧
          ‖iteratedFDeriv ℝ j (Ft s) v‖ ≤ B))
    (lv ε : ℝ) (hlv : 0 < lv) (hε : 0 < ε) :
    ∃ Bad : Set (GridΩA D N K),
      (gridLawA D N K μ₀).real Bad ≤ 2 * K * Real.exp (-lv ^ 2 / 2) +
        K * ((D * B * (S / K)) ^ 2 * (2 * ((3 + 2 * (∫ w, ‖w‖ ^ 2 ∂(gueBlocks D N)) +
          ∫ w, ‖w‖ ∂(gueBlocks D N)) ^ 2 + 9 * ∫ w, ‖w‖ ^ 4 ∂(gueBlocks D N)))) / ε ^ 2 ∧
      ∀ ω ∉ Bad, (Matrix.of ω.1).IsHermitian → ∀ n : ℕ, n ≤ K →
        (∀ j : ℕ, j < n →
          flowGoodAt A z τ' (j * (S / K)) (gridStateA D N K (S / K) ω j)) →
        |∑ j ∈ Finset.range n,
          ℓ ((((flowTc (lam D N A) z - (j + 1) * (S / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          (flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) x₁ x₂ x₃ -
            ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x₁ x₂ x₃
              ∂(gueBlocks D N)))| ≤
          lv * Real.sqrt (∑ k ∈ Finset.range n,
            (if k < K then 9 * D ^ 2 * (S / K) * (N : ℝ) ^ τ' /
              ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - k * (S / K)) ^ 4 *
                flowIm (lam D N A) z (k * (S / K)) ^ 6) else 1)) + ε := by
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  set μ := gridLawA D N K μ₀ with hμ
  set γ := gueBlocks D N with hγ
  set h := S / K with hhdef
  have hh : 0 < h := div_pos hSpos hKpos
  have hKh : (K : ℝ) * h = S := by rw [hhdef]; field_simp
  have hhS : h ≤ S := by
    rw [hhdef, div_le_iff₀ hKpos]
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have hh1 : h ≤ 1 := by linarith
  set q₀ := flowTc (lam D N A) z with hq₀
  set ρ := Real.exp (-h / 2) with hρ
  set s := Real.sqrt (1 - Real.exp (-h)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 ≤ h := by
    have he : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [hs, Real.sq_sqrt (by linarith)]
    linarith [Real.add_one_le_exp (-h)]
  have hs1 : s ≤ 1 := by
    rw [hs]; refine Real.sqrt_le_one.mpr ?_; linarith [Real.exp_pos (-h)]
  set F := flowLoop (lam D N A) (LF2_l z₁ z₂ z₃ x₁ x₂ x₃) with hF
  set arr := LF2_arrL D N with harr
  have harrn : ∀ w, ‖arr w‖ ≤ ‖w‖ := fun w => LF2_arr_norm_le D N w
  set M₁ := ∫ w, ‖w‖ ∂γ with hM₁
  set M₂ := ∫ w, ‖w‖ ^ 2 ∂γ with hM₂
  set M₄ := ∫ w, ‖w‖ ^ 4 ∂γ with hM₄
  have hM₁0 : 0 ≤ M₁ := integral_nonneg fun w => norm_nonneg _
  have hM₂0 : 0 ≤ M₂ := integral_nonneg fun w => by positivity
  have hM₄0 : 0 ≤ M₄ := integral_nonneg fun w => by positivity
  have hB0 : 0 ≤ B := (norm_nonneg _).trans ((hreg 0 ⟨le_rfl, hSpos.le⟩).2.2 1 le_rfl
    (by norm_num) 0).1
  -- grid times
  have hgrid : ∀ k : ℕ, k ≤ K → (k : ℝ) * h ∈ Set.Icc 0 S := fun k hk => by
    refine ⟨by positivity, ?_⟩
    rw [← hKh]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le
  have hgrid' : ∀ k : ℕ, k < K → ((k : ℝ) + 1) * h ∈ Set.Icc 0 S := fun k hk => by
    have := hgrid (k + 1) hk
    push_cast at this
    exact this
  -- regularity of the loops
  have hFr : ∀ r ∈ Set.Icc 0 S, ContDiff ℝ 4 (F r) ∧ (∀ v, ‖fderiv ℝ (F r) v‖ ≤ B) ∧
      (∀ v, ‖iteratedFDeriv ℝ 2 (F r) v‖ ≤ B) ∧ Differentiable ℝ (Ft r) ∧
      ∀ v, ‖fderiv ℝ (Ft r) v‖ ≤ B := by
    intro r hr
    obtain ⟨h1, h2, h3⟩ := hreg r hr
    refine ⟨h1, fun v => ?_, fun v => (h3 2 (by norm_num) (by norm_num) v).1,
      h2.differentiable (by norm_num), fun v => ?_⟩
    · rw [← norm_iteratedFDeriv_one]; exact (h3 1 le_rfl (by norm_num) v).1
    · rw [← norm_iteratedFDeriv_one]; exact (h3 1 le_rfl (by norm_num) v).2
  have hFb : ∀ r ∈ Set.Icc 0 S, ∀ v, ‖F r v‖ ≤ (N : ℝ) ^ 3 := by
    intro r hr v
    refine (LF2_f_le D N hD1 hN1 A z hz r (lt_of_le_of_lt hr.2 hSt) z₁ z₂ z₃ h₁ h₂ h₃ x₁ x₂ x₃
      v).trans ?_
    have hη := hηN r hr.1 hr.2
    have hηpos : 0 < (charFlowZ (lam D N A) z r).im := lt_trans (inv_pos.2 hNpos) hη
    rw [inv_le_comm₀ (pow_pos hηpos 3) (by positivity), ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hNpos.le) hη.le 3
  -- the weights `q_{k+1}^{3/2} D`
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun k : ℕ => (q₀ - ((k : ℝ) + 1) * h) ^ (3 / 2 : ℝ) * D :=
    ⟨_, rfl⟩
  have hc0 : ∀ k, k < K → 0 ≤ c k ∧ c k ≤ D ∧ c k ^ 2 ≤ (q₀ - k * h) ^ 3 * D ^ 2 := by
    intro k hk
    have h1 := (hgrid' k hk).2
    have hx0 : 0 ≤ q₀ - ((k : ℝ) + 1) * h := by linarith
    have hx1 : q₀ - ((k : ℝ) + 1) * h ≤ 1 := by
      have : 0 ≤ ((k : ℝ) + 1) * h := by positivity
      linarith
    have hp0 : 0 ≤ (q₀ - ((k : ℝ) + 1) * h) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx0 _
    rw [hc]
    refine ⟨mul_nonneg hp0 hD0, ?_, ?_⟩
    · have : (q₀ - ((k : ℝ) + 1) * h) ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hx0 hx1 (by norm_num)
      nlinarith
    · have e : ((q₀ - ((k : ℝ) + 1) * h) ^ (3 / 2 : ℝ)) ^ 2 = (q₀ - ((k : ℝ) + 1) * h) ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
      have h3 : (q₀ - ((k : ℝ) + 1) * h) ^ 3 ≤ (q₀ - k * h) ^ 3 :=
        pow_le_pow_left₀ hx0 (by nlinarith) 3
      rw [mul_pow, e]
      exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
  -- the one-step objects
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → (Idx D N → Idx D N → ℂ) → ℂ,
      Φ = fun (k : ℕ) H => ∫ w, F (((k : ℝ) + 1) * h) (ρ • H + s • arr w) ∂γ := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℕ → (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) → ℝ,
      Γ = fun (k : ℕ) p =>
        ℓ ((c k : ℂ) * (F (((k : ℝ) + 1) * h) (ρ • p.1 + s • arr p.2) - Φ k p.1)) -
        c k * s * ℓ (fderiv ℝ (F (k * h)) p.1 (arr p.2)) := ⟨_, rfl⟩
  set σ := LF2_sig (D := D) (N := N) (K := K) A z τ' h with hσ
  obtain ⟨a, ha⟩ : ∃ a : ℕ → GridΩA D N K → (Fin D → Coords N) →L[ℝ] ℝ,
      a = fun k ω => if k < K then
        ((c k * s) • (ℓ.comp (fderiv ℝ (F (k * h)) (gridStateA D N K h ω k)))).comp arr
        else 0 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → GridΩA D N K → ℝ, Y = fun k ω => if hk : k < K then
      (if (k : WithTop ℕ) < σ ω then Γ k (gridStateA D N K h ω k, ω.2 ⟨k, hk⟩) else 0)
      else 0 := ⟨_, rfl⟩
  -- properties of `Φ` and `Γ`
  have hΦb : ∀ k, k < K → ∀ H, ‖Φ k H‖ ≤ (N : ℝ) ^ 3 := by
    intro k hk H
    rw [hΦ]
    have := norm_integral_le_of_norm_le_const (μ := γ)
      (f := fun w => F (((k : ℝ) + 1) * h) (ρ • H + s • arr w)) (C := (N : ℝ) ^ 3)
      (ae_of_all _ fun w => hFb _ (hgrid' k hk) _)
    simpa using this
  have hΓm : ∀ k, k < K → Measurable (Γ k) := by
    intro k hk
    obtain ⟨hF1, -, -, -, -⟩ := hFr _ (hgrid' k hk)
    obtain ⟨hF0, -, -, -, -⟩ := hFr _ (hgrid k hk.le)
    have hc1 : Continuous fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
        F (((k : ℝ) + 1) * h) (ρ • p.1 + s • arr p.2) :=
      hF1.continuous.comp ((continuous_fst.const_smul ρ).add
        ((arr.continuous.comp continuous_snd).const_smul s))
    have hΦm : Measurable (Φ k) := by
      rw [hΦ]
      exact hc1.stronglyMeasurable.integral_prod_right'.measurable
    have hdf : Continuous fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
        fderiv ℝ (F (k * h)) p.1 (arr p.2) :=
      ((hF0.continuous_fderiv (by norm_num)).comp continuous_fst).clm_apply
        (arr.continuous.comp continuous_snd)
    rw [hΓ]
    exact (ℓ.continuous.measurable.comp ((hc1.measurable.sub (hΦm.comp measurable_fst)).const_mul
      _)).sub ((ℓ.continuous.comp hdf).measurable.const_mul _)
  have hΓglob : ∀ k, k < K → ∀ p, |Γ k p| ≤ (D * (2 * (N : ℝ) ^ 3 + B)) * (1 + ‖p.2‖) := by
    intro k hk p
    obtain ⟨hc0', hcD, -⟩ := hc0 k hk
    obtain ⟨-, hB1, -, -, -⟩ := hFr _ (hgrid k hk.le)
    rw [hΓ]
    refine (abs_sub _ _).trans ?_
    have t1 : |ℓ ((c k : ℂ) * (F (((k : ℝ) + 1) * h) (ρ • p.1 + s • arr p.2) - Φ k p.1))| ≤
        D * (2 * (N : ℝ) ^ 3) := by
      refine (hℓ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0']
      refine mul_le_mul hcD ((norm_sub_le _ _).trans ?_) (norm_nonneg _) hD0
      have := hFb _ (hgrid' k hk) (ρ • p.1 + s • arr p.2)
      have := hΦb k hk p.1
      linarith
    have t2 : |c k * s * ℓ (fderiv ℝ (F (k * h)) p.1 (arr p.2))| ≤ D * (B * ‖p.2‖) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc0', abs_of_nonneg hs0]
      have h1 : |ℓ (fderiv ℝ (F (k * h)) p.1 (arr p.2))| ≤ B * ‖p.2‖ :=
        (hℓ _).trans (((fderiv ℝ (F (k * h)) p.1).le_opNorm _).trans
          (mul_le_mul (hB1 p.1) (harrn _) (norm_nonneg _) hB0))
      calc c k * s * |ℓ (fderiv ℝ (F (k * h)) p.1 (arr p.2))| ≤ D * 1 * (B * ‖p.2‖) := by
            gcongr
        _ = D * (B * ‖p.2‖) := by ring
    have hp2 := norm_nonneg p.2
    have e : (D : ℝ) * (2 * (N : ℝ) ^ 3 + B) * (1 + ‖p.2‖) =
        D * (2 * (N : ℝ) ^ 3) + D * (B * ‖p.2‖) + (D * (2 * (N : ℝ) ^ 3) * ‖p.2‖ + D * B) := by
      ring
    have h3 : 0 ≤ (D : ℝ) * (2 * (N : ℝ) ^ 3) * ‖p.2‖ + D * B := by positivity
    linarith
  have hΓmean : ∀ k, k < K → ∀ H, ∫ w, Γ k (H, w) ∂γ = 0 := by
    intro k hk H
    obtain ⟨hF1, -, -, -, -⟩ := hFr _ (hgrid' k hk)
    have hY1 : Continuous fun w => F (((k : ℝ) + 1) * h) (ρ • H + s • arr w) :=
      hF1.continuous.comp (continuous_const.add (arr.continuous.const_smul s))
    have hi1 : Integrable (fun w => (c k : ℂ) * (F (((k : ℝ) + 1) * h) (ρ • H + s • arr w) -
        Φ k H)) γ :=
      LF2_int_of_le _ (continuous_const.mul (hY1.sub continuous_const))
        (|c k| * (2 * (N : ℝ) ^ 3)) 0 fun w => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, zero_mul, add_zero]
          refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (abs_nonneg _)
          have := hFb _ (hgrid' k hk) (ρ • H + s • arr w)
          have := hΦb k hk H
          linarith
    have hodd : ∫ w, ℓ (fderiv ℝ (F (k * h)) H (arr w)) ∂γ = 0 :=
      LF2_gueBlocks_odd D N _ fun w => by simp [map_neg]
    have hdfi : Integrable (fun w => ℓ (fderiv ℝ (F (k * h)) H (arr w))) γ := by
      obtain ⟨-, hB1, -, -, -⟩ := hFr _ (hgrid k hk.le)
      refine LF2_int_of_le _ (ℓ.continuous.comp ((fderiv ℝ (F (k * h)) H).continuous.comp
        arr.continuous)) B B fun w => ?_
      have h1 : ‖ℓ (fderiv ℝ (F (k * h)) H (arr w))‖ ≤ B * ‖w‖ := by
        rw [Real.norm_eq_abs]
        exact (hℓ _).trans (((fderiv ℝ (F (k * h)) H).le_opNorm _).trans
          (mul_le_mul (hB1 H) (harrn _) (norm_nonneg _) hB0))
      nlinarith [sq_nonneg (‖w‖ - 1), norm_nonneg w]
    have hY1i : Integrable (fun w => F (((k : ℝ) + 1) * h) (ρ • H + s • arr w)) γ :=
      LF2_int_of_le _ hY1 ((N : ℝ) ^ 3) 0 fun w => by
        simpa using hFb _ (hgrid' k hk) (ρ • H + s • arr w)
    have h0 : ∫ w, (F (((k : ℝ) + 1) * h) (ρ • H + s • arr w) - Φ k H) ∂γ = 0 := by
      rw [integral_sub hY1i (integrable_const _), integral_const, hΦ]
      simp
    simp only [hΓ]
    rw [integral_sub (ℓ.integrable_comp hi1) (hdfi.const_mul _), ℓ.integral_comp_comm hi1,
      integral_const_mul, integral_const_mul, hodd, h0]
    simp
  have hΓsmall : ∀ k, k < K → ∀ H : Idx D N → Idx D N → ℂ, ‖H‖ ≤ 1 → ∀ w,
      |Γ k (H, w)| ≤ D * B * h * ((3 + 2 * M₂ + M₁) + 3 * ‖w‖ ^ 2) := by
    intro k hk H hH w
    obtain ⟨hc0', hcD, -⟩ := hc0 k hk
    obtain ⟨hF0, hB1, hB2, -, -⟩ := hFr _ (hgrid k hk.le)
    obtain ⟨hF1, -, -, -, -⟩ := hFr _ (hgrid' k hk)
    have hg : ∀ Y₁ Y₂, ‖(F (((k : ℝ) + 1) * h) Y₁ - F (k * h) Y₁) -
        (F (((k : ℝ) + 1) * h) Y₂ - F (k * h) Y₂)‖ ≤ B * ‖Y₁ - Y₂‖ * h := by
      intro Y₁ Y₂
      have := LF2_tdiff F Ft S B hder (fun r hr => ⟨(hFr r hr).2.2.2.1, (hFr r hr).2.2.2.2⟩)
        (k * h) (((k : ℝ) + 1) * h) (hgrid k hk.le) (hgrid' k hk) Y₁ Y₂
      have e : |((k : ℝ) + 1) * h - k * h| = h := by
        rw [show ((k : ℝ) + 1) * h - k * h = h by ring, abs_of_pos hh]
      rwa [e] at this
    have h2 := LF2_second (F (k * h)) (F (((k : ℝ) + 1) * h)) B h ((N : ℝ) ^ 3) hh hh1
      (hF0.of_le (by norm_num)) hF1.continuous hB1 hB2 (hFb _ (hgrid k hk.le))
      (hFb _ (hgrid' k hk)) hg H hH w
    have eΓ : Γ k (H, w) = c k * ℓ (F (((k : ℝ) + 1) * h) (ρ • H + s • arr w) - Φ k H -
        (s : ℂ) * fderiv ℝ (F (k * h)) H (arr w)) := by
      rw [hΓ]
      simp only [map_sub, LF2_ell_mul]
      ring
    rw [eΓ, abs_mul, abs_of_nonneg hc0']
    have h3 : |ℓ (F (((k : ℝ) + 1) * h) (ρ • H + s • arr w) - Φ k H -
        (s : ℂ) * fderiv ℝ (F (k * h)) H (arr w))| ≤
        B * h * (2 + 2 * M₂ + M₁ + 2 * ‖w‖ ^ 2 + ‖w‖) := by
      refine (hℓ _).trans ?_
      rw [hΦ]
      exact h2
    have hw : ‖w‖ ≤ 1 + ‖w‖ ^ 2 := by nlinarith [sq_nonneg (‖w‖ - 1)]
    have hBh : 0 ≤ B * h := mul_nonneg hB0 hh.le
    calc c k * |ℓ (F (((k : ℝ) + 1) * h) (ρ • H + s • arr w) - Φ k H -
          (s : ℂ) * fderiv ℝ (F (k * h)) H (arr w))|
        ≤ D * (B * h * (2 + 2 * M₂ + M₁ + 2 * ‖w‖ ^ 2 + ‖w‖)) :=
          mul_le_mul hcD h3 (abs_nonneg _) hD0
      _ ≤ D * (B * h * ((3 + 2 * M₂ + M₁) + 3 * ‖w‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hBh) hD0
          linarith
      _ = _ := by ring
  have hstep : ∀ k (hk : k < K) (ω : GridΩA D N K), gridStateA D N K h ω (k + 1) =
      ρ • gridStateA D N K h ω k + s • arr (ω.2 ⟨k, hk⟩) := by
    intro k hk ω
    rw [gridStateA, dite_eq_left hk]
    rfl
  have hsplit : ∀ k (hk : k < K) (ω : GridΩA D N K),
      ℓ ((c k : ℂ) * (F (((k : ℝ) + 1) * h) (gridStateA D N K h ω (k + 1)) -
        Φ k (gridStateA D N K h ω k))) =
        Γ k (gridStateA D N K h ω k, ω.2 ⟨k, hk⟩) + a k ω (ω.2 ⟨k, hk⟩) := by
    intro k hk ω
    rw [hstep k hk ω, hΓ, ha]
    simp only [hk, ↓reduceIte, ContinuousLinearMap.comp_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hpin : ∀ ω : GridΩA D N K, (Matrix.of ω.1).IsHermitian → ∀ k, k < K →
      (((q₀ - (k + 1) * h) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        (flowLten3 (lam D N A) z₁ z₂ z₃ ((k + 1) * h) (gridStateA D N K h ω (k + 1)) x₁ x₂ x₃ -
          ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((k + 1) * h)
            (ρ • gridStateA D N K h ω k + s • Matrix.of.symm (blockH D N X)) x₁ x₂ x₃ ∂γ) =
      (c k : ℂ) * (F (((k : ℝ) + 1) * h) (gridStateA D N K h ω (k + 1)) -
        Φ k (gridStateA D N K h ω k)) := by
    intro ω hω k hk
    have hφ : ∀ (r : ℝ) (H' : Idx D N → Idx D N → ℂ), (Matrix.of H').IsHermitian →
        flowLten3 (lam D N A) z₁ z₂ z₃ r H' x₁ x₂ x₃ = (D : ℂ) * F r H' :=
      fun r H' hH' => LF2_Lten_loop' _ _ _ _ _ _ _ _ _ hH'
    rw [hφ _ _ (LF2_states_herm D N K h ω hω (k + 1)),
      integral_congr_ae (ae_of_all _ fun X => hφ _ _
        (LF2_state_herm _ _ _ (LF2_states_herm D N K h ω hω k) X)),
      integral_const_mul, hΦ, hc]
    simp only [harr, LF2_arrL_apply]
    push_cast
    ring
  -- the variances `c_k` of the Azuma part
  have hflowk : ∀ k, k < K → 0 < q₀ - k * h ∧ 0 < flowIm (lam D N A) z (k * h) ∧
      (q₀ - k * h) * flowIm (lam D N A) z (k * h) ≤ (charFlowZ (lam D N A) z (k * h)).im := by
    intro k hk
    obtain ⟨-, hιeq, hι0, -, -, -, hqι⟩ := LF2_flow D N hD1 hN1 A hA z hz S hSt (k * h)
      (hgrid k hk.le).1 (hgrid k hk.le).2
    refine ⟨by linarith [(hgrid k hk.le).2], by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0,
      hqι⟩
  obtain ⟨cv, hcv⟩ : ∃ cv : ℕ → ℝ, cv = fun k : ℕ => if k < K then 9 * D ^ 2 * h *
      (N : ℝ) ^ τ' / ((N : ℝ) ^ 2 * (q₀ - k * h) ^ 4 * flowIm (lam D N A) z (k * h) ^ 6)
      else 1 := ⟨_, rfl⟩
  have hcvpos : ∀ k, 0 < cv k := by
    intro k
    rw [hcv]
    dsimp only
    split_ifs with hk
    · obtain ⟨h1, h2, -⟩ := hflowk k hk
      have : (0 : ℝ) < D := by exact_mod_cast hD1
      positivity
    · exact one_pos
  set cc : ℕ → ℝ≥0 := fun k => ⟨cv k, (hcvpos k).le⟩ with hcc
  have hcc0 : ∀ k, 0 < cc k := fun k => hcvpos k
  have ha_meas : ∀ k, StronglyMeasurable[gridFiltrA D N K k] (a k) := by
    intro k
    by_cases hk : k < K
    · have hfd := (hFr _ (hgrid k hk.le)).1.continuous_fderiv (by norm_num)
      have h1 : Continuous fun H : Idx D N → Idx D N → ℂ => ℓ.comp (fderiv ℝ (F (k * h)) H) :=
        continuous_const.clm_comp hfd
      have h2 : Continuous fun H : Idx D N → Idx D N → ℂ =>
          (c k * s) • ℓ.comp (fderiv ℝ (F (k * h)) H) := h1.const_smul (c k * s)
      have hΨ : Continuous fun H : Idx D N → Idx D N → ℂ =>
          ((c k * s) • (ℓ.comp (fderiv ℝ (F (k * h)) H))).comp arr :=
        h2.clm_comp continuous_const
      have e : a k = fun ω =>
          ((c k * s) • (ℓ.comp (fderiv ℝ (F (k * h)) (gridStateA D N K h ω k)))).comp arr := by
        rw [ha]; funext ω; simp [hk]
      rw [e]
      exact hΨ.comp_stronglyMeasurable (gridStateA_adapted D N K h k).stronglyMeasurable
    · have e : a k = fun _ => 0 := by rw [ha]; funext ω; simp [hk]
      rw [e]
      exact stronglyMeasurable_const
  have hcvar : ∀ (k : ℕ) ω, (k : WithTop ℕ) < σ ω → ∫ w, (a k ω w) ^ 2 ∂γ ≤ cc k := by
    intro k ω hkσ
    by_cases hk : k < K
    · have hnb := (LF2_sig_lt A z τ' h ω k).1 hkσ k le_rfl
      have hnb' : (Matrix.of (gridStateA D N K h ω k)).IsHermitian ∧
          flowGoodAt A z τ' (k * h) (gridStateA D N K h ω k) := by
        by_contra hcon
        exact hnb ⟨hk.le, hcon⟩
      obtain ⟨hHk, hgk⟩ := hnb'
      obtain ⟨-, hB1, -, -, -⟩ := hFr _ (hgrid k hk.le)
      have e : ∀ w, a k ω w = c k * s *
          ℓ (fderiv ℝ (F (k * h)) (gridStateA D N K h ω k) (arr w)) := by
        intro w; rw [ha]; simp [hk, smul_eq_mul]
      have hv := LF2_var D N A z hz (k * h) (lt_of_le_of_lt (hgrid k hk.le).2 hSt) τ' _ hHk hgk
        z₁ z₂ z₃ h₁ h₂ h₃ x₁ x₂ x₃
      have hint : Integrable (fun w => ‖fderiv ℝ (F (k * h)) (gridStateA D N K h ω k)
          (arr w)‖ ^ 2) γ := by
        refine LF2_int_of_le _ ((((fderiv ℝ (F (k * h)) (gridStateA D N K h ω k)).continuous.comp
          arr.continuous).norm.pow 2)) 0 (B ^ 2) fun w => ?_
        have h1 : ‖fderiv ℝ (F (k * h)) (gridStateA D N K h ω k) (arr w)‖ ≤ B * ‖w‖ :=
          ((fderiv ℝ (F (k * h)) _).le_opNorm _).trans
            (mul_le_mul (hB1 _) (harrn _) (norm_nonneg _) hB0)
        rw [Real.norm_of_nonneg (by positivity), zero_add, ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      have hle : ∀ w, (a k ω w) ^ 2 ≤ (c k * s) ^ 2 *
          ‖fderiv ℝ (F (k * h)) (gridStateA D N K h ω k) (arr w)‖ ^ 2 := by
        intro w
        rw [e, mul_pow]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact sq_le_sq' (by linarith [abs_le.1 (hℓ (fderiv ℝ (F (k * h))
          (gridStateA D N K h ω k) (arr w)))] ) (abs_le.1 (hℓ _)).2
      obtain ⟨hq, hι, hqι⟩ := hflowk k hk
      obtain ⟨hc0', -, hcq⟩ := hc0 k hk
      calc ∫ w, (a k ω w) ^ 2 ∂γ ≤ ∫ w, (c k * s) ^ 2 *
            ‖fderiv ℝ (F (k * h)) (gridStateA D N K h ω k) (arr w)‖ ^ 2 ∂γ := by
            refine integral_mono_of_nonneg (ae_of_all _ fun w => sq_nonneg _)
              (hint.const_mul _) (ae_of_all _ hle)
        _ = (c k * s) ^ 2 * ∫ w,
            ‖fderiv ℝ (F (k * h)) (gridStateA D N K h ω k) (arr w)‖ ^ 2 ∂γ :=
            integral_const_mul _ _
        _ ≤ (c k * s) ^ 2 * (9 * ((N : ℝ) ^ τ' * (flowIm (lam D N A) z (k * h) /
            (charFlowZ (lam D N A) z (k * h)).im ^ 7)) / (N : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hv (sq_nonneg _)
        _ ≤ cv k := by
            rw [hcv]
            simp only [hk, ↓reduceIte]
            exact LF2_ar_var (c k) s (q₀ - k * h) _ _ D h N _ hcq hs2 hq hι hNpos
              (Real.rpow_nonneg hNpos.le _) hqι
        _ = cc k := rfl
    · have e : ∀ w, a k ω w = 0 := by intro w; rw [ha]; simp [hk]
      simp only [e]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero,
        NNReal.zero_le_coe]
  -- the second-order parts `Y_k`
  set C₀ := 3 + 2 * M₂ + M₁ with hC₀
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; linarith
  have hYle : ∀ k (hk : k < K) ω, |Y k ω| ≤ D * B * h * (C₀ + 3 * ‖ω.2 ⟨k, hk⟩‖ ^ 2) := by
    intro k hk ω
    rw [hY]
    simp only [hk, ↓reduceDIte]
    split_ifs with hkσ
    · have hnb := (LF2_sig_lt A z τ' h ω k).1 hkσ k le_rfl
      have hnb' : (Matrix.of (gridStateA D N K h ω k)).IsHermitian ∧
          flowGoodAt A z τ' (k * h) (gridStateA D N K h ω k) := by
        by_contra hcon
        exact hnb ⟨hk.le, hcon⟩
      have hHn : ‖gridStateA D N K h ω k‖ ≤ 1 :=
        (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
          (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => hnb'.2.2.2 i j
      exact hΓsmall k hk _ hHn _
    · rw [abs_zero]; positivity
  have hYmeas : ∀ k, StronglyMeasurable[gridFiltrA D N K (k + 1)] (Y k) := by
    intro k
    by_cases hk : k < K
    · have e : Y k = fun ω => if (k : WithTop ℕ) < σ ω then
          Γ k (gridStateA D N K h ω k, ω.2 ⟨k, hk⟩) else 0 := by
        rw [hY]; funext ω; simp [hk]
      rw [e]
      refine Measurable.stronglyMeasurable ?_
      refine Measurable.ite ((gridFiltrA_mono D N K).1 (Nat.le_succ k) _
        (LF2_sig_lt_meas D N K A z τ' h k)) ?_ measurable_const
      exact (hΓm k hk).comp (((gridStateA_adapted D N K h k).mono
        ((gridFiltrA_mono D N K).1 (Nat.le_succ k)) le_rfl).prodMk (LF2_incr_meas D N K k hk))
    · have e : Y k = fun _ => 0 := by rw [hY]; funext ω; simp [hk]
      rw [e]
      exact stronglyMeasurable_const
  have hmF : ∀ k, gridFiltrA D N K k ≤ (inferInstance : MeasurableSpace (GridΩA D N K)) :=
    fun k => (gridFiltrA_mono D N K).2 k
  have hpoly : Integrable (fun w : Fin D → Coords N =>
      (D * B * h) ^ 2 * (2 * (C₀ ^ 2 + 9 * ‖w‖ ^ 4))) γ :=
    ((integrable_const (C₀ ^ 2)).add ((LF2_int_pow D N 4).const_mul 9)).const_mul 2
      |>.const_mul _
  have hYsq : ∀ k (hk : k < K) ω, Y k ω ^ 2 ≤ (D * B * h) ^ 2 * (2 * (C₀ ^ 2 +
      9 * ‖ω.2 ⟨k, hk⟩‖ ^ 4)) := by
    intro k hk ω
    have h1 := hYle k hk ω
    have h2 : Y k ω ^ 2 ≤ (D * B * h * (C₀ + 3 * ‖ω.2 ⟨k, hk⟩‖ ^ 2)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans ?_
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    nlinarith [sq_nonneg (C₀ - 3 * ‖ω.2 ⟨k, hk⟩‖ ^ 2)]
  have hYL2 : ∀ k, MemLp (Y k) 2 μ := by
    intro k
    have hasm : AEStronglyMeasurable (Y k) μ :=
      ((hYmeas k).mono (hmF (k + 1))).aestronglyMeasurable
    by_cases hk : k < K
    · refine (memLp_two_iff_integrable_sq hasm).2 ?_
      refine Integrable.mono' ((LF2_incr_law D N K μ₀ k hk).integrable_comp_of_integrable hpoly)
        (hasm.pow 2) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hYsq k hk ω
    · have e : Y k = fun _ => 0 := by rw [hY]; funext ω; simp [hk]
      rw [e]
      exact memLp_const 0
  have hYcond : ∀ k, μ[Y k | gridFiltrA D N K k] =ᵐ[μ] 0 := by
    intro k
    by_cases hk : k < K
    · obtain ⟨ind, hind⟩ : ∃ ind : GridΩA D N K → ℝ,
          ind = fun ω => if (k : WithTop ℕ) < σ ω then 1 else 0 := ⟨_, rfl⟩
      have e : Y k = ind * fun ω => Γ k (gridStateA D N K h ω k, ω.2 ⟨k, hk⟩) := by
        rw [hY, hind]; funext ω; simp only [hk, ↓reduceDIte, Pi.mul_apply]
        split_ifs <;> simp
      have hindm : StronglyMeasurable[gridFiltrA D N K k] ind := by
        rw [hind]
        exact (Measurable.ite (LF2_sig_lt_meas D N K A z τ' h k) measurable_const
          measurable_const).stronglyMeasurable
      have hgm : Measurable fun ω : GridΩA D N K => Γ k (gridStateA D N K h ω k, ω.2 ⟨k, hk⟩) :=
        (hΓm k hk).comp ((LF2_state_meas D N K h k).prodMk
          ((measurable_pi_apply _).comp measurable_snd))
      have hlin : Integrable (fun w : Fin D → Coords N =>
          (D * (2 * (N : ℝ) ^ 3 + B)) * (1 + ‖w‖)) γ := by
        have hi1 : Integrable (fun w : Fin D → Coords N => ‖w‖) γ := by
          have := LF2_int_pow D N 1; simp only [pow_one] at this; exact this
        exact ((integrable_const 1).add hi1).const_mul _
      have hgi : Integrable (fun ω : GridΩA D N K =>
          Γ k (gridStateA D N K h ω k, ω.2 ⟨k, hk⟩)) μ :=
        Integrable.mono' ((LF2_incr_law D N K μ₀ k hk).integrable_comp_of_integrable hlin)
          hgm.aestronglyMeasurable (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs]; exact hΓglob k hk _)
      have h1 := condExp_stronglyMeasurable_mul_of_bound (hmF k) hindm hgi 1
        (ae_of_all _ fun ω => by rw [hind]; dsimp only; split_ifs <;> simp)
      have h2 := LF2_condExp D N K μ₀ h k hk (Γ k) (hΓm k hk) _ (hΓglob k hk)
      rw [e]
      filter_upwards [h1, h2] with ω h1ω h2ω
      rw [h1ω, Pi.mul_apply, h2ω, hΓmean k hk]
      simp
    · have e : Y k = fun _ => 0 := by rw [hY]; funext ω; simp [hk]
      rw [e, show (fun _ : GridΩA D N K => (0 : ℝ)) = 0 from rfl, condExp_zero]
  set v := (D * B * h) ^ 2 * (2 * (C₀ ^ 2 + 9 * M₄)) with hv
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hYv : ∀ k, ∫ ω, Y k ω ^ 2 ∂μ ≤ v := by
    intro k
    by_cases hk : k < K
    · have hgc : Continuous fun w : Fin D → Coords N =>
          (D * B * h) ^ 2 * (2 * (C₀ ^ 2 + 9 * ‖w‖ ^ 4)) := by fun_prop
      have hmap := integral_map (μ := μ) (LF2_incr_law D N K μ₀ k hk).measurable.aemeasurable
        hgc.aestronglyMeasurable
      rw [(LF2_incr_law D N K μ₀ k hk).map_eq] at hmap
      calc ∫ ω, Y k ω ^ 2 ∂μ ≤ ∫ ω, (D * B * h) ^ 2 *
            (2 * (C₀ ^ 2 + 9 * ‖ω.2 ⟨k, hk⟩‖ ^ 4)) ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
              ((LF2_incr_law D N K μ₀ k hk).integrable_comp_of_integrable hpoly)
              (ae_of_all _ (hYsq k hk))
        _ = ∫ w, (D * B * h) ^ 2 * (2 * (C₀ ^ 2 + 9 * ‖w‖ ^ 4)) ∂γ := hmap.symm
        _ = v := by
            rw [hv, integral_const_mul, integral_const_mul,
              integral_add (integrable_const _) ((LF2_int_pow D N 4).const_mul 9),
              integral_const_mul]
            simp [hM₄, hγ]
    · have e : Y k = fun _ => 0 := by rw [hY]; funext ω; simp [hk]
      rw [e]
      simpa using hv0
  -- Azuma and Doob
  have hAz := gridMartA_max D N K μ₀ a ha_meas σ (LF2_sig_stop D N K A z τ' h) cc hcc0 hcvar
    lv hlv
  have hDb := gridDoobA_max D N K μ₀ Y hYmeas hYL2 hYcond (fun _ => v) hYv ε hε
  refine ⟨{ω | ∃ n ≤ K, lv * Real.sqrt (∑ k ∈ Finset.range n, (cc k : ℝ)) <
      |∑ k ∈ Finset.range n, if hk : k < K then
        (if (k : WithTop ℕ) < σ ω then a k ω (ω.2 ⟨k, hk⟩) else 0) else 0|} ∪
      {ω | ∃ n ≤ K, ε ≤ |∑ k ∈ Finset.range n, Y k ω|}, ?_, ?_⟩
  · refine (measureReal_union_le _ _).trans ((add_le_add hAz hDb).trans (le_of_eq ?_))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hv]
  · intro ω hω hherm n hn hgood
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt,
      not_le] at hω
    obtain ⟨hω1, hω2⟩ := hω
    have h1 := hω1 n hn
    have h2 := hω2 n hn
    have hterm : ∀ j ∈ Finset.range n,
        ℓ ((((q₀ - (j + 1) * h) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          (flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * h) (gridStateA D N K h ω (j + 1)) x₁ x₂ x₃ -
            ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * h)
              (ρ • gridStateA D N K h ω j + s • Matrix.of.symm (blockH D N X)) x₁ x₂ x₃ ∂γ)) =
        (if hk : j < K then (if (j : WithTop ℕ) < σ ω then a j ω (ω.2 ⟨j, hk⟩) else 0)
          else 0) + Y j ω := by
      intro j hj
      have hjn : j < n := Finset.mem_range.1 hj
      have hjK : j < K := lt_of_lt_of_le hjn hn
      have hjσ : (j : WithTop ℕ) < σ ω := (LF2_sig_lt A z τ' h ω j).2 fun i hi hbad =>
        hbad.2 ⟨LF2_states_herm D N K h ω hherm i, hgood i (by omega)⟩
      rw [hpin ω hherm j hjK, hsplit j hjK ω, hY]
      simp only [hjK, hjσ, ↓reduceDIte, ↓reduceIte]
      ring
    have hcv' : ∀ k, (cc k : ℝ) = if k < K then 9 * D ^ 2 * h * (N : ℝ) ^ τ' /
        ((N : ℝ) ^ 2 * (q₀ - k * h) ^ 4 * flowIm (lam D N A) z (k * h) ^ 6) else 1 := by
      intro k
      change cv k = _
      rw [hcv]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    simp only [hcv'] at h1
    calc _ ≤ |∑ k ∈ Finset.range n, (if hk : k < K then
          (if (k : WithTop ℕ) < σ ω then a k ω (ω.2 ⟨k, hk⟩) else 0) else 0)| +
          |∑ k ∈ Finset.range n, Y k ω| := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2.le

/-- `C N^a e^{-N^b/2} ≤ 1` for large `N`, `b > 0`. -/
private lemma LF2_tail (a b C : ℝ) (hb : 0 < b) :
    ∀ᶠ N : ℕ in Filter.atTop, C * (N : ℝ) ^ a * Real.exp (-((N : ℝ) ^ b) / 2) ≤ 1 := by
  have t := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / b) (1 / 2) (by norm_num)
  have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ b) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
  have t3 := (t.comp t2).const_mul C
  filter_upwards [t3.eventually (Iic_mem_nhds (by simp : C * 0 < 1))] with N hN
  simp only [Function.comp] at hN
  have e : (N : ℝ) ^ a = ((N : ℝ) ^ b) ^ (a / b) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    field_simp
  have e2 : Real.exp (-((N : ℝ) ^ b) / 2) = Real.exp (-(1 / 2) * (N : ℝ) ^ b) := by ring_nf
  rw [e, e2, mul_assoc]
  exact hN

/-! ### The martingale part: assembly of the components -/

/-- `‖T‖₂ ≤ Σ_{x,y,w} (|Re T_{xyw}| + |Im T_{xyw}|)`. -/
private lemma LF2_ten_le {D : ℕ} (T : Fin D → Fin D → Fin D → ℂ) :
    ten3Norm T ≤ ∑ x, ∑ y, ∑ w, (|(T x y w).re| + |(T x y w).im|) := by
  unfold ten3Norm
  have h1 : ∑ x, ∑ y, ∑ w, ‖T x y w‖ ^ 2 ≤ (∑ x, ∑ y, ∑ w, ‖T x y w‖) ^ 2 := by
    calc ∑ x, ∑ y, ∑ w, ‖T x y w‖ ^ 2 ≤ ∑ x, ∑ y, (∑ w, ‖T x y w‖) ^ 2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            Finset.sum_sq_le_sq_sum_of_nonneg fun w _ => norm_nonneg _
      _ ≤ ∑ x, (∑ y, ∑ w, ‖T x y w‖) ^ 2 := Finset.sum_le_sum fun x _ =>
          Finset.sum_sq_le_sq_sum_of_nonneg fun y _ => Finset.sum_nonneg fun w _ => norm_nonneg _
      _ ≤ (∑ x, ∑ y, ∑ w, ‖T x y w‖) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun x _ =>
          Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun w _ => norm_nonneg _
  have h0 : 0 ≤ ∑ x, ∑ y, ∑ w, ‖T x y w‖ := Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun w _ => norm_nonneg _
  calc Real.sqrt (∑ x, ∑ y, ∑ w, ‖T x y w‖ ^ 2) ≤ ∑ x, ∑ y, ∑ w, ‖T x y w‖ := by
        rw [Real.sqrt_le_left h0]; exact h1
    _ ≤ _ := Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => Finset.sum_le_sum
        fun w _ => Complex.norm_le_abs_re_add_abs_im _

/-- The sum of the variances of the Azuma part along the grid: for `n ≤ K`,
`Σ_{k<n} 9 D² h N^{t} / (N² q_k⁴ (Im m_k)⁶) ≤ 3 e³ D² N^{t} / (N² q_n³ (Im m_n)⁶)`. -/
private lemma LF2_csum (D N K : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hSt : S < flowTc (lam D N A) z) (hq1 : flowTc (lam D N A) z ≤ 1) (h : ℝ) (hh : 0 < h)
    (hKh : (K : ℝ) * h = S) (t : ℝ) (n : ℕ) (hn : n ≤ K) :
    ∑ k ∈ Finset.range n, (if k < K then 9 * D ^ 2 * h * (N : ℝ) ^ t /
        ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - k * h) ^ 4 *
          flowIm (lam D N A) z (k * h) ^ 6) else 1) ≤
      3 * Real.exp 1 ^ 3 * D ^ 2 * (N : ℝ) ^ t /
        ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - n * h) ^ 3 *
          flowIm (lam D N A) z (n * h) ^ 6) := by
  set q₀ := flowTc (lam D N A) z with hq₀
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hgrid : ∀ k : ℕ, k ≤ K → 0 ≤ (k : ℝ) * h ∧ (k : ℝ) * h ≤ S := fun k hk =>
    ⟨by positivity, by rw [← hKh]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le⟩
  have hι : ∀ k : ℕ, k ≤ K → flowIm (lam D N A) z (k * h) =
      Real.exp (k * h / 2) * (mExt (lam D N A) z).im := fun k hk =>
    (LF2_flow D N hD hN A hA z hz S hSt (k * h) (hgrid k hk).1 (hgrid k hk).2).2.1
  have hι0 : 0 < (mExt (lam D N A) z).im :=
    (LF2_flow D N hD hN A hA z hz S hSt 0 le_rfl (le_trans (by positivity) (hgrid 0
      (Nat.zero_le K)).2)).2.2.1
  set ι₀ := (mExt (lam D N A) z).im with hι₀
  have hS0 : 0 ≤ S := by rw [← hKh]; positivity
  have hqn : 0 < q₀ - n * h := by linarith [(hgrid n hn).2]
  have hnK : (n : ℝ) * h < q₀ := by linarith
  have hterm : ∀ k ∈ Finset.range n, (if k < K then 9 * D ^ 2 * h * (N : ℝ) ^ t /
      ((N : ℝ) ^ 2 * (q₀ - k * h) ^ 4 * flowIm (lam D N A) z (k * h) ^ 6) else 1) ≤
      (9 * D ^ 2 * (N : ℝ) ^ t / ((N : ℝ) ^ 2 * ι₀ ^ 6)) *
        (h * (q₀ - (0 + k * h)) ^ (-(4 : ℝ))) := by
    intro k hk
    have hkn : k < n := Finset.mem_range.1 hk
    have hkK : k < K := lt_of_lt_of_le hkn hn
    simp only [hkK, ↓reduceIte, zero_add]
    have hqk : 0 < q₀ - k * h := by linarith [(hgrid k hkK.le).2]
    rw [hι k hkK.le]
    have hek : 1 ≤ Real.exp (k * h / 2) := Real.one_le_exp (by positivity)
    have e4 : (q₀ - k * h) ^ (-(4 : ℝ)) = ((q₀ - k * h) ^ 4)⁻¹ := by
      rw [Real.rpow_neg hqk.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e4]
    have hι6 : ι₀ ^ 6 ≤ (Real.exp (k * h / 2) * ι₀) ^ 6 := by
      apply pow_le_pow_left₀ hι0.le
      nlinarith
    have hNt : 0 ≤ (N : ℝ) ^ t := Real.rpow_nonneg hNpos.le _
    rw [div_le_iff₀ (by positivity)]
    have : 9 * D ^ 2 * (N : ℝ) ^ t / ((N : ℝ) ^ 2 * ι₀ ^ 6) * (h * ((q₀ - k * h) ^ 4)⁻¹) *
        ((N : ℝ) ^ 2 * (q₀ - k * h) ^ 4 * (Real.exp (k * h / 2) * ι₀) ^ 6) =
        9 * D ^ 2 * h * (N : ℝ) ^ t * ((Real.exp (k * h / 2) * ι₀) ^ 6 / ι₀ ^ 6) := by
      have hne : q₀ - (k : ℝ) * h ≠ 0 := hqk.ne'
      have hne2 : q₀ - h * (k : ℝ) ≠ 0 := by rw [mul_comm]; exact hne
      have hne' : ι₀ ≠ 0 := hι0.ne'
      field_simp
    rw [this]
    have h1 : 1 ≤ (Real.exp (k * h / 2) * ι₀) ^ 6 / ι₀ ^ 6 := by
      rw [le_div_iff₀ (by positivity), one_mul]; exact hι6
    have h2 : 0 ≤ 9 * (D : ℝ) ^ 2 * h * (N : ℝ) ^ t := by positivity
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hR := riemann_rpow_le 0 h q₀ 4 hh (by norm_num) 0 n (Nat.zero_le n)
    (by rw [zero_add]; exact hnK)
  rw [← Finset.range_eq_Ico] at hR
  have e2 : (q₀ - (0 + n * h)) ^ (1 - (4 : ℝ)) / (4 - 1) = ((q₀ - n * h) ^ 3)⁻¹ / 3 := by
    rw [zero_add, show (1 - (4 : ℝ)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hqn.le,
      Real.rpow_natCast]
    norm_num
  rw [e2] at hR
  have hC0 : 0 ≤ 9 * D ^ 2 * (N : ℝ) ^ t / ((N : ℝ) ^ 2 * ι₀ ^ 6) := by
    have := Real.rpow_nonneg hNpos.le t
    positivity
  refine (mul_le_mul_of_nonneg_left hR hC0).trans ?_
  rw [hι n hn]
  have hen : Real.exp (n * h / 2) ^ 6 ≤ Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have : (n : ℝ) * h ≤ 1 := by linarith
    push_cast
    linarith
  have hNt : 0 ≤ (N : ℝ) ^ t := Real.rpow_nonneg hNpos.le _
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have key : (Real.exp (n * h / 2) * ι₀) ^ 6 ≤ Real.exp 1 ^ 3 * ι₀ ^ 6 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right hen (by positivity)
  calc 9 * (D : ℝ) ^ 2 * (N : ℝ) ^ t * (((q₀ - n * h) ^ 3)⁻¹ / 3) *
        ((N : ℝ) ^ 2 * (q₀ - n * h) ^ 3 * (Real.exp (n * h / 2) * ι₀) ^ 6)
      = 3 * (D : ℝ) ^ 2 * (N : ℝ) ^ t * (N : ℝ) ^ 2 * (Real.exp (n * h / 2) * ι₀) ^ 6 := by
        have hne : q₀ - (n : ℝ) * h ≠ 0 := hqn.ne'
        field_simp
        norm_num
    _ ≤ 3 * (D : ℝ) ^ 2 * (N : ℝ) ^ t * (N : ℝ) ^ 2 * (Real.exp 1 ^ 3 * ι₀ ^ 6) := by
        gcongr
    _ = 3 * Real.exp 1 ^ 3 * D ^ 2 * (N : ℝ) ^ t * ((N : ℝ) ^ 2 * ι₀ ^ 6) := by ring

/-- The threshold of the martingale part dominates the sum of the `2D³` real components:
`2 D³ (N^{τ'/4} (Σ c)^{1/2} + 1/(4 D³ N)) ≤ N^{τ'} / (N p ι³)` when
`Σ c ≤ 3 e³ D² N^{τ'/8} / (N² p² ι⁶)`, `p, ι ∈ (0, 1]` and `8 e² D⁴ ≤ N^{11τ'/16}`. -/
private lemma LF2_thr (D N τ' p ι sc : ℝ) (hD : 1 ≤ D) (hN : 1 ≤ N) (hτ' : 0 < τ')
    (hp : 0 < p) (hp1 : p ≤ 1) (hι : 0 < ι) (hι1 : ι ≤ 1) (hsc0 : 0 ≤ sc)
    (hsc : sc ≤ 3 * Real.exp 1 ^ 3 * D ^ 2 * N ^ (τ' / 8) / (N ^ 2 * p ^ 2 * ι ^ 6))
    (hND : 8 * Real.exp 1 ^ 2 * D ^ 4 ≤ N ^ (11 * τ' / 16)) :
    2 * D ^ 3 * (N ^ (τ' / 4) * Real.sqrt sc + 1 / (4 * D ^ 3 * N)) ≤
      N ^ τ' / (N * p * ι ^ 3) := by
  have hNpos : 0 < N := by linarith
  have hDpos : 0 < D := by linarith
  set thr := N ^ τ' / (N * p * ι ^ 3) with hthr
  have hthr0 : 0 < thr := by positivity
  have hN1t : 1 ≤ N ^ τ' := Real.one_le_rpow hN hτ'.le
  have he := Real.exp_pos 1
  -- the Azuma part
  have hA : N ^ (τ' / 4) * Real.sqrt sc ≤ thr / (4 * D ^ 3) := by
    have h0 : 0 ≤ N ^ (τ' / 4) := Real.rpow_nonneg hNpos.le _
    rw [← Real.sqrt_sq h0, ← Real.sqrt_mul (sq_nonneg _)]
    rw [Real.sqrt_le_left (by positivity)]
    have e1 : (N ^ (τ' / 4)) ^ 2 = N ^ (τ' / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num; ring_nf
    have e2 : (N ^ (11 * τ' / 16)) ^ 2 = N ^ (11 * τ' / 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num; ring_nf
    have e3 : (N ^ τ') ^ 2 = N ^ (τ' / 2) * N ^ (τ' / 8) * N ^ (11 * τ' / 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos,
        ← Real.rpow_add hNpos]
      norm_num; ring_nf
    rw [e1]
    have hsq : (8 * Real.exp 1 ^ 2 * D ^ 4) ^ 2 ≤ N ^ (11 * τ' / 8) := by
      rw [← e2]; exact pow_le_pow_left₀ (by positivity) hND 2
    have hpos1 : 0 < N ^ (τ' / 2) := Real.rpow_pos_of_pos hNpos _
    have hpos2 : 0 < N ^ (τ' / 8) := Real.rpow_pos_of_pos hNpos _
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    calc N ^ (τ' / 2) * sc ≤ N ^ (τ' / 2) * (3 * Real.exp 1 ^ 3 * D ^ 2 * N ^ (τ' / 8) /
          (N ^ 2 * p ^ 2 * ι ^ 6)) := mul_le_mul_of_nonneg_left hsc hpos1.le
      _ ≤ (thr / (4 * D ^ 3)) ^ 2 := by
          have hY : 0 < N ^ 2 * p ^ 2 * ι ^ 6 := by positivity
          have h32 : 3 * Real.exp 1 ^ 3 * D ^ 2 * (16 * D ^ 6) ≤ N ^ (11 * τ' / 8) := by
            have : 3 * Real.exp 1 ^ 3 * D ^ 2 * (16 * D ^ 6) ≤
                (8 * Real.exp 1 ^ 2 * D ^ 4) ^ 2 := by
              have : (8 * Real.exp 1 ^ 2 * D ^ 4) ^ 2 = 64 * Real.exp 1 ^ 4 * D ^ 8 := by ring
              rw [this]
              have : Real.exp 1 ^ 3 ≤ Real.exp 1 ^ 4 := pow_le_pow_right₀ he1 (by norm_num)
              nlinarith [pow_pos hDpos 8]
            linarith
          have key : N ^ (τ' / 2) * (3 * Real.exp 1 ^ 3 * D ^ 2 * N ^ (τ' / 8)) ≤
              (N ^ τ') ^ 2 / (16 * D ^ 6) := by
            rw [le_div_iff₀ (by positivity), e3]
            have hx : 0 < N ^ (τ' / 2) * N ^ (τ' / 8) := mul_pos hpos1 hpos2
            have : N ^ (τ' / 2) * (3 * Real.exp 1 ^ 3 * D ^ 2 * N ^ (τ' / 8)) * (16 * D ^ 6) =
                (N ^ (τ' / 2) * N ^ (τ' / 8)) * (3 * Real.exp 1 ^ 3 * D ^ 2 * (16 * D ^ 6)) := by
              ring
            rw [this]
            exact mul_le_mul_of_nonneg_left h32 hx.le
          calc N ^ (τ' / 2) * (3 * Real.exp 1 ^ 3 * D ^ 2 * N ^ (τ' / 8) /
                (N ^ 2 * p ^ 2 * ι ^ 6))
              = N ^ (τ' / 2) * (3 * Real.exp 1 ^ 3 * D ^ 2 * N ^ (τ' / 8)) /
                (N ^ 2 * p ^ 2 * ι ^ 6) := by ring
            _ ≤ (N ^ τ') ^ 2 / (16 * D ^ 6) / (N ^ 2 * p ^ 2 * ι ^ 6) :=
                div_le_div_of_nonneg_right key hY.le
            _ = (thr / (4 * D ^ 3)) ^ 2 := by
                rw [hthr]
                field_simp
                ring
  -- the Doob part
  have hB : 1 / (4 * D ^ 3 * N) ≤ thr / (4 * D ^ 3) := by
    rw [hthr, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : p * ι ^ 3 ≤ 1 := by
      have : ι ^ 3 ≤ 1 := pow_le_one₀ hι.le hι1
      nlinarith
    have h2 : 0 < 4 * D ^ 3 * N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans hN1t) h2.le]
  calc 2 * D ^ 3 * (N ^ (τ' / 4) * Real.sqrt sc + 1 / (4 * D ^ 3 * N))
      ≤ 2 * D ^ 3 * (thr / (4 * D ^ 3) + thr / (4 * D ^ 3)) := by gcongr
    _ = thr := by field_simp; ring

/-- The failure probability of the martingale part over the `2D³` real components:
`2 D³ (2 K e^{-N^{τ'/2}/2} + K v / ε²) ≤ N^{-D'}` for `ε = 1/(4 D³ N)`, `K ∈ [N^{C_g}, N^{C_g+1}]`,
`C_g ≥ 31 + D'`, `h = S/K`, `S ≤ 1`, and `v = (D B h)² 2 ((3 + 2 M₂ + M₁)² + 9 M₄)` with
`B ≤ c_B N^{13}` and moments `M₁ ≤ 1 + M₂`, `M₂² ≤ M₄ ≤ 2 D N² m₄`. -/
private lemma LF2_prob (D N K Cg D' τ' cB m₄ S B M₁ M₂ M₄ : ℝ) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hKlo : N ^ Cg ≤ K) (hKhi : K ≤ N ^ (Cg + 1)) (hD' : 0 < D') (hCg : 31 + D' ≤ Cg)
    (hS0 : 0 < S) (hS1 : S ≤ 1) (hB0 : 0 ≤ B) (hB : B ≤ cB * N ^ 13) (hm₄ : 0 ≤ m₄)
    (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂) (hM₁ : M₁ ≤ 1 + M₂) (hM₂ : M₂ ^ 2 ≤ M₄) (hM₄0 : 0 ≤ M₄)
    (hM₄ : M₄ ≤ 2 * D * N ^ 2 * m₄)
    (htail : 16 * D ^ 3 * N ^ (Cg + 1 + D') * Real.exp (-(N ^ (τ' / 2)) / 2) ≤ 1)
    (hbig : 256 * D ^ 11 * cB ^ 2 * (32 + 54 * D * m₄) ≤ N) :
    D * D * D * 2 * (2 * K * Real.exp (-(N ^ (τ' / 4)) ^ 2 / 2) +
      K * ((D * B * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄))) /
        (1 / (4 * D ^ 3 * N)) ^ 2) ≤ N ^ (-D') := by
  have hNpos : 0 < N := by linarith
  have hD0 : 0 < D := by linarith
  have hNCg : 1 ≤ N ^ Cg := Real.one_le_rpow hN (by linarith)
  have hKpos : 0 < K := by linarith
  have hND' : 0 < N ^ (-D') := Real.rpow_pos_of_pos hNpos _
  -- the Azuma part
  have e1 : (N ^ (τ' / 4)) ^ 2 = N ^ (τ' / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num; ring_nf
  have hA : D * D * D * 2 * (2 * K * Real.exp (-(N ^ (τ' / 4)) ^ 2 / 2)) ≤ N ^ (-D') / 4 := by
    rw [e1]
    have hsplit : N ^ (Cg + 1 + D') = N ^ (Cg + 1) * N ^ D' := Real.rpow_add hNpos _ _
    have hinv : N ^ D' * N ^ (-D') = 1 := by
      rw [← Real.rpow_add hNpos]; simp
    have hE : 0 < Real.exp (-(N ^ (τ' / 2)) / 2) := Real.exp_pos _
    have h1 : D * D * D * 2 * (2 * K * Real.exp (-(N ^ (τ' / 2)) / 2)) ≤
        4 * D ^ 3 * N ^ (Cg + 1) * Real.exp (-(N ^ (τ' / 2)) / 2) := by
      have : D * D * D * 2 * (2 * K * Real.exp (-(N ^ (τ' / 2)) / 2)) =
          4 * D ^ 3 * K * Real.exp (-(N ^ (τ' / 2)) / 2) := by ring
      rw [this]
      gcongr
    refine h1.trans ?_
    rw [hsplit] at htail
    have : 4 * D ^ 3 * N ^ (Cg + 1) * Real.exp (-(N ^ (τ' / 2)) / 2) =
        (16 * D ^ 3 * (N ^ (Cg + 1) * N ^ D') * Real.exp (-(N ^ (τ' / 2)) / 2)) *
          (N ^ (-D') / 4) := by
      have : N ^ (Cg + 1) * N ^ D' * (N ^ (-D') / 4) = N ^ (Cg + 1) / 4 := by
        rw [mul_assoc, ← mul_div_assoc, hinv]; ring
      calc 4 * D ^ 3 * N ^ (Cg + 1) * Real.exp (-(N ^ (τ' / 2)) / 2)
          = 16 * D ^ 3 * (N ^ (Cg + 1) / 4) * Real.exp (-(N ^ (τ' / 2)) / 2) := by ring
        _ = _ := by rw [← this]; ring
    rw [this]
    exact mul_le_of_le_one_left (by positivity) htail
  -- the Doob part
  set cM := 32 + 54 * D * m₄ with hcM
  have hC₀ : (3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄ ≤ cM * N ^ 2 := by
    have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
    have h1 : (3 + 2 * M₂ + M₁) ^ 2 ≤ 32 + 18 * M₄ := by
      have : 3 + 2 * M₂ + M₁ ≤ 4 + 3 * M₂ := by linarith
      have h2 : (3 + 2 * M₂ + M₁) ^ 2 ≤ (4 + 3 * M₂) ^ 2 :=
        pow_le_pow_left₀ (by linarith) this 2
      nlinarith [sq_nonneg (4 - 3 * M₂)]
    have h3 : 32 + 27 * M₄ ≤ 32 * N ^ 2 + 54 * D * m₄ * N ^ 2 := by nlinarith
    rw [hcM]
    nlinarith
  have hcM0 : 0 ≤ cM := by rw [hcM]; positivity
  have hKh : K * (S / K) ^ 2 ≤ N ^ (-Cg) := by
    have hS2 : S ^ 2 ≤ 1 := pow_le_one₀ hS0.le hS1
    calc K * (S / K) ^ 2 = S ^ 2 / K := by field_simp
      _ ≤ 1 / K := div_le_div_of_nonneg_right hS2 hKpos.le
      _ ≤ 1 / N ^ Cg := one_div_le_one_div_of_le (by positivity) hKlo
      _ = N ^ (-Cg) := by rw [Real.rpow_neg hNpos.le, one_div]
  have hpow : N ^ (30 : ℝ) * N ^ (-Cg) ≤ N ^ (-1 - D') := by
    rw [← Real.rpow_add hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hB2 : (D * B * (S / K)) ^ 2 ≤ D ^ 2 * cB ^ 2 * N ^ 26 * (S / K) ^ 2 := by
    rw [mul_pow, mul_pow]
    have : B ^ 2 ≤ cB ^ 2 * N ^ 26 := by
      have := pow_le_pow_left₀ hB0 hB 2
      calc B ^ 2 ≤ (cB * N ^ 13) ^ 2 := this
        _ = cB ^ 2 * N ^ 26 := by ring
    calc D ^ 2 * B ^ 2 * (S / K) ^ 2 ≤ D ^ 2 * (cB ^ 2 * N ^ 26) * (S / K) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (sq_nonneg D))
            (sq_nonneg _)
      _ = _ := by ring
  have hDb : D * D * D * 2 * (K * ((D * B * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 +
      9 * M₄))) / (1 / (4 * D ^ 3 * N)) ^ 2) ≤ N ^ (-D') / 4 := by
    have hε : (1 / (4 * D ^ 3 * N)) ^ 2 = 1 / (16 * D ^ 6 * N ^ 2) := by ring
    rw [hε, div_div_eq_mul_div, div_one]
    have hX : 0 ≤ (3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄ := by positivity
    calc D * D * D * 2 * (K * ((D * B * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄))) *
          (16 * D ^ 6 * N ^ 2))
        ≤ D * D * D * 2 * (K * ((D ^ 2 * cB ^ 2 * N ^ 26 * (S / K) ^ 2) * (2 * (cM * N ^ 2))) *
          (16 * D ^ 6 * N ^ 2)) := by gcongr
      _ = 64 * D ^ 11 * cB ^ 2 * cM * (N ^ 30 * (K * (S / K) ^ 2)) := by ring
      _ ≤ 64 * D ^ 11 * cB ^ 2 * cM * (N ^ (30 : ℝ) * N ^ (-Cg)) := by
          rw [show (N ^ (30 : ℕ) : ℝ) = N ^ (30 : ℝ) by norm_cast]
          gcongr
      _ ≤ 64 * D ^ 11 * cB ^ 2 * cM * N ^ (-1 - D') := by gcongr
      _ ≤ N ^ (-D') / 4 := by
          rw [show -1 - D' = -D' + -1 by ring, Real.rpow_add hNpos, Real.rpow_neg_one]
          have : 64 * D ^ 11 * cB ^ 2 * cM * (N ^ (-D') * N⁻¹) =
              (64 * D ^ 11 * cB ^ 2 * cM / N) * N ^ (-D') := by ring
          rw [this]
          have h4 : 64 * D ^ 11 * cB ^ 2 * cM / N ≤ 1 / 4 := by
            rw [div_le_iff₀ hNpos]; linarith
          nlinarith
  calc D * D * D * 2 * (2 * K * Real.exp (-(N ^ (τ' / 4)) ^ 2 / 2) +
        K * ((D * B * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄))) /
          (1 / (4 * D ^ 3 * N)) ^ 2)
      = D * D * D * 2 * (2 * K * Real.exp (-(N ^ (τ' / 4)) ^ 2 / 2)) +
        D * D * D * 2 * (K * ((D * B * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄))) /
          (1 / (4 * D ^ 3 * N)) ^ 2) := by ring
    _ ≤ N ^ (-D') / 4 + N ^ (-D') / 4 := add_le_add hA hDb
    _ ≤ N ^ (-D') := by linarith

set_option maxHeartbeats 1600000 in
-- The `2D³` components and the failure probabilities are combined in one declaration.
/-- The martingale part for three resolvents on the grid (Lemma 3.9 [lem_flow_2]), proved from `LF2_comp`, `LF2_csum`, `LF2_thr` and `LF2_prob`. -/
private lemma LF2_mart_core (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∀ Cg : ℝ, 31 + D' ≤ Cg → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ K : ℕ, (N : ℝ) ^ Cg ≤ K → (K : ℝ) ≤ (N : ℝ) ^ (Cg + 1) →
      ∀ z₁ z₂ z₃ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (z₃ = z ∨ z₃ = star z) →
        gridLawA D N K μ₀ {ω | ∃ n : ℕ, n ≤ K ∧
          (∀ j : ℕ, j < n →
            flowGoodAt A z (τ' / 8) (j * (S / K)) (gridStateA D N K (S / K) ω j)) ∧
          (N : ℝ) ^ τ' / (N * (flowTc (lam D N A) z - n * (S / K)) ^ (3 / 2 : ℝ) *
              flowIm (lam D N A) z (n * (S / K)) ^ 3) <
            ten3Norm (fun x y w => ∑ j ∈ Finset.range n,
              (((flowTc (lam D N A) z - (j + 1) * (S / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
                (flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
                    (gridStateA D N K (S / K) ω (j + 1)) x y w -
                  ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
                    (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                      Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y w
                    ∂(gueBlocks D N)))} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD' Cg hCg
  obtain ⟨cR, hcR⟩ := flowLoop_regular
  set m₄ := (∫ y, ‖y‖ ^ 4 ∂(gaussianReal 0 1)) + ∫ z, ‖z‖ ^ 4 ∂(cGauss : Measure ℂ) with hm₄
  have hm₄0 : 0 ≤ m₄ := add_nonneg (integral_nonneg fun y => by positivity)
    (integral_nonneg fun z => by positivity)
  set cB := |cR 3| * (2 * (D : ℝ)) ^ 4 * Real.exp 1 * (4 + τ⁻¹) ^ 2 with hcB
  have hev : ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N ∧ 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧
      c * (N : ℝ) ^ (-εg) ≤ 1 ∧ 8 * Real.exp 1 ^ 2 * (D : ℝ) ^ 4 ≤ (N : ℝ) ^ (11 * τ' / 16) ∧
      16 * (D : ℝ) ^ 3 * (N : ℝ) ^ (Cg + 1 + D') * Real.exp (-((N : ℝ) ^ (τ' / 2)) / 2) ≤ 1 ∧
      256 * (D : ℝ) ^ 11 * cB ^ 2 * (32 + 54 * D * m₄) ≤ N := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    have t3 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (11 * τ' / 16)) Filter.atTop
        Filter.atTop := (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
    refine (Filter.eventually_ge_atTop 2).and (((t1.const_mul 2).eventually
      (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and (((t2.const_mul c).eventually
      (Iic_mem_nhds (by simp : c * 0 < 1))).and ((t3.eventually_ge_atTop _).and
      ((LF2_tail _ _ _ (by positivity)).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop _)))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ₀ hμ₀ A z S hadm K hK1 hK2 z₁ z₂ z₃ h₁ h₂ h₃ => ?_⟩
  obtain ⟨hN2, hAN, hcN, hND, htail, hbig⟩ := hN₀ N hN
  haveI := hμ₀.prob
  haveI : NeZero D := ⟨by omega⟩
  haveI : NeZero N := ⟨by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  obtain ⟨hΛ10, hzτ, hz, hm1, hq0, hq1, hS0, hSt, hη⟩ :=
    LF2_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  have hK1' : 1 ≤ K := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ Cg := Real.one_le_rpow hNr (by linarith)
    exact_mod_cast this.trans hK1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1'
  rcases hS0.eq_or_lt with hS | hSpos
  · -- the degenerate horizon `S = 0`: every one-step fluctuation vanishes
    subst hS
    have hst : ∀ (ω : GridΩA D N K) (j : ℕ), gridStateA D N K (0 / K) ω j = ω.1 := by
      intro ω j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [show ((0 : ℝ) / K) = 0 from zero_div _] at ih ⊢
        simp [gridStateA, ih]
    have hι0 : ∀ n : ℕ, 0 < flowIm (lam D N A) z (n * (0 / K)) := by
      intro n
      rw [zero_div, mul_zero]
      obtain ⟨-, hιeq, hι, -⟩ := LF2_flow D N hD1 hN1 A hΛ10 z hz 0 hSt 0 le_rfl le_rfl
      rw [hιeq]; exact mul_pos (Real.exp_pos _) hι
    refine le_trans (measure_mono (t := ∅) ?_) (by rw [measure_empty]; exact bot_le)
    rintro ω ⟨n, -, -, hlt⟩
    exfalso
    have hzero : (fun x y w => ∑ j ∈ Finset.range n,
        (((flowTc (lam D N A) z - (j + 1) * (0 / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          (flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (0 / K))
              (gridStateA D N K (0 / K) ω (j + 1)) x y w -
            ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (0 / K))
              (Real.exp (-(0 / K) / 2) • gridStateA D N K (0 / K) ω j +
                Real.sqrt (1 - Real.exp (-(0 / K))) • Matrix.of.symm (blockH D N X)) x y w
              ∂(gueBlocks D N))) = fun _ _ _ => 0 := by
      funext x y w
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hst, hst]
      simp
    rw [hzero] at hlt
    have h0 : ten3Norm (fun _ _ _ => (0 : ℂ) : Fin D → Fin D → Fin D → ℂ) = 0 := by
      simp [ten3Norm]
    rw [h0] at hlt
    have := hι0 n
    have hq : 0 < (flowTc (lam D N A) z - n * (0 / K)) ^ (3 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (by simp [hq0]) _
    have : 0 < (N : ℝ) ^ τ' / (N * (flowTc (lam D N A) z - n * (0 / K)) ^ (3 / 2 : ℝ) *
        flowIm (lam D N A) z (n * (0 / K)) ^ 3) := by positivity
    linarith
  -- the moments of the GUE blocks
  set γ := gueBlocks D N with hγ
  set M₁ := ∫ w, ‖w‖ ∂γ with hM₁
  set M₂ := ∫ w, ‖w‖ ^ 2 ∂γ with hM₂
  set M₄ := ∫ w, ‖w‖ ^ 4 ∂γ with hM₄
  have hi4 := LF2_int_pow D N 4
  have hi2 := LF2_int_pow D N 2
  have hM₁0 : 0 ≤ M₁ := integral_nonneg fun w => norm_nonneg _
  have hM₂0 : 0 ≤ M₂ := integral_nonneg fun w => by positivity
  have hM₄0 : 0 ≤ M₄ := integral_nonneg fun w => by positivity
  have hM₁2 : M₁ ≤ 1 + M₂ := by
    have hi1 : Integrable (fun w : Fin D → Coords N => ‖w‖) γ := by
      have := LF2_int_pow D N 1; simp only [pow_one] at this; exact this
    calc M₁ ≤ ∫ w, (1 + ‖w‖ ^ 2) ∂γ := integral_mono hi1 ((integrable_const 1).add hi2)
          fun w => by nlinarith [sq_nonneg (‖w‖ - 1), norm_nonneg w]
      _ = 1 + M₂ := by rw [integral_add (integrable_const 1) hi2]; simp [hM₂, hγ]
  have hM₂4 : M₂ ^ 2 ≤ M₄ := by
    have h0 : 0 ≤ ∫ w, (‖w‖ ^ 2 - M₂) ^ 2 ∂γ := integral_nonneg fun w => sq_nonneg _
    have e : ∀ w : Fin D → Coords N, (‖w‖ ^ 2 - M₂) ^ 2 = ‖w‖ ^ 4 - 2 * M₂ * ‖w‖ ^ 2 + M₂ ^ 2 :=
      fun w => by ring
    simp only [e] at h0
    have i1 : Integrable (fun w : Fin D → Coords N => ‖w‖ ^ 4 - 2 * M₂ * ‖w‖ ^ 2) γ :=
      hi4.sub (hi2.const_mul _)
    have e1 : ∫ w, (‖w‖ ^ 4 - 2 * M₂ * ‖w‖ ^ 2 + M₂ ^ 2) ∂γ = M₄ - 2 * M₂ * M₂ + M₂ ^ 2 := by
      rw [integral_add i1 (integrable_const _), integral_sub hi4 (hi2.const_mul _),
        integral_const_mul]
      simp [hM₂, hM₄, hγ]
    rw [e1] at h0
    nlinarith
  have hM₄m : M₄ ≤ 2 * D * (N : ℝ) ^ 2 * m₄ := by
    refine (LF2_moment4 D N).trans ?_
    have h1 : (D : ℝ) * N ≤ D * N ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have : (D : ℝ) * N + D * N * N ≤ 2 * D * N ^ 2 := by
      calc (D : ℝ) * N + D * N * N = D * N + D * N ^ 2 := by ring
        _ ≤ D * N ^ 2 + D * N ^ 2 := by linarith
        _ = 2 * D * N ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right this hm₄0
  -- the components
  have hhK : (K : ℝ) * (S / K) = S := by field_simp
  have hcomp : ∀ (x y w : Fin D) (b : Bool), ∃ Bad : Set (GridΩA D N K),
      (gridLawA D N K μ₀).real Bad ≤ 2 * K * Real.exp (-((N : ℝ) ^ (τ' / 4)) ^ 2 / 2) +
        K * ((D * (cB * (N : ℝ) ^ 13) * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 +
          9 * M₄))) / (1 / (4 * (D : ℝ) ^ 3 * N)) ^ 2 ∧
      ∀ ω ∉ Bad, (Matrix.of ω.1).IsHermitian → ∀ n : ℕ, n ≤ K →
        (∀ j : ℕ, j < n →
          flowGoodAt A z (τ' / 8) (j * (S / K)) (gridStateA D N K (S / K) ω j)) →
        |∑ j ∈ Finset.range n, (if b then Complex.imCLM else Complex.reCLM)
          ((((flowTc (lam D N A) z - (j + 1) * (S / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          (flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) x y w -
            ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y w
              ∂(gueBlocks D N)))| ≤
          (N : ℝ) ^ (τ' / 4) * Real.sqrt (∑ k ∈ Finset.range n,
            (if k < K then 9 * D ^ 2 * (S / K) * (N : ℝ) ^ (τ' / 8) /
              ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - k * (S / K)) ^ 4 *
                flowIm (lam D N A) z (k * (S / K)) ^ 6) else 1)) +
            1 / (4 * (D : ℝ) ^ 3 * N) := by
    intro x y w b
    have hlf : ∀ f ∈ LF2_l (N := N) z₁ z₂ z₃ x y w, f.2 = z ∨ f.2 = star z := by
      intro f hf
      simp only [LF2_l, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl
      exacts [h₁, h₂, h₃]
    obtain ⟨Ft, hder, hreg⟩ := hcR D N (lam D N A) (lam_isHermitian D N A) z hz
      (LF2_l z₁ z₂ z₃ x y w) hlf S hS0 hSt
    set B := cR (LF2_l (N := N) z₁ z₂ z₃ x y w).length * ((D : ℝ) * N + 1) ^ 4 *
      Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      ((LF2_l (N := N) z₁ z₂ z₃ x y w).map fun f => opNorm f.1).prod *
      ((min 1 (charFlowZ (lam D N A) z S).im) ^
        ((LF2_l (N := N) z₁ z₂ z₃ x y w).length + 6))⁻¹ with hB
    have hB0 : 0 ≤ B := (norm_nonneg _).trans
      ((hreg 0 ⟨le_rfl, hS0⟩).2.2.1 1 le_rfl (by norm_num) 0).1
    have hBle : B ≤ cB * (N : ℝ) ^ 13 := by
      have hηS := (hη S hS0 le_rfl).1
      have hBeq : B = cR 3 * ((D : ℝ) * N + 1) ^ 4 * Real.exp (flowTc (lam D N A) z) *
          (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
          (opNorm (Ea D N w) * (opNorm (Ea D N x) * opNorm (Ea D N y))) *
          ((min 1 (charFlowZ (lam D N A) z S).im) ^ 9)⁻¹ := by
        rw [hB]
        simp only [LF2_l, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, mul_one]
      rw [hBeq]
      refine (LF2_ar_B (cR 3) D N (Real.exp (flowTc (lam D N A) z))
        (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A))
        (opNorm (Ea D N w) * (opNorm (Ea D N x) * opNorm (Ea D N y)))
        (min 1 (charFlowZ (lam D N A) z S).im) τ
        hDr (by exact_mod_cast hN2) (Real.exp_le_exp.2 hq1) (Real.exp_pos _).le
        (by have h1 := norm_nonneg z; have h2 := norm_nonneg (mExt (lam D N A) z)
            have h3 := LF2_op_nonneg (lam D N A); linarith only [h1, h2, h3])
        (by linarith only [hzτ, hm1, hΛ10])
        (mul_nonneg (LF2_op_nonneg _) (mul_nonneg (LF2_op_nonneg _) (LF2_op_nonneg _)))
        ((mul_le_mul (LF2_opNorm_Ea D N w) ((mul_le_mul (LF2_opNorm_Ea D N x)
          (LF2_opNorm_Ea D N y) (LF2_op_nonneg _) zero_le_one).trans_eq (one_mul 1))
          (mul_nonneg (LF2_op_nonneg _) (LF2_op_nonneg _)) zero_le_one).trans_eq (one_mul 1))
        (le_min (inv_le_one_of_one_le₀ (by linarith)) hηS.le)).trans (le_of_eq ?_)
      rw [hcB]; ring
    have hℓ : ∀ w : ℂ, |(if b then Complex.imCLM else Complex.reCLM) w| ≤ ‖w‖ := by
      intro w
      cases b
      · simpa using Complex.abs_re_le_norm w
      · simpa using Complex.abs_im_le_norm w
    obtain ⟨Bad, hBadμ, hBad⟩ := LF2_comp D N K hK1' μ₀ A z S hΛ10 hz hSpos hSt hq1
      (fun s hs0 hsS => (hη s hs0 hsS).1) (τ' / 8) z₁ z₂ z₃ h₁ h₂ h₃ x y w _ hℓ Ft B hder
      (fun s hs => ⟨(hreg s hs).1, (hreg s hs).2.1, (hreg s hs).2.2.1⟩)
      ((N : ℝ) ^ (τ' / 4)) (1 / (4 * (D : ℝ) ^ 3 * N)) (Real.rpow_pos_of_pos hNpos _)
      (by positivity)
    refine ⟨Bad, hBadμ.trans ?_, hBad⟩
    gcongr
  choose Bad hBadμ hBad using hcomp
  set PB := 2 * K * Real.exp (-((N : ℝ) ^ (τ' / 4)) ^ 2 / 2) +
    K * ((D * (cB * (N : ℝ) ^ 13) * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 +
      9 * M₄))) / (1 / (4 * (D : ℝ) ^ 3 * N)) ^ 2 with hPB
  have hPBle : (D : ℝ) * D * D * 2 * PB ≤ (N : ℝ) ^ (-D') := by
    rw [hPB]
    exact LF2_prob D N K Cg D' τ' cB m₄ S (cB * (N : ℝ) ^ 13) M₁ M₂ M₄ hDr hNr hK1 hK2 hD' hCg
      hSpos (le_trans hSt.le hq1) (by
        have : 0 ≤ cB := by rw [hcB]; positivity
        positivity) le_rfl hm₄0 hM₁0 hM₂0 hM₁2 hM₂4 hM₄0 hM₄m htail hbig
  set NH := {ω : GridΩA D N K | ¬ (Matrix.of ω.1).IsHermitian} with hNH
  have hNH0 : gridLawA D N K μ₀ NH = 0 := by
    have hT : MeasurableSet {H : Idx D N → Idx D N → ℂ | ¬ (Matrix.of H).IsHermitian} :=
      LF2_herm_meas.compl
    have e : NH = Prod.fst ⁻¹' {H : Idx D N → Idx D N → ℂ | ¬ (Matrix.of H).IsHermitian} := rfl
    rw [e, ← Measure.map_apply measurable_fst hT]
    unfold gridLawA
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_iff.1 hμ₀.herm
  -- the event lies in the union of the bad sets of the components and of `NH`
  refine (measure_mono (t := (⋃ p : Fin D × Fin D × Fin D × Bool,
    Bad p.1 p.2.1 p.2.2.1 p.2.2.2) ∪ NH) ?_).trans ?_
  · rintro ω ⟨n, hn, hgood, hlt⟩
    by_contra hω
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, hNH, Set.mem_ofPred_eq,
      not_not] at hω
    obtain ⟨hω1, hherm⟩ := hω
    set T := (N : ℝ) ^ (τ' / 4) * Real.sqrt (∑ k ∈ Finset.range n,
      (if k < K then 9 * D ^ 2 * (S / K) * (N : ℝ) ^ (τ' / 8) /
        ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - k * (S / K)) ^ 4 *
          flowIm (lam D N A) z (k * (S / K)) ^ 6) else 1)) + 1 / (4 * (D : ℝ) ^ 3 * N) with hT
    have hre : ∀ x y w : Fin D, |(∑ j ∈ Finset.range n,
        (((flowTc (lam D N A) z - (j + 1) * (S / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          (flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) x y w -
            ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y w
              ∂(gueBlocks D N))).re| +
        |(∑ j ∈ Finset.range n,
        (((flowTc (lam D N A) z - (j + 1) * (S / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          (flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) x y w -
            ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y w
              ∂(gueBlocks D N))).im| ≤ 2 * T := by
      intro x y w
      rw [Complex.re_sum, Complex.im_sum]
      have h1 := hBad x y w false ω (hω1 (x, y, w, false)) hherm n hn hgood
      have h2 := hBad x y w true ω (hω1 (x, y, w, true)) hherm n hn hgood
      simp only [Bool.false_eq_true, ↓reduceIte, Complex.reCLM_apply,
        Complex.imCLM_apply] at h1 h2
      linarith
    have hsum := (LF2_ten_le _).trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      Finset.sum_le_sum fun w _ => hre x y w)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    -- the threshold
    have hnS : (n : ℝ) * (S / K) ≤ S := by
      have hnK : (n : ℝ) ≤ K := by exact_mod_cast hn
      calc (n : ℝ) * (S / K) ≤ K * (S / K) :=
            mul_le_mul_of_nonneg_right hnK (by positivity)
        _ = S := hhK
    obtain ⟨-, hιeq, hι0, hι1, -, -, -⟩ := LF2_flow D N hD1 hN1 A hΛ10 z hz S hSt (n * (S / K))
      (by positivity) hnS
    have hιn : 0 < flowIm (lam D N A) z (n * (S / K)) := by
      rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
    have hqn : 0 < flowTc (lam D N A) z - n * (S / K) := by linarith
    have hqn1 : flowTc (lam D N A) z - n * (S / K) ≤ 1 := by
      have : 0 ≤ (n : ℝ) * (S / K) := by positivity
      linarith
    have hcs := LF2_csum D N K hD1 hN1 A hΛ10 z hz S hSt hq1 (S / K) (by positivity) hhK
      (τ' / 8) n hn
    have hp2 : ((flowTc (lam D N A) z - n * (S / K)) ^ (3 / 2 : ℝ)) ^ 2 =
        (flowTc (lam D N A) z - n * (S / K)) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hqn.le]; norm_num
    rw [← hp2] at hcs
    have hthr := LF2_thr D N τ' ((flowTc (lam D N A) z - n * (S / K)) ^ (3 / 2 : ℝ))
      (flowIm (lam D N A) z (n * (S / K))) _ hDr hNr hτ' (Real.rpow_pos_of_pos hqn _)
      (Real.rpow_le_one hqn.le hqn1 (by norm_num)) hιn hι1.le (Finset.sum_nonneg fun k _ => by
        split_ifs with hk
        · have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk.le
          have hSK : 0 ≤ S / K := by positivity
          have hkS : (k : ℝ) * (S / K) ≤ S :=
            (mul_le_mul_of_nonneg_right hkK hSK).trans_eq hhK
          have hk00 : 0 ≤ (k : ℝ) * (S / K) := by positivity
          have h1 := (LF2_flow D N hD1 hN1 A hΛ10 z hz S hSt (k * (S / K)) hk00 hkS).2.1
          have hk0 : 0 < flowTc (lam D N A) z - k * (S / K) := by linarith
          have := Real.rpow_nonneg hNpos.le (τ' / 8)
          positivity
        · exact zero_le_one) hcs hND
    have e3 : (D : ℝ) * (D * (D * (2 * T))) = 2 * D ^ 3 * T := by ring
    rw [e3] at hsum
    linarith
  · refine (measure_union_le _ _).trans ?_
    rw [hNH0, add_zero]
    refine (measure_iUnion_fintype_le _ _).trans ?_
    calc ∑ p : Fin D × Fin D × Fin D × Bool, gridLawA D N K μ₀ (Bad p.1 p.2.1 p.2.2.1 p.2.2.2)
        ≤ ∑ _p : Fin D × Fin D × Fin D × Bool, ENNReal.ofReal PB := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal (hBadμ p.1 p.2.1 p.2.2.1 p.2.2.2)
      _ = ENNReal.ofReal ((D : ℝ) * D * D * 2 * PB) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
            Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
          rw [ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show ((D : ℝ) * D * D * 2) = ((D * (D * (D * 2)) : ℕ) : ℝ) by push_cast; ring,
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal hPBle

private def LF2_R {D : ℕ} (X : Matrix (Fin D) (Fin D) ℂ) (θ r : ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  (1 - ((Real.exp r : ℝ) : ℂ) • X * PTheta D (1 - Real.exp (-r) * (1 - θ)))⁻¹ *
    (((Real.exp r : ℝ) : ℂ) • X)

/-- Along the flow on `[0, S]`: `K_{θ_t}(z_{1,t}, z_{2,t})` is the closed form `LF2_R`, it solves
`dK/dt = K² + K` entrywise, and `‖(t_c - t₀ - t) K_{θ_t}‖ ≤ 1`, so its entries are at most
`(t_c - t₀ - t)⁻¹`. -/
private lemma LF2_flowK (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (t : ℝ) (ht0 : 0 ≤ t)
    (htS : t ≤ S) :
    flowKmat (lam D N A) θ z₁ z₂ t = LF2_R (Mhat (lam D N A) z₁ z₂) θ t ∧
      (∀ a b : Fin D, HasDerivAt (fun r => LF2_R (Mhat (lam D N A) z₁ z₂) θ r a b)
        ((LF2_R (Mhat (lam D N A) z₁ z₂) θ t * LF2_R (Mhat (lam D N A) z₁ z₂) θ t +
          LF2_R (Mhat (lam D N A) z₁ z₂) θ t) a b) t) ∧
      ∀ a b : Fin D, ‖flowKmat (lam D N A) θ z₁ z₂ t a b‖ ≤ (flowTc (lam D N A) z - t)⁻¹ := by
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hΛ := lam_isHermitian D N A
  have ht : t < flowTc (lam D N A) z := lt_of_le_of_lt htS hS
  obtain ⟨hηt, -, -, -, -, htc, -⟩ := LF2_flow D N hD1 hN1 A hA z hz S hS t ht0 htS
  have hMh := Mhat_flow (lam D N A) hΛ z hz t ht z₁ z₂ h₁ h₂
  have hθt : Real.exp (-t) * θ + 1 - Real.exp (-t) = 1 - Real.exp (-t) * (1 - θ) := by ring
  have hK : flowKmat (lam D N A) θ z₁ z₂ t = LF2_R (Mhat (lam D N A) z₁ z₂) θ t := by
    simp only [flowKmat, KTheta, LF2_R, hMh, hθt]
  -- the operator bound at the flowed point
  set A' : Matrix (Fin N) (Fin N) ℂ := ((Real.exp (-t / 2) : ℝ) : ℂ) • A with hA'
  have hlam : lam D N A' = ((Real.exp (-t / 2) : ℝ) : ℂ) • lam D N A :=
    (LF2_lam_smul D N A _).symm
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
    have h1 := LF2_entry_le (((flowTc (lam D N A) z - t : ℝ) : ℂ) •
      flowKmat (lam D N A) θ z₁ z₂ t) a b
    have h2 := h1.trans hop
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hq] at h2
    have h3 := (le_div_iff₀' hq).2 h2
    rwa [one_div] at h3

/-! ### The deterministic side: (3.19) [eq:whMK3] and the three-resolvent Riccati equation -/

section LF2_P

open scoped Matrix.Norms.L2Operator

/-- `‖1‖ ≤ 1` for the operator norm. -/
private lemma LF2_op_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

/-- `‖P_θ‖ ≤ 1` for `θ ∈ [0, 1]`: `P_θ = θ I + (1 - θ) J/D` with `J/D` an orthogonal projection. -/
private lemma LF2_P_norm (D : ℕ) [NeZero D] (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    opNorm (PTheta D θ) ≤ 1 := by
  have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne D)
  have hDc : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne D)
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
    rw [LF2_op_eq]
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
  have := LF2_op_one (ι := Fin D)
  nlinarith

end LF2_P

/-- `(1 - e^r X P_{θ_r})⁻¹`, `θ_r = 1 - e^{-r}(1 - θ)`, the resolvent factor of (3.19)
[eq:whMK3] along the flow with `X = M̂(z_i, z_j)`. -/
private def LF2_U {D : ℕ} (X : Matrix (Fin D) (Fin D) ℂ) (θ r : ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  (1 - ((Real.exp r : ℝ) : ℂ) • X * PTheta D (1 - Real.exp (-r) * (1 - θ)))⁻¹

/-- Along the flow on `[0, S]`: `1 - e^t X P_{θ_t}` is invertible for `X = M̂(z₁, z₂)`,
`‖K_{θ_t}‖ ≤ (t_c - t₀ - t)⁻¹` and `‖(1 - e^t X P_{θ_t})⁻¹‖ ≤ 1 + (t_c - t₀ - t)⁻¹`. -/
private lemma LF2_flowU (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (t : ℝ) (ht0 : 0 ≤ t)
    (htS : t ≤ S) :
    (1 - ((Real.exp t : ℝ) : ℂ) • Mhat (lam D N A) z₁ z₂ *
        PTheta D (1 - Real.exp (-t) * (1 - θ))).det ≠ 0 ∧
      opNorm (LF2_R (Mhat (lam D N A) z₁ z₂) θ t) ≤ (flowTc (lam D N A) z - t)⁻¹ ∧
      opNorm (LF2_U (Mhat (lam D N A) z₁ z₂) θ t) ≤ 1 + (flowTc (lam D N A) z - t)⁻¹ := by
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hΛ := lam_isHermitian D N A
  have ht : t < flowTc (lam D N A) z := lt_of_le_of_lt htS hS
  obtain ⟨hηt, -, -, -, -, htc, -⟩ := LF2_flow D N hD1 hN1 A hA z hz S hS t ht0 htS
  have hMh := Mhat_flow (lam D N A) hΛ z hz t ht z₁ z₂ h₁ h₂
  have hθt : Real.exp (-t) * θ + 1 - Real.exp (-t) = 1 - Real.exp (-t) * (1 - θ) := by ring
  set A' : Matrix (Fin N) (Fin N) ℂ := ((Real.exp (-t / 2) : ℝ) : ℂ) • A with hA'
  have hlam : lam D N A' = ((Real.exp (-t / 2) : ℝ) : ℂ) • lam D N A :=
    (LF2_lam_smul D N A _).symm
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
  have hq : 0 < flowTc (lam D N A) z - t := by linarith
  have hdet' : (1 - ((Real.exp t : ℝ) : ℂ) • Mhat (lam D N A) z₁ z₂ *
      PTheta D (1 - Real.exp (-t) * (1 - θ))).det ≠ 0 := by
    rw [hMh, hθt] at hdet
    exact hdet
  have hK : KTheta (((Real.exp (-t / 2) : ℝ) : ℂ) • lam D N A)
      (Real.exp (-t) * θ + 1 - Real.exp (-t))
      (charFlowZ (lam D N A) z₁ t) (charFlowZ (lam D N A) z₂ t) =
      LF2_R (Mhat (lam D N A) z₁ z₂) θ t := by
    simp only [KTheta, LF2_R, hMh, hθt]
  rw [hK] at hop
  have hR : opNorm (LF2_R (Mhat (lam D N A) z₁ z₂) θ t) ≤ (flowTc (lam D N A) z - t)⁻¹ := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] at hop
    calc opNorm (LF2_R (Mhat (lam D N A) z₁ z₂) θ t) =
        (flowTc (lam D N A) z - t)⁻¹ * ((flowTc (lam D N A) z - t) *
          opNorm (LF2_R (Mhat (lam D N A) z₁ z₂) θ t)) := by field_simp
      _ ≤ (flowTc (lam D N A) z - t)⁻¹ * 1 := mul_le_mul_of_nonneg_left hop (inv_nonneg.2 hq.le)
      _ = _ := mul_one _
  refine ⟨hdet', hR, ?_⟩
  -- `U = 1 + K P`
  set X := ((Real.exp t : ℝ) : ℂ) • Mhat (lam D N A) z₁ z₂ with hX
  set P := PTheta D (1 - Real.exp (-t) * (1 - θ)) with hP
  have hUnit : IsUnit (1 - X * P).det := isUnit_iff_ne_zero.2 hdet'
  have hUe : LF2_U (Mhat (lam D N A) z₁ z₂) θ t = 1 + LF2_R (Mhat (lam D N A) z₁ z₂) θ t * P := by
    simp only [LF2_U, LF2_R, ← hX, ← hP]
    have h1 : (1 - X * P)⁻¹ * (1 - X * P) = 1 := Matrix.nonsing_inv_mul _ hUnit
    rw [Matrix.mul_assoc]
    calc (1 - X * P)⁻¹ = (1 - X * P)⁻¹ * (1 - X * P) + (1 - X * P)⁻¹ * (X * P) := by
          rw [← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]
      _ = 1 + (1 - X * P)⁻¹ * (X * P) := by rw [h1]
  rw [hUe]
  have hPn := LF2_P_norm D (1 - Real.exp (-t) * (1 - θ)) (by nlinarith) (by nlinarith)
  refine (opNorm_add_le _ _).trans ?_
  have h2 := (LF2_op_mul (LF2_R (Mhat (lam D N A) z₁ z₂) θ t) P)
  have h3 := LF2_op_nonneg (LF2_R (Mhat (lam D N A) z₁ z₂) θ t)
  have h4 : opNorm (LF2_R (Mhat (lam D N A) z₁ z₂) θ t) * opNorm P ≤
      (flowTc (lam D N A) z - t)⁻¹ * 1 := mul_le_mul hR hPn (LF2_op_nonneg _) (by positivity)
  have := LF2_op_one (ι := Fin D)
  linarith

/-- `M(z_{i,s}, Λ_s) = e^{s/2} M(z_i, Λ)` along the flow for `z_i ∈ {z, z̄}`. -/
private lemma LF2_Mflow {D N : ℕ} [NeZero D] [NeZero N] (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc Λ z) (w : ℂ)
    (hw : w = z ∨ w = star z) :
    MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ w s) =
      ((Real.exp (s / 2) : ℝ) : ℂ) • MExt Λ w := by
  have hN : Nonempty (Idx D N) := ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩,
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩)⟩
  obtain ⟨hpos, hMz, -⟩ := charFlow_M Λ hΛ z hz s hs
  rcases hw with rfl | rfl
  · exact hMz
  · have hΛs := LF2_herm_smul Λ hΛ (Real.exp (-s / 2))
    rw [charFlowZ_conj _ z hz s, (mExt_conj _ hΛs _ hpos.ne').2, hMz,
      (mExt_conj _ hΛ _ hz.ne').2, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]

/-- `‖M(z_i)‖ ≤ 5/4` for `z_i ∈ {z, z̄}` and `‖Λ‖ ≤ 1/10`. -/
private lemma LF2_M_le {D N : ℕ} [NeZero D] [NeZero N] (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (hA : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (w : ℂ)
    (hw : w = z ∨ w = star z) : opNorm (MExt Λ w) ≤ 5 / 4 := by
  have hN : Nonempty (Idx D N) := ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩,
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩)⟩
  have hMz : opNorm (MExt Λ z) ≤ 5 / 4 := by
    have e : MExt Λ z = MSol Λ z := by simp [MExt, MSol, mExt, hz]
    rw [e]
    have h1 := (mSol_apriori Λ hΛ hA z hz).2.2
    have h0 := LF2_op_nonneg Λ
    have h2 : (1 - 2 * opNorm Λ)⁻¹ ≤ 5 / 4 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  rcases hw with rfl | rfl
  · exact hMz
  · rw [(mExt_conj _ hΛ _ hz.ne').2, LF2_op_conj]
    exact hMz

/-- `⟨(cA) E (cB) E' (cC) E''⟩ = c³ ⟨A E B E' C E''⟩`. -/
private lemma LF2_ntr_smul3 {ι : Type*} [Fintype ι] (c : ℂ) (A B C E E' E'' : Matrix ι ι ℂ) :
    ntr ((c • A) * E * (c • B) * E' * (c • C) * E'') = c ^ 3 * ntr (A * E * B * E' * C * E'') := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

/-- `K_{θ_t}(z_{1,t}, z_{2,t}, z_{3,t})` along the flow is the closed form of (3.19) [eq:whMK3]:
`Σ U¹² U²³ U³¹ (e^{3t/2} T)` with `U^{ij} = (1 - e^t M̂_{ij} P_{θ_t})⁻¹` and
`T_{b₁b₂b₃} = D ⟨M₁ E_{b₁} M₂ E_{b₂} M₃ E_{b₃}⟩` at the start. -/
private lemma LF2_flowK3_eq (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (θ : ℝ) (z₁ z₂ z₃ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (h₃ : z₃ = z ∨ z₃ = star z) (t : ℝ)
    (ht : t < flowTc (lam D N A) z) :
    flowKten3 (lam D N A) θ z₁ z₂ z₃ t = ten3Contr (LF2_U (Mhat (lam D N A) z₁ z₂) θ t)
      (LF2_U (Mhat (lam D N A) z₂ z₃) θ t) (LF2_U (Mhat (lam D N A) z₃ z₁) θ t)
      (fun b₁ b₂ b₃ => ((Real.exp (3 * t / 2) : ℝ) : ℂ) * ((D : ℂ) *
        ntr (MExt (lam D N A) z₁ * Ea D N b₁ * MExt (lam D N A) z₂ * Ea D N b₂ *
          MExt (lam D N A) z₃ * Ea D N b₃))) := by
  have hΛ := lam_isHermitian D N A
  have hθt : Real.exp (-t) * θ + 1 - Real.exp (-t) = 1 - Real.exp (-t) * (1 - θ) := by ring
  have he : ((Real.exp (t / 2) : ℝ) : ℂ) ^ 3 = ((Real.exp (3 * t / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul,
      show ((3 : ℕ) : ℝ) * (t / 2) = 3 * t / 2 by push_cast; ring]
  simp only [flowKten3, KTheta3, LF2_U, Mhat_flow (lam D N A) hΛ z hz t ht z₁ z₂ h₁ h₂,
    Mhat_flow (lam D N A) hΛ z hz t ht z₂ z₃ h₂ h₃, Mhat_flow (lam D N A) hΛ z hz t ht z₃ z₁ h₃ h₁,
    hθt, LF2_Mflow (lam D N A) hΛ z hz t ht z₁ h₁, LF2_Mflow (lam D N A) hΛ z hz t ht z₂ h₂,
    LF2_Mflow (lam D N A) hΛ z hz t ht z₃ h₃, LF2_ntr_smul3, he]
  congr 1
  funext b₁ b₂ b₃
  ring

/-- `|(Σ U¹ U² U³ T)_{xyw}| ≤ D³ u³ τ` from entry bounds `u` on the `U^i` and `τ` on `T`. -/
private lemma LF2_contr_le {D : ℕ} (U₁ U₂ U₃ : Matrix (Fin D) (Fin D) ℂ)
    (T : Fin D → Fin D → Fin D → ℂ) (u τ : ℝ) (hu1 : ∀ i j, ‖U₁ i j‖ ≤ u)
    (hu2 : ∀ i j, ‖U₂ i j‖ ≤ u) (hu3 : ∀ i j, ‖U₃ i j‖ ≤ u) (hT : ∀ a b c, ‖T a b c‖ ≤ τ)
    (x y w : Fin D) : ‖ten3Contr U₁ U₂ U₃ T x y w‖ ≤ D ^ 3 * (u ^ 3 * τ) := by
  have hu0 : 0 ≤ u := (norm_nonneg _).trans (hu1 x x)
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans (hT x x x)
  unfold ten3Contr
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b₁, ‖∑ b₂, ∑ b₃, U₁ x b₁ * U₂ y b₂ * U₃ w b₃ * T b₁ b₂ b₃‖
      ≤ ∑ _b₁ : Fin D, ∑ _b₂ : Fin D, ∑ _b₃ : Fin D, u ^ 3 * τ := by
        refine Finset.sum_le_sum fun b₁ _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun b₂ _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun b₃ _ => ?_))
        rw [norm_mul, norm_mul, norm_mul]
        have := mul_le_mul (mul_le_mul (hu1 x b₁) (hu2 y b₂) (norm_nonneg _) hu0) (hu3 w b₃)
          (norm_nonneg _) (by positivity)
        calc ‖U₁ x b₁‖ * ‖U₂ y b₂‖ * ‖U₃ w b₃‖ * ‖T b₁ b₂ b₃‖ ≤ u * u * u * τ :=
              mul_le_mul this (hT _ _ _) (norm_nonneg _) (by positivity)
          _ = u ^ 3 * τ := by ring
    _ = D ^ 3 * (u ^ 3 * τ) := by simp; ring

/-- Along the flow on `[0, S]`, `t_c - t₀ ≤ 1`: the entries of `K_{θ_t}(z_{1,t}, z_{2,t}, z_{3,t})`
are at most `κ = 2 D⁴ e² (1 + ρ)³`, `ρ = (t_c - t₀ - S)⁻¹`, and they solve
`dK_{xyw}/dt = (3/2) K_{xyw} + Σ_a (K¹²_{xa} K_{ayw} + K²³_{ya} K_{xaw} + K³¹_{wa} K_{xya})`. -/
private lemma LF2_flowK3 (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (hq1 : flowTc (lam D N A) z ≤ 1) (θ : ℝ) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) (z₁ z₂ z₃ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z)
    (h₃ : z₃ = z ∨ z₃ = star z) (t : ℝ) (ht0 : 0 ≤ t) (htS : t ≤ S) (x y w : Fin D) :
    HasDerivAt (fun r => ten3Contr (LF2_U (Mhat (lam D N A) z₁ z₂) θ r)
        (LF2_U (Mhat (lam D N A) z₂ z₃) θ r) (LF2_U (Mhat (lam D N A) z₃ z₁) θ r)
        (fun b₁ b₂ b₃ => ((Real.exp (3 * r / 2) : ℝ) : ℂ) * ((D : ℂ) *
          ntr (MExt (lam D N A) z₁ * Ea D N b₁ * MExt (lam D N A) z₂ * Ea D N b₂ *
            MExt (lam D N A) z₃ * Ea D N b₃))) x y w)
      ((3 / 2 : ℂ) * flowKten3 (lam D N A) θ z₁ z₂ z₃ t x y w + ∑ a,
        (flowKmat (lam D N A) θ z₁ z₂ t x a * flowKten3 (lam D N A) θ z₁ z₂ z₃ t a y w +
          flowKmat (lam D N A) θ z₂ z₃ t y a * flowKten3 (lam D N A) θ z₁ z₂ z₃ t x a w +
          flowKmat (lam D N A) θ z₃ z₁ t w a * flowKten3 (lam D N A) θ z₁ z₂ z₃ t x y a)) t ∧
      ‖flowKten3 (lam D N A) θ z₁ z₂ z₃ t x y w‖ ≤
        2 * D ^ 4 * Real.exp 1 ^ 2 * (1 + (flowTc (lam D N A) z - S)⁻¹) ^ 3 := by
  have ht : t < flowTc (lam D N A) z := lt_of_le_of_lt htS hS
  obtain ⟨hd₁, -, hU₁⟩ := LF2_flowU D N A hA z hz S hS θ hθ₀ hθ₁ z₁ z₂ h₁ h₂ t ht0 htS
  obtain ⟨hd₂, -, hU₂⟩ := LF2_flowU D N A hA z hz S hS θ hθ₀ hθ₁ z₂ z₃ h₂ h₃ t ht0 htS
  obtain ⟨hd₃, -, hU₃⟩ := LF2_flowU D N A hA z hz S hS θ hθ₀ hθ₁ z₃ z₁ h₃ h₁ t ht0 htS
  have hK₁ := (LF2_flowK D N A hA z hz S hS θ hθ₀ hθ₁ z₁ z₂ h₁ h₂ t ht0 htS).1
  have hK₂ := (LF2_flowK D N A hA z hz S hS θ hθ₀ hθ₁ z₂ z₃ h₂ h₃ t ht0 htS).1
  have hK₃ := (LF2_flowK D N A hA z hz S hS θ hθ₀ hθ₁ z₃ z₁ h₃ h₁ t ht0 htS).1
  have hE := LF2_flowK3_eq D N A z hz θ z₁ z₂ z₃ h₁ h₂ h₃ t ht
  refine ⟨?_, ?_⟩
  · have hU : ∀ X ∈ ({Mhat (lam D N A) z₁ z₂, Mhat (lam D N A) z₂ z₃, Mhat (lam D N A) z₃ z₁} :
        Set (Matrix (Fin D) (Fin D) ℂ)),
        (1 - ((Real.exp t : ℝ) : ℂ) • X * PTheta D (1 - Real.exp (-t) * (1 - θ))).det ≠ 0 := by
      intro X hX
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl | rfl
      exacts [hd₁, hd₂, hd₃]
    have h := kTheta3_riccati D (Mhat (lam D N A) z₁ z₂) (Mhat (lam D N A) z₂ z₃)
      (Mhat (lam D N A) z₃ z₁) (fun b₁ b₂ b₃ => (D : ℂ) *
        ntr (MExt (lam D N A) z₁ * Ea D N b₁ * MExt (lam D N A) z₂ * Ea D N b₂ *
          MExt (lam D N A) z₃ * Ea D N b₃)) θ t hU x y w
    refine h.congr_deriv ?_
    simp only [hE, hK₁, hK₂, hK₃, LF2_U, LF2_R]
  · have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
    have hΛ := lam_isHermitian D N A
    have hqS : 0 < flowTc (lam D N A) z - S := by linarith
    have hρ : 1 + (flowTc (lam D N A) z - t)⁻¹ ≤ 1 + (flowTc (lam D N A) z - S)⁻¹ := by
      have := inv_anti₀ hqS (show flowTc (lam D N A) z - S ≤ flowTc (lam D N A) z - t by linarith)
      linarith
    have hu : ∀ (U : Matrix (Fin D) (Fin D) ℂ), opNorm U ≤ 1 + (flowTc (lam D N A) z - t)⁻¹ →
        ∀ i j, ‖U i j‖ ≤ 1 + (flowTc (lam D N A) z - S)⁻¹ :=
      fun U hU i j => ((LF2_entry_le U i j).trans hU).trans hρ
    have hM := fun w hw => LF2_M_le (lam D N A) hΛ hA z hz w hw
    have hT : ∀ a b c : Fin D, ‖((Real.exp (3 * t / 2) : ℝ) : ℂ) * ((D : ℂ) *
        ntr (MExt (lam D N A) z₁ * Ea D N a * MExt (lam D N A) z₂ * Ea D N b *
          MExt (lam D N A) z₃ * Ea D N c))‖ ≤ Real.exp 1 ^ 2 * (2 * D) := by
      intro a b c
      have hNe : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1⟩)⟩
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg
        (Real.exp_pos _).le]
      have he : Real.exp (3 * t / 2) ≤ Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by push_cast; linarith)
      have hn : ‖ntr (MExt (lam D N A) z₁ * Ea D N a * MExt (lam D N A) z₂ * Ea D N b *
          MExt (lam D N A) z₃ * Ea D N c)‖ ≤ 2 := by
        refine (LF2_ntr_le _).trans ?_
        have e1 := LF2_opNorm_Ea D N a
        have e2 := LF2_opNorm_Ea D N b
        have e3 := LF2_opNorm_Ea D N c
        have m1 := hM z₁ h₁
        have m2 := hM z₂ h₂
        have m3 := hM z₃ h₃
        have p := fun B : Matrix (Idx D N) (Idx D N) ℂ => LF2_op_nonneg B
        calc opNorm (MExt (lam D N A) z₁ * Ea D N a * MExt (lam D N A) z₂ * Ea D N b *
              MExt (lam D N A) z₃ * Ea D N c)
            ≤ opNorm (MExt (lam D N A) z₁) * opNorm (Ea D N a) * opNorm (MExt (lam D N A) z₂) *
                opNorm (Ea D N b) * opNorm (MExt (lam D N A) z₃) * opNorm (Ea D N c) := by
              refine (LF2_op_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ (p _))
              refine (LF2_op_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ (p _))
              refine (LF2_op_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ (p _))
              refine (LF2_op_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ (p _))
              exact LF2_op_mul _ _
          _ ≤ 5 / 4 * 1 * (5 / 4) * 1 * (5 / 4) * 1 := by
              exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul m1 e1 (p _)
                (by norm_num)) m2 (p _) (by norm_num)) e2 (p _) (by norm_num)) m3 (p _)
                (by norm_num)) e3 (p _) (by norm_num)
          _ ≤ 2 := by norm_num
      have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
      calc Real.exp (3 * t / 2) * (D * ‖ntr _‖) ≤ Real.exp 1 ^ 2 * (D * 2) :=
            mul_le_mul he (mul_le_mul_of_nonneg_left hn hD0) (by positivity) (by positivity)
        _ = Real.exp 1 ^ 2 * (2 * D) := by ring
    rw [hE]
    refine (LF2_contr_le _ _ _ _ _ _ (hu _ hU₁) (hu _ hU₂) (hu _ hU₃) hT x y w).trans
      (le_of_eq ?_)
    ring

/-- One step of a `C^{1,1}` function: `|f(u + h) - f(u) - h f'(u)| ≤ L h²` when `f'` is
`L`-Lipschitz on `[0, S] ⊇ [u, u + h]`. -/
private lemma LF2_disc_gen (f f' : ℝ → ℂ) (S L : ℝ) (hL0 : 0 ≤ L)
    (hd : ∀ t ∈ Set.Icc 0 S, HasDerivAt f (f' t) t)
    (hl : ∀ t ∈ Set.Icc 0 S, ∀ s ∈ Set.Icc 0 S, ‖f' t - f' s‖ ≤ L * |t - s|)
    (u h : ℝ) (hu : 0 ≤ u) (hh : 0 ≤ h) (huh : u + h ≤ S) :
    ‖f (u + h) - f u - (h : ℂ) * f' u‖ ≤ L * h ^ 2 := by
  have hsub : Set.Icc u (u + h) ⊆ Set.Icc 0 S := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have huI : u ∈ Set.Icc 0 S := ⟨hu, by linarith⟩
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := L * h) (f := fun r => f r - (r : ℂ) * f' u) (f' := fun r => f' r - f' u)
    (fun x hx => by
      have h1 := hd x (hsub hx)
      have h2 : HasDerivAt (fun r : ℝ => (r : ℂ) * f' u) (1 * f' u) x :=
        (hasDerivAt_id x).ofReal_comp.mul_const _ |>.congr_deriv (by simp)
      exact (h1.sub h2).hasDerivWithinAt.congr_deriv (by ring))
    (fun x hx => by
      refine (hl x (hsub hx) u huI).trans ?_
      have : |x - u| ≤ h := by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
      exact mul_le_mul_of_nonneg_left this hL0)
    (convex_Icc u (u + h)) (⟨le_rfl, by linarith⟩ : u ∈ Set.Icc u (u + h))
    (⟨by linarith, le_rfl⟩ : u + h ∈ Set.Icc u (u + h))
  have e : f (u + h) - f u - (h : ℂ) * f' u =
      (f (u + h) - ((u + h : ℝ) : ℂ) * f' u) - (f u - (u : ℂ) * f' u) := by
    push_cast; ring
  rw [e]
  refine hmv.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, show u + h - u = h by ring, abs_of_nonneg hh]
  ring

/-- A function with derivative bounded by `M` on `[0, S]` is `M`-Lipschitz there. -/
private lemma LF2_lip_of_deriv (f f' : ℝ → ℂ) (S M : ℝ)
    (hd : ∀ t ∈ Set.Icc 0 S, HasDerivAt f (f' t) t) (hb : ∀ t ∈ Set.Icc 0 S, ‖f' t‖ ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc 0 S) (s : ℝ) (hs : s ∈ Set.Icc 0 S) :
    ‖f t - f s‖ ≤ M * |t - s| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f')
    (fun x hx => (hd x hx).hasDerivWithinAt) hb (convex_Icc 0 S) hs ht
  rwa [Real.norm_eq_abs] at this

/-- `|a(t) b(t) - a(u) b(u)| ≤ (L_a B + A L_b) |t - u|` from bounds and Lipschitz bounds. -/
private lemma LF2_lip_mul (a b : ℝ → ℂ) (s : Set ℝ) (Aa Bb La Lb : ℝ)
    (ha : ∀ t ∈ s, ‖a t‖ ≤ Aa) (hb : ∀ t ∈ s, ‖b t‖ ≤ Bb)
    (hla : ∀ t ∈ s, ∀ u ∈ s, ‖a t - a u‖ ≤ La * |t - u|)
    (hlb : ∀ t ∈ s, ∀ u ∈ s, ‖b t - b u‖ ≤ Lb * |t - u|) (t : ℝ) (ht : t ∈ s) (u : ℝ)
    (hu : u ∈ s) : ‖a t * b t - a u * b u‖ ≤ (La * Bb + Aa * Lb) * |t - u| := by
  have e : a t * b t - a u * b u = (a t - a u) * b t + a u * (b t - b u) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hA0 : 0 ≤ Aa := (norm_nonneg _).trans (ha u hu)
  have h1 := mul_le_mul (hla t ht u hu) (hb t ht) (norm_nonneg _)
    ((norm_nonneg _).trans (hla t ht u hu))
  have h2 := mul_le_mul (ha u hu) (hlb t ht u hu) (norm_nonneg _) hA0
  linarith

/-- `|√(q₀ - t) - √(q₀ - u)| ≤ ρ |t - u|` on `[0, S]` for `ρ = (q₀ - S)⁻¹`, `q₀ - S ∈ (0, 1]`. -/
private lemma LF2_sqrt_lip (q₀ S : ℝ) (hqS : 0 < q₀ - S) (hqS1 : q₀ - S ≤ 1) (t : ℝ)
    (ht : t ∈ Set.Icc 0 S) (u : ℝ) (hu : u ∈ Set.Icc 0 S) :
    ‖(((q₀ - t) ^ (1 / 2 : ℝ) : ℝ) : ℂ) - (((q₀ - u) ^ (1 / 2 : ℝ) : ℝ) : ℂ)‖ ≤
      (q₀ - S)⁻¹ * |t - u| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    (LF2_rpow32 _ (by linarith [ht.2])).2, (LF2_rpow32 _ (by linarith [hu.2])).2]
  set a := Real.sqrt (q₀ - t)
  set b := Real.sqrt (q₀ - u)
  have ha2 : a ^ 2 = q₀ - t := Real.sq_sqrt (by linarith [ht.2])
  have hb2 : b ^ 2 = q₀ - u := Real.sq_sqrt (by linarith [hu.2])
  have hm : q₀ - S ≤ a := by
    have : Real.sqrt (q₀ - S) ≤ a := Real.sqrt_le_sqrt (by linarith [ht.2])
    have h2 : q₀ - S ≤ Real.sqrt (q₀ - S) := by
      have h3 := Real.sq_sqrt hqS.le
      have h4 := Real.sqrt_nonneg (q₀ - S)
      have h5 : Real.sqrt (q₀ - S) ≤ 1 := Real.sqrt_le_one.mpr hqS1
      nlinarith
    linarith
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hab : 0 < a + b := by linarith
  have e2 : (a - b) * (a + b) = u - t := by linear_combination ha2 - hb2
  have e : |a - b| = |t - u| / (a + b) := by
    rw [eq_div_iff hab.ne', ← abs_of_pos hab, ← abs_mul, e2, abs_sub_comm]
  rw [e, div_le_iff₀ hab]
  have hρ : 0 < (q₀ - S)⁻¹ := inv_pos.2 hqS
  have : 1 ≤ (q₀ - S)⁻¹ * (a + b) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hqS]; linarith
  nlinarith [abs_nonneg (t - u)]

set_option maxHeartbeats 1000000 in
/-- The one-step error of the three-resolvent Riccati equation on the grid: for
`K̃_t = (t_c - t₀ - t)^{3/2} K_{θ_t}(z_{1,t}, z_{2,t}, z_{3,t})` and `[u, u + h] ⊂ [0, S]`,
`|K̃_{u+h} - K̃_u - h q_u^{1/2} ((3/2)(q_u - 1) K_u + q_u Σ_a (K¹²K + K²³K + K³¹K))| ≤ L h²`
entrywise, with `L = 38 D² ρ² κ`, `κ = 2 D⁴ e² (1 + ρ)³` and `ρ = (t_c - t₀ - S)⁻¹`. -/
private lemma LF2_K3disc (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (hq1 : flowTc (lam D N A) z ≤ 1) (θ : ℝ) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) (z₁ z₂ z₃ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z)
    (h₃ : z₃ = z ∨ z₃ = star z) (u h : ℝ) (hu : 0 ≤ u) (hh : 0 ≤ h) (huh : u + h ≤ S)
    (x y w : Fin D) :
    ‖(((flowTc (lam D N A) z - (u + h)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          flowKten3 (lam D N A) θ z₁ z₂ z₃ (u + h) x y w -
        (((flowTc (lam D N A) z - u) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          flowKten3 (lam D N A) θ z₁ z₂ z₃ u x y w -
        (h : ℂ) * (((flowTc (lam D N A) z - u) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ((3 / 2 : ℂ) * ((flowTc (lam D N A) z - u - 1 : ℝ) : ℂ) *
              flowKten3 (lam D N A) θ z₁ z₂ z₃ u x y w +
            ((flowTc (lam D N A) z - u : ℝ) : ℂ) * ∑ a,
              (flowKmat (lam D N A) θ z₁ z₂ u x a * flowKten3 (lam D N A) θ z₁ z₂ z₃ u a y w +
                flowKmat (lam D N A) θ z₂ z₃ u y a * flowKten3 (lam D N A) θ z₁ z₂ z₃ u x a w +
                flowKmat (lam D N A) θ z₃ z₁ u w a * flowKten3 (lam D N A) θ z₁ z₂ z₃ u x y a))‖ ≤
      38 * D ^ 2 * (flowTc (lam D N A) z - S)⁻¹ ^ 2 *
        (2 * D ^ 4 * Real.exp 1 ^ 2 * (1 + (flowTc (lam D N A) z - S)⁻¹) ^ 3) * h ^ 2 := by
  set q₀ := flowTc (lam D N A) z with hq₀
  set ρ := (q₀ - S)⁻¹ with hρdef
  set κ := 2 * D ^ 4 * Real.exp 1 ^ 2 * (1 + ρ) ^ 3 with hκdef
  have hqS : 0 < q₀ - S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hqS1 : q₀ - S ≤ 1 := by linarith
  have hρ1 : 1 ≤ ρ := by rw [hρdef]; exact one_le_inv₀ hqS |>.2 hqS1
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  set I := Set.Icc (0 : ℝ) S with hI
  -- the matrices `K^{ij}`
  have hKfac : ∀ (zi zj : ℂ), (zi = z ∨ zi = star z) → (zj = z ∨ zj = star z) →
      (∀ t ∈ I, ∀ c d : Fin D, ‖flowKmat (lam D N A) θ zi zj t c d‖ ≤ ρ) ∧
      (∀ c d : Fin D, ∀ t ∈ I, ∀ s ∈ I,
        ‖flowKmat (lam D N A) θ zi zj t c d - flowKmat (lam D N A) θ zi zj s c d‖ ≤
          (D * ρ ^ 2 + ρ) * |t - s|) := by
    intro zi zj hi hj
    set R := LF2_R (Mhat (lam D N A) zi zj) θ with hRdef
    have hfac : ∀ t ∈ I, flowKmat (lam D N A) θ zi zj t = R t ∧
        (∀ c d : Fin D, HasDerivAt (fun r => R r c d) ((R t * R t + R t) c d) t) ∧
        ∀ c d : Fin D, ‖R t c d‖ ≤ ρ := by
      intro t ht
      obtain ⟨e1, e2, e3⟩ := LF2_flowK D N A hA z hz S hS θ hθ₀ hθ₁ zi zj hi hj t ht.1 ht.2
      refine ⟨e1, e2, fun c d => ?_⟩
      have e4 := e3 c d
      rw [e1] at e4
      refine e4.trans ?_
      exact inv_anti₀ hqS (by linarith [ht.2])
    have hRR : ∀ t ∈ I, ∀ c d : Fin D, ‖(R t * R t + R t) c d‖ ≤ D * ρ ^ 2 + ρ := by
      intro t ht c d
      rw [Matrix.add_apply, Matrix.mul_apply]
      refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans ?_) ((hfac t ht).2.2 c d))
      calc ∑ e, ‖R t c e * R t e d‖ ≤ ∑ _e : Fin D, ρ ^ 2 := by
            refine Finset.sum_le_sum fun e _ => ?_
            rw [norm_mul, sq]
            exact mul_le_mul ((hfac t ht).2.2 c e) ((hfac t ht).2.2 e d) (norm_nonneg _)
              (by linarith)
        _ = D * ρ ^ 2 := by simp
    refine ⟨fun t ht c d => by rw [(hfac t ht).1]; exact (hfac t ht).2.2 c d,
      fun c d t ht s hs => ?_⟩
    rw [(hfac t ht).1, (hfac s hs).1]
    exact LF2_lip_of_deriv (fun r => R r c d) (fun r => (R r * R r + R r) c d) S _
      (fun r hr => (hfac r hr).2.1 c d) (fun r hr => hRR r hr c d) t ht s hs
  obtain ⟨hK₁b, hK₁l⟩ := hKfac z₁ z₂ h₁ h₂
  obtain ⟨hK₂b, hK₂l⟩ := hKfac z₂ z₃ h₂ h₃
  obtain ⟨hK₃b, hK₃l⟩ := hKfac z₃ z₁ h₃ h₁
  -- the tensor `K`
  set C : ℝ → Fin D → Fin D → Fin D → ℂ := fun r => ten3Contr
    (LF2_U (Mhat (lam D N A) z₁ z₂) θ r) (LF2_U (Mhat (lam D N A) z₂ z₃) θ r)
    (LF2_U (Mhat (lam D N A) z₃ z₁) θ r)
    (fun b₁ b₂ b₃ => ((Real.exp (3 * r / 2) : ℝ) : ℂ) * ((D : ℂ) *
      ntr (MExt (lam D N A) z₁ * Ea D N b₁ * MExt (lam D N A) z₂ * Ea D N b₂ *
        MExt (lam D N A) z₃ * Ea D N b₃))) with hC
  have hCK : ∀ t ∈ I, flowKten3 (lam D N A) θ z₁ z₂ z₃ t = C t := fun t ht =>
    LF2_flowK3_eq D N A z hz θ z₁ z₂ z₃ h₁ h₂ h₃ t (lt_of_le_of_lt ht.2 hS)
  set σ : ℝ → Fin D → Fin D → Fin D → ℂ := fun t x y w => ∑ a,
    (flowKmat (lam D N A) θ z₁ z₂ t x a * flowKten3 (lam D N A) θ z₁ z₂ z₃ t a y w +
      flowKmat (lam D N A) θ z₂ z₃ t y a * flowKten3 (lam D N A) θ z₁ z₂ z₃ t x a w +
      flowKmat (lam D N A) θ z₃ z₁ t w a * flowKten3 (lam D N A) θ z₁ z₂ z₃ t x y a) with hσ
  have hK3 : ∀ x y w : Fin D, (∀ t ∈ I, HasDerivAt (fun r => C r x y w)
      ((3 / 2 : ℂ) * flowKten3 (lam D N A) θ z₁ z₂ z₃ t x y w + σ t x y w) t) ∧
      ∀ t ∈ I, ‖flowKten3 (lam D N A) θ z₁ z₂ z₃ t x y w‖ ≤ κ := fun x y w =>
    ⟨fun t ht => (LF2_flowK3 D N A hA z hz S hS hq1 θ hθ₀ hθ₁ z₁ z₂ z₃ h₁ h₂ h₃ t ht.1 ht.2
      x y w).1, fun t ht => (LF2_flowK3 D N A hA z hz S hS hq1 θ hθ₀ hθ₁ z₁ z₂ z₃ h₁ h₂ h₃ t
      ht.1 ht.2 x y w).2⟩
  have hDρ : 1 ≤ (D : ℝ) * ρ := one_le_mul_of_one_le_of_one_le hD1 hρ1
  have hσb : ∀ x y w : Fin D, ∀ t ∈ I, ‖σ t x y w‖ ≤ 3 * D * ρ * κ := by
    intro x y w t ht
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun a _ => ?_).trans
      (le_of_eq (show ∑ _a : Fin D, 3 * (ρ * κ) = 3 * D * ρ * κ by simp; ring)))
    · refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
      rw [norm_mul, norm_mul, norm_mul]
      have t1 := mul_le_mul (hK₁b t ht x a) ((hK3 a y w).2 t ht) (norm_nonneg _) (by linarith)
      have t2 := mul_le_mul (hK₂b t ht y a) ((hK3 x a w).2 t ht) (norm_nonneg _) (by linarith)
      have t3 := mul_le_mul (hK₃b t ht w a) ((hK3 x y a).2 t ht) (norm_nonneg _) (by linarith)
      linarith
  -- Lipschitz bounds of the entries of `K`
  have hK3l : ∀ x y w : Fin D, ∀ t ∈ I, ∀ s ∈ I,
      ‖flowKten3 (lam D N A) θ z₁ z₂ z₃ t x y w - flowKten3 (lam D N A) θ z₁ z₂ z₃ s x y w‖ ≤
        (5 * D * ρ * κ) * |t - s| := by
    intro x y w t ht s hs
    rw [hCK t ht, hCK s hs]
    refine LF2_lip_of_deriv (fun r => C r x y w) _ S _ (hK3 x y w).1 (fun r hr => ?_) t ht s hs
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h1 := (hK3 x y w).2 r hr
    have h2 := hσb x y w r hr
    have : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    rw [this]
    have k : κ ≤ D * ρ * κ := by nlinarith
    linarith
  have hσl : ∀ t ∈ I, ∀ s ∈ I, ‖σ t x y w - σ s x y w‖ ≤ (21 * D ^ 2 * ρ ^ 2 * κ) * |t - s| := by
    intro t ht s hs
    simp only [hσ]
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hL : (D : ℝ) * ρ ^ 2 + ρ ≤ 2 * D * ρ ^ 2 := by nlinarith
    have hterm : ∀ (M : ℝ → Matrix (Fin D) (Fin D) ℂ) (c d : Fin D) (T : ℝ → ℂ),
        (∀ t ∈ I, ‖M t c d‖ ≤ ρ) →
        (∀ t ∈ I, ∀ s ∈ I, ‖M t c d - M s c d‖ ≤ (D * ρ ^ 2 + ρ) * |t - s|) →
        (∀ t ∈ I, ‖T t‖ ≤ κ) → (∀ t ∈ I, ∀ s ∈ I, ‖T t - T s‖ ≤ (5 * D * ρ * κ) * |t - s|) →
        ‖M t c d * T t - M s c d * T s‖ ≤ (7 * D * ρ ^ 2 * κ) * |t - s| := by
      intro M c d T hMb hMl hTb hTl
      refine (LF2_lip_mul (fun r => M r c d) T I ρ κ _ _ hMb hTb hMl hTl t ht s hs).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have : ρ * κ ≤ D * ρ ^ 2 * κ := by
        have : ρ ≤ D * ρ ^ 2 := by nlinarith
        nlinarith
      nlinarith
    refine (Finset.sum_le_sum fun a _ => ?_).trans (le_of_eq (show ∑ _a : Fin D,
      3 * ((7 * D * ρ ^ 2 * κ) * |t - s|) = (21 * D ^ 2 * ρ ^ 2 * κ) * |t - s| by simp; ring))
    · have e : ∀ p₁ p₂ p₃ p₁' p₂' p₃' : ℂ, (p₁ + p₂ + p₃) - (p₁' + p₂' + p₃') =
          (p₁ - p₁') + (p₂ - p₂') + (p₃ - p₃') := fun _ _ _ _ _ _ => by ring
      rw [e]
      refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
      have t1 := hterm (fun r => flowKmat (lam D N A) θ z₁ z₂ r) x a
        (fun r => flowKten3 (lam D N A) θ z₁ z₂ z₃ r a y w) (fun r hr => hK₁b r hr x a)
        (hK₁l x a) (fun r hr => (hK3 a y w).2 r hr) (hK3l a y w)
      have t2 := hterm (fun r => flowKmat (lam D N A) θ z₂ z₃ r) y a
        (fun r => flowKten3 (lam D N A) θ z₁ z₂ z₃ r x a w) (fun r hr => hK₂b r hr y a)
        (hK₂l y a) (fun r hr => (hK3 x a w).2 r hr) (hK3l x a w)
      have t3 := hterm (fun r => flowKmat (lam D N A) θ z₃ z₁ r) w a
        (fun r => flowKten3 (lam D N A) θ z₁ z₂ z₃ r x y a) (fun r hr => hK₃b r hr w a)
        (hK₃l w a) (fun r hr => (hK3 x y a).2 r hr) (hK3l x y a)
      linarith
  -- the derivative of `K̃` and its Lipschitz bound
  set Q : ℝ → ℂ := fun t => (3 / 2 : ℂ) * ((q₀ - t - 1 : ℝ) : ℂ) *
    flowKten3 (lam D N A) θ z₁ z₂ z₃ t x y w + ((q₀ - t : ℝ) : ℂ) * σ t x y w with hQ
  set g : ℝ → ℂ := fun t => (((q₀ - t) ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hg
  have hqt : ∀ t ∈ I, 0 < q₀ - t ∧ q₀ - t ≤ 1 := fun t ht => ⟨by linarith [ht.2], by
    linarith [ht.1]⟩
  have hgb : ∀ t ∈ I, ‖g t‖ ≤ 1 := by
    intro t ht
    simp only [hg, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.rpow_nonneg (hqt t ht).1.le _)]
    exact Real.rpow_le_one (hqt t ht).1.le (hqt t ht).2 (by norm_num)
  have hgl : ∀ t ∈ I, ∀ s ∈ I, ‖g t - g s‖ ≤ ρ * |t - s| := fun t ht s hs =>
    LF2_sqrt_lip q₀ S hqS hqS1 t ht s hs
  have hQb : ∀ t ∈ I, ‖Q t‖ ≤ 5 * D * ρ * κ := by
    intro t ht
    simp only [hQ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have h1 : |q₀ - t - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [(hqt t ht).1, (hqt t ht).2]
    have h2 : |q₀ - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(hqt t ht).1, (hqt t ht).2]
    have h3 := (hK3 x y w).2 t ht
    have h4 := hσb x y w t ht
    have : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    rw [this]
    have k1 : 3 / 2 * |q₀ - t - 1| * ‖flowKten3 (lam D N A) θ z₁ z₂ z₃ t x y w‖ ≤ 3 / 2 * 1 * κ :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h3 (norm_nonneg _) (by norm_num)
    have k2 : |q₀ - t| * ‖σ t x y w‖ ≤ 1 * (3 * D * ρ * κ) :=
      mul_le_mul h2 h4 (norm_nonneg _) zero_le_one
    have k3 : (3 / 2 : ℝ) * κ ≤ 2 * D * ρ * κ := by nlinarith [mul_le_mul_of_nonneg_right hDρ hκ0]
    linarith
  have hQl : ∀ t ∈ I, ∀ s ∈ I, ‖Q t - Q s‖ ≤ (33 * D ^ 2 * ρ ^ 2 * κ) * |t - s| := by
    intro t ht s hs
    have hc1 : ∀ t ∈ I, ‖(3 / 2 : ℂ) * ((q₀ - t - 1 : ℝ) : ℂ)‖ ≤ 3 / 2 := by
      intro t ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : |q₀ - t - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [(hqt t ht).1, (hqt t ht).2]
      have : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
      rw [this]; nlinarith [abs_nonneg (q₀ - t - 1)]
    have hc1l : ∀ t ∈ I, ∀ s ∈ I, ‖(3 / 2 : ℂ) * ((q₀ - t - 1 : ℝ) : ℂ) -
        (3 / 2 : ℂ) * ((q₀ - s - 1 : ℝ) : ℂ)‖ ≤ 3 / 2 * |t - s| := by
      intro t ht s hs
      rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        show q₀ - t - 1 - (q₀ - s - 1) = -(t - s) by ring, abs_neg]
      norm_num
    have hc2 : ∀ t ∈ I, ‖((q₀ - t : ℝ) : ℂ)‖ ≤ 1 := by
      intro t ht
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hqt t ht).1]; exact (hqt t ht).2
    have hc2l : ∀ t ∈ I, ∀ s ∈ I, ‖((q₀ - t : ℝ) : ℂ) - ((q₀ - s : ℝ) : ℂ)‖ ≤ 1 * |t - s| := by
      intro t ht s hs
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show q₀ - t - (q₀ - s) = -(t - s) by ring, abs_neg, one_mul]
    have l1 := LF2_lip_mul (fun r => (3 / 2 : ℂ) * ((q₀ - r - 1 : ℝ) : ℂ))
      (fun r => flowKten3 (lam D N A) θ z₁ z₂ z₃ r x y w) I (3 / 2) κ (3 / 2) (5 * D * ρ * κ)
      hc1 (fun r hr => (hK3 x y w).2 r hr) hc1l (hK3l x y w) t ht s hs
    have l2 := LF2_lip_mul (fun r => ((q₀ - r : ℝ) : ℂ)) (fun r => σ r x y w) I 1
      (3 * D * ρ * κ) 1 (21 * D ^ 2 * ρ ^ 2 * κ) hc2 (fun r hr => hσb x y w r hr) hc2l hσl
      t ht s hs
    have e : Q t - Q s = ((3 / 2 : ℂ) * ((q₀ - t - 1 : ℝ) : ℂ) *
        flowKten3 (lam D N A) θ z₁ z₂ z₃ t x y w - (3 / 2 : ℂ) * ((q₀ - s - 1 : ℝ) : ℂ) *
        flowKten3 (lam D N A) θ z₁ z₂ z₃ s x y w) +
        (((q₀ - t : ℝ) : ℂ) * σ t x y w - ((q₀ - s : ℝ) : ℂ) * σ s x y w) := by
      simp only [hQ]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have hts := abs_nonneg (t - s)
    have k : (3 / 2 * κ + 3 / 2 * (5 * D * ρ * κ)) + (1 * (3 * D * ρ * κ) +
        1 * (21 * D ^ 2 * ρ ^ 2 * κ)) ≤ 33 * D ^ 2 * ρ ^ 2 * κ := by
      have a1 : κ ≤ D ^ 2 * ρ ^ 2 * κ := by
        have : 1 ≤ (D : ℝ) ^ 2 * ρ ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD1)
          (one_le_pow₀ hρ1)
        nlinarith
      have a2 : D * ρ * κ ≤ D ^ 2 * ρ ^ 2 * κ := by
        have : (D : ℝ) * ρ ≤ D ^ 2 * ρ ^ 2 := by nlinarith
        nlinarith
      nlinarith
    have := mul_le_mul_of_nonneg_right k hts
    linarith
  have hfd : ∀ t ∈ I, HasDerivAt (fun r => (((q₀ - r) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * C r x y w)
      (g t * Q t) t := by
    intro t ht
    have hq := (hqt t ht).1
    have h1 := ((hasDerivAt_id' t).const_sub q₀).rpow_const (p := (3 / 2 : ℝ)) (Or.inl hq.ne')
    have h2 := h1.ofReal_comp.mul ((hK3 x y w).1 t ht)
    refine h2.congr_deriv ?_
    have e1 : (q₀ - t) ^ ((3 / 2 : ℝ) - 1) = (q₀ - t) ^ (1 / 2 : ℝ) := by norm_num
    have e2 : (q₀ - t) ^ (3 / 2 : ℝ) = (q₀ - t) * (q₀ - t) ^ (1 / 2 : ℝ) := by
      rw [(LF2_rpow32 _ hq.le).1, (LF2_rpow32 _ hq.le).2]
    rw [e1]
    simp only [hg, hQ]
    rw [hCK t ht, e2]
    push_cast
    ring
  have hfl : ∀ t ∈ I, ∀ s ∈ I, ‖g t * Q t - g s * Q s‖ ≤ (38 * D ^ 2 * ρ ^ 2 * κ) * |t - s| := by
    intro t ht s hs
    refine (LF2_lip_mul g Q I 1 (5 * D * ρ * κ) ρ (33 * D ^ 2 * ρ ^ 2 * κ) hgb hQb hgl hQl t ht
      s hs).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    have : (D : ℝ) * ρ ^ 2 * κ ≤ D ^ 2 * ρ ^ 2 * κ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg ρ)) hκ0
    nlinarith
  have key := LF2_disc_gen (fun r => (((q₀ - r) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * C r x y w)
    (fun t => g t * Q t) S _ (by positivity) hfd hfl u h hu hh huh
  have huI : u ∈ I := ⟨hu, by linarith⟩
  have huhI : u + h ∈ I := ⟨by linarith, huh⟩
  rw [← hCK u huI, ← hCK (u + h) huhI] at key
  refine le_trans (le_of_eq ?_) key
  congr 1
  simp only [hg, hQ, hσ]
  ring

/-- On the grid `q_j = q₀ - j h`, `q_j ≠ 0` for `j ≤ k`, `Σ_{j<k} h / q_j² ≤ 1 / q_k` and
`Σ_{j<k} h / q_j ≤ log(q₀ / q_k)`. -/
private lemma LF2_rsum (q₀ h : ℝ) (hh : 0 < h) (k : ℕ) (hk : k * h < q₀) :
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

/-! ### The linear recursion of the three-resolvent loop -/

/-- The entries of a `D × D × D` tensor as a vector of `ℂ^{D³}` with the Euclidean norm. -/
private def LF2_vec {D : ℕ} :
    (Fin D → Fin D → Fin D → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin D × Fin D × Fin D) where
  toFun T := WithLp.toLp 2 (fun p => T p.1 p.2.1 p.2.2)
  map_add' T T' := by ext p; simp
  map_smul' c T := by ext p; simp

/-- The tensor of a vector of `ℂ^{D³}`. -/
private def LF2_mat {D : ℕ} (v : EuclideanSpace ℂ (Fin D × Fin D × Fin D)) :
    Fin D → Fin D → Fin D → ℂ :=
  fun x y w => v (x, y, w)

private lemma LF2_mat_vec {D : ℕ} (T : Fin D → Fin D → Fin D → ℂ) : LF2_mat (LF2_vec T) = T :=
  rfl

private lemma LF2_vec_mat {D : ℕ} (v : EuclideanSpace ℂ (Fin D × Fin D × Fin D)) :
    LF2_vec (LF2_mat v) = v := rfl

/-- `‖vec T‖ = ‖T‖₂`. -/
private lemma LF2_norm_vec {D : ℕ} (T : Fin D → Fin D → Fin D → ℂ) :
    ‖LF2_vec T‖ = ten3Norm T := by
  rw [EuclideanSpace.norm_eq, ten3Norm]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

/-- `‖v‖ = ‖mat v‖₂`. -/
private lemma LF2_norm_mat {D : ℕ} (v : EuclideanSpace ℂ (Fin D × Fin D × Fin D)) :
    ‖v‖ = ten3Norm (LF2_mat v) := by
  rw [← LF2_norm_vec, LF2_vec_mat]

/-- The tensor map `V ↦ q Σ_a (K¹_{xa} V_{ayw} + K²_{ya} V_{xaw} + K³_{wa} V_{xya})`
`- (3/2)(1 - q) V` of the linearised three-resolvent equation. -/
private def LF2_top {D : ℕ} (K₁ K₂ K₃ : Matrix (Fin D) (Fin D) ℂ) (q : ℝ)
    (V : Fin D → Fin D → Fin D → ℂ) : Fin D → Fin D → Fin D → ℂ :=
  fun x y w => (q : ℂ) * (∑ a, (K₁ x a * V a y w + K₂ y a * V x a w + K₃ w a * V x y a)) -
    (3 / 2 : ℂ) * ((1 - q : ℝ) : ℂ) * V x y w

/-- `LF2_top` as a continuous linear map of `ℂ^{D³}`. -/
private def LF2_op3 {D : ℕ} (K₁ K₂ K₃ : Matrix (Fin D) (Fin D) ℂ) (q : ℝ) :
    EuclideanSpace ℂ (Fin D × Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D × Fin D) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => LF2_vec (LF2_top K₁ K₂ K₃ q (LF2_mat v))
      map_add' := fun v v' => by
        rw [← map_add]
        congr 1
        funext x y w
        simp only [LF2_top, LF2_mat, PiLp.add_apply, Pi.add_apply]
        simp only [mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        funext x y w
        simp only [LF2_top, LF2_mat, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul]
        simp only [Finset.mul_sum]
        rw [mul_sub, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun a _ => ?_
          ring
        · ring }

private lemma LF2_op3_apply {D : ℕ} (K₁ K₂ K₃ : Matrix (Fin D) (Fin D) ℂ) (q : ℝ)
    (v : EuclideanSpace ℂ (Fin D × Fin D × Fin D)) :
    LF2_op3 K₁ K₂ K₃ q v = LF2_vec (LF2_top K₁ K₂ K₃ q (LF2_mat v)) := rfl

/-- The operator bound of `tOp3_norm_le` along the flow: at `t ∈ [0, S]`, with
`K^{ij}_t = K_{θ_t}(z_{i,t}, z_{j,t})` and `q_t = t_c - t₀ - t`, the map `LF2_top` has norm at most
`(3/2)(1 + q_t)`, not `3/2 + o(1)`. -/
private lemma LF2_tOp3 (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ z₃ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (h₃ : z₃ = z ∨ z₃ = star z)
    (t : ℝ) (ht0 : 0 ≤ t) (htS : t ≤ S) (V : Fin D → Fin D → Fin D → ℂ) :
    ten3Norm (LF2_top (flowKmat (lam D N A) θ z₁ z₂ t) (flowKmat (lam D N A) θ z₂ z₃ t)
        (flowKmat (lam D N A) θ z₃ z₁ t) (flowTc (lam D N A) z - t) V) ≤
      3 / 2 * (1 + (flowTc (lam D N A) z - t)) * ten3Norm V := by
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  obtain ⟨hηt, -, -, -, -, htc, -⟩ := LF2_flow D N hD1 hN1 A hA z hz S hS t ht0 htS
  set A' : Matrix (Fin N) (Fin N) ℂ := ((Real.exp (-t / 2) : ℝ) : ℂ) • A with hA'
  have hlam : lam D N A' = ((Real.exp (-t / 2) : ℝ) : ℂ) • lam D N A :=
    (LF2_lam_smul D N A _).symm
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
  have hop := tOp3_norm_le D N A' (charFlowZ (lam D N A) z t) hηt
    (Real.exp (-t) * θ + 1 - Real.exp (-t)) hθ0' hθ1' (charFlowZ (lam D N A) z₁ t)
    (charFlowZ (lam D N A) z₂ t) (charFlowZ (lam D N A) z₃ t) (hflag z₁ h₁) (hflag z₂ h₂)
    (hflag z₃ h₃) V
  rw [hlam, htc] at hop
  exact hop

/-- The linear discrete Duhamel bound with a source split as `T ℰ + M`: if
`Δ_{k+1} - ℰ_{k+1} = Δ_k - ℰ_k + (h/q_k)(T_k Δ_k + M_k)` for `k < K`, `ℰ_0 = 0`, `‖T_k‖ ≤ c`,
`c ‖ℰ_k‖ + ‖M_k‖ ≤ X / ψ_k` and `(q_{j+1}/q_k)^c ≤ G ψ_j / ψ_k`, then
`‖Δ_k‖ ≤ (q₀/q_k)^c ‖Δ_0‖ + G X log(q₀/q_k) / ψ_k + ‖ℰ_k‖`, `q_k = q₀ - k h`. -/
private lemma LF2_duh {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : ℕ → E →L[ℂ] E) (h q₀ c : ℝ) (hh : 0 < h) (hc : 0 ≤ c) (hT : ∀ i, ‖T i‖ ≤ c)
    (K : ℕ) (hK : (K : ℝ) * h < q₀) (Δ ℰ M : ℕ → E) (hℰ0 : ℰ 0 = 0)
    (hrec : ∀ k, k < K → Δ (k + 1) - ℰ (k + 1) =
      Δ k - ℰ k + ((h / (q₀ - (0 + k * h)) : ℝ) : ℂ) • (T k (Δ k) + M k))
    (ψ : ℕ → ℝ) (hψ : ∀ k, k ≤ K → 0 < ψ k) (X G : ℝ) (hX0 : 0 ≤ X) (hG : 0 ≤ G)
    (hX : ∀ k, k < K → c * ‖ℰ k‖ + ‖M k‖ ≤ X / ψ k)
    (hrat : ∀ j k, j < k → k ≤ K →
      ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ c ≤ G * ψ j / ψ k)
    (k : ℕ) (hk : k ≤ K) :
    ‖Δ k‖ ≤ (q₀ / (q₀ - k * h)) ^ c * ‖Δ 0‖ + G * X * Real.log (q₀ / (q₀ - k * h)) / ψ k +
      ‖ℰ k‖ := by
  have hkh : (k : ℝ) * h < q₀ := by
    have : (k : ℝ) * h ≤ K * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le
    linarith
  have hpos : ∀ j : ℕ, j ≤ k → 0 < q₀ - j * h := fun j hj => by
    have : (j : ℝ) * h ≤ k * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh.le
    linarith
  obtain ⟨x, hx⟩ : ∃ x : ℕ → E, x = fun n => Δ n - ℰ n := ⟨_, rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ bb : ℕ → E, bb = fun n =>
      x (n + 1) - x n - ((h / (q₀ - (0 + n * h)) : ℝ) : ℂ) • T n (x n) := ⟨_, rfl⟩
  have hxrec : ∀ n, x (n + 1) = x n + ((h / (q₀ - (0 + n * h)) : ℝ) : ℂ) • T n (x n) + bb n := by
    intro n; rw [hbb]; dsimp only; rw [sub_sub, add_sub_cancel]
  have hlin := duhamel_lin_le T 0 h q₀ c hh hc hT x bb hxrec k (by rw [zero_add]; exact hkh)
  simp only [zero_add, sub_zero] at hlin
  have hbbj : ∀ j, j < k → ‖bb j‖ ≤ h / (q₀ - j * h) * (X / ψ j) := by
    intro j hj
    have hjK : j < K := lt_of_lt_of_le hj hk
    have hqj := hpos j hj.le
    have e1 : bb j = ((h / (q₀ - j * h) : ℝ) : ℂ) • (T j (ℰ j) + M j) := by
      rw [hbb]
      dsimp only
      rw [hx]
      dsimp only
      have hr := hrec j hjK
      rw [zero_add] at hr ⊢
      rw [hr, map_sub]
      simp only [smul_add, smul_sub]
      abel
    rw [e1, norm_smul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hh.le hqj.le)]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (div_nonneg hh.le hqj.le)
    refine le_trans ?_ (hX j hjK)
    have := ((T j).le_opNorm (ℰ j)).trans (mul_le_mul_of_nonneg_right (hT j) (norm_nonneg _))
    linarith
  have hsum : ∑ j ∈ Finset.range k,
      ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ c * ‖bb j‖ ≤
      G * X * Real.log (q₀ / (q₀ - k * h)) / ψ k := by
    have hψk := hψ k hk
    have hR := (LF2_rsum q₀ h hh k hkh).2.2
    calc ∑ j ∈ Finset.range k, ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ c * ‖bb j‖
        ≤ ∑ j ∈ Finset.range k, G * X / ψ k * (h / (q₀ - j * h)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjk : j < k := Finset.mem_range.1 hj
          have hψj := hψ j (hjk.le.trans hk)
          have hqj := hpos j hjk.le
          have hr := hrat j k hjk hk
          have hb := hbbj j hjk
          have h0 : 0 ≤ ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ c :=
            Real.rpow_nonneg (div_nonneg (by
              have := hpos (j + 1) (by omega); push_cast at this ⊢; linarith) (hpos k le_rfl).le) _
          calc ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ c * ‖bb j‖
              ≤ G * ψ j / ψ k * (h / (q₀ - j * h) * (X / ψ j)) :=
                mul_le_mul hr hb (norm_nonneg _) (by positivity)
            _ = G * X / ψ k * (h / (q₀ - j * h)) := by field_simp
      _ = G * X / ψ k * ∑ j ∈ Finset.range k, h / (q₀ - j * h) := by rw [Finset.mul_sum]
      _ ≤ G * X / ψ k * Real.log (q₀ / (q₀ - k * h)) :=
          mul_le_mul_of_nonneg_left hR (by positivity)
      _ = _ := by ring
  have hx0 : x 0 = Δ 0 := by rw [hx]; simp [hℰ0]
  have hΔle : ‖Δ k‖ ≤ ‖x k‖ + ‖ℰ k‖ := by
    have : Δ k = x k + ℰ k := by rw [hx]; exact (sub_add_cancel _ _).symm
    rw [this]; exact norm_add_le _ _
  rw [hx0] at hlin
  linarith

/-- An entry is bounded by the Hilbert–Schmidt norm. -/
private lemma LF2_entry_hs {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) (i j : Fin D) :
    ‖M i j‖ ≤ hsNorm M := by
  unfold hsNorm
  rw [← Real.sqrt_sq (norm_nonneg (M i j))]
  refine Real.sqrt_le_sqrt ?_
  calc ‖M i j‖ ^ 2 ≤ ∑ y, ‖M i y‖ ^ 2 :=
        Finset.single_le_sum (f := fun y => ‖M i y‖ ^ 2) (fun y _ => by positivity)
          (Finset.mem_univ j)
    _ ≤ ∑ x, ∑ y, ‖M x y‖ ^ 2 :=
        Finset.single_le_sum (f := fun x => ∑ y, ‖M x y‖ ^ 2)
          (fun x _ => Finset.sum_nonneg fun y _ => by positivity) (Finset.mem_univ i)

/-- Entrywise bounds give a bound for the `ℓ²` norm of a `D³` tensor. -/
private lemma LF2_ten_entry {D : ℕ} (hD : 1 ≤ D) (T : Fin D → Fin D → Fin D → ℂ) (β : ℝ)
    (hβ : 0 ≤ β) (h : ∀ a b c, ‖T a b c‖ ≤ β) : ten3Norm T ≤ D ^ 2 * β := by
  unfold ten3Norm
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  calc ∑ a, ∑ b, ∑ c, ‖T a b c‖ ^ 2 ≤ ∑ _a : Fin D, ∑ _b : Fin D, ∑ _c : Fin D, β ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h a b c) 2
    _ = (D : ℝ) ^ 3 * β ^ 2 := by simp; ring
    _ ≤ (D : ℝ) ^ 4 * β ^ 2 := by
        have : (D : ℝ) ^ 3 ≤ (D : ℝ) ^ 4 := pow_le_pow_right₀ hDr (by norm_num)
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = ((D : ℝ) ^ 2 * β) ^ 2 := by ring

/-- `‖c T‖₂ = |c| ‖T‖₂`. -/
private lemma LF2_ten_smul {D : ℕ} (c : ℂ) (T : Fin D → Fin D → Fin D → ℂ) :
    ten3Norm (fun x y w => c * T x y w) = ‖c‖ * ten3Norm T := by
  rw [← LF2_norm_vec, ← LF2_norm_vec, ← norm_smul, ← map_smul]
  rfl

/-- At `s = 0` the flowed tensors are the unflowed ones. -/
private lemma LF2_zero3 {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ z₃ : ℂ)
    (H : Idx D N → Idx D N → ℂ) :
    flowLten3 Λ z₁ z₂ z₃ 0 H = Lten3 Λ H z₁ z₂ z₃ ∧
      flowKten3 Λ θ z₁ z₂ z₃ 0 = KTheta3 Λ θ z₁ z₂ z₃ := by
  have hz : ∀ w : ℂ, charFlowZ Λ w 0 = w := fun w => by simp [charFlowZ]
  have he : ((Real.exp (-0 / 2) : ℝ) : ℂ) • Λ = Λ := by simp
  refine ⟨?_, ?_⟩
  · simp only [flowLten3, hz, he]
  · simp only [flowKten3, hz, he]
    congr 1
    simp

/-- The one-step identity behind the linear recursion: with `Δ = p (L - K)`, `p = q^{3/2}`,
`r = q^{1/2}`, `g q = h`, the change `Δ' - Δ - g (T Δ + Mid)` is the martingale increment plus the
drift error of `L` minus the one-step error of `K`, entrywise. -/
private lemma LF2_step {D : ℕ} (q q' h : ℝ) (g : ℂ) (hq : 0 < q) (hg : g * (q : ℂ) = (h : ℂ))
    (Lt Kt Lt' Kt' Et : Fin D → Fin D → Fin D → ℂ)
    (L₁ L₂ L₃ K₁ K₂ K₃ : Matrix (Fin D) (Fin D) ℂ) (x y w : Fin D) :
    (((q' ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (Lt' x y w - Kt' x y w) -
        ((q ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (Lt x y w - Kt x y w)) -
      g * (LF2_top K₁ K₂ K₃ q (fun x y w => ((q ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          (Lt x y w - Kt x y w)) x y w +
        ∑ a, ((q : ℂ) * (L₁ x a - K₁ x a) * (((q ^ (3 / 2 : ℝ) : ℝ) : ℂ) * Lt a y w) +
          (q : ℂ) * (L₂ y a - K₂ y a) * (((q ^ (3 / 2 : ℝ) : ℝ) : ℂ) * Lt x a w) +
          (q : ℂ) * (L₃ w a - K₃ w a) * (((q ^ (3 / 2 : ℝ) : ℝ) : ℂ) * Lt x y a))) =
    ((q' ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (Lt' x y w - Et x y w) +
      ((((q' ^ (3 / 2 : ℝ) : ℝ) : ℂ) * Et x y w - ((q ^ (3 / 2 : ℝ) : ℝ) : ℂ) * Lt x y w -
        (h : ℂ) * ((q ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((3 / 2 : ℂ) * ((q - 1 : ℝ) : ℂ) * Lt x y w +
          (q : ℂ) * ∑ a, (L₁ x a * Lt a y w + L₂ y a * Lt x a w + L₃ w a * Lt x y a))) -
      (((q' ^ (3 / 2 : ℝ) : ℝ) : ℂ) * Kt' x y w - ((q ^ (3 / 2 : ℝ) : ℝ) : ℂ) * Kt x y w -
        (h : ℂ) * ((q ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((3 / 2 : ℂ) * ((q - 1 : ℝ) : ℂ) * Kt x y w +
          (q : ℂ) * ∑ a, (K₁ x a * Kt a y w + K₂ y a * Kt x a w + K₃ w a * Kt x y a)))) := by
  obtain ⟨hp1, hp2⟩ := LF2_rpow32 q hq.le
  set r : ℂ := ((q ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hr
  have hpr : ((q ^ (3 / 2 : ℝ) : ℝ) : ℂ) = (q : ℂ) * r := by rw [hr, hp1, hp2]; push_cast; ring
  set p : ℂ := ((q ^ (3 / 2 : ℝ) : ℝ) : ℂ) with hp
  have key : (q : ℂ) * (∑ a, (K₁ x a * (p * (Lt a y w - Kt a y w)) +
        K₂ y a * (p * (Lt x a w - Kt x a w)) + K₃ w a * (p * (Lt x y a - Kt x y a)))) +
      ∑ a, ((q : ℂ) * (L₁ x a - K₁ x a) * (p * Lt a y w) +
        (q : ℂ) * (L₂ y a - K₂ y a) * (p * Lt x a w) +
        (q : ℂ) * (L₃ w a - K₃ w a) * (p * Lt x y a)) =
      (q : ℂ) * p * ((∑ a, (L₁ x a * Lt a y w + L₂ y a * Lt x a w + L₃ w a * Lt x y a)) -
        ∑ a, (K₁ x a * Kt a y w + K₂ y a * Kt x a w + K₃ w a * Kt x y a)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  simp only [LF2_top]
  rw [← hg]
  rw [hpr] at key ⊢
  push_cast
  linear_combination (-g) * key

/-- On the good event, `|L_{(1,2,3),xyw}| ≤ D N^{τ'} Im m_s / η_s²` (A.53) [entprodG] for three
resolvents. -/
private lemma LF2_Lten_good (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z) (τ' : ℝ)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian)
    (hgood : flowGoodAt A z τ' s H) (z₁ z₂ z₃ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (h₃ : z₃ = z ∨ z₃ = star z) (x y w : Fin D) :
    ‖flowLten3 (lam D N A) z₁ z₂ z₃ s H x y w‖ ≤
      D * ((N : ℝ) ^ τ' * (flowIm (lam D N A) z s / (charFlowZ (lam D N A) z s).im ^ 2)) := by
  obtain ⟨b₁, hG₁, -⟩ := LF2_flag hD hN A z hz s hs H hH z₁ h₁
  obtain ⟨b₂, hG₂, -⟩ := LF2_flag hD hN A z hz s hs H hH z₂ h₂
  obtain ⟨b₃, hG₃, -⟩ := LF2_flag hD hN A z hz s hs H hH z₃ h₃
  simp only [flowLten3, Lten3]
  rw [hG₁, hG₂, hG₃, norm_mul, Complex.norm_natCast, LF2_word3]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have h3 := hgood.2.1 3 (by norm_num) (by norm_num) ![b₁, b₂, b₃] ![x, y, w]
  rw [LF2_bndA4 3 (by norm_num)] at h3
  have e : (fun i : Fin 3 => Ea D N (![x, y, w] i)) = ![Ea D N x, Ea D N y, Ea D N w] := by
    funext i; fin_cases i <;> rfl
  rw [e] at h3
  exact h3

set_option maxHeartbeats 6400000 in
-- The linear recursion, its sources and the sharp bound share their objects.
/-- (3.28) [flow_3G_res] on one grid, pathwise: if the one-step drift errors, the martingale sums,
the two-resolvent bounds of `flowL2_grid` at all grid times, the start bounds
`q₀² ‖L_{(i,j),0} - K_θ‖₂ ≤ Y / (N (Im m)²)` and the good event satisfy the stated bounds, then
`‖L_{(1,2,3),k} - K_k‖₂ ≤ N^{τ'} ((q₀/q_k)³ ‖L_{(1,2,3),0} - K_θ‖₂ + N^{ε_g}/(N q_k³ (Im m_k)³))` at
every grid time, by the linear recursion of `Δ̃_k = q_k^{3/2} (L_k - K_k)` and `LF2_duh`. -/
private lemma LF2_lin (D N K : ℕ) [NeZero D] [NeZero N] (hK : 1 ≤ K)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ) (hA : opNorm (lam D N A) ≤ 1 / 10)
    (hz : 0 < z.im) (hSpos : 0 < S) (hSt : S < flowTc (lam D N A) z)
    (hq1 : flowTc (lam D N A) z ≤ 1)
    (hηN : ∀ s, 0 ≤ s → s ≤ S → (N : ℝ)⁻¹ < (charFlowZ (lam D N A) z s).im)
    (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ z₃ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (h₃ : z₃ = z ∨ z₃ = star z) (H : ℕ → Idx D N → Idx D N → ℂ)
    (a b τ₂ τg Y τ' εg : ℝ)
    (hgood : ∀ k, k < K → (Matrix.of (H k)).IsHermitian ∧
      flowGoodAt A z τg (k * (S / K)) (H k))
    (hdrift : ∀ j, j < K → ∀ x y w : Fin D,
      ‖(∫ X, (((flowTc (lam D N A) z - (j * (S / K) + S / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
            flowLten3 (lam D N A) z₁ z₂ z₃ (j * (S / K) + S / K)
              (Real.exp (-(S / K) / 2) • H j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y w
            ∂(gueBlocks D N)) -
          (((flowTc (lam D N A) z - j * (S / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
            flowLten3 (lam D N A) z₁ z₂ z₃ (j * (S / K)) (H j) x y w -
          ((S / K : ℝ) : ℂ) * (((flowTc (lam D N A) z - j * (S / K)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
            ((3 / 2 : ℂ) * ((flowTc (lam D N A) z - j * (S / K) - 1 : ℝ) : ℂ) *
                flowLten3 (lam D N A) z₁ z₂ z₃ (j * (S / K)) (H j) x y w +
              ((flowTc (lam D N A) z - j * (S / K) : ℝ) : ℂ) * ∑ a,
                (flowLmat (lam D N A) z₁ z₂ (j * (S / K)) (H j) x a *
                    flowLten3 (lam D N A) z₁ z₂ z₃ (j * (S / K)) (H j) a y w +
                  flowLmat (lam D N A) z₂ z₃ (j * (S / K)) (H j) y a *
                    flowLten3 (lam D N A) z₁ z₂ z₃ (j * (S / K)) (H j) x a w +
                  flowLmat (lam D N A) z₃ z₁ (j * (S / K)) (H j) w a *
                    flowLten3 (lam D N A) z₁ z₂ z₃ (j * (S / K)) (H j) x y a))‖ ≤
        S / K * ((N : ℝ) ^ a / (N * (flowTc (lam D N A) z - j * (S / K)) ^ (5 / 2 : ℝ) *
          flowIm (lam D N A) z (j * (S / K)) ^ 3)) + (S / K) ^ 2 * (N : ℝ) ^ (20 : ℝ))
    (hmart : ∀ n, n ≤ K → ten3Norm (fun x y w => ∑ j ∈ Finset.range n,
        (((flowTc (lam D N A) z - (j + 1) * (S / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          (flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K)) (H (j + 1)) x y w -
            ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • H j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y w
              ∂(gueBlocks D N))) ≤
      (N : ℝ) ^ b / (N * (flowTc (lam D N A) z - n * (S / K)) ^ (3 / 2 : ℝ) *
        flowIm (lam D N A) z (n * (S / K)) ^ 3))
    (hL2 : ∀ w₁ w₂ : ℂ, (w₁ = z ∨ w₁ = star z) → (w₂ = z ∨ w₂ = star z) → ∀ k, k ≤ K →
      hsNorm (flowLmat (lam D N A) w₁ w₂ (k * (S / K)) (H k) -
          flowKmat (lam D N A) θ w₁ w₂ (k * (S / K))) ≤
        (N : ℝ) ^ τ₂ * ((flowTc (lam D N A) z / (flowTc (lam D N A) z - k * (S / K))) ^ 2 *
            hsNorm (Lmat (lam D N A) (H 0) w₁ w₂ - KTheta (lam D N A) θ w₁ w₂) +
          1 / (N * (flowTc (lam D N A) z - k * (S / K)) ^ 2 *
            flowIm (lam D N A) z (k * (S / K)) ^ 2)))
    (hY : ∀ w₁ w₂ : ℂ, (w₁ = z ∨ w₁ = star z) → (w₂ = z ∨ w₂ = star z) →
      flowTc (lam D N A) z ^ 2 * hsNorm (Lmat (lam D N A) (H 0) w₁ w₂ -
        KTheta (lam D N A) θ w₁ w₂) ≤ Y / (N * (mExt (lam D N A) z).im ^ 2))
    (hY0 : 0 ≤ Y)
    (hγ : (flowTc (lam D N A) z / (flowTc (lam D N A) z - S)) ^ (flowTc (lam D N A) z) ≤
      Real.exp 1)
    (hlog : Real.log (flowTc (lam D N A) z / (flowTc (lam D N A) z - S)) ≤
      Real.log (Real.exp 1 * N))
    (hfin1 : Real.exp 1 ^ 2 ≤ (N : ℝ) ^ τ')
    (hfin2 : Real.exp 1 ^ 4 * (3 * ((N : ℝ) ^ b + Real.exp 1 ^ 2 * D ^ 2 * (N : ℝ) ^ a +
        N * D ^ 2 * (K * (S / K) ^ 2) * ((N : ℝ) ^ (20 : ℝ) +
          38 * D ^ 2 * (flowTc (lam D N A) z - S)⁻¹ ^ 2 *
            (2 * D ^ 4 * Real.exp 1 ^ 2 * (1 + (flowTc (lam D N A) z - S)⁻¹) ^ 3))) +
        3 * D ^ 4 * (N : ℝ) ^ (τ₂ + τg) * (1 + Real.exp 1 * Y)) * Real.log (Real.exp 1 * N) +
      ((N : ℝ) ^ b + Real.exp 1 ^ 2 * D ^ 2 * (N : ℝ) ^ a +
        N * D ^ 2 * (K * (S / K) ^ 2) * ((N : ℝ) ^ (20 : ℝ) +
          38 * D ^ 2 * (flowTc (lam D N A) z - S)⁻¹ ^ 2 *
            (2 * D ^ 4 * Real.exp 1 ^ 2 * (1 + (flowTc (lam D N A) z - S)⁻¹) ^ 3))) ≤
      (N : ℝ) ^ τ' * (N : ℝ) ^ εg) :
    ∀ k, k ≤ K → ten3Norm (flowLten3 (lam D N A) z₁ z₂ z₃ (k * (S / K)) (H k) -
        flowKten3 (lam D N A) θ z₁ z₂ z₃ (k * (S / K))) ≤
      (N : ℝ) ^ τ' * ((flowTc (lam D N A) z / (flowTc (lam D N A) z - k * (S / K))) ^ 3 *
          ten3Norm (Lten3 (lam D N A) (H 0) z₁ z₂ z₃ - KTheta3 (lam D N A) θ z₁ z₂ z₃) +
        (N : ℝ) ^ εg / (N * (flowTc (lam D N A) z - k * (S / K)) ^ 3 *
          flowIm (lam D N A) z (k * (S / K)) ^ 3)) := by
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  set h := S / K with hhdef
  have hh : 0 < h := div_pos hSpos hKpos
  have hKh : (K : ℝ) * h = S := by rw [hhdef]; field_simp
  set q₀ := flowTc (lam D N A) z with hq₀
  have hq0 : 0 < q₀ := by linarith
  set e := Real.exp 1 with he
  have he1 : 1 ≤ e := Real.one_le_exp (by norm_num)
  have he0 : 0 < e := by linarith
  have hgrid : ∀ k : ℕ, k ≤ K → 0 ≤ (k : ℝ) * h ∧ (k : ℝ) * h ≤ S := fun k hk =>
    ⟨by positivity, (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le).trans_eq hKh⟩
  set ι₀ := (mExt (lam D N A) z).im with hι₀def
  have hι0 : 0 < ι₀ := (LF2_flow D N hD1 hN1 A hA z hz S hSt 0 le_rfl hSpos.le).2.2.1
  -- the flow at the grid times
  have hfl : ∀ k : ℕ, k ≤ K → 0 < q₀ - k * h ∧ q₀ - k * h ≤ 1 ∧
      0 < flowIm (lam D N A) z (k * h) ∧ flowIm (lam D N A) z (k * h) ≤ 1 ∧
      ι₀ ≤ flowIm (lam D N A) z (k * h) ∧ flowIm (lam D N A) z (k * h) ^ 3 ≤ e ^ 2 * ι₀ ^ 3 ∧
      flowIm (lam D N A) z (k * h) ^ 2 ≤ e * ι₀ ^ 2 ∧
      0 < (charFlowZ (lam D N A) z (k * h)).im ∧
      (q₀ - k * h) * flowIm (lam D N A) z (k * h) ≤ (charFlowZ (lam D N A) z (k * h)).im := by
    intro k hk
    obtain ⟨h0, hS'⟩ := hgrid k hk
    obtain ⟨hη, hιeq, -, hι1, -, -, hqι⟩ := LF2_flow D N hD1 hN1 A hA z hz S hSt (k * h) h0 hS'
    have hek : 1 ≤ Real.exp (k * h / 2) := Real.one_le_exp (by positivity)
    have hek2 : Real.exp (k * h / 2) ^ 3 ≤ e ^ 2 := by
      rw [← Real.exp_nat_mul, he, ← Real.exp_nat_mul]
      exact Real.exp_le_exp.2 (by push_cast; linarith)
    have hek3 : Real.exp (k * h / 2) ^ 2 ≤ e := by
      rw [← Real.exp_nat_mul, he]
      exact Real.exp_le_exp.2 (by push_cast; linarith)
    refine ⟨by linarith, by linarith, by rw [hιeq]; positivity, hι1.le, ?_, ?_, ?_, hη, hqι⟩
    · rw [hιeq]; nlinarith
    · rw [hιeq, mul_pow]; exact mul_le_mul_of_nonneg_right hek2 (by positivity)
    · rw [hιeq, mul_pow]; exact mul_le_mul_of_nonneg_right hek3 (by positivity)
  have hqK : (e * N)⁻¹ ≤ q₀ - S := by
    obtain ⟨-, hιeq, -, hιS1, -, -, -⟩ := LF2_flow D N hD1 hN1 A hA z hz S hSt S hSpos.le le_rfl
    have hup := LF2_flow_up D N hD1 hN1 A hA z hz S hSt hq1 S hSpos.le le_rfl
    have hιS : 0 < flowIm (lam D N A) z S := by rw [hιeq]; positivity
    have h1 := hηN S hSpos.le le_rfl
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have : (1 : ℝ) < N * (charFlowZ (lam D N A) z S).im := by
      rw [inv_lt_iff_one_lt_mul₀ hNpos] at h1; linarith
    nlinarith
  have hqS : 0 < q₀ - S := by linarith
  -- the weights `p_k = q_k^{3/2}` and `ψ_k = N p_k (Im m_k)³`
  set p : ℕ → ℝ := fun k => (q₀ - k * h) ^ (3 / 2 : ℝ) with hpdef
  have hp : ∀ k, k ≤ K → 0 < p k ∧ p k ≤ 1 ∧ p k ^ 2 = (q₀ - k * h) ^ 3 := by
    intro k hk
    obtain ⟨hq, hq1', -⟩ := hfl k hk
    refine ⟨Real.rpow_pos_of_pos hq _, Real.rpow_le_one hq.le hq1' (by norm_num), ?_⟩
    simp only [hpdef]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]; norm_num
  set ψ : ℕ → ℝ := fun k => N * p k * flowIm (lam D N A) z (k * h) ^ 3 with hψdef
  have hψ : ∀ k, k ≤ K → 0 < ψ k ∧ ψ k ≤ N := by
    intro k hk
    obtain ⟨-, -, hι, hι1, -⟩ := hfl k hk
    obtain ⟨hp0, hp1, -⟩ := hp k hk
    refine ⟨by simp only [hψdef]; positivity, ?_⟩
    simp only [hψdef]
    have : flowIm (lam D N A) z (k * h) ^ 3 ≤ 1 := pow_le_one₀ hι.le hι1
    have : p k * flowIm (lam D N A) z (k * h) ^ 3 ≤ 1 := by nlinarith
    nlinarith
  -- the objects of the recursion
  set Lt : ℕ → Fin D → Fin D → Fin D → ℂ := fun k =>
    flowLten3 (lam D N A) z₁ z₂ z₃ (k * h) (H k) with hLt
  set Kt : ℕ → Fin D → Fin D → Fin D → ℂ := fun k =>
    flowKten3 (lam D N A) θ z₁ z₂ z₃ (k * h) with hKt
  set Et : ℕ → Fin D → Fin D → Fin D → ℂ := fun j x y w =>
    ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * h) (Real.exp (-h / 2) • H j +
      Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X)) x y w ∂(gueBlocks D N)
    with hEt
  set Lm : ℂ → ℂ → ℕ → Matrix (Fin D) (Fin D) ℂ := fun w₁ w₂ k =>
    flowLmat (lam D N A) w₁ w₂ (k * h) (H k) with hLm
  set Km : ℂ → ℂ → ℕ → Matrix (Fin D) (Fin D) ℂ := fun w₁ w₂ k =>
    flowKmat (lam D N A) θ w₁ w₂ (k * h) with hKm
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℕ → EuclideanSpace ℂ (Fin D × Fin D × Fin D),
      Δ = fun k => LF2_vec (fun x y w => ((p k : ℝ) : ℂ) * (Lt k x y w - Kt k x y w)) :=
    ⟨_, rfl⟩
  obtain ⟨Mid, hMid⟩ : ∃ Mid : ℕ → Fin D → Fin D → Fin D → ℂ, Mid = fun (k : ℕ) x y w =>
      ∑ a, (((q₀ - k * h : ℝ) : ℂ) * (Lm z₁ z₂ k x a - Km z₁ z₂ k x a) *
          (((p k : ℝ) : ℂ) * Lt k a y w) +
        ((q₀ - k * h : ℝ) : ℂ) * (Lm z₂ z₃ k y a - Km z₂ z₃ k y a) *
          (((p k : ℝ) : ℂ) * Lt k x a w) +
        ((q₀ - k * h : ℝ) : ℂ) * (Lm z₃ z₁ k w a - Km z₃ z₁ k w a) *
          (((p k : ℝ) : ℂ) * Lt k x y a)) := ⟨_, rfl⟩
  obtain ⟨Mj, hMj⟩ : ∃ Mj : ℕ → Fin D → Fin D → Fin D → ℂ, Mj = fun j x y w =>
      ((p (j + 1) : ℝ) : ℂ) * (Lt (j + 1) x y w - Et j x y w) := ⟨_, rfl⟩
  obtain ⟨Dr, hDr⟩ : ∃ Dr : ℕ → Fin D → Fin D → Fin D → ℂ, Dr = fun j x y w =>
      ((p (j + 1) : ℝ) : ℂ) * Et j x y w - ((p j : ℝ) : ℂ) * Lt j x y w -
        (h : ℂ) * (((q₀ - j * h) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((3 / 2 : ℂ) *
          ((q₀ - j * h - 1 : ℝ) : ℂ) * Lt j x y w + ((q₀ - j * h : ℝ) : ℂ) * ∑ a,
            (Lm z₁ z₂ j x a * Lt j a y w + Lm z₂ z₃ j y a * Lt j x a w +
              Lm z₃ z₁ j w a * Lt j x y a)) := ⟨_, rfl⟩
  obtain ⟨rK, hrK⟩ : ∃ rK : ℕ → Fin D → Fin D → Fin D → ℂ, rK = fun j x y w =>
      ((p (j + 1) : ℝ) : ℂ) * Kt (j + 1) x y w - ((p j : ℝ) : ℂ) * Kt j x y w -
        (h : ℂ) * (((q₀ - j * h) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((3 / 2 : ℂ) *
          ((q₀ - j * h - 1 : ℝ) : ℂ) * Kt j x y w + ((q₀ - j * h : ℝ) : ℂ) * ∑ a,
            (Km z₁ z₂ j x a * Kt j a y w + Km z₂ z₃ j y a * Kt j x a w +
              Km z₃ z₁ j w a * Kt j x y a)) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → EuclideanSpace ℂ (Fin D × Fin D × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Fin D × Fin D × Fin D), T = fun k => if k < K then
        LF2_op3 (Km z₁ z₂ k) (Km z₂ z₃ k) (Km z₃ z₁ k) (q₀ - k * h) else 0 := ⟨_, rfl⟩
  obtain ⟨ℰ, hℰdef⟩ : ∃ ℰ : ℕ → EuclideanSpace ℂ (Fin D × Fin D × Fin D),
      ℰ = fun k => ∑ j ∈ Finset.range k, LF2_vec (Mj j + Dr j - rK j) := ⟨_, rfl⟩
  have hℰ0 : ℰ 0 = 0 := by rw [hℰdef]; simp
  -- the operator bound
  set c := 3 / 2 * (1 + q₀) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hc3 : c ≤ 3 := by rw [hc]; linarith
  have hTn : ∀ k, ‖T k‖ ≤ c := by
    intro k
    rw [hTdef]
    dsimp only
    split_ifs with hk
    · refine ContinuousLinearMap.opNorm_le_bound _ hc0 fun v => ?_
      rw [LF2_op3_apply, LF2_norm_vec, LF2_norm_mat]
      obtain ⟨h0, hS'⟩ := hgrid k hk.le
      refine (LF2_tOp3 D N A hA z hz S hSt θ hθ₀ hθ₁ z₁ z₂ z₃ h₁ h₂ h₃ (k * h) h0 hS'
        (LF2_mat v)).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
      rw [hc]; nlinarith
    · rw [norm_zero]; exact hc0
  -- the recursion
  have hrec : ∀ k, k < K → Δ (k + 1) - ℰ (k + 1) = Δ k - ℰ k +
      ((h / (q₀ - (0 + k * h)) : ℝ) : ℂ) • (T k (Δ k) + LF2_vec (Mid k)) := by
    intro k hk
    have hqk := (hfl k hk.le).1
    have hT : T k = LF2_op3 (Km z₁ z₂ k) (Km z₂ z₃ k) (Km z₃ z₁ k) (q₀ - k * h) := by
      rw [hTdef]; simp [hk]
    have hℰs : ℰ (k + 1) = ℰ k + LF2_vec (Mj k + Dr k - rK k) := by
      rw [hℰdef]; simp only [Finset.sum_range_succ]
    rw [hT, hℰs, LF2_op3_apply]
    have hg : ((h / (q₀ - (0 + k * h)) : ℝ) : ℂ) * ((q₀ - k * h : ℝ) : ℂ) = (h : ℂ) := by
      rw [zero_add, ← Complex.ofReal_mul, div_mul_cancel₀ _ hqk.ne']
    have key : Δ (k + 1) - Δ k - ((h / (q₀ - (0 + k * h)) : ℝ) : ℂ) •
        (LF2_vec (LF2_top (Km z₁ z₂ k) (Km z₂ z₃ k) (Km z₃ z₁ k) (q₀ - k * h)
          (LF2_mat (Δ k))) + LF2_vec (Mid k)) = LF2_vec (Mj k + Dr k - rK k) := by
      rw [hΔ]
      dsimp only
      rw [LF2_mat_vec, ← map_add, ← map_smul, ← map_sub, ← map_sub]
      congr 1
      funext x y w
      have hcast : ((k + 1 : ℕ) : ℝ) * h = ((k : ℝ) + 1) * h := by push_cast; ring
      have hcast2 : (((k : ℝ) + 1) * h) = (k : ℝ) * h + h := by ring
      have := LF2_step (q₀ - k * h) (q₀ - (k + 1 : ℕ) * h) h _ hqk hg (Lt k) (Kt k) (Lt (k + 1))
        (Kt (k + 1)) (Et k) (Lm z₁ z₂ k) (Lm z₂ z₃ k) (Lm z₃ z₁ k) (Km z₁ z₂ k) (Km z₂ z₃ k)
        (Km z₃ z₁ k) x y w
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hMid, hMj, hDr, hrK, hpdef]
      linear_combination this
    rw [← key]
    abel
  -- bounds on the pieces
  have hDΔ : ∀ k, k ≤ K → ‖Δ k‖ = p k * ten3Norm (Lt k - Kt k) := by
    intro k hk
    rw [hΔ]
    dsimp only
    rw [LF2_norm_vec]
    have := LF2_ten_smul ((p k : ℝ) : ℂ) (Lt k - Kt k)
    simp only [Pi.sub_apply] at this
    rw [this, Complex.norm_real, Real.norm_of_nonneg (hp k hk).1.le]
  -- the start
  have hΔ0 : ‖Δ 0‖ = p 0 * ten3Norm (Lten3 (lam D N A) (H 0) z₁ z₂ z₃ -
      KTheta3 (lam D N A) θ z₁ z₂ z₃) := by
    rw [hDΔ 0 (Nat.zero_le K)]
    obtain ⟨z0L, z0K⟩ := LF2_zero3 (lam D N A) θ z₁ z₂ z₃ (H 0)
    simp only [hLt, hKt, Nat.cast_zero, zero_mul, z0L, z0K]
  -- the drift errors
  have hDrb : ∀ j, j < K → ten3Norm (Dr j) ≤ D ^ 2 * (h * ((N : ℝ) ^ a /
      (N * (q₀ - j * h) ^ (5 / 2 : ℝ) * flowIm (lam D N A) z (j * h) ^ 3)) +
        h ^ 2 * (N : ℝ) ^ (20 : ℝ)) := by
    intro j hj
    refine LF2_ten_entry hD1 _ _ (by
      have := Real.rpow_nonneg hNpos.le a
      have := (hfl j hj.le).1
      have := (hfl j hj.le).2.2.1
      have := Real.rpow_nonneg (hfl j hj.le).1.le (5 / 2 : ℝ)
      positivity) fun x y w => ?_
    refine le_of_eq_of_le ?_ (hdrift j hj x y w)
    congr 1
    rw [hDr, hEt, hLt, hLm]
    simp only [hpdef]
    rw [integral_const_mul, show ((j : ℝ) + 1) * h = j * h + h by ring,
      show ((j + 1 : ℕ) : ℝ) * h = j * h + h by push_cast; ring, sub_sub,
      show q₀ - (j * h + h) = q₀ - (j * h + h) from rfl]
  -- the errors of the Riccati equation
  set Lk := 38 * D ^ 2 * (q₀ - S)⁻¹ ^ 2 * (2 * D ^ 4 * e ^ 2 * (1 + (q₀ - S)⁻¹) ^ 3) with hLk
  have hLk0 : 0 ≤ Lk := by rw [hLk]; have := inv_pos.2 hqS; positivity
  have hrKb : ∀ j, j < K → ten3Norm (rK j) ≤ D ^ 2 * (Lk * h ^ 2) := by
    intro j hj
    refine LF2_ten_entry hD1 _ _ (by positivity) fun x y w => ?_
    have hu := (hgrid j hj.le).1
    have huh : (j : ℝ) * h + h ≤ S := by
      have := (hgrid (j + 1) hj).2; push_cast at this; linarith
    have hk := LF2_K3disc D N A hA z hz S hSt hq1 θ hθ₀ hθ₁ z₁ z₂ z₃ h₁ h₂ h₃ (j * h) h hu hh.le
      huh x y w
    refine le_of_eq_of_le ?_ hk
    congr 1
    rw [hrK, hKt, hKm]
    simp only [hpdef]
    rw [show ((j + 1 : ℕ) : ℝ) * h = j * h + h by push_cast; ring]
  -- `ℰ`
  have hι3 : ∀ j k, j ≤ k → k ≤ K → flowIm (lam D N A) z (k * h) ^ 3 ≤
      e ^ 2 * flowIm (lam D N A) z (j * h) ^ 3 := by
    intro j k hjk hkK
    have h1 := (hfl k hkK).2.2.2.2.2.1
    have h2 := (hfl j (hjk.trans hkK)).2.2.2.2.1
    have h3 : ι₀ ^ 3 ≤ flowIm (lam D N A) z (j * h) ^ 3 := pow_le_pow_left₀ hι0.le h2 3
    nlinarith
  set Eb := (N : ℝ) ^ b + e ^ 2 * D ^ 2 * (N : ℝ) ^ a +
    N * D ^ 2 * (K * h ^ 2) * ((N : ℝ) ^ (20 : ℝ) + Lk) with hEb
  have hℰb : ∀ k, k ≤ K → ‖ℰ k‖ ≤ Eb / ψ k := by
    intro k hk
    obtain ⟨hψk, hψN⟩ := hψ k hk
    obtain ⟨hqk, -, hιk, hιk1, -⟩ := hfl k hk
    have hsum : ℰ k = LF2_vec (∑ j ∈ Finset.range k, Mj j) +
        LF2_vec (∑ j ∈ Finset.range k, Dr j) - LF2_vec (∑ j ∈ Finset.range k, rK j) := by
      rw [hℰdef]
      dsimp only
      rw [← map_add, ← map_sub, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, map_sum]
    have hM : ‖LF2_vec (∑ j ∈ Finset.range k, Mj j)‖ ≤ (N : ℝ) ^ b / ψ k := by
      rw [LF2_norm_vec]
      have e1 : (∑ j ∈ Finset.range k, Mj j) = fun x y w => ∑ j ∈ Finset.range k,
          (((q₀ - (j + 1) * h) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
            (flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * h) (H (j + 1)) x y w -
              ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * h)
                (Real.exp (-h / 2) • H j +
                  Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X)) x y w
                ∂(gueBlocks D N)) := by
        funext x y w
        rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hMj, hLt, hEt, hpdef]
        push_cast
        ring_nf
      rw [e1]
      refine (hmart k hk).trans (le_of_eq ?_)
      simp only [hψdef, hpdef]
    have hDs : ‖LF2_vec (∑ j ∈ Finset.range k, Dr j)‖ ≤
        e ^ 2 * D ^ 2 * (N : ℝ) ^ a / ψ k + D ^ 2 * (K * h ^ 2) * (N : ℝ) ^ (20 : ℝ) := by
      rw [map_sum]
      refine (norm_sum_le _ _).trans ?_
      simp only [LF2_norm_vec]
      have hkh : (k : ℝ) * h < q₀ := by linarith [(hgrid k hk).2]
      have hR := riemann_rpow_le 0 h q₀ (5 / 2) hh (by norm_num) 0 k (Nat.zero_le k)
        (by rw [zero_add]; exact hkh)
      rw [← Finset.range_eq_Ico] at hR
      simp only [zero_add] at hR
      have e2 : (q₀ - k * h) ^ (1 - (5 / 2 : ℝ)) / (5 / 2 - 1) = 2 / 3 * (p k)⁻¹ := by
        simp only [hpdef]
        rw [show (1 - (5 / 2 : ℝ)) = -(3 / 2) by norm_num, Real.rpow_neg hqk.le]
        norm_num
        ring
      rw [e2] at hR
      have hNa : 0 ≤ (N : ℝ) ^ a := Real.rpow_nonneg hNpos.le _
      calc ∑ j ∈ Finset.range k, ten3Norm (Dr j)
          ≤ ∑ j ∈ Finset.range k, (D ^ 2 * ((N : ℝ) ^ a / (N * ι₀ ^ 3)) *
              (h * (q₀ - j * h) ^ (-(5 / 2 : ℝ))) + D ^ 2 * h ^ 2 * (N : ℝ) ^ (20 : ℝ)) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjk : j < k := Finset.mem_range.1 hj
            have hjK : j < K := lt_of_lt_of_le hjk hk
            refine (hDrb j hjK).trans ?_
            obtain ⟨hqj, -, hιj, -, hι0j, -⟩ := hfl j hjK.le
            have hι3 : ι₀ ^ 3 ≤ flowIm (lam D N A) z (j * h) ^ 3 := pow_le_pow_left₀ hι0.le hι0j 3
            have e3 : (q₀ - j * h) ^ (-(5 / 2 : ℝ)) = ((q₀ - j * h) ^ (5 / 2 : ℝ))⁻¹ :=
              Real.rpow_neg hqj.le _
            rw [e3]
            have hq52 : 0 < (q₀ - j * h) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hqj _
            have h1 : h * ((N : ℝ) ^ a / (N * (q₀ - j * h) ^ (5 / 2 : ℝ) *
                flowIm (lam D N A) z (j * h) ^ 3)) ≤
                (N : ℝ) ^ a / (N * ι₀ ^ 3) * (h * ((q₀ - j * h) ^ (5 / 2 : ℝ))⁻¹) := by
              rw [show h * ((N : ℝ) ^ a / (N * (q₀ - j * h) ^ (5 / 2 : ℝ) *
                  flowIm (lam D N A) z (j * h) ^ 3)) = (N : ℝ) ^ a / (N *
                  flowIm (lam D N A) z (j * h) ^ 3) * (h * ((q₀ - j * h) ^ (5 / 2 : ℝ))⁻¹) by
                field_simp]
              gcongr
            nlinarith [sq_nonneg (D : ℝ)]
        _ = D ^ 2 * ((N : ℝ) ^ a / (N * ι₀ ^ 3)) *
              (∑ j ∈ Finset.range k, (h * (q₀ - j * h) ^ (-(5 / 2 : ℝ)))) +
            D ^ 2 * (k * h ^ 2) * (N : ℝ) ^ (20 : ℝ) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
              nsmul_eq_mul]
            ring
        _ ≤ D ^ 2 * ((N : ℝ) ^ a / (N * ι₀ ^ 3)) * (2 / 3 * (p k)⁻¹) +
            D ^ 2 * (K * h ^ 2) * (N : ℝ) ^ (20 : ℝ) := by
            have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk
            gcongr
        _ ≤ e ^ 2 * D ^ 2 * (N : ℝ) ^ a / ψ k + D ^ 2 * (K * h ^ 2) * (N : ℝ) ^ (20 : ℝ) := by
            refine add_le_add ?_ le_rfl
            have hι3k := (hfl k hk).2.2.2.2.2.1
            have hpk := (hp k hk).1
            have hιk3 : 0 < flowIm (lam D N A) z (k * h) ^ 3 := pow_pos hιk 3
            have key : 1 / ι₀ ^ 3 ≤ e ^ 2 / flowIm (lam D N A) z (k * h) ^ 3 := by
              rw [div_le_div_iff₀ (pow_pos hι0 3) hιk3]; linarith
            have hA0 : 0 ≤ (2 / 3 : ℝ) * (D ^ 2 * (N : ℝ) ^ a / (N * p k)) := by positivity
            calc D ^ 2 * ((N : ℝ) ^ a / (N * ι₀ ^ 3)) * (2 / 3 * (p k)⁻¹)
                = (2 / 3 : ℝ) * (D ^ 2 * (N : ℝ) ^ a / (N * p k)) * (1 / ι₀ ^ 3) := by
                  field_simp
              _ ≤ (2 / 3 : ℝ) * (D ^ 2 * (N : ℝ) ^ a / (N * p k)) *
                  (e ^ 2 / flowIm (lam D N A) z (k * h) ^ 3) := mul_le_mul_of_nonneg_left key hA0
              _ ≤ 1 * (D ^ 2 * (N : ℝ) ^ a / (N * p k)) *
                  (e ^ 2 / flowIm (lam D N A) z (k * h) ^ 3) := by
                  gcongr; norm_num
              _ = e ^ 2 * D ^ 2 * (N : ℝ) ^ a / ψ k := by
                  simp only [hψdef]; field_simp
    have hRs : ‖LF2_vec (∑ j ∈ Finset.range k, rK j)‖ ≤ D ^ 2 * (K * h ^ 2) * Lk := by
      rw [map_sum]
      refine (norm_sum_le _ _).trans ?_
      simp only [LF2_norm_vec]
      calc ∑ j ∈ Finset.range k, ten3Norm (rK j) ≤ ∑ _j ∈ Finset.range k, D ^ 2 * (Lk * h ^ 2) :=
            Finset.sum_le_sum fun j hj => hrKb j (lt_of_lt_of_le (Finset.mem_range.1 hj) hk)
        _ = D ^ 2 * (k * h ^ 2) * Lk := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        _ ≤ D ^ 2 * (K * h ^ 2) * Lk := by
            have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk
            gcongr
    rw [hsum]
    refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    have hX : 0 ≤ D ^ 2 * (K * h ^ 2) * ((N : ℝ) ^ (20 : ℝ) + Lk) := by
      have := Real.rpow_nonneg hNpos.le (20 : ℝ); positivity
    have hX2 : D ^ 2 * (K * h ^ 2) * ((N : ℝ) ^ (20 : ℝ) + Lk) ≤
        N * D ^ 2 * (K * h ^ 2) * ((N : ℝ) ^ (20 : ℝ) + Lk) / ψ k := by
      rw [le_div_iff₀ hψk]
      have := mul_le_mul_of_nonneg_left hψN hX
      nlinarith
    rw [hEb, add_div, add_div]
    have e4 : D ^ 2 * (K * h ^ 2) * (N : ℝ) ^ (20 : ℝ) + D ^ 2 * (K * h ^ 2) * Lk =
        D ^ 2 * (K * h ^ 2) * ((N : ℝ) ^ (20 : ℝ) + Lk) := by ring
    linarith
  -- the middle term
  have hLg : ∀ j, j < K → ∀ x y w : Fin D, ‖Lt j x y w‖ ≤
      D * ((N : ℝ) ^ τg * (flowIm (lam D N A) z (j * h) /
        (charFlowZ (lam D N A) z (j * h)).im ^ 2)) := by
    intro j hj x y w
    obtain ⟨hHj, hgj⟩ := hgood j hj
    have hjs : (j : ℝ) * h < q₀ := by linarith [(hgrid j hj.le).2]
    exact LF2_Lten_good D N hD1 hN1 A z hz (j * h) hjs τg (H j) hHj hgj z₁ z₂ z₃ h₁ h₂ h₃ x y w
  have hMidb : ∀ j, j < K → ‖LF2_vec (Mid j)‖ ≤
      3 * D ^ 4 * (N : ℝ) ^ (τ₂ + τg) * (1 + e * Y) / ψ j := by
    intro j hj
    obtain ⟨hqj, hqj1, hιj, hιj1, hι0j, -, hι2j, hηj, hqιj⟩ := hfl j hj.le
    obtain ⟨hpj, -, hpj2⟩ := hp j hj.le
    have hψj := (hψ j hj.le).1
    set m₁ := (N : ℝ) ^ τ₂ * (1 + e * Y) / (N * (q₀ - j * h) * flowIm (lam D N A) z (j * h) ^ 2)
      with hm₁
    set m₂ := D * (N : ℝ) ^ τg * p j / ((q₀ - j * h) ^ 2 * flowIm (lam D N A) z (j * h)) with hm₂
    have hm₁0 : 0 ≤ m₁ := by rw [hm₁]; have := Real.rpow_nonneg hNpos.le τ₂; positivity
    have hm₂0 : 0 ≤ m₂ := by rw [hm₂]; have := Real.rpow_nonneg hNpos.le τg; positivity
    have hA1 : ∀ w₁ w₂ : ℂ, (w₁ = z ∨ w₁ = star z) → (w₂ = z ∨ w₂ = star z) → ∀ c d : Fin D,
        ‖((q₀ - j * h : ℝ) : ℂ) * (Lm w₁ w₂ j c d - Km w₁ w₂ j c d)‖ ≤ m₁ := by
      intro w₁ w₂ hw₁ hw₂ c d
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hqj.le]
      have h1 : ‖Lm w₁ w₂ j c d - Km w₁ w₂ j c d‖ ≤
          hsNorm (flowLmat (lam D N A) w₁ w₂ (j * h) (H j) -
            flowKmat (lam D N A) θ w₁ w₂ (j * h)) := by
        have := LF2_entry_hs (flowLmat (lam D N A) w₁ w₂ (j * h) (H j) -
          flowKmat (lam D N A) θ w₁ w₂ (j * h)) c d
        rwa [Matrix.sub_apply] at this
      have h2 := hL2 w₁ w₂ hw₁ hw₂ j hj.le
      have h3 := hY w₁ w₂ hw₁ hw₂
      set X := hsNorm (Lmat (lam D N A) (H 0) w₁ w₂ - KTheta (lam D N A) θ w₁ w₂) with hX
      have hX0 : 0 ≤ X := Real.sqrt_nonneg _
      have h4 : (q₀ / (q₀ - j * h)) ^ 2 * X ≤ e * Y /
          (N * (q₀ - j * h) ^ 2 * flowIm (lam D N A) z (j * h) ^ 2) := by
        rw [div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        rw [le_div_iff₀ (by positivity)] at h3
        have h6 : q₀ ^ 2 * X * (N * (q₀ - j * h) ^ 2 * flowIm (lam D N A) z (j * h) ^ 2) ≤
            q₀ ^ 2 * X * (N * (q₀ - j * h) ^ 2 * (e * ι₀ ^ 2)) := by gcongr
        have h7 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ e * (q₀ - j * h) ^ 2)
        linarith
      have h5 : hsNorm (flowLmat (lam D N A) w₁ w₂ (j * h) (H j) -
          flowKmat (lam D N A) θ w₁ w₂ (j * h)) ≤ (N : ℝ) ^ τ₂ * ((1 + e * Y) /
            (N * (q₀ - j * h) ^ 2 * flowIm (lam D N A) z (j * h) ^ 2)) := by
        refine h2.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hNpos.le _))
        rw [add_div, one_div]
        linarith [h4]
      calc (q₀ - j * h) * ‖Lm w₁ w₂ j c d - Km w₁ w₂ j c d‖
          ≤ (q₀ - j * h) * ((N : ℝ) ^ τ₂ * ((1 + e * Y) /
            (N * (q₀ - j * h) ^ 2 * flowIm (lam D N A) z (j * h) ^ 2))) :=
            mul_le_mul_of_nonneg_left (h1.trans h5) hqj.le
        _ = m₁ := by rw [hm₁]; field_simp
    have hA2 : ∀ c d e' : Fin D, ‖((p j : ℝ) : ℂ) * Lt j c d e'‖ ≤ m₂ := by
      intro c d e'
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpj.le]
      have h1 := hLg j hj c d e'
      have h2 : flowIm (lam D N A) z (j * h) / (charFlowZ (lam D N A) z (j * h)).im ^ 2 ≤
          1 / ((q₀ - j * h) ^ 2 * flowIm (lam D N A) z (j * h)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := pow_le_pow_left₀ (by positivity) hqιj 2
        nlinarith
      calc p j * ‖Lt j c d e'‖ ≤ p j * (D * ((N : ℝ) ^ τg *
            (1 / ((q₀ - j * h) ^ 2 * flowIm (lam D N A) z (j * h))))) := by
            refine mul_le_mul_of_nonneg_left (h1.trans ?_) hpj.le
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2
              (Real.rpow_nonneg hNpos.le _)) hD0
        _ = m₂ := by rw [hm₂]; field_simp
    rw [LF2_norm_vec]
    refine (LF2_ten_entry hD1 _ (3 * D * (m₁ * m₂)) (by positivity) fun x y w => ?_).trans ?_
    · rw [hMid]
      dsimp only
      refine (norm_sum_le _ _).trans ?_
      calc ∑ a, ‖((q₀ - j * h : ℝ) : ℂ) * (Lm z₁ z₂ j x a - Km z₁ z₂ j x a) *
            (((p j : ℝ) : ℂ) * Lt j a y w) +
          ((q₀ - j * h : ℝ) : ℂ) * (Lm z₂ z₃ j y a - Km z₂ z₃ j y a) *
            (((p j : ℝ) : ℂ) * Lt j x a w) +
          ((q₀ - j * h : ℝ) : ℂ) * (Lm z₃ z₁ j w a - Km z₃ z₁ j w a) *
            (((p j : ℝ) : ℂ) * Lt j x y a)‖ ≤ ∑ _a : Fin D, 3 * (m₁ * m₂) := by
            refine Finset.sum_le_sum fun a _ => ?_
            refine norm_add₃_le.trans ?_
            have t1 := (norm_mul_le _ _).trans
              (mul_le_mul (hA1 z₁ z₂ h₁ h₂ x a) (hA2 a y w) (norm_nonneg _) hm₁0)
            have t2 := (norm_mul_le _ _).trans
              (mul_le_mul (hA1 z₂ z₃ h₂ h₃ y a) (hA2 x a w) (norm_nonneg _) hm₁0)
            have t3 := (norm_mul_le _ _).trans
              (mul_le_mul (hA1 z₃ z₁ h₃ h₁ w a) (hA2 x y a) (norm_nonneg _) hm₁0)
            linarith
        _ = 3 * D * (m₁ * m₂) := by simp; ring
    · have hq3 : (q₀ - j * h) ^ 3 = p j ^ 2 := hpj2.symm
      have e5 : m₁ * m₂ = (D * ((N : ℝ) ^ τ₂ * (N : ℝ) ^ τg) * (1 + e * Y)) *
          (p j / (N * (q₀ - j * h) ^ 3 * flowIm (lam D N A) z (j * h) ^ 3)) := by
        rw [hm₁, hm₂]; field_simp
      have e6 : p j / (N * (q₀ - j * h) ^ 3 * flowIm (lam D N A) z (j * h) ^ 3) =
          1 / ψ j := by
        simp only [hψdef]; rw [hq3]; field_simp
      rw [e5, e6, Real.rpow_add hNpos]
      apply le_of_eq
      ring
  -- the ratios
  have hrat0 : ∀ j k, j ≤ k → k ≤ K →
      ((q₀ - j * h) / (q₀ - k * h)) ^ (3 / 2 * q₀) ≤ e ^ 2 := by
    intro j k hjk hk
    obtain ⟨hqk, -⟩ := hfl k hk
    obtain ⟨hqj, -⟩ := hfl j (hjk.trans hk)
    have hb : (q₀ - j * h) / (q₀ - k * h) ≤ q₀ / (q₀ - S) := by
      have h1 : q₀ - j * h ≤ q₀ := by have := (hgrid j (hjk.trans hk)).1; linarith
      have h2 : q₀ - S ≤ q₀ - k * h := by have := (hgrid k hk).2; linarith
      calc (q₀ - j * h) / (q₀ - k * h) ≤ q₀ / (q₀ - k * h) :=
            div_le_div_of_nonneg_right h1 hqk.le
        _ ≤ q₀ / (q₀ - S) := div_le_div_of_nonneg_left hq0.le hqS h2
    have h0 : 0 ≤ (q₀ - j * h) / (q₀ - k * h) := div_nonneg hqj.le hqk.le
    calc ((q₀ - j * h) / (q₀ - k * h)) ^ (3 / 2 * q₀)
        ≤ (q₀ / (q₀ - S)) ^ (3 / 2 * q₀) := Real.rpow_le_rpow h0 hb (by positivity)
      _ = ((q₀ / (q₀ - S)) ^ q₀) ^ (3 / 2 : ℝ) := by
          rw [← Real.rpow_mul (div_nonneg hq0.le hqS.le)]; ring_nf
      _ ≤ e ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg (div_nonneg hq0.le hqS.le) _)
          hγ (by norm_num)
      _ ≤ e ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le he1 (by norm_num)
      _ = e ^ 2 := by norm_cast
  have hrat : ∀ j k, j < k → k ≤ K →
      ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ c ≤ e ^ 4 * ψ j / ψ k := by
    intro j k hjk hk
    obtain ⟨hqk, -⟩ := hfl k hk
    obtain ⟨hqj, -⟩ := hfl j (hjk.le.trans hk)
    have hqj1 := (hfl (j + 1) (by omega)).1
    have hr0 : 0 < (q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h) := div_pos hqj1 hqk
    have hcs : c = 3 / 2 + 3 / 2 * q₀ := by rw [hc]; ring
    rw [hcs, Real.rpow_add hr0]
    have h1 : ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ (3 / 2 : ℝ) ≤ p j / p k := by
      have hle : (q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h) ≤ (q₀ - j * h) / (q₀ - k * h) := by
        apply div_le_div_of_nonneg_right _ hqk.le
        push_cast; nlinarith
      refine (Real.rpow_le_rpow hr0.le hle (by norm_num)).trans (le_of_eq ?_)
      simp only [hpdef]
      exact Real.div_rpow hqj.le hqk.le _
    have h2 : ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ (3 / 2 * q₀) ≤ e ^ 2 :=
      hrat0 (j + 1) k (by omega) hk
    have h3 : p j / p k ≤ e ^ 2 * ψ j / ψ k := by
      have hι := hι3 j k hjk.le hk
      obtain ⟨hpj, -⟩ := hp j (hjk.le.trans hk)
      obtain ⟨hpk, -⟩ := hp k hk
      have hιj := (hfl j (hjk.le.trans hk)).2.2.1
      have hιk := (hfl k hk).2.2.1
      simp only [hψdef]
      rw [div_le_div_iff₀ hpk (by positivity)]
      have : p j * (N * p k * flowIm (lam D N A) z (k * h) ^ 3) ≤
          p j * (N * p k * (e ^ 2 * flowIm (lam D N A) z (j * h) ^ 3)) := by gcongr
      nlinarith
    have h4 : 0 ≤ ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ (3 / 2 : ℝ) :=
      Real.rpow_nonneg hr0.le _
    calc ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ (3 / 2 : ℝ) *
          ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ (3 / 2 * q₀)
        ≤ (e ^ 2 * ψ j / ψ k) * e ^ 2 := mul_le_mul (h1.trans h3) h2 (Real.rpow_nonneg hr0.le _)
          (by have := (hψ j (hjk.le.trans hk)).1; have := (hψ k hk).1; positivity)
      _ = e ^ 4 * ψ j / ψ k := by ring
  -- the Duhamel bound
  set X := 3 * Eb + 3 * D ^ 4 * (N : ℝ) ^ (τ₂ + τg) * (1 + e * Y) with hXdef
  have hEb0 : 0 ≤ Eb := by
    rw [hEb]
    have := Real.rpow_nonneg hNpos.le b
    have := Real.rpow_nonneg hNpos.le a
    have := Real.rpow_nonneg hNpos.le (20 : ℝ)
    positivity
  have hX0 : 0 ≤ X := by
    rw [hXdef]; have := Real.rpow_nonneg hNpos.le (τ₂ + τg); positivity
  have hXb : ∀ k, k < K → c * ‖ℰ k‖ + ‖LF2_vec (Mid k)‖ ≤ X / ψ k := by
    intro k hk
    have hψk := (hψ k hk.le).1
    have h1 := hℰb k hk.le
    have h2 := hMidb k hk
    have h3 : c * ‖ℰ k‖ ≤ 3 * (Eb / ψ k) :=
      mul_le_mul hc3 h1 (norm_nonneg _) (by norm_num)
    rw [hXdef, add_div, mul_div_assoc]
    linarith
  intro k hk
  have hduh := LF2_duh T h q₀ c hh hc0 hTn K (by rw [hKh]; exact hSt) Δ ℰ (fun k => LF2_vec (Mid k))
    hℰ0 hrec ψ (fun k hk => (hψ k hk).1) X (e ^ 4) hX0 (by positivity) hXb hrat k hk
  obtain ⟨hqk, -, hιk, -⟩ := hfl k hk
  obtain ⟨hpk, -, hpk2⟩ := hp k hk
  obtain ⟨hp0, -, hp02⟩ := hp 0 (Nat.zero_le K)
  have hψk := (hψ k hk).1
  rw [hDΔ k hk, hΔ0] at hduh
  have hEk := hℰb k hk
  change ten3Norm (Lt k - Kt k) ≤ (N : ℝ) ^ τ' * ((q₀ / (q₀ - k * h)) ^ 3 *
      ten3Norm (Lten3 (lam D N A) (H 0) z₁ z₂ z₃ - KTheta3 (lam D N A) θ z₁ z₂ z₃) +
    (N : ℝ) ^ εg / (N * (q₀ - k * h) ^ 3 * flowIm (lam D N A) z (k * h) ^ 3))
  set Tk := ten3Norm (Lt k - Kt k) with hTk
  set X₃ := ten3Norm (Lten3 (lam D N A) (H 0) z₁ z₂ z₃ - KTheta3 (lam D N A) θ z₁ z₂ z₃) with hX₃
  have hX₃0 : 0 ≤ X₃ := Real.sqrt_nonneg _
  -- the first term
  have hq0k : q₀ - (0 : ℕ) * h = q₀ := by simp
  have hratk : (q₀ / (q₀ - k * h)) ^ c ≤ e ^ 2 * (p 0 / p k) := by
    have hr0 : 0 < q₀ / (q₀ - k * h) := div_pos hq0 hqk
    have hcs : c = 3 / 2 + 3 / 2 * q₀ := by rw [hc]; ring
    rw [hcs, Real.rpow_add hr0]
    have h1 : (q₀ / (q₀ - k * h)) ^ (3 / 2 : ℝ) = p 0 / p k := by
      simp only [hpdef, Nat.cast_zero, zero_mul, sub_zero]
      exact Real.div_rpow hq0.le hqk.le _
    have h2 := hrat0 0 k (Nat.zero_le k) hk
    simp only [Nat.cast_zero, zero_mul, sub_zero] at h2
    rw [h1, mul_comm]
    exact mul_le_mul_of_nonneg_right h2 (div_nonneg hp0.le hpk.le)
  have hlogk : Real.log (q₀ / (q₀ - k * h)) ≤ Real.log (e * N) := by
    refine le_trans (Real.log_le_log (div_pos hq0 hqk) ?_) hlog
    exact div_le_div_of_nonneg_left hq0.le hqS (by have := (hgrid k hk).2; linarith)
  have hlog0 : 0 ≤ Real.log (q₀ / (q₀ - k * h)) := Real.log_nonneg (by
    rw [le_div_iff₀ hqk]; have := (hgrid k hk).1; linarith)
  have hmain : p k * Tk ≤ e ^ 2 * (p 0 / p k) * (p 0 * X₃) +
      (e ^ 4 * X * Real.log (e * N) + Eb) / ψ k := by
    have h1 : (q₀ / (q₀ - k * h)) ^ c * (p 0 * X₃) ≤ e ^ 2 * (p 0 / p k) * (p 0 * X₃) :=
      mul_le_mul_of_nonneg_right hratk (by positivity)
    have h2 : e ^ 4 * X * Real.log (q₀ / (q₀ - k * h)) / ψ k ≤
        e ^ 4 * X * Real.log (e * N) / ψ k := by
      gcongr
    rw [add_div]
    linarith
  have hfin : Tk ≤ e ^ 2 * (q₀ / (q₀ - k * h)) ^ 3 * X₃ +
      (e ^ 4 * X * Real.log (e * N) + Eb) / (N * (q₀ - k * h) ^ 3 *
        flowIm (lam D N A) z (k * h) ^ 3) := by
    have e1 : e ^ 2 * (p 0 / p k) * (p 0 * X₃) / p k = e ^ 2 * (q₀ / (q₀ - k * h)) ^ 3 * X₃ := by
      rw [div_pow, ← hpk2]
      have : q₀ ^ 3 = p 0 ^ 2 := by rw [hp02]; simp
      rw [this]
      field_simp
    have e2 : (e ^ 4 * X * Real.log (e * N) + Eb) / ψ k / p k =
        (e ^ 4 * X * Real.log (e * N) + Eb) / (N * (q₀ - k * h) ^ 3 *
          flowIm (lam D N A) z (k * h) ^ 3) := by
      simp only [hψdef]
      rw [← hpk2, div_div]
      congr 1
      ring
    rw [← e1, ← e2, ← add_div, le_div_iff₀ hpk, mul_comm]
    exact hmain
  have hNτ : 0 ≤ (N : ℝ) ^ τ' := Real.rpow_nonneg hNpos.le _
  have hfin2' : e ^ 4 * X * Real.log (e * N) + Eb ≤ (N : ℝ) ^ τ' * (N : ℝ) ^ εg := by
    refine le_trans (le_of_eq ?_) hfin2
    rw [hXdef, hEb, hLk]
  refine hfin.trans ?_
  have hma := mul_add ((N : ℝ) ^ τ') ((q₀ / (q₀ - k * h)) ^ 3 * X₃)
    ((N : ℝ) ^ εg / (N * (q₀ - k * h) ^ 3 * flowIm (lam D N A) z (k * h) ^ 3))
  have hden : 0 < N * (q₀ - k * h) ^ 3 * flowIm (lam D N A) z (k * h) ^ 3 := by positivity
  have k1 : e ^ 2 * (q₀ / (q₀ - k * h)) ^ 3 * X₃ ≤
      (N : ℝ) ^ τ' * ((q₀ / (q₀ - k * h)) ^ 3 * X₃) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hfin1 (by positivity)
  have k2 : (e ^ 4 * X * Real.log (e * N) + Eb) / (N * (q₀ - k * h) ^ 3 *
      flowIm (lam D N A) z (k * h) ^ 3) ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ εg /
        (N * (q₀ - k * h) ^ 3 * flowIm (lam D N A) z (k * h) ^ 3)) := by
    calc (e ^ 4 * X * Real.log (e * N) + Eb) / (N * (q₀ - k * h) ^ 3 *
          flowIm (lam D N A) z (k * h) ^ 3) ≤ (N : ℝ) ^ τ' * (N : ℝ) ^ εg /
          (N * (q₀ - k * h) ^ 3 * flowIm (lam D N A) z (k * h) ^ 3) :=
          div_le_div_of_nonneg_right hfin2' hden.le
      _ = _ := mul_div_assoc _ _ _
  linarith

/-- `C N^α ≤ N^β` for large `N` when `α < β`. -/
private lemma LF2_ev_pow (C α β : ℝ) (hαβ : α < β) :
    ∀ᶠ N : ℕ in Filter.atTop, C * (N : ℝ) ^ α ≤ (N : ℝ) ^ β := by
  have t : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (β - α)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [t.eventually_ge_atTop C, Filter.eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have e : (N : ℝ) ^ β = (N : ℝ) ^ (β - α) * (N : ℝ) ^ α := by
    rw [← Real.rpow_add hNpos]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hNpos.le _)

/-- `log(e N) ≤ (1 + s⁻¹) N^s` for `N ≥ 1`, `s > 0`. -/
private lemma LF2_log_le (N s : ℝ) (hN : 1 ≤ N) (hs : 0 < s) :
    Real.log (Real.exp 1 * N) ≤ (1 + s⁻¹) * N ^ s := by
  have hNpos : 0 < N := by linarith
  rw [Real.log_mul (Real.exp_pos 1).ne' hNpos.ne', Real.log_exp]
  have h1 := Real.log_le_rpow_div hNpos.le hs
  have h2 : 1 ≤ N ^ s := Real.one_le_rpow hN hs.le
  rw [div_eq_mul_inv] at h1
  nlinarith [inv_pos.2 hs]

/-- The arithmetic of the sharp bound of `flowL3_grid`: with the levels `τ'/16` (drift, good
event, `flowL2_grid`, start) and `τ'/2` (martingale), `K h² ≤ N^{-32}`, `ρ ≤ e N` and
`Y = 4 c N^{τ'/16} N^{ε_g}`, the total of the rows of the recursion is at most `N^{τ'} N^{ε_g}`. -/
private lemma LF2_ar_fin2 (N D c τ' εg Kh2 ρ Y : ℝ) (hN : 1 ≤ N) (hD : 1 ≤ D) (hc : 1 ≤ c)
    (hτ' : 0 < τ') (hεg : 0 < εg) (hKh2 : 0 ≤ Kh2) (hKh2' : Kh2 ≤ N ^ (-(32 : ℝ)))
    (hρ0 : 0 < ρ) (hρ : ρ ≤ Real.exp 1 * N) (hY : Y = 4 * c * N ^ (τ' / 16) * N ^ εg)
    (hlog : Real.log (Real.exp 1 * N) ≤ (1 + (τ' / 16)⁻¹) * N ^ (τ' / 16))
    (E2 : D ^ 2 * (1 + 608 * D ^ 6 * Real.exp 1 ^ 7) * N ^ (-(11 : ℝ)) ≤ 1)
    (E3 : 3 * Real.exp 1 ^ 4 * (2 + Real.exp 1 ^ 2 * D ^ 2) * (1 + (τ' / 16)⁻¹) *
      N ^ (τ' / 2 + τ' / 16) ≤ N ^ τ' / 3)
    (E4 : 3 * Real.exp 1 ^ 4 * D ^ 4 * (1 + 4 * Real.exp 1 * c) * (1 + (τ' / 16)⁻¹) *
      N ^ (τ' / 16 + τ' / 16 + τ' / 16 + τ' / 16) ≤ N ^ τ' / 3)
    (E5 : (2 + Real.exp 1 ^ 2 * D ^ 2) * N ^ (τ' / 2) ≤ N ^ τ' / 3) :
    Real.exp 1 ^ 4 * (3 * (N ^ (τ' / 2) + Real.exp 1 ^ 2 * D ^ 2 * N ^ (3 * (τ' / 16)) +
        N * D ^ 2 * Kh2 * (N ^ (20 : ℝ) + 38 * D ^ 2 * ρ ^ 2 *
          (2 * D ^ 4 * Real.exp 1 ^ 2 * (1 + ρ) ^ 3))) +
        3 * D ^ 4 * N ^ (τ' / 16 + τ' / 16) * (1 + Real.exp 1 * Y)) * Real.log (Real.exp 1 * N) +
      (N ^ (τ' / 2) + Real.exp 1 ^ 2 * D ^ 2 * N ^ (3 * (τ' / 16)) +
        N * D ^ 2 * Kh2 * (N ^ (20 : ℝ) + 38 * D ^ 2 * ρ ^ 2 *
          (2 * D ^ 4 * Real.exp 1 ^ 2 * (1 + ρ) ^ 3))) ≤ N ^ τ' * N ^ εg := by
  set e := Real.exp 1 with he
  have he1 : 1 ≤ e := Real.one_le_exp (by norm_num)
  have hNpos : 0 < N := by linarith
  have hD0 : 0 ≤ D := by linarith
  -- the tail of the Riccati errors
  set Lk := 38 * D ^ 2 * ρ ^ 2 * (2 * D ^ 4 * e ^ 2 * (1 + ρ) ^ 3) with hLk
  have heN : 1 ≤ e * N := one_le_mul_of_one_le_of_one_le he1 hN
  have hlog0 : 0 ≤ Real.log (e * N) := Real.log_nonneg heN
  have hLkb : Lk ≤ 608 * D ^ 6 * e ^ 7 * N ^ 5 := by
    have h1 : ρ ^ 2 ≤ (e * N) ^ 2 := pow_le_pow_left₀ hρ0.le hρ 2
    have h2 : (1 + ρ) ^ 3 ≤ (2 * (e * N)) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    rw [hLk]
    calc 38 * D ^ 2 * ρ ^ 2 * (2 * D ^ 4 * e ^ 2 * (1 + ρ) ^ 3)
        ≤ 38 * D ^ 2 * (e * N) ^ 2 * (2 * D ^ 4 * e ^ 2 * (2 * (e * N)) ^ 3) := by gcongr
      _ = 608 * D ^ 6 * e ^ 7 * N ^ 5 := by ring
  have hN5 : N ^ 5 ≤ N ^ (20 : ℝ) := by
    rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_right₀ hN (by norm_num)
  have hN20 : 0 ≤ N ^ (20 : ℝ) := Real.rpow_nonneg hNpos.le _
  have hT : N * D ^ 2 * Kh2 * (N ^ (20 : ℝ) + Lk) ≤ 1 := by
    have h1 : N ^ (20 : ℝ) + Lk ≤ (1 + 608 * D ^ 6 * e ^ 7) * N ^ (20 : ℝ) := by
      have : 608 * D ^ 6 * e ^ 7 * N ^ 5 ≤ 608 * D ^ 6 * e ^ 7 * N ^ (20 : ℝ) :=
        mul_le_mul_of_nonneg_left hN5 (by positivity)
      linarith
    have h2 : N * N ^ (-(32 : ℝ)) * N ^ (20 : ℝ) = N ^ (-(11 : ℝ)) := by
      rw [show (-(11 : ℝ)) = 1 + (-(32 : ℝ)) + 20 by norm_num, Real.rpow_add hNpos,
        Real.rpow_add hNpos, Real.rpow_one]
    have hLk0 : 0 ≤ Lk := by rw [hLk]; positivity
    calc N * D ^ 2 * Kh2 * (N ^ (20 : ℝ) + Lk)
        ≤ N * D ^ 2 * N ^ (-(32 : ℝ)) * ((1 + 608 * D ^ 6 * e ^ 7) * N ^ (20 : ℝ)) := by
          gcongr
      _ = D ^ 2 * (1 + 608 * D ^ 6 * e ^ 7) * (N * N ^ (-(32 : ℝ)) * N ^ (20 : ℝ)) := by ring
      _ = D ^ 2 * (1 + 608 * D ^ 6 * e ^ 7) * N ^ (-(11 : ℝ)) := by rw [h2]
      _ ≤ 1 := E2
  -- `Eb ≤ (2 + e² D²) N^{τ'/2}`
  have hN2 : 1 ≤ N ^ (τ' / 2) := Real.one_le_rpow hN (by positivity)
  have hN316 : N ^ (3 * (τ' / 16)) ≤ N ^ (τ' / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hEb : N ^ (τ' / 2) + e ^ 2 * D ^ 2 * N ^ (3 * (τ' / 16)) +
      N * D ^ 2 * Kh2 * (N ^ (20 : ℝ) + Lk) ≤ (2 + e ^ 2 * D ^ 2) * N ^ (τ' / 2) := by
    have : e ^ 2 * D ^ 2 * N ^ (3 * (τ' / 16)) ≤ e ^ 2 * D ^ 2 * N ^ (τ' / 2) :=
      mul_le_mul_of_nonneg_left hN316 (by positivity)
    linarith
  have hEb0 : 0 ≤ N ^ (τ' / 2) + e ^ 2 * D ^ 2 * N ^ (3 * (τ' / 16)) +
      N * D ^ 2 * Kh2 * (N ^ (20 : ℝ) + Lk) := by
    have hLk0 : 0 ≤ Lk := by rw [hLk]; positivity
    have := Real.rpow_nonneg hNpos.le (3 * (τ' / 16))
    positivity
  -- the middle term
  have hN16 : 1 ≤ N ^ (τ' / 16) := Real.one_le_rpow hN (by positivity)
  have hNe : 1 ≤ N ^ εg := Real.one_le_rpow hN hεg.le
  have hM : 3 * D ^ 4 * N ^ (τ' / 16 + τ' / 16) * (1 + e * Y) ≤
      3 * D ^ 4 * (1 + 4 * e * c) * N ^ (τ' / 16 + τ' / 16 + τ' / 16) * N ^ εg := by
    rw [hY]
    have h1 : 1 + e * (4 * c * N ^ (τ' / 16) * N ^ εg) ≤
        (1 + 4 * e * c) * (N ^ (τ' / 16) * N ^ εg) := by
      have : 1 ≤ N ^ (τ' / 16) * N ^ εg := one_le_mul_of_one_le_of_one_le hN16 hNe
      linarith
    have h2 : N ^ (τ' / 16 + τ' / 16 + τ' / 16) = N ^ (τ' / 16 + τ' / 16) * N ^ (τ' / 16) :=
      Real.rpow_add hNpos _ _
    rw [h2]
    have h3 : 0 ≤ 3 * D ^ 4 * N ^ (τ' / 16 + τ' / 16) := by
      have := Real.rpow_nonneg hNpos.le (τ' / 16 + τ' / 16); positivity
    calc 3 * D ^ 4 * N ^ (τ' / 16 + τ' / 16) * (1 + e * (4 * c * N ^ (τ' / 16) * N ^ εg))
        ≤ 3 * D ^ 4 * N ^ (τ' / 16 + τ' / 16) * ((1 + 4 * e * c) * (N ^ (τ' / 16) * N ^ εg)) :=
          mul_le_mul_of_nonneg_left h1 h3
      _ = _ := by ring
  -- assembly
  have hA : e ^ 4 * (3 * ((2 + e ^ 2 * D ^ 2) * N ^ (τ' / 2))) * Real.log (e * N) ≤
      N ^ τ' / 3 := by
    have h1 : e ^ 4 * (3 * ((2 + e ^ 2 * D ^ 2) * N ^ (τ' / 2))) * Real.log (e * N) ≤
        e ^ 4 * (3 * ((2 + e ^ 2 * D ^ 2) * N ^ (τ' / 2))) * ((1 + (τ' / 16)⁻¹) * N ^ (τ' / 16)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : N ^ (τ' / 2 + τ' / 16) = N ^ (τ' / 2) * N ^ (τ' / 16) := Real.rpow_add hNpos _ _
    rw [h2] at E3
    linarith
  have hB : e ^ 4 * (3 * D ^ 4 * (1 + 4 * e * c) * N ^ (τ' / 16 + τ' / 16 + τ' / 16) * N ^ εg) *
      Real.log (e * N) ≤ N ^ τ' / 3 * N ^ εg := by
    have h0 : 0 ≤ e ^ 4 * (3 * D ^ 4 * (1 + 4 * e * c) * N ^ (τ' / 16 + τ' / 16 + τ' / 16) *
        N ^ εg) := by
      have := Real.rpow_nonneg hNpos.le (τ' / 16 + τ' / 16 + τ' / 16)
      have := Real.rpow_nonneg hNpos.le εg
      positivity
    have h1 := mul_le_mul_of_nonneg_left hlog h0
    have h2 : N ^ (τ' / 16 + τ' / 16 + τ' / 16 + τ' / 16) =
        N ^ (τ' / 16 + τ' / 16 + τ' / 16) * N ^ (τ' / 16) := Real.rpow_add hNpos _ _
    rw [h2] at E4
    have h3 := mul_le_mul_of_nonneg_right E4 (Real.rpow_nonneg hNpos.le εg)
    linarith
  have hXle : e ^ 4 * (3 * (N ^ (τ' / 2) + e ^ 2 * D ^ 2 * N ^ (3 * (τ' / 16)) +
      N * D ^ 2 * Kh2 * (N ^ (20 : ℝ) + Lk)) +
        3 * D ^ 4 * N ^ (τ' / 16 + τ' / 16) * (1 + e * Y)) * Real.log (e * N) ≤
      e ^ 4 * (3 * ((2 + e ^ 2 * D ^ 2) * N ^ (τ' / 2))) * Real.log (e * N) +
        e ^ 4 * (3 * D ^ 4 * (1 + 4 * e * c) * N ^ (τ' / 16 + τ' / 16 + τ' / 16) * N ^ εg) *
          Real.log (e * N) := by
    have := add_le_add (mul_le_mul_of_nonneg_left hEb (by norm_num : (0 : ℝ) ≤ 3)) hM
    have h2 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ e ^ 4)
    have h3 := mul_le_mul_of_nonneg_right h2 hlog0
    linarith
  have hNτ : 0 ≤ N ^ τ' := Real.rpow_nonneg hNpos.le _
  have hfin : N ^ τ' / 3 + N ^ τ' / 3 * N ^ εg + N ^ τ' / 3 ≤ N ^ τ' * N ^ εg := by
    have := mul_le_mul_of_nonneg_left hNe hNτ
    linarith
  linarith

set_option maxHeartbeats 6400000 in
-- The arithmetic conditions on `N` and the exceptional sets are handled together.
/-- The statement of `flowL3_grid`, proved from `flowL3_drift`, `LF2_mart_core`, `flowGood_grid`,
`flowL2_grid`, `lemma_G_large_two` and the linear recursion `LF2_lin`. -/
private lemma LF2_grid_core (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∀ Cg : ℝ, 32 + D' ≤ Cg → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ K : ℕ, (N : ℝ) ^ Cg ≤ K → (K : ℝ) ≤ (N : ℝ) ^ (Cg + 1) →
      ∀ z₁ z₂ z₃ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (z₃ = z ∨ z₃ = star z) →
        gridLawA D N K μ₀ {ω |
          (∀ w₁ w₂ : ℂ, (w₁ = z ∨ w₁ = star z) → (w₂ = z ∨ w₂ = star z) →
            N * flowTc (lam D N A) z ^ 2 * (mExt (lam D N A) z).im ^ 2 *
              hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0) w₁ w₂ -
                KTheta (lam D N A) θ w₁ w₂) ≤ (N : ℝ) ^ (2 * εg)) ∧
            ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ' *
              ((flowTc (lam D N A) z / (flowTc (lam D N A) z - k * (S / K))) ^ 3 *
                  ten3Norm (Lten3 (lam D N A) (gridStateA D N K (S / K) ω 0) z₁ z₂ z₃ -
                    KTheta3 (lam D N A) θ z₁ z₂ z₃) +
                (N : ℝ) ^ εg / (N * (flowTc (lam D N A) z - k * (S / K)) ^ 3 *
                  flowIm (lam D N A) z (k * (S / K)) ^ 3)) <
              ten3Norm (flowLten3 (lam D N A) z₁ z₂ z₃ (k * (S / K))
                  (gridStateA D N K (S / K) ω k) -
                flowKten3 (lam D N A) θ z₁ z₂ z₃ (k * (S / K)))} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD' Cg hCg
  set τq := τ' / 16 with hτq
  have hτq0 : 0 < τq := by rw [hτq]; positivity
  obtain ⟨Nd, hNd⟩ := flowL3_drift D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc τq hτq0
  obtain ⟨Nm, hNm⟩ := LF2_mart_core D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    (τ' / 2) (by positivity) (D' + 1) (by linarith) Cg (by linarith)
  obtain ⟨Ng, hNg⟩ := flowGood_grid D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    τq hτq0 (D' + 1) (by linarith) Cg (by linarith)
  obtain ⟨Nl, hNl⟩ := flowL2_grid D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    τq hτq0 (D' + 1) (by linarith) Cg (by linarith)
  obtain ⟨Ns, hNs⟩ := lemma_G_large_two D hD δA τ εg c hδA hτ hεg hεg₂ hc C τq hτq0 (D' + 1)
    (by linarith)
  set e := Real.exp 1 with he
  have hev : ∀ᶠ N : ℕ in Filter.atTop, Nd ≤ N ∧ Nm ≤ N ∧ Ng ≤ N ∧ Nl ≤ N ∧ Ns ≤ N ∧ 10 ≤ N ∧
      2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧ c * (N : ℝ) ^ (-εg) ≤ 1 ∧
      c * (1 + (εg / 2)⁻¹) * (N : ℝ) ^ (-(εg / 2)) ≤ (N : ℝ) ^ (0 : ℝ) ∧
      e ^ 2 * (N : ℝ) ^ (0 : ℝ) ≤ (N : ℝ) ^ τ' ∧
      D ^ 2 * (1 + 608 * D ^ 6 * e ^ 7) * (N : ℝ) ^ (-(11 : ℝ)) ≤ (N : ℝ) ^ (0 : ℝ) ∧
      (3 * (3 * e ^ 4 * (2 + e ^ 2 * D ^ 2) * (1 + τq⁻¹))) * (N : ℝ) ^ (τ' / 2 + τq) ≤
        (N : ℝ) ^ τ' ∧
      (3 * (3 * e ^ 4 * D ^ 4 * (1 + 4 * e * c) * (1 + τq⁻¹))) * (N : ℝ) ^ (τq + τq + τq + τq) ≤
        (N : ℝ) ^ τ' ∧
      (3 * (2 + e ^ 2 * D ^ 2)) * (N : ℝ) ^ (τ' / 2) ≤ (N : ℝ) ^ τ' := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    refine (Filter.eventually_ge_atTop Nd).and ((Filter.eventually_ge_atTop Nm).and
      ((Filter.eventually_ge_atTop Ng).and ((Filter.eventually_ge_atTop Nl).and
      ((Filter.eventually_ge_atTop Ns).and ((Filter.eventually_ge_atTop 10).and
      (((t1.const_mul 2).eventually (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and
      (((t2.const_mul c).eventually (Iic_mem_nhds (by simp : c * 0 < 1))).and
      ((LF2_ev_pow _ _ _ (by linarith)).and ((LF2_ev_pow _ _ _ (by linarith)).and
      ((LF2_ev_pow _ _ _ (by norm_num)).and ((LF2_ev_pow _ _ _ (by linarith)).and
      ((LF2_ev_pow _ _ _ (by linarith)).and
      (LF2_ev_pow _ _ _ (by linarith))))))))))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ₀ hμ₀ A z S hadm K hK1 hK2 z₁ z₂ z₃ h₁ h₂ h₃ => ?_⟩
  obtain ⟨hNd', hNm', hNg', hNl', hNs', hN10, hAN, hcN, hE3, hE1, hE2, hE3a, hE4a, hE5a⟩ := hN₀ N hN
  haveI := hμ₀.prob
  haveI : NeZero D := ⟨by omega⟩
  haveI : NeZero N := ⟨by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have h0 : (N : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero _
  rw [h0] at hE3 hE2
  rw [h0, mul_one] at hE1
  have hadm' := hadm
  obtain ⟨hΛ10, hzτ, hz, hm1, hq0, hq1, hS0, hSt, hη⟩ :=
    LF2_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  have hK1' : 1 ≤ K := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ Cg := Real.one_le_rpow hNr (by linarith)
    exact_mod_cast this.trans hK1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1'
  have hNτ : 1 ≤ (N : ℝ) ^ τ' := Real.one_le_rpow hNr hτ'.le
  set q₀ := flowTc (lam D N A) z with hq₀
  set wz : Bool → ℂ := fun b => if b then star z else z with hwz
  have hwz1 : ∀ b, wz b = z ∨ wz b = star z := by
    intro b; cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hwz2 : ∀ w : ℂ, (w = z ∨ w = star z) → ∃ b, w = wz b := by
    rintro w (rfl | rfl)
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  -- the degenerate horizon
  rcases hS0.eq_or_lt with hS | hSpos
  · subst hS
    have hst : ∀ (ω : GridΩA D N K) (j : ℕ), gridStateA D N K (0 / K) ω j = ω.1 := by
      intro ω j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [show ((0 : ℝ) / K) = 0 from zero_div _] at ih ⊢
        simp [gridStateA, ih]
    refine le_trans (measure_mono (t := ∅) ?_) (by rw [measure_empty]; exact bot_le)
    rintro ω ⟨-, k, -, hlt⟩
    exfalso
    obtain ⟨z0L, z0K⟩ := LF2_zero3 (lam D N A) θ z₁ z₂ z₃ ω.1
    rw [hst, hst] at hlt
    simp only [zero_div, mul_zero, sub_zero, z0L, z0K] at hlt
    have hι : 0 < flowIm (lam D N A) z 0 := by
      obtain ⟨-, hιeq, hι, -⟩ := LF2_flow D N hD1 hN1 A hΛ10 z hz 0 hSt 0 le_rfl le_rfl
      rw [hιeq]; positivity
    have hX := Real.sqrt_nonneg (∑ a, ∑ b, ∑ c, ‖(Lten3 (lam D N A) ω.1 z₁ z₂ z₃ -
      KTheta3 (lam D N A) θ z₁ z₂ z₃) a b c‖ ^ 2)
    have hq : q₀ / q₀ = 1 := div_self hq0.ne'
    rw [hq, one_pow, one_mul] at hlt
    have hp : 0 < (N : ℝ) ^ εg / (N * q₀ ^ 3 * flowIm (lam D N A) z 0 ^ 3) := by positivity
    unfold ten3Norm at hlt
    nlinarith
  -- the grid with `S > 0`
  have hS1 : S ≤ 1 := by linarith
  have hSK : S / K ≤ 1 / K := div_le_div_of_nonneg_right hS1 hKpos.le
  have hKinv : 1 / (K : ℝ) ≤ (N : ℝ) ^ (-Cg) := by
    rw [Real.rpow_neg hNpos.le, one_div]
    exact inv_anti₀ (Real.rpow_pos_of_pos hNpos _) hK1
  have hN31 : (N : ℝ) ^ (-Cg) ≤ (N : ℝ) ^ (-(31 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hh31 : S / K ≤ (N : ℝ) ^ (-(31 : ℝ)) := hSK.trans (hKinv.trans hN31)
  have hhpos : 0 < S / K := div_pos hSpos hKpos
  have hKh : (K : ℝ) * (S / K) = S := by field_simp
  have hKh2 : (K : ℝ) * (S / K) ^ 2 ≤ (N : ℝ) ^ (-(32 : ℝ)) := by
    have : (K : ℝ) * (S / K) ^ 2 = S * (S / K) := by field_simp
    rw [this]
    have hN32 : (N : ℝ) ^ (-Cg) ≤ (N : ℝ) ^ (-(32 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    calc S * (S / K) ≤ 1 * (S / K) := mul_le_mul_of_nonneg_right hS1 hhpos.le
      _ ≤ _ := by rw [one_mul]; exact hSK.trans (hKinv.trans hN32)
  -- `q₀ ≤ c N^{-ε_g}`, `q₀⁻¹ ≤ 2 c N^{ε_g}` and `q₀ - S ≥ (eN)⁻¹`
  have hι0 := (LF2_flow D N hD1 hN1 A hΛ10 z hz S hSt 0 le_rfl hSpos.le).2.2.1
  have hx0 : 0 < z.im / (mExt (lam D N A) z).im := div_pos hz hι0
  have hq0c : q₀ ≤ c * (N : ℝ) ^ (-εg) := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + z.im / (mExt (lam D N A) z).im by
      linarith)
    have h2 := hadm.2.2.2.2.2.1
    change Real.log (1 + z.im / (mExt (lam D N A) z).im) ≤ _
    linarith
  have hq0inv : q₀⁻¹ ≤ 2 * c * (N : ℝ) ^ εg := by
    have hlo := hadm.2.2.2.2.1
    have hx1 : z.im / (mExt (lam D N A) z).im ≤ 1 := hadm.2.2.2.2.2.1.trans hcN
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + z.im / (mExt (lam D N A) z).im by
      linarith)
    have h2 : z.im / (mExt (lam D N A) z).im / 2 ≤ q₀ := by
      change _ ≤ Real.log (1 + z.im / (mExt (lam D N A) z).im)
      refine le_trans ?_ h1
      rw [show 1 - (1 + z.im / (mExt (lam D N A) z).im)⁻¹ = z.im / (mExt (lam D N A) z).im /
        (1 + z.im / (mExt (lam D N A) z).im) by field_simp; ring]
      exact div_le_div_of_nonneg_left hx0.le (by positivity) (by linarith)
    have hcpos : 0 < c := by linarith
    have hNεpos : 0 < (N : ℝ) ^ εg := Real.rpow_pos_of_pos hNpos _
    have h3 : c⁻¹ * (N : ℝ) ^ (-εg) / 2 ≤ q₀ := le_trans (by linarith) h2
    have hpos : 0 < c⁻¹ * (N : ℝ) ^ (-εg) / 2 := by
      have := inv_pos.2 hcpos; have := Real.rpow_pos_of_pos hNpos (-εg); positivity
    calc q₀⁻¹ ≤ (c⁻¹ * (N : ℝ) ^ (-εg) / 2)⁻¹ := inv_anti₀ hpos h3
      _ = 2 * c * (N : ℝ) ^ εg := by
          rw [Real.rpow_neg hNpos.le]
          have := hcpos.ne'; have := hNεpos.ne'
          field_simp
  have hqK : (e * N)⁻¹ ≤ q₀ - S := by
    obtain ⟨-, hιeq, hι0', hιS1, -, -, -⟩ :=
      LF2_flow D N hD1 hN1 A hΛ10 z hz S hSt S hSpos.le le_rfl
    have hup := LF2_flow_up D N hD1 hN1 A hΛ10 z hz S hSt hq1 S hSpos.le le_rfl
    have hιS : 0 < flowIm (lam D N A) z S := by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0'
    have h1 := (hη S hSpos.le le_rfl).1
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have : (1 : ℝ) < N * (charFlowZ (lam D N A) z S).im := by
      rw [inv_lt_iff_one_lt_mul₀ hNpos] at h1; linarith
    nlinarith
  have hqS : 0 < q₀ - S := by linarith
  have hrat1 : 1 ≤ q₀ / (q₀ - S) := by rw [le_div_iff₀ hqS]; linarith
  have hrat : q₀ / (q₀ - S) ≤ e * N := by
    rw [div_le_iff₀ hqS]
    have := mul_le_mul_of_nonneg_left hqK (by positivity : (0 : ℝ) ≤ e * N)
    rw [mul_inv_cancel₀ (by positivity)] at this
    nlinarith
  have heN : 1 ≤ e * N := by have := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num); nlinarith
  have hγ : (q₀ / (q₀ - S)) ^ q₀ ≤ e := by
    calc (q₀ / (q₀ - S)) ^ q₀ ≤ (e * N) ^ q₀ :=
          Real.rpow_le_rpow (by positivity) hrat hq0.le
      _ ≤ (e * N) ^ (c * (N : ℝ) ^ (-εg)) := Real.rpow_le_rpow_of_exponent_le heN hq0c
      _ ≤ e := by
          rw [Real.rpow_def_of_pos (by positivity), he]
          apply Real.exp_le_exp.2
          have hl := LF2_log_le N (εg / 2) hNr (by positivity)
          have hpow : (N : ℝ) ^ (εg / 2) * (N : ℝ) ^ (-εg) = (N : ℝ) ^ (-(εg / 2)) := by
            rw [← Real.rpow_add hNpos]; ring_nf
          have hcN0 : 0 ≤ c * (N : ℝ) ^ (-εg) := by
            have := Real.rpow_nonneg hNpos.le (-εg); positivity
          calc Real.log (Real.exp 1 * N) * (c * (N : ℝ) ^ (-εg))
              ≤ (1 + (εg / 2)⁻¹) * (N : ℝ) ^ (εg / 2) * (c * (N : ℝ) ^ (-εg)) :=
                mul_le_mul_of_nonneg_right hl hcN0
            _ = c * (1 + (εg / 2)⁻¹) * ((N : ℝ) ^ (εg / 2) * (N : ℝ) ^ (-εg)) := by ring
            _ = c * (1 + (εg / 2)⁻¹) * (N : ℝ) ^ (-(εg / 2)) := by rw [hpow]
            _ ≤ 1 := hE3
  have hlog : Real.log (q₀ / (q₀ - S)) ≤ Real.log (e * N) :=
    Real.log_le_log (by positivity) hrat
  -- the start bound from `lemma_G_large_two`
  set Y := 4 * c * (N : ℝ) ^ τq * (N : ℝ) ^ εg with hY
  have hYstart : ∀ w₁ w₂ : ℂ, (w₁ = z ∨ w₁ = star z) → (w₂ = z ∨ w₂ = star z) →
      ∀ H₀ : Idx D N → Idx D N → ℂ, hsNorm (Lmat (lam D N A) H₀ w₁ w₂ -
        KTheta (lam D N A) θ w₁ w₂) ≤ (N : ℝ) ^ τq * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
          opNorm (1 - Mhat (lam D N A) w₁ w₂ * PTheta D θ)⁻¹) →
      q₀ ^ 2 * hsNorm (Lmat (lam D N A) H₀ w₁ w₂ - KTheta (lam D N A) θ w₁ w₂) ≤
        Y / (N * (mExt (lam D N A) z).im ^ 2) := by
    intro w₁ w₂ hw₁ hw₂ H₀ hle
    set ι₀ := (mExt (lam D N A) z).im with hι₀d
    have hU := (LF2_flowU D N A hΛ10 z hz S hSt θ hθ0 hθ1 w₁ w₂ hw₁ hw₂ 0 le_rfl hSpos.le).2.2
    have hU0 : LF2_U (Mhat (lam D N A) w₁ w₂) θ 0 =
        (1 - Mhat (lam D N A) w₁ w₂ * PTheta D θ)⁻¹ := by
      simp [LF2_U]
    rw [hU0, sub_zero] at hU
    obtain ⟨-, hιeq0, -, -, -, -, hqι⟩ :=
      LF2_flow D N hD1 hN1 A hΛ10 z hz S hSt 0 le_rfl hSpos.le
    have hcz : charFlowZ (lam D N A) z 0 = z := by simp [charFlowZ]
    rw [hcz, hιeq0, sub_zero, zero_div, Real.exp_zero, one_mul] at hqι
    have hq0inv1 : 1 ≤ q₀⁻¹ := one_le_inv₀ hq0 |>.2 hq1
    have hX0 : 0 ≤ hsNorm (Lmat (lam D N A) H₀ w₁ w₂ - KTheta (lam D N A) θ w₁ w₂) :=
      Real.sqrt_nonneg _
    have hzim : 0 < z.im := hz
    have hNt : 0 < (N : ℝ) ^ τq := Real.rpow_pos_of_pos hNpos _
    calc q₀ ^ 2 * hsNorm (Lmat (lam D N A) H₀ w₁ w₂ - KTheta (lam D N A) θ w₁ w₂)
        ≤ q₀ ^ 2 * ((N : ℝ) ^ τq * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
          opNorm (1 - Mhat (lam D N A) w₁ w₂ * PTheta D θ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      _ ≤ q₀ ^ 2 * ((N : ℝ) ^ τq * ((N : ℝ)⁻¹ * ((q₀ * ι₀) ^ 2)⁻¹ * (1 + q₀⁻¹))) := by
          have hR0 := LF2_op_nonneg (1 - Mhat (lam D N A) w₁ w₂ * PTheta D θ)⁻¹
          have hinv : (z.im ^ 2)⁻¹ ≤ ((q₀ * ι₀) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hqι 2)
          gcongr
      _ = (N : ℝ) ^ τq * (1 + q₀⁻¹) / (N * ι₀ ^ 2) := by
          field_simp
      _ ≤ (N : ℝ) ^ τq * (2 * (2 * c * (N : ℝ) ^ εg)) / (N * ι₀ ^ 2) := by
          gcongr
          linarith
      _ = Y / (N * ι₀ ^ 2) := by rw [hY]; ring
  -- the exceptional sets
  set NH := {ω : GridΩA D N K | ¬ (Matrix.of ω.1).IsHermitian} with hNH
  have hNH0 : gridLawA D N K μ₀ NH = 0 := by
    have hT : MeasurableSet {H : Idx D N → Idx D N → ℂ | ¬ (Matrix.of H).IsHermitian} :=
      LF2_herm_meas.compl
    have e1 : NH = Prod.fst ⁻¹' {H : Idx D N → Idx D N → ℂ | ¬ (Matrix.of H).IsHermitian} := rfl
    rw [e1, ← Measure.map_apply measurable_fst hT]
    unfold gridLawA
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_iff.1 hμ₀.herm
  set Bg := {ω : GridΩA D N K | ∃ k : ℕ, k ≤ K ∧
    ¬ flowGoodAt A z τq (k * (S / K)) (gridStateA D N K (S / K) ω k)} with hBg
  set Bm := {ω : GridΩA D N K | ∃ n : ℕ, n ≤ K ∧
    (∀ j : ℕ, j < n →
      flowGoodAt A z (τ' / 2 / 8) (j * (S / K)) (gridStateA D N K (S / K) ω j)) ∧
    (N : ℝ) ^ (τ' / 2) / (N * (q₀ - n * (S / K)) ^ (3 / 2 : ℝ) *
        flowIm (lam D N A) z (n * (S / K)) ^ 3) <
      ten3Norm (fun x y w => ∑ j ∈ Finset.range n,
        (((q₀ - (j + 1) * (S / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          (flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) x y w -
            ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y w
              ∂(gueBlocks D N)))} with hBm
  set Bl : Bool × Bool → Set (GridΩA D N K) := fun p => {ω |
    N * q₀ ^ 2 * (mExt (lam D N A) z).im ^ 2 *
        hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0) (wz p.1) (wz p.2) -
          KTheta (lam D N A) θ (wz p.1) (wz p.2)) ≤ (N : ℝ) ^ (2 * εg) ∧
      ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τq *
        ((q₀ / (q₀ - k * (S / K))) ^ 2 *
            hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0) (wz p.1) (wz p.2) -
              KTheta (lam D N A) θ (wz p.1) (wz p.2)) +
          1 / (N * (q₀ - k * (S / K)) ^ 2 * flowIm (lam D N A) z (k * (S / K)) ^ 2)) <
        hsNorm (flowLmat (lam D N A) (wz p.1) (wz p.2) (k * (S / K))
            (gridStateA D N K (S / K) ω k) -
          flowKmat (lam D N A) θ (wz p.1) (wz p.2) (k * (S / K)))} with hBl
  set Bs : Bool × Bool → Set (GridΩA D N K) := fun p => Prod.fst ⁻¹' {H |
    (N : ℝ) ^ τq * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
        opNorm (1 - Mhat (lam D N A) (wz p.1) (wz p.2) * PTheta D θ)⁻¹) <
      hsNorm (Lmat (lam D N A) H (wz p.1) (wz p.2) - KTheta (lam D N A) θ (wz p.1) (wz p.2))}
    with hBs
  have hτ16 : τ' / 2 / 8 = τq := by rw [hτq]; ring
  refine (measure_mono (t := (((Bg ∪ Bm) ∪ ⋃ p, Bl p) ∪ ⋃ p, Bs p) ∪ NH) ?_).trans ?_
  · rintro ω ⟨hinit, k, hk, hlt⟩
    by_contra hω
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, hNH, Set.mem_ofPred_eq,
      not_not] at hω
    obtain ⟨⟨⟨⟨hωg, hωm⟩, hωl⟩, hωs⟩, hherm⟩ := hω
    have hgood : ∀ j, j ≤ K → flowGoodAt A z τq (j * (S / K)) (gridStateA D N K (S / K) ω j) := by
      intro j hj
      by_contra hc'
      exact hωg (by rw [hBg]; exact ⟨j, hj, hc'⟩)
    have hfl : ∀ j, j ≤ K → 0 < (charFlowZ (lam D N A) z (j * (S / K))).im ∧
        0 < flowIm (lam D N A) z (j * (S / K)) := by
      intro j hj
      have h0 : 0 ≤ (j : ℝ) * (S / K) := by positivity
      have hjS : (j : ℝ) * (S / K) ≤ S :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hhpos.le).trans_eq hKh
      obtain ⟨hηj, hιeq, hι0', -⟩ := LF2_flow D N hD1 hN1 A hΛ10 z hz S hSt _ h0 hjS
      exact ⟨hηj, by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0'⟩
    have hdrift : ∀ j, j < K → ∀ x y w : Fin D,
        ‖(∫ X, (((flowTc (lam D N A) z - (j * (S / K) + S / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
              flowLten3 (lam D N A) z₁ z₂ z₃ (j * (S / K) + S / K)
                (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                  Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y w
              ∂(gueBlocks D N)) -
            (((flowTc (lam D N A) z - j * (S / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
              flowLten3 (lam D N A) z₁ z₂ z₃ (j * (S / K)) (gridStateA D N K (S / K) ω j) x y w -
            ((S / K : ℝ) : ℂ) * (((flowTc (lam D N A) z - j * (S / K)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
              ((3 / 2 : ℂ) * ((flowTc (lam D N A) z - j * (S / K) - 1 : ℝ) : ℂ) *
                  flowLten3 (lam D N A) z₁ z₂ z₃ (j * (S / K))
                    (gridStateA D N K (S / K) ω j) x y w +
                ((flowTc (lam D N A) z - j * (S / K) : ℝ) : ℂ) * ∑ a,
                  (flowLmat (lam D N A) z₁ z₂ (j * (S / K)) (gridStateA D N K (S / K) ω j) x a *
                      flowLten3 (lam D N A) z₁ z₂ z₃ (j * (S / K))
                        (gridStateA D N K (S / K) ω j) a y w +
                    flowLmat (lam D N A) z₂ z₃ (j * (S / K)) (gridStateA D N K (S / K) ω j) y a *
                      flowLten3 (lam D N A) z₁ z₂ z₃ (j * (S / K))
                        (gridStateA D N K (S / K) ω j) x a w +
                    flowLmat (lam D N A) z₃ z₁ (j * (S / K)) (gridStateA D N K (S / K) ω j) w a *
                      flowLten3 (lam D N A) z₁ z₂ z₃ (j * (S / K))
                        (gridStateA D N K (S / K) ω j) x y a))‖ ≤
          S / K * ((N : ℝ) ^ (3 * τq) / (N * (flowTc (lam D N A) z - j * (S / K)) ^ (5 / 2 : ℝ) *
            flowIm (lam D N A) z (j * (S / K)) ^ 3)) + (S / K) ^ 2 * (N : ℝ) ^ (20 : ℝ) := by
      intro j hj x y w
      have hsh : (j : ℝ) * (S / K) + S / K ≤ S := by
        have : ((j + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hj
        have := (mul_le_mul_of_nonneg_right this hhpos.le).trans_eq hKh
        push_cast at this; linarith
      exact hNd N hNd' A z S hadm' (j * (S / K)) (S / K) (by positivity) hhpos hsh hh31 _
        (LF2_states_herm D N K (S / K) ω hherm j) (hgood j hj.le) z₁ z₂ z₃ h₁ h₂ h₃ x y w
    have hmart : ∀ n, n ≤ K → ten3Norm (fun x y w => ∑ j ∈ Finset.range n,
        (((flowTc (lam D N A) z - (j + 1) * (S / K)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          (flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) x y w -
            ∫ X, flowLten3 (lam D N A) z₁ z₂ z₃ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y w
              ∂(gueBlocks D N))) ≤
        (N : ℝ) ^ (τ' / 2) / (N * (flowTc (lam D N A) z - n * (S / K)) ^ (3 / 2 : ℝ) *
          flowIm (lam D N A) z (n * (S / K)) ^ 3) := by
      intro n hn
      by_contra hc'
      push Not at hc'
      exact hωm (by
        rw [hBm]; exact ⟨n, hn, fun j hj => by rw [hτ16]; exact hgood j (by omega), hc'⟩)
    have hL2 : ∀ w₁ w₂ : ℂ, (w₁ = z ∨ w₁ = star z) → (w₂ = z ∨ w₂ = star z) → ∀ k, k ≤ K →
        hsNorm (flowLmat (lam D N A) w₁ w₂ (k * (S / K)) (gridStateA D N K (S / K) ω k) -
            flowKmat (lam D N A) θ w₁ w₂ (k * (S / K))) ≤
          (N : ℝ) ^ τq * ((flowTc (lam D N A) z / (flowTc (lam D N A) z - k * (S / K))) ^ 2 *
              hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0) w₁ w₂ -
                KTheta (lam D N A) θ w₁ w₂) +
            1 / (N * (flowTc (lam D N A) z - k * (S / K)) ^ 2 *
              flowIm (lam D N A) z (k * (S / K)) ^ 2)) := by
      intro w₁ w₂ hw₁ hw₂ k' hk'
      obtain ⟨b₁, rfl⟩ := hwz2 w₁ hw₁
      obtain ⟨b₂, rfl⟩ := hwz2 w₂ hw₂
      by_contra hc'
      push Not at hc'
      exact hωl (b₁, b₂) (by rw [hBl]; exact ⟨hinit _ _ hw₁ hw₂, k', hk', hc'⟩)
    have hYω : ∀ w₁ w₂ : ℂ, (w₁ = z ∨ w₁ = star z) → (w₂ = z ∨ w₂ = star z) →
        flowTc (lam D N A) z ^ 2 * hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0)
          w₁ w₂ - KTheta (lam D N A) θ w₁ w₂) ≤ Y / (N * (mExt (lam D N A) z).im ^ 2) := by
      intro w₁ w₂ hw₁ hw₂
      obtain ⟨b₁, rfl⟩ := hwz2 w₁ hw₁
      obtain ⟨b₂, rfl⟩ := hwz2 w₂ hw₂
      refine hYstart _ _ hw₁ hw₂ _ ?_
      by_contra hc'
      push Not at hc'
      exact hωs (b₁, b₂) (by rw [hBs]; exact hc')
    refine absurd hlt (not_lt.2 (LF2_lin D N K hK1' A z S hΛ10 hz hSpos hSt hq1
      (fun s hs0 hsS => (hη s hs0 hsS).1) θ hθ0 hθ1 z₁ z₂ z₃ h₁ h₂ h₃
      (fun j => gridStateA D N K (S / K) ω j) (3 * τq) (τ' / 2) τq τq Y τ' εg
      (fun k hk => ⟨LF2_states_herm D N K (S / K) ω hherm k, hgood k hk.le⟩) hdrift
      hmart hL2 hYω (by
        rw [hY]
        have := Real.rpow_nonneg hNpos.le τq; have := Real.rpow_nonneg hNpos.le εg
        have : (0 : ℝ) ≤ c := by linarith
        positivity) hγ hlog (by linarith) ?_ k hk))
    · -- the arithmetic
      have hρ : (flowTc (lam D N A) z - S)⁻¹ ≤ e * N := by
        rw [inv_le_comm₀ hqS (by positivity)]; exact hqK
      have hl := LF2_log_le N τq hNr hτq0
      have hKh2' : 0 ≤ (K : ℝ) * (S / K) ^ 2 := by positivity
      have h3 := LF2_ar_fin2 N D c τ' εg (K * (S / K) ^ 2) (flowTc (lam D N A) z - S)⁻¹ Y hNr hDr hc
        hτ' hεg hKh2' hKh2 (inv_pos.2 hqS) hρ hY (by rw [← hτq]; exact hl) hE2
        (by rw [← hτq]; linarith) (by rw [← hτq]; linarith) (by linarith)
      rw [← hτq] at h3
      exact h3
  · -- the probability budget
    have hBg' := hNg N hNg' θ hθ0 hθ1 μ₀ hμ₀ A z S hadm' K hK1' hK2
    have hBm' := hNm N hNm' θ hθ0 hθ1 μ₀ hμ₀ A z S hadm' K hK1 hK2 z₁ z₂ z₃ h₁ h₂ h₃
    have hBl' : ∀ p, gridLawA D N K μ₀ (Bl p) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) :=
      fun p => hNl N hNl' θ hθ0 hθ1 μ₀ hμ₀ A z S hadm' K hK1 hK2 (wz p.1) (wz p.2) (hwz1 _)
        (hwz1 _)
    have hBs' : ∀ p, gridLawA D N K μ₀ (Bs p) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := by
      intro p
      have hη13 : c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im := by
        refine le_trans ?_ hadm.2.2.2.1
        have : (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 3 : ℝ) + τe) :=
          Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
        have hc0 : 0 ≤ c⁻¹ := inv_nonneg.2 (by linarith)
        exact mul_le_mul_of_nonneg_left this hc0
      have h := (hNs N hNs' θ hθ0 hθ1 μ₀ hμ₀ A hadm.1 z hadm.2.1 hz hη13 hadm.2.2.2.2.1
        hadm.2.2.2.2.2.1 (wz p.1) (wz p.2) (hwz1 _) (hwz1 _)).2
      refine le_trans ?_ h
      refine le_trans (Measure.le_map_apply measurable_fst.aemeasurable _) (le_of_eq ?_)
      unfold gridLawA
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    refine (measure_union_le _ _).trans ?_
    rw [hNH0, add_zero]
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add hBg' hBm')) ((measure_iUnion_fintype_le _ _).trans
        (Finset.sum_le_sum fun p _ => hBl' p)))) ((measure_iUnion_fintype_le _ _).trans
        (Finset.sum_le_sum fun p _ => hBs' p))).trans ?_
    have hpos : 0 ≤ (N : ℝ) ^ (-(D' + 1)) := Real.rpow_nonneg hNpos.le _
    have h4 : ∑ _p : Bool × Bool, ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) =
        ENNReal.ofReal (4 * (N : ℝ) ^ (-(D' + 1))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul,
        ENNReal.ofReal_mul (by norm_num)]
      congr 1
      norm_num
    rw [h4, ← ENNReal.ofReal_add hpos hpos, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : (N : ℝ) ^ (-(D' + 1)) = (N : ℝ) ^ (-D') * (N : ℝ)⁻¹ := by
      rw [show -(D' + 1) = -D' + -1 by ring, Real.rpow_add hNpos, Real.rpow_neg_one]
    rw [e1]
    have hNinv : (N : ℝ)⁻¹ ≤ 1 / 10 := by
      rw [inv_le_comm₀ hNpos (by norm_num)]; norm_num
      exact_mod_cast hN10
    have := Real.rpow_nonneg hNpos.le (-D')
    nlinarith

/-- Lemma 3.9 [lem_flow_2], (3.28) [flow_3G_res], on the grid, conditional form: on the grid of
`flowL2_grid`, the event that the start satisfies `N q₀² (Im m)² ‖L_{(i,j),0} - K_θ‖₂ ≤ N^{2ε_g}`
for all `z_i, z_j ∈ {z, z̄}` and (3.28) fails at some grid time,
`‖L_{(1,2,3),k} - K_k‖₂ > N^{τ'} ((q₀/q_k)³ ‖L_{(1,2,3),0} - K_θ‖₂ + N^{ε_g}/(N q_k³ (Im m_k)³))`,
has probability at most `N^{-D'}`. -/
theorem flowL3_grid (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∀ Cg : ℝ, 32 + D' ≤ Cg → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ K : ℕ, (N : ℝ) ^ Cg ≤ K → (K : ℝ) ≤ (N : ℝ) ^ (Cg + 1) →
      ∀ z₁ z₂ z₃ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (z₃ = z ∨ z₃ = star z) →
        gridLawA D N K μ₀ {ω |
          (∀ w₁ w₂ : ℂ, (w₁ = z ∨ w₁ = star z) → (w₂ = z ∨ w₂ = star z) →
            N * flowTc (lam D N A) z ^ 2 * (mExt (lam D N A) z).im ^ 2 *
              hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0) w₁ w₂ -
                KTheta (lam D N A) θ w₁ w₂) ≤ (N : ℝ) ^ (2 * εg)) ∧
            ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ' *
              ((flowTc (lam D N A) z / (flowTc (lam D N A) z - k * (S / K))) ^ 3 *
                  ten3Norm (Lten3 (lam D N A) (gridStateA D N K (S / K) ω 0) z₁ z₂ z₃ -
                    KTheta3 (lam D N A) θ z₁ z₂ z₃) +
                (N : ℝ) ^ εg / (N * (flowTc (lam D N A) z - k * (S / K)) ^ 3 *
                  flowIm (lam D N A) z (k * (S / K)) ^ 3)) <
              ten3Norm (flowLten3 (lam D N A) z₁ z₂ z₃ (k * (S / K))
                  (gridStateA D N K (S / K) ω k) -
                flowKten3 (lam D N A) θ z₁ z₂ z₃ (k * (S / K)))} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  exact LF2_grid_core D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C

end RBMTransitionEdge

end

