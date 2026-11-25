module

public import RBMTransitionEdge.Flow.Duhamel
public import RBMTransitionEdge.Flow.Generator
public import RBMTransitionEdge.Flow.GridGood

@[expose] public section

/-!
# Lemma 3.8 on the grid: the two-resolvent loop along the flow

`L_{(1,2),s}` and `K_{θ_s}` along the flow, the drift of (3.53) [ItowtL]–(3.54) [mainwtL] in one
grid step on the good event, the martingale part (3.59) [CIest], and (3.26) [flow_1_result] on one
grid, in a conditional form: the bound holds on the event that the initial loop is already close
to `K_θ`; the paper form (3.27) [flow_1_result_2] is a separate statement.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `L_{(1,2),s}` along the flow at the state `H`: `Lmat` at `Λ_s = e^{-s/2} Λ`, `z_{1,s}`,
`z_{2,s}`. -/
def flowLmat {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (s : ℝ)
    (H : Idx D N → Idx D N → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  Lmat (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) H (charFlowZ Λ z₁ s) (charFlowZ Λ z₂ s)

/-- `K_{θ_s}(z_{1,s}, z_{2,s})` along the flow, with the class parameter
`θ_s = e^{-s} θ + 1 - e^{-s}` of the block-OU law. -/
def flowKmat {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ) (s : ℝ) :
    Matrix (Fin D) (Fin D) ℂ :=
  KTheta (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (Real.exp (-s) * θ + 1 - Real.exp (-s))
    (charFlowZ Λ z₁ s) (charFlowZ Λ z₂ s)


/-! ### Operator-norm tools -/

section LF1_Op

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `opNorm` is the `L²` operator norm. -/
private lemma LF1_op_eq (A : Matrix ι ι ℂ) : opNorm A = ‖A‖ := rfl

/-- `‖AB‖ ≤ ‖A‖ ‖B‖`. -/
private lemma LF1_op_mul (A B : Matrix ι ι ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  simpa only [LF1_op_eq] using norm_mul_le A B

/-- `‖A‖ ≥ 0`. -/
private lemma LF1_op_nonneg (A : Matrix ι ι ℂ) : 0 ≤ opNorm A := norm_nonneg _

/-- `‖A^*‖ = ‖A‖`. -/
private lemma LF1_op_conj (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  simpa only [LF1_op_eq] using Matrix.l2_opNorm_conjTranspose A

/-- An entry is bounded by the operator norm. -/
private lemma LF1_entry_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ opNorm A := by
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
private lemma LF1_ntr_le [Nonempty ι] (A : Matrix ι ι ℂ) : ‖ntr A‖ ≤ opNorm A := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, opNorm A := Finset.sum_le_sum fun i _ => LF1_entry_le A i i
    _ = _ := by simp

/-- `⟨A^*⟩ = conj ⟨A⟩`. -/
private lemma LF1_ntr_conj (A : Matrix ι ι ℂ) : ntr Aᴴ = star (ntr A) := by
  simp [ntr, Matrix.trace_conjTranspose, star_mul']

/-- `⟨AB⟩ = ⟨BA⟩`. -/
private lemma LF1_ntr_comm (A B : Matrix ι ι ℂ) : ntr (A * B) = ntr (B * A) := by
  simp only [ntr, Matrix.trace_mul_comm A B]

end LF1_Op

/-- `‖E_a‖ ≤ 1` for the block projection. -/
private lemma LF1_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- `E_a^* = E_a`. -/
private lemma LF1_Ea_conj (D N : ℕ) (a : Fin D) : (Ea D N a)ᴴ = Ea D N a := by
  unfold Ea
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  simp only [Pi.star_apply]
  split_ifs <;> simp

/-- The Hermitian part of a Hermitian array is the array. -/
private lemma LF1_hermPart_eq {ι : Type*} (H : ι → ι → ℂ) (hH : (Matrix.of H).IsHermitian) :
    hermPart H = H := by
  funext i j
  have h1 : star (H j i) = H i j := by
    have := congrFun (congrFun hH i) j
    simpa [Matrix.conjTranspose_apply] using this
  simp only [hermPart, h1]
  ring

/-- `t Λ(A) = Λ(t A)` for real `t`. -/
private lemma LF1_lam_smul (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    (t : ℂ) • lam D N A = lam D N ((t : ℂ) • A) := by
  ext p q
  simp only [lam, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [mul_add, Complex.conj_ofReal]

/-- A real multiple of a Hermitian matrix is Hermitian. -/
private lemma LF1_herm_smul {ι : Type*} (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (c : ℝ) :
    (((c : ℝ) : ℂ) • Λ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hΛ.eq]
  simp

/-! ### The closed-form flow on `[0, S]` -/

/-- Along the closed-form flow (3.10) [eq:deterflow] on `[0, S]`, `S < t_c - t₀`, `‖Λ‖ ≤ 1/10`:
`η_s > 0`, `Im m_s = e^{s/2} Im m ∈ (0, 1)`, `η_s Im m_s` is at least its value at `S`,
`t_c - t_s = (t_c - t₀) - s` and `η_s ≥ (t_c - t_s) Im m_s`. -/
private lemma LF1_flow (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
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
  have hapr := mSol_apriori _ (LF1_herm_smul Λ hΛ (Real.exp (-s / 2))) hnorm _ hpos
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
private lemma LF1_adm (D N : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ N) (δA τ τe εg c C₀ : ℝ) (hεg : 0 < εg)
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
    LF1_flow D N hD (by omega) A hΛ z hz S hSt s hs0 hsS
  obtain ⟨-, hιeq, hι0, -, -, -, -⟩ := LF1_flow D N hD (by omega) A hΛ z hz S hSt s hs0 hsS
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

/-! ### The two-resolvent loop as a loop along the flow -/

/-- The loop list `[(E_y, z₁), (E_x, z₂)]`, whose loop is `⟨E_y G₁ E_x G₂⟩ = D⁻¹ L_{xy}`. -/
private abbrev LF1_l {D N : ℕ} (z₁ z₂ : ℂ) (x y : Fin D) :
    List (Matrix (Idx D N) (Idx D N) ℂ × ℂ) :=
  [(Ea D N y, z₁), (Ea D N x, z₂)]

/-- `⟨A B C E⟩ = ⟨E A (B C)⟩`. -/
private lemma LF1_ntr4 {ι : Type*} [Fintype ι] (A B C E : Matrix ι ι ℂ) :
    ntr (A * B * C * E) = ntr (E * A * (B * C)) := by
  rw [LF1_ntr_comm]
  simp only [Matrix.mul_assoc]

/-- `L_{xy}` at the Hermitian part of an array is `D` times the loop of `LF1_l`. -/
private lemma LF1_Lmat_loop {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (x y : Fin D) (r : ℝ) (h : Idx D N → Idx D N → ℂ) :
    flowLmat Λ z₁ z₂ r (hermPart h) x y = (D : ℂ) * flowLoop Λ (LF1_l z₁ z₂ x y) r h := by
  simp only [flowLmat, Lmat, flowLoop, chainB, LF1_l, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Matrix.mul_one]
  rw [LF1_ntr4]

/-- `𝓛(cF) = c 𝓛F` for real `c` and `C²` functions `F`. -/
private lemma LF1_genA_smul {D N : ℕ} (F : (Idx D N → Idx D N → ℂ) → ℂ) (hF : ContDiff ℝ 2 F)
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
private abbrev LF1_pw {ι : Type*} (G : Matrix ι ι ℂ) (b : Bool) : Matrix ι ι ℂ :=
  if b then Gᴴ else G

/-- `‖G^b‖ = ‖G‖`. -/
private lemma LF1_op_pw {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (b : Bool) :
    opNorm (LF1_pw G b) = opNorm G := by
  cases b
  · rfl
  · exact LF1_op_conj G

/-- At the flowed points `z_{i,s} ∈ {z_s, z̄_s}`: `G(z_{i,s}) = G(z_s)^b` and
`M(z_{i,s}) = M(z_s)^b` for one flag `b`. -/
private lemma LF1_flag {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian) (zi : ℂ)
    (hi : zi = z ∨ zi = star z) :
    ∃ b : Bool,
      res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) zi s) =
        LF1_pw (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) b ∧
      MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) zi s) =
        LF1_pw (MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) b := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  rcases hi with rfl | rfl
  · exact ⟨false, rfl, rfl⟩
  · refine ⟨true, ?_, ?_⟩
    · have hΛ := lam_isHermitian D N A
      have hX : (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A).IsHermitian :=
        hH.add (LF1_herm_smul _ hΛ _)
      have hw := (charFlow_M (lam D N A) hΛ z hz s hs).1
      rw [charFlowZ_conj _ z hz s, Complex.star_def, res_conj _ hX _ hw]
      rfl
    · have hΛ := lam_isHermitian D N A
      have hw := (charFlow_M (lam D N A) hΛ z hz s hs).1
      rw [charFlowZ_conj _ z hz s, (mExt_conj _ (LF1_herm_smul _ hΛ _) _ hw.ne').2]
      rfl

/-- `|⟨(G^b - M^b) E⟩| = |⟨(G - M) E⟩|` for a Hermitian `E`. -/
private lemma LF1_ntr_pw_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (G M E : Matrix ι ι ℂ)
    (hE : Eᴴ = E) (b : Bool) :
    ‖ntr ((LF1_pw G b - LF1_pw M b) * E)‖ = ‖ntr ((G - M) * E)‖ := by
  cases b
  · rfl
  · change ‖ntr ((Gᴴ - Mᴴ) * E)‖ = _
    have e : (Gᴴ - Mᴴ) * E = (E * (G - M))ᴴ := by
      rw [Matrix.conjTranspose_mul, hE, Matrix.conjTranspose_sub]
    rw [e, LF1_ntr_conj, norm_star, LF1_ntr_comm]

/-- The three-resolvent word as `resProd`. -/
private lemma LF1_word3 {ι : Type*} [Fintype ι] [DecidableEq ι] (G E₁ E₂ E₃ : Matrix ι ι ℂ)
    (b₁ b₂ b₃ : Bool) :
    LF1_pw G b₁ * E₁ * LF1_pw G b₂ * E₂ * LF1_pw G b₃ * E₃ =
      resProd (fun _ : Fin 3 => G) ![b₁, b₂, b₃] ![E₁, E₂, E₃] := by
  simp only [resProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.mul_one, Matrix.mul_assoc, LF1_pw]
  rfl

/-- The size `bndA4` of (A.53) [entprodG] for `p` equal resolvents: `Im m / η^{p-1}`, `p ≥ 2`. -/
private lemma LF1_bndA4 (p : ℕ) (hp : 2 ≤ p) (ι η : ℝ) :
    bndA4 (fun _ : Fin p => ι) (fun _ : Fin p => η) p = ι / η ^ (p - 1) := by
  have : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  simp [bndA4, hp]

/-- The fluctuation term of (3.53) [ItowtL]:
`D Σ_a (⟨(G₁ - M₁) E_a⟩ L_{(1,2,1),xya} + ⟨(G₂ - M₂) E_a⟩ L_{(2,1,2),yxa})`. -/
private def LF1_err {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (s : ℝ)
    (H : Idx D N → Idx D N → ℂ) (x y : Fin D) : ℂ :=
  (D : ℂ) * (∑ a, (ntr ((res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • Λ)
        (charFlowZ Λ z₁ s) - MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z₁ s)) *
        Ea D N a) *
      Lten3 (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) H (charFlowZ Λ z₁ s) (charFlowZ Λ z₂ s)
        (charFlowZ Λ z₁ s) x y a +
    ntr ((res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z₂ s) -
        MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z₂ s)) * Ea D N a) *
      Lten3 (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) H (charFlowZ Λ z₂ s) (charFlowZ Λ z₁ s)
        (charFlowZ Λ z₂ s) y x a))

/-- The fluctuation term for abstract `G`, `M` and Hermitian `E_a`, from bounds `β₁` on
`|⟨(G^b - M^b) E_a⟩|` and `β₂` on the three-resolvent words. -/
private lemma LF1_err_abs {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ℕ) (hD : 1 ≤ D)
    (G M : Matrix ι ι ℂ) (E : Fin D → Matrix ι ι ℂ) (b₁ b₂ : Bool) (β₁ β₂ : ℝ)
    (hfl : ∀ (b : Bool) (a : Fin D), ‖ntr ((LF1_pw G b - LF1_pw M b) * E a)‖ ≤ β₁)
    (hw : ∀ (c₁ c₂ c₃ : Bool) (a₁ a₂ a₃ : Fin D),
      ‖(D : ℂ) * ntr (LF1_pw G c₁ * E a₁ * LF1_pw G c₂ * E a₂ * LF1_pw G c₃ * E a₃)‖ ≤ β₂)
    (x y : Fin D) :
    ‖(D : ℂ) * (∑ a, (ntr ((LF1_pw G b₁ - LF1_pw M b₁) * E a) *
        ((D : ℂ) * ntr (LF1_pw G b₁ * E x * LF1_pw G b₂ * E y * LF1_pw G b₁ * E a)) +
      ntr ((LF1_pw G b₂ - LF1_pw M b₂) * E a) *
        ((D : ℂ) * ntr (LF1_pw G b₂ * E y * LF1_pw G b₁ * E x * LF1_pw G b₂ * E a))))‖ ≤
      D * (D * (2 * (β₁ * β₂))) := by
  have hβ₁0 : 0 ≤ β₁ := (norm_nonneg _).trans (hfl false ⟨0, hD⟩)
  have hterm : ∀ a : Fin D,
      ‖ntr ((LF1_pw G b₁ - LF1_pw M b₁) * E a) *
        ((D : ℂ) * ntr (LF1_pw G b₁ * E x * LF1_pw G b₂ * E y * LF1_pw G b₁ * E a)) +
      ntr ((LF1_pw G b₂ - LF1_pw M b₂) * E a) *
        ((D : ℂ) * ntr (LF1_pw G b₂ * E y * LF1_pw G b₁ * E x * LF1_pw G b₂ * E a))‖ ≤
        2 * (β₁ * β₂) := by
    intro a
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul (ntr ((LF1_pw G b₂ - LF1_pw M b₂) * E a))]
    have t1 := mul_le_mul (hfl b₁ a) (hw b₁ b₂ b₁ x y a) (norm_nonneg _) hβ₁0
    have t2 := mul_le_mul (hfl b₂ a) (hw b₂ b₁ b₂ y x a) (norm_nonneg _) hβ₁0
    linarith
  rw [norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => hterm a).trans ?_
  simp

/-- On the good event: `|⟨(G_i - M_i) E_a⟩| ≤ N^{τ'}/(N η_s)` (2.23) [eq:aver_local] and
`|L_{(i,j,i),xya}| ≤ D N^{τ'} Im m_s / η_s²` (A.53) [entprodG], so the fluctuation term is at
most `2 D³ N^{2τ'} Im m_s / (N η_s³)`. -/
private lemma LF1_err_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z) (τ' : ℝ)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian)
    (hgood : flowGoodAt A z τ' s H) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (x y : Fin D) :
    ‖LF1_err (lam D N A) z₁ z₂ s H x y‖ ≤
      2 * D ^ 3 * ((N : ℝ) ^ τ') ^ 2 * flowIm (lam D N A) z s /
        (N * (charFlowZ (lam D N A) z s).im ^ 3) := by
  have hNe : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  obtain ⟨b₁, hG₁, hM₁⟩ := LF1_flag hD hN A z hz s hs H hH z₁ h₁
  obtain ⟨b₂, hG₂, hM₂⟩ := LF1_flag hD hN A z hz s hs H hH z₂ h₂
  have hηpos : 0 < (charFlowZ (lam D N A) z s).im :=
    (charFlow_M _ (lam_isHermitian D N A) z hz s hs).1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hfl : ∀ (b : Bool) (a : Fin D),
      ‖ntr ((LF1_pw (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) b -
        LF1_pw (MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) b) * Ea D N a)‖ ≤
        (N : ℝ) ^ τ' / (N * (charFlowZ (lam D N A) z s).im) := fun b a => by
    rw [LF1_ntr_pw_sub _ _ _ (LF1_Ea_conj D N a)]
    exact hgood.1 a
  have hw : ∀ (c₁ c₂ c₃ : Bool) (a₁ a₂ a₃ : Fin D),
      ‖(D : ℂ) * ntr (LF1_pw (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) c₁ * Ea D N a₁ *
        LF1_pw (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) c₂ * Ea D N a₂ *
        LF1_pw (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) c₃ * Ea D N a₃)‖ ≤
        (D : ℝ) * ((N : ℝ) ^ τ' * (flowIm (lam D N A) z s /
          (charFlowZ (lam D N A) z s).im ^ 2)) := by
    intro c₁ c₂ c₃ a₁ a₂ a₃
    rw [norm_mul, Complex.norm_natCast, LF1_word3]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h3 := hgood.2.1 3 (by norm_num) (by norm_num) ![c₁, c₂, c₃] ![a₁, a₂, a₃]
    rw [LF1_bndA4 3 (by norm_num)] at h3
    have e : (fun i : Fin 3 => Ea D N (![a₁, a₂, a₃] i)) =
        ![Ea D N a₁, Ea D N a₂, Ea D N a₃] := by
      funext i; fin_cases i <;> rfl
    rw [e] at h3
    exact h3
  have key := LF1_err_abs D hD _ _ (Ea D N) b₁ b₂ _ _ hfl hw x y
  unfold LF1_err
  simp only [Lten3]
  rw [hG₁, hG₂, hM₁, hM₂]
  refine key.trans (le_of_eq ?_)
  field_simp

/-- `|L_{ab}| ≤ D / η_s²` along the flow. -/
private lemma LF1_L_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (a b : Fin D) :
    ‖flowLmat (lam D N A) z₁ z₂ s H a b‖ ≤ D / (charFlowZ (lam D N A) z s).im ^ 2 := by
  have hNe : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  obtain ⟨b₁, hG₁, -⟩ := LF1_flag hD hN A z hz s hs H hH z₁ h₁
  obtain ⟨b₂, hG₂, -⟩ := LF1_flag hD hN A z hz s hs H hH z₂ h₂
  have hΛ := lam_isHermitian D N A
  have hX : (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A).IsHermitian :=
    hH.add (LF1_herm_smul _ hΛ _)
  have hη := (charFlow_M _ hΛ z hz s hs).1
  have hGn := opNorm_res_le _ hX _ hη
  set G := res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
    (charFlowZ (lam D N A) z s)
  simp only [flowLmat, Lmat]
  rw [hG₁, hG₂, norm_mul, Complex.norm_natCast, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (LF1_ntr_le _).trans ?_
  have e1 := LF1_opNorm_Ea D N a
  have e2 := LF1_opNorm_Ea D N b
  have g1 : opNorm (LF1_pw G b₁) ≤ (charFlowZ (lam D N A) z s).im⁻¹ := by
    rw [LF1_op_pw]; exact hGn
  have g2 : opNorm (LF1_pw G b₂) ≤ (charFlowZ (lam D N A) z s).im⁻¹ := by
    rw [LF1_op_pw]; exact hGn
  have p1 := LF1_op_nonneg (LF1_pw G b₁)
  have p2 := LF1_op_nonneg (LF1_pw G b₂)
  have p3 := LF1_op_nonneg (Ea D N a)
  have p4 := LF1_op_nonneg (Ea D N b)
  have hinv : 0 ≤ (charFlowZ (lam D N A) z s).im⁻¹ := inv_nonneg.2 hη.le
  calc opNorm (LF1_pw G b₁ * Ea D N a * LF1_pw G b₂ * Ea D N b)
      ≤ opNorm (LF1_pw G b₁) * opNorm (Ea D N a) * opNorm (LF1_pw G b₂) * opNorm (Ea D N b) := by
        refine (LF1_op_mul _ _).trans ?_
        refine mul_le_mul_of_nonneg_right ((LF1_op_mul _ _).trans ?_) p4
        exact mul_le_mul_of_nonneg_right (LF1_op_mul _ _) p2
    _ ≤ (charFlowZ (lam D N A) z s).im⁻¹ * 1 * (charFlowZ (lam D N A) z s).im⁻¹ * 1 := by
        gcongr
    _ = ((charFlowZ (lam D N A) z s).im ^ 2)⁻¹ := by ring

/-- The block-diagonal GUE array is Hermitian. -/
private lemma LF1_blockH_herm (D N : ℕ) (w : Fin D → Coords N) : (blockH D N w).IsHermitian := by
  have h := HLam_isHermitian D N 0 w
  have e : lam D N (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
    funext p q; simp [lam]
  simpa [HLam, e] using h

/-- A real combination `a H + b X` of a Hermitian array and a block GUE array is Hermitian. -/
private lemma LF1_state_herm {D N : ℕ} (a b : ℝ) (H : Idx D N → Idx D N → ℂ)
    (hH : (Matrix.of H).IsHermitian) (X : Fin D → Coords N) :
    (Matrix.of (a • H + b • Matrix.of.symm (blockH D N X))).IsHermitian := by
  have e : Matrix.of (a • H + b • Matrix.of.symm (blockH D N X)) =
      ((a : ℝ) : ℂ) • Matrix.of H + ((b : ℝ) : ℂ) • blockH D N X := by
    ext i j
    simp [Complex.real_smul]
  rw [e]
  exact (LF1_herm_smul _ hH a).add (LF1_herm_smul _ (LF1_blockH_herm D N X) b)

/-- `N^{3τ} = (N^τ)³`. -/
private lemma LF1_rpow3 (x τ : ℝ) (hx : 0 ≤ x) : x ^ (3 * τ) = (x ^ τ) ^ 3 := by
  rw [mul_comm, Real.rpow_mul hx, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-! ### Real inequalities behind the drift bound -/

/-- The size `B` of the derivatives of a two-loop: `c (DN + 1)⁴ e^{q} K² ‖E‖² (η_S ∧ 1)^{-8}
≤ |c| (2D)⁴ N⁴ e (4 + τ⁻¹)² N⁸` when `q ≤ 1`, `K ≤ 4 + τ⁻¹`, `‖E‖² ≤ 1`, `η_S ∧ 1 ≥ N⁻¹`. -/
private lemma LF1_ar_B (c D N e K P m τ : ℝ) (hD : 1 ≤ D) (hN : 2 ≤ N) (he : e ≤ Real.exp 1)
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

/-- The remainder of the expansion: `D K B h² (1 + ‖H‖)⁴ (DN + 1)⁴ ≤ C₁ N^{16} h²`. -/
private lemma LF1_ar_R (KG c D N h Hn B R τ : ℝ) (hD : 1 ≤ D) (hN : 2 ≤ N) (hB0 : 0 ≤ B)
    (hB : B ≤ |c| * ((2 * D) ^ 4 * N ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2 * N ^ 8)
    (hHn0 : 0 ≤ Hn) (hHn : Hn ≤ 1)
    (hR : R ≤ KG * B * h ^ 2 * (1 + Hn) ^ 4 * (D * N + 1) ^ 4) :
    D * R ≤ (D * |KG| * |c| * Real.exp 1 * (4 + τ⁻¹) ^ 2 * 16 * (2 * D) ^ 8) * N ^ 16 * h ^ 2 := by
  have hDN : D * N + 1 ≤ 2 * D * N := by nlinarith
  have hDN4 : (D * N + 1) ^ 4 ≤ (2 * D) ^ 4 * N ^ 4 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hDN 4
  have hH4 : (1 + Hn) ^ 4 ≤ 16 := by
    have : (1 + Hn) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    norm_num at this ⊢; linarith
  have hKG : KG ≤ |KG| := le_abs_self _
  have h1 : R ≤ |KG| * (|c| * ((2 * D) ^ 4 * N ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2 * N ^ 8) *
      h ^ 2 * 16 * ((2 * D) ^ 4 * N ^ 4) := by
    refine hR.trans ?_
    calc KG * B * h ^ 2 * (1 + Hn) ^ 4 * (D * N + 1) ^ 4
        ≤ |KG| * B * h ^ 2 * (1 + Hn) ^ 4 * (D * N + 1) ^ 4 := by gcongr
      _ ≤ _ := by gcongr
  calc D * R ≤ D * (|KG| * (|c| * ((2 * D) ^ 4 * N ^ 4) * Real.exp 1 * (4 + τ⁻¹) ^ 2 * N ^ 8) *
      h ^ 2 * 16 * ((2 * D) ^ 4 * N ^ 4)) := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = _ := by ring

/-- `C₁ N^{16} ≤ N^{20}/2` for `N ≥ max(2, 2 C₁)`. -/
private lemma LF1_ar_N16 (C₁ N : ℝ) (hN : 2 ≤ N) (hC0 : 0 ≤ C₁) (hC : 2 * C₁ ≤ N) :
    C₁ * N ^ 16 ≤ N ^ (20 : ℝ) / 2 := by
  have hNpos : 0 < N := by linarith
  rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h1 : 2 * C₁ ≤ N ^ 4 := by
    have : N ≤ N ^ 4 := by
      calc N = N ^ 1 := (pow_one _).symm
        _ ≤ N ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have e : N ^ 20 = N ^ 4 * N ^ 16 := by ring
  rw [e]
  nlinarith [pow_pos hNpos 16]

/-- `D N² + D (D N²)² ≤ N^{20}/2` for `N ≥ max(2, 2D³)`. -/
private lemma LF1_ar_h2 (D N : ℝ) (hD : 1 ≤ D) (hN : 2 ≤ N) (hDN : 2 * D ^ 3 ≤ N) :
    D * N ^ 2 + D * (D * N ^ 2) ^ 2 ≤ N ^ (20 : ℝ) / 2 := by
  have hNpos : 0 < N := by linarith
  rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hD2 : 1 ≤ D ^ 2 := one_le_pow₀ hD
  have hDD : D ≤ D ^ 3 := by nlinarith
  have h5 : N ^ 5 * 2 ≤ N ^ 20 := by
    have e : N ^ 20 = N ^ 5 * N ^ 15 := by ring
    rw [e]
    have : (2 : ℝ) ≤ N ^ 15 := by
      calc (2 : ℝ) ≤ N := hN
        _ = N ^ 1 := (pow_one _).symm
        _ ≤ N ^ 15 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith [pow_pos hNpos 5]
  have e : D * N ^ 2 + D * (D * N ^ 2) ^ 2 = D * N ^ 2 + D ^ 3 * N ^ 4 := by ring
  rw [e]
  have t1 : D ^ 3 * N ^ 4 * 2 ≤ N * N ^ 4 := by nlinarith [pow_pos hNpos 4]
  have h7 : N ^ 2 ≤ N ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have t2 : D * N ^ 2 * 2 ≤ N * N ^ 4 := by nlinarith [pow_pos hNpos 2]
  have e2 : N * N ^ 4 = N ^ 5 := by ring
  nlinarith

/-- `q |err| ≤ t³ / (N q² ι²)` from `|err| ≤ 2 D³ t² ι / (N η³)`, `q ι ≤ η` and `2 D³ ≤ t`. -/
private lemma LF1_ar_err (q ι η D N t er : ℝ) (hq : 0 < q) (hι : 0 < ι) (hN : 0 < N)
    (ht : 0 < t) (hqι : q * ι ≤ η) (hD : 2 * D ^ 3 ≤ t)
    (her : er ≤ 2 * D ^ 3 * t ^ 2 * ι / (N * η ^ 3)) :
    q * er ≤ t ^ 3 / (N * q ^ 2 * ι ^ 2) := by
  have hη : 0 < η := lt_of_lt_of_le (mul_pos hq hι) hqι
  have h1 : q * er ≤ q * (2 * D ^ 3 * t ^ 2 * ι / (N * η ^ 3)) :=
    mul_le_mul_of_nonneg_left her hq.le
  refine h1.trans ?_
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (q * ι) ^ 3 ≤ η ^ 3 := pow_le_pow_left₀ (by positivity) hqι 3
  have h4 : 2 * D ^ 3 * t ^ 2 ≤ t ^ 3 := by
    have := mul_le_mul_of_nonneg_right hD (sq_nonneg t)
    nlinarith
  calc q * (2 * D ^ 3 * t ^ 2 * ι) * (N * q ^ 2 * ι ^ 2)
      = (2 * D ^ 3 * t ^ 2) * (N * (q * ι) ^ 3) := by ring
    _ ≤ t ^ 3 * (N * η ^ 3) := by
        apply mul_le_mul h4 _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left h3 hN.le

/-- `D / η² ≤ D N²` for `η > N⁻¹`. -/
private lemma LF1_ar_L (D N η : ℝ) (hD : 0 ≤ D) (hN : 0 < N) (hη : 0 < η) (hηN : N⁻¹ < η) :
    D / η ^ 2 ≤ D * N ^ 2 := by
  rw [div_le_iff₀ (pow_pos hη 2)]
  have : 1 ≤ N * η := by rw [inv_lt_iff_one_lt_mul₀ hN] at hηN; linarith
  have h2 : 1 ≤ (N * η) ^ 2 := one_le_pow₀ this
  nlinarith

/-- The drift of (3.53) [ItowtL]–(3.54) [mainwtL] in one grid step: on the good event at time
`s`, for `L̃ = q_s L_{(1,2),s}`, `q_s = t_c - t₀ - s`, a step `h ≤ N^{-31}` within `[0, S]` gives
`|E_X L̃(s + h) - L̃ - h q_s⁻¹ ((q_s - 1) L̃ + L̃²)| ≤ h N^{3τ'} / (N q_s² (Im m_s)²) + h² N^{20}`,
entrywise. -/
theorem flowL2_drift (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ s h : ℝ, 0 ≤ s → 0 < h → s + h ≤ S → h ≤ (N : ℝ) ^ (-(31 : ℝ)) →
      ∀ H : Idx D N → Idx D N → ℂ, (Matrix.of H).IsHermitian → flowGoodAt A z τ' s H →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → ∀ x y : Fin D,
        ‖(∫ X, ((flowTc (lam D N A) z - (s + h) : ℝ) : ℂ) *
              flowLmat (lam D N A) z₁ z₂ (s + h) (Real.exp (-h / 2) • H +
                Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N)) -
            ((flowTc (lam D N A) z - s : ℝ) : ℂ) * flowLmat (lam D N A) z₁ z₂ s H x y -
            (h : ℂ) * (((flowTc (lam D N A) z - s - 1 : ℝ) : ℂ) *
                flowLmat (lam D N A) z₁ z₂ s H x y +
              ((flowTc (lam D N A) z - s : ℝ) : ℂ) *
                (flowLmat (lam D N A) z₁ z₂ s H * flowLmat (lam D N A) z₁ z₂ s H) x y)‖ ≤
          h * ((N : ℝ) ^ (3 * τ') /
              (N * (flowTc (lam D N A) z - s) ^ 2 * flowIm (lam D N A) z s ^ 2)) +
            h ^ 2 * (N : ℝ) ^ (20 : ℝ) := by
  intro τ' hτ'
  obtain ⟨cR, hcR⟩ := flowLoop_regular
  obtain ⟨KG, hKG⟩ := gaussStepA_expansion_t
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = (D : ℝ) * |KG| * |cR 2| * Real.exp 1 * (4 + τ⁻¹) ^ 2 * 16 *
      (2 * D) ^ 8 := ⟨_, rfl⟩
  have hev : ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N ∧ 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧
      c * (N : ℝ) ^ (-εg) ≤ 1 ∧ 2 * (D : ℝ) ^ 3 ≤ (N : ℝ) ^ τ' ∧
      2 * C₁ + 2 * (D : ℝ) ^ 3 + 2 ≤ N := by
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
  refine ⟨N₀, fun N hN A z S hadm s h hs0 hh hsh hhN H hH hgood z₁ z₂ h₁ h₂ x y => ?_⟩
  obtain ⟨hN2, hAN, hcN, hDτ, hNC⟩ := hN₀ N hN
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  haveI : NeZero D := ⟨by omega⟩
  haveI : NeZero N := ⟨by omega⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hΛ10, hzτ, hz, hm1, hq0, hq1, hS0, hSt, hη⟩ :=
    LF1_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  have hSpos : 0 < S := by linarith
  have hsS : s ≤ S := by linarith
  have hsq : s < flowTc (lam D N A) z := by linarith
  obtain ⟨hηs, hιeq, hι0, hιs1, -, -, hqι⟩ := LF1_flow D N hD1 hN1 A hΛ10 z hz S hSt s hs0 hsS
  have hιs : 0 < flowIm (lam D N A) z s := by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
  have hh1 : h ≤ 1 :=
    hhN.trans (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num))
  have hΛ : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hlf : ∀ f ∈ LF1_l (N := N) z₁ z₂ x y, f.2 = z ∨ f.2 = star z := by
    intro f hf
    simp only [LF1_l, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    exacts [h₁, h₂]
  obtain ⟨Ft, hder, hreg⟩ := hcR D N (lam D N A) hΛ z hz (LF1_l z₁ z₂ x y) hlf S hS0 hSt
  have hsub : Set.Icc s (s + h) ⊆ Set.Icc 0 S := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hexp := hKG D N (fun r v => flowLoop (lam D N A) (LF1_l z₁ z₂ x y) r v) Ft _ h s hh hh1
    (fun r hr => ⟨(hreg r (hsub hr)).1, (hreg r (hsub hr)).2.1⟩)
    (fun r hr v => (hder r (hsub hr) v).mono hsub)
    (fun r hr j hj1 hj4 v => (hreg r (hsub hr)).2.2.1 j hj1 hj4 v)
    (fun r hr r' hr' v => (hreg r (hsub hr)).2.2.2 r' (hsub hr') v) H
  -- `L = D ⟨E_y G₁ E_x G₂⟩` at Hermitian arrays
  have hφ : ∀ (r : ℝ) (H' : Idx D N → Idx D N → ℂ), (Matrix.of H').IsHermitian →
      flowLmat (lam D N A) z₁ z₂ r H' x y =
        (D : ℂ) * flowLoop (lam D N A) (LF1_l z₁ z₂ x y) r H' := by
    intro r H' hH'
    have := LF1_Lmat_loop (lam D N A) z₁ z₂ x y r H'
    rwa [LF1_hermPart_eq H' hH'] at this
  have hsI : s ∈ Set.Icc 0 S := ⟨hs0, hsS⟩
  have hd1 : HasDerivWithinAt (fun r => flowLmat (lam D N A) z₁ z₂ r H x y)
      ((D : ℂ) * Ft s H) (Set.Icc 0 S) s :=
    ((hder s hsI H).const_mul (D : ℂ)).congr (fun r _ => hφ r H hH) (hφ s H hH)
  have hd2 : HasDerivAt (fun r : ℝ => flowLmat (lam D N A) z₁ z₂ r H x y)
      (flowLmat (lam D N A) z₁ z₂ s H x y +
        (flowLmat (lam D N A) z₁ z₂ s H * flowLmat (lam D N A) z₁ z₂ s H) x y +
        LF1_err (lam D N A) z₁ z₂ s H x y -
        genA (fun h => flowLmat (lam D N A) z₁ z₂ s (hermPart h) x y) H) s :=
    gen_loop2 D N A z hz s hsq z₁ z₂ h₁ h₂ H hH x y
  have huniq := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc hSpos s hsI) hd1
    hd2.hasDerivWithinAt
  have hgen : genA (fun h => flowLmat (lam D N A) z₁ z₂ s (hermPart h) x y) H =
      (D : ℂ) * genA (flowLoop (lam D N A) (LF1_l z₁ z₂ x y) s) H := by
    have e : (fun h => flowLmat (lam D N A) z₁ z₂ s (hermPart h) x y) =
        fun h => ((D : ℝ) : ℂ) * flowLoop (lam D N A) (LF1_l z₁ z₂ x y) s h := by
      funext h
      rw [LF1_Lmat_loop]
      push_cast
      rfl
    rw [e, LF1_genA_smul _ ((hreg s hsI).1.of_le (by norm_num))]
    push_cast
    rfl
  -- the integral
  have hint : (∫ X, ((flowTc (lam D N A) z - (s + h) : ℝ) : ℂ) *
        flowLmat (lam D N A) z₁ z₂ (s + h) (Real.exp (-h / 2) • H +
          Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X)) x y
        ∂(gueBlocks D N)) =
      ((flowTc (lam D N A) z - (s + h) : ℝ) : ℂ) * ((D : ℂ) *
        ∫ X, flowLoop (lam D N A) (LF1_l z₁ z₂ x y) (s + h) (Real.exp (-h / 2) • H +
          Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X)) ∂(gueBlocks D N)) := by
    rw [integral_const_mul, integral_congr_ae (Filter.Eventually.of_forall fun X =>
      hφ _ _ (LF1_state_herm _ _ H hH X)), integral_const_mul]
  rw [hint]
  -- the error terms
  set E := ∫ X, flowLoop (lam D N A) (LF1_l z₁ z₂ x y) (s + h) (Real.exp (-h / 2) • H +
    Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X)) ∂(gueBlocks D N) with hE
  set Fs := flowLoop (lam D N A) (LF1_l z₁ z₂ x y) s H with hFs
  set gA := genA (flowLoop (lam D N A) (LF1_l z₁ z₂ x y) s) H with hgA
  set R := E - Fs - h * (Ft s H + gA) with hR
  set Lx := flowLmat (lam D N A) z₁ z₂ s H x y with hLx
  set LL := (flowLmat (lam D N A) z₁ z₂ s H * flowLmat (lam D N A) z₁ z₂ s H) x y with hLL
  set er := LF1_err (lam D N A) z₁ z₂ s H x y with her
  set gT := genA (fun h => flowLmat (lam D N A) z₁ z₂ s (hermPart h) x y) H with hgT
  set q := flowTc (lam D N A) z - s with hq
  have hLF : Lx = (D : ℂ) * Fs := hφ s H hH
  have ekey : ((flowTc (lam D N A) z - (s + h) : ℝ) : ℂ) * ((D : ℂ) * E) -
        ((flowTc (lam D N A) z - s : ℝ) : ℂ) * Lx -
        (h : ℂ) * (((flowTc (lam D N A) z - s - 1 : ℝ) : ℂ) * Lx +
          ((flowTc (lam D N A) z - s : ℝ) : ℂ) * LL) =
      ((q - h : ℝ) : ℂ) * ((D : ℂ) * R) + (h : ℂ) * ((q - h : ℝ) : ℂ) * er -
        (h : ℂ) ^ 2 * (Lx + LL) := by
    have e1 : ((flowTc (lam D N A) z - (s + h) : ℝ) : ℂ) = ((q - h : ℝ) : ℂ) := by
      rw [hq]; push_cast; ring
    have e2 : ((flowTc (lam D N A) z - s - 1 : ℝ) : ℂ) = (q : ℂ) - 1 := by
      rw [hq]; push_cast; ring
    have e3 : ((flowTc (lam D N A) z - s : ℝ) : ℂ) = (q : ℂ) := by rw [hq]
    rw [e1, e2, e3]
    push_cast
    linear_combination (↑q - ↑h) * (D : ℂ) * hR - (↑q - ↑h) * hLF +
      (↑q - ↑h) * (h : ℂ) * huniq - (↑q - ↑h) * (h : ℂ) * hgen
  rw [ekey]
  -- bounds
  have hq0' : 0 ≤ q - h := by rw [hq]; linarith
  have hq1' : q - h ≤ 1 := by rw [hq]; linarith
  have hqq : q - h ≤ q := by linarith
  have hHn : ‖H‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => hgood.2.2 i j
  -- the remainder of the expansion
  have hηS := (hη S hS0 le_rfl).1
  have hBle := LF1_ar_B (cR 2) D N (Real.exp (flowTc (lam D N A) z))
    (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A))
    (opNorm (Ea D N y) * opNorm (Ea D N x)) (min 1 (charFlowZ (lam D N A) z S).im) τ
    (by exact_mod_cast hD1) hNr (Real.exp_le_exp.2 hq1) (Real.exp_pos _).le
    (by have h1 := norm_nonneg z; have h2 := norm_nonneg (mExt (lam D N A) z)
        have h3 := LF1_op_nonneg (lam D N A); linarith only [h1, h2, h3])
    (by linarith only [hzτ, hm1, hΛ10])
    (mul_nonneg (LF1_op_nonneg _) (LF1_op_nonneg _))
    ((mul_le_mul (LF1_opNorm_Ea D N y) (LF1_opNorm_Ea D N x) (LF1_op_nonneg _)
      zero_le_one).trans_eq (one_mul 1))
    (le_min (inv_le_one_of_one_le₀ (by linarith)) hηS.le)
  have hB0 : 0 ≤ cR (LF1_l (N := N) z₁ z₂ x y).length * ((D : ℝ) * N + 1) ^ 4 *
      Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      ((LF1_l (N := N) z₁ z₂ x y).map fun f => opNorm f.1).prod *
      ((min 1 (charFlowZ (lam D N A) z S).im) ^ ((LF1_l (N := N) z₁ z₂ x y).length + 6))⁻¹ :=
    (norm_nonneg _).trans ((hreg s hsI).2.2.1 1 le_rfl (by norm_num) H).1
  have hBeq : cR (LF1_l (N := N) z₁ z₂ x y).length * ((D : ℝ) * N + 1) ^ 4 *
      Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      ((LF1_l (N := N) z₁ z₂ x y).map fun f => opNorm f.1).prod *
      ((min 1 (charFlowZ (lam D N A) z S).im) ^ ((LF1_l (N := N) z₁ z₂ x y).length + 6))⁻¹ =
      cR 2 * ((D : ℝ) * N + 1) ^ 4 * Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      (opNorm (Ea D N y) * opNorm (Ea D N x)) *
      ((min 1 (charFlowZ (lam D N A) z S).im) ^ 8)⁻¹ := by
    simp only [LF1_l, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
  rw [hBeq] at hB0 hexp
  have hR16 : (D : ℝ) * ‖R‖ ≤ C₁ * (N : ℝ) ^ 16 * h ^ 2 := by
    rw [hC₁]
    exact LF1_ar_R KG (cR 2) D N h ‖H‖ _ ‖R‖ τ (by exact_mod_cast hD1) hNr hB0 hBle
      (norm_nonneg _) hHn hexp
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hN16 := LF1_ar_N16 C₁ N hNr hC₁0 (by linarith only [hNC, hC₁0, pow_nonneg (Nat.cast_nonneg D : (0:ℝ) ≤ D) 3])
  -- the fluctuation term
  have herr := LF1_err_le D N hD1 hN1 A z hz s hsq τ' H hH hgood z₁ z₂ h₁ h₂ x y
  have hqpos : 0 < q := by rw [hq]; linarith
  have herrq : q * ‖er‖ ≤ (N : ℝ) ^ (3 * τ') /
      (N * (flowTc (lam D N A) z - s) ^ 2 * flowIm (lam D N A) z s ^ 2) := by
    rw [← hq, LF1_rpow3 _ _ hNpos.le]
    exact LF1_ar_err q (flowIm (lam D N A) z s) (charFlowZ (lam D N A) z s).im D N
      ((N : ℝ) ^ τ') ‖er‖ hqpos hιs hNpos (Real.rpow_pos_of_pos hNpos _) hqι hDτ herr
  -- the terms of order `h²`
  have hLb : ∀ a b : Fin D, ‖flowLmat (lam D N A) z₁ z₂ s H a b‖ ≤ D * (N : ℝ) ^ 2 := by
    intro a b
    refine (LF1_L_le D N hD1 hN1 A z hz s hsq H hH z₁ z₂ h₁ h₂ a b).trans ?_
    exact LF1_ar_L D N _ (Nat.cast_nonneg D) hNpos hηs (hη s hs0 hsS).1
  have hLLb : ‖LL‖ ≤ D * (D * (N : ℝ) ^ 2) ^ 2 := by
    rw [hLL, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖flowLmat (lam D N A) z₁ z₂ s H x a * flowLmat (lam D N A) z₁ z₂ s H a y‖
        ≤ ∑ _a : Fin D, (D * (N : ℝ) ^ 2) ^ 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul, sq]
          exact mul_le_mul (hLb x a) (hLb a y) (norm_nonneg _) (by positivity)
      _ = D * (D * (N : ℝ) ^ 2) ^ 2 := by simp
  have hh2 := LF1_ar_h2 D N (by exact_mod_cast hD1) hNr (by linarith only [hNC, hC₁0])
  -- assembly
  have hnorm1 : ‖((q - h : ℝ) : ℂ) * ((D : ℂ) * R)‖ ≤ (N : ℝ) ^ (20 : ℝ) / 2 * h ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0',
      Complex.norm_natCast]
    calc (q - h) * (D * ‖R‖) ≤ 1 * (C₁ * (N : ℝ) ^ 16 * h ^ 2) :=
          mul_le_mul hq1' hR16 (by positivity) zero_le_one
      _ ≤ (N : ℝ) ^ (20 : ℝ) / 2 * h ^ 2 := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right hN16 (sq_nonneg h)
  have hnorm2 : ‖(h : ℂ) * ((q - h : ℝ) : ℂ) * er‖ ≤ h * ((N : ℝ) ^ (3 * τ') /
      (N * (flowTc (lam D N A) z - s) ^ 2 * flowIm (lam D N A) z s ^ 2)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hh, abs_of_nonneg hq0', mul_assoc]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ herrq) hh.le
    exact mul_le_mul_of_nonneg_right hqq (norm_nonneg _)
  have hnorm3 : ‖(h : ℂ) ^ 2 * (Lx + LL)‖ ≤ (N : ℝ) ^ (20 : ℝ) / 2 * h ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have : ‖Lx + LL‖ ≤ (N : ℝ) ^ (20 : ℝ) / 2 :=
      (norm_add_le _ _).trans ((add_le_add (hLb x y) hLLb).trans hh2)
    calc h ^ 2 * ‖Lx + LL‖ ≤ h ^ 2 * ((N : ℝ) ^ (20 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left this (sq_nonneg h)
      _ = _ := by ring
  calc ‖((q - h : ℝ) : ℂ) * ((D : ℂ) * R) + (h : ℂ) * ((q - h : ℝ) : ℂ) * er -
        (h : ℂ) ^ 2 * (Lx + LL)‖
      ≤ ‖((q - h : ℝ) : ℂ) * ((D : ℂ) * R)‖ + ‖(h : ℂ) * ((q - h : ℝ) : ℂ) * er‖ +
        ‖(h : ℂ) ^ 2 * (Lx + LL)‖ := by
        exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (N : ℝ) ^ (20 : ℝ) / 2 * h ^ 2 + h * ((N : ℝ) ^ (3 * τ') /
          (N * (flowTc (lam D N A) z - s) ^ 2 * flowIm (lam D N A) z s ^ 2)) +
        (N : ℝ) ^ (20 : ℝ) / 2 * h ^ 2 := add_le_add (add_le_add hnorm1 hnorm2) hnorm3
    _ = _ := by ring

/-! ### The deterministic side: (3.18) [eq:whMK] and the Riccati equation of `K_{θ_s}` -/

/-- `K_r = (1 - e^r X P_{θ_r})⁻¹ e^r X`, `θ_r = 1 - e^{-r}(1 - θ)`, the closed form of
`K_{θ_r}` along the flow with `X = M̂(z₁, z₂)` (3.18) [eq:whMK]. -/
private def LF1_R {D : ℕ} (X : Matrix (Fin D) (Fin D) ℂ) (θ r : ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  (1 - ((Real.exp r : ℝ) : ℂ) • X * PTheta D (1 - Real.exp (-r) * (1 - θ)))⁻¹ *
    (((Real.exp r : ℝ) : ℂ) • X)

/-- Along the flow on `[0, S]`: `K_{θ_t}(z_{1,t}, z_{2,t})` is the closed form `LF1_R`, it solves
`dK/dt = K² + K` entrywise, and `‖(t_c - t₀ - t) K_{θ_t}‖ ≤ 1`, so its entries are at most
`(t_c - t₀ - t)⁻¹`. -/
private lemma LF1_flowK (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (t : ℝ) (ht0 : 0 ≤ t)
    (htS : t ≤ S) :
    flowKmat (lam D N A) θ z₁ z₂ t = LF1_R (Mhat (lam D N A) z₁ z₂) θ t ∧
      (∀ a b : Fin D, HasDerivAt (fun r => LF1_R (Mhat (lam D N A) z₁ z₂) θ r a b)
        ((LF1_R (Mhat (lam D N A) z₁ z₂) θ t * LF1_R (Mhat (lam D N A) z₁ z₂) θ t +
          LF1_R (Mhat (lam D N A) z₁ z₂) θ t) a b) t) ∧
      ∀ a b : Fin D, ‖flowKmat (lam D N A) θ z₁ z₂ t a b‖ ≤ (flowTc (lam D N A) z - t)⁻¹ := by
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hΛ := lam_isHermitian D N A
  have ht : t < flowTc (lam D N A) z := lt_of_le_of_lt htS hS
  obtain ⟨hηt, -, -, -, -, htc, -⟩ := LF1_flow D N hD1 hN1 A hA z hz S hS t ht0 htS
  have hMh := Mhat_flow (lam D N A) hΛ z hz t ht z₁ z₂ h₁ h₂
  have hθt : Real.exp (-t) * θ + 1 - Real.exp (-t) = 1 - Real.exp (-t) * (1 - θ) := by ring
  have hK : flowKmat (lam D N A) θ z₁ z₂ t = LF1_R (Mhat (lam D N A) z₁ z₂) θ t := by
    simp only [flowKmat, KTheta, LF1_R, hMh, hθt]
  -- the operator bound at the flowed point
  set A' : Matrix (Fin N) (Fin N) ℂ := ((Real.exp (-t / 2) : ℝ) : ℂ) • A with hA'
  have hlam : lam D N A' = ((Real.exp (-t / 2) : ℝ) : ℂ) • lam D N A :=
    (LF1_lam_smul D N A _).symm
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
    have h1 := LF1_entry_le (((flowTc (lam D N A) z - t : ℝ) : ℂ) •
      flowKmat (lam D N A) θ z₁ z₂ t) a b
    have h2 := h1.trans hop
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hq] at h2
    have h3 := (le_div_iff₀' hq).2 h2
    rwa [one_div] at h3

/-- The one-step error of the Riccati equation (3.55) [mainwtK] on the grid: for
`K̃_t = (t_c - t₀ - t) K_{θ_t}` and `[u, u + h] ⊂ [0, S]`,
`|K̃_{u+h} - K̃_u - h ((q_u - 1) K_u + q_u K_u²)| ≤ L h²` entrywise, with
`L = (D ρ² + ρ)(3 + 2 D ρ)` and `ρ = (t_c - t₀ - S)⁻¹`. -/
private lemma LF1_Kdisc (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (hq1 : flowTc (lam D N A) z ≤ 1) (θ : ℝ) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z)
    (u h : ℝ) (hu : 0 ≤ u) (hh : 0 ≤ h) (huh : u + h ≤ S) (a b : Fin D) :
    ‖(((flowTc (lam D N A) z - (u + h) : ℝ) : ℂ) • flowKmat (lam D N A) θ z₁ z₂ (u + h) -
        ((flowTc (lam D N A) z - u : ℝ) : ℂ) • flowKmat (lam D N A) θ z₁ z₂ u -
        (h : ℂ) • (((flowTc (lam D N A) z - u - 1 : ℝ) : ℂ) • flowKmat (lam D N A) θ z₁ z₂ u +
          ((flowTc (lam D N A) z - u : ℝ) : ℂ) •
            (flowKmat (lam D N A) θ z₁ z₂ u * flowKmat (lam D N A) θ z₁ z₂ u))) a b‖ ≤
      ((D : ℝ) * (flowTc (lam D N A) z - S)⁻¹ ^ 2 + (flowTc (lam D N A) z - S)⁻¹) *
        (3 + 2 * D * (flowTc (lam D N A) z - S)⁻¹) * h ^ 2 := by
  set q₀ := flowTc (lam D N A) z with hq₀
  set ρ := (q₀ - S)⁻¹ with hρ
  set R := LF1_R (Mhat (lam D N A) z₁ z₂) θ with hRdef
  have hqS : 0 < q₀ - S := by linarith
  have hρ0 : 0 < ρ := inv_pos.2 hqS
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hfac : ∀ t ∈ Set.Icc 0 S, flowKmat (lam D N A) θ z₁ z₂ t = R t ∧
      (∀ c d : Fin D, HasDerivAt (fun r => R r c d) ((R t * R t + R t) c d) t) ∧
      ∀ c d : Fin D, ‖R t c d‖ ≤ ρ := by
    intro t ht
    obtain ⟨e1, e2, e3⟩ := LF1_flowK D N A hA z hz S hS θ hθ₀ hθ₁ z₁ z₂ h₁ h₂ t ht.1 ht.2
    refine ⟨e1, e2, fun c d => ?_⟩
    have e4 := e3 c d
    rw [e1] at e4
    refine e4.trans ?_
    have : 0 < q₀ - t := by linarith [ht.2]
    exact inv_anti₀ hqS (by linarith [ht.2])
  -- entries of `R²` and of `R² + R`
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
  -- Lipschitz bounds on `[0, S]`
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
  -- the derivative of `K̃_{ab}` and its Lipschitz bound
  set Kp : ℝ → ℂ := fun t => -R t a b + ((q₀ - t : ℝ) : ℂ) * (R t * R t + R t) a b with hKp
  have hKpd : ∀ t ∈ Set.Icc 0 S,
      HasDerivAt (fun r => ((q₀ - r : ℝ) : ℂ) * R r a b) (Kp t) t := by
    intro t ht
    have h1 : HasDerivAt (fun r : ℝ => ((q₀ - r : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) t :=
      ((hasDerivAt_id t).const_sub q₀).ofReal_comp
    have h2 := h1.mul ((hfac t ht).2.1 a b)
    convert h2 using 1
    simp only [hKp]
    push_cast
    ring
  have hKplip : ∀ t ∈ Set.Icc 0 S, ∀ u ∈ Set.Icc 0 S,
      ‖Kp t - Kp u‖ ≤ ((D : ℝ) * ρ ^ 2 + ρ) * (3 + 2 * D * ρ) * |t - u| := by
    intro t ht u hu
    have e1 : Kp t - Kp u = -(R t a b - R u a b) +
        ((q₀ - t : ℝ) : ℂ) * (((R t * R t) a b - (R u * R u) a b) + (R t a b - R u a b)) +
        ((u - t : ℝ) : ℂ) * (R u * R u + R u) a b := by
      simp only [hKp, Matrix.add_apply]
      push_cast
      ring
    rw [e1]
    have hqt : ‖((q₀ - t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      linarith [ht.1]
    have l1 := hRlip t ht u hu a b
    have l2 := hRRlip t ht u hu
    have l3 := hP u hu a b
    have hut : ‖((u - t : ℝ) : ℂ)‖ = |t - u| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    have hL0 : 0 ≤ (D * ρ ^ 2 + ρ) * |t - u| := by positivity
    calc ‖-(R t a b - R u a b) +
          ((q₀ - t : ℝ) : ℂ) * (((R t * R t) a b - (R u * R u) a b) + (R t a b - R u a b)) +
          ((u - t : ℝ) : ℂ) * (R u * R u + R u) a b‖
        ≤ ‖R t a b - R u a b‖ +
          ‖((q₀ - t : ℝ) : ℂ)‖ * (‖(R t * R t) a b - (R u * R u) a b‖ + ‖R t a b - R u a b‖) +
          ‖((u - t : ℝ) : ℂ)‖ * ‖(R u * R u + R u) a b‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (le_of_eq (norm_neg _)) ?_)) (le_of_eq (norm_mul _ _)))
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ ≤ (D * ρ ^ 2 + ρ) * |t - u| +
          1 * (D * (2 * ρ * ((D * ρ ^ 2 + ρ) * |t - u|)) + (D * ρ ^ 2 + ρ) * |t - u|) +
          |t - u| * (D * ρ ^ 2 + ρ) := by
          rw [hut]
          gcongr
      _ = ((D : ℝ) * ρ ^ 2 + ρ) * (3 + 2 * D * ρ) * |t - u| := by ring
  -- the mean value theorem for `t ↦ K̃_{ab}(t) - t K̃'_{ab}(u)` on `[u, u + h]`
  have hsub : Set.Icc u (u + h) ⊆ Set.Icc 0 S := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have huI : u ∈ Set.Icc 0 S := ⟨hu, by linarith⟩
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := ((D : ℝ) * ρ ^ 2 + ρ) * (3 + 2 * D * ρ) * h)
    (f := fun r => ((q₀ - r : ℝ) : ℂ) * R r a b - (r : ℂ) * Kp u)
    (f' := fun r => Kp r - Kp u)
    (fun x hx => by
      have h1 := hKpd x (hsub hx)
      have h2 : HasDerivAt (fun r : ℝ => (r : ℂ) * Kp u) (1 * Kp u) x :=
        (hasDerivAt_id x).ofReal_comp.mul_const _ |>.congr_deriv (by simp)
      exact (h1.sub h2).hasDerivWithinAt.congr_deriv (by ring))
    (fun x hx => by
      refine (hKplip x (hsub hx) u huI).trans ?_
      have : |x - u| ≤ h := by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
      have hL : 0 ≤ ((D : ℝ) * ρ ^ 2 + ρ) * (3 + 2 * D * ρ) := by positivity
      exact mul_le_mul_of_nonneg_left this hL)
    (convex_Icc u (u + h)) (⟨le_rfl, by linarith⟩ : u ∈ Set.Icc u (u + h))
    (⟨by linarith, le_rfl⟩ : u + h ∈ Set.Icc u (u + h))
  -- identification of the entry
  have hKu := (hfac u huI).1
  have hKuh := (hfac (u + h) ⟨by linarith, huh⟩).1
  rw [hKu, hKuh]
  have e2 : ((((q₀ - (u + h) : ℝ) : ℂ) • R (u + h) - ((q₀ - u : ℝ) : ℂ) • R u -
      (h : ℂ) • (((q₀ - u - 1 : ℝ) : ℂ) • R u + ((q₀ - u : ℝ) : ℂ) • (R u * R u))) a b) =
      (((q₀ - (u + h) : ℝ) : ℂ) * R (u + h) a b - ((u + h : ℝ) : ℂ) * Kp u) -
        (((q₀ - u : ℝ) : ℂ) * R u a b - (u : ℂ) * Kp u) := by
    simp only [hKp, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    push_cast
    ring
  rw [e2]
  refine hmv.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, show u + h - u = h by ring, abs_of_nonneg hh]
  ring

/-! ### Gaussian and grid tools for the martingale part -/

/-- The map `(x, y) ↦ x + y i` as a continuous linear map. -/
private def LF1_RealPairToC : ℝ × ℝ →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I

/-- `cGauss` is a Gaussian law. -/
private instance LF1_cGauss_isGaussian : IsGaussian (cGauss : Measure ℂ) := by
  have : (cGauss : Measure ℂ) =
      ((gaussianReal 0 (1 / 2 : ℝ≥0)).prod (gaussianReal 0 (1 / 2 : ℝ≥0))).map
        LF1_RealPairToC := by
    have e : (LF1_RealPairToC : ℝ × ℝ → ℂ) =
        fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      funext p; simp [LF1_RealPairToC, Complex.real_smul]
    rw [e]
    rfl
  rw [this]
  infer_instance

/-- A product of copies of a Gaussian law is Gaussian. -/
private instance LF1_isGaussian_pi {ι X : Type*} [Fintype ι] [NormedAddCommGroup X]
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
private instance LF1_gueBlocks_isGaussian (D N : ℕ) : IsGaussian (gueBlocks D N) := by
  have : IsGaussian (gueLaw N) := by unfold gueLaw; infer_instance
  unfold gueBlocks
  infer_instance

/-- `‖x‖^p` is integrable under the GUE blocks. -/
private lemma LF1_int_pow (D N p : ℕ) :
    Integrable (fun x : Fin D → Coords N => ‖x‖ ^ p) (gueBlocks D N) :=
  (IsGaussian.memLp_id (gueBlocks D N) p (by simp)).integrable_norm_pow'

/-- `x ↦ -x` preserves the GUE blocks. -/
private lemma LF1_gueBlocks_neg (D N : ℕ) :
    MeasurePreserving (fun x : Fin D → Coords N => -x) (gueBlocks D N) (gueBlocks D N) := by
  refine ⟨measurable_neg, ?_⟩
  have := Measure.pi_map_pi (μ := fun _ : Fin D => gueLaw N) (f := fun _ x => -x)
    (fun _ => measurable_neg.aemeasurable)
  simp only [gueLaw_map_neg] at this
  exact this

/-- An odd function has integral `0` under the GUE blocks. -/
private lemma LF1_gueBlocks_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (D N : ℕ)
    (f : (Fin D → Coords N) → E) (hf : ∀ x, f (-x) = -f x) :
    ∫ x, f x ∂(gueBlocks D N) = 0 := by
  have h := (LF1_gueBlocks_neg D N).integral_comp (MeasurableEquiv.neg _).measurableEmbedding f
  simp only [hf, integral_neg] at h
  have : (2 : ℝ) • ∫ x, f x ∂(gueBlocks D N) = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; simp
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

/-- `‖x‖⁴ ≤ Σ_i ‖x_i‖⁴` for the sup norm of a finite product. -/
private lemma LF1_pi_pow4 {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (x : ι → E) :
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
private lemma LF1_prod_pow4 {E G : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup G]
    (p : E × G) : ‖p‖ ^ 4 ≤ ‖p.1‖ ^ 4 + ‖p.2‖ ^ 4 := by
  rw [Prod.norm_def]
  rcases le_total ‖p.1‖ ‖p.2‖ with h | h
  · rw [max_eq_right h]; have := pow_nonneg (norm_nonneg p.1) 4; linarith
  · rw [max_eq_left h]; have := pow_nonneg (norm_nonneg p.2) 4; linarith

/-- The fourth moment of the GUE blocks: `E‖X‖⁴ ≤ (DN + DN²)(m₄ + m₄')`, with `m₄` and `m₄'` the
fourth absolute moments of `N(0, 1)` and of the standard complex Gaussian. -/
private lemma LF1_moment4 (D N : ℕ) :
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
    refine (LF1_pi_pow4 x).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (LF1_prod_pow4 (x a)).trans (add_le_add (LF1_pi_pow4 _) ?_)
    exact (LF1_pi_pow4 _).trans (Finset.sum_le_sum fun i _ => LF1_pi_pow4 _)
  have iS : ∀ a : Fin D, Integrable (fun x : Fin D → Coords N =>
      (∑ i, ‖(x a).1 i‖ ^ 4) + ∑ i, ∑ j, ‖(x a).2 i j‖ ^ 4) γ := fun a =>
    (integrable_finsetSum _ fun i _ => iDc a i).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iAc a i j)
  calc ∫ x, ‖x‖ ^ 4 ∂γ ≤ ∫ x, ∑ a, ((∑ i, ‖(x a).1 i‖ ^ 4) + ∑ i, ∑ j, ‖(x a).2 i j‖ ^ 4) ∂γ :=
        integral_mono (LF1_int_pow D N 4) (integrable_finsetSum _ fun a _ => iS a) hpt
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
private lemma LF1_incr_law (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] (k : ℕ) (hk : k < K) :
    MeasurePreserving (fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩) (gridLawA D N K μ₀)
      (gueBlocks D N) :=
  (measurePreserving_eval (fun _ : Fin K => gueBlocks D N) ⟨k, hk⟩).comp measurePreserving_snd

/-- The increment `X_{k+1}` is `𝓕_{k+1}`-measurable. -/
private lemma LF1_incr_meas (D N K k : ℕ) (hk : k < K) :
    Measurable[gridFiltrA D N K (k + 1)] fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩ := by
  have e : (fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩) = (fun u : GridΩA D N K => u.2 ⟨k, hk⟩) ∘
      (fun ω : GridΩA D N K =>
        (ω.1, fun j : Fin K => if (j : ℕ) < k + 1 then ω.2 j else 0)) := by
    funext ω
    simp
  rw [e]
  exact ((measurable_pi_apply _).comp measurable_snd).comp (comap_measurable _)

/-- The generating map of `𝓕_k`: the initial array and the increments `X_{j+1}`, `j < k`. -/
private def LF1_mask (D N K k : ℕ) (ω : GridΩA D N K) : GridΩA D N K :=
  (ω.1, fun j : Fin K => if (j : ℕ) < k then ω.2 j else 0)

private lemma LF1_mask_measurable (D N K k : ℕ) : Measurable (LF1_mask D N K k) := by
  unfold LF1_mask
  refine measurable_fst.prodMk (measurable_pi_iff.mpr fun j => ?_)
  by_cases hj : (j : ℕ) < k
  · simp only [hj, ↓reduceIte]
    fun_prop
  · simp [hj]

/-- `H_j` depends only on the generating map of `𝓕_k`, `j ≤ k`. -/
private lemma LF1_state_mask (D N K : ℕ) (h : ℝ) (k : ℕ) (ω : GridΩA D N K) :
    ∀ j, j ≤ k → gridStateA D N K h (LF1_mask D N K k ω) j = gridStateA D N K h ω j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    simp only [gridStateA, h1]
    congr 2
    by_cases hjK : j < K
    · simp only [hjK, ↓reduceDIte, LF1_mask]
      have : j < k := by omega
      simp [this]
    · simp [hjK]

/-- Every grid state is measurable. -/
private lemma LF1_state_meas (D N K : ℕ) (h : ℝ) (k : ℕ) :
    Measurable fun ω : GridΩA D N K => gridStateA D N K h ω k :=
  (gridStateA_adapted D N K h k).mono ((gridFiltrA_mono D N K).2 k) le_rfl

/-- The one-step conditional expectation of `Γ(H_k, X_{k+1})` integrates out `X_{k+1}`, for a
measurable `Γ` with `|Γ(H, x)| ≤ C (1 + ‖x‖)`. -/
private lemma LF1_condExp (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
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
  have hmV : μ.map V = γ := (LF1_incr_law D N K μ₀ k hk).map_eq
  have hind : ProbabilityTheory.IndepFun (LF1_mask D N K k) V μ :=
    (ProbabilityTheory.IndepFun_iff_Indep _ _ _).2 (gridIncrA_indep D N K μ₀ k hk)
  have hC0 : 0 ≤ C := by
    have := hC (0, 0)
    have h2 : 0 ≤ C * (1 + ‖((0 : Idx D N → Idx D N → ℂ), (0 : Fin D → Coords N)).2‖) :=
      (abs_nonneg _).trans this
    simp at h2
    exact h2
  have hi1 : Integrable (fun x : Fin D → Coords N => ‖x‖) (gueBlocks D N) := by
    have h1 := LF1_int_pow D N 1
    simp only [pow_one] at h1
    exact h1
  have hint1 : Integrable (fun x : Fin D → Coords N => C * (1 + ‖x‖)) γ :=
    ((integrable_const 1).add hi1).const_mul C
  have hHk := LF1_state_meas D N K h k
  have hf : Integrable (fun ω => Γ (gridStateA D N K h ω k, V ω)) μ := by
    refine Integrable.mono' ((LF1_incr_law D N K μ₀ k hk).integrable_comp_of_integrable hint1)
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
  set A := LF1_mask D N K k with hA
  have hAm : Measurable A := LF1_mask_measurable D N K k
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
    (LF1_state_mask D N K h k ω k le_rfl).symm
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
private def LF1_arrLin (D N : ℕ) : (Fin D → Coords N) →ₗ[ℝ] (Idx D N → Idx D N → ℂ) where
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
private def LF1_arrL (D N : ℕ) : (Fin D → Coords N) →L[ℝ] (Idx D N → Idx D N → ℂ) :=
  LinearMap.toContinuousLinearMap (LF1_arrLin D N)

private lemma LF1_arrL_apply (D N : ℕ) (w : Fin D → Coords N) :
    LF1_arrL D N w = Matrix.of.symm (blockH D N w) := rfl

/-- An entry of `wig n c` is bounded by the sup norm of the coordinates `c`. -/
private lemma LF1_wig_norm_le (n : ℕ) (c : Coords n) (i j : Fin n) : ‖wig n c i j‖ ≤ ‖c‖ := by
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
private lemma LF1_arr_norm_le (D N : ℕ) (w : Fin D → Coords N) :
    ‖Matrix.of.symm (blockH D N w)‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun p =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun q => ?_
  simp only [blockH, Matrix.of_symm_apply]
  split_ifs
  · exact (LF1_wig_norm_le N (w p.1) p.2 q.2).trans (norm_le_pi_norm w p.1)
  · simp

/-- Taylor's formula of order `n` with the remainder bounded by `B ‖y‖^{n+1}`. -/
private lemma LF1_taylor {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
private lemma LF1_taylor1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℂ)
    (hf : ContDiff ℝ 2 f) (B : ℝ) (hB : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ B) (x y : E) :
    ‖f (x + y) - f x - fderiv ℝ f x y‖ ≤ B * ‖y‖ ^ 2 := by
  have h := LF1_taylor f 1 hf B hB x y
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, one_smul, iteratedFDeriv_zero_apply,
    iteratedFDeriv_one_apply] at h
  have e : f (x + y) - f x - fderiv ℝ f x y = f (x + y) - (f x + fderiv ℝ f x y) := by ring
  rw [e]
  simpa using h

/-- The time difference `F(r₂, ·) - F(r₁, ·)` is `B |r₂ - r₁|`-Lipschitz when `∂_s F` is
`C¹` in the array with `‖D ∂_s F‖ ≤ B`. -/
private lemma LF1_tdiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
private lemma LF1_inv_meas {ι : Type*} [Fintype ι] [DecidableEq ι] :
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
private lemma LF1_res_meas {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (w : ℂ) :
    Measurable fun H : Idx D N → Idx D N → ℂ => res (Matrix.of H + Λ) w := by
  unfold res
  have : Continuous fun H : Idx D N → Idx D N → ℂ =>
      Matrix.of H + Λ - w • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
    have : Continuous fun H : Idx D N → Idx D N → ℂ => (Matrix.of H : Matrix _ _ ℂ) :=
      continuous_id
    fun_prop
  exact LF1_inv_meas.comp this.measurable

/-- `G ↦ ⟨Π G^{b_i} B_i⟩` is continuous. -/
private lemma LF1_resProd_cont {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} (b : Fin p → Bool)
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
private lemma LF1_good_meas {D N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' s : ℝ) :
    MeasurableSet {H : Idx D N → Idx D N → ℂ | flowGoodAt A z τ' s H} := by
  have hG := LF1_res_meas (D := D) (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
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
    exact (LF1_resProd_cont b _).norm.measurable.comp hG
  · simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    exact measurableSet_le (by fun_prop) measurable_const

/-- The Hermitian arrays form a measurable set. -/
private lemma LF1_herm_meas {ι : Type*} [Fintype ι] :
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
private def LF1_bad {D N K : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' h : ℝ)
    (ω : GridΩA D N K) (j : ℕ) : Prop :=
  j ≤ K ∧ ¬ ((Matrix.of (gridStateA D N K h ω j)).IsHermitian ∧
    flowGoodAt A z τ' (j * h) (gridStateA D N K h ω j))

/-- The first bad grid time, `⊤` if there is none. -/
private def LF1_sig {D N K : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' h : ℝ)
    (ω : GridΩA D N K) : WithTop ℕ :=
  if hex : ∃ j, LF1_bad A z τ' h ω j then ((Nat.find hex : ℕ) : WithTop ℕ) else ⊤

/-- `k < σ` iff no grid time `j ≤ k` is bad. -/
private lemma LF1_sig_lt {D N K : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' h : ℝ)
    (ω : GridΩA D N K) (k : ℕ) :
    (k : WithTop ℕ) < LF1_sig A z τ' h ω ↔ ∀ j, j ≤ k → ¬ LF1_bad A z τ' h ω j := by
  unfold LF1_sig
  split_ifs with hex
  · rw [show ((k : ℕ) : WithTop ℕ) < ((Nat.find hex : ℕ) : WithTop ℕ) ↔ k < Nat.find hex by
      norm_cast, Nat.lt_find_iff]
  · push Not at hex
    refine ⟨fun _ j _ => hex j, fun _ => ?_⟩
    rw [Nat.cast_withTop]
    exact WithTop.coe_lt_top k

/-- The first bad grid time is a stopping time. -/
private lemma LF1_sig_stop (D N K : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' h : ℝ) :
    IsStoppingTime (gridFiltrationA D N K) (LF1_sig (D := D) (N := N) (K := K) A z τ' h) := by
  intro i
  have e : {ω : GridΩA D N K | LF1_sig A z τ' h ω ≤ WithTop.some i} =
      ⋃ j ∈ Finset.range (i + 1), {ω | LF1_bad A z τ' h ω j} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    rw [← not_lt, ← Nat.cast_withTop, LF1_sig_lt]
    push Not
    exact ⟨fun ⟨j, hj, hb⟩ => ⟨j, by omega, hb⟩, fun ⟨j, hj, hb⟩ => ⟨j, by omega, hb⟩⟩
  rw [e]
  refine Finset.measurableSet_biUnion _ fun j hj => ?_
  have hji : j ≤ i := by have := Finset.mem_range.1 hj; omega
  have hP : MeasurableSet {H : Idx D N → Idx D N → ℂ |
      (Matrix.of H).IsHermitian ∧ flowGoodAt A z τ' (j * h) H} :=
    LF1_herm_meas.inter (LF1_good_meas A z τ' (j * h))
  have hm : Measurable[gridFiltrA D N K j] fun ω : GridΩA D N K => gridStateA D N K h ω j :=
    gridStateA_adapted D N K h j
  by_cases hjK : j ≤ K
  · have e2 : {ω : GridΩA D N K | LF1_bad A z τ' h ω j} =
        (fun ω => gridStateA D N K h ω j) ⁻¹' {H : Idx D N → Idx D N → ℂ |
          (Matrix.of H).IsHermitian ∧ flowGoodAt A z τ' (j * h) H}ᶜ := by
      ext ω
      simp [LF1_bad, hjK]
    rw [e2]
    exact (gridFiltrA_mono D N K).1 hji _ (hm hP.compl)
  · have e2 : {ω : GridΩA D N K | LF1_bad A z τ' h ω j} = ∅ := by
      ext ω
      simp [LF1_bad, hjK]
    rw [e2]
    exact @MeasurableSet.empty _ ((gridFiltrationA D N K) i)

/-! ### The quadratic variation on the good event: (3.56) [eq:quad_var], (3.57)
[eq:quad_integrand] -/

/-- `(G^b)^* = G^{¬b}`. -/
private lemma LF1_pw_conj {ι : Type*} (G : Matrix ι ι ℂ) (b : Bool) :
    (LF1_pw G b)ᴴ = LF1_pw G (!b) := by
  cases b <;> simp [LF1_pw]

/-- The six-resolvent word as `resProd`. -/
private lemma LF1_word6 {D N : ℕ} (G : Matrix (Idx D N) (Idx D N) ℂ) (c : Fin 6 → Bool)
    (a : Fin 6 → Fin D) :
    LF1_pw G (c 0) * Ea D N (a 0) * LF1_pw G (c 1) * Ea D N (a 1) * LF1_pw G (c 2) *
        Ea D N (a 2) * LF1_pw G (c 3) * Ea D N (a 3) * LF1_pw G (c 4) * Ea D N (a 4) *
        LF1_pw G (c 5) * Ea D N (a 5) =
      resProd (fun _ : Fin 6 => G) c (fun i => Ea D N (a i)) := by
  simp only [resProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.mul_one, Matrix.mul_assoc, LF1_pw]
  rfl

/-- The six-resolvent loops of (3.57) [eq:quad_integrand]: for
`W = G₁ E_x G₂ E_y G₁ + G₂ E_y G₁ E_x G₂` with `G_i = G^{b_i}`, `|⟨W E_a W^* E_a⟩|` is at most four
times a bound on the words of six resolvents. -/
private lemma LF1_quad_abs {D N : ℕ} (G : Matrix (Idx D N) (Idx D N) ℂ) (b₁ b₂ : Bool)
    (x y a : Fin D) (β : ℝ)
    (hβ : ∀ (c : Fin 6 → Bool) (e : Fin 6 → Fin D),
      ‖ntr (resProd (fun _ : Fin 6 => G) c (fun i => Ea D N (e i)))‖ ≤ β) :
    ‖ntr ((LF1_pw G b₁ * Ea D N x * LF1_pw G b₂ * Ea D N y * LF1_pw G b₁ +
        LF1_pw G b₂ * Ea D N y * LF1_pw G b₁ * Ea D N x * LF1_pw G b₂) * Ea D N a *
      (LF1_pw G b₁ * Ea D N x * LF1_pw G b₂ * Ea D N y * LF1_pw G b₁ +
        LF1_pw G b₂ * Ea D N y * LF1_pw G b₁ * Ea D N x * LF1_pw G b₂)ᴴ * Ea D N a)‖ ≤
      4 * β := by
  have hE : ∀ c : Fin D, (Ea D N c)ᴴ = Ea D N c := LF1_Ea_conj D N
  set E := Ea D N
  set g := LF1_pw G
  have hW : ∀ (u v : Bool) (p r : Fin D),
      (g u * E p * g v * E r * g u)ᴴ = g (!u) * E r * g (!v) * E p * g (!u) := by
    intro u v p r
    simp only [Matrix.conjTranspose_mul, hE, g, LF1_pw_conj, Matrix.mul_assoc]
  have hexp : (g b₁ * E x * g b₂ * E y * g b₁ + g b₂ * E y * g b₁ * E x * g b₂) * E a *
      (g b₁ * E x * g b₂ * E y * g b₁ + g b₂ * E y * g b₁ * E x * g b₂)ᴴ * E a =
      (g b₁ * E x * g b₂ * E y * g b₁ * E a * g (!b₁) * E y * g (!b₂) * E x * g (!b₁) * E a +
        g b₁ * E x * g b₂ * E y * g b₁ * E a * g (!b₂) * E x * g (!b₁) * E y * g (!b₂) * E a) +
      (g b₂ * E y * g b₁ * E x * g b₂ * E a * g (!b₁) * E y * g (!b₂) * E x * g (!b₁) * E a +
        g b₂ * E y * g b₁ * E x * g b₂ * E a * g (!b₂) * E x * g (!b₁) * E y * g (!b₂) * E a) := by
    rw [Matrix.conjTranspose_add, hW, hW]
    noncomm_ring
  have hw : ∀ (c₀ c₁ c₂ c₃ c₄ c₅ : Bool) (e₀ e₁ e₂ e₃ e₄ e₅ : Fin D),
      ‖ntr (g c₀ * E e₀ * g c₁ * E e₁ * g c₂ * E e₂ * g c₃ * E e₃ *
        g c₄ * E e₄ * g c₅ * E e₅)‖ ≤ β := by
    intro c₀ c₁ c₂ c₃ c₄ c₅ e₀ e₁ e₂ e₃ e₄ e₅
    have h1 := hβ ![c₀, c₁, c₂, c₃, c₄, c₅] ![e₀, e₁, e₂, e₃, e₄, e₅]
    rw [← LF1_word6] at h1
    exact h1
  rw [hexp]
  have t1 := hw b₁ b₂ b₁ (!b₁) (!b₂) (!b₁) x y a y x a
  have t2 := hw b₁ b₂ b₁ (!b₂) (!b₁) (!b₂) x y a x y a
  have t3 := hw b₂ b₁ b₂ (!b₁) (!b₂) (!b₁) y x a y x a
  have t4 := hw b₂ b₁ b₂ (!b₂) (!b₁) (!b₂) y x a x y a
  have hadd : ∀ M₁ M₂ : Matrix (Idx D N) (Idx D N) ℂ, ntr (M₁ + M₂) = ntr M₁ + ntr M₂ := by
    intro M₁ M₂; simp [ntr, Matrix.trace_add, mul_add]
  rw [hadd, hadd, hadd]
  calc _ ≤ (‖ntr _‖ + ‖ntr _‖) + (‖ntr _‖ + ‖ntr _‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ (β + β) + (β + β) := add_le_add (add_le_add t1 t2) (add_le_add t3 t4)
    _ = 4 * β := by ring

/-- The Hermitian part of an array is Hermitian. -/
private lemma LF1_hermPart_herm {ι : Type*} (H : ι → ι → ℂ) :
    (Matrix.of (hermPart H)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [Matrix.of_apply, hermPart, star_div₀, star_add, star_star, star_ofNat]
  ring

/-- `|⟨E_y G₁ E_x G₂⟩| ≤ η_r⁻²` at every array, on `[0, S]`. -/
private lemma LF1_f_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (r : ℝ) (hr : r < flowTc (lam D N A) z) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (x y : Fin D)
    (H : Idx D N → Idx D N → ℂ) :
    ‖flowLoop (lam D N A) (LF1_l z₁ z₂ x y) r H‖ ≤ ((charFlowZ (lam D N A) z r).im ^ 2)⁻¹ := by
  have h1 := LF1_L_le D N hD hN A z hz r hr (hermPart H) (LF1_hermPart_herm H) z₁ z₂ h₁ h₂ x y
  rw [LF1_Lmat_loop, norm_mul, Complex.norm_natCast] at h1
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_eq_mul_inv] at h1
  exact le_of_mul_le_mul_left h1 hD0

/-- The grid states of a Hermitian start are Hermitian. -/
private lemma LF1_states_herm (D N K : ℕ) (h : ℝ) (ω : GridΩA D N K)
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
      exact LF1_state_herm _ _ _ ih _
    · have e : gridStateA D N K h ω (k + 1) = Real.exp (-h / 2) • gridStateA D N K h ω k := by
        simp [gridStateA, hk]
      rw [e]
      have : Matrix.of (Real.exp (-h / 2) • gridStateA D N K h ω k) =
          ((Real.exp (-h / 2) : ℝ) : ℂ) • Matrix.of (gridStateA D N K h ω k) := by
        ext i j; simp [Complex.real_smul]
      rw [this]
      exact LF1_herm_smul _ ih _

/-- The cut-open loop `W` of `loop_quadVar` for a loop of two resolvents. -/
private lemma LF1_W2 {D N : ℕ} (H : Idx D N → Idx D N → ℂ)
    (f₀ f₁ : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ) :
    (∑ i : Fin [f₀, f₁].length, res (Matrix.of H + ([f₀, f₁].get i).2.1) ([f₀, f₁].get i).2.2 *
      chainB H ([f₀, f₁].rotate (i + 1))) =
      res (Matrix.of H + f₀.2.1) f₀.2.2 * chainB H [f₁, f₀] +
        res (Matrix.of H + f₁.2.1) f₁.2.2 * chainB H [f₀, f₁] := by
  change ∑ i : Fin 2, _ = _
  rw [Fin.sum_univ_two]
  simp [List.rotate]

/-- The quadratic variation (3.56) [eq:quad_var] on the good event, with (3.57)
[eq:quad_integrand] and (A.53) [entprodG] for six resolvents:
`E_X |D⟨E_y G₁ E_x G₂⟩[X]|² ≤ 4 N^{τ'} Im m_r / (N² η_r⁵)`. -/
private lemma LF1_var (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (r : ℝ) (hr : r < flowTc (lam D N A) z) (τ' : ℝ)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian)
    (hgood : flowGoodAt A z τ' r H) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (x y : Fin D) :
    ∫ w, ‖fderiv ℝ (flowLoop (lam D N A) (LF1_l z₁ z₂ x y) r) H
        (Matrix.of.symm (blockH D N w))‖ ^ 2 ∂(gueBlocks D N) ≤
      4 * ((N : ℝ) ^ τ' * (flowIm (lam D N A) z r / (charFlowZ (lam D N A) z r).im ^ 5)) /
        (N : ℝ) ^ 2 := by
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hΛ := lam_isHermitian D N A
  set Λs := ((Real.exp (-r / 2) : ℝ) : ℂ) • lam D N A with hΛs
  have hΛsH : Λs.IsHermitian := LF1_herm_smul _ hΛ _
  have him : ∀ zi : ℂ, (zi = z ∨ zi = star z) → (charFlowZ (lam D N A) zi r).im ≠ 0 := by
    have hη := (charFlow_M _ hΛ z hz r hr).1
    rintro zi (rfl | rfl)
    · exact hη.ne'
    · rw [charFlowZ_conj _ z hz r]; simpa using hη.ne'
  have hl : ∀ f ∈ [(Ea D N y, Λs, charFlowZ (lam D N A) z₁ r),
      (Ea D N x, Λs, charFlowZ (lam D N A) z₂ r)], f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨hΛsH, him z₁ h₁⟩
    · exact ⟨hΛsH, him z₂ h₂⟩
  have hq := loop_quadVar _ hl H hH
  simp only at hq
  have hfl : flowLoop (lam D N A) (LF1_l z₁ z₂ x y) r = fun h => ntr (chainB (hermPart h)
      [(Ea D N y, Λs, charFlowZ (lam D N A) z₁ r), (Ea D N x, Λs, charFlowZ (lam D N A) z₂ r)]) :=
    rfl
  rw [hfl, hq, LF1_W2]
  obtain ⟨b₁, hG₁, -⟩ := LF1_flag hD1 hN1 A z hz r hr H hH z₁ h₁
  obtain ⟨b₂, hG₂, -⟩ := LF1_flag hD1 hN1 A z hz r hr H hH z₂ h₂
  set G := res (Matrix.of H + Λs) (charFlowZ (lam D N A) z r) with hG
  have hW : res (Matrix.of H + Λs) (charFlowZ (lam D N A) z₁ r) *
        chainB H [(Ea D N x, Λs, charFlowZ (lam D N A) z₂ r),
          (Ea D N y, Λs, charFlowZ (lam D N A) z₁ r)] +
      res (Matrix.of H + Λs) (charFlowZ (lam D N A) z₂ r) *
        chainB H [(Ea D N y, Λs, charFlowZ (lam D N A) z₁ r),
          (Ea D N x, Λs, charFlowZ (lam D N A) z₂ r)] =
      LF1_pw G b₁ * Ea D N x * LF1_pw G b₂ * Ea D N y * LF1_pw G b₁ +
        LF1_pw G b₂ * Ea D N y * LF1_pw G b₁ * Ea D N x * LF1_pw G b₂ := by
    simp only [chainB, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Matrix.mul_one]
    rw [hG₁, hG₂]
    simp only [Matrix.mul_assoc]
  rw [hW]
  have hβ : ∀ (c : Fin 6 → Bool) (e : Fin 6 → Fin D),
      ‖ntr (resProd (fun _ : Fin 6 => G) c (fun i => Ea D N (e i)))‖ ≤
        (N : ℝ) ^ τ' * (flowIm (lam D N A) z r / (charFlowZ (lam D N A) z r).im ^ 5) := by
    intro c e
    have h6 := hgood.2.1 6 (by norm_num) (by norm_num) c e
    rwa [LF1_bndA4 6 (by norm_num)] at h6
  have hterm : ∀ a : Fin D,
      (ntr ((LF1_pw G b₁ * Ea D N x * LF1_pw G b₂ * Ea D N y * LF1_pw G b₁ +
        LF1_pw G b₂ * Ea D N y * LF1_pw G b₁ * Ea D N x * LF1_pw G b₂) * Ea D N a *
      (LF1_pw G b₁ * Ea D N x * LF1_pw G b₂ * Ea D N y * LF1_pw G b₁ +
        LF1_pw G b₂ * Ea D N y * LF1_pw G b₁ * Ea D N x * LF1_pw G b₂)ᴴ * Ea D N a)).re ≤
      4 * ((N : ℝ) ^ τ' * (flowIm (lam D N A) z r / (charFlowZ (lam D N A) z r).im ^ 5)) :=
    fun a => (Complex.re_le_norm _).trans (LF1_quad_abs G b₁ b₂ x y a _ hβ)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  calc ((D : ℝ) * N ^ 2)⁻¹ * ∑ a, (ntr (_ * Ea D N a * _ * Ea D N a)).re
      ≤ ((D : ℝ) * N ^ 2)⁻¹ * ∑ _a : Fin D,
          4 * ((N : ℝ) ^ τ' * (flowIm (lam D N A) z r / (charFlowZ (lam D N A) z r).im ^ 5)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hterm a) (by positivity)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-! ### The second-order part of one step -/

/-- A continuous function with `‖φ x‖ ≤ a + b ‖x‖²` is integrable under the GUE blocks. -/
private lemma LF1_int_of_le {D N : ℕ} {W : Type*} [NormedAddCommGroup W]
    (φ : (Fin D → Coords N) → W) (hφ : Continuous φ) (a b : ℝ)
    (hb : ∀ x, ‖φ x‖ ≤ a + b * ‖x‖ ^ 2) : Integrable φ (gueBlocks D N) :=
  Integrable.mono' ((integrable_const a).add ((LF1_int_pow D N 2).const_mul b))
    hφ.aestronglyMeasurable (ae_of_all _ hb)

/-- The second-order part of one step of the flow: for `‖H‖ ≤ 1`, `0 < h ≤ 1`, `s = √(1 - e^{-h})`,
`Y(x) = e^{-h/2} H + s X(x)`, `f` with `‖Df‖, ‖D²f‖ ≤ B` and `f' - f` that is `B h`-Lipschitz:
`|f'(Y(x)) - E f'(Y) - s Df(H)[X(x)]| ≤ B h (2 + 2 E‖X‖² + E‖X‖ + 2 ‖x‖² + ‖x‖)`. -/
private lemma LF1_second {D N : ℕ} (f f' : (Idx D N → Idx D N → ℂ) → ℂ) (B h Mf : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hf : ContDiff ℝ 2 f) (hf'c : Continuous f')
    (hB1 : ∀ v, ‖fderiv ℝ f v‖ ≤ B) (hB2 : ∀ v, ‖iteratedFDeriv ℝ 2 f v‖ ≤ B)
    (hMf : ∀ v, ‖f v‖ ≤ Mf) (hMf' : ∀ v, ‖f' v‖ ≤ Mf)
    (hg : ∀ Y₁ Y₂, ‖(f' Y₁ - f Y₁) - (f' Y₂ - f Y₂)‖ ≤ B * ‖Y₁ - Y₂‖ * h)
    (H : Idx D N → Idx D N → ℂ) (hH : ‖H‖ ≤ 1) (x : Fin D → Coords N) :
    ‖f' (Real.exp (-h / 2) • H + Real.sqrt (1 - Real.exp (-h)) • LF1_arrL D N x) -
        (∫ x', f' (Real.exp (-h / 2) • H + Real.sqrt (1 - Real.exp (-h)) • LF1_arrL D N x')
          ∂(gueBlocks D N)) -
        (Real.sqrt (1 - Real.exp (-h)) : ℂ) * fderiv ℝ f H (LF1_arrL D N x)‖ ≤
      B * h * (2 + 2 * (∫ x', ‖x'‖ ^ 2 ∂(gueBlocks D N)) + (∫ x', ‖x'‖ ∂(gueBlocks D N)) +
        2 * ‖x‖ ^ 2 + ‖x‖) := by
  set γ := gueBlocks D N with hγ
  set ρ := Real.exp (-h / 2) with hρ
  set s := Real.sqrt (1 - Real.exp (-h)) with hs
  set arr := LF1_arrL D N with harr
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
  have harrn : ∀ w, ‖arr w‖ ≤ ‖w‖ := fun w => LF1_arr_norm_le D N w
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
    have := LF1_taylor1 f hf B hB2 H (Y w - H)
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
  have hTi : Integrable T γ := LF1_int_of_le T hTc (B * h) (B * h * 2) fun w => by
    have := hTb w; nlinarith
  have hGi : Integrable G γ := LF1_int_of_le G hGc (2 * Mf) 0 fun w => by
    have h1 := hMf' (Y w); have h2 := hMf (Y w)
    simp only [zero_mul, add_zero]
    exact (norm_sub_le _ _).trans (by linarith)
  have hdfi : Integrable (fun w => fderiv ℝ f H (arr w)) γ :=
    LF1_int_of_le _ hdfc (B) B fun w => by
      have h1 : ‖fderiv ℝ f H (arr w)‖ ≤ B * ‖w‖ :=
        ((fderiv ℝ f H).le_opNorm _).trans (mul_le_mul (hB1 H) (harrn w) (norm_nonneg _) hB0)
      nlinarith [sq_nonneg (‖w‖ - 1)]
  have hmean : ∫ w, fderiv ℝ f H (arr w) ∂γ = 0 :=
    LF1_gueBlocks_odd D N _ fun w => by simp [map_neg]
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
    have := LF1_int_pow D N 1; simp only [pow_one] at this; exact this
  have hM2 := LF1_int_pow D N 2
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
private lemma LF1_sig_lt_meas (D N K : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' h : ℝ)
    (k : ℕ) :
    MeasurableSet[gridFiltrA D N K k]
      {ω : GridΩA D N K | (k : WithTop ℕ) < LF1_sig A z τ' h ω} := by
  have e : {ω : GridΩA D N K | (k : WithTop ℕ) < LF1_sig A z τ' h ω} =
      ⋂ j ∈ Finset.range (k + 1), {ω | LF1_bad A z τ' h ω j}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff,
      LF1_sig_lt]
    exact ⟨fun h1 j hj => h1 j (by omega), fun h1 j hj => h1 j (by omega)⟩
  rw [e]
  refine Finset.measurableSet_biInter _ fun j hj => ?_
  have hjk : j ≤ k := by have := Finset.mem_range.1 hj; omega
  refine MeasurableSet.compl ?_
  have hP : MeasurableSet {H : Idx D N → Idx D N → ℂ |
      (Matrix.of H).IsHermitian ∧ flowGoodAt A z τ' (j * h) H} :=
    LF1_herm_meas.inter (LF1_good_meas A z τ' (j * h))
  by_cases hjK : j ≤ K
  · have e2 : {ω : GridΩA D N K | LF1_bad A z τ' h ω j} =
        (fun ω => gridStateA D N K h ω j) ⁻¹' {H : Idx D N → Idx D N → ℂ |
          (Matrix.of H).IsHermitian ∧ flowGoodAt A z τ' (j * h) H}ᶜ := by
      ext ω
      simp [LF1_bad, hjK]
    rw [e2]
    exact (gridFiltrA_mono D N K).1 hjk _ (gridStateA_adapted D N K h j hP.compl)
  · have e2 : {ω : GridΩA D N K | LF1_bad A z τ' h ω j} = ∅ := by
      ext ω
      simp [LF1_bad, hjK]
    rw [e2]
    exact @MeasurableSet.empty _ (gridFiltrA D N K k)

/-- `ℓ(c w) = c ℓ(w)` for a real-linear `ℓ` and real `c`. -/
private lemma LF1_ell_mul (ℓ : ℂ →L[ℝ] ℝ) (c : ℝ) (w : ℂ) : ℓ ((c : ℂ) * w) = c * ℓ w := by
  rw [← Complex.real_smul, map_smul, smul_eq_mul]

/-- `(c s)² · 4 N^{τ} ι / (N² η⁵) ≤ 4 D² h N^{τ} / (N² q³ ι⁴)` for `0 ≤ c ≤ q D`, `s² ≤ h`,
`q ι ≤ η`. -/
private lemma LF1_ar_var (c s q ι η D h N t : ℝ) (hc0 : 0 ≤ c) (hcq : c ≤ q * D) (hs : s ^ 2 ≤ h)
    (hq : 0 < q) (hι : 0 < ι) (hN : 0 < N) (ht : 0 ≤ t) (hqι : q * ι ≤ η) :
    (c * s) ^ 2 * (4 * (t * (ι / η ^ 5)) / N ^ 2) ≤
      4 * D ^ 2 * h * t / (N ^ 2 * q ^ 3 * ι ^ 4) := by
  have hη : 0 < η := lt_of_lt_of_le (mul_pos hq hι) hqι
  have hD : 0 ≤ q * D := le_trans hc0 hcq
  have h1 : (c * s) ^ 2 ≤ (q * D) ^ 2 * h := by
    rw [mul_pow]
    exact mul_le_mul (pow_le_pow_left₀ hc0 hcq 2) hs (sq_nonneg s) (sq_nonneg _)
  have h2 : ι / η ^ 5 ≤ ι / (q * ι) ^ 5 :=
    div_le_div_of_nonneg_left hι.le (pow_pos (mul_pos hq hι) 5)
      (pow_le_pow_left₀ (mul_pos hq hι).le hqι 5)
  have h3 : 0 ≤ 4 * (t * (ι / η ^ 5)) / N ^ 2 := by positivity
  calc (c * s) ^ 2 * (4 * (t * (ι / η ^ 5)) / N ^ 2)
      ≤ (q * D) ^ 2 * h * (4 * (t * (ι / (q * ι) ^ 5)) / N ^ 2) := by
        refine mul_le_mul h1 ?_ h3 (mul_nonneg (sq_nonneg _) (le_trans (sq_nonneg s) hs))
        gcongr
    _ = 4 * D ^ 2 * h * t / (N ^ 2 * q ^ 3 * ι ^ 4) := by
        field_simp

-- The proof assembles the Azuma and Doob parts of one component in a single declaration.
set_option maxHeartbeats 1600000 in
/-- One real component of the martingale part (3.59) [CIest] on the grid: outside a set of
probability at most `2K e^{-ℓ²/2} + K v / ε²`, for every Hermitian start and every `n ≤ K` at which
the good event has held before `n`, the real part (or the imaginary part) of the `(x, y)` entry of
`Σ_{j<n} q_{j+1} (L_{j+1} - E_j L_{j+1})` is at most `ℓ (Σ_{k<n} c_k)^{1/2} + ε` in absolute
value; `c_k = 4 D² h N^{τ'} / (N² q_k³ (Im m_k)⁴)` from the quadratic variation and `v` bounds the
second moments of the second-order parts. -/
private lemma LF1_comp (D N K : ℕ) [NeZero D] [NeZero N] (hK : 1 ≤ K)
    (μ₀ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ₀]
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ) (hA : opNorm (lam D N A) ≤ 1 / 10)
    (hz : 0 < z.im) (hSpos : 0 < S) (hSt : S < flowTc (lam D N A) z)
    (hq1 : flowTc (lam D N A) z ≤ 1)
    (hηN : ∀ s, 0 ≤ s → s ≤ S → (N : ℝ)⁻¹ < (charFlowZ (lam D N A) z s).im) (τ' : ℝ)
    (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (x y : Fin D)
    (ℓ : ℂ →L[ℝ] ℝ) (hℓ : ∀ w, |ℓ w| ≤ ‖w‖) (Ft : ℝ → (Idx D N → Idx D N → ℂ) → ℂ) (B : ℝ)
    (hder : ∀ s ∈ Set.Icc 0 S, ∀ v, HasDerivWithinAt
      (fun r => flowLoop (lam D N A) (LF1_l z₁ z₂ x y) r v) (Ft s v) (Set.Icc 0 S) s)
    (hreg : ∀ s ∈ Set.Icc 0 S, ContDiff ℝ 4 (flowLoop (lam D N A) (LF1_l z₁ z₂ x y) s) ∧
      ContDiff ℝ 4 (Ft s) ∧ (∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ v,
        ‖iteratedFDeriv ℝ j (flowLoop (lam D N A) (LF1_l z₁ z₂ x y) s) v‖ ≤ B ∧
          ‖iteratedFDeriv ℝ j (Ft s) v‖ ≤ B))
    (lv ε : ℝ) (hlv : 0 < lv) (hε : 0 < ε) :
    ∃ Bad : Set (GridΩA D N K),
      (gridLawA D N K μ₀).real Bad ≤ 2 * K * Real.exp (-lv ^ 2 / 2) +
        K * ((D * B * (S / K)) ^ 2 * (2 * ((3 + 2 * (∫ w, ‖w‖ ^ 2 ∂(gueBlocks D N)) +
          ∫ w, ‖w‖ ∂(gueBlocks D N)) ^ 2 + 9 * ∫ w, ‖w‖ ^ 4 ∂(gueBlocks D N)))) / ε ^ 2 ∧
      ∀ ω ∉ Bad, (Matrix.of ω.1).IsHermitian → ∀ n : ℕ, n ≤ K →
        (∀ j : ℕ, j < n →
          flowGoodAt A z τ' (j * (S / K)) (gridStateA D N K (S / K) ω j)) →
        |∑ j ∈ Finset.range n, ℓ (((flowTc (lam D N A) z - (j + 1) * (S / K) : ℝ) : ℂ) *
          (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) x y -
            ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N)))| ≤
          lv * Real.sqrt (∑ k ∈ Finset.range n,
            (if k < K then 4 * D ^ 2 * (S / K) * (N : ℝ) ^ τ' /
              ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - k * (S / K)) ^ 3 *
                flowIm (lam D N A) z (k * (S / K)) ^ 4) else 1)) + ε := by
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
  set F := flowLoop (lam D N A) (LF1_l z₁ z₂ x y) with hF
  set arr := LF1_arrL D N with harr
  have harrn : ∀ w, ‖arr w‖ ≤ ‖w‖ := fun w => LF1_arr_norm_le D N w
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
  have hFb : ∀ r ∈ Set.Icc 0 S, ∀ v, ‖F r v‖ ≤ (N : ℝ) ^ 2 := by
    intro r hr v
    refine (LF1_f_le D N hD1 hN1 A z hz r (lt_of_le_of_lt hr.2 hSt) z₁ z₂ h₁ h₂ x y v).trans ?_
    have hη := hηN r hr.1 hr.2
    have hηpos : 0 < (charFlowZ (lam D N A) z r).im := lt_trans (inv_pos.2 hNpos) hη
    rw [inv_le_comm₀ (pow_pos hηpos 2) (by positivity), ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hNpos.le) hη.le 2
  -- the weights `q_{k+1} D`
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun k : ℕ => (q₀ - ((k : ℝ) + 1) * h) * D := ⟨_, rfl⟩
  have hc0 : ∀ k, k < K → 0 ≤ c k ∧ c k ≤ D ∧ c k ≤ (q₀ - k * h) * D := by
    intro k hk
    have h1 := (hgrid' k hk).2
    rw [hc]
    refine ⟨mul_nonneg (by linarith) hD0, ?_, ?_⟩
    · have : q₀ - ((k : ℝ) + 1) * h ≤ 1 := by
        have : 0 ≤ ((k : ℝ) + 1) * h := by positivity
        linarith
      nlinarith
    · exact mul_le_mul_of_nonneg_right (by linarith) hD0
  -- the one-step objects
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → (Idx D N → Idx D N → ℂ) → ℂ,
      Φ = fun (k : ℕ) H => ∫ w, F (((k : ℝ) + 1) * h) (ρ • H + s • arr w) ∂γ := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℕ → (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) → ℝ,
      Γ = fun (k : ℕ) p => ℓ ((c k : ℂ) * (F (((k : ℝ) + 1) * h) (ρ • p.1 + s • arr p.2) - Φ k p.1)) -
        c k * s * ℓ (fderiv ℝ (F (k * h)) p.1 (arr p.2)) := ⟨_, rfl⟩
  set σ := LF1_sig (D := D) (N := N) (K := K) A z τ' h with hσ
  obtain ⟨a, ha⟩ : ∃ a : ℕ → GridΩA D N K → (Fin D → Coords N) →L[ℝ] ℝ,
      a = fun k ω => if k < K then
        ((c k * s) • (ℓ.comp (fderiv ℝ (F (k * h)) (gridStateA D N K h ω k)))).comp arr
        else 0 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → GridΩA D N K → ℝ, Y = fun k ω => if hk : k < K then
      (if (k : WithTop ℕ) < σ ω then Γ k (gridStateA D N K h ω k, ω.2 ⟨k, hk⟩) else 0)
      else 0 := ⟨_, rfl⟩
  -- properties of `Φ` and `Γ`
  have hΦb : ∀ k, k < K → ∀ H, ‖Φ k H‖ ≤ (N : ℝ) ^ 2 := by
    intro k hk H
    rw [hΦ]
    have := norm_integral_le_of_norm_le_const (μ := γ)
      (f := fun w => F (((k : ℝ) + 1) * h) (ρ • H + s • arr w)) (C := (N : ℝ) ^ 2)
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
  have hΓglob : ∀ k, k < K → ∀ p, |Γ k p| ≤ (D * (2 * (N : ℝ) ^ 2 + B)) * (1 + ‖p.2‖) := by
    intro k hk p
    obtain ⟨hc0', hcD, -⟩ := hc0 k hk
    obtain ⟨-, hB1, -, -, -⟩ := hFr _ (hgrid k hk.le)
    rw [hΓ]
    refine (abs_sub _ _).trans ?_
    have t1 : |ℓ ((c k : ℂ) * (F (((k : ℝ) + 1) * h) (ρ • p.1 + s • arr p.2) - Φ k p.1))| ≤
        D * (2 * (N : ℝ) ^ 2) := by
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
    have e : (D : ℝ) * (2 * (N : ℝ) ^ 2 + B) * (1 + ‖p.2‖) =
        D * (2 * (N : ℝ) ^ 2) + D * (B * ‖p.2‖) + (D * (2 * (N : ℝ) ^ 2) * ‖p.2‖ + D * B) := by
      ring
    have h3 : 0 ≤ (D : ℝ) * (2 * (N : ℝ) ^ 2) * ‖p.2‖ + D * B := by positivity
    linarith
  have hΓmean : ∀ k, k < K → ∀ H, ∫ w, Γ k (H, w) ∂γ = 0 := by
    intro k hk H
    obtain ⟨hF1, -, -, -, -⟩ := hFr _ (hgrid' k hk)
    have hY1 : Continuous fun w => F (((k : ℝ) + 1) * h) (ρ • H + s • arr w) :=
      hF1.continuous.comp (continuous_const.add (arr.continuous.const_smul s))
    have hi1 : Integrable (fun w => (c k : ℂ) * (F (((k : ℝ) + 1) * h) (ρ • H + s • arr w) -
        Φ k H)) γ :=
      LF1_int_of_le _ (continuous_const.mul (hY1.sub continuous_const))
        (|c k| * (2 * (N : ℝ) ^ 2)) 0 fun w => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, zero_mul, add_zero]
          refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (abs_nonneg _)
          have := hFb _ (hgrid' k hk) (ρ • H + s • arr w)
          have := hΦb k hk H
          linarith
    have hodd : ∫ w, ℓ (fderiv ℝ (F (k * h)) H (arr w)) ∂γ = 0 :=
      LF1_gueBlocks_odd D N _ fun w => by simp [map_neg]
    have hdfi : Integrable (fun w => ℓ (fderiv ℝ (F (k * h)) H (arr w))) γ := by
      obtain ⟨-, hB1, -, -, -⟩ := hFr _ (hgrid k hk.le)
      refine LF1_int_of_le _ (ℓ.continuous.comp ((fderiv ℝ (F (k * h)) H).continuous.comp
        arr.continuous)) B B fun w => ?_
      have h1 : ‖ℓ (fderiv ℝ (F (k * h)) H (arr w))‖ ≤ B * ‖w‖ := by
        rw [Real.norm_eq_abs]
        exact (hℓ _).trans (((fderiv ℝ (F (k * h)) H).le_opNorm _).trans
          (mul_le_mul (hB1 H) (harrn _) (norm_nonneg _) hB0))
      nlinarith [sq_nonneg (‖w‖ - 1), norm_nonneg w]
    have hY1i : Integrable (fun w => F (((k : ℝ) + 1) * h) (ρ • H + s • arr w)) γ :=
      LF1_int_of_le _ hY1 ((N : ℝ) ^ 2) 0 fun w => by
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
      have := LF1_tdiff F Ft S B hder (fun r hr => ⟨(hFr r hr).2.2.2.1, (hFr r hr).2.2.2.2⟩)
        (k * h) (((k : ℝ) + 1) * h) (hgrid k hk.le) (hgrid' k hk) Y₁ Y₂
      have e : |((k : ℝ) + 1) * h - k * h| = h := by
        rw [show ((k : ℝ) + 1) * h - k * h = h by ring, abs_of_pos hh]
      rwa [e] at this
    have h2 := LF1_second (F (k * h)) (F (((k : ℝ) + 1) * h)) B h ((N : ℝ) ^ 2) hh hh1
      (hF0.of_le (by norm_num)) hF1.continuous hB1 hB2 (hFb _ (hgrid k hk.le))
      (hFb _ (hgrid' k hk)) hg H hH w
    have eΓ : Γ k (H, w) = c k * ℓ (F (((k : ℝ) + 1) * h) (ρ • H + s • arr w) - Φ k H -
        (s : ℂ) * fderiv ℝ (F (k * h)) H (arr w)) := by
      rw [hΓ]
      simp only [map_sub, LF1_ell_mul]
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
      ((q₀ - (k + 1) * h : ℝ) : ℂ) *
        (flowLmat (lam D N A) z₁ z₂ ((k + 1) * h) (gridStateA D N K h ω (k + 1)) x y -
          ∫ X, flowLmat (lam D N A) z₁ z₂ ((k + 1) * h)
            (ρ • gridStateA D N K h ω k + s • Matrix.of.symm (blockH D N X)) x y ∂γ) =
      (c k : ℂ) * (F (((k : ℝ) + 1) * h) (gridStateA D N K h ω (k + 1)) -
        Φ k (gridStateA D N K h ω k)) := by
    intro ω hω k hk
    have hφ : ∀ (r : ℝ) (H' : Idx D N → Idx D N → ℂ), (Matrix.of H').IsHermitian →
        flowLmat (lam D N A) z₁ z₂ r H' x y = (D : ℂ) * F r H' := by
      intro r H' hH'
      have := LF1_Lmat_loop (lam D N A) z₁ z₂ x y r H'
      rwa [LF1_hermPart_eq H' hH'] at this
    rw [hφ _ _ (LF1_states_herm D N K h ω hω (k + 1)),
      integral_congr_ae (ae_of_all _ fun X => hφ _ _
        (LF1_state_herm _ _ _ (LF1_states_herm D N K h ω hω k) X)),
      integral_const_mul, hΦ, hc]
    simp only [harr, LF1_arrL_apply]
    push_cast
    ring
  -- the variances `c_k` of the Azuma part
  have hflowk : ∀ k, k < K → 0 < q₀ - k * h ∧ 0 < flowIm (lam D N A) z (k * h) ∧
      (q₀ - k * h) * flowIm (lam D N A) z (k * h) ≤ (charFlowZ (lam D N A) z (k * h)).im := by
    intro k hk
    obtain ⟨-, hιeq, hι0, -, -, -, hqι⟩ := LF1_flow D N hD1 hN1 A hA z hz S hSt (k * h)
      (hgrid k hk.le).1 (hgrid k hk.le).2
    refine ⟨by linarith [(hgrid k hk.le).2], by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0,
      hqι⟩
  obtain ⟨cv, hcv⟩ : ∃ cv : ℕ → ℝ, cv = fun k : ℕ => if k < K then 4 * D ^ 2 * h *
      (N : ℝ) ^ τ' / ((N : ℝ) ^ 2 * (q₀ - k * h) ^ 3 * flowIm (lam D N A) z (k * h) ^ 4)
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
    · have hnb := (LF1_sig_lt A z τ' h ω k).1 hkσ k le_rfl
      have hnb' : (Matrix.of (gridStateA D N K h ω k)).IsHermitian ∧
          flowGoodAt A z τ' (k * h) (gridStateA D N K h ω k) := by
        by_contra hcon
        exact hnb ⟨hk.le, hcon⟩
      obtain ⟨hHk, hgk⟩ := hnb'
      obtain ⟨-, hB1, -, -, -⟩ := hFr _ (hgrid k hk.le)
      have e : ∀ w, a k ω w = c k * s *
          ℓ (fderiv ℝ (F (k * h)) (gridStateA D N K h ω k) (arr w)) := by
        intro w; rw [ha]; simp [hk, smul_eq_mul]
      have hv := LF1_var D N A z hz (k * h) (lt_of_le_of_lt (hgrid k hk.le).2 hSt) τ' _ hHk hgk
        z₁ z₂ h₁ h₂ x y
      have hint : Integrable (fun w => ‖fderiv ℝ (F (k * h)) (gridStateA D N K h ω k)
          (arr w)‖ ^ 2) γ := by
        refine LF1_int_of_le _ ((((fderiv ℝ (F (k * h)) (gridStateA D N K h ω k)).continuous.comp
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
        _ ≤ (c k * s) ^ 2 * (4 * ((N : ℝ) ^ τ' * (flowIm (lam D N A) z (k * h) /
            (charFlowZ (lam D N A) z (k * h)).im ^ 5)) / (N : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hv (sq_nonneg _)
        _ ≤ cv k := by
            rw [hcv]
            simp only [hk, ↓reduceIte]
            exact LF1_ar_var (c k) s (q₀ - k * h) _ _ D h N _ hc0' (by linarith) hs2 hq hι hNpos
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
    · have hnb := (LF1_sig_lt A z τ' h ω k).1 hkσ k le_rfl
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
        (LF1_sig_lt_meas D N K A z τ' h k)) ?_ measurable_const
      exact (hΓm k hk).comp (((gridStateA_adapted D N K h k).mono
        ((gridFiltrA_mono D N K).1 (Nat.le_succ k)) le_rfl).prodMk (LF1_incr_meas D N K k hk))
    · have e : Y k = fun _ => 0 := by rw [hY]; funext ω; simp [hk]
      rw [e]
      exact stronglyMeasurable_const
  have hmF : ∀ k, gridFiltrA D N K k ≤ (inferInstance : MeasurableSpace (GridΩA D N K)) :=
    fun k => (gridFiltrA_mono D N K).2 k
  have hpoly : Integrable (fun w : Fin D → Coords N =>
      (D * B * h) ^ 2 * (2 * (C₀ ^ 2 + 9 * ‖w‖ ^ 4))) γ :=
    ((integrable_const (C₀ ^ 2)).add ((LF1_int_pow D N 4).const_mul 9)).const_mul 2
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
      refine Integrable.mono' ((LF1_incr_law D N K μ₀ k hk).integrable_comp_of_integrable hpoly)
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
        exact (Measurable.ite (LF1_sig_lt_meas D N K A z τ' h k) measurable_const
          measurable_const).stronglyMeasurable
      have hgm : Measurable fun ω : GridΩA D N K => Γ k (gridStateA D N K h ω k, ω.2 ⟨k, hk⟩) :=
        (hΓm k hk).comp ((LF1_state_meas D N K h k).prodMk
          ((measurable_pi_apply _).comp measurable_snd))
      have hlin : Integrable (fun w : Fin D → Coords N =>
          (D * (2 * (N : ℝ) ^ 2 + B)) * (1 + ‖w‖)) γ := by
        have hi1 : Integrable (fun w : Fin D → Coords N => ‖w‖) γ := by
          have := LF1_int_pow D N 1; simp only [pow_one] at this; exact this
        exact ((integrable_const 1).add hi1).const_mul _
      have hgi : Integrable (fun ω : GridΩA D N K =>
          Γ k (gridStateA D N K h ω k, ω.2 ⟨k, hk⟩)) μ :=
        Integrable.mono' ((LF1_incr_law D N K μ₀ k hk).integrable_comp_of_integrable hlin)
          hgm.aestronglyMeasurable (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs]; exact hΓglob k hk _)
      have h1 := condExp_stronglyMeasurable_mul_of_bound (hmF k) hindm hgi 1
        (ae_of_all _ fun ω => by rw [hind]; dsimp only; split_ifs <;> simp)
      have h2 := LF1_condExp D N K μ₀ h k hk (Γ k) (hΓm k hk) _ (hΓglob k hk)
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
      have hmap := integral_map (μ := μ) (LF1_incr_law D N K μ₀ k hk).measurable.aemeasurable
        hgc.aestronglyMeasurable
      rw [(LF1_incr_law D N K μ₀ k hk).map_eq] at hmap
      calc ∫ ω, Y k ω ^ 2 ∂μ ≤ ∫ ω, (D * B * h) ^ 2 *
            (2 * (C₀ ^ 2 + 9 * ‖ω.2 ⟨k, hk⟩‖ ^ 4)) ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
              ((LF1_incr_law D N K μ₀ k hk).integrable_comp_of_integrable hpoly)
              (ae_of_all _ (hYsq k hk))
        _ = ∫ w, (D * B * h) ^ 2 * (2 * (C₀ ^ 2 + 9 * ‖w‖ ^ 4)) ∂γ := hmap.symm
        _ = v := by
            rw [hv, integral_const_mul, integral_const_mul,
              integral_add (integrable_const _) ((LF1_int_pow D N 4).const_mul 9),
              integral_const_mul]
            simp [hM₄, hγ]
    · have e : Y k = fun _ => 0 := by rw [hY]; funext ω; simp [hk]
      rw [e]
      simpa using hv0
  -- Azuma and Doob
  have hAz := gridMartA_max D N K μ₀ a ha_meas σ (LF1_sig_stop D N K A z τ' h) cc hcc0 hcvar
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
        ℓ (((q₀ - (j + 1) * h : ℝ) : ℂ) *
          (flowLmat (lam D N A) z₁ z₂ ((j + 1) * h) (gridStateA D N K h ω (j + 1)) x y -
            ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * h)
              (ρ • gridStateA D N K h ω j + s • Matrix.of.symm (blockH D N X)) x y ∂γ)) =
        (if hk : j < K then (if (j : WithTop ℕ) < σ ω then a j ω (ω.2 ⟨j, hk⟩) else 0)
          else 0) + Y j ω := by
      intro j hj
      have hjn : j < n := Finset.mem_range.1 hj
      have hjK : j < K := lt_of_lt_of_le hjn hn
      have hjσ : (j : WithTop ℕ) < σ ω := (LF1_sig_lt A z τ' h ω j).2 fun i hi hbad =>
        hbad.2 ⟨LF1_states_herm D N K h ω hherm i, hgood i (by omega)⟩
      rw [hpin ω hherm j hjK, hsplit j hjK ω, hY]
      simp only [hjK, hjσ, ↓reduceDIte, ↓reduceIte]
      ring
    have hcv' : ∀ k, (cc k : ℝ) = if k < K then 4 * D ^ 2 * h * (N : ℝ) ^ τ' /
        ((N : ℝ) ^ 2 * (q₀ - k * h) ^ 3 * flowIm (lam D N A) z (k * h) ^ 4) else 1 := by
      intro k
      change cv k = _
      rw [hcv]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    simp only [hcv'] at h1
    calc _ ≤ |∑ k ∈ Finset.range n, (if hk : k < K then
          (if (k : WithTop ℕ) < σ ω then a k ω (ω.2 ⟨k, hk⟩) else 0) else 0)| +
          |∑ k ∈ Finset.range n, Y k ω| := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2.le

/-! ### The martingale part: assembly of the components -/

/-- `‖M‖_HS ≤ Σ_{x,y} (|Re M_{xy}| + |Im M_{xy}|)`. -/
private lemma LF1_hs_le {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) :
    hsNorm M ≤ ∑ x, ∑ y, (|(M x y).re| + |(M x y).im|) := by
  unfold hsNorm
  have h1 : ∑ x, ∑ y, ‖M x y‖ ^ 2 ≤ (∑ x, ∑ y, ‖M x y‖) ^ 2 := by
    calc ∑ x, ∑ y, ‖M x y‖ ^ 2 ≤ ∑ x, (∑ y, ‖M x y‖) ^ 2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_sq_le_sq_sum_of_nonneg fun y _ => norm_nonneg _
      _ ≤ (∑ x, ∑ y, ‖M x y‖) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun x _ =>
          Finset.sum_nonneg fun y _ => norm_nonneg _
  have h0 : 0 ≤ ∑ x, ∑ y, ‖M x y‖ := Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => norm_nonneg _
  calc Real.sqrt (∑ x, ∑ y, ‖M x y‖ ^ 2) ≤ ∑ x, ∑ y, ‖M x y‖ := by
        rw [Real.sqrt_le_left h0]; exact h1
    _ ≤ _ := Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        Complex.norm_le_abs_re_add_abs_im _

/-- The sum of the variances of the Azuma part along the grid: for `n ≤ K`,
`Σ_{k<n} 4 D² h N^{t} / (N² q_k³ (Im m_k)⁴) ≤ 2 e² D² N^{t} / (N² q_n² (Im m_n)⁴)`. -/
private lemma LF1_csum (D N K : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hSt : S < flowTc (lam D N A) z) (hq1 : flowTc (lam D N A) z ≤ 1) (h : ℝ) (hh : 0 < h)
    (hKh : (K : ℝ) * h = S) (t : ℝ) (n : ℕ) (hn : n ≤ K) :
    ∑ k ∈ Finset.range n, (if k < K then 4 * D ^ 2 * h * (N : ℝ) ^ t /
        ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - k * h) ^ 3 *
          flowIm (lam D N A) z (k * h) ^ 4) else 1) ≤
      2 * Real.exp 1 ^ 2 * D ^ 2 * (N : ℝ) ^ t /
        ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - n * h) ^ 2 *
          flowIm (lam D N A) z (n * h) ^ 4) := by
  set q₀ := flowTc (lam D N A) z with hq₀
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hgrid : ∀ k : ℕ, k ≤ K → 0 ≤ (k : ℝ) * h ∧ (k : ℝ) * h ≤ S := fun k hk =>
    ⟨by positivity, by rw [← hKh]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le⟩
  have hι : ∀ k : ℕ, k ≤ K → flowIm (lam D N A) z (k * h) =
      Real.exp (k * h / 2) * (mExt (lam D N A) z).im := fun k hk =>
    (LF1_flow D N hD hN A hA z hz S hSt (k * h) (hgrid k hk).1 (hgrid k hk).2).2.1
  have hι0 : 0 < (mExt (lam D N A) z).im :=
    (LF1_flow D N hD hN A hA z hz S hSt 0 le_rfl (le_trans (by positivity) (hgrid 0
      (Nat.zero_le K)).2)).2.2.1
  set ι₀ := (mExt (lam D N A) z).im with hι₀
  have hS0 : 0 ≤ S := by rw [← hKh]; positivity
  have hqn : 0 < q₀ - n * h := by linarith [(hgrid n hn).2]
  have hnK : (n : ℝ) * h < q₀ := by linarith
  -- each term
  have hterm : ∀ k ∈ Finset.range n, (if k < K then 4 * D ^ 2 * h * (N : ℝ) ^ t /
      ((N : ℝ) ^ 2 * (q₀ - k * h) ^ 3 * flowIm (lam D N A) z (k * h) ^ 4) else 1) ≤
      (4 * D ^ 2 * (N : ℝ) ^ t / ((N : ℝ) ^ 2 * ι₀ ^ 4)) * (h * (q₀ - (0 + k * h)) ^ (-(3 : ℝ))) := by
    intro k hk
    have hkn : k < n := Finset.mem_range.1 hk
    have hkK : k < K := lt_of_lt_of_le hkn hn
    simp only [hkK, ↓reduceIte, zero_add]
    have hqk : 0 < q₀ - k * h := by linarith [(hgrid k hkK.le).2]
    rw [hι k hkK.le]
    have hek : 1 ≤ Real.exp (k * h / 2) := Real.one_le_exp (by positivity)
    have e3 : (q₀ - k * h) ^ (-(3 : ℝ)) = ((q₀ - k * h) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hqk.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e3]
    have hι4 : ι₀ ^ 4 ≤ (Real.exp (k * h / 2) * ι₀) ^ 4 := by
      apply pow_le_pow_left₀ hι0.le
      nlinarith
    have hNt : 0 ≤ (N : ℝ) ^ t := Real.rpow_nonneg hNpos.le _
    rw [div_le_iff₀ (by positivity)]
    have : 4 * D ^ 2 * (N : ℝ) ^ t / ((N : ℝ) ^ 2 * ι₀ ^ 4) * (h * ((q₀ - k * h) ^ 3)⁻¹) *
        ((N : ℝ) ^ 2 * (q₀ - k * h) ^ 3 * (Real.exp (k * h / 2) * ι₀) ^ 4) =
        4 * D ^ 2 * h * (N : ℝ) ^ t * ((Real.exp (k * h / 2) * ι₀) ^ 4 / ι₀ ^ 4) := by
      have hne : q₀ - (k : ℝ) * h ≠ 0 := hqk.ne'
      have hne2 : q₀ - h * (k : ℝ) ≠ 0 := by rw [mul_comm]; exact hne
      have hne' : ι₀ ≠ 0 := hι0.ne'
      field_simp
    rw [this]
    have h1 : 1 ≤ (Real.exp (k * h / 2) * ι₀) ^ 4 / ι₀ ^ 4 := by
      rw [le_div_iff₀ (by positivity), one_mul]; exact hι4
    have h2 : 0 ≤ 4 * (D : ℝ) ^ 2 * h * (N : ℝ) ^ t := by positivity
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hR := riemann_rpow_le 0 h q₀ 3 hh (by norm_num) 0 n (Nat.zero_le n)
    (by rw [zero_add]; exact hnK)
  rw [← Finset.range_eq_Ico] at hR
  have e2 : (q₀ - (0 + n * h)) ^ (1 - (3 : ℝ)) / (3 - 1) = ((q₀ - n * h) ^ 2)⁻¹ / 2 := by
    rw [zero_add, show (1 - (3 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hqn.le,
      Real.rpow_natCast]
    norm_num
  rw [e2] at hR
  have hC0 : 0 ≤ 4 * D ^ 2 * (N : ℝ) ^ t / ((N : ℝ) ^ 2 * ι₀ ^ 4) := by
    have := Real.rpow_nonneg hNpos.le t
    positivity
  refine (mul_le_mul_of_nonneg_left hR hC0).trans ?_
  -- `ι₀^{-4} ≤ e² ι_n^{-4}`
  rw [hι n hn]
  have hen : Real.exp (n * h / 2) ^ 4 ≤ Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have : (n : ℝ) * h ≤ 1 := by linarith
    push_cast
    linarith
  have hNt : 0 ≤ (N : ℝ) ^ t := Real.rpow_nonneg hNpos.le _
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have key : (Real.exp (n * h / 2) * ι₀) ^ 4 ≤ Real.exp 1 ^ 2 * ι₀ ^ 4 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right hen (by positivity)
  have hX : 0 ≤ 4 * (D : ℝ) ^ 2 * (N : ℝ) ^ t * ((q₀ - n * h) ^ 2)⁻¹ := by positivity
  calc 4 * (D : ℝ) ^ 2 * (N : ℝ) ^ t * (((q₀ - n * h) ^ 2)⁻¹ / 2) *
        ((N : ℝ) ^ 2 * (q₀ - n * h) ^ 2 * (Real.exp (n * h / 2) * ι₀) ^ 4)
      = 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ t * (N : ℝ) ^ 2 * (Real.exp (n * h / 2) * ι₀) ^ 4 := by
        have hne : q₀ - (n : ℝ) * h ≠ 0 := hqn.ne'
        field_simp
        norm_num
    _ ≤ 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ t * (N : ℝ) ^ 2 * (Real.exp 1 ^ 2 * ι₀ ^ 4) := by
        gcongr
    _ = 2 * Real.exp 1 ^ 2 * D ^ 2 * (N : ℝ) ^ t * ((N : ℝ) ^ 2 * ι₀ ^ 4) := by ring

/-- `C N^a e^{-N^b/2} ≤ 1` for large `N`, `b > 0`. -/
private lemma LF1_tail (a b C : ℝ) (hb : 0 < b) :
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

/-- The threshold of (3.59) [CIest] dominates the sum of the `2D²` real components:
`2 D² (N^{τ'/4} (Σ c)^{1/2} + 1/(4 D² N)) ≤ N^{τ'} / (N q ι²)` when
`Σ c ≤ 2 e² D² N^{τ'/8} / (N² q² ι⁴)`, `q, ι ∈ (0, 1]` and `8 e D³ ≤ N^{11τ'/16}`. -/
private lemma LF1_thr (D N τ' q ι sc : ℝ) (hD : 1 ≤ D) (hN : 1 ≤ N) (hτ' : 0 < τ')
    (hq : 0 < q) (hq1 : q ≤ 1) (hι : 0 < ι) (hι1 : ι ≤ 1) (hsc0 : 0 ≤ sc)
    (hsc : sc ≤ 2 * Real.exp 1 ^ 2 * D ^ 2 * N ^ (τ' / 8) / (N ^ 2 * q ^ 2 * ι ^ 4))
    (hND : 8 * Real.exp 1 * D ^ 3 ≤ N ^ (11 * τ' / 16)) :
    2 * D ^ 2 * (N ^ (τ' / 4) * Real.sqrt sc + 1 / (4 * D ^ 2 * N)) ≤
      N ^ τ' / (N * q * ι ^ 2) := by
  have hNpos : 0 < N := by linarith
  have hDpos : 0 < D := by linarith
  set thr := N ^ τ' / (N * q * ι ^ 2) with hthr
  have hthr0 : 0 < thr := by positivity
  have hN1t : 1 ≤ N ^ τ' := Real.one_le_rpow hN hτ'.le
  -- the Azuma part
  have hA : N ^ (τ' / 4) * Real.sqrt sc ≤ thr / (4 * D ^ 2) := by
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
    have hsq : (8 * Real.exp 1 * D ^ 3) ^ 2 ≤ N ^ (11 * τ' / 8) := by
      rw [← e2]; exact pow_le_pow_left₀ (by positivity) hND 2
    have hpos1 : 0 < N ^ (τ' / 2) := Real.rpow_pos_of_pos hNpos _
    have hpos2 : 0 < N ^ (τ' / 8) := Real.rpow_pos_of_pos hNpos _
    calc N ^ (τ' / 2) * sc ≤ N ^ (τ' / 2) * (2 * Real.exp 1 ^ 2 * D ^ 2 * N ^ (τ' / 8) /
          (N ^ 2 * q ^ 2 * ι ^ 4)) := mul_le_mul_of_nonneg_left hsc hpos1.le
      _ ≤ (thr / (4 * D ^ 2)) ^ 2 := by
          have hY : 0 < N ^ 2 * q ^ 2 * ι ^ 4 := by positivity
          have h32 : 2 * Real.exp 1 ^ 2 * D ^ 2 * (16 * D ^ 4) ≤ N ^ (11 * τ' / 8) := by
            have : 2 * Real.exp 1 ^ 2 * D ^ 2 * (16 * D ^ 4) =
                (8 * Real.exp 1 * D ^ 3) ^ 2 / 2 := by ring
            rw [this]
            have := sq_nonneg (8 * Real.exp 1 * D ^ 3)
            linarith
          have key : N ^ (τ' / 2) * (2 * Real.exp 1 ^ 2 * D ^ 2 * N ^ (τ' / 8)) ≤
              (N ^ τ') ^ 2 / (16 * D ^ 4) := by
            rw [le_div_iff₀ (by positivity), e3]
            have hx : 0 < N ^ (τ' / 2) * N ^ (τ' / 8) := mul_pos hpos1 hpos2
            have : N ^ (τ' / 2) * (2 * Real.exp 1 ^ 2 * D ^ 2 * N ^ (τ' / 8)) * (16 * D ^ 4) =
                (N ^ (τ' / 2) * N ^ (τ' / 8)) * (2 * Real.exp 1 ^ 2 * D ^ 2 * (16 * D ^ 4)) := by
              ring
            rw [this]
            exact mul_le_mul_of_nonneg_left h32 hx.le
          calc N ^ (τ' / 2) * (2 * Real.exp 1 ^ 2 * D ^ 2 * N ^ (τ' / 8) /
                (N ^ 2 * q ^ 2 * ι ^ 4))
              = N ^ (τ' / 2) * (2 * Real.exp 1 ^ 2 * D ^ 2 * N ^ (τ' / 8)) /
                (N ^ 2 * q ^ 2 * ι ^ 4) := by ring
            _ ≤ (N ^ τ') ^ 2 / (16 * D ^ 4) / (N ^ 2 * q ^ 2 * ι ^ 4) :=
                div_le_div_of_nonneg_right key hY.le
            _ = (thr / (4 * D ^ 2)) ^ 2 := by
                rw [hthr]
                field_simp
                ring
  -- the Doob part
  have hB : 1 / (4 * D ^ 2 * N) ≤ thr / (4 * D ^ 2) := by
    rw [hthr, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : q * ι ^ 2 ≤ 1 := by
      have : ι ^ 2 ≤ 1 := pow_le_one₀ hι.le hι1
      nlinarith
    have h2 : 0 < 4 * D ^ 2 * N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans hN1t) h2.le]
  calc 2 * D ^ 2 * (N ^ (τ' / 4) * Real.sqrt sc + 1 / (4 * D ^ 2 * N))
      ≤ 2 * D ^ 2 * (thr / (4 * D ^ 2) + thr / (4 * D ^ 2)) := by gcongr
    _ = thr := by field_simp; ring

set_option maxHeartbeats 1000000 in
/-- The failure probability of the martingale part over the `2D²` real components:
`2 D² (2 K e^{-N^{τ'/2}/2} + K v / ε²) ≤ N^{-D'}/2` for `ε = 1/(4 D² N)`, `K ∈ [N^{C_g}, N^{C_g+1}]`,
`C_g ≥ 31 + D'`, `h = S/K`, `S ≤ 1`, and `v = (D B h)² 2 ((3 + 2 M₂ + M₁)² + 9 M₄)` with
`B ≤ c_B N^{12}` and moments `M₁, M₂ ≤ 1 + M₄`, `M₄ ≤ 2 D N² m₄`. -/
private lemma LF1_prob (D N K Cg D' τ' cB m₄ S B M₁ M₂ M₄ : ℝ) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hKlo : N ^ Cg ≤ K) (hKhi : K ≤ N ^ (Cg + 1)) (hD' : 0 < D') (hCg : 31 + D' ≤ Cg)
    (hS0 : 0 < S)
    (hS1 : S ≤ 1) (hB0 : 0 ≤ B) (hB : B ≤ cB * N ^ 12) (hm₄ : 0 ≤ m₄) (hM₁0 : 0 ≤ M₁)
    (hM₂0 : 0 ≤ M₂) (hM₁ : M₁ ≤ 1 + M₄) (hM₂ : M₂ ≤ 1 + M₄) (hM₄0 : 0 ≤ M₄)
    (hM₄ : M₄ ≤ 2 * D * N ^ 2 * m₄)
    (htail : 16 * D ^ 2 * N ^ (Cg + 1 + D') * Real.exp (-(N ^ (τ' / 2)) / 2) ≤ 1)
    (hbig : 256 * D ^ 8 * cB ^ 2 * ((6 + 6 * D * m₄) ^ 2 + 18 * D * m₄) ≤ N) :
    D * D * 2 * (2 * K * Real.exp (-(N ^ (τ' / 4)) ^ 2 / 2) +
      K * ((D * B * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄))) /
        (1 / (4 * D ^ 2 * N)) ^ 2) ≤ N ^ (-D') / 2 := by
  have hNpos : 0 < N := by linarith
  have hD0 : 0 < D := by linarith
  have hNCg : 1 ≤ N ^ Cg := Real.one_le_rpow hN (by linarith)
  have hKpos : 0 < K := by linarith
  have hND' : 0 < N ^ (-D') := Real.rpow_pos_of_pos hNpos _
  -- the Azuma part
  have e1 : (N ^ (τ' / 4)) ^ 2 = N ^ (τ' / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num; ring_nf
  have hA : D * D * 2 * (2 * K * Real.exp (-(N ^ (τ' / 4)) ^ 2 / 2)) ≤ N ^ (-D') / 4 := by
    rw [e1]
    have hsplit : N ^ (Cg + 1 + D') = N ^ (Cg + 1) * N ^ D' := Real.rpow_add hNpos _ _
    have hinv : N ^ D' * N ^ (-D') = 1 := by
      rw [← Real.rpow_add hNpos]; simp
    have hE : 0 < Real.exp (-(N ^ (τ' / 2)) / 2) := Real.exp_pos _
    have h1 : D * D * 2 * (2 * K * Real.exp (-(N ^ (τ' / 2)) / 2)) ≤
        4 * D ^ 2 * N ^ (Cg + 1) * Real.exp (-(N ^ (τ' / 2)) / 2) := by
      have : D * D * 2 * (2 * K * Real.exp (-(N ^ (τ' / 2)) / 2)) =
          4 * D ^ 2 * K * Real.exp (-(N ^ (τ' / 2)) / 2) := by ring
      rw [this]
      gcongr
    refine h1.trans ?_
    rw [hsplit] at htail
    have : 4 * D ^ 2 * N ^ (Cg + 1) * Real.exp (-(N ^ (τ' / 2)) / 2) =
        (16 * D ^ 2 * (N ^ (Cg + 1) * N ^ D') * Real.exp (-(N ^ (τ' / 2)) / 2)) *
          (N ^ (-D') / 4) := by
      have : N ^ (Cg + 1) * N ^ D' * (N ^ (-D') / 4) = N ^ (Cg + 1) / 4 := by
        rw [mul_assoc, ← mul_div_assoc, hinv]; ring
      calc 4 * D ^ 2 * N ^ (Cg + 1) * Real.exp (-(N ^ (τ' / 2)) / 2)
          = 16 * D ^ 2 * (N ^ (Cg + 1) / 4) * Real.exp (-(N ^ (τ' / 2)) / 2) := by ring
        _ = _ := by rw [← this]; ring
    rw [this]
    exact mul_le_of_le_one_left (by positivity) htail
  -- the Doob part
  set cM := (6 + 6 * D * m₄) ^ 2 + 18 * D * m₄ with hcM
  have hC₀ : (3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄ ≤ cM * N ^ 4 := by
    have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
    have hN4 : N ^ 2 ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
    have h1 : 3 + 2 * M₂ + M₁ ≤ (6 + 6 * D * m₄) * N ^ 2 := by
      have : 3 + 2 * M₂ + M₁ ≤ 6 + 3 * M₄ := by linarith
      have h6 : 6 ≤ 6 * N ^ 2 := by linarith
      nlinarith
    have h2 : (3 + 2 * M₂ + M₁) ^ 2 ≤ (6 + 6 * D * m₄) ^ 2 * N ^ 4 := by
      have := pow_le_pow_left₀ (by linarith) h1 2
      calc (3 + 2 * M₂ + M₁) ^ 2 ≤ ((6 + 6 * D * m₄) * N ^ 2) ^ 2 := this
        _ = (6 + 6 * D * m₄) ^ 2 * N ^ 4 := by ring
    have h3 : 9 * M₄ ≤ 18 * D * m₄ * N ^ 4 := by
      have : 9 * M₄ ≤ 18 * D * m₄ * N ^ 2 := by nlinarith
      have : 18 * D * m₄ * N ^ 2 ≤ 18 * D * m₄ * N ^ 4 :=
        mul_le_mul_of_nonneg_left hN4 (by positivity)
      linarith
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
  have hB2 : (D * B * (S / K)) ^ 2 ≤ D ^ 2 * cB ^ 2 * N ^ 24 * (S / K) ^ 2 := by
    rw [mul_pow, mul_pow]
    have : B ^ 2 ≤ cB ^ 2 * N ^ 24 := by
      have := pow_le_pow_left₀ hB0 hB 2
      calc B ^ 2 ≤ (cB * N ^ 12) ^ 2 := this
        _ = cB ^ 2 * N ^ 24 := by ring
    calc D ^ 2 * B ^ 2 * (S / K) ^ 2 ≤ D ^ 2 * (cB ^ 2 * N ^ 24) * (S / K) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (sq_nonneg D))
            (sq_nonneg _)
      _ = _ := by ring
  have hDb : D * D * 2 * (K * ((D * B * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄))) /
      (1 / (4 * D ^ 2 * N)) ^ 2) ≤ N ^ (-D') / 4 := by
    have hε : (1 / (4 * D ^ 2 * N)) ^ 2 = 1 / (16 * D ^ 4 * N ^ 2) := by ring
    rw [hε, div_div_eq_mul_div, div_one]
    have hX : 0 ≤ (3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄ := by positivity
    calc D * D * 2 * (K * ((D * B * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄))) *
          (16 * D ^ 4 * N ^ 2))
        ≤ D * D * 2 * (K * ((D ^ 2 * cB ^ 2 * N ^ 24 * (S / K) ^ 2) * (2 * (cM * N ^ 4))) *
          (16 * D ^ 4 * N ^ 2)) := by gcongr
      _ = 64 * D ^ 8 * cB ^ 2 * cM * (N ^ 30 * (K * (S / K) ^ 2)) := by ring
      _ ≤ 64 * D ^ 8 * cB ^ 2 * cM * (N ^ (30 : ℝ) * N ^ (-Cg)) := by
          rw [show (N ^ (30 : ℕ) : ℝ) = N ^ (30 : ℝ) by norm_cast]
          gcongr
      _ ≤ 64 * D ^ 8 * cB ^ 2 * cM * N ^ (-1 - D') := by gcongr
      _ ≤ N ^ (-D') / 4 := by
          rw [show -1 - D' = -D' + -1 by ring, Real.rpow_add hNpos, Real.rpow_neg_one]
          have : 64 * D ^ 8 * cB ^ 2 * cM * (N ^ (-D') * N⁻¹) =
              (64 * D ^ 8 * cB ^ 2 * cM / N) * N ^ (-D') := by ring
          rw [this]
          have h4 : 64 * D ^ 8 * cB ^ 2 * cM / N ≤ 1 / 4 := by
            rw [div_le_iff₀ hNpos]; linarith
          nlinarith
  calc D * D * 2 * (2 * K * Real.exp (-(N ^ (τ' / 4)) ^ 2 / 2) +
        K * ((D * B * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄))) /
          (1 / (4 * D ^ 2 * N)) ^ 2)
      = D * D * 2 * (2 * K * Real.exp (-(N ^ (τ' / 4)) ^ 2 / 2)) +
        D * D * 2 * (K * ((D * B * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 + 9 * M₄))) /
          (1 / (4 * D ^ 2 * N)) ^ 2) := by ring
    _ ≤ N ^ (-D') / 4 + N ^ (-D') / 4 := add_le_add hA hDb
    _ = N ^ (-D') / 2 := by ring

-- The proof combines the `2D²` components and the failure probabilities in one declaration.
set_option maxHeartbeats 1600000 in
/-- The martingale part (3.59) [CIest] on the grid with failure probability `N^{-D'}/2`, half
the failure probability `N^{-D'}` of (3.59) [CIest]. -/
private lemma LF1_mart_half (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hεg : 0 < εg) (hC₀ : 6 < C₀) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∀ Cg : ℝ, 31 + D' ≤ Cg → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ K : ℕ, (N : ℝ) ^ Cg ≤ K → (K : ℝ) ≤ (N : ℝ) ^ (Cg + 1) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        gridLawA D N K μ₀ {ω | ∃ n : ℕ, n ≤ K ∧
          (∀ j : ℕ, j < n →
            flowGoodAt A z (τ' / 8) (j * (S / K)) (gridStateA D N K (S / K) ω j)) ∧
          (N : ℝ) ^ τ' / (N * (flowTc (lam D N A) z - n * (S / K)) *
              flowIm (lam D N A) z (n * (S / K)) ^ 2) <
            hsNorm (∑ j ∈ Finset.range n,
              ((flowTc (lam D N A) z - (j + 1) * (S / K) : ℝ) : ℂ) •
                (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
                    (gridStateA D N K (S / K) ω (j + 1)) -
                  Matrix.of fun x y => ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
                    (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                      Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
                    ∂(gueBlocks D N)))} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D') / 2) := by
  intro τ' hτ' D' hD' Cg hCg
  obtain ⟨cR, hcR⟩ := flowLoop_regular
  set m₄ := (∫ y, ‖y‖ ^ 4 ∂(gaussianReal 0 1)) + ∫ z, ‖z‖ ^ 4 ∂(cGauss : Measure ℂ) with hm₄
  have hm₄0 : 0 ≤ m₄ := add_nonneg (integral_nonneg fun y => by positivity)
    (integral_nonneg fun z => by positivity)
  set cB := |cR 2| * (2 * (D : ℝ)) ^ 4 * Real.exp 1 * (4 + τ⁻¹) ^ 2 with hcB
  have hev : ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N ∧ 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧
      c * (N : ℝ) ^ (-εg) ≤ 1 ∧ 8 * Real.exp 1 * (D : ℝ) ^ 3 ≤ (N : ℝ) ^ (11 * τ' / 16) ∧
      16 * (D : ℝ) ^ 2 * (N : ℝ) ^ (Cg + 1 + D') * Real.exp (-((N : ℝ) ^ (τ' / 2)) / 2) ≤ 1 ∧
      256 * (D : ℝ) ^ 8 * cB ^ 2 * ((6 + 6 * D * m₄) ^ 2 + 18 * D * m₄) ≤ N := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    have t3 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (11 * τ' / 16)) Filter.atTop
        Filter.atTop := (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
    refine (Filter.eventually_ge_atTop 2).and (((t1.const_mul 2).eventually
      (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and (((t2.const_mul c).eventually
      (Iic_mem_nhds (by simp : c * 0 < 1))).and ((t3.eventually_ge_atTop _).and
      ((LF1_tail _ _ _ (by positivity)).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop _)))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ₀ hμ₀ A z S hadm K hK1 hK2 z₁ z₂ h₁ h₂ => ?_⟩
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
    LF1_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
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
      obtain ⟨-, hιeq, hι, -⟩ := LF1_flow D N hD1 hN1 A hΛ10 z hz 0 hSt 0 le_rfl le_rfl
      rw [hιeq]; exact mul_pos (Real.exp_pos _) hι
    have hempty : {ω : GridΩA D N K | ∃ n : ℕ, n ≤ K ∧
        (∀ j : ℕ, j < n →
          flowGoodAt A z (τ' / 8) (j * (0 / K)) (gridStateA D N K (0 / K) ω j)) ∧
        (N : ℝ) ^ τ' / (N * (flowTc (lam D N A) z - n * (0 / K)) *
            flowIm (lam D N A) z (n * (0 / K)) ^ 2) <
          hsNorm (∑ j ∈ Finset.range n,
            ((flowTc (lam D N A) z - (j + 1) * (0 / K) : ℝ) : ℂ) •
              (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (0 / K))
                  (gridStateA D N K (0 / K) ω (j + 1)) -
                Matrix.of fun x y => ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (0 / K))
                  (Real.exp (-(0 / K) / 2) • gridStateA D N K (0 / K) ω j +
                    Real.sqrt (1 - Real.exp (-(0 / K))) • Matrix.of.symm (blockH D N X)) x y
                  ∂(gueBlocks D N)))} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro n _ _ hlt
      have hzero : ∀ j : ℕ, ((flowTc (lam D N A) z - (j + 1) * (0 / K) : ℝ) : ℂ) •
          (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (0 / K))
              (gridStateA D N K (0 / K) ω (j + 1)) -
            Matrix.of fun x y => ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (0 / K))
              (Real.exp (-(0 / K) / 2) • gridStateA D N K (0 / K) ω j +
                Real.sqrt (1 - Real.exp (-(0 / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N)) = 0 := by
        intro j
        rw [hst, hst]
        have e : (Matrix.of fun x y => ∫ X : Fin D → Coords N, flowLmat (lam D N A) z₁ z₂
            ((j + 1) * (0 / K)) (Real.exp (-(0 / K) / 2) • ω.1 +
              Real.sqrt (1 - Real.exp (-(0 / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N)) = flowLmat (lam D N A) z₁ z₂ ((j + 1) * (0 / K)) ω.1 := by
          ext x y
          simp
        rw [e, sub_self, smul_zero]
      rw [Finset.sum_congr rfl fun j _ => hzero j, Finset.sum_const_zero] at hlt
      have h0 : hsNorm (0 : Matrix (Fin D) (Fin D) ℂ) = 0 := by simp [hsNorm]
      rw [h0] at hlt
      have hq : 0 < flowTc (lam D N A) z - n * (0 / K) := by simp [hq0]
      have := hι0 n
      have : 0 < (N : ℝ) ^ τ' / (N * (flowTc (lam D N A) z - n * (0 / K)) *
          flowIm (lam D N A) z (n * (0 / K)) ^ 2) := by positivity
      linarith
    rw [hempty, measure_empty]
    exact bot_le
  -- the moments of the GUE blocks
  set γ := gueBlocks D N with hγ
  set M₁ := ∫ w, ‖w‖ ∂γ with hM₁
  set M₂ := ∫ w, ‖w‖ ^ 2 ∂γ with hM₂
  set M₄ := ∫ w, ‖w‖ ^ 4 ∂γ with hM₄
  have hi4 := LF1_int_pow D N 4
  have hM₁0 : 0 ≤ M₁ := integral_nonneg fun w => norm_nonneg _
  have hM₂0 : 0 ≤ M₂ := integral_nonneg fun w => by positivity
  have hM₄0 : 0 ≤ M₄ := integral_nonneg fun w => by positivity
  have hM₁4 : M₁ ≤ 1 + M₄ := by
    have hi1 : Integrable (fun w : Fin D → Coords N => ‖w‖) γ := by
      have := LF1_int_pow D N 1; simp only [pow_one] at this; exact this
    calc M₁ ≤ ∫ w, (1 + ‖w‖ ^ 4) ∂γ := integral_mono hi1 ((integrable_const 1).add hi4)
          fun w => by nlinarith [sq_nonneg (‖w‖ - 1), sq_nonneg (‖w‖ ^ 2 - 1), norm_nonneg w]
      _ = 1 + M₄ := by rw [integral_add (integrable_const 1) hi4]; simp [hM₄, hγ]
  have hM₂4 : M₂ ≤ 1 + M₄ := by
    calc M₂ ≤ ∫ w, (1 + ‖w‖ ^ 4) ∂γ := integral_mono (LF1_int_pow D N 2)
          ((integrable_const 1).add hi4)
          fun w => by nlinarith [sq_nonneg (‖w‖ ^ 2 - 1), norm_nonneg w]
      _ = 1 + M₄ := by rw [integral_add (integrable_const 1) hi4]; simp [hM₄, hγ]
  have hM₄m : M₄ ≤ 2 * D * (N : ℝ) ^ 2 * m₄ := by
    refine (LF1_moment4 D N).trans ?_
    have h1 : (D : ℝ) * N ≤ D * N ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have : (D : ℝ) * N + D * N * N ≤ 2 * D * N ^ 2 := by
      calc (D : ℝ) * N + D * N * N = D * N + D * N ^ 2 := by ring
        _ ≤ D * N ^ 2 + D * N ^ 2 := by linarith
        _ = 2 * D * N ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right this hm₄0
  -- the components
  have hhK : (K : ℝ) * (S / K) = S := by field_simp
  have hcomp : ∀ (x y : Fin D) (b : Bool), ∃ Bad : Set (GridΩA D N K),
      (gridLawA D N K μ₀).real Bad ≤ 2 * K * Real.exp (-((N : ℝ) ^ (τ' / 4)) ^ 2 / 2) +
        K * ((D * (cB * (N : ℝ) ^ 12) * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 +
          9 * M₄))) / (1 / (4 * (D : ℝ) ^ 2 * N)) ^ 2 ∧
      ∀ ω ∉ Bad, (Matrix.of ω.1).IsHermitian → ∀ n : ℕ, n ≤ K →
        (∀ j : ℕ, j < n →
          flowGoodAt A z (τ' / 8) (j * (S / K)) (gridStateA D N K (S / K) ω j)) →
        |∑ j ∈ Finset.range n, (if b then Complex.imCLM else Complex.reCLM)
          (((flowTc (lam D N A) z - (j + 1) * (S / K) : ℝ) : ℂ) *
          (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) x y -
            ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N)))| ≤
          (N : ℝ) ^ (τ' / 4) * Real.sqrt (∑ k ∈ Finset.range n,
            (if k < K then 4 * D ^ 2 * (S / K) * (N : ℝ) ^ (τ' / 8) /
              ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - k * (S / K)) ^ 3 *
                flowIm (lam D N A) z (k * (S / K)) ^ 4) else 1)) +
            1 / (4 * (D : ℝ) ^ 2 * N) := by
    intro x y b
    have hlf : ∀ f ∈ LF1_l (N := N) z₁ z₂ x y, f.2 = z ∨ f.2 = star z := by
      intro f hf
      simp only [LF1_l, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      exacts [h₁, h₂]
    obtain ⟨Ft, hder, hreg⟩ := hcR D N (lam D N A) (lam_isHermitian D N A) z hz
      (LF1_l z₁ z₂ x y) hlf S hS0 hSt
    set B := cR (LF1_l (N := N) z₁ z₂ x y).length * ((D : ℝ) * N + 1) ^ 4 *
      Real.exp (flowTc (lam D N A) z) *
      (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
      ((LF1_l (N := N) z₁ z₂ x y).map fun f => opNorm f.1).prod *
      ((min 1 (charFlowZ (lam D N A) z S).im) ^ ((LF1_l (N := N) z₁ z₂ x y).length + 6))⁻¹
      with hB
    have hB0 : 0 ≤ B := (norm_nonneg _).trans
      ((hreg 0 ⟨le_rfl, hS0⟩).2.2.1 1 le_rfl (by norm_num) 0).1
    have hBle : B ≤ cB * (N : ℝ) ^ 12 := by
      have hηS := (hη S hS0 le_rfl).1
      have hBeq : B = cR 2 * ((D : ℝ) * N + 1) ^ 4 * Real.exp (flowTc (lam D N A) z) *
          (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A)) ^ 2 *
          (opNorm (Ea D N y) * opNorm (Ea D N x)) *
          ((min 1 (charFlowZ (lam D N A) z S).im) ^ 8)⁻¹ := by
        rw [hB]
        simp only [LF1_l, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, mul_one]
      rw [hBeq]
      refine (LF1_ar_B (cR 2) D N (Real.exp (flowTc (lam D N A) z))
        (1 + ‖z‖ + 2 * ‖mExt (lam D N A) z‖ + opNorm (lam D N A))
        (opNorm (Ea D N y) * opNorm (Ea D N x)) (min 1 (charFlowZ (lam D N A) z S).im) τ
        hDr (by exact_mod_cast hN2) (Real.exp_le_exp.2 hq1) (Real.exp_pos _).le
        (by have h1 := norm_nonneg z; have h2 := norm_nonneg (mExt (lam D N A) z)
            have h3 := LF1_op_nonneg (lam D N A); linarith only [h1, h2, h3])
        (by linarith only [hzτ, hm1, hΛ10])
        (mul_nonneg (LF1_op_nonneg _) (LF1_op_nonneg _))
        ((mul_le_mul (LF1_opNorm_Ea D N y) (LF1_opNorm_Ea D N x) (LF1_op_nonneg _)
          zero_le_one).trans_eq (one_mul 1))
        (le_min (inv_le_one_of_one_le₀ (by linarith)) hηS.le)).trans (le_of_eq ?_)
      rw [hcB]; ring
    have hℓ : ∀ w : ℂ, |(if b then Complex.imCLM else Complex.reCLM) w| ≤ ‖w‖ := by
      intro w
      cases b
      · simpa using Complex.abs_re_le_norm w
      · simpa using Complex.abs_im_le_norm w
    obtain ⟨Bad, hBadμ, hBad⟩ := LF1_comp D N K hK1' μ₀ A z S hΛ10 hz hSpos hSt hq1
      (fun s hs0 hsS => (hη s hs0 hsS).1) (τ' / 8) z₁ z₂ h₁ h₂ x y _ hℓ Ft B hder
      (fun s hs => ⟨(hreg s hs).1, (hreg s hs).2.1, (hreg s hs).2.2.1⟩)
      ((N : ℝ) ^ (τ' / 4)) (1 / (4 * (D : ℝ) ^ 2 * N)) (Real.rpow_pos_of_pos hNpos _)
      (by positivity)
    refine ⟨Bad, hBadμ.trans ?_, hBad⟩
    gcongr
  choose Bad hBadμ hBad using hcomp
  set PB := 2 * K * Real.exp (-((N : ℝ) ^ (τ' / 4)) ^ 2 / 2) +
    K * ((D * (cB * (N : ℝ) ^ 12) * (S / K)) ^ 2 * (2 * ((3 + 2 * M₂ + M₁) ^ 2 +
      9 * M₄))) / (1 / (4 * (D : ℝ) ^ 2 * N)) ^ 2 with hPB
  have hPBle : (D : ℝ) * D * 2 * PB ≤ (N : ℝ) ^ (-D') / 2 := by
    rw [hPB]
    exact LF1_prob D N K Cg D' τ' cB m₄ S (cB * (N : ℝ) ^ 12) M₁ M₂ M₄ hDr hNr hK1 hK2 hD' hCg
      hSpos (le_trans hSt.le hq1) (by
        have : 0 ≤ cB := by rw [hcB]; positivity
        positivity) le_rfl hm₄0 hM₁0 hM₂0 hM₁4 hM₂4 hM₄0 hM₄m htail hbig
  set NH := {ω : GridΩA D N K | ¬ (Matrix.of ω.1).IsHermitian} with hNH
  have hNH0 : gridLawA D N K μ₀ NH = 0 := by
    have hT : MeasurableSet {H : Idx D N → Idx D N → ℂ | ¬ (Matrix.of H).IsHermitian} :=
      LF1_herm_meas.compl
    have e : NH = Prod.fst ⁻¹' {H : Idx D N → Idx D N → ℂ | ¬ (Matrix.of H).IsHermitian} := rfl
    rw [e, ← Measure.map_apply measurable_fst hT]
    unfold gridLawA
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_iff.1 hμ₀.herm
  -- the event lies in the union of the bad sets of the components and of `NH`
  refine (measure_mono (t := (⋃ p : Fin D × Fin D × Bool, Bad p.1 p.2.1 p.2.2) ∪ NH) ?_).trans
    ?_
  · rintro ω ⟨n, hn, hgood, hlt⟩
    by_contra hω
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, hNH, Set.mem_ofPred_eq,
      not_not] at hω
    obtain ⟨hω1, hherm⟩ := hω
    set T := (N : ℝ) ^ (τ' / 4) * Real.sqrt (∑ k ∈ Finset.range n,
      (if k < K then 4 * D ^ 2 * (S / K) * (N : ℝ) ^ (τ' / 8) /
        ((N : ℝ) ^ 2 * (flowTc (lam D N A) z - k * (S / K)) ^ 3 *
          flowIm (lam D N A) z (k * (S / K)) ^ 4) else 1)) + 1 / (4 * (D : ℝ) ^ 2 * N) with hT
    have hent : ∀ x y : Fin D, (∑ j ∈ Finset.range n,
        ((flowTc (lam D N A) z - (j + 1) * (S / K) : ℝ) : ℂ) •
          (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) -
            Matrix.of fun x y => ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N))) x y =
        ∑ j ∈ Finset.range n, ((flowTc (lam D N A) z - (j + 1) * (S / K) : ℝ) : ℂ) *
          (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) x y -
            ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N)) := by
      intro x y
      simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply]
    have hre : ∀ x y : Fin D, |((∑ j ∈ Finset.range n,
        ((flowTc (lam D N A) z - (j + 1) * (S / K) : ℝ) : ℂ) •
          (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) -
            Matrix.of fun x y => ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N))) x y).re| +
        |((∑ j ∈ Finset.range n,
        ((flowTc (lam D N A) z - (j + 1) * (S / K) : ℝ) : ℂ) •
          (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) -
            Matrix.of fun x y => ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N))) x y).im| ≤ 2 * T := by
      intro x y
      rw [hent x y, Complex.re_sum, Complex.im_sum]
      have h1 := hBad x y false ω (hω1 (x, y, false)) hherm n hn hgood
      have h2 := hBad x y true ω (hω1 (x, y, true)) hherm n hn hgood
      simp only [Bool.false_eq_true, ↓reduceIte, Complex.reCLM_apply,
        Complex.imCLM_apply] at h1 h2
      linarith
    have hhs := LF1_hs_le (∑ j ∈ Finset.range n,
        ((flowTc (lam D N A) z - (j + 1) * (S / K) : ℝ) : ℂ) •
          (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) -
            Matrix.of fun x y => ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N)))
    have hsum : hsNorm (∑ j ∈ Finset.range n,
        ((flowTc (lam D N A) z - (j + 1) * (S / K) : ℝ) : ℂ) •
          (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (gridStateA D N K (S / K) ω (j + 1)) -
            Matrix.of fun x y => ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N))) ≤ 2 * D ^ 2 * T := by
      refine hhs.trans ?_
      calc ∑ x, ∑ y, _ ≤ ∑ _x : Fin D, ∑ _y : Fin D, 2 * T :=
            Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hre x y
        _ = 2 * D ^ 2 * T := by simp; ring
    -- the threshold
    have hnS : (n : ℝ) * (S / K) ≤ S := by
      have hnK : (n : ℝ) ≤ K := by exact_mod_cast hn
      calc (n : ℝ) * (S / K) ≤ K * (S / K) :=
            mul_le_mul_of_nonneg_right hnK (by positivity)
        _ = S := hhK
    obtain ⟨-, hιeq, hι0, hι1, -, -, -⟩ := LF1_flow D N hD1 hN1 A hΛ10 z hz S hSt (n * (S / K))
      (by positivity) hnS
    have hιn : 0 < flowIm (lam D N A) z (n * (S / K)) := by
      rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
    have hcs := LF1_csum D N K hD1 hN1 A hΛ10 z hz S hSt hq1 (S / K) (by positivity) hhK
      (τ' / 8) n hn
    have hthr := LF1_thr D N τ' (flowTc (lam D N A) z - n * (S / K))
      (flowIm (lam D N A) z (n * (S / K))) _ hDr hNr hτ' (by linarith) (by
        have : 0 ≤ (n : ℝ) * (S / K) := by positivity
        linarith) hιn hι1.le (Finset.sum_nonneg fun k _ => by
          split_ifs with hk
          · have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk.le
            have hSK : 0 ≤ S / K := by positivity
            have hkS : (k : ℝ) * (S / K) ≤ S :=
              (mul_le_mul_of_nonneg_right hkK hSK).trans_eq hhK
            have hk00 : 0 ≤ (k : ℝ) * (S / K) := by positivity
            have h1 := (LF1_flow D N hD1 hN1 A hΛ10 z hz S hSt (k * (S / K)) hk00 hkS).2.1
            have hk0 : 0 < flowTc (lam D N A) z - k * (S / K) := by linarith
            have := Real.rpow_nonneg hNpos.le (τ' / 8)
            positivity
          · exact zero_le_one) hcs hND
    linarith
  · refine (measure_union_le _ _).trans ?_
    rw [hNH0, add_zero]
    refine (measure_iUnion_fintype_le _ _).trans ?_
    calc ∑ p : Fin D × Fin D × Bool, gridLawA D N K μ₀ (Bad p.1 p.2.1 p.2.2)
        ≤ ∑ _p : Fin D × Fin D × Bool, ENNReal.ofReal PB := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal (hBadμ p.1 p.2.1 p.2.2)
      _ = ENNReal.ofReal ((D : ℝ) * D * 2 * PB) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
            Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
          rw [ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show ((D : ℝ) * D * 2) = ((D * (D * 2) : ℕ) : ℝ) by push_cast; ring,
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D') / 2) := ENNReal.ofReal_le_ofReal hPBle

/-! ### Tools for the bootstrap of Lemma 3.8 [lem_flow_1] -/

section LF1_Frob

open scoped Matrix.Norms.Frobenius

/-- `‖AB‖_HS ≤ ‖A‖_HS ‖B‖_HS`. -/
private lemma LF1_hs_mul {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) :
    hsNorm (A * B) ≤ hsNorm A * hsNorm B := by
  have h := Matrix.frobenius_norm_mul A B
  have e : ∀ M : Matrix (Fin D) (Fin D) ℂ, ‖M‖ = hsNorm M := fun M => by
    rw [Matrix.frobenius_norm_def, hsNorm, Real.sqrt_eq_rpow]
    congr 1
    simp [Real.rpow_two]
  rw [e, e, e] at h
  exact h

end LF1_Frob

/-- The entries of `M` as a vector of `ℂ^{D×D}` with the Euclidean norm. -/
private def LF1_vec {D : ℕ} : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin D × Fin D) where
  toFun M := WithLp.toLp 2 (fun p => M p.1 p.2)
  map_add' M M' := by ext p; simp
  map_smul' c M := by ext p; simp

/-- The matrix of a vector of `ℂ^{D×D}`. -/
private def LF1_mat {D : ℕ} (v : EuclideanSpace ℂ (Fin D × Fin D)) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j => v (i, j)

private lemma LF1_mat_vec {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) : LF1_mat (LF1_vec M) = M := rfl

private lemma LF1_vec_mat {D : ℕ} (v : EuclideanSpace ℂ (Fin D × Fin D)) :
    LF1_vec (LF1_mat v) = v := rfl

private lemma LF1_mat_add {D : ℕ} (v w : EuclideanSpace ℂ (Fin D × Fin D)) :
    LF1_mat (v + w) = LF1_mat v + LF1_mat w := rfl

private lemma LF1_mat_smul {D : ℕ} (c : ℂ) (v : EuclideanSpace ℂ (Fin D × Fin D)) :
    LF1_mat (c • v) = c • LF1_mat v := rfl

/-- `‖vec M‖ = ‖M‖_HS`. -/
private lemma LF1_norm_vec {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) :
    ‖LF1_vec M‖ = hsNorm M := by
  rw [EuclideanSpace.norm_eq, hsNorm, Fintype.sum_prod_type]
  rfl

/-- `‖v‖ = ‖mat v‖_HS`. -/
private lemma LF1_norm_mat {D : ℕ} (v : EuclideanSpace ℂ (Fin D × Fin D)) :
    ‖v‖ = hsNorm (LF1_mat v) := by
  rw [← LF1_norm_vec, LF1_vec_mat]

/-- The linear map `V ↦ T V` of (3.62) [eq:TtV] on `ℂ^{D×D}`, from a matrix map. -/
private def LF1_op {D : ℕ} (K : Matrix (Fin D) (Fin D) ℂ) (q : ℝ) :
    EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => LF1_vec ((q : ℂ) • (K * LF1_mat v + LF1_mat v * K) -
        ((1 - q : ℝ) : ℂ) • LF1_mat v)
      map_add' := fun v w => by
        simp only [LF1_mat_add, Matrix.mul_add, Matrix.add_mul, smul_add, map_sub, map_add,
          map_smul]
        abel
      map_smul' := fun c v => by
        simp only [LF1_mat_smul, Matrix.mul_smul, Matrix.smul_mul, map_sub, map_add, map_smul,
          RingHom.id_apply, smul_add, smul_sub, smul_comm c] }

private lemma LF1_op_apply {D : ℕ} (K : Matrix (Fin D) (Fin D) ℂ) (q : ℝ)
    (v : EuclideanSpace ℂ (Fin D × Fin D)) :
    LF1_op K q v = LF1_vec ((q : ℂ) • (K * LF1_mat v + LF1_mat v * K) -
      ((1 - q : ℝ) : ℂ) • LF1_mat v) := rfl

/-- The square map `V ↦ V²` on `ℂ^{D×D}`. -/
private def LF1_sq {D : ℕ} (v : EuclideanSpace ℂ (Fin D × Fin D)) :
    EuclideanSpace ℂ (Fin D × Fin D) :=
  LF1_vec (LF1_mat v * LF1_mat v)

private lemma LF1_sq_le {D : ℕ} (v : EuclideanSpace ℂ (Fin D × Fin D)) :
    ‖LF1_sq v‖ ≤ ‖v‖ ^ 2 := by
  rw [LF1_sq, LF1_norm_vec, LF1_norm_mat, sq]
  exact LF1_hs_mul _ _

/-- The identity behind the recursion of the bootstrap: with `W = L - K` and `g q = h`,
`q'(L' - K') - q W - g (T(q W) + (q W)²) = (q' L' - E) + (E - q L - h((q - 1)L + q L²))
- (q' K' - q K - h((q - 1)K + q K²))` for `T V = q (K V + V K) - (1 - q) V`. -/
private lemma LF1_alg_id {R : Type*} [Ring R] [Algebra ℂ R] (L K L' K' E : R) (q q' g : ℂ) :
    q' • (L' - K') - q • (L - K) -
        g • ((q • (K * (q • (L - K)) + (q • (L - K)) * K) - (1 - q) • (q • (L - K))) +
          (q • (L - K)) * (q • (L - K))) =
      (q' • L' - E) + (E - q • L - (g * q) • ((q - 1) • L + q • (L * L))) -
        (q' • K' - q • K - (g * q) • ((q - 1) • K + q • (K * K))) := by
  simp only [smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul, smul_sub, smul_smul, smul_add,
    sub_smul, one_smul]
  module

/-- `η_s ≤ e (t_c - t₀ - s) Im m_s` along the flow on `[0, S]`, `t_c - t₀ ≤ 1`. -/
private lemma LF1_flow_up (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (hq1 : flowTc (lam D N A) z ≤ 1) (s : ℝ) (hs0 : 0 ≤ s)
    (hsS : s ≤ S) :
    (charFlowZ (lam D N A) z s).im ≤
      Real.exp 1 * (flowTc (lam D N A) z - s) * flowIm (lam D N A) z s := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hs : s < flowTc (lam D N A) z := lt_of_le_of_lt hsS hS
  obtain ⟨-, hιeq, hι0, -, -, -, -⟩ := LF1_flow D N hD hN A hA z hz S hS s hs0 hsS
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

/-- The good event is monotone in the loss `N^{τ'}`, for `N ≥ 1` and `η_s, Im m_s > 0`. -/
private lemma LF1_good_mono {D N : ℕ} (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (τ₁ τ₂ s : ℝ) (hτ : τ₁ ≤ τ₂) (H : Idx D N → Idx D N → ℂ)
    (hη : 0 < (charFlowZ (lam D N A) z s).im) (hι : 0 < flowIm (lam D N A) z s)
    (hg : flowGoodAt A z τ₁ s H) : flowGoodAt A z τ₂ s H := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hmono : (N : ℝ) ^ τ₁ ≤ (N : ℝ) ^ τ₂ := Real.rpow_le_rpow_of_exponent_le hNr hτ
  refine ⟨fun a => (hg.1 a).trans ?_, fun p hp1 hp8 b a => (hg.2.1 p hp1 hp8 b a).trans ?_,
    hg.2.2⟩
  · exact div_le_div_of_nonneg_right hmono (by positivity)
  · refine mul_le_mul_of_nonneg_right hmono ?_
    have : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
    unfold bndA4
    simp only [ciSup_const, ciInf_const]
    split_ifs <;> positivity

/-- `‖M‖_HS ≤ Σ_{x,y} |M_{xy}|`. -/
private lemma LF1_hs_le' {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) :
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
private lemma LF1_hs_entry {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) (m : ℝ)
    (hm : ∀ x y, ‖M x y‖ ≤ m) : hsNorm M ≤ D ^ 2 * m := by
  refine (LF1_hs_le' M).trans ?_
  calc ∑ x, ∑ y, ‖M x y‖ ≤ ∑ _x : Fin D, ∑ _y : Fin D, m :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hm x y
    _ = D ^ 2 * m := by simp; ring

/-- `‖Σ_j M_j‖_HS ≤ Σ_j ‖M_j‖_HS` and `‖A + B‖_HS ≤ ‖A‖_HS + ‖B‖_HS`. -/
private lemma LF1_hs_add {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) :
    hsNorm (A + B) ≤ hsNorm A + hsNorm B := by
  rw [← LF1_norm_vec, ← LF1_norm_vec, ← LF1_norm_vec, map_add]
  exact norm_add_le _ _

private lemma LF1_hs_sub {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) :
    hsNorm (A - B) ≤ hsNorm A + hsNorm B := by
  rw [← LF1_norm_vec, ← LF1_norm_vec, ← LF1_norm_vec, map_sub]
  exact norm_sub_le _ _

private lemma LF1_hs_sum {D : ℕ} (n : ℕ) (M : ℕ → Matrix (Fin D) (Fin D) ℂ) :
    hsNorm (∑ j ∈ Finset.range n, M j) ≤ ∑ j ∈ Finset.range n, hsNorm (M j) := by
  rw [← LF1_norm_vec, map_sum]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp only [LF1_norm_vec]

private lemma LF1_hs_smul {D : ℕ} (c : ℂ) (A : Matrix (Fin D) (Fin D) ℂ) :
    hsNorm (c • A) = ‖c‖ * hsNorm A := by
  rw [← LF1_norm_vec, ← LF1_norm_vec, map_smul, norm_smul]

/-- At `s = 0` the flowed objects are the unflowed ones. -/
private lemma LF1_zero {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z z₁ z₂ : ℂ)
    (H : Idx D N → Idx D N → ℂ) :
    flowLmat Λ z₁ z₂ 0 H = Lmat Λ H z₁ z₂ ∧ flowKmat Λ θ z₁ z₂ 0 = KTheta Λ θ z₁ z₂ ∧
      flowIm Λ z 0 = (mExt Λ z).im := by
  have hz : ∀ w : ℂ, charFlowZ Λ w 0 = w := fun w => by simp [charFlowZ]
  have he : ((Real.exp (-0 / 2) : ℝ) : ℂ) • Λ = Λ := by simp
  refine ⟨?_, ?_, ?_⟩
  · simp only [flowLmat, hz, he]
  · simp only [flowKmat, hz, he]
    congr 1
    simp
  · simp only [flowIm, hz, he]

/-- The operator bound (3.67) [Tnorm] along the flow: at `t ∈ [0, S]`,
`‖q_t (K_t V + V K_t) - (1 - q_t) V‖_HS ≤ (1 + q_t) ‖V‖_HS` with `K_t = K_{θ_t}(z_{1,t}, z_{2,t})`
and `q_t = t_c - t₀ - t`. -/
private lemma LF1_tOp (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hS : S < flowTc (lam D N A) z) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (t : ℝ) (ht0 : 0 ≤ t)
    (htS : t ≤ S) (V : Matrix (Fin D) (Fin D) ℂ) :
    hsNorm (((flowTc (lam D N A) z - t : ℝ) : ℂ) • (flowKmat (lam D N A) θ z₁ z₂ t * V +
        V * flowKmat (lam D N A) θ z₁ z₂ t) - ((1 - (flowTc (lam D N A) z - t) : ℝ) : ℂ) • V) ≤
      (1 + (flowTc (lam D N A) z - t)) * hsNorm V := by
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  obtain ⟨hηt, -, -, -, -, htc, -⟩ := LF1_flow D N hD1 hN1 A hA z hz S hS t ht0 htS
  set A' : Matrix (Fin N) (Fin N) ℂ := ((Real.exp (-t / 2) : ℝ) : ℂ) • A with hA'
  have hlam : lam D N A' = ((Real.exp (-t / 2) : ℝ) : ℂ) • lam D N A :=
    (LF1_lam_smul D N A _).symm
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
private lemma LF1_rsum (q₀ h : ℝ) (hh : 0 < h) (k : ℕ) (hk : k * h < q₀) :
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

-- The bootstrap and the sharp bound share their objects, so they stay in one declaration.
set_option maxHeartbeats 6400000 in
/-- The bootstrap of the proof of Lemma 3.8 [lem_flow_1] on one grid, pathwise: if the one-step
drift errors, the martingale sums and the start satisfy the bounds of `flowL2_drift`,
(3.59) [CIest] and `N q₀² ι₀² ‖L₀ - K_θ‖ ≤ δ_*`, then (3.26) [flow_1_result] holds at every grid
time, by `duhamel_quad_boot` and `duhamel_lin_le` with `Ψ_k = N q_k ι_k²`. -/
private lemma LF1_boot (D N K : ℕ) [NeZero D] [NeZero N] (hK : 1 ≤ K)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ) (hA : opNorm (lam D N A) ≤ 1 / 10)
    (hz : 0 < z.im) (hSpos : 0 < S) (hSt : S < flowTc (lam D N A) z)
    (hq1 : flowTc (lam D N A) z ≤ 1)
    (hηN : ∀ s, 0 ≤ s → s ≤ S → (N : ℝ)⁻¹ < (charFlowZ (lam D N A) z s).im) (e0 : ℝ)
    (hNη : ∀ s, 0 ≤ s → s ≤ S →
      (N : ℝ) ^ e0 ≤ N * (charFlowZ (lam D N A) z s).im * flowIm (lam D N A) z s)
    (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (H : ℕ → Idx D N → Idx D N → ℂ) (a b εs δs Θ τ' : ℝ)
    (hdrift : ∀ j, j < K → ∀ x y : Fin D,
      ‖(∫ X, ((flowTc (lam D N A) z - (j * (S / K) + S / K) : ℝ) : ℂ) *
            flowLmat (lam D N A) z₁ z₂ (j * (S / K) + S / K)
              (Real.exp (-(S / K) / 2) • H j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
            ∂(gueBlocks D N)) -
          ((flowTc (lam D N A) z - j * (S / K) : ℝ) : ℂ) *
            flowLmat (lam D N A) z₁ z₂ (j * (S / K)) (H j) x y -
          ((S / K : ℝ) : ℂ) * (((flowTc (lam D N A) z - j * (S / K) - 1 : ℝ) : ℂ) *
              flowLmat (lam D N A) z₁ z₂ (j * (S / K)) (H j) x y +
            ((flowTc (lam D N A) z - j * (S / K) : ℝ) : ℂ) *
              (flowLmat (lam D N A) z₁ z₂ (j * (S / K)) (H j) *
                flowLmat (lam D N A) z₁ z₂ (j * (S / K)) (H j)) x y)‖ ≤
        S / K * ((N : ℝ) ^ a / (N * (flowTc (lam D N A) z - j * (S / K)) ^ 2 *
          flowIm (lam D N A) z (j * (S / K)) ^ 2)) + (S / K) ^ 2 * (N : ℝ) ^ (20 : ℝ))
    (hmart : ∀ n, n ≤ K → hsNorm (∑ j ∈ Finset.range n,
        ((flowTc (lam D N A) z - (j + 1) * (S / K) : ℝ) : ℂ) •
          (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K)) (H (j + 1)) -
            Matrix.of fun x y => ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • H j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N))) ≤
      (N : ℝ) ^ b / (N * (flowTc (lam D N A) z - n * (S / K)) *
        flowIm (lam D N A) z (n * (S / K)) ^ 2))
    (hinit : N * flowTc (lam D N A) z ^ 2 * (mExt (lam D N A) z).im ^ 2 *
      hsNorm (Lmat (lam D N A) (H 0) z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) ≤ δs)
    (hγ : (flowTc (lam D N A) z / (flowTc (lam D N A) z - S)) ^ (flowTc (lam D N A) z) ≤
      Real.exp 1)
    (hlog : Real.log (flowTc (lam D N A) z / (flowTc (lam D N A) z - S)) ≤
      Real.log (Real.exp 1 * N))
    (hεs : (N : ℝ) ^ b + Real.exp 1 * D ^ 2 * (N : ℝ) ^ a + D ^ 2 * N * ((N : ℝ) ^ (20 : ℝ) +
      ((D : ℝ) * (Real.exp 1 * N) ^ 2 + Real.exp 1 * N) * (3 + 2 * D * (Real.exp 1 * N))) *
        (K * (S / K) ^ 2) ≤ εs)
    (hΘ : εs + Real.exp 1 ^ 2 * δs + 2 * Real.exp 1 ^ 2 * εs * Real.log (Real.exp 1 * N) +
      Real.exp 1 ^ 4 * Θ ^ 2 / (N : ℝ) ^ e0 < Θ)
    (hfin1 : Real.exp 1 ≤ (N : ℝ) ^ τ')
    (hfin2 : εs + 2 * Real.exp 1 ^ 2 * εs * Real.log (Real.exp 1 * N) +
      Real.exp 1 ^ 4 * Θ ^ 2 / (N : ℝ) ^ e0 ≤ (N : ℝ) ^ τ') :
    ∀ k, k ≤ K → hsNorm (flowLmat (lam D N A) z₁ z₂ (k * (S / K)) (H k) -
        flowKmat (lam D N A) θ z₁ z₂ (k * (S / K))) ≤
      (N : ℝ) ^ τ' * ((flowTc (lam D N A) z / (flowTc (lam D N A) z - k * (S / K))) ^ 2 *
          hsNorm (Lmat (lam D N A) (H 0) z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) +
        1 / (N * (flowTc (lam D N A) z - k * (S / K)) ^ 2 *
          flowIm (lam D N A) z (k * (S / K)) ^ 2)) := by
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (NeZero.ne D)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  set h := S / K with hhdef
  have hh : 0 < h := div_pos hSpos hKpos
  have hKh : (K : ℝ) * h = S := by rw [hhdef]; field_simp
  set q₀ := flowTc (lam D N A) z with hq₀
  have hq0 : 0 < q₀ := by linarith
  set e := Real.exp 1 with he
  have he1 : 1 ≤ e := Real.one_le_exp (by norm_num)
  have hgrid : ∀ k : ℕ, k ≤ K → 0 ≤ (k : ℝ) * h ∧ (k : ℝ) * h ≤ S := fun k hk =>
    ⟨by positivity, (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le).trans_eq hKh⟩
  -- the flow at the grid times
  have hfl : ∀ k : ℕ, k ≤ K → 0 < q₀ - k * h ∧ 0 < flowIm (lam D N A) z (k * h) ∧
      flowIm (lam D N A) z (k * h) < 1 ∧
      flowIm (lam D N A) z (k * h) = Real.exp (k * h / 2) * (mExt (lam D N A) z).im ∧
      (N : ℝ) ^ e0 / e ≤ N * flowIm (lam D N A) z (k * h) ^ 2 * (q₀ - k * h) := by
    intro k hk
    obtain ⟨h0, hS'⟩ := hgrid k hk
    obtain ⟨hη, hιeq, hι0, hι1, -, -, -⟩ := LF1_flow D N hD1 hN1 A hA z hz S hSt (k * h) h0 hS'
    have hιpos : 0 < flowIm (lam D N A) z (k * h) := by
      rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
    have hup := LF1_flow_up D N hD1 hN1 A hA z hz S hSt hq1 (k * h) h0 hS'
    have hNη' := hNη (k * h) h0 hS'
    refine ⟨by linarith, hιpos, hι1, hιeq, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    calc (N : ℝ) ^ e0 ≤ N * (charFlowZ (lam D N A) z (k * h)).im * flowIm (lam D N A) z (k * h) :=
          hNη'
      _ ≤ N * (e * (q₀ - k * h) * flowIm (lam D N A) z (k * h)) *
          flowIm (lam D N A) z (k * h) := by gcongr
      _ = N * flowIm (lam D N A) z (k * h) ^ 2 * (q₀ - k * h) * e := by ring
  have hι0 : 0 < (mExt (lam D N A) z).im :=
    (LF1_flow D N hD1 hN1 A hA z hz S hSt 0 le_rfl hSpos.le).2.2.1
  -- `q_K ≥ (eN)⁻¹`
  have hqK : (e * N)⁻¹ ≤ q₀ - S := by
    obtain ⟨hη, -, -, hιS1, -, -, -⟩ := LF1_flow D N hD1 hN1 A hA z hz S hSt S hSpos.le le_rfl
    have hup := LF1_flow_up D N hD1 hN1 A hA z hz S hSt hq1 S hSpos.le le_rfl
    have hιS : 0 < flowIm (lam D N A) z S := by
      have := (hfl K le_rfl).2.1; rwa [hKh] at this
    have h1 := hηN S hSpos.le le_rfl
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have : (1 : ℝ) < N * (charFlowZ (lam D N A) z S).im := by
      rw [inv_lt_iff_one_lt_mul₀ hNpos] at h1; linarith
    nlinarith
  -- the objects of the bootstrap
  obtain ⟨Lm, hLm⟩ : ∃ Lm : ℕ → Matrix (Fin D) (Fin D) ℂ,
      Lm = fun k : ℕ => flowLmat (lam D N A) z₁ z₂ (k * h) (H k) := ⟨_, rfl⟩
  obtain ⟨Km, hKm⟩ : ∃ Km : ℕ → Matrix (Fin D) (Fin D) ℂ,
      Km = fun k : ℕ => flowKmat (lam D N A) θ z₁ z₂ (k * h) := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℕ → ℝ, ρ = fun k : ℕ => N * flowIm (lam D N A) z (k * h) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℕ → EuclideanSpace ℂ (Fin D × Fin D),
      Δ = fun k : ℕ => LF1_vec (((q₀ - k * h : ℝ) : ℂ) • (Lm k - Km k)) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Fin D × Fin D),
      T = fun k : ℕ => if k < K then LF1_op (Km k) (q₀ - k * h) else 0 := ⟨_, rfl⟩
  obtain ⟨ℰ, hℰdef⟩ : ∃ ℰ : ℕ → EuclideanSpace ℂ (Fin D × Fin D),
      ℰ = fun k : ℕ => ∑ j ∈ Finset.range k, (Δ (j + 1) - Δ j -
        ((h / (q₀ - (0 + j * h)) : ℝ) : ℂ) • (T j (Δ j) + LF1_sq (Δ j))) := ⟨_, rfl⟩
  have hTn : ∀ k, ‖T k‖ ≤ 1 + q₀ := by
    intro k
    rw [hTdef]
    dsimp only
    split_ifs with hk
    · refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun v => ?_
      rw [LF1_op_apply, LF1_norm_vec, LF1_norm_mat]
      obtain ⟨h0, hS'⟩ := hgrid k hk.le
      have := LF1_tOp D N A hA z hz S hSt θ hθ₀ hθ₁ z₁ z₂ h₁ h₂ (k * h) h0 hS' (LF1_mat v)
      rw [hKm]
      refine this.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
    · rw [norm_zero]; linarith
  have hρ0 : 0 < ρ 0 := by
    rw [hρdef]; have := (hfl 0 (Nat.zero_le K)).2.1; positivity
  have hρle : ∀ j k, j ≤ k → k ≤ K → ρ j ≤ ρ k ∧ ρ k ≤ e * ρ j := by
    intro j k hjk hkK
    have hj := (hfl j (hjk.trans hkK)).2.2.2.1
    have hk := (hfl k hkK).2.2.2.1
    rw [hρdef]
    dsimp only
    rw [hj, hk, mul_pow, mul_pow]
    have e2 : ∀ x : ℝ, Real.exp (x / 2) ^ 2 = Real.exp x := fun x => by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e2, e2]
    have hjk' : (j : ℝ) * h ≤ k * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hjk) hh.le
    have hkS := (hgrid k hkK).2
    have h0 := (hgrid j (hjk.trans hkK)).1
    have hm2 : 0 ≤ (mExt (lam D N A) z).im ^ 2 := sq_nonneg _
    constructor
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 hjk') hm2) hNpos.le
    · have : Real.exp (k * h) ≤ e * Real.exp (j * h) := by
        rw [he, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
      have := mul_le_mul_of_nonneg_right this hm2
      nlinarith
  have hℰ0 : ℰ 0 = 0 := by rw [hℰdef]; simp
  have hrec : ∀ k, k < K → Δ (k + 1) - ℰ (k + 1) = Δ k - ℰ k +
      ((h / (q₀ - (0 + k * h)) : ℝ) : ℂ) • (T k (Δ k) + LF1_sq (Δ k)) := by
    intro k _
    rw [hℰdef]
    dsimp only
    rw [Finset.sum_range_succ]
    abel
  have hΔ0 : ρ 0 * (q₀ - 0) * ‖Δ 0‖ ≤ δs := by
    obtain ⟨z0L, z0K, z0I⟩ := LF1_zero (lam D N A) θ z z₁ z₂ (H 0)
    rw [hρdef, hΔ, hLm, hKm]
    dsimp only
    simp only [Nat.cast_zero, zero_mul, sub_zero, z0L, z0K, z0I, LF1_norm_vec, LF1_hs_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
    refine le_trans (le_of_eq ?_) hinit
    ring
  have hΨ : ∀ k, k ≤ K → (N : ℝ) ^ e0 / e ≤ ρ k * (q₀ - (0 + k * h)) := by
    intro k hk
    rw [hρdef, zero_add]
    exact (hfl k hk).2.2.2.2
  have hΨ0 : 0 < (N : ℝ) ^ e0 / e := by
    have := Real.rpow_pos_of_pos hNpos e0; positivity
  -- the one-step decomposition
  obtain ⟨Ej, hEj⟩ : ∃ Ej : ℕ → Matrix (Fin D) (Fin D) ℂ, Ej = fun j : ℕ =>
      Matrix.of fun x y => ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * h)
        (Real.exp (-h / 2) • H j + Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N X))
          x y ∂(gueBlocks D N) := ⟨_, rfl⟩
  obtain ⟨Mj, hMj⟩ : ∃ Mj : ℕ → Matrix (Fin D) (Fin D) ℂ, Mj = fun j : ℕ =>
      ((q₀ - (j + 1) * h : ℝ) : ℂ) • (flowLmat (lam D N A) z₁ z₂ ((j + 1) * h) (H (j + 1)) -
        Ej j) := ⟨_, rfl⟩
  obtain ⟨Dr, hDr⟩ : ∃ Dr : ℕ → Matrix (Fin D) (Fin D) ℂ, Dr = fun j : ℕ =>
      ((q₀ - (j + 1) * h : ℝ) : ℂ) • Ej j - ((q₀ - j * h : ℝ) : ℂ) • Lm j -
        (h : ℂ) • (((q₀ - j * h - 1 : ℝ) : ℂ) • Lm j + ((q₀ - j * h : ℝ) : ℂ) • (Lm j * Lm j)) :=
    ⟨_, rfl⟩
  obtain ⟨rK, hrK⟩ : ∃ rK : ℕ → Matrix (Fin D) (Fin D) ℂ, rK = fun j : ℕ =>
      ((q₀ - (j + 1) * h : ℝ) : ℂ) • Km (j + 1) - ((q₀ - j * h : ℝ) : ℂ) • Km j -
        (h : ℂ) • (((q₀ - j * h - 1 : ℝ) : ℂ) • Km j + ((q₀ - j * h : ℝ) : ℂ) • (Km j * Km j)) :=
    ⟨_, rfl⟩
  have hid : ∀ j, j < K → Δ (j + 1) - Δ j -
      ((h / (q₀ - (0 + j * h)) : ℝ) : ℂ) • (T j (Δ j) + LF1_sq (Δ j)) =
      LF1_vec (Mj j + Dr j - rK j) := by
    intro j hj
    have hqj : (q₀ - j * h : ℝ) ≠ 0 := (hfl j hj.le).1.ne'
    have hT : T j = LF1_op (Km j) (q₀ - j * h) := by rw [hTdef]; simp [hj]
    rw [hT, hΔ, LF1_op_apply, LF1_sq]
    simp only [LF1_mat_vec, ← map_smul, ← map_add, ← map_sub]
    congr 1
    have key := LF1_alg_id (Lm j) (Km j) (Lm (j + 1)) (Km (j + 1))
      (((q₀ - (j + 1) * h : ℝ) : ℂ) • Ej j) ((q₀ - j * h : ℝ) : ℂ)
      ((q₀ - (j + 1) * h : ℝ) : ℂ) ((h / (q₀ - (0 + j * h)) : ℝ) : ℂ)
    have hgq : ((h / (q₀ - (0 + j * h)) : ℝ) : ℂ) * ((q₀ - j * h : ℝ) : ℂ) = (h : ℂ) := by
      rw [zero_add, ← Complex.ofReal_mul, div_mul_cancel₀ _ hqj]
    rw [hgq] at key
    have hcast : ((q₀ - ((j + 1 : ℕ) : ℝ) * h : ℝ) : ℂ) = ((q₀ - (j + 1) * h : ℝ) : ℂ) := by
      push_cast; ring
    have hcast2 : ((1 - (q₀ - j * h) : ℝ) : ℂ) = 1 - ((q₀ - j * h : ℝ) : ℂ) := by push_cast; ring
    have hcast3 : ((q₀ - j * h - 1 : ℝ) : ℂ) = ((q₀ - j * h : ℝ) : ℂ) - 1 := by push_cast; ring
    have hLm1 : Lm (j + 1) = flowLmat (lam D N A) z₁ z₂ ((j + 1) * h) (H (j + 1)) := by
      rw [hLm]; push_cast; rfl
    rw [hcast, hcast2]
    rw [hMj, hDr, hrK]
    dsimp only
    rw [← hLm1, hcast3]
    rw [key]
    simp only [smul_sub]
  have hℰsum : ∀ k, k ≤ K → ℰ k = LF1_vec (∑ j ∈ Finset.range k, (Mj j + Dr j - rK j)) := by
    intro k hk
    rw [hℰdef]
    dsimp only
    rw [map_sum]
    exact Finset.sum_congr rfl fun j hj => hid j (lt_of_lt_of_le (Finset.mem_range.1 hj) hk)
  -- the drift errors
  have hDrb : ∀ j, j < K → hsNorm (Dr j) ≤ D ^ 2 * (h * ((N : ℝ) ^ a /
      (N * (q₀ - j * h) ^ 2 * flowIm (lam D N A) z (j * h) ^ 2)) + h ^ 2 * (N : ℝ) ^ (20 : ℝ)) := by
    intro j hj
    refine LF1_hs_entry _ _ fun x y => ?_
    have hd := hdrift j hj x y
    refine le_of_eq_of_le ?_ hd
    congr 1
    rw [hDr, hEj, hLm]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
      smul_eq_mul]
    rw [integral_const_mul, show ((j : ℝ) + 1) * h = j * h + h by ring]
  -- the errors of the Riccati equation
  set ρ' := (q₀ - S)⁻¹ with hρ'
  have hρ'le : ρ' ≤ e * N := by
    rw [hρ', inv_le_comm₀ (by linarith) (by positivity)]
    exact hqK
  have hρ'0 : 0 < ρ' := inv_pos.2 (by linarith)
  set Lbar := ((D : ℝ) * (e * N) ^ 2 + e * N) * (3 + 2 * D * (e * N)) with hLbar
  have hLle : ((D : ℝ) * ρ' ^ 2 + ρ') * (3 + 2 * D * ρ') ≤ Lbar := by
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    rw [hLbar]
    gcongr
  have hrKb : ∀ j, j < K → hsNorm (rK j) ≤ D ^ 2 * (Lbar * h ^ 2) := by
    intro j hj
    refine LF1_hs_entry _ _ fun x y => ?_
    have hjK := hgrid (j + 1) hj
    have hu := (hgrid j hj.le).1
    have huh : (j : ℝ) * h + h ≤ S := by
      have := hjK.2; push_cast at this; linarith
    have hk := LF1_Kdisc D N A hA z hz S hSt hq1 θ hθ₀ hθ₁ z₁ z₂ h₁ h₂ (j * h) h hu hh.le huh x y
    have e1 : rK j = ((q₀ - (j * h + h) : ℝ) : ℂ) • flowKmat (lam D N A) θ z₁ z₂ (j * h + h) -
        ((q₀ - j * h : ℝ) : ℂ) • flowKmat (lam D N A) θ z₁ z₂ (j * h) -
        (h : ℂ) • (((q₀ - j * h - 1 : ℝ) : ℂ) • flowKmat (lam D N A) θ z₁ z₂ (j * h) +
          ((q₀ - j * h : ℝ) : ℂ) • (flowKmat (lam D N A) θ z₁ z₂ (j * h) *
            flowKmat (lam D N A) θ z₁ z₂ (j * h))) := by
      rw [hrK, hKm]
      dsimp only
      rw [show ((j : ℝ) + 1) * h = j * h + h by ring,
        show ((j + 1 : ℕ) : ℝ) * h = j * h + h by push_cast; ring]
    rw [e1]
    refine hk.trans ?_
    exact mul_le_mul_of_nonneg_right hLle (sq_nonneg h)
  have hℰb : ∀ k, k ≤ K → ρ k * (q₀ - (0 + k * h)) * ‖ℰ k‖ ≤ εs := by
    intro k hk
    rw [hℰsum k hk, LF1_norm_vec, zero_add]
    obtain ⟨hqk, hιk, hιk1, hιeq, -⟩ := hfl k hk
    have hkS := (hgrid k hk).2
    have hs : hsNorm (∑ j ∈ Finset.range k, (Mj j + Dr j - rK j)) ≤
        hsNorm (∑ j ∈ Finset.range k, Mj j) + (∑ j ∈ Finset.range k, hsNorm (Dr j)) +
          ∑ j ∈ Finset.range k, hsNorm (rK j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      refine (LF1_hs_sub _ _).trans (add_le_add ((LF1_hs_add _ _).trans
        (add_le_add le_rfl (LF1_hs_sum _ _))) (LF1_hs_sum _ _))
    have hM : hsNorm (∑ j ∈ Finset.range k, Mj j) ≤ (N : ℝ) ^ b /
        (N * (q₀ - k * h) * flowIm (lam D N A) z (k * h) ^ 2) := by
      have := hmart k hk
      rw [hMj, hEj]
      exact this
    -- the drift sum
    have hι2 : ∀ j, j ≤ k → (mExt (lam D N A) z).im ^ 2 ≤ flowIm (lam D N A) z (j * h) ^ 2 := by
      intro j hj
      rw [(hfl j (hj.trans hk)).2.2.2.1, mul_pow]
      have : 1 ≤ Real.exp (j * h / 2) ^ 2 :=
        one_le_pow₀ (Real.one_le_exp (by have := (hgrid j (hj.trans hk)).1; linarith))
      nlinarith [sq_nonneg (mExt (lam D N A) z).im]
    have hιk2 : flowIm (lam D N A) z (k * h) ^ 2 ≤ e * (mExt (lam D N A) z).im ^ 2 := by
      rw [hιeq, mul_pow]
      have : Real.exp (k * h / 2) ^ 2 ≤ e := by
        rw [← Real.exp_nat_mul, he]
        exact Real.exp_le_exp.2 (by push_cast; linarith)
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have hR := (LF1_rsum q₀ h hh k (by linarith)).2.1
    have hDsum : ∑ j ∈ Finset.range k, hsNorm (Dr j) ≤
        D ^ 2 * ((N : ℝ) ^ a / N * (1 / (mExt (lam D N A) z).im ^ 2) * (q₀ - k * h)⁻¹) +
          D ^ 2 * (K * h ^ 2) * (N : ℝ) ^ (20 : ℝ) := by
      have hNa : 0 ≤ (N : ℝ) ^ a := Real.rpow_nonneg hNpos.le _
      calc ∑ j ∈ Finset.range k, hsNorm (Dr j)
          ≤ ∑ j ∈ Finset.range k, (D ^ 2 * ((N : ℝ) ^ a / N * (1 / (mExt (lam D N A) z).im ^ 2) *
              (h * ((q₀ - j * h) ^ 2)⁻¹)) + D ^ 2 * h ^ 2 * (N : ℝ) ^ (20 : ℝ)) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjk : j < k := Finset.mem_range.1 hj
            refine (hDrb j (lt_of_lt_of_le hjk hk)).trans ?_
            have hqj := (hfl j (hjk.le.trans hk)).1
            have hιj := hι2 j hjk.le
            have h1 : h * ((N : ℝ) ^ a / (N * (q₀ - j * h) ^ 2 *
                flowIm (lam D N A) z (j * h) ^ 2)) ≤ (N : ℝ) ^ a / N *
                (1 / (mExt (lam D N A) z).im ^ 2) * (h * ((q₀ - j * h) ^ 2)⁻¹) := by
              rw [show h * ((N : ℝ) ^ a / (N * (q₀ - j * h) ^ 2 *
                  flowIm (lam D N A) z (j * h) ^ 2)) = (N : ℝ) ^ a / N *
                  (1 / flowIm (lam D N A) z (j * h) ^ 2) * (h * ((q₀ - j * h) ^ 2)⁻¹) by
                field_simp]
              gcongr
            nlinarith [sq_nonneg (D : ℝ)]
        _ = D ^ 2 * ((N : ℝ) ^ a / N * (1 / (mExt (lam D N A) z).im ^ 2) *
              ∑ j ∈ Finset.range k, (h * ((q₀ - j * h) ^ 2)⁻¹)) +
            D ^ 2 * (k * h ^ 2) * (N : ℝ) ^ (20 : ℝ) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
              Finset.card_range, nsmul_eq_mul]
            ring
        _ ≤ _ := by
            have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk
            gcongr
    have hRsum : ∑ j ∈ Finset.range k, hsNorm (rK j) ≤ D ^ 2 * (Lbar * (K * h ^ 2)) := by
      calc ∑ j ∈ Finset.range k, hsNorm (rK j) ≤ ∑ _j ∈ Finset.range k, D ^ 2 * (Lbar * h ^ 2) :=
            Finset.sum_le_sum fun j hj =>
              hrKb j (lt_of_lt_of_le (Finset.mem_range.1 hj) hk)
        _ = D ^ 2 * (Lbar * (k * h ^ 2)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        _ ≤ _ := by
            have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk
            have hL0 : 0 ≤ Lbar := by rw [hLbar]; positivity
            gcongr
    -- assembly
    rw [hρdef]
    dsimp only
    have hρk : 0 ≤ (N : ℝ) * flowIm (lam D N A) z (k * h) ^ 2 * (q₀ - k * h) := by positivity
    have hι0' : 0 < (mExt (lam D N A) z).im := hι0
    calc (N : ℝ) * flowIm (lam D N A) z (k * h) ^ 2 * (q₀ - k * h) *
          hsNorm (∑ j ∈ Finset.range k, (Mj j + Dr j - rK j))
        ≤ (N : ℝ) * flowIm (lam D N A) z (k * h) ^ 2 * (q₀ - k * h) *
          ((N : ℝ) ^ b / (N * (q₀ - k * h) * flowIm (lam D N A) z (k * h) ^ 2) +
            (D ^ 2 * ((N : ℝ) ^ a / N * (1 / (mExt (lam D N A) z).im ^ 2) * (q₀ - k * h)⁻¹) +
              D ^ 2 * (K * h ^ 2) * (N : ℝ) ^ (20 : ℝ)) + D ^ 2 * (Lbar * (K * h ^ 2))) := by
          refine mul_le_mul_of_nonneg_left (hs.trans ?_) hρk
          exact add_le_add (add_le_add hM hDsum) hRsum
      _ = (N : ℝ) ^ b + D ^ 2 * (N : ℝ) ^ a *
            (flowIm (lam D N A) z (k * h) ^ 2 / (mExt (lam D N A) z).im ^ 2) +
          (N : ℝ) * flowIm (lam D N A) z (k * h) ^ 2 * (q₀ - k * h) *
            (D ^ 2 * ((N : ℝ) ^ (20 : ℝ) + Lbar) * (K * h ^ 2)) := by
          field_simp
          ring
      _ ≤ (N : ℝ) ^ b + D ^ 2 * (N : ℝ) ^ a * e +
          (N : ℝ) * 1 * 1 * (D ^ 2 * ((N : ℝ) ^ (20 : ℝ) + Lbar) * (K * h ^ 2)) := by
          have hL0 : 0 ≤ Lbar := by rw [hLbar]; positivity
          have hX : 0 ≤ (D : ℝ) ^ 2 * ((N : ℝ) ^ (20 : ℝ) + Lbar) * (K * h ^ 2) := by positivity
          have h1 : flowIm (lam D N A) z (k * h) ^ 2 / (mExt (lam D N A) z).im ^ 2 ≤ e := by
            rw [div_le_iff₀ (by positivity)]; exact hιk2
          have h2 : flowIm (lam D N A) z (k * h) ^ 2 ≤ 1 := pow_le_one₀ hιk.le hιk1.le
          have h3 : q₀ - k * h ≤ 1 := by have := (hgrid k hk).1; linarith
          have hNa : 0 ≤ (N : ℝ) ^ a := Real.rpow_nonneg hNpos.le _
          gcongr
      _ ≤ εs := by
          refine le_trans (le_of_eq ?_) hεs
          rw [hLbar]
          ring
  -- the bootstrap
  have hεs0 : 0 ≤ εs := le_trans (by
    have hL0 : 0 ≤ ((D : ℝ) * (e * N) ^ 2 + e * N) * (3 + 2 * D * (e * N)) := by positivity
    have := Real.rpow_nonneg hNpos.le b
    have := Real.rpow_nonneg hNpos.le a
    have := Real.rpow_nonneg hNpos.le (20 : ℝ)
    positivity) hεs
  have hδs0 : 0 ≤ δs := le_trans (by
    have := LF1_op_nonneg (lam D N A)
    unfold hsNorm
    positivity) hinit
  have hKS : (0 : ℝ) + K * h = S := by rw [zero_add, hKh]
  have hrat1 : 1 ≤ q₀ / (q₀ - S) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hγ' : ((q₀ - 0) / (q₀ - (0 + K * h))) ^ q₀ ≤ e := by
    rw [hKS, sub_zero]; exact hγ
  have hlog0 : 0 ≤ Real.log (q₀ / (q₀ - S)) := Real.log_nonneg hrat1
  have hγ0 : 0 ≤ ((q₀ - 0) / (q₀ - (0 + K * h))) ^ q₀ := Real.rpow_nonneg (by
    rw [hKS, sub_zero]; positivity) _
  have hΘ' : εs + ((q₀ - 0) / (q₀ - (0 + K * h))) ^ q₀ * e * δs +
      ((q₀ - 0) / (q₀ - (0 + K * h))) ^ q₀ * (1 + q₀) * e * εs *
        Real.log ((q₀ - 0) / (q₀ - (0 + K * h))) +
      ((q₀ - 0) / (q₀ - (0 + K * h))) ^ q₀ * e ^ 2 * Θ ^ 2 / ((N : ℝ) ^ e0 / e) < Θ := by
    rw [hKS, sub_zero] at hγ0 ⊢
    set γ := (q₀ / (q₀ - S)) ^ q₀
    have hNe0 : 0 < (N : ℝ) ^ e0 := Real.rpow_pos_of_pos hNpos _
    have t1 : γ * e * δs ≤ e ^ 2 * δs := by
      have := mul_le_mul_of_nonneg_right hγ (by positivity : 0 ≤ e * δs); nlinarith
    have t2 : γ * (1 + q₀) * e * εs * Real.log (q₀ / (q₀ - S)) ≤
        2 * e ^ 2 * εs * Real.log (e * N) := by
      have h1 : γ * (1 + q₀) ≤ e * 2 := mul_le_mul hγ (by linarith) (by linarith) (by linarith)
      have h2 := mul_le_mul h1 (mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ e * εs))
        (by positivity) (by positivity)
      nlinarith
    have t3 : γ * e ^ 2 * Θ ^ 2 / ((N : ℝ) ^ e0 / e) ≤ e ^ 4 * Θ ^ 2 / (N : ℝ) ^ e0 := by
      rw [div_div_eq_mul_div, div_le_div_iff₀ hNe0 hNe0]
      have := mul_le_mul_of_nonneg_right hγ (by positivity : 0 ≤ e ^ 2 * Θ ^ 2 * e *
        (N : ℝ) ^ e0)
      nlinarith
    linarith
  have hboot := duhamel_quad_boot T LF1_sq 0 h q₀ q₀ e εs δs Θ ((N : ℝ) ^ e0 / e) K hh hq0.le
    he1 (by rw [hKS]; exact hSt) (fun k _ => hTn k) LF1_sq_le ρ hρ0 hρle Δ ℰ hℰ0 hrec hℰb hΔ0
    hΨ hΨ0 hΘ'
  -- the sharp bound by the linear Duhamel formula
  obtain ⟨x, hx⟩ : ∃ x : ℕ → EuclideanSpace ℂ (Fin D × Fin D), x = fun k => Δ k - ℰ k :=
    ⟨_, rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ bb : ℕ → EuclideanSpace ℂ (Fin D × Fin D), bb = fun k : ℕ =>
      x (k + 1) - x k - ((h / (q₀ - (0 + k * h)) : ℝ) : ℂ) • T k (x k) := ⟨_, rfl⟩
  have hxrec : ∀ k, x (k + 1) = x k + ((h / (q₀ - (0 + k * h)) : ℝ) : ℂ) • T k (x k) + bb k := by
    intro k
    rw [hbb]
    dsimp only
    rw [sub_sub, add_sub_cancel]
  have hbbj : ∀ j, j < K → ‖bb j‖ ≤ h / (q₀ - j * h) * ((1 + q₀) * ‖ℰ j‖ + ‖Δ j‖ ^ 2) := by
    intro j hj
    have hqj := (hfl j hj.le).1
    have e1 : bb j = ((h / (q₀ - j * h) : ℝ) : ℂ) • (T j (ℰ j) + LF1_sq (Δ j)) := by
      rw [hbb]
      dsimp only
      rw [hx]
      dsimp only
      have hr := hrec j hj
      rw [zero_add] at hr ⊢
      rw [hr, map_sub]
      simp only [smul_add, smul_sub]
      abel
    rw [e1, norm_smul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hh.le hqj.le)]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ (LF1_sq_le _)))
      (div_nonneg hh.le hqj.le)
    exact ((T j).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hTn j) (norm_nonneg _))
  intro k hk
  obtain ⟨hqk, hιk, hιk1, hιeq, hΨk⟩ := hfl k hk
  have hkS := (hgrid k hk).2
  have hlin := duhamel_lin_le T 0 h q₀ (1 + q₀) hh (by linarith) hTn x bb hxrec k
    (by rw [zero_add]; linarith)
  simp only [zero_add, sub_zero] at hlin
  -- the pieces
  have hx0 : x 0 = Δ 0 := by rw [hx]; simp [hℰ0]
  have hΔ0n : ‖Δ 0‖ = q₀ * hsNorm (Lmat (lam D N A) (H 0) z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) := by
    obtain ⟨z0L, z0K, -⟩ := LF1_zero (lam D N A) θ z z₁ z₂ (H 0)
    rw [hΔ, hLm, hKm]
    dsimp only
    simp only [Nat.cast_zero, zero_mul, sub_zero, z0L, z0K, LF1_norm_vec, LF1_hs_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
  set X₀ := hsNorm (Lmat (lam D N A) (H 0) z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) with hX₀
  have hX₀0 : 0 ≤ X₀ := Real.sqrt_nonneg _
  have hΔk : ‖Δ k‖ = (q₀ - k * h) * hsNorm (flowLmat (lam D N A) z₁ z₂ (k * h) (H k) -
      flowKmat (lam D N A) θ z₁ z₂ (k * h)) := by
    rw [hΔ, hLm, hKm]
    dsimp only
    rw [LF1_norm_vec, LF1_hs_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqk]
  -- ratios
  have hratk : (q₀ / (q₀ - k * h)) ^ q₀ ≤ e := by
    refine le_trans (Real.rpow_le_rpow (by positivity) ?_ hq0.le) hγ
    exact div_le_div_of_nonneg_left hq0.le (by linarith) (by linarith)
  have hratj : ∀ j, j < k → ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ (1 + q₀) ≤
      e * ((q₀ - j * h) / (q₀ - k * h)) := by
    intro j hj
    have hqj := (hfl j (hj.le.trans hk)).1
    have hqj1 := (hfl (j + 1) (by omega)).1
    have h1 : (q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h) ≤ (q₀ - j * h) / (q₀ - k * h) := by
      apply div_le_div_of_nonneg_right _ hqk.le
      push_cast; nlinarith
    have h2 : (q₀ - j * h) / (q₀ - k * h) ≤ q₀ / (q₀ - S) := by
      have : (q₀ - j * h) ≤ q₀ := by have := (hgrid j (hj.le.trans hk)).1; linarith
      calc (q₀ - j * h) / (q₀ - k * h) ≤ q₀ / (q₀ - k * h) :=
            div_le_div_of_nonneg_right this hqk.le
        _ ≤ q₀ / (q₀ - S) := div_le_div_of_nonneg_left hq0.le (by linarith) (by linarith)
    have h0 : 0 ≤ (q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h) := div_nonneg hqj1.le hqk.le
    calc ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ (1 + q₀)
        ≤ ((q₀ - j * h) / (q₀ - k * h)) ^ (1 + q₀) :=
          Real.rpow_le_rpow h0 h1 (by linarith)
      _ = ((q₀ - j * h) / (q₀ - k * h)) * ((q₀ - j * h) / (q₀ - k * h)) ^ q₀ := by
          rw [Real.rpow_add (div_pos hqj hqk), Real.rpow_one]
      _ ≤ ((q₀ - j * h) / (q₀ - k * h)) * e := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hqj.le hqk.le)
          exact (Real.rpow_le_rpow (div_nonneg hqj.le hqk.le) h2 hq0.le).trans hγ
      _ = _ := by ring
  -- the sum of the propagated sources
  set R := ρ k with hR
  have hRpos : 0 < R := by rw [hR, hρdef]; positivity
  have hRq : (N : ℝ) ^ e0 / e ≤ R * (q₀ - k * h) := by
    have := hΨ k hk; rwa [zero_add] at this
  have hlogk : Real.log (q₀ / (q₀ - k * h)) ≤ Real.log (e * N) := by
    refine le_trans (Real.log_le_log (by positivity) ?_) hlog
    exact div_le_div_of_nonneg_left hq0.le (by linarith) (by linarith)
  have hsumb : ∑ j ∈ Finset.range k,
      ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ (1 + q₀) * ‖bb j‖ ≤
      e / (q₀ - k * h) * (2 * εs * (e / R) * Real.log (e * N) +
        Θ ^ 2 * (e / R) ^ 2 * (q₀ - k * h)⁻¹) := by
    obtain ⟨-, hR2, hRl⟩ := LF1_rsum q₀ h hh k (by linarith)
    have hstep : ∀ j ∈ Finset.range k,
        ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ (1 + q₀) * ‖bb j‖ ≤
        e / (q₀ - k * h) * (2 * εs * (e / R) * (h / (q₀ - j * h)) +
          Θ ^ 2 * (e / R) ^ 2 * (h * ((q₀ - j * h) ^ 2)⁻¹)) := by
      intro j hj
      have hjk : j < k := Finset.mem_range.1 hj
      have hjK : j < K := lt_of_lt_of_le hjk hk
      have hqj := (hfl j hjK.le).1
      have hρj : 0 < ρ j := by rw [hρdef]; have := (hfl j hjK.le).2.1; positivity
      have hρjk : R ≤ e * ρ j := (hρle j k hjk.le hk).2
      have hinvρ : 1 / ρ j ≤ e / R := by
        rw [div_le_div_iff₀ hρj hRpos]; linarith
      have hE : ‖ℰ j‖ ≤ εs / (ρ j * (q₀ - j * h)) := by
        have := hℰb j hjK.le; rw [zero_add] at this
        rw [le_div_iff₀ (by positivity)]; linarith
      have hD : ‖Δ j‖ ≤ Θ / (ρ j * (q₀ - j * h)) := by
        have := hboot j hjK.le; rw [zero_add] at this
        rw [le_div_iff₀ (by positivity)]; linarith
      have hb := hbbj j hjK
      have hb' : ‖bb j‖ ≤ h / (q₀ - j * h) * (2 * (εs / (ρ j * (q₀ - j * h))) +
          (Θ / (ρ j * (q₀ - j * h))) ^ 2) := by
        refine hb.trans (mul_le_mul_of_nonneg_left ?_ (div_nonneg hh.le hqj.le))
        have hΔ2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
        have h1 : (1 + q₀) * ‖ℰ j‖ ≤ 2 * (εs / (ρ j * (q₀ - j * h))) := by
          have := norm_nonneg (ℰ j)
          nlinarith
        linarith
      have hrj := hratj j hjk
      have h0 : 0 ≤ ‖bb j‖ := norm_nonneg _
      calc ((q₀ - ((j + 1 : ℕ) : ℝ) * h) / (q₀ - k * h)) ^ (1 + q₀) * ‖bb j‖
          ≤ e * ((q₀ - j * h) / (q₀ - k * h)) * (h / (q₀ - j * h) *
            (2 * (εs / (ρ j * (q₀ - j * h))) + (Θ / (ρ j * (q₀ - j * h))) ^ 2)) :=
            mul_le_mul hrj hb' h0 (by positivity)
        _ = e / (q₀ - k * h) * (2 * εs * (1 / ρ j) * (h / (q₀ - j * h)) +
            Θ ^ 2 * (1 / ρ j) ^ 2 * (h * ((q₀ - j * h) ^ 2)⁻¹)) := by
            field_simp
        _ ≤ e / (q₀ - k * h) * (2 * εs * (e / R) * (h / (q₀ - j * h)) +
            Θ ^ 2 * (e / R) ^ 2 * (h * ((q₀ - j * h) ^ 2)⁻¹)) := by
            have h1 : 0 ≤ 1 / ρ j := by positivity
            gcongr
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (hRl.trans hlogk)
      (by positivity)) (mul_le_mul_of_nonneg_left hR2 (by positivity))) (by positivity)
  -- the final bound
  have hEk : ‖ℰ k‖ ≤ εs / (R * (q₀ - k * h)) := by
    have := hℰb k hk; rw [zero_add] at this
    rw [le_div_iff₀ (by positivity)]; linarith
  have hxk : ‖x k‖ ≤ (q₀ / (q₀ - k * h)) ^ (1 + q₀) * (q₀ * X₀) +
      e / (q₀ - k * h) * (2 * εs * (e / R) * Real.log (e * N) +
        Θ ^ 2 * (e / R) ^ 2 * (q₀ - k * h)⁻¹) := by
    rw [hx0, hΔ0n] at hlin
    exact hlin.trans (add_le_add le_rfl hsumb)
  have hΔle : ‖Δ k‖ ≤ ‖x k‖ + ‖ℰ k‖ := by
    have : Δ k = x k + ℰ k := by rw [hx]; exact (sub_add_cancel _ _).symm
    rw [this]; exact norm_add_le _ _
  have hfirst : (q₀ / (q₀ - k * h)) ^ (1 + q₀) * (q₀ * X₀) / (q₀ - k * h) ≤
      (N : ℝ) ^ τ' * ((q₀ / (q₀ - k * h)) ^ 2 * X₀) := by
    have hr0 : 0 < q₀ / (q₀ - k * h) := div_pos hq0 hqk
    have e1 : (q₀ / (q₀ - k * h)) ^ (1 + q₀) * (q₀ * X₀) / (q₀ - k * h) =
        (q₀ / (q₀ - k * h)) ^ q₀ * ((q₀ / (q₀ - k * h)) ^ 2 * X₀) := by
      rw [Real.rpow_add hr0, Real.rpow_one]
      field_simp
    rw [e1]
    exact mul_le_mul_of_nonneg_right (hratk.trans hfin1) (by positivity)
  have hsecond : (e / (q₀ - k * h) * (2 * εs * (e / R) * Real.log (e * N) +
        Θ ^ 2 * (e / R) ^ 2 * (q₀ - k * h)⁻¹) + εs / (R * (q₀ - k * h))) / (q₀ - k * h) ≤
      (N : ℝ) ^ τ' * (1 / (N * (q₀ - k * h) ^ 2 * flowIm (lam D N A) z (k * h) ^ 2)) := by
    have hRdef : R = N * flowIm (lam D N A) z (k * h) ^ 2 := by rw [hR, hρdef]
    have hNe0 : 0 < (N : ℝ) ^ e0 := Real.rpow_pos_of_pos hNpos _
    have hΘ2 : Θ ^ 2 / (R * (q₀ - k * h)) ≤ e * Θ ^ 2 / (N : ℝ) ^ e0 := by
      rw [div_le_div_iff₀ (by positivity) hNe0]
      have := mul_le_mul_of_nonneg_left hRq (sq_nonneg Θ)
      rw [div_le_iff₀ (by positivity)] at hRq
      nlinarith [sq_nonneg Θ]
    have e2 : (e / (q₀ - k * h) * (2 * εs * (e / R) * Real.log (e * N) +
          Θ ^ 2 * (e / R) ^ 2 * (q₀ - k * h)⁻¹) + εs / (R * (q₀ - k * h))) / (q₀ - k * h) =
        (2 * e ^ 2 * εs * Real.log (e * N) + e ^ 3 * (Θ ^ 2 / (R * (q₀ - k * h))) + εs) /
          (R * (q₀ - k * h) ^ 2) := by
      field_simp
    have hRHS : (N : ℝ) ^ τ' * (1 / (N * (q₀ - k * h) ^ 2 * flowIm (lam D N A) z (k * h) ^ 2)) =
        (N : ℝ) ^ τ' / (R * (q₀ - k * h) ^ 2) := by
      rw [hRdef]; field_simp
    rw [e2, hRHS]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h3 : 2 * e ^ 2 * εs * Real.log (e * N) + e ^ 3 * (Θ ^ 2 / (R * (q₀ - k * h))) + εs ≤
        (N : ℝ) ^ τ' := by
      have h4 : e ^ 3 * (Θ ^ 2 / (R * (q₀ - k * h))) ≤ e ^ 4 * Θ ^ 2 / (N : ℝ) ^ e0 := by
        have := mul_le_mul_of_nonneg_left hΘ2 (by positivity : (0 : ℝ) ≤ e ^ 3)
        calc e ^ 3 * (Θ ^ 2 / (R * (q₀ - k * h))) ≤ e ^ 3 * (e * Θ ^ 2 / (N : ℝ) ^ e0) := this
          _ = e ^ 4 * Θ ^ 2 / (N : ℝ) ^ e0 := by ring
      linarith
    exact h3
  have hfin : hsNorm (flowLmat (lam D N A) z₁ z₂ (k * h) (H k) -
      flowKmat (lam D N A) θ z₁ z₂ (k * h)) = ‖Δ k‖ / (q₀ - k * h) := by
    rw [hΔk]; field_simp
  rw [hfin, mul_add]
  calc ‖Δ k‖ / (q₀ - k * h) ≤ (‖x k‖ + ‖ℰ k‖) / (q₀ - k * h) :=
        div_le_div_of_nonneg_right hΔle hqk.le
    _ ≤ ((q₀ / (q₀ - k * h)) ^ (1 + q₀) * (q₀ * X₀) +
          (e / (q₀ - k * h) * (2 * εs * (e / R) * Real.log (e * N) +
            Θ ^ 2 * (e / R) ^ 2 * (q₀ - k * h)⁻¹) + εs / (R * (q₀ - k * h)))) /
          (q₀ - k * h) := by
        apply div_le_div_of_nonneg_right _ hqk.le
        linarith
    _ = (q₀ / (q₀ - k * h)) ^ (1 + q₀) * (q₀ * X₀) / (q₀ - k * h) +
        (e / (q₀ - k * h) * (2 * εs * (e / R) * Real.log (e * N) +
            Θ ^ 2 * (e / R) ^ 2 * (q₀ - k * h)⁻¹) + εs / (R * (q₀ - k * h))) /
          (q₀ - k * h) := by rw [add_div]
    _ ≤ _ := add_le_add hfirst hsecond

/-- `C N^α ≤ N^β` for large `N` when `α < β`. -/
private lemma LF1_ev_pow (C α β : ℝ) (hαβ : α < β) :
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
private lemma LF1_log_le (N s : ℝ) (hN : 1 ≤ N) (hs : 0 < s) :
    Real.log (Real.exp 1 * N) ≤ (1 + s⁻¹) * N ^ s := by
  have hNpos : 0 < N := by linarith
  rw [Real.log_mul (Real.exp_pos 1).ne' hNpos.ne', Real.log_exp]
  have h1 := Real.log_le_rpow_div hNpos.le hs
  have h2 : 1 ≤ N ^ s := Real.one_le_rpow hN hs.le
  rw [div_eq_mul_inv] at h1
  nlinarith [inv_pos.2 hs]

-- The arithmetic conditions on `N` and the three exceptional sets are handled together.
set_option maxHeartbeats 3200000 in
/-- The statement of `flowL2_grid`, proved from `flowL2_drift`, `LF1_mart_half`, `flowGood_grid`
and the bootstrap `LF1_boot`. -/
private lemma LF1_grid_core (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4)
    (hC₀ : 6 < C₀) (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∀ Cg : ℝ, 31 + D' ≤ Cg → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ K : ℕ, (N : ℝ) ^ Cg ≤ K → (K : ℝ) ≤ (N : ℝ) ^ (Cg + 1) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        gridLawA D N K μ₀ {ω |
          N * flowTc (lam D N A) z ^ 2 * (mExt (lam D N A) z).im ^ 2 *
              hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0) z₁ z₂ -
                KTheta (lam D N A) θ z₁ z₂) ≤ (N : ℝ) ^ (2 * εg) ∧
            ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ' *
              ((flowTc (lam D N A) z / (flowTc (lam D N A) z - k * (S / K))) ^ 2 *
                  hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0) z₁ z₂ -
                    KTheta (lam D N A) θ z₁ z₂) +
                1 / (N * (flowTc (lam D N A) z - k * (S / K)) ^ 2 *
                  flowIm (lam D N A) z (k * (S / K)) ^ 2)) <
              hsNorm (flowLmat (lam D N A) z₁ z₂ (k * (S / K)) (gridStateA D N K (S / K) ω k) -
                flowKmat (lam D N A) θ z₁ z₂ (k * (S / K)))} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD' Cg hCg
  set τb := min τ' εg / 8 with hτb
  have hτb0 : 0 < τb := by rw [hτb]; exact div_pos (lt_min hτ' hεg) (by norm_num)
  have hτbτ : τb ≤ τ' / 8 := by
    rw [hτb]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hτbε : τb ≤ εg / 8 := by
    rw [hτb]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨Nd, hNd⟩ := flowL2_drift D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc
    (τb / 12) (by positivity)
  obtain ⟨Nm, hNm⟩ := LF1_mart_half D hD δA τ τe εg c C₀ hδA hτ hεg hC₀ C (τb / 4)
    (by positivity) D' hD' Cg hCg
  obtain ⟨Ng, hNg⟩ := flowGood_grid D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C
    (τb / 32) (by positivity) (D' + 1) (by linarith) Cg (by linarith)
  set e := Real.exp 1 with he
  have hev : ∀ᶠ N : ℕ in Filter.atTop, Nd ≤ N ∧ Nm ≤ N ∧ Ng ≤ N ∧ 2 ≤ N ∧
      2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧ c * (N : ℝ) ^ (-εg) ≤ 1 ∧
      c * (1 + (εg / 2)⁻¹) * (N : ℝ) ^ (-(εg / 2)) ≤ (N : ℝ) ^ (0 : ℝ) ∧
      3 * (N : ℝ) ^ (τb / 4) ≤ (N : ℝ) ^ τb ∧
      3 * (e * D ^ 2) * (N : ℝ) ^ (3 * (τb / 12)) ≤ (N : ℝ) ^ τb ∧
      3 * (D ^ 2 * (1 + 10 * D ^ 2 * e ^ 3)) * (N : ℝ) ^ (-10 : ℝ) ≤ (N : ℝ) ^ τb ∧
      5 * (N : ℝ) ^ τb ≤ (N : ℝ) ^ (5 * εg / 2) ∧
      5 * e ^ 2 * (N : ℝ) ^ (2 * εg) ≤ (N : ℝ) ^ (5 * εg / 2) ∧
      10 * e ^ 2 * (1 + (εg / 2)⁻¹) * (N : ℝ) ^ (τb + εg / 2) ≤ (N : ℝ) ^ (5 * εg / 2) ∧
      5 * e ^ 4 * (N : ℝ) ^ (5 * εg - C₀ * εg) ≤ (N : ℝ) ^ (5 * εg / 2) ∧
      e * (N : ℝ) ^ (0 : ℝ) ≤ (N : ℝ) ^ τ' ∧
      4 * (N : ℝ) ^ τb ≤ (N : ℝ) ^ τ' ∧
      8 * e ^ 2 * (1 + (τ' / 4)⁻¹) * (N : ℝ) ^ (τb + τ' / 4) ≤ (N : ℝ) ^ τ' ∧
      4 * e ^ 4 * (N : ℝ) ^ (5 * εg - C₀ * εg) ≤ (N : ℝ) ^ τ' := by
    have t1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    have t2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-εg)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hεg).comp tendsto_natCast_atTop_atTop
    refine (Filter.eventually_ge_atTop Nd).and ((Filter.eventually_ge_atTop Nm).and
      ((Filter.eventually_ge_atTop Ng).and ((Filter.eventually_ge_atTop 2).and
      (((t1.const_mul 2).eventually (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 10))).and
      (((t2.const_mul c).eventually (Iic_mem_nhds (by simp : c * 0 < 1))).and
      ((LF1_ev_pow _ _ _ (by linarith)).and ((LF1_ev_pow _ _ _ (by linarith)).and
      ((LF1_ev_pow _ _ _ (by linarith)).and ((LF1_ev_pow _ _ _ (by linarith)).and
      ((LF1_ev_pow _ _ _ (by linarith)).and ((LF1_ev_pow _ _ _ (by linarith)).and
      ((LF1_ev_pow _ _ _ (by linarith)).and ((LF1_ev_pow _ _ _ (by nlinarith)).and
      ((LF1_ev_pow _ _ _ (by linarith)).and ((LF1_ev_pow _ _ _ (by linarith)).and
      ((LF1_ev_pow _ _ _ (by linarith)).and
      (LF1_ev_pow _ _ _ (by nlinarith))))))))))))))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ₀ hμ₀ A z S hadm K hK1 hK2 z₁ z₂ h₁ h₂ => ?_⟩
  obtain ⟨hNd', hNm', hNg', hN2, hAN, hcN, hE3, hE4a, hE4b, hE4c, hE5a, hE5b, hE5c, hE5d, hE6,
    hE7a, hE7b, hE7c⟩ := hN₀ N hN
  haveI := hμ₀.prob
  haveI : NeZero D := ⟨by omega⟩
  haveI : NeZero N := ⟨by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hadm' := hadm
  obtain ⟨hΛ10, hzτ, hz, hm1, hq0, hq1, hS0, hSt, hη⟩ :=
    LF1_adm D N hD1 hN2 δA τ τe εg c C₀ hεg (by linarith) A z S hadm hAN hcN
  have hK1' : 1 ≤ K := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ Cg := Real.one_le_rpow hNr (by linarith)
    exact_mod_cast this.trans hK1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1'
  have hNτ : 1 ≤ (N : ℝ) ^ τ' := Real.one_le_rpow hNr hτ'.le
  set q₀ := flowTc (lam D N A) z with hq₀
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
    have hι0 : 0 < flowIm (lam D N A) z 0 := by
      obtain ⟨-, hιeq, hι, -⟩ := LF1_flow D N hD1 hN1 A hΛ10 z hz 0 hSt 0 le_rfl le_rfl
      rw [hιeq]; exact mul_pos (Real.exp_pos _) hι
    have hempty : {ω : GridΩA D N K |
        N * q₀ ^ 2 * (mExt (lam D N A) z).im ^ 2 *
            hsNorm (Lmat (lam D N A) (gridStateA D N K (0 / K) ω 0) z₁ z₂ -
              KTheta (lam D N A) θ z₁ z₂) ≤ (N : ℝ) ^ (2 * εg) ∧
          ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ' *
            ((q₀ / (q₀ - k * (0 / K))) ^ 2 *
                hsNorm (Lmat (lam D N A) (gridStateA D N K (0 / K) ω 0) z₁ z₂ -
                  KTheta (lam D N A) θ z₁ z₂) +
              1 / (N * (q₀ - k * (0 / K)) ^ 2 * flowIm (lam D N A) z (k * (0 / K)) ^ 2)) <
            hsNorm (flowLmat (lam D N A) z₁ z₂ (k * (0 / K)) (gridStateA D N K (0 / K) ω k) -
              flowKmat (lam D N A) θ z₁ z₂ (k * (0 / K)))} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
      intro _ k _ hlt
      obtain ⟨z0L, z0K, -⟩ := LF1_zero (lam D N A) θ z z₁ z₂ ω.1
      rw [hst, hst] at hlt
      simp only [zero_div, mul_zero, sub_zero, z0L, z0K] at hlt
      have hX := Real.sqrt_nonneg (∑ i, ∑ j, ‖(Lmat (lam D N A) ω.1 z₁ z₂ -
        KTheta (lam D N A) θ z₁ z₂) i j‖ ^ 2)
      have hq : q₀ / q₀ = 1 := div_self hq0.ne'
      rw [hq, one_pow, one_mul] at hlt
      have hp : 0 < 1 / (N * q₀ ^ 2 * flowIm (lam D N A) z 0 ^ 2) := by positivity
      have : hsNorm (Lmat (lam D N A) ω.1 z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) <
          (N : ℝ) ^ τ' * (hsNorm (Lmat (lam D N A) ω.1 z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) +
            1 / (N * q₀ ^ 2 * flowIm (lam D N A) z 0 ^ 2)) := by
        have h0 := Real.sqrt_nonneg (∑ i, ∑ j, ‖(Lmat (lam D N A) ω.1 z₁ z₂ -
          KTheta (lam D N A) θ z₁ z₂) i j‖ ^ 2)
        unfold hsNorm at hlt ⊢
        nlinarith
      unfold hsNorm at hlt this
      linarith
    rw [hempty, measure_empty]
    exact bot_le
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
  have hKh2 : (K : ℝ) * (S / K) ^ 2 ≤ (N : ℝ) ^ (-(31 : ℝ)) := by
    have : (K : ℝ) * (S / K) ^ 2 = S * (S / K) := by field_simp
    rw [this]
    calc S * (S / K) ≤ 1 * (S / K) := mul_le_mul_of_nonneg_right hS1 hhpos.le
      _ ≤ _ := by rw [one_mul]; exact hh31
  -- `q₀ ≤ c N^{-ε_g}` and `q₀ - S ≥ (eN)⁻¹`
  have hq0c : q₀ ≤ c * (N : ℝ) ^ (-εg) := by
    have hι := (LF1_flow D N hD1 hN1 A hΛ10 z hz S hSt 0 le_rfl hSpos.le).2.2.1
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + z.im / (mExt (lam D N A) z).im by
      have := div_pos hz hι; linarith)
    have h2 := hadm.2.2.2.2.2.1
    change Real.log (1 + z.im / (mExt (lam D N A) z).im) ≤ _
    linarith
  have hqK : (e * N)⁻¹ ≤ q₀ - S := by
    obtain ⟨-, hιeq, hι0, hιS1, -, -, -⟩ :=
      LF1_flow D N hD1 hN1 A hΛ10 z hz S hSt S hSpos.le le_rfl
    have hup := LF1_flow_up D N hD1 hN1 A hΛ10 z hz S hSt hq1 S hSpos.le le_rfl
    have hιS : 0 < flowIm (lam D N A) z S := by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0
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
          have hl := LF1_log_le N (εg / 2) hNr (by positivity)
          have hpow : (N : ℝ) ^ (εg / 2) * (N : ℝ) ^ (-εg) = (N : ℝ) ^ (-(εg / 2)) := by
            rw [← Real.rpow_add hNpos]; ring_nf
          have h0 : (N : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero _
          rw [h0] at hE3
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
  -- the arithmetic conditions of the bootstrap
  have h0 : (N : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero _
  have he1 : 1 ≤ e := Real.one_le_exp (by norm_num)
  have hεs : (N : ℝ) ^ (τb / 4) + e * D ^ 2 * (N : ℝ) ^ (3 * (τb / 12)) + D ^ 2 * N *
      ((N : ℝ) ^ (20 : ℝ) + ((D : ℝ) * (e * N) ^ 2 + e * N) * (3 + 2 * D * (e * N))) *
        (K * (S / K) ^ 2) ≤ (N : ℝ) ^ τb := by
    have hL : ((D : ℝ) * (e * N) ^ 2 + e * N) * (3 + 2 * D * (e * N)) ≤
        10 * D ^ 2 * e ^ 3 * (N : ℝ) ^ 3 := by
      have h1 : (D : ℝ) * (e * N) ^ 2 + e * N ≤ 2 * D * (e * N) ^ 2 := by nlinarith
      have h2 : 3 + 2 * D * (e * N) ≤ 5 * D * (e * N) := by nlinarith
      calc ((D : ℝ) * (e * N) ^ 2 + e * N) * (3 + 2 * D * (e * N))
          ≤ (2 * D * (e * N) ^ 2) * (5 * D * (e * N)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 10 * D ^ 2 * e ^ 3 * (N : ℝ) ^ 3 := by ring
    have hN20 : (N : ℝ) ^ (20 : ℝ) = (N : ℝ) ^ (20 : ℕ) := by norm_cast
    have hN10 : (N : ℝ) ^ (-10 : ℝ) = ((N : ℝ) ^ (10 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hNpos.le]; norm_cast
    have hN31 : (N : ℝ) ^ (-(31 : ℝ)) = ((N : ℝ) ^ (31 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hNpos.le]; norm_cast
    have h3 : (D : ℝ) ^ 2 * N * ((N : ℝ) ^ (20 : ℝ) + ((D : ℝ) * (e * N) ^ 2 + e * N) *
        (3 + 2 * D * (e * N))) * (K * (S / K) ^ 2) ≤
        D ^ 2 * (1 + 10 * D ^ 2 * e ^ 3) * (N : ℝ) ^ (-10 : ℝ) := by
      have hX : 0 ≤ (N : ℝ) ^ (20 : ℝ) + ((D : ℝ) * (e * N) ^ 2 + e * N) *
          (3 + 2 * D * (e * N)) := by positivity
      calc (D : ℝ) ^ 2 * N * ((N : ℝ) ^ (20 : ℝ) + ((D : ℝ) * (e * N) ^ 2 + e * N) *
            (3 + 2 * D * (e * N))) * (K * (S / K) ^ 2)
          ≤ (D : ℝ) ^ 2 * N * ((N : ℝ) ^ (20 : ℕ) + 10 * D ^ 2 * e ^ 3 * (N : ℝ) ^ 3) *
            ((N : ℝ) ^ (31 : ℕ))⁻¹ := by
            rw [← hN31, ← hN20]
            gcongr
        _ ≤ D ^ 2 * (1 + 10 * D ^ 2 * e ^ 3) * ((N : ℝ) ^ (10 : ℕ))⁻¹ := by
            rw [mul_comm ((D : ℝ) ^ 2 * N * _), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
            have hN3 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 20 := pow_le_pow_right₀ hNr (by norm_num)
            have hDe : 0 ≤ (10 : ℝ) * D ^ 2 * e ^ 3 := by positivity
            have : (D : ℝ) ^ 2 * (1 + 10 * D ^ 2 * e ^ 3) * ((N : ℝ) ^ 10)⁻¹ * N ^ 31 =
                D ^ 2 * (1 + 10 * D ^ 2 * e ^ 3) * N ^ 21 := by
              field_simp
            rw [this]
            have : (D : ℝ) ^ 2 * N * ((N : ℝ) ^ 20 + 10 * D ^ 2 * e ^ 3 * N ^ 3) ≤
                D ^ 2 * N * ((N : ℝ) ^ 20 + 10 * D ^ 2 * e ^ 3 * N ^ 20) := by gcongr
            calc (D : ℝ) ^ 2 * N * ((N : ℝ) ^ 20 + 10 * D ^ 2 * e ^ 3 * N ^ 3) ≤
                D ^ 2 * N * ((N : ℝ) ^ 20 + 10 * D ^ 2 * e ^ 3 * N ^ 20) := this
              _ = D ^ 2 * (1 + 10 * D ^ 2 * e ^ 3) * N ^ 21 := by ring
        _ = D ^ 2 * (1 + 10 * D ^ 2 * e ^ 3) * (N : ℝ) ^ (-10 : ℝ) := by rw [hN10]
    linarith
  have hΘ0 : 0 < (N : ℝ) ^ (5 * εg / 2) := Real.rpow_pos_of_pos hNpos _
  have hΘsq : ((N : ℝ) ^ (5 * εg / 2)) ^ 2 / (N : ℝ) ^ (C₀ * εg) =
      (N : ℝ) ^ (5 * εg - C₀ * εg) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, Real.rpow_sub hNpos]
    norm_num
  have hlogτb : 2 * e ^ 2 * (N : ℝ) ^ τb * Real.log (e * N) ≤
      2 * e ^ 2 * (1 + (εg / 2)⁻¹) * (N : ℝ) ^ (τb + εg / 2) := by
    have hl := LF1_log_le N (εg / 2) hNr (by positivity)
    rw [Real.rpow_add hNpos]
    have := Real.rpow_nonneg hNpos.le τb
    have : 0 ≤ 2 * e ^ 2 * (N : ℝ) ^ τb := by positivity
    calc 2 * e ^ 2 * (N : ℝ) ^ τb * Real.log (e * N) ≤
        2 * e ^ 2 * (N : ℝ) ^ τb * ((1 + (εg / 2)⁻¹) * (N : ℝ) ^ (εg / 2)) :=
          mul_le_mul_of_nonneg_left hl this
      _ = _ := by ring
  have hΘ : (N : ℝ) ^ τb + e ^ 2 * (N : ℝ) ^ (2 * εg) +
      2 * e ^ 2 * (N : ℝ) ^ τb * Real.log (e * N) +
      e ^ 4 * ((N : ℝ) ^ (5 * εg / 2)) ^ 2 / (N : ℝ) ^ (C₀ * εg) < (N : ℝ) ^ (5 * εg / 2) := by
    rw [mul_div_assoc, hΘsq]
    linarith
  have hfin1 : e ≤ (N : ℝ) ^ τ' := by rw [h0, mul_one] at hE6; exact hE6
  have hfin2 : (N : ℝ) ^ τb + 2 * e ^ 2 * (N : ℝ) ^ τb * Real.log (e * N) +
      e ^ 4 * ((N : ℝ) ^ (5 * εg / 2)) ^ 2 / (N : ℝ) ^ (C₀ * εg) ≤ (N : ℝ) ^ τ' := by
    rw [mul_div_assoc, hΘsq]
    have hl := LF1_log_le N (τ' / 4) hNr (by positivity)
    have h1 : 2 * e ^ 2 * (N : ℝ) ^ τb * Real.log (e * N) ≤
        2 * e ^ 2 * (1 + (τ' / 4)⁻¹) * (N : ℝ) ^ (τb + τ' / 4) := by
      rw [Real.rpow_add hNpos]
      have : 0 ≤ 2 * e ^ 2 * (N : ℝ) ^ τb := by
        have := Real.rpow_nonneg hNpos.le τb; positivity
      calc 2 * e ^ 2 * (N : ℝ) ^ τb * Real.log (e * N) ≤
          2 * e ^ 2 * (N : ℝ) ^ τb * ((1 + (τ' / 4)⁻¹) * (N : ℝ) ^ (τ' / 4)) :=
            mul_le_mul_of_nonneg_left hl this
        _ = _ := by ring
    have hNt : 0 ≤ (N : ℝ) ^ τ' := Real.rpow_nonneg hNpos.le _
    linarith
  -- the three exceptional sets
  have hBg := hNg N hNg' θ hθ0 hθ1 μ₀ hμ₀ A z S hadm' K hK1' hK2
  have hBm := hNm N hNm' θ hθ0 hθ1 μ₀ hμ₀ A z S hadm' K hK1 hK2 z₁ z₂ h₁ h₂
  set NH := {ω : GridΩA D N K | ¬ (Matrix.of ω.1).IsHermitian} with hNH
  have hNH0 : gridLawA D N K μ₀ NH = 0 := by
    have hT : MeasurableSet {H : Idx D N → Idx D N → ℂ | ¬ (Matrix.of H).IsHermitian} :=
      LF1_herm_meas.compl
    have e1 : NH = Prod.fst ⁻¹' {H : Idx D N → Idx D N → ℂ | ¬ (Matrix.of H).IsHermitian} := rfl
    rw [e1, ← Measure.map_apply measurable_fst hT]
    unfold gridLawA
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_iff.1 hμ₀.herm
  have hτ32 : τb / 4 / 8 = τb / 32 := by ring
  refine (measure_mono (t := ({ω | ∃ k : ℕ, k ≤ K ∧ ¬ flowGoodAt A z (τb / 32) (k * (S / K))
      (gridStateA D N K (S / K) ω k)} ∪ {ω | ∃ n : ℕ, n ≤ K ∧
        (∀ j : ℕ, j < n → flowGoodAt A z (τb / 4 / 8) (j * (S / K))
          (gridStateA D N K (S / K) ω j)) ∧
        (N : ℝ) ^ (τb / 4) / (N * (q₀ - n * (S / K)) * flowIm (lam D N A) z (n * (S / K)) ^ 2) <
          hsNorm (∑ j ∈ Finset.range n, ((q₀ - (j + 1) * (S / K) : ℝ) : ℂ) •
            (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K)) (gridStateA D N K (S / K) ω (j + 1)) -
              Matrix.of fun x y => ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
                (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                  Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
                ∂(gueBlocks D N)))}) ∪ NH) ?_).trans ?_
  · rintro ω ⟨hinit, k, hk, hlt⟩
    by_contra hω
    simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, not_exists, not_and, not_not, hNH]
      at hω
    obtain ⟨⟨hωg, hωm⟩, hherm⟩ := hω
    have hgood : ∀ j, j ≤ K → flowGoodAt A z (τb / 32) (j * (S / K))
        (gridStateA D N K (S / K) ω j) := hωg
    have hfl : ∀ j, j ≤ K → 0 < (charFlowZ (lam D N A) z (j * (S / K))).im ∧
        0 < flowIm (lam D N A) z (j * (S / K)) := by
      intro j hj
      have h0 : 0 ≤ (j : ℝ) * (S / K) := by positivity
      have hjS : (j : ℝ) * (S / K) ≤ S :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hhpos.le).trans_eq hKh
      obtain ⟨hηj, hιeq, hι0, -⟩ := LF1_flow D N hD1 hN1 A hΛ10 z hz S hSt _ h0 hjS
      exact ⟨hηj, by rw [hιeq]; exact mul_pos (Real.exp_pos _) hι0⟩
    have hdrift : ∀ j, j < K → ∀ x y : Fin D,
        ‖(∫ X, ((flowTc (lam D N A) z - (j * (S / K) + S / K) : ℝ) : ℂ) *
              flowLmat (lam D N A) z₁ z₂ (j * (S / K) + S / K)
                (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                  Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N)) -
            ((flowTc (lam D N A) z - j * (S / K) : ℝ) : ℂ) *
              flowLmat (lam D N A) z₁ z₂ (j * (S / K)) (gridStateA D N K (S / K) ω j) x y -
            ((S / K : ℝ) : ℂ) * (((flowTc (lam D N A) z - j * (S / K) - 1 : ℝ) : ℂ) *
                flowLmat (lam D N A) z₁ z₂ (j * (S / K)) (gridStateA D N K (S / K) ω j) x y +
              ((flowTc (lam D N A) z - j * (S / K) : ℝ) : ℂ) *
                (flowLmat (lam D N A) z₁ z₂ (j * (S / K)) (gridStateA D N K (S / K) ω j) *
                  flowLmat (lam D N A) z₁ z₂ (j * (S / K)) (gridStateA D N K (S / K) ω j)) x y)‖ ≤
          S / K * ((N : ℝ) ^ (3 * (τb / 12)) / (N * (flowTc (lam D N A) z - j * (S / K)) ^ 2 *
            flowIm (lam D N A) z (j * (S / K)) ^ 2)) + (S / K) ^ 2 * (N : ℝ) ^ (20 : ℝ) := by
      intro j hj x y
      have hsh : (j : ℝ) * (S / K) + S / K ≤ S := by
        have : ((j + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hj
        have := (mul_le_mul_of_nonneg_right this hhpos.le).trans_eq hKh
        push_cast at this; linarith
      have hg := LF1_good_mono hN1 A z (τb / 32) (τb / 12) (j * (S / K)) (by linarith) _
        (hfl j hj.le).1 (hfl j hj.le).2 (hgood j hj.le)
      exact hNd N hNd' A z S hadm' (j * (S / K)) (S / K) (by positivity) hhpos hsh hh31 _
        (LF1_states_herm D N K (S / K) ω hherm j) hg z₁ z₂ h₁ h₂ x y
    have hmart : ∀ n, n ≤ K → hsNorm (∑ j ∈ Finset.range n,
        ((flowTc (lam D N A) z - (j + 1) * (S / K) : ℝ) : ℂ) •
          (flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K)) (gridStateA D N K (S / K) ω (j + 1)) -
            Matrix.of fun x y => ∫ X, flowLmat (lam D N A) z₁ z₂ ((j + 1) * (S / K))
              (Real.exp (-(S / K) / 2) • gridStateA D N K (S / K) ω j +
                Real.sqrt (1 - Real.exp (-(S / K))) • Matrix.of.symm (blockH D N X)) x y
              ∂(gueBlocks D N))) ≤
        (N : ℝ) ^ (τb / 4) / (N * (flowTc (lam D N A) z - n * (S / K)) *
          flowIm (lam D N A) z (n * (S / K)) ^ 2) := by
      intro n hn
      have h1 := hωm n hn (fun j hj => by rw [hτ32]; exact hgood j (by omega))
      exact not_lt.1 h1
    have hb := LF1_boot D N K hK1' A z S hΛ10 hz hSpos hSt hq1
      (fun s hs0 hsS => (hη s hs0 hsS).1) (C₀ * εg) (fun s hs0 hsS => (hη s hs0 hsS).2) θ hθ0
      hθ1 z₁ z₂ h₁ h₂ (fun j => gridStateA D N K (S / K) ω j) (3 * (τb / 12)) (τb / 4)
      ((N : ℝ) ^ τb) ((N : ℝ) ^ (2 * εg)) ((N : ℝ) ^ (5 * εg / 2)) τ' hdrift hmart hinit hγ hlog
      hεs hΘ hfin1 hfin2 k hk
    linarith
  · refine (measure_union_le _ _).trans ?_
    rw [hNH0, add_zero]
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add hBg hBm).trans ?_
    rw [← ENNReal.ofReal_add (Real.rpow_nonneg hNpos.le _)
      (div_nonneg (Real.rpow_nonneg hNpos.le _) (by norm_num))]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : (N : ℝ) ^ (-(D' + 1)) = (N : ℝ) ^ (-D') * (N : ℝ)⁻¹ := by
      rw [show -(D' + 1) = -D' + -1 by ring, Real.rpow_add hNpos, Real.rpow_neg_one]
    rw [e1]
    have hNinv : (N : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hNpos (by norm_num)]; norm_num
      exact_mod_cast hN2
    have := Real.rpow_nonneg hNpos.le (-D')
    nlinarith

/-- Lemma 3.8 [lem_flow_1], (3.26) [flow_1_result], on the grid, conditional form: on one grid of
`K ∈ [N^{C_g}, N^{C_g+1}]` steps, `C_g ≥ 31 + D'`, of `[0, S]` from any class member `μ₀`, the
event that the start satisfies `N q₀² (Im m)² ‖L_0 - K_θ‖₂ ≤ N^{2ε_g}` and (3.26) fails at some
grid time `u_k = k S / K`, `‖L_k - K_k‖₂ > N^{τ'} ((q₀/q_k)² ‖L_0 - K_θ‖₂ + 1/(N q_k² (Im m_k)²))`,
has probability at most `N^{-D'}`; `q_k = t_c - t₀ - u_k`, `K_k` with the parameter `θ_{u_k}`. -/
theorem flowL2_grid (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∀ Cg : ℝ, 31 + D' ≤ Cg → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ K : ℕ, (N : ℝ) ^ Cg ≤ K → (K : ℝ) ≤ (N : ℝ) ^ (Cg + 1) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        gridLawA D N K μ₀ {ω |
          N * flowTc (lam D N A) z ^ 2 * (mExt (lam D N A) z).im ^ 2 *
              hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0) z₁ z₂ -
                KTheta (lam D N A) θ z₁ z₂) ≤ (N : ℝ) ^ (2 * εg) ∧
            ∃ k : ℕ, k ≤ K ∧ (N : ℝ) ^ τ' *
              ((flowTc (lam D N A) z / (flowTc (lam D N A) z - k * (S / K))) ^ 2 *
                  hsNorm (Lmat (lam D N A) (gridStateA D N K (S / K) ω 0) z₁ z₂ -
                    KTheta (lam D N A) θ z₁ z₂) +
                1 / (N * (flowTc (lam D N A) z - k * (S / K)) ^ 2 *
                  flowIm (lam D N A) z (k * (S / K)) ^ 2)) <
              hsNorm (flowLmat (lam D N A) z₁ z₂ (k * (S / K)) (gridStateA D N K (S / K) ω k) -
                flowKmat (lam D N A) θ z₁ z₂ (k * (S / K)))} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  exact LF1_grid_core D hD δA τ τe εg c C₀ hδA hτ hτe hεg hεg₁ hεg₂ hC₀ hc C

end RBMTransitionEdge

end
