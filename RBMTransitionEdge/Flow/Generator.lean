module

public import RBMTransitionEdge.Flow.LoopReg
public import RBMTransitionEdge.Prob.Underline

@[expose] public section

/-!
# The generator along the characteristic flow: M9

(3.48)–(3.51) for one, two and three resolvents along the flow (3.10) [eq:deterflow] before any
local law is used, the drift of (3.53) [ItowtL], and the quadratic variation (3.56) [eq:quad_var]
of a loop in one step.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Entrywise derivatives of matrix functions of one real variable -/

section Calc

variable {ι : Type*}

/-- Entrywise derivative of a matrix-valued function of one real variable at `t`. -/
private def Generator_MHD (A : ℝ → Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) (t : ℝ) : Prop :=
  ∀ k l, HasDerivAt (fun s => A s k l) (A' k l) t

private lemma Generator_MHD.congr {A : ℝ → Matrix ι ι ℂ} {A' A'' : Matrix ι ι ℂ} {t : ℝ}
    (h : Generator_MHD A A' t) (e : A' = A'') : Generator_MHD A A'' t := e ▸ h

private lemma Generator_MHD.mul [Fintype ι] {A B : ℝ → Matrix ι ι ℂ} {A' B' : Matrix ι ι ℂ} {t : ℝ}
    (hA : Generator_MHD A A' t) (hB : Generator_MHD B B' t) :
    Generator_MHD (fun s => A s * B s) (A' * B t + A t * B') t := by
  intro k l
  simp only [Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun m _ => (hA k m).mul (hB m l)

private lemma Generator_MHD.const (C : Matrix ι ι ℂ) (t : ℝ) :
    Generator_MHD (fun _ => C) 0 t := fun k l => by
  simpa using hasDerivAt_const t (C k l)

private lemma Generator_MHD.mulc [Fintype ι] {A : ℝ → Matrix ι ι ℂ} {A' : Matrix ι ι ℂ} {t : ℝ}
    (hA : Generator_MHD A A' t) (C : Matrix ι ι ℂ) :
    Generator_MHD (fun s => A s * C) (A' * C) t :=
  (hA.mul (Generator_MHD.const C t)).congr (by simp)

private lemma Generator_MHD.add {A B : ℝ → Matrix ι ι ℂ} {A' B' : Matrix ι ι ℂ} {t : ℝ}
    (hA : Generator_MHD A A' t) (hB : Generator_MHD B B' t) :
    Generator_MHD (fun s => A s + B s) (A' + B') t := fun k l => by
  simpa using (hA k l).fun_add (hB k l)

private lemma Generator_MHD.sub {A B : ℝ → Matrix ι ι ℂ} {A' B' : Matrix ι ι ℂ} {t : ℝ}
    (hA : Generator_MHD A A' t) (hB : Generator_MHD B B' t) :
    Generator_MHD (fun s => A s - B s) (A' - B') t := fun k l => by
  simpa using (hA k l).fun_sub (hB k l)

private lemma Generator_MHD.smul {A : ℝ → Matrix ι ι ℂ} {c : ℝ → ℂ} {A' : Matrix ι ι ℂ}
    {c' : ℂ} {t : ℝ} (hc : HasDerivAt c c' t) (hA : Generator_MHD A A' t) :
    Generator_MHD (fun s => c s • A s) (c' • A t + c t • A') t := fun k l => by
  simpa using hc.fun_mul (hA k l)

/-- The normalized trace of an entrywise derivative. -/
private lemma Generator_MHD.ntr [Fintype ι] {A : ℝ → Matrix ι ι ℂ} {A' : Matrix ι ι ℂ} {t : ℝ}
    (hA : Generator_MHD A A' t) : HasDerivAt (fun s => ntr (A s)) (ntr A') t := by
  unfold RBMTransitionEdge.ntr Matrix.trace
  exact (HasDerivAt.fun_sum fun k _ => hA k k).const_mul _

variable [Fintype ι] [DecidableEq ι]

/-- The determinant of an entrywise differentiable matrix function is differentiable. -/
private lemma Generator_det_diff (M : ℝ → Matrix ι ι ℂ) (t : ℝ)
    (hd : ∀ k l, DifferentiableAt ℝ (fun s => M s k l) t) :
    DifferentiableAt ℝ (fun s => (M s).det) t := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  exact (differentiableAt_const _).mul (DifferentiableAt.fun_finsetProd fun i _ => hd _ _)

/-- The derivative of the inverse: `(M⁻¹)' = -M⁻¹ M' M⁻¹` at an invertible point. -/
private lemma Generator_MHD.inv {M : ℝ → Matrix ι ι ℂ} {M' B : Matrix ι ι ℂ} {t : ℝ}
    (hM : Generator_MHD M M' t) (h1 : M t * B = 1) (h2 : B * M t = 1) :
    Generator_MHD (fun s => (M s)⁻¹) (-(B * M' * B)) t := by
  have hd : ∀ k l, DifferentiableAt ℝ (fun s => M s k l) t := fun k l => (hM k l).differentiableAt
  have hdet := Generator_det_diff M t hd
  have hdet0 : (M t).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hid : ∀ k l, DifferentiableAt ℝ (fun s => (M s)⁻¹ k l) t := by
    intro k l
    have e : (fun s => (M s)⁻¹ k l) = fun s => ((M s).det)⁻¹ * (M s).adjugate k l := by
      funext s
      rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
    rw [e]
    refine (hdet.inv hdet0).mul ?_
    simp only [Matrix.adjugate_apply]
    refine Generator_det_diff _ t fun a b => ?_
    by_cases ha : a = l
    · simp only [Matrix.updateRow_apply, ha, ite_true]
      exact differentiableAt_const _
    · simp only [Matrix.updateRow_apply, ha, ite_false]
      exact hd a b
  set G' : Matrix ι ι ℂ := Matrix.of fun k l => deriv (fun s => (M s)⁻¹ k l) t with hG'
  have hG : Generator_MHD (fun s => (M s)⁻¹) G' t := fun k l => (hid k l).hasDerivAt
  have hP := hM.mul hG
  have hev : ∀ᶠ s in nhds t, M s * (M s)⁻¹ = 1 := by
    filter_upwards [hdet.continuousAt.eventually_ne hdet0] with s hs
    exact Matrix.mul_nonsing_inv _ (Ne.isUnit hs)
  have hzero : M' * (M t)⁻¹ + M t * G' = 0 := by
    ext k l
    have h0 : HasDerivAt (fun s => (M s * (M s)⁻¹) k l) 0 t := by
      refine (hasDerivAt_const t ((1 : Matrix ι ι ℂ) k l)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with s hs
      rw [hs]
    exact (hP k l).unique h0
  have hBinv : (M t)⁻¹ = B := Matrix.inv_eq_right_inv h1
  rw [hBinv] at hzero
  have : G' = -(B * M' * B) := by
    have e1 : G' = B * (M t * G') := by rw [← mul_assoc, h2, one_mul]
    rw [e1, eq_neg_of_add_eq_zero_right hzero]
    noncomm_ring
  exact hG.congr this

/-- The derivative of a resolvent `(X_s - w_s)⁻¹` along a differentiable Hermitian path. -/
private lemma Generator_MHD.res {X : ℝ → Matrix ι ι ℂ} {X' : Matrix ι ι ℂ} {w : ℝ → ℂ} {w' : ℂ}
    {t : ℝ} (hX : Generator_MHD X X' t) (hw : HasDerivAt w w' t) (hH : (X t).IsHermitian)
    (him : (w t).im ≠ 0) :
    Generator_MHD (fun s => res (X s) (w s))
      (-(res (X t) (w t) * (X' - w' • (1 : Matrix ι ι ℂ)) * res (X t) (w t))) t := by
  obtain ⟨h1, h2⟩ := res_mul_sub_of_im_ne (X t) hH (w t) him
  have hM : Generator_MHD (fun s => X s - w s • (1 : Matrix ι ι ℂ))
      (X' - w' • (1 : Matrix ι ι ℂ)) t :=
    (hX.sub (Generator_MHD.smul hw (Generator_MHD.const 1 t))).congr (by simp)
  exact hM.inv h1 h2

end Calc


/-! ### Second moments of the block GUE -/

section Prob

/-- Every absolute moment of a centred real Gaussian law is finite. -/
private lemma Generator_G_int (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 v) := by
  have := (memLp_id_gaussianReal' (μ := 0) (v := v) ((k : ℕ) : ENNReal)
    (by simp)).integrable_norm_pow'
  simpa using this

/-- The identity is integrable against a centred real Gaussian law. -/
private lemma Generator_G_int1 (v : ℝ≥0) : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal' (μ := 0) (v := v) 1 (by simp)).integrable le_rfl

/-- The second moment of `N(0, v)` is `v`. -/
private lemma Generator_G_sq (v : ℝ≥0) : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- `x²` is integrable against a centred real Gaussian law. -/
private lemma Generator_G_int_sq (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
  simpa [sq_abs] using Generator_G_int v 2

/-- Integrals against `cGauss` as integrals against `N(0, 1/2) ⊗ N(0, 1/2)`. -/
private lemma Generator_c_integral (f : ℂ → ℂ) (hf : Continuous f) :
    ∫ z, f z ∂(cGauss : Measure ℂ) =
      ∫ p : ℝ × ℝ, f ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
        ∂((gaussianReal 0 (1 / 2 : ℝ≥0)).prod (gaussianReal 0 (1 / 2 : ℝ≥0))) := by
  have hm : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  change ∫ z, f z ∂(((gaussianReal 0 (1 / 2 : ℝ≥0)).prod
    (gaussianReal 0 (1 / 2 : ℝ≥0))).map fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) = _
  exact integral_map hm.aemeasurable hf.aestronglyMeasurable

/-- Every absolute moment of `cGauss` is finite. -/
private lemma Generator_c_int (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ k) (cGauss : Measure ℂ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact (IsGaussian.memLp_id (cGauss : Measure ℂ) (k : ENNReal) (by simp)).integrable_norm_pow
      hk.ne'

/-- `cGauss` has mean zero. -/
private lemma Generator_c_mean : ∫ z : ℂ, z ∂(cGauss : Measure ℂ) = 0 := by
  set G := gaussianReal 0 (1 / 2 : ℝ≥0) with hG
  rw [Generator_c_integral (fun z => z) continuous_id]
  have h1 : Integrable (fun p : ℝ × ℝ => (p.1 : ℂ)) (G.prod G) :=
    ((Generator_G_int1 _).comp_fst G).ofReal
  have h2 : Integrable (fun p : ℝ × ℝ => (p.2 : ℂ) * Complex.I) (G.prod G) :=
    (((Generator_G_int1 _).comp_snd G).ofReal).mul_const _
  rw [integral_add h1 h2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_fun_fst (fun x : ℝ => x), integral_fun_snd (fun x : ℝ => x)]
  simp [hG]

/-- `E|z|² = 1` for `cGauss`. -/
private lemma Generator_c_var : ∫ z : ℂ, ‖z‖ ^ 2 ∂(cGauss : Measure ℂ) = 1 := by
  set G := gaussianReal 0 (1 / 2 : ℝ≥0) with hG
  have hm : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  have e0 : ∫ z : ℂ, ‖z‖ ^ 2 ∂(cGauss : Measure ℂ) =
      ∫ p : ℝ × ℝ, ‖(p.1 : ℂ) + (p.2 : ℂ) * Complex.I‖ ^ 2 ∂(G.prod G) := by
    change ∫ z, ‖z‖ ^ 2 ∂((G.prod G).map fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) = _
    exact integral_map hm.aemeasurable (by fun_prop)
  have e : ∀ p : ℝ × ℝ, ‖(p.1 : ℂ) + (p.2 : ℂ) * Complex.I‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    intro p
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [e0]
  simp only [e]
  rw [integral_add ((Generator_G_int_sq _).comp_fst G) ((Generator_G_int_sq _).comp_snd G),
    integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2), hG,
    Generator_G_sq]
  norm_num

/-- `E z² = 0` for `cGauss`. -/
private lemma Generator_c_pseudo : ∫ z : ℂ, z ^ 2 ∂(cGauss : Measure ℂ) = 0 := by
  set G := gaussianReal 0 (1 / 2 : ℝ≥0) with hG
  rw [Generator_c_integral (fun z => z ^ 2) (by fun_prop)]
  have e : ∀ p : ℝ × ℝ, ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ^ 2 =
      ((p.1 ^ 2 : ℝ) : ℂ) - ((p.2 ^ 2 : ℝ) : ℂ) + (2 * Complex.I) * ((p.1 : ℂ) * (p.2 : ℂ)) := by
    intro p
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [e]
  have h1 : Integrable (fun p : ℝ × ℝ => ((p.1 ^ 2 : ℝ) : ℂ)) (G.prod G) :=
    ((Generator_G_int_sq _).comp_fst G).ofReal
  have h2 : Integrable (fun p : ℝ × ℝ => ((p.2 ^ 2 : ℝ) : ℂ)) (G.prod G) :=
    ((Generator_G_int_sq _).comp_snd G).ofReal
  have h3 : Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) * (p.2 : ℂ)) (G.prod G) :=
    Integrable.mul_prod (Generator_G_int1 _).ofReal (Generator_G_int1 _).ofReal
  have h12 : Integrable (fun p : ℝ × ℝ => ((p.1 ^ 2 : ℝ) : ℂ) - ((p.2 ^ 2 : ℝ) : ℂ))
      (G.prod G) := h1.sub h2
  rw [integral_add h12 (h3.const_mul _), integral_sub h1 h2, integral_const_mul,
    integral_prod_mul (fun x : ℝ => (x : ℂ)) (fun y : ℝ => (y : ℂ))]
  simp only [integral_complex_ofReal]
  rw [integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2),
    integral_complex_ofReal (f := fun x : ℝ => x)]
  simp [hG]

/-- The entry laws of the block GUE: `N(0, 1)` on the diagonal and `cGauss` above it. -/
private def Generator_LG : EntryLaws (fun k => (∫ x : ℝ, |x| ^ k ∂(gaussianReal 0 1)) +
    ∫ z : ℂ, ‖z‖ ^ k ∂(cGauss : Measure ℂ)) where
  νd := ⟨gaussianReal 0 1, inferInstance⟩
  νo := cGauss
  intd := fun p => Generator_G_int 1 p
  into := Generator_c_int
  meand := by
    change ∫ x : ℝ, x ∂(gaussianReal 0 1) = 0
    rw [integral_id_gaussianReal]
  vard := by
    change ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1
    rw [Generator_G_sq]
    simp
  meano := Generator_c_mean
  varo := Generator_c_var
  pseudo := Generator_c_pseudo
  moments := fun p => le_of_eq rfl

/-- The law of the block GUE is `blockLaw` of these entry laws. -/
private lemma Generator_gueBlocks_eq (D N : ℕ) : gueBlocks D N = blockLaw D N Generator_LG := rfl

variable {D N : ℕ}

/-- An entry of `blockH` as a continuous real-linear function of the coordinates. -/
private def Generator_entryL (D N : ℕ) (p q : Idx D N) : (Fin D → Coords N) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => blockH D N w p q
      map_add' := fun v w => by
        simp only [blockH]
        split_ifs
        · rw [Pi.add_apply, wig_add, Matrix.add_apply]
        · simp
      map_smul' := fun c w => by
        simp only [blockH, RingHom.id_apply]
        split_ifs
        · rw [Pi.smul_apply, wig_smul, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
        · simp }

/-- Each entry of `blockH` is square integrable under the block GUE. -/
private lemma Generator_memLp_entry (p q : Idx D N) :
    MemLp (fun w => blockH D N w p q) 2 (gueBlocks D N) :=
  (Generator_entryL D N p q).comp_memLp' (IsGaussian.memLp_id (gueBlocks D N) 2 (by simp))

/-- The product of two entries of `blockH` is integrable under the block GUE. -/
private lemma Generator_int_entry2 (p q r t : Idx D N) :
    Integrable (fun w => blockH D N w p q * blockH D N w r t) (gueBlocks D N) :=
  (Generator_memLp_entry p q).integrable_mul (Generator_memLp_entry r t)


/-- `D⟨G E_a⟩ = N⁻¹ Σ_j G_{(a,j),(a,j)}`. -/
private lemma Generator_D_ntr_Ea [NeZero D] (G : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D) :
    (D : ℂ) * ntr (G * Ea D N a) = (N : ℂ)⁻¹ * ∑ j : Fin N, G (a, j) (a, j) := by
  have hD : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne D)
  unfold ntr Ea
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_diagonal, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp only [ite_true]
  push_cast
  field_simp

/-- The entries of `E_a`. -/
private lemma Generator_Ea_apply (a : Fin D) (x y : Idx D N) :
    Ea D N a x y = if x = y ∧ x.1 = a then 1 else 0 := by
  unfold Ea
  rw [Matrix.diagonal_apply]
  by_cases h : x = y <;> simp [h]

/-- The expectation of `X G X` for the block GUE `X`: `E[X G X] = Σ_a D⟨G E_a⟩ E_a`,
entrywise. -/
private lemma Generator_EXGX [NeZero D] (G : Matrix (Idx D N) (Idx D N) ℂ) (x y : Idx D N) :
    ∫ w, (blockH D N w * G * blockH D N w) x y ∂(gueBlocks D N) =
      (∑ a : Fin D, ((D : ℂ) * ntr (G * Ea D N a)) • Ea D N a) x y := by
  rw [Generator_gueBlocks_eq, integral_blockH_mul_blockH, Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, Generator_Ea_apply]
  by_cases hxy : x = y
  · subst hxy
    simp only [true_and, ite_true, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single x.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), Generator_D_ntr_Ea]
  · simp [hxy]

/-- The entries of `A B C`. -/
private lemma Generator_mul3_apply {ι : Type*} [Fintype ι] (A B C : Matrix ι ι ℂ) (x y : ι) :
    (A * B * C) x y = ∑ p, ∑ q, B p q * (A x p * C q y) := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- The entries of `X G X` are integrable under the block GUE. -/
private lemma Generator_int_XGX (G : Matrix (Idx D N) (Idx D N) ℂ) (x y : Idx D N) :
    Integrable (fun w => (blockH D N w * G * blockH D N w) x y) (gueBlocks D N) := by
  simp only [Generator_mul3_apply]
  exact integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
    (Generator_int_entry2 x p q y).const_mul _

/-- `⟨P B R⟩` as a linear combination of the entries of `B`. -/
private lemma Generator_ntr_PBR {ι : Type*} [Fintype ι] (P R B : Matrix ι ι ℂ) :
    ntr (P * B * R) = ∑ x, ∑ y, ((Fintype.card ι : ℂ)⁻¹ * ∑ k, R y k * P k x) * B x y := by
  unfold ntr Matrix.trace
  simp only [Matrix.diag, Generator_mul3_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun k _ => by ring

/-- The integral of `⟨P M R⟩` for a matrix-valued `M` with integrable entries. -/
private lemma Generator_integral_ntr {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (P R : Matrix ι ι ℂ) (M : Ω → Matrix ι ι ℂ)
    (hM : ∀ x y, Integrable (fun ω => M ω x y) μ) :
    ∫ ω, ntr (P * M ω * R) ∂μ = ntr (P * Matrix.of (fun x y => ∫ ω, M ω x y ∂μ) * R) := by
  simp only [Generator_ntr_PBR, Matrix.of_apply]
  rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => (hM x y).const_mul _]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finsetSum _ fun y _ => (hM x y).const_mul _]
  exact Finset.sum_congr rfl fun y _ => integral_const_mul _ _

/-- `⟨P X Q X R⟩` is integrable under the block GUE. -/
private lemma Generator_int_PXQXR (P Q R : Matrix (Idx D N) (Idx D N) ℂ) :
    Integrable (fun w => ntr (P * blockH D N w * Q * blockH D N w * R)) (gueBlocks D N) := by
  have e : ∀ w, P * blockH D N w * Q * blockH D N w * R =
      P * (blockH D N w * Q * blockH D N w) * R := fun w => by simp only [Matrix.mul_assoc]
  simp only [e, Generator_ntr_PBR]
  exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    (Generator_int_XGX Q x y).const_mul _

/-- `⟨Σ_a c_a B_a⟩`-linearity: `⟨P (Σ_a c_a E_a) R⟩ = Σ_a c_a ⟨P E_a R⟩`. -/
private lemma Generator_ntr_sum_smul {ι α : Type*} [Fintype ι] (s : Finset α) (c : α → ℂ)
    (B : α → Matrix ι ι ℂ) (P R : Matrix ι ι ℂ) :
    ntr (P * (∑ a ∈ s, c a • B a) * R) = ∑ a ∈ s, c a * ntr (P * B a * R) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  unfold ntr
  rw [Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul]
  ring

/-- `E⟨P X Q X R⟩ = Σ_a D⟨Q E_a⟩⟨P E_a R⟩` for the block GUE `X`. -/
private lemma Generator_E_PXQXR [NeZero D] (P Q R : Matrix (Idx D N) (Idx D N) ℂ) :
    ∫ w, ntr (P * blockH D N w * Q * blockH D N w * R) ∂(gueBlocks D N) =
      ∑ a, (D : ℂ) * ntr (Q * Ea D N a) * ntr (P * Ea D N a * R) := by
  have e : ∀ w, P * blockH D N w * Q * blockH D N w * R =
      P * (blockH D N w * Q * blockH D N w) * R := fun w => by simp only [Matrix.mul_assoc]
  simp only [e]
  rw [Generator_integral_ntr _ P R _ (Generator_int_XGX Q)]
  have e2 : Matrix.of (fun x y => ∫ w, (blockH D N w * Q * blockH D N w) x y ∂(gueBlocks D N)) =
      ∑ a : Fin D, ((D : ℂ) * ntr (Q * Ea D N a)) • Ea D N a := by
    ext x y
    rw [Matrix.of_apply, Generator_EXGX]
  rw [e2, Generator_ntr_sum_smul]

/-- The covariance of two entries of the block GUE: `E X_{pq} X_{rt} = N⁻¹` if `p = t`,
`q = r` and `p, q` lie in one block, and `0` otherwise. -/
private lemma Generator_cov [NeZero D] (p q r t : Idx D N) :
    ∫ w, blockH D N w p q * blockH D N w r t ∂(gueBlocks D N) =
      if p = t ∧ q = r ∧ p.1 = q.1 then (N : ℂ)⁻¹ else 0 := by
  have e : ∀ w, blockH D N w p q * blockH D N w r t =
      (blockH D N w * Matrix.single q r (1 : ℂ) * blockH D N w) p t := by
    intro w
    rw [Generator_mul3_apply, Finset.sum_eq_single q, Finset.sum_eq_single r]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  simp only [e]
  rw [Generator_gueBlocks_eq, integral_blockH_mul_blockH]
  by_cases hpt : p = t
  · subst hpt
    simp only [true_and, ite_true]
    by_cases hqr : q = r
    · subst hqr
      rw [Finset.sum_eq_single q.2]
      · by_cases hb : p.1 = q.1
        · simp [hb]
        · have : ¬ ((p.1, q.2) = q) := fun h => hb (by rw [← h])
          have this' : ¬ (q = (p.1, q.2)) := fun h => this h.symm
          simp [hb, this']
      · intro j _ hj
        have : ¬ ((p.1, j) = q) := fun h => hj (by rw [← h])
        have this' : ¬ (q = (p.1, j)) := fun h => this h.symm
        simp [this']
      · simp
    · have : ∀ j : Fin N, Matrix.single q r (1 : ℂ) (p.1, j) (p.1, j) = 0 := by
        intro j
        rw [Matrix.single_apply]
        exact ite_eq_right_iff.mpr fun h => absurd (h.1.trans h.2.symm) hqr
      simp [this, hqr]
  · simp [hpt]

/-- `⟨X M⟩ = (DN)⁻¹ Σ_{p,q} X_{pq} M_{qp}`. -/
private lemma Generator_ntr_mul {ι : Type*} [Fintype ι] (X M : Matrix ι ι ℂ) :
    ntr (X * M) = (Fintype.card ι : ℂ)⁻¹ * ∑ p, ∑ q, X p q * M q p := by
  unfold ntr Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply]

/-- The entries of `E_a A E_a`. -/
private lemma Generator_EaAEa_apply (a : Fin D) (A : Matrix (Idx D N) (Idx D N) ℂ)
    (k m : Idx D N) :
    (Ea D N a * A * Ea D N a) k m = if k.1 = a ∧ m.1 = a then A k m else 0 := by
  unfold Ea
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h1 : k.1 = a <;> by_cases h2 : m.1 = a <;> simp [h1, h2]

/-- `E⟨X A⟩⟨X B⟩ = (DN²)⁻¹ Σ_a ⟨E_a A E_a B⟩` for the block GUE `X`. -/
private lemma Generator_E_ntr_ntr [NeZero D] [NeZero N] (A B : Matrix (Idx D N) (Idx D N) ℂ) :
    ∫ w, ntr (blockH D N w * A) * ntr (blockH D N w * B) ∂(gueBlocks D N) =
      ((D : ℂ) * N ^ 2)⁻¹ * ∑ a, ntr (Ea D N a * A * Ea D N a * B) := by
  set c : ℂ := (Fintype.card (Idx D N) : ℂ)⁻¹ with hc
  have e : ∀ w, ntr (blockH D N w * A) * ntr (blockH D N w * B) =
      ∑ p, ∑ q, ∑ r, ∑ t, (c * c * A q p * B t r) * (blockH D N w p q * blockH D N w r t) := by
    intro w
    rw [Generator_ntr_mul, Generator_ntr_mul, ← hc, mul_mul_mul_comm, Finset.sum_mul_sum]
    simp only [Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  simp only [e]
  have hi : ∀ p q r t, Integrable (fun w => (c * c * A q p * B t r) *
      (blockH D N w p q * blockH D N w r t)) (gueBlocks D N) := fun p q r t =>
    (Generator_int_entry2 p q r t).const_mul _
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
    integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun t _ => hi p q r t]
  have lhs : ∀ p q : Idx D N, ∫ w, ∑ r, ∑ t, (c * c * A q p * B t r) *
      (blockH D N w p q * blockH D N w r t) ∂(gueBlocks D N) =
      if p.1 = q.1 then c * c * (N : ℂ)⁻¹ * (A q p * B p q) else 0 := by
    intro p q
    rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun t _ => hi p q r t]
    simp only [integral_finsetSum _ fun t _ => hi p q _ t, integral_const_mul, Generator_cov]
    rw [Finset.sum_eq_single q, Finset.sum_eq_single p]
    · by_cases h : p.1 = q.1
      · simp only [h, and_self, ite_true]; ring
      · simp [h]
    · intro t _ ht; simp [Ne.symm ht]
    · simp
    · intro r _ hr
      refine Finset.sum_eq_zero fun t _ => ?_
      simp [Ne.symm hr]
    · simp
  have step : ∀ p : Idx D N, ∫ w, ∑ q, ∑ r, ∑ t, (c * c * A q p * B t r) *
      (blockH D N w p q * blockH D N w r t) ∂(gueBlocks D N) =
      ∑ q, if p.1 = q.1 then c * c * (N : ℂ)⁻¹ * (A q p * B p q) else 0 := by
    intro p
    rw [integral_finsetSum _ fun q _ => integrable_finsetSum _ fun r _ =>
      integrable_finsetSum _ fun t _ => hi p q r t]
    exact Finset.sum_congr rfl fun q _ => lhs p q
  simp only [step]
  have rhs : ∀ a : Fin D, ntr (Ea D N a * A * Ea D N a * B) =
      c * ∑ k, ∑ m, if k.1 = a ∧ m.1 = a then A k m * B m k else 0 := by
    intro a
    rw [Generator_ntr_mul, ← hc]
    simp only [Generator_EaAEa_apply, ite_mul, zero_mul]
  simp only [rhs]
  rw [← Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  have inner : ∀ k : Idx D N, ∑ a : Fin D, (∑ m, if k.1 = a ∧ m.1 = a then A k m * B m k else 0) =
      ∑ m, if m.1 = k.1 then A k m * B m k else 0 := by
    intro k
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_eq_single k.1]
    · by_cases h : m.1 = k.1 <;> simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  simp only [inner]
  rw [Finset.sum_comm]
  have hc' : c = ((D : ℂ) * N)⁻¹ := by
    rw [hc, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; rfl
  have hD : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne D)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : p.1 = q.1
  · simp only [h, ite_true, hc']
    field_simp
  · simp [Ne.symm h]

/-- Three second-order terms at once: `E c (2⟨P₁XQ₁XR₁⟩ + 2⟨P₂XQ₂XR₂⟩ + 2⟨P₃XQ₃XR₃⟩)`. -/
private lemma Generator_E3 [NeZero D] (c : ℂ) (P₁ Q₁ R₁ P₂ Q₂ R₂ P₃ Q₃ R₃ :
    Matrix (Idx D N) (Idx D N) ℂ) :
    ∫ w, c * (2 * ntr (P₁ * blockH D N w * Q₁ * blockH D N w * R₁) +
      2 * ntr (P₂ * blockH D N w * Q₂ * blockH D N w * R₂) +
      2 * ntr (P₃ * blockH D N w * Q₃ * blockH D N w * R₃)) ∂(gueBlocks D N) =
      c * (2 * (∑ a, (D : ℂ) * ntr (Q₁ * Ea D N a) * ntr (P₁ * Ea D N a * R₁)) +
        2 * (∑ a, (D : ℂ) * ntr (Q₂ * Ea D N a) * ntr (P₂ * Ea D N a * R₂)) +
        2 * ∑ a, (D : ℂ) * ntr (Q₃ * Ea D N a) * ntr (P₃ * Ea D N a * R₃)) := by
  have i₁ := (Generator_int_PXQXR P₁ Q₁ R₁).const_mul (2 : ℂ)
  have i₂ := (Generator_int_PXQXR P₂ Q₂ R₂).const_mul (2 : ℂ)
  have i₃ := (Generator_int_PXQXR P₃ Q₃ R₃).const_mul (2 : ℂ)
  rw [integral_const_mul, integral_add (by exact i₁.add i₂) (by exact i₃),
    integral_add (by exact i₁) (by exact i₂), integral_const_mul,
    integral_const_mul, integral_const_mul, Generator_E_PXQXR, Generator_E_PXQXR,
    Generator_E_PXQXR]

/-- Six second-order terms at once, `E c Σ_{i ≤ 6} 2⟨P_i X Q_i X R_i⟩`. -/
private lemma Generator_E6 [NeZero D] (c : ℂ)
    (P₁ Q₁ R₁ P₂ Q₂ R₂ P₃ Q₃ R₃ P₄ Q₄ R₄ P₅ Q₅ R₅ P₆ Q₆ R₆ :
    Matrix (Idx D N) (Idx D N) ℂ) :
    ∫ ω, c * (2 * ntr (P₁ * blockH D N ω * Q₁ * blockH D N ω * R₁) +
      2 * ntr (P₂ * blockH D N ω * Q₂ * blockH D N ω * R₂) +
      2 * ntr (P₃ * blockH D N ω * Q₃ * blockH D N ω * R₃) +
      2 * ntr (P₄ * blockH D N ω * Q₄ * blockH D N ω * R₄) +
      2 * ntr (P₅ * blockH D N ω * Q₅ * blockH D N ω * R₅) +
      2 * ntr (P₆ * blockH D N ω * Q₆ * blockH D N ω * R₆)) ∂(gueBlocks D N) =
      c * (2 * (∑ a, (D : ℂ) * ntr (Q₁ * Ea D N a) * ntr (P₁ * Ea D N a * R₁)) +
        2 * (∑ a, (D : ℂ) * ntr (Q₂ * Ea D N a) * ntr (P₂ * Ea D N a * R₂)) +
        2 * (∑ a, (D : ℂ) * ntr (Q₃ * Ea D N a) * ntr (P₃ * Ea D N a * R₃)) +
        2 * (∑ a, (D : ℂ) * ntr (Q₄ * Ea D N a) * ntr (P₄ * Ea D N a * R₄)) +
        2 * (∑ a, (D : ℂ) * ntr (Q₅ * Ea D N a) * ntr (P₅ * Ea D N a * R₅)) +
        2 * ∑ a, (D : ℂ) * ntr (Q₆ * Ea D N a) * ntr (P₆ * Ea D N a * R₆)) := by
  have i₁ := (Generator_int_PXQXR P₁ Q₁ R₁).const_mul (2 : ℂ)
  have i₂ := (Generator_int_PXQXR P₂ Q₂ R₂).const_mul (2 : ℂ)
  have i₃ := (Generator_int_PXQXR P₃ Q₃ R₃).const_mul (2 : ℂ)
  have i₄ := (Generator_int_PXQXR P₄ Q₄ R₄).const_mul (2 : ℂ)
  have i₅ := (Generator_int_PXQXR P₅ Q₅ R₅).const_mul (2 : ℂ)
  have i₆ := (Generator_int_PXQXR P₆ Q₆ R₆).const_mul (2 : ℂ)
  rw [integral_const_mul, integral_add (by exact ((((i₁.add i₂).add i₃).add i₄).add i₅))
      (by exact i₆),
    integral_add (by exact (((i₁.add i₂).add i₃).add i₄)) (by exact i₅),
    integral_add (by exact ((i₁.add i₂).add i₃)) (by exact i₄),
    integral_add (by exact (i₁.add i₂)) (by exact i₃),
    integral_add (by exact i₁) (by exact i₂)]
  simp only [integral_const_mul, Generator_E_PXQXR]

end Prob


/-! ### Resolvents along lines and along the characteristic flow -/

section Flow

variable {D N : ℕ}

/-- `⟨A + B⟩ = ⟨A⟩ + ⟨B⟩`. -/
private lemma Generator_ntr_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    ntr (A + B) = ntr A + ntr B := by
  simp only [ntr, Matrix.trace_add, mul_add]

/-- `⟨-A⟩ = -⟨A⟩`. -/
private lemma Generator_ntr_neg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    ntr (-A) = -ntr A := by
  simp only [ntr, Matrix.trace_neg, mul_neg]

/-- `⟨A - B⟩ = ⟨A⟩ - ⟨B⟩`. -/
private lemma Generator_ntr_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    ntr (A - B) = ntr A - ntr B := by
  simp only [ntr, Matrix.trace_sub, mul_sub]

/-- `⟨c A⟩ = c ⟨A⟩`. -/
private lemma Generator_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (A : Matrix ι ι ℂ) :
    ntr (c • A) = c * ntr A := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

/-- Cyclicity `⟨A B⟩ = ⟨B A⟩`. -/
private lemma Generator_ntr_comm {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    ntr (A * B) = ntr (B * A) := by
  unfold ntr
  rw [Matrix.trace_mul_comm]

/-- `hermPart` is `symArr`. -/
private lemma Generator_hermPart_eq (h : Idx D N → Idx D N → ℂ) : hermPart h = symArr h := by
  funext i j
  simp [hermPart, symArr]

/-- A real multiple of a Hermitian matrix is Hermitian. -/
private lemma Generator_herm_smul {ι : Type*} (V : Matrix ι ι ℂ) (hV : V.IsHermitian)
    (c : ℝ) : (c • V).IsHermitian :=
  hV.smul (IsSelfAdjoint.all c)

/-- A real complex multiple of a Hermitian matrix is Hermitian. -/
private lemma Generator_herm_csmul {ι : Type*} (V : Matrix ι ι ℂ)
    (hV : V.IsHermitian) (c : ℝ) : (((c : ℝ) : ℂ) • V).IsHermitian :=
  hV.smul (by simp [IsSelfAdjoint])

/-- Along a line through Hermitian arrays, the Hermitian part is the line itself. -/
private lemma Generator_of_hermPart_line (H V : Idx D N → Idx D N → ℂ)
    (hH : (Matrix.of H).IsHermitian) (hV : (Matrix.of V).IsHermitian) (t : ℝ) :
    Matrix.of (hermPart (H + t • V)) = Matrix.of H + t • Matrix.of V := by
  have e : Matrix.of (H + t • V) = Matrix.of H + t • Matrix.of V := rfl
  have hh : (Matrix.of (H + t • V)).IsHermitian := by
    rw [e]
    exact hH.add (Generator_herm_smul _ hV t)
  rw [Generator_hermPart_eq, symArr_of_isHermitian _ hh, e]

/-- `blockH` is Hermitian. -/
private lemma Generator_blockH_herm (D N : ℕ) (w : Fin D → Coords N) :
    (blockH D N w).IsHermitian := by
  have h := HLam_isHermitian D N 0 w
  have e : lam D N (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
    funext p q
    simp [lam]
  simpa [HLam, e] using h

/-- The resolvent along a line `t ↦ A + t V + B` of Hermitian matrices:
`∂_t G = -G V G`. -/
private lemma Generator_res_line {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B V : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hV : V.IsHermitian) (ξ : ℂ) (hξ : ξ.im ≠ 0) (t : ℝ) :
    Generator_MHD (fun s : ℝ => res (A + s • V + B) ξ)
      (-(res (A + t • V + B) ξ * V * res (A + t • V + B) ξ)) t := by
  have hX : Generator_MHD (fun s : ℝ => A + s • V + B) V t := fun k l => by
    have := (((hasDerivAt_id t).smul_const (V k l)).const_add (A k l)).add_const (B k l)
    simpa using this
  have := Generator_MHD.res hX (hasDerivAt_const t ξ)
    ((hA.add (Generator_herm_smul _ hV t)).add hB) hξ
  exact this.congr (by simp)

/-- The second derivative at `0` from a derivative known at every point. -/
private lemma Generator_iter2 (g g1 : ℝ → ℂ) (c : ℂ) (h1 : ∀ t, HasDerivAt g (g1 t) t)
    (h2 : HasDerivAt g1 c 0) : iteratedDeriv 2 g 0 = c := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have : deriv g = g1 := funext fun t => (h1 t).deriv
  rw [this]
  exact h2.deriv

/-- The second derivative along a line. -/
private lemma Generator_line2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℂ) (hF : ContDiff ℝ 2 F) (H V : E) :
    iteratedFDeriv ℝ 2 F H ![V, V] = iteratedDeriv 2 (fun t : ℝ => F (H + t • V)) 0 := by
  set L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight V with hL
  have hg : (fun t : ℝ => F (H + t • V)) = (fun z => F (H + z)) ∘ L := by
    funext t
    simp [hL]
  have hF' : ContDiff ℝ 2 (fun z => F (H + z)) := hF.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv, hg, L.iteratedFDeriv_comp_right hF' 0 le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
  simp only [map_zero, add_zero, hL, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, one_smul]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The first derivative along a line. -/
private lemma Generator_line1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℂ) (H V : E) (hF : DifferentiableAt ℝ F H) :
    fderiv ℝ F H V = deriv (fun t : ℝ => F (H + t • V)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => H + t • V) V 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add H
  have h2 : HasFDerivAt F (fderiv ℝ F H) (H + (0 : ℝ) • V) := by
    simpa using hF.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv.symm

/-- Entrywise `C²` matrix functions of an array. -/
private def Generator_CD (A : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ) : Prop :=
  ∀ k l, ContDiff ℝ 2 (fun h => A h k l)

private lemma Generator_CD.mul {A B : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ}
    (hA : Generator_CD A) (hB : Generator_CD B) : Generator_CD (fun h => A h * B h) :=
  fun k l => by
    simp only [Matrix.mul_apply]
    exact ContDiff.sum fun m _ => (hA k m).mul (hB m l)

private lemma Generator_CD.const (C : Matrix (Idx D N) (Idx D N) ℂ) :
    Generator_CD (D := D) (N := N) (fun _ => C) := fun _ _ => contDiff_const

private lemma Generator_CD.res (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (ξ : ℂ)
    (hξ : ξ.im ≠ 0) : Generator_CD (fun h => res (Matrix.of (hermPart h) + Λ) ξ) := fun k l => by
  simp only [Generator_hermPart_eq]
  exact_mod_cast contDiff_res_symArr Λ hΛ ξ hξ k l 2

private lemma Generator_CD.ntr {A : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ}
    (hA : Generator_CD A) : ContDiff ℝ 2 (fun h => ntr (A h)) := by
  unfold RBMTransitionEdge.ntr Matrix.trace
  exact contDiff_const.mul (ContDiff.sum fun k _ => hA k k)

/-- `S(M) = m` at the flow: `Σ_a D⟨M E_a⟩ E_a = m I` for `M = M(w, e^{-s/2} Λ)`, `Im w ≠ 0`. -/
private lemma Generator_SM (A : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (w : ℂ) (hw : w.im ≠ 0) :
    ∑ a : Fin D, ((D : ℂ) * ntr (MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) w *
      Ea D N a)) • Ea D N a =
      mExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) w • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
  have e : ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A =
      lam D N (((Real.exp (-s / 2) : ℝ) : ℂ) • A) := by
    funext p q
    simp only [lam, Matrix.smul_apply, smul_eq_mul, star_mul', Complex.star_def,
      Complex.conj_ofReal]
    split_ifs <;> ring
  rw [e]
  have h := sTheta_MExt D N 1 (((Real.exp (-s / 2) : ℝ) : ℂ) • A) w hw
  simpa [sTheta] using h

/-- The flow (3.10) [eq:deterflow] started at `z₁ ∈ {z, z̄}`: `w' = -w/2 - m(w, Λ_s)` and
`Im w ≠ 0`, for `s < t_c - t₀`. -/
private lemma Generator_flow [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z) (z₁ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) :
    HasDerivAt (charFlowZ (lam D N A) z₁) (-(charFlowZ (lam D N A) z₁ s) / 2 -
      mExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z₁ s)) s ∧
      (charFlowZ (lam D N A) z₁ s).im ≠ 0 := by
  have : Nonempty (Idx D N) := ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩,
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hs' : s < Real.log (1 + z.im / (mExt (lam D N A) z).im) := hs
  have hpos := (charFlow_M (lam D N A) hΛ z hz s hs').1
  rcases h₁ with rfl | rfl
  · exact ⟨charFlow_deriv (lam D N A) hΛ z₁ hz s hs', hpos.ne'⟩
  · have hcj : charFlowZ (lam D N A) (star z) = fun r => star (charFlowZ (lam D N A) z r) :=
      funext (charFlowZ_conj (lam D N A) z hz)
    have hd := (charFlow_deriv (lam D N A) hΛ z hz s hs').star
    have hΛs := Generator_herm_csmul _ hΛ (Real.exp (-s / 2))
    have hm := (mExt_conj _ hΛs (charFlowZ (lam D N A) z s) hpos.ne').1
    refine ⟨?_, ?_⟩
    · rw [hcj]
      convert hd using 1
      simp only [hm, star_sub, star_div₀, star_neg, star_ofNat]
    · rw [hcj]
      simp only [Complex.star_def, Complex.conj_im, neg_ne_zero]
      exact hpos.ne'

/-- The resolvent along the flow: `∂_s G = ½ G - ½ G H G - m G²` for
`G = (H + Λ_s - z_{1,s})⁻¹`, `m = m(z_{1,s}, Λ_s)`, at a Hermitian `H`. -/
private lemma Generator_res_time [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z) (z₁ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian) :
    Generator_MHD (fun r : ℝ => res (Matrix.of H + ((Real.exp (-r / 2) : ℝ) : ℂ) • lam D N A)
        (charFlowZ (lam D N A) z₁ r))
      ((1 / 2 : ℂ) • res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z₁ s) -
        (1 / 2 : ℂ) • (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z₁ s) * Matrix.of H *
          res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z₁ s)) -
        mExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A) (charFlowZ (lam D N A) z₁ s) •
          (res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
            (charFlowZ (lam D N A) z₁ s) *
          res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
            (charFlowZ (lam D N A) z₁ s))) s := by
  obtain ⟨hw, him⟩ := Generator_flow A z hz s hs z₁ h₁
  set Λ := lam D N A with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N A
  set c : ℂ := ((Real.exp (-s / 2) : ℝ) : ℂ) with hc
  set w := charFlowZ Λ z₁ s with hwdef
  set m := mExt (c • Λ) w with hm
  have hcd : HasDerivAt (fun r : ℝ => ((Real.exp (-r / 2) : ℝ) : ℂ))
      (((Real.exp (-s / 2) * (-1 / 2) : ℝ) : ℂ)) s := by
    have h : HasDerivAt (fun r : ℝ => Real.exp (-r / 2)) (Real.exp (-s / 2) * (-1 / 2)) s := by
      have := ((hasDerivAt_id s).neg.div_const 2).exp
      simpa [neg_div] using this
    exact h.ofReal_comp
  have hX : Generator_MHD (fun r : ℝ => Matrix.of H + ((Real.exp (-r / 2) : ℝ) : ℂ) • Λ)
      ((((Real.exp (-s / 2) * (-1 / 2) : ℝ) : ℂ)) • Λ) s :=
    ((Generator_MHD.const (Matrix.of H) s).add
      (Generator_MHD.smul hcd (Generator_MHD.const Λ s))).congr (by simp)
  have hXH : (Matrix.of H + c • Λ).IsHermitian := hH.add (Generator_herm_csmul _ hΛ _)
  have hR := Generator_MHD.res hX hw hXH him
  refine hR.congr ?_
  obtain ⟨-, hGY⟩ := res_mul_sub_of_im_ne (Matrix.of H + c • Λ) hXH w him
  set G := res (Matrix.of H + c • Λ) w with hG
  set Y := Matrix.of H + c • Λ - w • (1 : Matrix (Idx D N) (Idx D N) ℂ) with hY
  have e1 : ((((Real.exp (-s / 2) * (-1 / 2) : ℝ) : ℂ)) • Λ -
      (-w / 2 - m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) =
      (-(1 / 2) : ℂ) • Y + (1 / 2 : ℂ) • Matrix.of H + m • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
    rw [hY, hc]
    ext k l
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [e1]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hGY, Matrix.one_mul]
  module

end Flow

/-! ### The derivative of a loop in a Hermitian direction -/

section Loop

variable {D N : ℕ}

/-- The derivative of a product of matrix functions listed by `L`: the sum over the positions
of the product with the factor at that position differentiated. -/
private lemma Generator_MHD.list_prod {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (φ : α → ℝ → Matrix ι ι ℂ) (φ' : α → Matrix ι ι ℂ) (t : ℝ) :
    ∀ L : List α, (∀ a ∈ L, Generator_MHD (φ a) (φ' a) t) →
      Generator_MHD (fun s => (L.map fun a => φ a s).prod)
        (∑ i : Fin L.length, (((L.take i).map fun a => φ a t).prod * φ' (L.get i) *
          ((L.drop (i + 1)).map fun a => φ a t).prod)) t
  | [], _ => (Generator_MHD.const 1 t).congr (by simp)
  | a :: L, h => by
    have ih := Generator_MHD.list_prod φ φ' t L (fun b hb => h b (by simp [hb]))
    have := (h a (by simp)).mul ih
    simp only [List.map_cons, List.prod_cons]
    refine this.congr ?_
    erw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.take_zero, List.map_nil, List.prod_nil, Matrix.one_mul,
      List.get_cons_zero, zero_add, Fin.val_succ,
      List.take_succ_cons, List.map_cons, List.prod_cons,
      List.drop_succ_cons, Matrix.mul_sum, Matrix.mul_assoc, List.drop_zero,
      List.get_cons_succ']

/-- The chain `B₁G₁⋯B_pG_p` is entrywise `C²` in the array through its Hermitian part. -/
private lemma Generator_CD.chain :
    ∀ l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ),
      (∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) →
      Generator_CD (fun h => chainB (hermPart h) l)
  | [], _ => by
    simpa [chainB] using Generator_CD.const (D := D) (N := N) 1
  | f :: l, hl => by
    have ih := Generator_CD.chain l (fun g hg => hl g (by simp [hg]))
    have hf := hl f (by simp)
    have := ((Generator_CD.const f.1).mul (Generator_CD.res f.2.1 hf.1 f.2.2 hf.2)).mul ih
    simpa [chainB] using this

/-- A chain of an appended list is the product of the chains. -/
private lemma Generator_chainB_append (h : Idx D N → Idx D N → ℂ)
    (l₁ l₂ : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ)) :
    chainB h (l₁ ++ l₂) = chainB h l₁ * chainB h l₂ := by
  simp only [chainB, List.map_append, List.prod_append]

/-- The loop cut open at `G_i`: `B_{i+1}G_{i+1}⋯B_iG_i` as the chain after `i` times the chain
before `i` times `B_iG_i`. -/
private lemma Generator_chainB_rotate (h : Idx D N → Idx D N → ℂ)
    (l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (i : Fin l.length) :
    chainB h (l.rotate (i + 1)) = chainB h (l.drop (i + 1)) * (chainB h (l.take i) *
      ((l.get i).1 * res (Matrix.of h + (l.get i).2.1) (l.get i).2.2)) := by
  rw [List.rotate_eq_drop_append_take (by omega), Generator_chainB_append, List.take_add_one,
    Generator_chainB_append]
  congr 2
  simp [chainB]

/-- `⟨Σ_i A_i⟩ = Σ_i ⟨A_i⟩`. -/
private lemma Generator_ntr_sum {ι α : Type*} [Fintype ι] (s : Finset α)
    (A : α → Matrix ι ι ℂ) : ntr (∑ i ∈ s, A i) = ∑ i ∈ s, ntr (A i) := by
  unfold ntr
  rw [Matrix.trace_sum, Finset.mul_sum]

/-- The derivative of the loop `⟨B₁G₁⋯B_pG_p⟩` at a Hermitian `H` in a Hermitian direction `X`:
`-⟨X W⟩` with `W = Σ_r G_r B_{r+1}G_{r+1}⋯B_rG_r`. -/
private lemma Generator_loop_fderiv
    (l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (H : Idx D N → Idx D N → ℂ)
    (hH : (Matrix.of H).IsHermitian) (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : X.IsHermitian) :
    fderiv ℝ (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (hermPart h) l)) H
        (Matrix.of.symm X) =
      -ntr (X * ∑ i : Fin l.length,
        res (Matrix.of H + (l.get i).2.1) (l.get i).2.2 * chainB H (l.rotate (i + 1))) := by
  have hCD : ContDiff ℝ 2 (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (hermPart h) l)) :=
    (Generator_CD.chain l hl).ntr
  have hX' : (Matrix.of (Matrix.of.symm X)).IsHermitian := hX
  rw [Generator_line1 _ H _ (hCD.differentiable (by norm_num) H)]
  have hline : (fun t : ℝ => ntr (chainB (hermPart (H + t • Matrix.of.symm X)) l)) =
      fun t => ntr ((l.map fun f => f.1 * res (Matrix.of H + t • X + f.2.1) f.2.2).prod) := by
    funext t
    simp only [chainB, Generator_of_hermPart_line H _ hH hX' t, Equiv.apply_symm_apply]
  rw [hline]
  have hM := Generator_MHD.list_prod (fun f s => f.1 * res (Matrix.of H + s • X + f.2.1) f.2.2)
    (fun f => f.1 * -(res (Matrix.of H + f.2.1) f.2.2 * X * res (Matrix.of H + f.2.1) f.2.2)) 0
    l (fun f hf => by
      have := (Generator_MHD.const f.1 0).mul
        (Generator_res_line (Matrix.of H) f.2.1 X hH (hl f hf).1 hX f.2.2 (hl f hf).2 0)
      simpa using this)
  have hd := hM.ntr.deriv
  beta_reduce at hd
  refine hd.trans ?_
  simp only [zero_smul, add_zero, Generator_ntr_sum, Matrix.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Generator_chainB_rotate]
  set P := ((l.take i).map fun f => f.1 * res (Matrix.of H + f.2.1) f.2.2).prod with hP
  set S := ((l.drop (i + 1)).map fun f => f.1 * res (Matrix.of H + f.2.1) f.2.2).prod with hS
  have eP : chainB H (l.take i) = P := rfl
  have eS : chainB H (l.drop (i + 1)) = S := rfl
  rw [eP, eS]
  set B := (l.get i).1
  set G := res (Matrix.of H + (l.get i).2.1) (l.get i).2.2
  rw [show P * (B * -(G * X * G)) * S = -((P * (B * G)) * (X * (G * S))) by noncomm_ring,
    Generator_ntr_neg, Generator_ntr_comm]
  simp only [Matrix.mul_assoc]

end Loop


/-! ### The generator along the flow and the quadratic variation -/

/-- (3.48)–(3.51) for one resolvent: along the flow, at every Hermitian `H`,
`(∂_s + 𝓛)⟨G E_x⟩ = (1/2)⟨G E_x⟩ + Σ_a ⟨(G - M) E_a⟩ L_{(1,1),ax}` with
`G = (H + Λ_s - z_{1,s})⁻¹`, `M = M(z_{1,s}, Λ_s)`, `z₁ ∈ {z, z̄}` and `s < t_c - t₀`. -/
theorem gen_loop1 (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z) (z₁ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian)
    (x : Fin D) :
    let Λs : Matrix (Idx D N) (Idx D N) ℂ := ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A
    let w₁ := charFlowZ (lam D N A) z₁ s
    HasDerivAt (fun r : ℝ => ntr (res (Matrix.of H + ((Real.exp (-r / 2) : ℝ) : ℂ) • lam D N A)
        (charFlowZ (lam D N A) z₁ r) * Ea D N x))
      ((1 / 2 : ℂ) * ntr (res (Matrix.of H + Λs) w₁ * Ea D N x) +
        (∑ a, ntr ((res (Matrix.of H + Λs) w₁ - MExt Λs w₁) * Ea D N a) * Lmat Λs H w₁ w₁ a x) -
        genA (fun h => ntr (res (Matrix.of (hermPart h) + Λs) w₁ * Ea D N x)) H) s := by
  intro Λs w₁
  obtain ⟨hw, him⟩ := Generator_flow A z hz s hs z₁ h₁
  have hΛ := lam_isHermitian D N A
  have hΛs : Λs.IsHermitian := Generator_herm_csmul _ hΛ _
  set E := Ea D N x with hE
  set F : (Idx D N → Idx D N → ℂ) → ℂ :=
    fun h => ntr (res (Matrix.of (hermPart h) + Λs) w₁ * E) with hF
  have hT := ((Generator_res_time A z hz s hs z₁ h₁ H hH).mulc E).ntr
  set G := res (Matrix.of H + Λs) w₁ with hG
  have hCD : ContDiff ℝ 2 F :=
    ((Generator_CD.res Λs hΛs w₁ him).mul (Generator_CD.const E)).ntr
  have hline : ∀ V : Idx D N → Idx D N → ℂ, (Matrix.of V).IsHermitian →
      (fun t : ℝ => F (H + t • V)) =
        fun t => ntr (res (Matrix.of H + t • Matrix.of V + Λs) w₁ * E) := by
    intro V hV
    funext t
    simp only [hF, Generator_of_hermPart_line H V hH hV t]
  have hd1 : fderiv ℝ F H H = -ntr (G * Matrix.of H * G * E) := by
    rw [Generator_line1 F H H (hCD.differentiable (by norm_num) H), hline H hH]
    have := ((Generator_res_line (Matrix.of H) Λs (Matrix.of H) hH hΛs hH w₁ him 0).mulc E).ntr
    simp only [zero_smul, add_zero, ← hG] at this
    rw [this.deriv, Matrix.neg_mul, Generator_ntr_neg]
  have hd2 : ∀ X : Matrix (Idx D N) (Idx D N) ℂ, X.IsHermitian →
      iteratedFDeriv ℝ 2 F H ![Matrix.of.symm X, Matrix.of.symm X] =
        2 * ntr (G * X * G * X * (G * E)) := by
    intro X hX
    have hX' : (Matrix.of (Matrix.of.symm X)).IsHermitian := hX
    rw [Generator_line2 F hCD, hline _ hX']
    simp only [Equiv.apply_symm_apply]
    have hR := fun t => Generator_res_line (Matrix.of H) Λs X hH hΛs hX w₁ him t
    refine Generator_iter2 _ (fun t => -ntr (res (Matrix.of H + t • X + Λs) w₁ * X *
      res (Matrix.of H + t • X + Λs) w₁ * E)) _ (fun t => ?_) ?_
    · have := ((hR t).mulc E).ntr
      rw [Matrix.neg_mul, Generator_ntr_neg] at this
      exact this
    · have := ((((hR 0).mulc X).mul (hR 0)).mulc E).ntr.neg
      simp only [zero_smul, add_zero, ← hG] at this
      convert this using 1
      simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.add_mul, Generator_ntr_add,
        Generator_ntr_neg, Matrix.mul_assoc]
      ring
  have hint : ∫ w, iteratedFDeriv ℝ 2 F H
      ![Matrix.of.symm (blockH D N w), Matrix.of.symm (blockH D N w)] ∂(gueBlocks D N) =
      2 * ∑ a, (D : ℂ) * ntr (G * Ea D N a) * ntr (G * Ea D N a * (G * E)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun w =>
      hd2 _ (Generator_blockH_herm D N w)), integral_const_mul, Generator_E_PXQXR]
  have hgen : genA F H = (1 / 2 : ℂ) * ntr (G * Matrix.of H * G * E) +
      ∑ a, (D : ℂ) * ntr (G * Ea D N a) * ntr (G * Ea D N a * (G * E)) := by
    unfold genA
    rw [hd1, hint]
    ring
  set M := MExt Λs w₁ with hM
  set m := mExt Λs w₁ with hm
  have hSM : m * ntr (G * G * E) =
      ∑ a, (D : ℂ) * ntr (M * Ea D N a) * ntr (G * Ea D N a * (G * E)) := by
    have h := congrArg (fun S => ntr (G * S * (G * E))) (Generator_SM A s w₁ him)
    simp only [Generator_ntr_sum_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Generator_ntr_smul] at h
    rw [h, Matrix.mul_assoc]
  have key : ∑ a, ntr ((G - M) * Ea D N a) * Lmat Λs H w₁ w₁ a x =
      (∑ a, (D : ℂ) * ntr (G * Ea D N a) * ntr (G * Ea D N a * (G * E))) -
        ∑ a, (D : ℂ) * ntr (M * Ea D N a) * ntr (G * Ea D N a * (G * E)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Lmat, Matrix.sub_mul, Generator_ntr_sub, ← hG, ← hE, Matrix.mul_assoc]
    ring
  convert hT using 1
  rw [hgen, key]
  simp only [Matrix.sub_mul, Matrix.smul_mul, Generator_ntr_sub, Generator_ntr_smul]
  linear_combination hSM

/-- (3.48)–(3.51) for two resolvents, the drift of (3.53) [ItowtL] before any local law: along
the flow, at every Hermitian `H`, `(∂_s + 𝓛) L_{xy} = L_{xy} + Σ_a L_{xa} L_{ay} +
D Σ_a (⟨(G₁ - M₁) E_a⟩ L_{(1,2,1),xya} + ⟨(G₂ - M₂) E_a⟩ L_{(2,1,2),yxa})`,
`L = L_{(1,2),s}`, `z₁, z₂ ∈ {z, z̄}`, `s < t_c - t₀`. -/
theorem gen_loop2 (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (H : Idx D N → Idx D N → ℂ)
    (hH : (Matrix.of H).IsHermitian) (x y : Fin D) :
    let Λs : Matrix (Idx D N) (Idx D N) ℂ := ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A
    let w₁ := charFlowZ (lam D N A) z₁ s
    let w₂ := charFlowZ (lam D N A) z₂ s
    HasDerivAt (fun r : ℝ => Lmat (((Real.exp (-r / 2) : ℝ) : ℂ) • lam D N A) H
        (charFlowZ (lam D N A) z₁ r) (charFlowZ (lam D N A) z₂ r) x y)
      (Lmat Λs H w₁ w₂ x y + (Lmat Λs H w₁ w₂ * Lmat Λs H w₁ w₂) x y +
        (D : ℂ) * (∑ a, (ntr ((res (Matrix.of H + Λs) w₁ - MExt Λs w₁) * Ea D N a) *
            Lten3 Λs H w₁ w₂ w₁ x y a +
          ntr ((res (Matrix.of H + Λs) w₂ - MExt Λs w₂) * Ea D N a) *
            Lten3 Λs H w₂ w₁ w₂ y x a)) -
        genA (fun h => Lmat Λs (hermPart h) w₁ w₂ x y) H) s := by
  intro Λs w₁ w₂
  obtain ⟨-, him₁⟩ := Generator_flow A z hz s hs z₁ h₁
  obtain ⟨-, him₂⟩ := Generator_flow A z hz s hs z₂ h₂
  have hΛ := lam_isHermitian D N A
  have hΛs : Λs.IsHermitian := Generator_herm_csmul _ hΛ _
  set Ex := Ea D N x with hEx
  set Ey := Ea D N y with hEy
  set F : (Idx D N → Idx D N → ℂ) → ℂ := fun h => Lmat Λs (hermPart h) w₁ w₂ x y with hF
  have hT := ((((Generator_res_time A z hz s hs z₁ h₁ H hH).mulc Ex).mul
    (Generator_res_time A z hz s hs z₂ h₂ H hH)).mulc Ey).ntr.const_mul (D : ℂ)
  set G₁ := res (Matrix.of H + Λs) w₁ with hG₁
  set G₂ := res (Matrix.of H + Λs) w₂ with hG₂
  have hCD : ContDiff ℝ 2 F := contDiff_const.mul
    ((((Generator_CD.res Λs hΛs w₁ him₁).mul (Generator_CD.const Ex)).mul
      (Generator_CD.res Λs hΛs w₂ him₂)).mul (Generator_CD.const Ey)).ntr
  have hline : ∀ V : Idx D N → Idx D N → ℂ, (Matrix.of V).IsHermitian →
      (fun t : ℝ => F (H + t • V)) = fun t => (D : ℂ) *
        ntr (res (Matrix.of H + t • Matrix.of V + Λs) w₁ * Ex *
          res (Matrix.of H + t • Matrix.of V + Λs) w₂ * Ey) := by
    intro V hV
    funext t
    simp only [hF, Lmat, Generator_of_hermPart_line H V hH hV t, ← hEx, ← hEy]
  have hd1 : fderiv ℝ F H H = (D : ℂ) * (-ntr (G₁ * (Matrix.of H * (G₁ * (Ex * (G₂ * Ey))))) -
      ntr (G₁ * (Ex * (G₂ * (Matrix.of H * (G₂ * Ey)))))) := by
    rw [Generator_line1 F H H (hCD.differentiable (by norm_num) H), hline H hH]
    have h1 := Generator_res_line (Matrix.of H) Λs (Matrix.of H) hH hΛs hH w₁ him₁ 0
    have h2 := Generator_res_line (Matrix.of H) Λs (Matrix.of H) hH hΛs hH w₂ him₂ 0
    have := ((((h1.mulc Ex).mul h2).mulc Ey).ntr.const_mul (D : ℂ))
    simp only [zero_smul, add_zero, ← hG₁, ← hG₂] at this
    rw [this.deriv]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.add_mul, Generator_ntr_add,
      Generator_ntr_neg, Matrix.mul_assoc]
    ring
  have hd2 : ∀ X : Matrix (Idx D N) (Idx D N) ℂ, X.IsHermitian →
      iteratedFDeriv ℝ 2 F H ![Matrix.of.symm X, Matrix.of.symm X] =
        (D : ℂ) * (2 * ntr (G₁ * X * G₁ * X * (G₁ * Ex * G₂ * Ey)) +
          2 * ntr (G₁ * X * (G₁ * Ex * G₂) * X * (G₂ * Ey)) +
          2 * ntr (G₁ * Ex * G₂ * X * G₂ * X * (G₂ * Ey))) := by
    intro X hX
    have hX' : (Matrix.of (Matrix.of.symm X)).IsHermitian := hX
    rw [Generator_line2 F hCD, hline _ hX']
    simp only [Equiv.apply_symm_apply]
    have hR₁ := fun t => Generator_res_line (Matrix.of H) Λs X hH hΛs hX w₁ him₁ t
    have hR₂ := fun t => Generator_res_line (Matrix.of H) Λs X hH hΛs hX w₂ him₂ t
    refine Generator_iter2 _ (fun t => (D : ℂ) *
      (-ntr (res (Matrix.of H + t • X + Λs) w₁ * X * res (Matrix.of H + t • X + Λs) w₁ * Ex *
          res (Matrix.of H + t • X + Λs) w₂ * Ey) -
        ntr (res (Matrix.of H + t • X + Λs) w₁ * Ex * res (Matrix.of H + t • X + Λs) w₂ * X *
          res (Matrix.of H + t • X + Λs) w₂ * Ey))) _ (fun t => ?_) ?_
    · have := ((((hR₁ t).mulc Ex).mul (hR₂ t)).mulc Ey).ntr.const_mul (D : ℂ)
      convert this using 1
      simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.add_mul, Generator_ntr_add,
        Generator_ntr_neg, Matrix.mul_assoc]
      ring
    · have P1 := ((((((hR₁ 0).mulc X).mul (hR₁ 0)).mulc Ex).mul (hR₂ 0)).mulc Ey).ntr
      have P2 := ((((((hR₁ 0).mulc Ex).mul (hR₂ 0)).mulc X).mul (hR₂ 0)).mulc Ey).ntr
      have := (P1.neg.sub P2).const_mul (D : ℂ)
      simp only [zero_smul, add_zero, ← hG₁, ← hG₂] at this
      convert this using 1
      simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.add_mul,
        Generator_ntr_add, Generator_ntr_neg, Matrix.mul_assoc]
      ring
  have hint : ∫ w, iteratedFDeriv ℝ 2 F H
      ![Matrix.of.symm (blockH D N w), Matrix.of.symm (blockH D N w)] ∂(gueBlocks D N) =
      (D : ℂ) * (2 * (∑ a, (D : ℂ) * ntr (G₁ * Ea D N a) *
          ntr (G₁ * Ea D N a * (G₁ * Ex * G₂ * Ey))) +
        2 * (∑ a, (D : ℂ) * ntr (G₁ * Ex * G₂ * Ea D N a) * ntr (G₁ * Ea D N a * (G₂ * Ey))) +
        2 * ∑ a, (D : ℂ) * ntr (G₂ * Ea D N a) * ntr (G₁ * Ex * G₂ * Ea D N a * (G₂ * Ey))) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun w =>
      hd2 _ (Generator_blockH_herm D N w)), Generator_E3]
  have hgen : genA F H = -(1 / 2 : ℂ) * ((D : ℂ) *
      (-ntr (G₁ * (Matrix.of H * (G₁ * (Ex * (G₂ * Ey))))) -
        ntr (G₁ * (Ex * (G₂ * (Matrix.of H * (G₂ * Ey))))))) + (D : ℂ) *
      ((∑ a, (D : ℂ) * ntr (G₁ * Ea D N a) * ntr (G₁ * Ea D N a * (G₁ * Ex * G₂ * Ey))) +
        (∑ a, (D : ℂ) * ntr (G₁ * Ex * G₂ * Ea D N a) * ntr (G₁ * Ea D N a * (G₂ * Ey))) +
        ∑ a, (D : ℂ) * ntr (G₂ * Ea D N a) * ntr (G₁ * Ex * G₂ * Ea D N a * (G₂ * Ey))) := by
    unfold genA
    rw [hd1, hint]
    ring
  set M₁ := MExt Λs w₁ with hM₁
  set M₂ := MExt Λs w₂ with hM₂
  set m₁ := mExt Λs w₁ with hm₁
  set m₂ := mExt Λs w₂ with hm₂
  have hSM₁ : m₁ * ntr (G₁ * G₁ * (Ex * G₂ * Ey)) =
      ∑ a, (D : ℂ) * ntr (M₁ * Ea D N a) * ntr (G₁ * Ea D N a * (G₁ * Ex * G₂ * Ey)) := by
    have h := congrArg (fun S => ntr (G₁ * S * (G₁ * Ex * G₂ * Ey))) (Generator_SM A s w₁ him₁)
    simp only [Generator_ntr_sum_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Generator_ntr_smul] at h
    simp only [Matrix.mul_assoc] at h ⊢
    exact h.symm
  have hSM₂ : m₂ * ntr (G₁ * Ex * G₂ * G₂ * Ey) =
      ∑ a, (D : ℂ) * ntr (M₂ * Ea D N a) * ntr (G₁ * Ex * G₂ * Ea D N a * (G₂ * Ey)) := by
    have h := congrArg (fun S => ntr (G₁ * Ex * G₂ * S * (G₂ * Ey))) (Generator_SM A s w₂ him₂)
    simp only [Generator_ntr_sum_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Generator_ntr_smul] at h
    simp only [Matrix.mul_assoc] at h ⊢
    exact h.symm
  have key1 : ∑ a, (ntr ((G₁ - M₁) * Ea D N a) * Lten3 Λs H w₁ w₂ w₁ x y a +
      ntr ((G₂ - M₂) * Ea D N a) * Lten3 Λs H w₂ w₁ w₂ y x a) =
      (∑ a, (D : ℂ) * ntr (G₁ * Ea D N a) * ntr (G₁ * Ea D N a * (G₁ * Ex * G₂ * Ey))) -
        (∑ a, (D : ℂ) * ntr (M₁ * Ea D N a) * ntr (G₁ * Ea D N a * (G₁ * Ex * G₂ * Ey))) +
        ((∑ a, (D : ℂ) * ntr (G₂ * Ea D N a) * ntr (G₁ * Ex * G₂ * Ea D N a * (G₂ * Ey))) -
        ∑ a, (D : ℂ) * ntr (M₂ * Ea D N a) * ntr (G₁ * Ex * G₂ * Ea D N a * (G₂ * Ey))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have c1 : ntr (G₁ * Ex * G₂ * Ey * G₁ * Ea D N a) =
        ntr (G₁ * Ea D N a * (G₁ * Ex * G₂ * Ey)) := by
      rw [show G₁ * Ex * G₂ * Ey * G₁ * Ea D N a = (G₁ * Ex * G₂ * Ey) * (G₁ * Ea D N a) by
        simp only [Matrix.mul_assoc], Generator_ntr_comm]
    have c2 : ntr (G₂ * Ey * G₁ * Ex * G₂ * Ea D N a) =
        ntr (G₁ * Ex * G₂ * Ea D N a * (G₂ * Ey)) := by
      rw [show G₂ * Ey * G₁ * Ex * G₂ * Ea D N a = (G₂ * Ey) * (G₁ * Ex * G₂ * Ea D N a) by
        simp only [Matrix.mul_assoc], Generator_ntr_comm]
    simp only [Lten3, ← hG₁, ← hG₂, ← hEx, ← hEy, c1, c2, Matrix.sub_mul, Generator_ntr_sub]
    ring
  have key2 : (Lmat Λs H w₁ w₂ * Lmat Λs H w₁ w₂) x y = (D : ℂ) *
      ∑ a, (D : ℂ) * ntr (G₁ * Ex * G₂ * Ea D N a) * ntr (G₁ * Ea D N a * (G₂ * Ey)) := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Lmat, ← hG₁, ← hG₂, ← hEx, ← hEy, Matrix.mul_assoc]
    ring
  convert hT using 1
  · rfl
  rw [hgen, key1, key2]
  simp only [Lmat, ← hG₁, ← hG₂, ← hEx, ← hEy, Matrix.sub_mul, Matrix.smul_mul, Matrix.add_mul,
    Matrix.mul_sub, Matrix.mul_smul, Generator_ntr_sub, Generator_ntr_smul, Generator_ntr_add,
    Matrix.mul_assoc] at hSM₁ hSM₂ ⊢
  linear_combination (D : ℂ) * hSM₁ + (D : ℂ) * hSM₂

/-- (3.48)–(3.51) for three resolvents: along the flow, at every Hermitian `H`,
`(∂_s + 𝓛) L_{xyw} = (3/2) L_{xyw} + Σ_a (L_{(1,2),xa} L_{ayw} + L_{(2,3),ya} L_{xaw} +
L_{(3,1),wa} L_{xya}) + D Σ_{i,a} ⟨(G_i - M_i) E_a⟩ ℒ^{(i)}_{xywa}`, `L = L_{(1,2,3),s}`, where
`ℒ^{(i)}` is the four-resolvent loop with `G_i E_a G_i` in place of `G_i`. -/
theorem gen_loop3 (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc (lam D N A) z) (z₁ z₂ z₃ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (h₃ : z₃ = z ∨ z₃ = star z)
    (H : Idx D N → Idx D N → ℂ) (hH : (Matrix.of H).IsHermitian) (x y w : Fin D) :
    let Λs : Matrix (Idx D N) (Idx D N) ℂ := ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A
    let w₁ := charFlowZ (lam D N A) z₁ s
    let w₂ := charFlowZ (lam D N A) z₂ s
    let w₃ := charFlowZ (lam D N A) z₃ s
    let G₁ := res (Matrix.of H + Λs) w₁
    let G₂ := res (Matrix.of H + Λs) w₂
    let G₃ := res (Matrix.of H + Λs) w₃
    HasDerivAt (fun r : ℝ => Lten3 (((Real.exp (-r / 2) : ℝ) : ℂ) • lam D N A) H
        (charFlowZ (lam D N A) z₁ r) (charFlowZ (lam D N A) z₂ r) (charFlowZ (lam D N A) z₃ r)
        x y w)
      ((3 / 2 : ℂ) * Lten3 Λs H w₁ w₂ w₃ x y w +
        (∑ a, (Lmat Λs H w₁ w₂ x a * Lten3 Λs H w₁ w₂ w₃ a y w +
          Lmat Λs H w₂ w₃ y a * Lten3 Λs H w₁ w₂ w₃ x a w +
          Lmat Λs H w₃ w₁ w a * Lten3 Λs H w₁ w₂ w₃ x y a)) +
        (D : ℂ) * (∑ a, (ntr ((G₁ - MExt Λs w₁) * Ea D N a) * ((D : ℂ) *
            ntr (G₁ * Ea D N a * G₁ * Ea D N x * G₂ * Ea D N y * G₃ * Ea D N w)) +
          ntr ((G₂ - MExt Λs w₂) * Ea D N a) * ((D : ℂ) *
            ntr (G₁ * Ea D N x * G₂ * Ea D N a * G₂ * Ea D N y * G₃ * Ea D N w)) +
          ntr ((G₃ - MExt Λs w₃) * Ea D N a) * ((D : ℂ) *
            ntr (G₁ * Ea D N x * G₂ * Ea D N y * G₃ * Ea D N a * G₃ * Ea D N w)))) -
        genA (fun h => Lten3 Λs (hermPart h) w₁ w₂ w₃ x y w) H) s := by
  intro Λs w₁ w₂ w₃ G₁ G₂ G₃
  obtain ⟨-, him₁⟩ := Generator_flow A z hz s hs z₁ h₁
  obtain ⟨-, him₂⟩ := Generator_flow A z hz s hs z₂ h₂
  obtain ⟨-, him₃⟩ := Generator_flow A z hz s hs z₃ h₃
  have hΛ := lam_isHermitian D N A
  have hΛs : Λs.IsHermitian := Generator_herm_csmul _ hΛ _
  have hG₁ : G₁ = res (Matrix.of H + Λs) w₁ := rfl
  have hG₂ : G₂ = res (Matrix.of H + Λs) w₂ := rfl
  have hG₃ : G₃ = res (Matrix.of H + Λs) w₃ := rfl
  set Ex := Ea D N x with hEx
  set Ey := Ea D N y with hEy
  set Ew := Ea D N w with hEw
  set F : (Idx D N → Idx D N → ℂ) → ℂ :=
    fun h => Lten3 Λs (hermPart h) w₁ w₂ w₃ x y w with hF
  have hT := ((((((Generator_res_time A z hz s hs z₁ h₁ H hH).mulc Ex).mul
    (Generator_res_time A z hz s hs z₂ h₂ H hH)).mulc Ey).mul
    (Generator_res_time A z hz s hs z₃ h₃ H hH)).mulc Ew).ntr.const_mul (D : ℂ)
  have hCD : ContDiff ℝ 2 F := contDiff_const.mul
    ((((((Generator_CD.res Λs hΛs w₁ him₁).mul (Generator_CD.const Ex)).mul
      (Generator_CD.res Λs hΛs w₂ him₂)).mul (Generator_CD.const Ey)).mul
      (Generator_CD.res Λs hΛs w₃ him₃)).mul (Generator_CD.const Ew)).ntr
  have hline : ∀ V : Idx D N → Idx D N → ℂ, (Matrix.of V).IsHermitian →
      (fun t : ℝ => F (H + t • V)) = fun t => (D : ℂ) *
        ntr (res (Matrix.of H + t • Matrix.of V + Λs) w₁ * Ex *
          res (Matrix.of H + t • Matrix.of V + Λs) w₂ * Ey *
          res (Matrix.of H + t • Matrix.of V + Λs) w₃ * Ew) := by
    intro V hV
    funext t
    simp only [hF, Lten3, Generator_of_hermPart_line H V hH hV t, ← hEx, ← hEy, ← hEw]
  have hd1 : fderiv ℝ F H H = (D : ℂ) *
      (-ntr (G₁ * (Matrix.of H * (G₁ * (Ex * (G₂ * (Ey * (G₃ * Ew))))))) -
        ntr (G₁ * (Ex * (G₂ * (Matrix.of H * (G₂ * (Ey * (G₃ * Ew))))))) -
        ntr (G₁ * (Ex * (G₂ * (Ey * (G₃ * (Matrix.of H * (G₃ * Ew)))))))) := by
    rw [Generator_line1 F H H (hCD.differentiable (by norm_num) H), hline H hH]
    have h1 := Generator_res_line (Matrix.of H) Λs (Matrix.of H) hH hΛs hH w₁ him₁ 0
    have h2 := Generator_res_line (Matrix.of H) Λs (Matrix.of H) hH hΛs hH w₂ him₂ 0
    have h3 := Generator_res_line (Matrix.of H) Λs (Matrix.of H) hH hΛs hH w₃ him₃ 0
    have := ((((((h1.mulc Ex).mul h2).mulc Ey).mul h3).mulc Ew).ntr.const_mul (D : ℂ))
    simp only [zero_smul, add_zero, ← hG₁, ← hG₂, ← hG₃] at this
    rw [this.deriv]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.add_mul, Generator_ntr_add,
      Generator_ntr_neg, Matrix.mul_assoc]
    ring
  have hd2 : ∀ X : Matrix (Idx D N) (Idx D N) ℂ, X.IsHermitian →
      iteratedFDeriv ℝ 2 F H ![Matrix.of.symm X, Matrix.of.symm X] =
        (D : ℂ) * (2 * ntr (G₁ * X * G₁ * X * (G₁ * Ex * G₂ * Ey * G₃ * Ew)) +
          2 * ntr (G₁ * Ex * G₂ * X * G₂ * X * (G₂ * Ey * G₃ * Ew)) +
          2 * ntr (G₁ * Ex * G₂ * Ey * G₃ * X * G₃ * X * (G₃ * Ew)) +
          2 * ntr (G₁ * X * (G₁ * Ex * G₂) * X * (G₂ * Ey * G₃ * Ew)) +
          2 * ntr (G₁ * X * (G₁ * Ex * G₂ * Ey * G₃) * X * (G₃ * Ew)) +
          2 * ntr (G₁ * Ex * G₂ * X * (G₂ * Ey * G₃) * X * (G₃ * Ew))) := by
    intro X hX
    have hX' : (Matrix.of (Matrix.of.symm X)).IsHermitian := hX
    rw [Generator_line2 F hCD, hline _ hX']
    simp only [Equiv.apply_symm_apply]
    have hR₁ := fun t => Generator_res_line (Matrix.of H) Λs X hH hΛs hX w₁ him₁ t
    have hR₂ := fun t => Generator_res_line (Matrix.of H) Λs X hH hΛs hX w₂ him₂ t
    have hR₃ := fun t => Generator_res_line (Matrix.of H) Λs X hH hΛs hX w₃ him₃ t
    refine Generator_iter2 _ (fun t => (D : ℂ) *
      (-ntr (res (Matrix.of H + t • X + Λs) w₁ * X * res (Matrix.of H + t • X + Λs) w₁ * Ex *
          res (Matrix.of H + t • X + Λs) w₂ * Ey * res (Matrix.of H + t • X + Λs) w₃ * Ew) -
        ntr (res (Matrix.of H + t • X + Λs) w₁ * Ex * res (Matrix.of H + t • X + Λs) w₂ * X *
          res (Matrix.of H + t • X + Λs) w₂ * Ey * res (Matrix.of H + t • X + Λs) w₃ * Ew) -
        ntr (res (Matrix.of H + t • X + Λs) w₁ * Ex * res (Matrix.of H + t • X + Λs) w₂ * Ey *
          res (Matrix.of H + t • X + Λs) w₃ * X * res (Matrix.of H + t • X + Λs) w₃ * Ew)))
      _ (fun t => ?_) ?_
    · have := ((((((hR₁ t).mulc Ex).mul (hR₂ t)).mulc Ey).mul (hR₃ t)).mulc Ew).ntr.const_mul
        (D : ℂ)
      convert this using 1
      simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.add_mul,
        Generator_ntr_add, Generator_ntr_neg, Matrix.mul_assoc]
      ring
    · have P1 := ((((((((hR₁ 0).mulc X).mul (hR₁ 0)).mulc Ex).mul (hR₂ 0)).mulc Ey).mul
        (hR₃ 0)).mulc Ew).ntr
      have P2 := ((((((((hR₁ 0).mulc Ex).mul (hR₂ 0)).mulc X).mul (hR₂ 0)).mulc Ey).mul
        (hR₃ 0)).mulc Ew).ntr
      have P3 := ((((((((hR₁ 0).mulc Ex).mul (hR₂ 0)).mulc Ey).mul (hR₃ 0)).mulc X).mul
        (hR₃ 0)).mulc Ew).ntr
      have := ((P1.neg.sub P2).sub P3).const_mul (D : ℂ)
      simp only [zero_smul, add_zero, ← hG₁, ← hG₂, ← hG₃] at this
      convert this using 1
      simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.add_mul,
        Generator_ntr_add, Generator_ntr_neg, Matrix.mul_assoc]
      ring
  set S₁ := ∑ a, (D : ℂ) * ntr (G₁ * Ea D N a) *
    ntr (G₁ * Ea D N a * (G₁ * Ex * G₂ * Ey * G₃ * Ew)) with hS₁
  set S₂ := ∑ a, (D : ℂ) * ntr (G₂ * Ea D N a) *
    ntr (G₁ * Ex * G₂ * Ea D N a * (G₂ * Ey * G₃ * Ew)) with hS₂
  set S₃ := ∑ a, (D : ℂ) * ntr (G₃ * Ea D N a) *
    ntr (G₁ * Ex * G₂ * Ey * G₃ * Ea D N a * (G₃ * Ew)) with hS₃
  set C₁₂ := ∑ a, (D : ℂ) * ntr (G₁ * Ex * G₂ * Ea D N a) *
    ntr (G₁ * Ea D N a * (G₂ * Ey * G₃ * Ew)) with hC₁₂
  set C₁₃ := ∑ a, (D : ℂ) * ntr (G₁ * Ex * G₂ * Ey * G₃ * Ea D N a) *
    ntr (G₁ * Ea D N a * (G₃ * Ew)) with hC₁₃
  set C₂₃ := ∑ a, (D : ℂ) * ntr (G₂ * Ey * G₃ * Ea D N a) *
    ntr (G₁ * Ex * G₂ * Ea D N a * (G₃ * Ew)) with hC₂₃
  have hint : ∫ ω, iteratedFDeriv ℝ 2 F H
      ![Matrix.of.symm (blockH D N ω), Matrix.of.symm (blockH D N ω)] ∂(gueBlocks D N) =
      (D : ℂ) * (2 * S₁ + 2 * S₂ + 2 * S₃ + 2 * C₁₂ + 2 * C₁₃ + 2 * C₂₃) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      hd2 _ (Generator_blockH_herm D N ω)), Generator_E6]
  have hgen : genA F H = -(1 / 2 : ℂ) * ((D : ℂ) *
      (-ntr (G₁ * (Matrix.of H * (G₁ * (Ex * (G₂ * (Ey * (G₃ * Ew))))))) -
        ntr (G₁ * (Ex * (G₂ * (Matrix.of H * (G₂ * (Ey * (G₃ * Ew))))))) -
        ntr (G₁ * (Ex * (G₂ * (Ey * (G₃ * (Matrix.of H * (G₃ * Ew))))))))) +
      (D : ℂ) * (S₁ + S₂ + S₃ + C₁₂ + C₁₃ + C₂₃) := by
    unfold genA
    rw [hd1, hint]
    ring
  set M₁ := MExt Λs w₁ with hM₁
  set M₂ := MExt Λs w₂ with hM₂
  set M₃ := MExt Λs w₃ with hM₃
  set m₁ := mExt Λs w₁ with hm₁
  set m₂ := mExt Λs w₂ with hm₂
  set m₃ := mExt Λs w₃ with hm₃
  have hSM₁ : m₁ * ntr (G₁ * G₁ * (Ex * G₂ * Ey * G₃ * Ew)) =
      ∑ a, (D : ℂ) * ntr (M₁ * Ea D N a) * ntr (G₁ * Ea D N a * (G₁ * Ex * G₂ * Ey * G₃ * Ew)) := by
    have h := congrArg (fun S => ntr (G₁ * S * (G₁ * Ex * G₂ * Ey * G₃ * Ew)))
      (Generator_SM A s w₁ him₁)
    simp only [Generator_ntr_sum_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Generator_ntr_smul] at h
    simp only [Matrix.mul_assoc] at h ⊢
    exact h.symm
  have hSM₂ : m₂ * ntr (G₁ * Ex * G₂ * G₂ * (Ey * G₃ * Ew)) =
      ∑ a, (D : ℂ) * ntr (M₂ * Ea D N a) * ntr (G₁ * Ex * G₂ * Ea D N a * (G₂ * Ey * G₃ * Ew)) := by
    have h := congrArg (fun S => ntr (G₁ * Ex * G₂ * S * (G₂ * Ey * G₃ * Ew)))
      (Generator_SM A s w₂ him₂)
    simp only [Generator_ntr_sum_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Generator_ntr_smul] at h
    simp only [Matrix.mul_assoc] at h ⊢
    exact h.symm
  have hSM₃ : m₃ * ntr (G₁ * Ex * G₂ * Ey * G₃ * G₃ * Ew) =
      ∑ a, (D : ℂ) * ntr (M₃ * Ea D N a) * ntr (G₁ * Ex * G₂ * Ey * G₃ * Ea D N a * (G₃ * Ew)) := by
    have h := congrArg (fun S => ntr (G₁ * Ex * G₂ * Ey * G₃ * S * (G₃ * Ew)))
      (Generator_SM A s w₃ him₃)
    simp only [Generator_ntr_sum_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Generator_ntr_smul] at h
    simp only [Matrix.mul_assoc] at h ⊢
    exact h.symm
  have key1 : ∑ a, (Lmat Λs H w₁ w₂ x a * Lten3 Λs H w₁ w₂ w₃ a y w +
      Lmat Λs H w₂ w₃ y a * Lten3 Λs H w₁ w₂ w₃ x a w +
      Lmat Λs H w₃ w₁ w a * Lten3 Λs H w₁ w₂ w₃ x y a) =
      (D : ℂ) * (C₁₂ + C₂₃ + C₁₃) := by
    rw [hC₁₂, hC₂₃, hC₁₃, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have c1 : ntr (G₃ * Ew * G₁ * Ea D N a) = ntr (G₁ * Ea D N a * (G₃ * Ew)) := by
      rw [show G₃ * Ew * G₁ * Ea D N a = (G₃ * Ew) * (G₁ * Ea D N a) by
        simp only [Matrix.mul_assoc], Generator_ntr_comm]
    simp only [Lmat, Lten3, ← hG₁, ← hG₂, ← hG₃, ← hEx, ← hEy, ← hEw, c1]
    simp only [Matrix.mul_assoc]
    ring
  have key2 : ∑ a, (ntr ((G₁ - M₁) * Ea D N a) * ((D : ℂ) *
        ntr (G₁ * Ea D N a * G₁ * Ex * G₂ * Ey * G₃ * Ew)) +
      ntr ((G₂ - M₂) * Ea D N a) * ((D : ℂ) *
        ntr (G₁ * Ex * G₂ * Ea D N a * G₂ * Ey * G₃ * Ew)) +
      ntr ((G₃ - M₃) * Ea D N a) * ((D : ℂ) *
        ntr (G₁ * Ex * G₂ * Ey * G₃ * Ea D N a * G₃ * Ew))) =
      (S₁ - (∑ a, (D : ℂ) * ntr (M₁ * Ea D N a) *
          ntr (G₁ * Ea D N a * (G₁ * Ex * G₂ * Ey * G₃ * Ew))) +
        (S₂ - ∑ a, (D : ℂ) * ntr (M₂ * Ea D N a) *
          ntr (G₁ * Ex * G₂ * Ea D N a * (G₂ * Ey * G₃ * Ew))) +
        (S₃ - ∑ a, (D : ℂ) * ntr (M₃ * Ea D N a) *
          ntr (G₁ * Ex * G₂ * Ey * G₃ * Ea D N a * (G₃ * Ew)))) := by
    rw [hS₁, hS₂, hS₃, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.sub_mul, Generator_ntr_sub, Matrix.mul_assoc]
    ring
  convert hT using 1
  · rfl
  rw [hgen, key1, key2]
  simp only [Lten3, ← hG₁, ← hG₂, ← hG₃, ← hEx, ← hEy, ← hEw, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.add_mul, Matrix.mul_sub, Matrix.mul_smul, Generator_ntr_sub, Generator_ntr_smul,
    Generator_ntr_add, Matrix.mul_assoc] at hSM₁ hSM₂ hSM₃ ⊢
  linear_combination (D : ℂ) * hSM₁ + (D : ℂ) * hSM₂ + (D : ℂ) * hSM₃

/-- The quadratic variation (3.56) [eq:quad_var] of a loop in one step: for a block-diagonal GUE
`X` and the loop `F = ⟨B₁G₁⋯B_pG_p⟩` at a Hermitian `H`,
`E_X |DF(H)[X]|² = (D N²)⁻¹ Σ_a ⟨W E_a W^* E_a⟩` with `W = Σ_r G_r B_{r+1}G_{r+1}⋯B_rG_r` (the
loop cut open at `G_r`); for `F = L_{xy}` this gives the six-resolvent loops of (3.57)
[eq:quad_integrand]. -/
theorem loop_quadVar {D N : ℕ} [NeZero D] [NeZero N]
    (l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (H : Idx D N → Idx D N → ℂ)
    (hH : (Matrix.of H).IsHermitian) :
    let W : Matrix (Idx D N) (Idx D N) ℂ := ∑ i : Fin l.length,
      res (Matrix.of H + (l.get i).2.1) (l.get i).2.2 * chainB H (l.rotate (i + 1))
    ∫ x, ‖fderiv ℝ (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (hermPart h) l)) H
        (Matrix.of.symm (blockH D N x))‖ ^ 2 ∂(gueBlocks D N) =
      ((D : ℝ) * N ^ 2)⁻¹ * ∑ a, (ntr (W * Ea D N a * Wᴴ * Ea D N a)).re := by
  intro W
  have hconj : ∀ X : Matrix (Idx D N) (Idx D N) ℂ, X.IsHermitian →
      starRingEnd ℂ (ntr (X * W)) = ntr (X * Wᴴ) := by
    intro X hX
    unfold ntr
    rw [map_mul, map_inv₀, map_natCast, ← Complex.star_def, ← Matrix.trace_conjTranspose,
      Matrix.conjTranspose_mul, hX.eq, Matrix.trace_mul_comm]
  have hpt : ∀ x : Fin D → Coords N,
      ((‖fderiv ℝ (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (hermPart h) l)) H
        (Matrix.of.symm (blockH D N x))‖ ^ 2 : ℝ) : ℂ) =
        ntr (blockH D N x * W) * ntr (blockH D N x * Wᴴ) := by
    intro x
    rw [Generator_loop_fderiv l hl H hH _ (Generator_blockH_herm D N x), norm_neg,
      ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hconj _ (Generator_blockH_herm D N x)]
  have h1 : ∫ x, ‖fderiv ℝ (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (hermPart h) l)) H
        (Matrix.of.symm (blockH D N x))‖ ^ 2 ∂(gueBlocks D N) =
      (∫ x, ((‖fderiv ℝ (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (hermPart h) l)) H
        (Matrix.of.symm (blockH D N x))‖ ^ 2 : ℝ) : ℂ) ∂(gueBlocks D N)).re := by
    rw [integral_complex_ofReal, Complex.ofReal_re]
  rw [h1, integral_congr_ae (Filter.Eventually.of_forall hpt), Generator_E_ntr_ntr]
  have e : ((D : ℂ) * N ^ 2)⁻¹ = ((((D : ℝ) * N ^ 2)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.re_sum]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => congrArg Complex.re ?_)
  rw [show Ea D N a * W * Ea D N a * Wᴴ = Ea D N a * (W * Ea D N a * Wᴴ) by
    simp only [Matrix.mul_assoc], Generator_ntr_comm]

end RBMTransitionEdge

end
