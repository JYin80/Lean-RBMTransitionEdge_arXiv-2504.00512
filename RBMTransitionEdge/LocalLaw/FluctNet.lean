module

public import RBMTransitionEdge.LocalLaw.FluctIso
public import RBMTransitionEdge.LocalLaw.FluctAvg
public import RBMTransitionEdge.LocalLaw.BootstrapDet

@[expose] public section

/-!
# The net bound

The Lipschitz bound for `R_x` in `x`, and the isotropic and averaged fluctuation bounds for the
random `R_x̃`, `x̃ = σ_θ g`, `g_a = D⟨G E_a⟩`, on the event `‖R_x̃‖ ≤ C_R`, behind Lemma 2.9
[lem_loc].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `Σ_b y_b E_b` is the diagonal matrix with entry `y_a` at every index of the block `a`. -/
private lemma FNet_sum_Ea (D N : ℕ) (y : Fin D → ℂ) :
    ∑ b, y b • Ea D N b = Matrix.diagonal (fun p : Idx D N => y p.1) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, Ea, Matrix.diagonal_apply, smul_eq_mul]
  by_cases h : p = q
  · subst h
    simp
  · simp [h]

open scoped Matrix.Norms.L2Operator in
/-- The operator norm of a diagonal matrix is the sup norm of its entries. -/
private lemma FNet_opNorm_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    opNorm (Matrix.diagonal v) = ‖v‖ := by
  unfold opNorm
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]

/-- `‖Σ_b y_b E_b‖ ≤ max_b |y_b|`. -/
private lemma FNet_opNorm_blocks_le (D N : ℕ) (y : Fin D → ℂ) :
    opNorm (∑ b, y b • Ea D N b) ≤ ‖y‖ := by
  rw [FNet_sum_Ea, FNet_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun p => norm_le_pi_norm y p.1

/-- The operator norm is nonnegative. -/
private lemma FNet_opNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    0 ≤ opNorm X := norm_nonneg _

/-- The operator norm of a difference. -/
private lemma FNet_opNorm_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ) : opNorm (X - Y) ≤ opNorm X + opNorm Y := by
  unfold opNorm
  rw [map_sub]
  exact norm_sub_le _ _

/-- `R_x - R_{x'} = R_x (Σ_b (x_b - x'_b) E_b) R_{x'}` when both are true inverses, so
`‖R_x - R_{x'}‖ ≤ ‖R_x‖ ‖R_{x'}‖ max_b |x_b - x'_b|`. -/
theorem resX_sub_le {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (x x' : Fin D → ℂ)
    (hx : IsUnit (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - ∑ b, x b • Ea D N b))
    (hx' : IsUnit (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - ∑ b, x' b • Ea D N b)) :
    opNorm (resX Λ z x - resX Λ z x') ≤ opNorm (resX Λ z x) * opNorm (resX Λ z x') * ‖x - x'‖ := by
  set Tx := Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - ∑ b, x b • Ea D N b with hTx
  set Tx' := Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - ∑ b, x' b • Ea D N b with hTx'
  have h1 : Tx⁻¹ * Tx = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hx)
  have h2 : Tx' * Tx'⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hx')
  have hΔ : Tx' - Tx = ∑ b, (x - x') b • Ea D N b := by
    simp only [hTx, hTx', Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    abel
  have key : resX Λ z x - resX Λ z x' = resX Λ z x * (∑ b, (x - x') b • Ea D N b) * resX Λ z x' := by
    rw [← hΔ]
    change Tx⁻¹ - Tx'⁻¹ = Tx⁻¹ * (Tx' - Tx) * Tx'⁻¹
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc Tx⁻¹ Tx' Tx'⁻¹, h2, Matrix.mul_one,
      h1, Matrix.one_mul]
  rw [key]
  have hΔn := FNet_opNorm_blocks_le D N (x - x')
  have hRx := FNet_opNorm_nonneg (resX Λ z x)
  have hRx' := FNet_opNorm_nonneg (resX Λ z x')
  calc opNorm (resX Λ z x * (∑ b, (x - x') b • Ea D N b) * resX Λ z x')
      ≤ opNorm (resX Λ z x * (∑ b, (x - x') b • Ea D N b)) * opNorm (resX Λ z x') :=
        opNorm_mul_le _ _
    _ ≤ (opNorm (resX Λ z x) * opNorm (∑ b, (x - x') b • Ea D N b)) * opNorm (resX Λ z x') := by
        gcongr
        exact opNorm_mul_le _ _
    _ ≤ (opNorm (resX Λ z x) * ‖x - x'‖) * opNorm (resX Λ z x') := by gcongr
    _ = opNorm (resX Λ z x) * opNorm (resX Λ z x') * ‖x - x'‖ := by ring

/-- `|x^* T y| ≤ ‖T‖` for `|x|, |y| ≤ 1`. -/
private lemma FNet_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
    (x y : ι → ℂ) (hx : ∑ k, ‖x k‖ ^ 2 ≤ 1) (hy : ∑ k, ‖y k‖ ^ 2 ≤ 1) :
    ‖star x ⬝ᵥ (T *ᵥ y)‖ ≤ opNorm T := by
  have e : star x ⬝ᵥ (T *ᵥ y) =
      inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanLin T (WithLp.toLp 2 y)) := by
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
  have hx' : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_one.mpr hx
  have hy' : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_one.mpr hy
  have h1 : Matrix.toEuclideanLin T (WithLp.toLp 2 y) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y) := rfl
  have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y)‖ ≤ opNorm T * 1 :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by unfold opNorm; gcongr)
  rw [e, h1]
  calc ‖inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y))‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y)‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (opNorm T * 1) := mul_le_mul hx' h2 (norm_nonneg _) zero_le_one
    _ = opNorm T := by ring

/-- `|⟨M⟩| ≤ ‖M‖`. -/
private lemma FNet_ntr_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    ‖ntr M‖ ≤ opNorm M := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp [ntr, Matrix.trace, FNet_opNorm_nonneg]
  · have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    unfold ntr Matrix.trace
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, M.diag i‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, opNorm M := by
          gcongr
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun i _ => norm_apply_le_opNorm M i i)
      _ = opNorm M := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp

open scoped Matrix.Norms.L2Operator in
/-- `‖R^*‖ = ‖R‖`. -/
private lemma FNet_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℂ) : opNorm Rᴴ = opNorm R := by
  unfold opNorm
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_toEuclideanCLM,
    Matrix.l2_opNorm_conjTranspose]

/-- A deterministic unit vector `p` and `0 ≤ c ≤ ‖R‖` with `u^* R Y v = c p^* Y v` for all `Y`, `v`:
`p = R^* u / ‖R^* u‖`, and any unit vector if `R^* u = 0`. -/
private lemma FNet_dir {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (R : Matrix ι ι ℂ)
    (u : ι → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) :
    ∃ p : ι → ℂ, ∑ i, ‖p i‖ ^ 2 = 1 ∧ ∃ c : ℝ, 0 ≤ c ∧ c ≤ opNorm R ∧
      ∀ (Y : Matrix ι ι ℂ) (v : ι → ℂ),
        star u ⬝ᵥ ((R * Y) *ᵥ v) = (c : ℂ) * (star p ⬝ᵥ (Y *ᵥ v)) := by
  set w : ι → ℂ := Rᴴ *ᵥ u with hw
  have hkey : ∀ (Y : Matrix ι ι ℂ) (v : ι → ℂ),
      star u ⬝ᵥ ((R * Y) *ᵥ v) = star w ⬝ᵥ (Y *ᵥ v) := by
    intro Y v
    rw [hw, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec]
  set s : ℝ := ∑ i, ‖w i‖ ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => by positivity
  set c : ℝ := Real.sqrt s with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c * c = s := Real.mul_self_sqrt hs0
  have hcle : c ≤ opNorm R := by
    have hu' : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ ι)‖ = 1 := by
      rw [EuclideanSpace.norm_eq, hu, Real.sqrt_one]
    have h1 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Rᴴ (WithLp.toLp 2 u)‖ ≤ opNorm Rᴴ * 1 := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [hu']
      rfl
    rw [FNet_opNorm_conjTranspose, mul_one, Matrix.toEuclideanCLM_toLp,
      EuclideanSpace.norm_eq] at h1
    simpa [hw, hs, hc] using h1
  by_cases hc00 : c = 0
  · have hw0 : w = 0 := by
      funext i
      have : s = 0 := by rw [← hcsq, hc00]; ring
      have h2 : ‖w i‖ ^ 2 = 0 :=
        le_antisymm (this ▸ Finset.single_le_sum (f := fun i => ‖w i‖ ^ 2)
          (fun i _ => by positivity) (Finset.mem_univ i)) (by positivity)
      simpa using h2
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨Pi.single i₀ 1, ?_, c, hc0, hcle, fun Y v => ?_⟩
    · rw [Finset.sum_eq_single i₀]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    · rw [hkey, hw0, hc00]
      simp
  · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc00)
    refine ⟨((c⁻¹ : ℝ) : ℂ) • w, ?_, c, hc0, hcle, fun Y v => ?_⟩
    · have : ∀ i, ‖(((c⁻¹ : ℝ) : ℂ) • w) i‖ ^ 2 = (c⁻¹) ^ 2 * ‖w i‖ ^ 2 := by
        intro i
        rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hc0), mul_pow]
      simp only [this, ← Finset.mul_sum, ← hs]
      rw [← hcsq]
      field_simp
    · rw [hkey]
      have e1 : star (((c⁻¹ : ℝ) : ℂ) • w) = ((c⁻¹ : ℝ) : ℂ) • star w := by
        funext i
        simp [Pi.star_apply]
      rw [e1, smul_dotProduct, smul_eq_mul, ← mul_assoc]
      have : (c : ℂ) * ((c⁻¹ : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ hcpos.ne']
        simp
      rw [this, one_mul]

/-- The normalized trace on an empty index type vanishes. -/
private lemma FNet_ntr_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (B : Matrix ι ι ℂ) :
    ntr B = 0 := by
  simp [ntr, Matrix.trace]

/-- `(σ_θ x)_a = θ x_a + (1 - θ) D⁻¹ Σ_b x_b`. -/
private lemma FNet_sig_apply (D : ℕ) (θ : ℝ) (x : Fin D → ℂ) (a : Fin D) :
    (sigTheta D θ *ᵥ x) a =
      (θ : ℂ) * x a + ((1 - θ : ℝ) : ℂ) * ((D : ℂ)⁻¹ * ∑ b, x b) := by
  have hJ : (Matrix.of fun (_ _ : Fin D) => (1 : ℂ)) *ᵥ x = fun _ => ∑ b, x b := by
    ext
    simp [Matrix.mulVec, dotProduct]
  simp only [sigTheta, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hJ,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- `|(σ_θ x)_a| ≤ |x|_∞` for `θ ∈ [0, 1]`. -/
private lemma FNet_sig_linf (D : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : Fin D → ℂ)
    (a : Fin D) : ‖(sigTheta D θ *ᵥ x) a‖ ≤ ‖x‖ := by
  have hD : 0 < D := a.pos
  have hx : ∀ b, ‖x b‖ ≤ ‖x‖ := fun b => norm_le_pi_norm x b
  rw [FNet_sig_apply]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (by linarith), norm_inv,
    Complex.norm_natCast]
  have h2 : (D : ℝ)⁻¹ * ‖∑ b, x b‖ ≤ ‖x‖ := by
    have : ‖∑ b, x b‖ ≤ D * ‖x‖ := by
      calc ‖∑ b, x b‖ ≤ ∑ b, ‖x b‖ := norm_sum_le _ _
        _ ≤ ∑ _b : Fin D, ‖x‖ := Finset.sum_le_sum fun b _ => hx b
        _ = D * ‖x‖ := by simp
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    calc (D : ℝ)⁻¹ * ‖∑ b, x b‖ ≤ (D : ℝ)⁻¹ * (D * ‖x‖) := by gcongr
      _ = ‖x‖ := by field_simp
  nlinarith [hx a, norm_nonneg x]

/-- `σ_θ` keeps a vector with nonnegative imaginary parts in that cone, for `θ ∈ [0, 1]`. -/
private lemma FNet_sig_im_nonneg (D : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : Fin D → ℂ)
    (hx : ∀ a, 0 ≤ (x a).im) (b : Fin D) : 0 ≤ ((sigTheta D θ *ᵥ x) b).im := by
  rw [FNet_sig_apply, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
  have e : ((D : ℂ)⁻¹ * ∑ b, x b).im = (D : ℝ)⁻¹ * ∑ b, (x b).im := by
    have : (D : ℂ)⁻¹ = (((D : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.im_ofReal_mul, Complex.im_sum]
  rw [e]
  have hs : 0 ≤ ∑ b, (x b).im := Finset.sum_nonneg fun a _ => hx a
  have := hx b
  have h2 : 0 ≤ 1 - θ := by linarith
  positivity

/-- `|D⟨E_a W⟩| ≤ B` when the diagonal entries of `W` are at most `B` in modulus. -/
private lemma FNet_blk_le (D N : ℕ) (a : Fin D) (W : Matrix (Idx D N) (Idx D N) ℂ)
    (B : ℝ) (hB : 0 ≤ B) (h : ∀ p, ‖W p p‖ ≤ B) : ‖blockTr D N W a‖ ≤ B := by
  unfold blockTr
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : IsEmpty (Idx D 0) := ⟨fun p => p.2.elim0⟩
    simp [FNet_ntr_of_isEmpty, hB]
  · have hD : 0 < D := a.pos
    have htr : (Ea D N a * W).trace = ∑ p : Idx D N, if p.1 = a then W p p else 0 := by
      simp [Matrix.trace, Ea, Matrix.diagonal_mul]
    have hsum : ‖∑ p : Idx D N, if p.1 = a then W p p else 0‖ ≤ N * B := by
      calc ‖∑ p : Idx D N, if p.1 = a then W p p else 0‖
          ≤ ∑ p : Idx D N, ‖if p.1 = a then W p p else 0‖ := norm_sum_le _ _
        _ ≤ ∑ p : Idx D N, if p.1 = a then B else 0 :=
          Finset.sum_le_sum fun p _ => by split_ifs <;> simp [h p]
        _ = N * B := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          simp
    unfold ntr
    rw [htr]
    have hDN : (0 : ℝ) < D * N := by positivity
    calc ‖(D : ℂ) * (((Fintype.card (Idx D N) : ℕ) : ℂ)⁻¹ *
          ∑ p : Idx D N, if p.1 = a then W p p else 0)‖
        = D * (D * N : ℝ)⁻¹ * ‖∑ p : Idx D N, if p.1 = a then W p p else 0‖ := by
          rw [norm_mul, norm_mul, norm_inv]
          simp [Fintype.card_prod]
          ring
      _ ≤ D * (D * N : ℝ)⁻¹ * (N * B) := by gcongr
      _ = B := by field_simp

/-- `Im G_{pp} ≥ 0` for the resolvent of a Hermitian matrix at `Im z > 0`. -/
private lemma FNet_im_diag_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (p : ι) : 0 ≤ (res X z p p).im := by
  have h := (ward_diag X hX z hz p).1
  have h1 : (res X z p p).im = z.im * ∑ x, ‖res X z x p‖ ^ 2 := by
    rw [h]
    field_simp
  rw [h1]
  positivity

/-- The block traces `D⟨E_c G⟩` have nonnegative imaginary part when `Im G_{pp} ≥ 0`. -/
private lemma FNet_blockTr_im_nonneg (D N : ℕ) (G : Matrix (Idx D N) (Idx D N) ℂ)
    (h : ∀ p, 0 ≤ (G p p).im) (c : Fin D) : 0 ≤ (blockTr D N G c).im := by
  unfold blockTr ntr
  have htr : (Ea D N c * G).trace = ∑ p : Idx D N, if p.1 = c then G p p else 0 := by
    simp [Matrix.trace, Ea, Matrix.diagonal_mul]
  rw [htr]
  have e : ((D : ℂ) * (((Fintype.card (Idx D N) : ℕ) : ℂ)⁻¹ *
      ∑ p : Idx D N, if p.1 = c then G p p else 0)) =
      ((D * ((Fintype.card (Idx D N) : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
        ∑ p : Idx D N, if p.1 = c then G p p else 0 := by
    push_cast
    ring
  rw [e, Complex.im_ofReal_mul, Complex.im_sum]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ => ?_)
  split_ifs
  · exact h p
  · simp

/-- The block traces of the resolvent of a Hermitian matrix at `Im z > 0`, and their image under
`σ_θ` (`θ ∈ [0, 1]`): bounded by `(Im z)⁻¹` in the sup norm and with nonnegative imaginary parts. -/
private lemma FNet_xt (D N : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    ‖sigTheta D θ *ᵥ blockTr D N (res X z)‖ ≤ z.im⁻¹ ∧
      ∀ b, 0 ≤ ((sigTheta D θ *ᵥ blockTr D N (res X z)) b).im := by
  have hG := opNorm_res_le X hX z hz
  have hbl : ‖blockTr D N (res X z)‖ ≤ z.im⁻¹ := by
    refine (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hz.le)).mpr fun a => ?_
    exact FNet_blk_le D N a _ _ (inv_nonneg.mpr hz.le)
      fun p => (norm_apply_le_opNorm _ p p).trans hG
  refine ⟨?_, fun b => FNet_sig_im_nonneg D θ h0 h1 _
    (fun c => FNet_blockTr_im_nonneg D N _ (FNet_im_diag_nonneg X hX z hz) c) b⟩
  refine (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hz.le)).mpr fun a => ?_
  exact (FNet_sig_linf D θ h0 h1 _ a).trans hbl

/-- `‖H̲G‖ ≤ 1 + (‖Λ‖ + |z|)/η + 1/η²` for Hermitian `H`, `Λ`, `θ ∈ [0, 1]`, from
`HG = I - (Λ - z) G` and `S_θ(G) = Σ_a (σ_θ g)_a E_a` ((2.30) [eq:HGline]). -/
private lemma FNet_Y_le (D N : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (H Λ : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) :
    opNorm (hgUnder D N θ H Λ z) ≤ 1 + (opNorm Λ + ‖z‖) / z.im + 1 / z.im ^ 2 := by
  set G := res (H + Λ) z with hG
  have hHΛ : (H + Λ).IsHermitian := hH.add hΛ
  have hGn : opNorm G ≤ z.im⁻¹ := opNorm_res_le _ hHΛ z hz
  have hres := (res_mul_sub (H + Λ) hHΛ z hz).1
  have hHG : H * G = 1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G := by
    have : H * G = (H + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G -
        (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G := by
      rw [← Matrix.sub_mul]
      congr 1
      abel
    rw [this, hres]
  have hform : hgUnder D N θ H Λ z =
      1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G + sTheta D N θ G * G := by
    unfold hgUnder
    rw [← hG, hHG]
  have hη : 0 < z.im⁻¹ := inv_pos.mpr hz
  have hG0 : 0 ≤ opNorm G := norm_nonneg _
  have hone : opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ 1 := by
    unfold opNorm
    rw [map_one]
    exact ContinuousLinearMap.norm_id_le
  have hΛz : opNorm (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ opNorm Λ + ‖z‖ := by
    refine (FNet_opNorm_sub_le _ _).trans ?_
    rw [opNorm_smul]
    nlinarith [norm_nonneg z]
  have hSn : opNorm (sTheta D N θ G) ≤ z.im⁻¹ := by
    rw [sTheta_blockTr]
    exact (FNet_opNorm_blocks_le D N _).trans (FNet_xt D N θ h0 h1 _ hHΛ z hz).1
  have hS : opNorm (sTheta D N θ G * G) ≤ z.im⁻¹ * z.im⁻¹ :=
    (opNorm_mul_le _ _).trans (mul_le_mul hSn hGn hG0 hη.le)
  have hT : opNorm ((Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G) ≤
      (opNorm Λ + ‖z‖) * z.im⁻¹ :=
    (opNorm_mul_le _ _).trans (mul_le_mul hΛz hGn hG0 ((norm_nonneg _).trans hΛz))
  rw [hform]
  calc opNorm (1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G + sTheta D N θ G * G)
      ≤ opNorm (1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G) +
          opNorm (sTheta D N θ G * G) := opNorm_add_le _ _
    _ ≤ (opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) +
          opNorm ((Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G)) +
          opNorm (sTheta D N θ G * G) := by
        gcongr
        exact FNet_opNorm_sub_le _ _
    _ ≤ (1 + (opNorm Λ + ‖z‖) * z.im⁻¹) + z.im⁻¹ * z.im⁻¹ := by gcongr
    _ = 1 + (opNorm Λ + ‖z‖) / z.im + 1 / z.im ^ 2 := by
        have : (z.im ^ 2)⁻¹ = z.im⁻¹ * z.im⁻¹ := by rw [sq, mul_inv]
        rw [div_eq_mul_inv, one_div, this]

/-- `‖M‖ ≤ n² b` for an `n × n` matrix with all entries at most `b` in modulus. -/
private lemma FNet_opNorm_le_card {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (b : ℝ) (hb : 0 ≤ b) (h : ∀ p q, ‖M p q‖ ≤ b) :
    opNorm M ≤ (Fintype.card ι : ℝ) ^ 2 * b := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  obtain ⟨y, rfl⟩ : ∃ y, w = WithLp.toLp 2 y := ⟨w.ofLp, rfl⟩
  rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.norm_eq]
  set W : ℝ := ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ with hW
  have hW0 : 0 ≤ W := norm_nonneg _
  have hy : ∀ j, ‖y j‖ ≤ W := fun j => PiLp.norm_apply_le (WithLp.toLp 2 y) j
  have hcomp : ∀ i, ‖(M *ᵥ y) i‖ ≤ n * b * W := by
    intro i
    calc ‖(M *ᵥ y) i‖ = ‖∑ j, M i j * y j‖ := by simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ j, ‖M i j * y j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : ι, b * W := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul (h i j) (hy j) (norm_nonneg _) hb
      _ = n * b * W := by simp [hn]; ring
  rcases isEmpty_or_nonempty ι with hE | hne
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, Real.sqrt_zero]
    positivity
  · have hn1 : 1 ≤ n := by
      rw [hn]
      exact_mod_cast Fintype.card_pos
    rw [Real.sqrt_le_left (by positivity)]
    calc ∑ i, ‖(M *ᵥ y) i‖ ^ 2 ≤ ∑ _i : ι, (n * b * W) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcomp i) 2
      _ = n * (n * b * W) ^ 2 := by simp [hn]
      _ ≤ (n ^ 2 * b * W) ^ 2 := by
          have : 0 ≤ n ^ 3 * (b * W) ^ 2 * (n - 1) := by
            have : 0 ≤ n - 1 := by linarith
            positivity
          nlinarith [this]

/-- `‖Λ‖ ≤ 2 (DN)² ‖A‖` for the interaction `Λ = lam D N A` of (1.3) [matrix_H]. -/
private lemma FNet_opNorm_lam (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * ((D : ℝ) * N) ^ 2 * opNorm A := by
  have hA := FNet_opNorm_nonneg A
  have h := FNet_opNorm_le_card (lam D N A) (2 * opNorm A) (by positivity) ?_
  · simpa [Fintype.card_prod, mul_comm, mul_assoc, mul_left_comm] using h
  · intro p q
    unfold lam
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if fwd D p.1 q.1 then A p.2 q.2 else 0)‖ ≤ opNorm A := by
      split_ifs
      · exact norm_apply_le_opNorm A _ _
      · simpa using hA
    have h2 : ‖(if fwd D q.1 p.1 then star (A q.2 p.2) else 0)‖ ≤ opNorm A := by
      split_ifs
      · rw [norm_star]
        exact norm_apply_le_opNorm A _ _
      · simpa using hA
    linarith

/-- A finite set of at most `N^15` points of the closed upper half plane such that every `w` with
`|w| ≤ N` and `Im w ≥ 0` has a point of it within `2/N^6`. -/
private lemma FNet_grid1 (N : ℕ) (hN : 6 ≤ N) :
    ∃ S : Finset ℂ, S.card ≤ N ^ 15 ∧ ∀ w : ℂ, ‖w‖ ≤ N → 0 ≤ w.im →
      ∃ w' ∈ S, 0 ≤ w'.im ∧ ‖w - w'‖ ≤ 2 / (N : ℝ) ^ 6 := by
  set m : ℕ := N ^ 7 with hm
  set s : ℝ := (N : ℝ) ^ 6 with hs
  have hN0 : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : 0 < s := by rw [hs]; positivity
  have hmR : (m : ℝ) = (N : ℝ) * s := by rw [hm, hs]; push_cast; ring
  refine ⟨((Finset.Icc (-(m : ℤ)) m) ×ˢ (Finset.Icc 0 (m : ℤ))).image
    (fun q : ℤ × ℤ => (((q.1 : ℝ) / s : ℝ) : ℂ) + (((q.2 : ℝ) / s : ℝ) : ℂ) * Complex.I),
    ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
    have e1 : ((m : ℤ) + 1 - -(m : ℤ)).toNat = 2 * m + 1 := by omega
    have e2 : ((m : ℤ) + 1 - 0).toNat = m + 1 := by omega
    rw [e1, e2]
    have hm1 : 1 ≤ m := Nat.one_le_pow _ _ (by omega)
    have h15 : N ^ 15 = N * (m * m) := by rw [hm]; ring
    rw [h15]
    calc (2 * m + 1) * (m + 1) ≤ 6 * (m * m) := by nlinarith
      _ ≤ N * (m * m) := Nat.mul_le_mul_right _ hN
  · intro w hw him
    have hre := abs_le.mp ((Complex.abs_re_le_norm w).trans hw)
    set k : ℤ := ⌊w.re * s⌋ with hk
    set j : ℤ := ⌈w.im * s⌉ with hj
    have hk1 : (k : ℝ) ≤ w.re * s := Int.floor_le _
    have hk2 : w.re * s < k + 1 := Int.lt_floor_add_one _
    have hj1 : w.im * s ≤ j := Int.le_ceil _
    have hj2 : (j : ℝ) < w.im * s + 1 := Int.ceil_lt_add_one _
    have hreN : w.re * s ≤ m := by
      rw [hmR]; exact mul_le_mul_of_nonneg_right hre.2 hs0.le
    have hreN' : -(m : ℝ) ≤ w.re * s := by
      rw [hmR]; nlinarith [mul_le_mul_of_nonneg_right hre.1 hs0.le]
    have himN : w.im * s ≤ m := by
      have : w.im ≤ N := (Complex.abs_im_le_norm w).trans hw |> fun h => (le_abs_self _).trans h
      rw [hmR]; exact mul_le_mul_of_nonneg_right this hs0.le
    have hkm : k ≤ m := by
      have : (k : ℝ) ≤ m := hk1.trans hreN
      exact_mod_cast this
    have hkm' : -(m : ℤ) ≤ k := Int.le_floor.mpr (by push_cast; exact hreN')
    have hj0 : 0 ≤ j := Int.ceil_nonneg (mul_nonneg him hs0.le)
    have hjm : j ≤ m := Int.ceil_le.mpr (by exact_mod_cast himN)
    refine ⟨(((k : ℝ) / s : ℝ) : ℂ) + (((j : ℝ) / s : ℝ) : ℂ) * Complex.I,
      Finset.mem_image.mpr ⟨(k, j), Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hkm', hkm⟩, Finset.mem_Icc.mpr ⟨hj0, hjm⟩⟩, rfl⟩, ?_, ?_⟩
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_add, mul_zero, mul_one]
      have : (0 : ℝ) ≤ j := by exact_mod_cast hj0
      positivity
    · have hre' : (w - ((((k : ℝ) / s : ℝ) : ℂ) + (((j : ℝ) / s : ℝ) : ℂ) * Complex.I)).re =
          (w.re * s - k) / s := by
        have : (w - ((((k : ℝ) / s : ℝ) : ℂ) + (((j : ℝ) / s : ℝ) : ℂ) * Complex.I)).re =
            w.re - k / s := by simp
        rw [this]
        field_simp
      have him' : (w - ((((k : ℝ) / s : ℝ) : ℂ) + (((j : ℝ) / s : ℝ) : ℂ) * Complex.I)).im =
          (w.im * s - j) / s := by
        have : (w - ((((k : ℝ) / s : ℝ) : ℂ) + (((j : ℝ) / s : ℝ) : ℂ) * Complex.I)).im =
            w.im - j / s := by simp
        rw [this]
        field_simp
      have hA : |w.re * s - k| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hB : |w.im * s - j| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [hre', him', abs_div, abs_div, abs_of_pos hs0]
      calc |w.re * s - k| / s + |w.im * s - j| / s ≤ 1 / s + 1 / s := by gcongr
        _ = 2 / s := by ring

/-- The grid of mesh `N^{-6}` in `{|x_b| ≤ N, Im x_b ≥ 0} ⊂ ℂ^D`: at most `N^{15 D}` points of the
closed upper half plane in each coordinate, within `2/N^6` in the sup norm of every such `x`. -/
private lemma FNet_grid (D N : ℕ) (hN : 6 ≤ N) :
    ∃ G : Finset (Fin D → ℂ), G.card ≤ N ^ (15 * D) ∧
      ∀ x : Fin D → ℂ, (∀ b, ‖x b‖ ≤ N ∧ 0 ≤ (x b).im) →
        ∃ x' ∈ G, (∀ b, 0 ≤ (x' b).im) ∧ ‖x - x'‖ ≤ 2 / (N : ℝ) ^ 6 := by
  obtain ⟨S, hSc, hS⟩ := FNet_grid1 N hN
  refine ⟨Fintype.piFinset fun _ : Fin D => S, ?_, ?_⟩
  · rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    exact Nat.pow_le_pow_left hSc D
  · intro x hx
    choose y hyS hy1 hy2 using fun b => hS (x b) (hx b).1 (hx b).2
    refine ⟨y, Fintype.mem_piFinset.mpr hyS, hy1, ?_⟩
    have hN0 : (0 : ℝ) < N := by
      have : (6 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun b => hy2 b

/-- `T x * R_x = 1` gives `IsUnit T x`. -/
private lemma FNet_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] {T R : Matrix ι ι ℂ}
    (h : T * R = 1) : IsUnit T :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h)

/-- The net step: if `‖R_x‖ ≤ C_R` and `4 C_R ≤ N^6` then the grid point `x'` within `2/N^6` of `x`
has `‖R_{x'}‖ ≤ 2 C_R` and `‖R_x - R_{x'}‖ ≤ 4 C_R²/N^6`, by `resX_sub_le`. -/
private lemma FNet_approx {D N : ℕ} (hN : 6 ≤ N) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (CR : ℝ) (hCR : 1 ≤ CR)
    (hCRN : 4 * CR ≤ (N : ℝ) ^ 6) (G : Finset (Fin D → ℂ))
    (hG : ∀ x : Fin D → ℂ, (∀ b, ‖x b‖ ≤ N ∧ 0 ≤ (x b).im) →
      ∃ x' ∈ G, (∀ b, 0 ≤ (x' b).im) ∧ ‖x - x'‖ ≤ 2 / (N : ℝ) ^ 6)
    (x : Fin D → ℂ) (hx : ∀ b, ‖x b‖ ≤ N ∧ 0 ≤ (x b).im) (hR : opNorm (resX Λ z x) ≤ CR) :
    ∃ x' ∈ G, opNorm (resX Λ z x') ≤ 2 * CR ∧
      opNorm (resX Λ z x - resX Λ z x') ≤ 4 * CR ^ 2 / (N : ℝ) ^ 6 := by
  obtain ⟨x', hx'G, hx'im, hxx'⟩ := hG x hx
  refine ⟨x', hx'G, ?_⟩
  have hs0 : (0 : ℝ) < (N : ℝ) ^ 6 := by
    have : (6 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  have hU := (resX_spec Λ hΛ z hz x (fun b => (hx b).2)).1
  have hU' := (resX_spec Λ hΛ z hz x' hx'im).1
  have hlip := resX_sub_le Λ z x x' (FNet_isUnit hU) (FNet_isUnit hU')
  set a := opNorm (resX Λ z x) with ha
  set a' := opNorm (resX Λ z x') with ha'
  have ha0 : 0 ≤ a := FNet_opNorm_nonneg _
  have ha'0 : 0 ≤ a' := FNet_opNorm_nonneg _
  set q : ℝ := 2 / (N : ℝ) ^ 6 with hq
  have hq0 : 0 ≤ q := by positivity
  have hCq : CR * q ≤ 1 / 2 := by
    rw [hq, ← mul_div_assoc, div_le_iff₀ hs0]
    linarith
  have hδ0 : 0 ≤ ‖x - x'‖ := norm_nonneg _
  have h1 : a' ≤ a + opNorm (resX Λ z x - resX Λ z x') := by
    have := FNet_opNorm_sub_le (resX Λ z x) (resX Λ z x - resX Λ z x')
    rwa [sub_sub_cancel] at this
  have h2 : opNorm (resX Λ z x - resX Λ z x') ≤ CR * a' * q :=
    hlip.trans (by gcongr)
  have h3 : a' ≤ 2 * CR := by
    have h4 : a' ≤ CR + a' * (CR * q) := by
      nlinarith [h1, h2, mul_nonneg ha'0 hq0]
    nlinarith [mul_le_mul_of_nonneg_left hCq ha'0]
  refine ⟨h3, ?_⟩
  calc opNorm (resX Λ z x - resX Λ z x') ≤ CR * a' * q := h2
    _ ≤ CR * (2 * CR) * q := by gcongr
    _ = 4 * CR ^ 2 / (N : ℝ) ^ 6 := by rw [hq]; ring

/-- The union bound over a finite grid `S` of at most `N^{D_g}` points, each with failure
probability `≤ N^{-(D' + D_g)}`, together with a null set. -/
private lemma FNet_union {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ) (hN : 1 ≤ N)
    (D' Dg : ℝ) (S : Finset ι) (hS : (S.card : ℝ) ≤ (N : ℝ) ^ Dg) (Bad Null : Set Ω)
    (E : ι → Set Ω) (hNull : P Null = 0) (hsub : Bad ⊆ Null ∪ ⋃ x ∈ S, E x)
    (hE : ∀ x ∈ S, P (E x) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + Dg)))) :
    P Bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc P Bad ≤ P (Null ∪ ⋃ x ∈ S, E x) := measure_mono hsub
    _ ≤ P Null + P (⋃ x ∈ S, E x) := measure_union_le _ _
    _ ≤ 0 + ∑ x ∈ S, P (E x) := by
        rw [hNull]
        exact add_le_add le_rfl (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _x ∈ S, ENNReal.ofReal ((N : ℝ) ^ (-(D' + Dg))) := by
        rw [zero_add]
        exact Finset.sum_le_sum hE
    _ = ENNReal.ofReal ((S.card : ℝ) * (N : ℝ) ^ (-(D' + Dg))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
        apply ENNReal.ofReal_le_ofReal
        calc (S.card : ℝ) * (N : ℝ) ^ (-(D' + Dg))
            ≤ (N : ℝ) ^ Dg * (N : ℝ) ^ (-(D' + Dg)) :=
              mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg hN0.le _)
          _ = (N : ℝ) ^ (-D') := by
              rw [← Real.rpow_add hN0]
              congr 1
              ring

/-- Real arithmetic of the net step: `c t + E ≤ a² ζ` when `c ≤ 2 C_R`, `t ≤ a ζ`, `E ≤ ζ/2` and
`a ≥ 4 C_R`. -/
private lemma FNet_close (a ζ t c E CR : ℝ) (hCR : 1 ≤ CR) (ha : 4 * CR ≤ a) (hζ : 0 ≤ ζ)
    (hE : E ≤ ζ / 2) (hc : c ≤ 2 * CR) (ht0 : 0 ≤ t) (ht : t ≤ a * ζ) :
    c * t + E ≤ a * a * ζ := by
  have h1 : c * t ≤ 2 * CR * (a * ζ) := mul_le_mul hc ht ht0 (by linarith)
  have ha0 : 0 ≤ a := by linarith
  have ha1 : 1 ≤ a := by linarith
  have h2 : 2 * CR * (a * ζ) ≤ a * a * ζ / 2 := by
    nlinarith [mul_nonneg (mul_nonneg ha0 hζ) (by linarith : (0 : ℝ) ≤ a - 4 * CR)]
  have h3 : ζ / 2 ≤ a * a * ζ / 2 := by
    nlinarith [mul_nonneg hζ (by nlinarith : (0 : ℝ) ≤ a * a - 1)]
  linarith

/-- The control parameters are at least `N⁻¹` and `N⁻²`: `Ψ_φ ≥ 1/(Nη)` and
`(1 + |z|)^K ≥ 1 + |z| ≥ η` for `K ≥ 1`. -/
private lemma FNet_zeta_lb {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (N : ℕ)
    (hN : 1 ≤ N) (z : ℂ) (hz : 0 < z.im) (φ K : ℝ) (hφ : 0 ≤ φ) (hK : 1 ≤ K) :
    (N : ℝ)⁻¹ ≤ (1 + ‖z‖) ^ K * (1 + φ) ^ 3 * psiPhi Λ N z φ ∧
      ((N : ℝ)⁻¹) ^ 2 ≤ (1 + ‖z‖) ^ (2 * K) * (1 + φ) ^ 6 * psiPhi Λ N z φ ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hψ : 1 / ((N : ℝ) * z.im) ≤ psiPhi Λ N z φ := by
    unfold psiPhi
    linarith [Real.sqrt_nonneg (((mExt Λ z).im + φ) / ((N : ℝ) * z.im))]
  have hψ0 : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
  have hz1 : z.im ≤ 1 + ‖z‖ := (Complex.im_le_norm z).trans (by linarith)
  have hb : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hφ1 : 1 ≤ 1 + φ := by linarith
  have hK1 : 1 + ‖z‖ ≤ (1 + ‖z‖) ^ K := by
    calc 1 + ‖z‖ = (1 + ‖z‖) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 + ‖z‖) ^ K := Real.rpow_le_rpow_of_exponent_le hb hK
  have hK2 : (1 + ‖z‖) ^ 2 ≤ (1 + ‖z‖) ^ (2 * K) := by
    calc (1 + ‖z‖) ^ 2 = (1 + ‖z‖) ^ (2 : ℝ) := (Real.rpow_two _).symm
      _ ≤ (1 + ‖z‖) ^ (2 * K) := Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  have hη : z.im * (1 / ((N : ℝ) * z.im)) = (N : ℝ)⁻¹ := by field_simp
  have hΨ0 : 0 ≤ psiPhi Λ N z φ := hψ0.trans hψ
  have hP0 : 0 ≤ (1 + ‖z‖) ^ K := Real.rpow_nonneg (by linarith) _
  have h3 : 1 ≤ (1 + φ) ^ 3 := one_le_pow₀ hφ1
  have h6 : 1 ≤ (1 + φ) ^ 6 := one_le_pow₀ hφ1
  constructor
  · calc (N : ℝ)⁻¹ = z.im * (1 / ((N : ℝ) * z.im)) := hη.symm
      _ ≤ (1 + ‖z‖) ^ K * psiPhi Λ N z φ := mul_le_mul (hz1.trans hK1) hψ hψ0 hP0
      _ = (1 + ‖z‖) ^ K * 1 * psiPhi Λ N z φ := by ring
      _ ≤ (1 + ‖z‖) ^ K * (1 + φ) ^ 3 * psiPhi Λ N z φ := by gcongr
  · calc ((N : ℝ)⁻¹) ^ 2 = (z.im * (1 / ((N : ℝ) * z.im))) ^ 2 := by rw [hη]
      _ ≤ ((1 + ‖z‖) * psiPhi Λ N z φ) ^ 2 := by
          gcongr
      _ = (1 + ‖z‖) ^ 2 * 1 * psiPhi Λ N z φ ^ 2 := by ring
      _ ≤ (1 + ‖z‖) ^ (2 * K) * (1 + φ) ^ 6 * psiPhi Λ N z φ ^ 2 := by gcongr

/-- Size facts at a fixed `N ≥ 1` and `z ∈ Z_N` (`Im z ≥ N^{-1+τ}`, `|z| ≤ N^{δ₀}`, `δ₀ ≤ τ`,
`‖A‖ ≤ N^{-δ_A}`): `Im z > 0`, `(Im z)⁻¹ ≤ N`, and `1 + (‖Λ‖ + |z|)/η + 1/η² ≤ (2D² + 3) N³`. -/
private lemma FNet_level (D : ℕ) (δA τ δ₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) (hδτ : δ₀ ≤ τ)
    (N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) (hA : opNorm A ≤ (N : ℝ) ^ (-δA))
    (z : ℂ) (hz : ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im) :
    0 < z.im ∧ z.im⁻¹ ≤ N ∧
      1 + (opNorm (lam D N A) + ‖z‖) / z.im + 1 / z.im ^ 2 ≤
        (2 * (D : ℝ) ^ 2 + 3) * (N : ℝ) ^ 3 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hpos : 0 < (N : ℝ) ^ (-1 + τ) := Real.rpow_pos_of_pos hN0 _
  have hηpos : 0 < z.im := lt_of_lt_of_le hpos hz.2
  have hinv : z.im⁻¹ ≤ (N : ℝ) ^ (1 - τ) := by
    calc z.im⁻¹ ≤ ((N : ℝ) ^ (-1 + τ))⁻¹ := inv_anti₀ hpos hz.2
      _ = (N : ℝ) ^ (1 - τ) := by
          rw [← Real.rpow_neg hN0.le]
          congr 1
          ring
  have hinvN : z.im⁻¹ ≤ N := by
    refine hinv.trans ?_
    calc (N : ℝ) ^ (1 - τ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ = N := Real.rpow_one _
  refine ⟨hηpos, hinvN, ?_⟩
  have hA1 : opNorm A ≤ 1 := hA.trans (Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith))
  have hL : opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
    refine (FNet_opNorm_lam D N A).trans ?_
    have : 0 ≤ 2 * ((D : ℝ) * N) ^ 2 := by positivity
    calc 2 * ((D : ℝ) * N) ^ 2 * opNorm A ≤ 2 * ((D : ℝ) * N) ^ 2 * 1 := by gcongr
      _ = 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ 2 := by ring
  have hzη : ‖z‖ * z.im⁻¹ ≤ N := by
    calc ‖z‖ * z.im⁻¹ ≤ (N : ℝ) ^ δ₀ * (N : ℝ) ^ (1 - τ) :=
          mul_le_mul hz.1 hinv (inv_nonneg.mpr hηpos.le) (Real.rpow_nonneg hN0.le _)
      _ = (N : ℝ) ^ (δ₀ + (1 - τ)) := (Real.rpow_add hN0 _ _).symm
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ = N := Real.rpow_one _
  have hΛη : opNorm (lam D N A) * z.im⁻¹ ≤ 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ 2 * N :=
    mul_le_mul hL hinvN (inv_nonneg.mpr hηpos.le) (by positivity)
  have hη2 : 1 / z.im ^ 2 ≤ (N : ℝ) ^ 2 := by
    have : 1 / z.im ^ 2 = z.im⁻¹ * z.im⁻¹ := by rw [one_div, sq, mul_inv]
    rw [this, sq]
    exact mul_le_mul hinvN hinvN (inv_nonneg.mpr hηpos.le) hN0.le
  have e : (opNorm (lam D N A) + ‖z‖) / z.im =
      opNorm (lam D N A) * z.im⁻¹ + ‖z‖ * z.im⁻¹ := by rw [div_eq_mul_inv, add_mul]
  rw [e]
  have hD0 : (0 : ℝ) ≤ (D : ℝ) ^ 2 := by positivity
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ hNr
  have h2 : (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [mul_nonneg hN0.le hN0.le]
  have h3 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by nlinarith
  nlinarith

/-- The grid point near `x̃ = σ_θ g`, `g_a = D⟨G E_a⟩`, on `‖R_x̃‖ ≤ C_R`: `‖x̃‖ ≤ (Im z)⁻¹ ≤ N` and
`Im x̃_b ≥ 0` for the resolvent `G` of a Hermitian matrix. -/
private lemma FNet_core {D N : ℕ} (hN : 6 ≤ N) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (Λ H : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (hH : H.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (hη : z.im⁻¹ ≤ N) (CR : ℝ) (hCR : 1 ≤ CR) (hCRN : 4 * CR ≤ (N : ℝ) ^ 6)
    (G : Finset (Fin D → ℂ))
    (hG : ∀ x : Fin D → ℂ, (∀ b, ‖x b‖ ≤ N ∧ 0 ≤ (x b).im) →
      ∃ x' ∈ G, (∀ b, 0 ≤ (x' b).im) ∧ ‖x - x'‖ ≤ 2 / (N : ℝ) ^ 6)
    (hcut : opNorm (resX Λ z (sigTheta D θ *ᵥ blockTr D N (res (H + Λ) z))) ≤ CR) :
    ∃ x' ∈ G, opNorm (resX Λ z x') ≤ 2 * CR ∧
      opNorm (resX Λ z (sigTheta D θ *ᵥ blockTr D N (res (H + Λ) z)) - resX Λ z x') ≤
        4 * CR ^ 2 / (N : ℝ) ^ 6 := by
  obtain ⟨hbox, himx⟩ := FNet_xt D N θ h0 h1 (H + Λ) (hH.add hΛ) z hz
  exact FNet_approx hN Λ hΛ z hz CR hCR hCRN G hG _
    (fun b => ⟨(norm_le_pi_norm _ b).trans (hbox.trans hη), himx b⟩) hcut

/-- The thresholds of the net bound, for `N ≥ 6` and `N ≥ 8 C_R² (2D² + 3)`: `4 C_R ≤ N^6` and
`4 C_R²/N^6 · (2D² + 3) N³ ≤ N⁻²/2`. -/
private lemma FNet_thresholds (D N : ℕ) (CR : ℝ) (hCR : 1 ≤ CR) (hN : 6 ≤ N)
    (hM : 8 * CR ^ 2 * (2 * (D : ℝ) ^ 2 + 3) ≤ N) :
    4 * CR ≤ (N : ℝ) ^ 6 ∧
      4 * CR ^ 2 / (N : ℝ) ^ 6 * ((2 * (D : ℝ) ^ 2 + 3) * (N : ℝ) ^ 3) ≤ ((N : ℝ)⁻¹) ^ 2 / 2 := by
  have hNr : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hD0 : (0 : ℝ) ≤ (D : ℝ) ^ 2 := by positivity
  have hCR2 : CR ≤ CR ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · have h1 : 4 * CR ≤ 8 * CR ^ 2 * (2 * (D : ℝ) ^ 2 + 3) := by nlinarith
    have h2 : (N : ℝ) ≤ (N : ℝ) ^ 6 := by
      have : (1 : ℝ) ≤ N := by linarith
      calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ) ^ 6 := pow_le_pow_right₀ this (by norm_num)
    linarith
  · have e : 4 * CR ^ 2 / (N : ℝ) ^ 6 * ((2 * (D : ℝ) ^ 2 + 3) * (N : ℝ) ^ 3) =
        (4 * CR ^ 2 * (2 * (D : ℝ) ^ 2 + 3)) / (N : ℝ) ^ 3 := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have : (N : ℝ)⁻¹ ^ 2 / 2 * (N : ℝ) ^ 3 = (N : ℝ) / 2 := by field_simp
    rw [this]
    nlinarith

/-- The isotropic part of `fluct_net'`, from the bound for the deterministic vectors
`R_x̂^* u / ‖R_x̂^* u‖` at the points `x̂` of the grid and a union bound. -/
private lemma FNet_iso (D : ℕ) (δA τ δ₀ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hseq : LLSeq D δA C θ μ A) (hτ : 0 < τ) (hδτ : δ₀ ≤ τ)
    (Z : ℕ → Set ℂ) (hZ : ∀ N, ∀ z ∈ Z N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im)
    (φ : ℕ → ℂ → ℝ) (hφ : ∀ N, ∀ z ∈ Z N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ δ₀)
    (K Ki : ℝ) (hK1 : 1 ≤ K) (hKK : Ki ≤ K)
    (hpre : PrecS μ (U := fun N => {z // z ∈ Z N} × {u : Idx D N → ℂ // ∑ i, ‖u i‖ ^ 2 = 1} ×
        {v : Idx D N → ℂ // ∑ i, ‖v i‖ ^ 2 = 1})
      (fun N w h => ‖star w.2.1.1 ⬝ᵥ
        (hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1 *ᵥ w.2.2.1)‖)
      (fun N w _ => (1 + ‖w.1.1‖) ^ Ki * (1 + φ N w.1.1) ^ 3 *
        psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1)))
    (CR : ℝ) (hCR : 1 ≤ CR) :
    PrecS μ (U := fun N => {z // z ∈ Z N} × {u : Idx D N → ℂ // ∑ i, ‖u i‖ ^ 2 = 1} ×
        {v : Idx D N → ℂ // ∑ i, ‖v i‖ ^ 2 = 1})
      (fun N w h =>
        if opNorm (resX (lam D N (A N)) w.1.1 (sigTheta D (θ N) *ᵥ
            blockTr D N (res (Matrix.of h + lam D N (A N)) w.1.1))) ≤ CR then
          ‖star w.2.1.1 ⬝ᵥ ((resX (lam D N (A N)) w.1.1 (sigTheta D (θ N) *ᵥ
            blockTr D N (res (Matrix.of h + lam D N (A N)) w.1.1)) *
              hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1) *ᵥ w.2.2.1)‖
        else 0)
      (fun N w _ => (1 + ‖w.1.1‖) ^ K * (1 + φ N w.1.1) ^ 3 *
        psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1)) := by
  intro τ' hτ' D' hD'
  have hD1 : 1 ≤ D := hseq.one_le_D
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  obtain ⟨N₀, hN₀⟩ := hpre (τ' / 2) (half_pos hτ') (D' + 15 * D) (by positivity)
  obtain ⟨N₃, hN₃⟩ : ∃ N₃ : ℕ, ∀ N : ℕ, N₃ ≤ N → 4 * CR ≤ (N : ℝ) ^ (τ' / 2) :=
    eventually_atTop.mp (((tendsto_rpow_atTop (half_pos hτ')).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (4 * CR))
  set Mx : ℝ := 8 * CR ^ 2 * (2 * (D : ℝ) ^ 2 + 3) with hMx
  refine ⟨max (max N₀ N₃) (max 6 ⌈Mx⌉₊), fun N hN w => ?_⟩
  have hNN₀ : N₀ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNN₃ : N₃ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN6 : 6 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNMx : Mx ≤ N :=
    (Nat.le_ceil Mx).trans
      (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN1 : 1 ≤ N := by omega
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hCRN, hEb⟩ := FNet_thresholds D N CR hCR hN6 hNMx
  obtain ⟨⟨z, hzZ⟩, ⟨u, hu⟩, ⟨v, hv⟩⟩ := w
  dsimp only
  obtain ⟨hηpos, hηN, hYb⟩ := FNet_level D δA τ δ₀ hseq.pos hτ hδτ N hN1 (A N) (hseq.small N) z
    (hZ N z hzZ)
  have hφ0 : 0 ≤ φ N z := le_trans (by positivity) (hφ N z hzZ).1
  obtain ⟨hζ1, -⟩ := FNet_zeta_lb (lam D N (A N)) N hN1 z hηpos (φ N z) K hφ0 hK1
  set Λ := lam D N (A N) with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N (A N)
  set ζK : ℝ := (1 + ‖z‖) ^ K * (1 + φ N z) ^ 3 * psiPhi Λ N z (φ N z) with hζK
  have hNinv1 : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNr1
  have hNinv0 : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hζ0 : 0 ≤ ζK := hNinv0.trans hζ1
  have hEζ : 4 * CR ^ 2 / (N : ℝ) ^ 6 * ((2 * (D : ℝ) ^ 2 + 3) * (N : ℝ) ^ 3) ≤ ζK / 2 := by
    refine hEb.trans ?_
    have : ((N : ℝ)⁻¹) ^ 2 ≤ (N : ℝ)⁻¹ := by nlinarith
    linarith
  set a : ℝ := (N : ℝ) ^ (τ' / 2) with ha
  have ha4 : 4 * CR ≤ a := hN₃ N hNN₃
  have haa : (N : ℝ) ^ τ' = a * a := by
    rw [ha, ← Real.rpow_add hN0]
    congr 1
    ring
  have hnull : μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := ae_iff.mp (hseq.mem N).herm
  obtain ⟨G, hGc, hG⟩ := FNet_grid D N hN6
  set G' := G.filter (fun x => opNorm (resX Λ z x) ≤ 2 * CR) with hG'
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hdir : ∀ x : Fin D → ℂ, ∃ p : Idx D N → ℂ, ∑ i, ‖p i‖ ^ 2 = 1 ∧ ∃ c : ℝ, 0 ≤ c ∧
      c ≤ opNorm (resX Λ z x) ∧ ∀ (Y : Matrix (Idx D N) (Idx D N) ℂ) (v : Idx D N → ℂ),
        star u ⬝ᵥ ((resX Λ z x * Y) *ᵥ v) = (c : ℂ) * (star p ⬝ᵥ (Y *ᵥ v)) :=
    fun x => FNet_dir _ u hu
  choose p hp c hc0 hcle hceq using hdir
  refine FNet_union (μ N) N hN1 D' (15 * D) G' ?_ _ {h | ¬ (Matrix.of h).IsHermitian}
    (fun x => {h | a * ζK <
      ‖star (p x) ⬝ᵥ (hgUnder D N (θ N) (Matrix.of h) Λ z *ᵥ v)‖}) hnull ?_ ?_
  · calc (G'.card : ℝ) ≤ ((N ^ (15 * D) : ℕ) : ℝ) := by
          exact_mod_cast (Finset.card_filter_le _ _).trans hGc
      _ = (N : ℝ) ^ (15 * (D : ℝ)) := by
          rw [show (15 * (D : ℝ)) = ((15 * D : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
          push_cast
          ring
  · intro h hh
    simp only [Set.mem_ofPred_eq] at hh
    by_cases hherm : (Matrix.of h).IsHermitian
    · right
      by_cases hcut : opNorm (resX Λ z (sigTheta D (θ N) *ᵥ
          blockTr D N (res (Matrix.of h + Λ) z))) ≤ CR
      · simp only [hcut, ↓reduceIte] at hh
        obtain ⟨x', hx'G, hx'R, hx'err⟩ := FNet_core hN6 (θ N) (hseq.theta N).1 (hseq.theta N).2 Λ
          (Matrix.of h) hΛ hherm z hηpos hηN CR hCR hCRN G hG hcut
        simp only [Set.mem_iUnion]
        refine ⟨x', Finset.mem_filter.mpr ⟨hx'G, hx'R⟩, ?_⟩
        simp only [Set.mem_ofPred_eq]
        by_contra hnot
        rw [not_lt] at hnot
        set Y := hgUnder D N (θ N) (Matrix.of h) Λ z with hY
        set Rt := resX Λ z (sigTheta D (θ N) *ᵥ blockTr D N (res (Matrix.of h + Λ) z)) with hRt
        have hYn : opNorm Y ≤ (2 * (D : ℝ) ^ 2 + 3) * (N : ℝ) ^ 3 :=
          (FNet_Y_le D N (θ N) (hseq.theta N).1 (hseq.theta N).2 (Matrix.of h) Λ hherm hΛ z
            hηpos).trans hYb
        have hdecomp : star u ⬝ᵥ ((Rt * Y) *ᵥ v) =
            (c x' : ℂ) * (star (p x') ⬝ᵥ (Y *ᵥ v)) +
              star u ⬝ᵥ (((Rt - resX Λ z x') * Y) *ᵥ v) := by
          rw [← hceq x' Y v, ← dotProduct_add, ← Matrix.add_mulVec, ← Matrix.add_mul]
          congr 3
          abel
        have hxi : ‖star u ⬝ᵥ ((Rt * Y) *ᵥ v)‖ ≤ c x' * ‖star (p x') ⬝ᵥ (Y *ᵥ v)‖ +
            4 * CR ^ 2 / (N : ℝ) ^ 6 * ((2 * (D : ℝ) ^ 2 + 3) * (N : ℝ) ^ 3) := by
          rw [hdecomp]
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 x')]
          · refine (FNet_form_le _ u v hu.le hv.le).trans
              ((opNorm_mul_le _ _).trans ?_)
            exact mul_le_mul hx'err hYn (FNet_opNorm_nonneg _) (by positivity)
        have hcl := FNet_close a ζK ‖star (p x') ⬝ᵥ (Y *ᵥ v)‖ (c x') _ CR hCR ha4 hζ0 hEζ
          ((hcle x').trans hx'R) (norm_nonneg _) hnot
        rw [haa] at hh
        linarith
      · simp only [hcut, ↓reduceIte] at hh
        exfalso
        have : 0 ≤ (N : ℝ) ^ τ' * ζK := mul_nonneg (Real.rpow_nonneg hN0.le _) hζ0
        linarith
    · left
      exact hherm
  · intro x hx
    have h1 := hN₀ N hNN₀ ⟨⟨z, hzZ⟩, ⟨p x, hp x⟩, ⟨v, hv⟩⟩
    refine le_trans (measure_mono ?_) h1
    intro h hh
    simp only [Set.mem_ofPred_eq] at hh ⊢
    have hb : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hle : (1 + ‖z‖) ^ Ki * (1 + φ N z) ^ 3 * psiPhi Λ N z (φ N z) ≤ ζK := by
      have hΨ0 : 0 ≤ psiPhi Λ N z (φ N z) := by
        unfold psiPhi
        have : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
        have := Real.sqrt_nonneg (((mExt Λ z).im + φ N z) / ((N : ℝ) * z.im))
        linarith
      rw [hζK]
      have hP : (1 + ‖z‖) ^ Ki ≤ (1 + ‖z‖) ^ K := Real.rpow_le_rpow_of_exponent_le hb hKK
      have hQ0 : 0 ≤ (1 + φ N z) ^ 3 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP hQ0) hΨ0
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hN0.le _)) hh

/-- The normalized trace is additive. -/
private lemma FNet_ntr_add {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P + Q) = ntr P + ntr Q := by
  simp [ntr, Matrix.trace_add, mul_add]

/-- The normalized trace is homogeneous. -/
private lemma FNet_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (P : Matrix ι ι ℂ) :
    ntr (c • P) = c * ntr P := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

/-- The averaged part of `fluct_net'`, from the bound for the deterministic matrices
`B R_x̂ / (2 C_R)` at the points `x̂` of the grid with `‖R_x̂‖ ≤ 2 C_R` and a union bound. -/
private lemma FNet_avg (D : ℕ) (δA τ δ₀ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hseq : LLSeq D δA C θ μ A) (hτ : 0 < τ) (hδτ : δ₀ ≤ τ)
    (Z : ℕ → Set ℂ) (hZ : ∀ N, ∀ z ∈ Z N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im)
    (φ : ℕ → ℂ → ℝ) (hφ : ∀ N, ∀ z ∈ Z N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ δ₀)
    (K Ka : ℝ) (hK1 : 1 ≤ K) (hKK : Ka ≤ K)
    (hpre : PrecS μ (U := fun N => {z // z ∈ Z N} ×
        {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1})
      (fun N w h => ‖ntr (w.2.1 * hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1)‖)
      (fun N w _ => (1 + ‖w.1.1‖) ^ (2 * Ka) * (1 + φ N w.1.1) ^ 6 *
        psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1) ^ 2))
    (CR : ℝ) (hCR : 1 ≤ CR) :
    PrecS μ (U := fun N => {z // z ∈ Z N} × {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1})
      (fun N w h =>
        if opNorm (resX (lam D N (A N)) w.1.1 (sigTheta D (θ N) *ᵥ
            blockTr D N (res (Matrix.of h + lam D N (A N)) w.1.1))) ≤ CR then
          ‖ntr (w.2.1 * resX (lam D N (A N)) w.1.1 (sigTheta D (θ N) *ᵥ
            blockTr D N (res (Matrix.of h + lam D N (A N)) w.1.1)) *
              hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1)‖
        else 0)
      (fun N w _ => (1 + ‖w.1.1‖) ^ (2 * K) * (1 + φ N w.1.1) ^ 6 *
        psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1) ^ 2) := by
  intro τ' hτ' D' hD'
  have hD1 : 1 ≤ D := hseq.one_le_D
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  obtain ⟨N₀, hN₀⟩ := hpre (τ' / 2) (half_pos hτ') (D' + 15 * D) (by positivity)
  obtain ⟨N₃, hN₃⟩ : ∃ N₃ : ℕ, ∀ N : ℕ, N₃ ≤ N → 4 * CR ≤ (N : ℝ) ^ (τ' / 2) :=
    eventually_atTop.mp (((tendsto_rpow_atTop (half_pos hτ')).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (4 * CR))
  set Mx : ℝ := 8 * CR ^ 2 * (2 * (D : ℝ) ^ 2 + 3) with hMx
  refine ⟨max (max N₀ N₃) (max 6 ⌈Mx⌉₊), fun N hN w => ?_⟩
  have hNN₀ : N₀ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNN₃ : N₃ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN6 : 6 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNMx : Mx ≤ N :=
    (Nat.le_ceil Mx).trans
      (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN1 : 1 ≤ N := by omega
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hCRN, hEb⟩ := FNet_thresholds D N CR hCR hN6 hNMx
  obtain ⟨⟨z, hzZ⟩, ⟨B, hB⟩⟩ := w
  dsimp only
  obtain ⟨hηpos, hηN, hYb⟩ := FNet_level D δA τ δ₀ hseq.pos hτ hδτ N hN1 (A N) (hseq.small N) z
    (hZ N z hzZ)
  have hφ0 : 0 ≤ φ N z := le_trans (by positivity) (hφ N z hzZ).1
  obtain ⟨-, hζ2⟩ := FNet_zeta_lb (lam D N (A N)) N hN1 z hηpos (φ N z) K hφ0 hK1
  set Λ := lam D N (A N) with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N (A N)
  set ζK : ℝ := (1 + ‖z‖) ^ (2 * K) * (1 + φ N z) ^ 6 * psiPhi Λ N z (φ N z) ^ 2 with hζK
  have hζ0 : 0 ≤ ζK := (sq_nonneg _).trans hζ2
  have hEζ : 4 * CR ^ 2 / (N : ℝ) ^ 6 * ((2 * (D : ℝ) ^ 2 + 3) * (N : ℝ) ^ 3) ≤ ζK / 2 := by
    linarith
  set a : ℝ := (N : ℝ) ^ (τ' / 2) with ha
  have ha4 : 4 * CR ≤ a := hN₃ N hNN₃
  have haa : (N : ℝ) ^ τ' = a * a := by
    rw [ha, ← Real.rpow_add hN0]
    congr 1
    ring
  have hnull : μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := ae_iff.mp (hseq.mem N).herm
  obtain ⟨G, hGc, hG⟩ := FNet_grid D N hN6
  set G' := G.filter (fun x => opNorm (resX Λ z x) ≤ 2 * CR) with hG'
  have hCR0 : 0 < 2 * CR := by linarith
  set Bx : (Fin D → ℂ) → Matrix (Idx D N) (Idx D N) ℂ :=
    fun x => (((2 * CR)⁻¹ : ℝ) : ℂ) • (B * resX Λ z x) with hBx
  have hBxn : ∀ x ∈ G', opNorm (Bx x) ≤ 1 := by
    intro x hx
    have hxR : opNorm (resX Λ z x) ≤ 2 * CR := (Finset.mem_filter.mp hx).2
    rw [hBx]
    dsimp only
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (2 * CR)⁻¹ * opNorm (B * resX Λ z x) ≤ (2 * CR)⁻¹ * (1 * (2 * CR)) := by
          gcongr
          exact (opNorm_mul_le _ _).trans
            (mul_le_mul hB hxR (FNet_opNorm_nonneg _) zero_le_one)
      _ = 1 := by field_simp
  refine FNet_union (μ N) N hN1 D' (15 * D) G' ?_ _ {h | ¬ (Matrix.of h).IsHermitian}
    (fun x => {h | a * ζK < ‖ntr (Bx x * hgUnder D N (θ N) (Matrix.of h) Λ z)‖}) hnull ?_ ?_
  · calc (G'.card : ℝ) ≤ ((N ^ (15 * D) : ℕ) : ℝ) := by
          exact_mod_cast (Finset.card_filter_le _ _).trans hGc
      _ = (N : ℝ) ^ (15 * (D : ℝ)) := by
          rw [show (15 * (D : ℝ)) = ((15 * D : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
          push_cast
          ring
  · intro h hh
    simp only [Set.mem_ofPred_eq] at hh
    by_cases hherm : (Matrix.of h).IsHermitian
    · right
      by_cases hcut : opNorm (resX Λ z (sigTheta D (θ N) *ᵥ
          blockTr D N (res (Matrix.of h + Λ) z))) ≤ CR
      · simp only [hcut, ↓reduceIte] at hh
        obtain ⟨x', hx'G, hx'R, hx'err⟩ := FNet_core hN6 (θ N) (hseq.theta N).1 (hseq.theta N).2 Λ
          (Matrix.of h) hΛ hherm z hηpos hηN CR hCR hCRN G hG hcut
        simp only [Set.mem_iUnion]
        refine ⟨x', Finset.mem_filter.mpr ⟨hx'G, hx'R⟩, ?_⟩
        simp only [Set.mem_ofPred_eq]
        by_contra hnot
        rw [not_lt] at hnot
        set Y := hgUnder D N (θ N) (Matrix.of h) Λ z with hY
        set Rt := resX Λ z (sigTheta D (θ N) *ᵥ blockTr D N (res (Matrix.of h + Λ) z)) with hRt
        have hYn : opNorm Y ≤ (2 * (D : ℝ) ^ 2 + 3) * (N : ℝ) ^ 3 :=
          (FNet_Y_le D N (θ N) (hseq.theta N).1 (hseq.theta N).2 (Matrix.of h) Λ hherm hΛ z
            hηpos).trans hYb
        have hBR : B * resX Λ z x' = (((2 * CR : ℝ)) : ℂ) • Bx x' := by
          rw [hBx]
          dsimp only
          rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hCR0.ne', Complex.ofReal_one,
            one_smul]
        have hdecomp : ntr ((B * Rt) * Y) =
            (((2 * CR : ℝ)) : ℂ) * ntr (Bx x' * Y) + ntr ((B * (Rt - resX Λ z x')) * Y) := by
          have e1 : (B * Rt) * Y = (((2 * CR : ℝ)) : ℂ) • (Bx x' * Y) +
              (B * (Rt - resX Λ z x')) * Y := by
            rw [← Matrix.smul_mul, ← hBR, ← Matrix.add_mul, ← Matrix.mul_add]
            congr 2
            abel
          rw [e1, FNet_ntr_add, FNet_ntr_smul]
        have hxi : ‖ntr ((B * Rt) * Y)‖ ≤ (2 * CR) * ‖ntr (Bx x' * Y)‖ +
            4 * CR ^ 2 / (N : ℝ) ^ 6 * ((2 * (D : ℝ) ^ 2 + 3) * (N : ℝ) ^ 3) := by
          rw [hdecomp]
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCR0.le]
          · refine (FNet_ntr_le _).trans ((opNorm_mul_le _ _).trans ?_)
            have h2 : opNorm (B * (Rt - resX Λ z x')) ≤ 1 * (4 * CR ^ 2 / (N : ℝ) ^ 6) :=
              (opNorm_mul_le _ _).trans
                (mul_le_mul hB hx'err (FNet_opNorm_nonneg _) zero_le_one)
            calc opNorm (B * (Rt - resX Λ z x')) * opNorm Y
                ≤ (1 * (4 * CR ^ 2 / (N : ℝ) ^ 6)) * ((2 * (D : ℝ) ^ 2 + 3) * (N : ℝ) ^ 3) :=
                  mul_le_mul h2 hYn (FNet_opNorm_nonneg _) (by positivity)
              _ = 4 * CR ^ 2 / (N : ℝ) ^ 6 * ((2 * (D : ℝ) ^ 2 + 3) * (N : ℝ) ^ 3) := by ring
        have hcl := FNet_close a ζK ‖ntr (Bx x' * Y)‖ (2 * CR) _ CR hCR ha4 hζ0 hEζ le_rfl
          (norm_nonneg _) hnot
        rw [haa] at hh
        linarith
      · simp only [hcut, ↓reduceIte] at hh
        exfalso
        have : 0 ≤ (N : ℝ) ^ τ' * ζK := mul_nonneg (Real.rpow_nonneg hN0.le _) hζ0
        linarith
    · left
      exact hherm
  · intro x hx
    have h1 := hN₀ N hNN₀ ⟨⟨z, hzZ⟩, ⟨Bx x, hBxn x hx⟩⟩
    refine le_trans (measure_mono ?_) h1
    intro h hh
    simp only [Set.mem_ofPred_eq] at hh ⊢
    have hb : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hle : (1 + ‖z‖) ^ (2 * Ka) * (1 + φ N z) ^ 6 * psiPhi Λ N z (φ N z) ^ 2 ≤ ζK := by
      rw [hζK]
      have hP : (1 + ‖z‖) ^ (2 * Ka) ≤ (1 + ‖z‖) ^ (2 * K) :=
        Real.rpow_le_rpow_of_exponent_le hb (by linarith)
      have hQ0 : 0 ≤ (1 + φ N z) ^ 6 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP hQ0) (sq_nonneg _)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hN0.le _)) hh

/-- The net bound for the random `R_x̃`, `x̃ = σ_θ g`, `g_a = D⟨G E_a⟩`, with a priori bound up to
`N^{δ₀}` on spectral sets that may grow with `N`, under `LLSeq`, `K δ₀ ≤ τ` and `aprioriLL`:
for every `C_R ≥ 1`, `1(‖R_x̃‖ ≤ C_R) |(R_x̃ H̲G)_{uv}| ≺ (1 + |z|)^K (1 + φ)³ Ψ_φ` and
`1(‖R_x̃‖ ≤ C_R) |⟨B R_x̃ H̲G⟩| ≺ (1 + |z|)^{2K} (1 + φ)⁶ Ψ_φ²`, in sup form over `z ∈ Z_N`,
deterministic unit `u, v` and deterministic `‖B‖ ≤ 1`. -/
theorem fluct_net' : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (D : ℕ) (δA τ δ₀ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
      (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ),
      LLSeq D δA C θ μ A → 0 < τ → 0 ≤ δ₀ → K * δ₀ ≤ τ →
    ∀ Z : ℕ → Set ℂ, (∀ N, ∀ z ∈ Z N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im) →
    ∀ φ : ℕ → ℂ → ℝ, (∀ N, ∀ z ∈ Z N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ δ₀) →
    aprioriLL D μ A Z φ → ∀ CR : ℝ, 1 ≤ CR →
    PrecS μ (U := fun N => {z // z ∈ Z N} × {u : Idx D N → ℂ // ∑ i, ‖u i‖ ^ 2 = 1} ×
        {v : Idx D N → ℂ // ∑ i, ‖v i‖ ^ 2 = 1})
      (fun N w h =>
        if opNorm (resX (lam D N (A N)) w.1.1 (sigTheta D (θ N) *ᵥ
            blockTr D N (res (Matrix.of h + lam D N (A N)) w.1.1))) ≤ CR then
          ‖star w.2.1.1 ⬝ᵥ ((resX (lam D N (A N)) w.1.1 (sigTheta D (θ N) *ᵥ
            blockTr D N (res (Matrix.of h + lam D N (A N)) w.1.1)) *
              hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1) *ᵥ w.2.2.1)‖
        else 0)
      (fun N w _ => (1 + ‖w.1.1‖) ^ K * (1 + φ N w.1.1) ^ 3 *
        psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1)) ∧
    PrecS μ (U := fun N => {z // z ∈ Z N} × {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1})
      (fun N w h =>
        if opNorm (resX (lam D N (A N)) w.1.1 (sigTheta D (θ N) *ᵥ
            blockTr D N (res (Matrix.of h + lam D N (A N)) w.1.1))) ≤ CR then
          ‖ntr (w.2.1 * resX (lam D N (A N)) w.1.1 (sigTheta D (θ N) *ᵥ
            blockTr D N (res (Matrix.of h + lam D N (A N)) w.1.1)) *
              hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1)‖
        else 0)
      (fun N w _ => (1 + ‖w.1.1‖) ^ (2 * K) * (1 + φ N w.1.1) ^ 6 *
        psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1) ^ 2) := by
  obtain ⟨Ki, hKi1, hKi⟩ := fluct_iso_prec'
  obtain ⟨Ka, hKa1, hKa⟩ := fluct_avg_prec'
  have hK1 : 1 ≤ max Ki Ka := le_max_of_le_left hKi1
  refine ⟨max Ki Ka, hK1, ?_⟩
  intro D δA τ δ₀ C θ μ A hseq hτ hδ₀ hδτ Z hZ φ hφ hLL CR hCR
  have hδτ' : δ₀ ≤ τ := by nlinarith
  have hi : Ki * δ₀ ≤ τ := (mul_le_mul_of_nonneg_right (le_max_left Ki Ka) hδ₀).trans hδτ
  have ha : Ka * δ₀ ≤ τ := (mul_le_mul_of_nonneg_right (le_max_right Ki Ka) hδ₀).trans hδτ
  exact ⟨FNet_iso D δA τ δ₀ C θ μ A hseq hτ hδτ' Z hZ φ hφ (max Ki Ka) Ki hK1 (le_max_left _ _)
      (hKi D δA τ δ₀ C θ μ A hseq hτ hδ₀ hi Z hZ φ hφ hLL) CR hCR,
    FNet_avg D δA τ δ₀ C θ μ A hseq hτ hδτ' Z hZ φ hφ (max Ki Ka) Ka hK1 (le_max_right _ _)
      (hKa D δA τ δ₀ C θ μ A hseq hτ hδ₀ ha Z hZ φ hφ hLL) CR hCR⟩


end RBMTransitionEdge

end
