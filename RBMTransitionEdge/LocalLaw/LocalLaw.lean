module

public import RBMTransitionEdge.LocalLaw.Bootstrap
public import RBMTransitionEdge.LocalLaw.Uniform
public import RBMTransitionEdge.LocalLaw.FarDet

@[expose] public section

/-!
# The local laws

Lemma 2.9 [lem_loc] for the class: along one sequence of members by the levels of the continuity
argument, then uniformly over the class: the block traces, (2.22) [eq:aniso_local] and (2.23)
[eq:aver_local] on `𝐃(τ)` of Definition 3.1 [def_wtM], for all `z` at once.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge


/-! ### Norms, traces and the deterministic equation -/

/-- The operator norm is nonnegative. -/
private lemma LL_opNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    0 ≤ opNorm X := norm_nonneg _

/-- The operator norm of a difference. -/
private lemma LL_opNorm_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Matrix ι ι ℂ) :
    opNorm (X - Y) ≤ opNorm X + opNorm Y := by
  unfold opNorm
  rw [map_sub]
  exact norm_sub_le _ _

/-- The operator norm of a product of matrices with bounded norms. -/
private lemma LL_opNorm_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ}
    {x y : ℝ} (hX : opNorm X ≤ x) (hY : opNorm Y ≤ y) : opNorm (X * Y) ≤ x * y :=
  (opNorm_mul_le X Y).trans
    (mul_le_mul hX hY (LL_opNorm_nonneg Y) ((LL_opNorm_nonneg X).trans hX))

/-- The normalized trace is subtractive. -/
private lemma LL_ntr_sub {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P - Q) = ntr P - ntr Q := by
  simp [ntr, Matrix.trace_sub, mul_sub]

/-- The normalized trace is cyclic. -/
private lemma LL_ntr_comm {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P * Q) = ntr (Q * P) := by
  simp [ntr, Matrix.trace_mul_comm P Q]

/-- `|⟨X⟩| ≤ ‖X‖`. -/
private lemma LL_ntr_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    ‖ntr X‖ ≤ opNorm X := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp [ntr, Matrix.trace, LL_opNorm_nonneg]
  · have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    unfold ntr Matrix.trace
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, X.diag i‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, opNorm X := by
          gcongr
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun i _ => norm_apply_le_opNorm X i i)
      _ = opNorm X := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp

/-- `|x^* T y| ≤ ‖T‖` for `|x|, |y| ≤ 1`. -/
private lemma LL_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
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

/-- The block traces are subtractive. -/
private lemma LL_blockTr_sub (D N : ℕ) (X Y : Matrix (Idx D N) (Idx D N) ℂ) :
    blockTr D N (X - Y) = blockTr D N X - blockTr D N Y := by
  funext a
  simp only [blockTr, Pi.sub_apply, LL_ntr_sub, mul_sub]

/-- `‖E_a‖ ≤ 1`. -/
private lemma LL_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- `D⟨E_a M⟩ = m` for every block (`D, N ≥ 1`, `z ∉ ℝ`): the block traces of (2.17) [def_G0]
are the solution of (2.16) [self_m]. -/
private lemma LL_blockTr_M (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : z.im ≠ 0) :
    blockTr D N (MExt (lam D N A) z) = fun _ => mExt (lam D N A) z := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  funext a
  simp only [blockTr]
  rw [LL_ntr_comm]
  obtain ⟨hm, -, -⟩ := MExt_spec (lam D N A) (lam_isHermitian D N A) z hz
  by_cases h2 : 2 ≤ D
  · exact (def_M_scalar D h2 N hN A z hz).1 a
  · obtain rfl : D = 1 := by omega
    have hE : Ea 1 N a = 1 := by
      ext p q
      have : p.1 = a := Subsingleton.elim _ _
      simp [Ea, Matrix.diagonal_apply, Matrix.one_apply, this]
    rw [hE, Matrix.mul_one, ← hm]
    simp

/-- `m = mSol`, `M = MSol` on the upper half plane. -/
private lemma LL_MExt_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ)
    (hz : 0 < z.im) : mExt Λ z = mSol Λ z ∧ MExt Λ z = MSol Λ z := by
  have he1 : mExt Λ z = mSol Λ z := by simp [mExt, hz]
  exact ⟨he1, by simp [MExt, MSol, he1]⟩

/-- `‖M‖ ≤ 5/4` and `|m| < 1` for `‖Λ‖ ≤ 1/10`, `Im z > 0` (from (A.19) [taylor_expansion_M]). -/
private lemma LL_M_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) :
    opNorm (MExt Λ z) ≤ 5 / 4 ∧ ‖mExt Λ z‖ < 1 := by
  obtain ⟨e1, e2⟩ := LL_MExt_eq Λ z hz
  obtain ⟨-, hm, hM⟩ := mSol_apriori Λ hΛ hℓ z hz
  refine ⟨?_, by rw [e1]; exact hm⟩
  rw [e2]
  refine hM.le.trans ?_
  have h0 := LL_opNorm_nonneg Λ
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- For Hermitian `Λ` and `Im z > 0`: `Im m > 0` and `‖M‖ ≤ (Im z)⁻¹`. -/
private lemma LL_M_inv {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    0 < (mExt Λ z).im ∧ opNorm (MExt Λ z) ≤ z.im⁻¹ := by
  obtain ⟨-, -, hmim⟩ := MExt_spec Λ hΛ z hz.ne'
  have hm0 : 0 < (mExt Λ z).im := by
    by_contra hneg
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hz.le
    linarith
  have hzm : 0 < (z + mExt Λ z).im := by
    simp only [Complex.add_im]
    linarith
  refine ⟨hm0, ?_⟩
  have := opNorm_res_le Λ hΛ (z + mExt Λ z) hzm
  refine (le_of_eq rfl).trans (this.trans ?_)
  refine inv_anti₀ hz ?_
  simp only [Complex.add_im]
  linarith

/-- For a Hermitian array and `Im z > 0`: `‖G - M‖ ≤ 2 (Im z)⁻¹`. -/
private lemma LL_GM_le (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) [Nonempty (Idx D N)] (z : ℂ)
    (hz : 0 < z.im) :
    opNorm (res (H + lam D N A) z - MExt (lam D N A) z) ≤ 2 * z.im⁻¹ := by
  have hΛh := lam_isHermitian D N A
  have hG := opNorm_res_le _ (hH.add hΛh) z hz
  have hM := (LL_M_inv _ hΛh z hz).2
  refine (LL_opNorm_sub_le _ _).trans ?_
  linarith

/-- The decomposition `G - M = (R_x̃ - M) - R_x̃ H̲G`: for Hermitian `H`, `Im z > 0`,
`‖Λ‖ ≤ 1/10` and `|x|_∞ ≤ 2/5` for `x = blockTr(G - M)`, the matrix `R_x̃`,
`x̃ = σ_θ blockTr G`, satisfies `‖R_x̃‖ ≤ 5/2` and `‖R_x̃ - M‖ ≤ (25/8) |x|_∞`. -/
private lemma LL_decomp (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 10)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (hx : ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 2 / 5) :
    opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z))) ≤ 5 / 2 ∧
      opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) -
        MExt (lam D N A) z) ≤
          25 / 8 * ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ∧
      res (H + lam D N A) z - MExt (lam D N A) z =
        (resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) -
          MExt (lam D N A) z) -
          resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) *
            hgUnder D N θ H (lam D N A) z := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  set Λ := lam D N A with hΛdef
  set G := res (H + Λ) z with hGdef
  set M := MExt Λ z with hMdef
  set m := mExt Λ z with hmdef
  set x := blockTr D N (G - M) with hxdef
  have hbM : blockTr D N M = fun _ => m := LL_blockTr_M D N hD hN A z hz.ne'
  have hbG : blockTr D N G = fun a => m + x a := by
    funext a
    have := congrFun (LL_blockTr_sub D N G M) a
    rw [← hxdef, hbM] at this
    simp only [Pi.sub_apply] at this
    rw [this]
    ring
  have hMn : opNorm M ≤ 5 / 4 := (LL_M_le Λ hΛ hℓ z hz).1
  obtain ⟨hR, hRM, -⟩ := resX_taylor D N hD hN θ hθ0 hθ1 A z hz hMn x hx
  rw [hbG]
  set R := resX Λ z (sigTheta D θ *ᵥ fun a => m + x a) with hRdef
  have hRn : opNorm R ≤ 5 / 2 := by
    have e : R = (R - M) + M := by abel
    rw [e]
    refine (opNorm_add_le _ _).trans ?_
    nlinarith [norm_nonneg x]
  have hG : G = R - R * hgUnder D N θ H Λ z := by
    have := res_eq_resX_sub D N θ A H hH z hz (by rw [hbG]; exact hR)
    rw [hbG] at this
    exact this
  refine ⟨hRn, hRM, ?_⟩
  conv_lhs => rw [hG]
  abel

/-- The isotropic entries from the block traces (deterministic): if `|x|_∞ ≤ X`, `|x|_∞ ≤ 1/5`
and `1(‖R_x̃‖ ≤ 5/2) |u^* R_x̃ H̲G v| ≤ Y` for unit `u, v`, then `|u^* (G - M) v| ≤ (25/8) X + Y`. -/
private lemma LL_iso_det (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 10)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (s t : Idx D N → ℂ) (hs : ∑ i, ‖s i‖ ^ 2 = 1) (ht : ∑ i, ‖t i‖ ^ 2 = 1) (X Y : ℝ)
    (hx : ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ X)
    (hx5 : ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 1 / 5)
    (hY : (if opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ
          blockTr D N (res (H + lam D N A) z))) ≤ 5 / 2 then
        ‖star s ⬝ᵥ ((resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) *
          hgUnder D N θ H (lam D N A) z) *ᵥ t)‖ else 0) ≤ Y) :
    ‖star s ⬝ᵥ ((res (H + lam D N A) z - MExt (lam D N A) z) *ᵥ t)‖ ≤ 25 / 8 * X + Y := by
  obtain ⟨hR, hRM, hdec⟩ := LL_decomp D N hD hN θ hθ0 hθ1 A hℓ H hH z hz (by linarith)
  simp only [hR, ↓reduceIte] at hY
  rw [hdec, Matrix.sub_mulVec, dotProduct_sub]
  refine (norm_sub_le _ _).trans ?_
  have h1 := LL_form_le (resX (lam D N A) z (sigTheta D θ *ᵥ
    blockTr D N (res (H + lam D N A) z)) - MExt (lam D N A) z) s t hs.le ht.le
  have h2 : 25 / 8 * ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 25 / 8 * X :=
    mul_le_mul_of_nonneg_left hx (by norm_num)
  linarith

/-- The averages from the block traces (deterministic): if `|x|_∞ ≤ X`, `|x|_∞ ≤ 1/5` and
`1(‖R_x̃‖ ≤ 5/2) |⟨B R_x̃ H̲G⟩| ≤ Y` for `‖B‖ ≤ 1`, then `|⟨(G - M) B⟩| ≤ (25/8) X + Y`. -/
private lemma LL_avg_det (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 10)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (B : Matrix (Idx D N) (Idx D N) ℂ) (hB : opNorm B ≤ 1) (X Y : ℝ)
    (hx : ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ X)
    (hx5 : ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 1 / 5)
    (hY : (if opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ
          blockTr D N (res (H + lam D N A) z))) ≤ 5 / 2 then
        ‖ntr (B * resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) *
          hgUnder D N θ H (lam D N A) z)‖ else 0) ≤ Y) :
    ‖ntr ((res (H + lam D N A) z - MExt (lam D N A) z) * B)‖ ≤ 25 / 8 * X + Y := by
  obtain ⟨hR, hRM, hdec⟩ := LL_decomp D N hD hN θ hθ0 hθ1 A hℓ H hH z hz (by linarith)
  simp only [hR, ↓reduceIte] at hY
  set R := resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z))
  set W := hgUnder D N θ H (lam D N A) z
  rw [hdec, Matrix.sub_mul, LL_ntr_sub]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖ntr ((R - MExt (lam D N A) z) * B)‖ ≤
      25 / 8 * ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ :=
    (LL_ntr_le _).trans ((LL_opNorm_mul_le hRM hB).trans (by rw [mul_one]))
  have h2 : ntr (R * W * B) = ntr (B * R * W) := by
    rw [LL_ntr_comm, Matrix.mul_assoc]
  have h3 : 25 / 8 * ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 25 / 8 * X :=
    mul_le_mul_of_nonneg_left hx (by norm_num)
  rw [h2]
  linarith

/-- `η ↦ Im m(E + iη)/η` does not increase on `η > 0`: by Definition 2.7 [defn_Mm] and (2.19)
[eq:density_rhoN], `Im m(E + iη)/η = ∫ ρ(x) ((x - E)² + η²)⁻¹ dx`. -/
private lemma LL_imm_anti {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (E η η' : ℝ)
    (hη : 0 < η) (hηη : η ≤ η') :
    (mSol Λ ((E : ℂ) + (η' : ℂ) * Complex.I)).im / η' ≤
      (mSol Λ ((E : ℂ) + (η : ℂ) * Complex.I)).im / η := by
  obtain ⟨hρ0, hρc, hρi, -, hrep⟩ := rho_stieltjes Λ hΛ hℓ
  have hden : ∀ t : ℝ, 0 < t → ∀ x : ℝ, t ^ 2 ≤ (x - E) ^ 2 + t ^ 2 := fun t _ x => by
    nlinarith [sq_nonneg (x - E)]
  have hint2 : ∀ t : ℝ, 0 < t → Integrable (fun x : ℝ => rho Λ x / ((x - E) ^ 2 + t ^ 2)) := by
    intro t ht
    refine Integrable.mono' (hρi.div_const (t ^ 2)) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · refine Continuous.aestronglyMeasurable (hρc.div (by fun_prop) fun x => ?_)
      have := hden t ht x
      positivity
    · have h1 := hden t ht x
      have ht2 : 0 < t ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hρ0 x) (by positivity))]
      exact div_le_div_of_nonneg_left (hρ0 x) ht2 h1
  have key : ∀ t : ℝ, 0 < t → (mSol Λ ((E : ℂ) + (t : ℂ) * Complex.I)).im / t =
      ∫ x, rho Λ x / ((x - E) ^ 2 + t ^ 2) := by
    intro t ht
    have hz : 0 < ((E : ℂ) + (t : ℂ) * Complex.I).im := by simpa using ht
    rw [hrep _ hz]
    have hpt : ∀ x : ℝ, (x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro x h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hint : Integrable
        (fun x : ℝ => (rho Λ x : ℂ) / ((x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I))) := by
      refine Integrable.mono' (hρi.div_const t) ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (Continuous.div (Complex.continuous_ofReal.comp hρc) (by fun_prop)
          hpt).aestronglyMeasurable
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]
        have h1 : t ≤ ‖(x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I)‖ := by
          have him' : ((x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I)).im = -t := by simp
          have := Complex.abs_im_le_norm ((x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I))
          rwa [him', abs_neg, abs_of_pos ht] at this
        exact div_le_div_of_nonneg_left (hρ0 x) ht h1
    have him := integral_im hint
    simp only [RCLike.im_to_complex] at him
    rw [← him, ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hd : 0 < (x - E) ^ 2 + t ^ 2 := by positivity
    have hre : ((x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I)).re = x - E := by simp
    have him' : ((x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I)).im = -t := by simp
    have hns : Complex.normSq ((x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I)) =
        (x - E) ^ 2 + t ^ 2 := by
      rw [Complex.normSq_apply, hre, him']; ring
    simp only
    rw [Complex.div_im, hns, hre, him']
    simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul, zero_div, zero_sub]
    field_simp
  rw [key η' (lt_of_lt_of_le hη hηη), key η hη]
  refine integral_mono (hint2 η' (lt_of_lt_of_le hη hηη)) (hint2 η hη) fun x => ?_
  have h1 : (x - E) ^ 2 + η ^ 2 ≤ (x - E) ^ 2 + η' ^ 2 := by nlinarith
  have h2 : 0 < (x - E) ^ 2 + η ^ 2 := by positivity
  exact div_le_div_of_nonneg_left (hρ0 x) h2 h1

/-! ### Powers of `N` -/

/-- `N^{-δ} ≤ c` for large `N`. -/
private lemma LL_rpow_small {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) ^ (-δ) ≤ c := by
  have h := ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually
    (ge_mem_nhds hc)
  exact Filter.eventually_atTop.mp h

/-- `C ≤ N^ε` for large `N`. -/
private lemma LL_rpow_large {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C ≤ (N : ℝ) ^ ε := by
  have h := ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop C)
  exact Filter.eventually_atTop.mp h

/-- `C N^a ≤ N^b` for large `N` when `a < b`. -/
private lemma LL_rpow_absorb {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  obtain ⟨N₁, hN₁⟩ := LL_rpow_large (sub_pos.mpr hab) C
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hN0 : (0 : ℝ) < N := by linarith
  have e : (N : ℝ) ^ b = (N : ℝ) ^ (b - a) * (N : ℝ) ^ a := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right (hN₁ N (le_of_max_le_left hN)) (Real.rpow_nonneg hN0.le _)

/-- `x^a ≤ x^b` for `1 ≤ x`, `a ≤ b`. -/
private lemma LL_rpow_mono {x a b : ℝ} (hx : 1 ≤ x) (hab : a ≤ b) : x ^ a ≤ x ^ b :=
  Real.rpow_le_rpow_of_exponent_le hx hab

/-- Two sets of measure `≤ N^{-(D'+1)}` have total measure `≤ N^{-D'}` once `N ≥ 2`. -/
private lemma LL_two_le (N : ℕ) (hN : 2 ≤ N) (D' : ℝ) :
    ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [← ENNReal.ofReal_add (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : (N : ℝ) ^ (-(D' + 1)) = (N : ℝ) ^ (-D') * (N : ℝ)⁻¹ := by
    rw [show -(D' + 1) = -D' + -(1 : ℝ) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
  rw [e]
  have hp : 0 < (N : ℝ) ^ (-D') := Real.rpow_pos_of_pos hN0 _
  have : (N : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hN0 (by norm_num)]; linarith
  nlinarith

/-- `k` sets of measure `≤ N^{-(D'+1)}` have total measure `≤ N^{-D'}` once `k ≤ N`. -/
private lemma LL_k_le (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) (D' : ℝ) :
    (k : ENNReal) * ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : (N : ℝ) ^ (-(D' + 1)) = (N : ℝ) ^ (-D') * (N : ℝ)⁻¹ := by
    rw [show -(D' + 1) = -D' + -(1 : ℝ) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
  rw [e]
  have hp : 0 < (N : ℝ) ^ (-D') := Real.rpow_pos_of_pos hN0 _
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  have : (k : ℝ) * (N : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN0]; exact hk'
  calc (k : ℝ) * ((N : ℝ) ^ (-D') * (N : ℝ)⁻¹) = (N : ℝ) ^ (-D') * ((k : ℝ) * (N : ℝ)⁻¹) := by
        ring
    _ ≤ (N : ℝ) ^ (-D') * 1 := mul_le_mul_of_nonneg_left this hp.le
    _ = _ := mul_one _

/-- `Nat.log 2 N + 2 ≤ N^ε / (ε log 2) + 2` for `N ≥ 1`: the dyadic count is below every power. -/
private lemma LL_log_le (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) (hε : 0 < ε) :
    ((Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) ^ ε / (ε * Real.log 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : ((2 : ℝ) ^ Nat.log 2 N) ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h2 : ((Nat.log 2 N : ℕ) : ℝ) * Real.log 2 ≤ Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h1
  have h3 : Real.log N ≤ (N : ℝ) ^ ε / ε := Real.log_le_rpow_div hN0.le hε
  rw [le_div_iff₀ (by positivity)]
  calc ((Nat.log 2 N : ℕ) : ℝ) * (ε * Real.log 2) = ε * (((Nat.log 2 N : ℕ) : ℝ) * Real.log 2) := by
        ring
    _ ≤ ε * ((N : ℝ) ^ ε / ε) := mul_le_mul_of_nonneg_left (h2.trans h3) hε.le
    _ = (N : ℝ) ^ ε := by field_simp

/-- `(Nat.log 2 N + 2) ≤ N^ε` for large `N`. -/
private lemma LL_log_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ((Nat.log 2 N : ℕ) : ℝ) + 2 ≤ (N : ℝ) ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N₁, hN₁⟩ := LL_rpow_absorb (show ε / 2 < ε by linarith) (2 / ((ε / 2) * Real.log 2))
  obtain ⟨N₂, hN₂⟩ := LL_rpow_absorb (show (0 : ℝ) < ε by linarith) 4
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have h1 := LL_log_le N hN1 (ε / 2) (by linarith)
  have h2 := hN₁ N (le_trans (by simp) hN)
  have h3 := hN₂ N (le_trans (by simp) hN)
  rw [Real.rpow_zero, mul_one] at h3
  have e : (N : ℝ) ^ (ε / 2) / (ε / 2 * Real.log 2) =
      1 / 2 * (2 / (ε / 2 * Real.log 2) * (N : ℝ) ^ (ε / 2)) := by
    field_simp
  rw [e] at h1
  linarith

/-! ### Sup-form domination over a spectral set -/

/-- Pairs of deterministic unit vectors. -/
private abbrev LL_UV (D N : ℕ) :=
  {s : Idx D N → ℂ // ∑ i, ‖s i‖ ^ 2 = 1} × {t : Idx D N → ℂ // ∑ i, ‖t i‖ ^ 2 = 1}

/-- Deterministic matrices of norm at most one. -/
private abbrev LL_Bs (D N : ℕ) := {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1}

/-- Definition 2.8 [stoch_domination] in sup form over `z ∈ Z_N` and a deterministic parameter
`w ∈ W_N`: `sup P(ξ > N^{τ'} ζ) ≤ N^{-D'}` for `N ≥ N₀(τ', D')`. -/
private def LL_Sup {D : ℕ} (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) {W : ℕ → Type}
    (Z : ℕ → Set ℂ) (ξ : ∀ N, ℂ → W N → (Idx D N → Idx D N → ℂ) → ℝ) (ζ : ℕ → ℂ → ℝ) :
    Prop :=
  ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z ∈ Z N, ∀ w : W N,
    μ N {h | (N : ℝ) ^ τ' * ζ N z < ξ N z w h} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D'))

/-- The block traces `|blockTr(G - M)|_∞`. -/
private def LL_xb (D : ℕ) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (N : ℕ) (z : ℂ) (_ : Unit)
    (h : Idx D N → Idx D N → ℂ) : ℝ :=
  ‖blockTr D N (res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z)‖

/-- The isotropic entries `|s^*(G - M)t|`. -/
private def LL_xi (D : ℕ) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (N : ℕ) (z : ℂ) (w : LL_UV D N)
    (h : Idx D N → Idx D N → ℂ) : ℝ :=
  ‖star w.1.1 ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ w.2.1)‖

/-- The averages `|⟨(G - M) B⟩|`. -/
private def LL_xa (D : ℕ) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (N : ℕ) (z : ℂ) (w : LL_Bs D N)
    (h : Idx D N → Idx D N → ℂ) : ℝ :=
  ‖ntr ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) * w.1)‖

section SupCalc

variable {D : ℕ} {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)} {W : ℕ → Type}
  {Z Z' : ℕ → Set ℂ} {ξ : ∀ N, ℂ → W N → (Idx D N → Idx D N → ℂ) → ℝ} {ζ ζ' : ℕ → ℂ → ℝ}

/-- A larger control. -/
private lemma LL_Sup_le (h : LL_Sup μ Z ξ ζ)
    (hle : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ z ∈ Z N, ζ N z ≤ ζ' N z) : LL_Sup μ Z ξ ζ' := by
  intro τ' hτ' D' hD'
  obtain ⟨N₀, hN₀⟩ := h τ' hτ' D' hD'
  obtain ⟨N₁, hN₁⟩ := hle
  refine ⟨max N₀ N₁, fun N hN z hz w =>
    le_trans (measure_mono ?_) (hN₀ N (le_of_max_le_left hN) z hz w)⟩
  intro x hx
  have h1 := hN₁ N (le_of_max_le_right hN) z hz
  have h0 : 0 ≤ (N : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  simp only [Set.mem_ofPred_eq] at hx ⊢
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 h0) hx

/-- A control that is, for every `ε > 0`, at least `N^{-ε}` times a dominating control. -/
private lemma LL_Sup_fam
    (h : ∀ ε : ℝ, 0 < ε → ∃ ζ₀ : ℕ → ℂ → ℝ, LL_Sup μ Z ξ ζ₀ ∧
      ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ z ∈ Z N, ζ₀ N z ≤ (N : ℝ) ^ ε * ζ N z) :
    LL_Sup μ Z ξ ζ := by
  intro τ' hτ' D' hD'
  obtain ⟨ζ₀, h0, N₁, hN₁⟩ := h (τ' / 2) (by linarith)
  obtain ⟨N₀, hN₀⟩ := h0 (τ' / 2) (by linarith) D' hD'
  refine ⟨max (max N₀ N₁) 1, fun N hN z hz w =>
    le_trans (measure_mono ?_) (hN₀ N (le_trans (by simp) hN) z hz w)⟩
  intro x hx
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hN0 : (0 : ℝ) < N := by linarith
  have h1 := hN₁ N (le_trans (by simp) hN) z hz
  have h2 : (N : ℝ) ^ (τ' / 2) * ζ₀ N z ≤ (N : ℝ) ^ τ' * ζ N z := by
    have e : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
      rw [← Real.rpow_add hN0]; ring_nf
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hN0.le _)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  exact lt_of_le_of_lt h2 hx

/-- A smaller spectral set. -/
private lemma LL_Sup_sub (h : LL_Sup μ Z ξ ζ) (hZ : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → Z' N ⊆ Z N) :
    LL_Sup μ Z' ξ ζ := by
  intro τ' hτ' D' hD'
  obtain ⟨N₀, hN₀⟩ := h τ' hτ' D' hD'
  obtain ⟨N₁, hN₁⟩ := hZ
  exact ⟨max N₀ N₁, fun N hN z hz w =>
    hN₀ N (le_of_max_le_left hN) z (hN₁ N (le_of_max_le_right hN) hz) w⟩

/-- The union of two spectral sets. -/
private lemma LL_Sup_union (h1 : LL_Sup μ Z ξ ζ) (h2 : LL_Sup μ Z' ξ ζ) :
    LL_Sup μ (fun N => Z N ∪ Z' N) ξ ζ := by
  intro τ' hτ' D' hD'
  obtain ⟨N₁, hN₁⟩ := h1 τ' hτ' D' hD'
  obtain ⟨N₂, hN₂⟩ := h2 τ' hτ' D' hD'
  refine ⟨max N₁ N₂, fun N hN z hz w => ?_⟩
  rcases hz with hz | hz
  · exact hN₁ N (le_of_max_le_left hN) z hz w
  · exact hN₂ N (le_of_max_le_right hN) z hz w

end SupCalc

/-- The a priori bound `aprioriLL` in the form `LL_Sup`. -/
private lemma LL_of_apriori {D : ℕ} {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)}
    {A : ∀ N, Matrix (Fin N) (Fin N) ℂ} {Z : ℕ → Set ℂ} {φ : ℕ → ℂ → ℝ}
    (h : aprioriLL D μ A Z φ) : LL_Sup μ Z (LL_xi D A) φ := by
  intro τ' hτ' D' hD'
  obtain ⟨N₀, hN₀⟩ := h τ' hτ' D' hD'
  exact ⟨N₀, fun N hN z hz w => hN₀ N hN (⟨z, hz⟩, w.1, w.2)⟩

/-- `LL_Sup` for the isotropic entries is the a priori bound `aprioriLL`. -/
private lemma LL_to_apriori {D : ℕ} {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)}
    {A : ∀ N, Matrix (Fin N) (Fin N) ℂ} {Z : ℕ → Set ℂ} {φ : ℕ → ℂ → ℝ}
    (h : LL_Sup μ Z (LL_xi D A) φ) : aprioriLL D μ A Z φ := by
  intro τ' hτ' D' hD'
  obtain ⟨N₀, hN₀⟩ := h τ' hτ' D' hD'
  exact ⟨N₀, fun N hN w => hN₀ N hN w.1.1 w.1.2 (w.2.1, w.2.2)⟩

/-- The block-trace output of `bootstrap_stage` in the form `LL_Sup`. -/
private lemma LL_of_block {D : ℕ} {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)}
    {A : ∀ N, Matrix (Fin N) (Fin N) ℂ} {Z : ℕ → Set ℂ} {ζ : ℕ → ℂ → ℝ}
    (h : PrecS μ (U := fun N => {z // z ∈ Z N})
      (fun N w h => ‖blockTr D N (res (Matrix.of h + lam D N (A N)) w.1 -
        MExt (lam D N (A N)) w.1)‖) (fun N w _ => ζ N w.1)) :
    LL_Sup μ Z (LL_xb D A) ζ := by
  intro τ' hτ' D' hD'
  obtain ⟨N₀, hN₀⟩ := h τ' hτ' D' hD'
  exact ⟨N₀, fun N hN z hz _ => hN₀ N hN ⟨z, hz⟩⟩

/-- The averaged output of `bootstrap_stage` in the form `LL_Sup`. -/
private lemma LL_of_avg {D : ℕ} {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)}
    {A : ∀ N, Matrix (Fin N) (Fin N) ℂ} {Z : ℕ → Set ℂ} {ζ : ℕ → ℂ → ℝ}
    (h : PrecS μ (U := fun N => {z // z ∈ Z N} ×
        {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1})
      (fun N w h => ‖ntr ((res (Matrix.of h + lam D N (A N)) w.1.1 -
        MExt (lam D N (A N)) w.1.1) * w.2.1)‖) (fun N w _ => ζ N w.1.1)) :
    LL_Sup μ Z (LL_xa D A) ζ := by
  intro τ' hτ' D' hD'
  obtain ⟨N₀, hN₀⟩ := h τ' hτ' D' hD'
  exact ⟨N₀, fun N hN z hz w => hN₀ N hN (⟨z, hz⟩, w)⟩

/-! ### The control parameters -/

/-- `Ψ_φ = √((Im m + φ) x) + x` with `x = (Nη)⁻¹`. -/
private lemma LL_psiPhi_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (N : ℕ)
    (z : ℂ) (φ : ℝ) :
    psiPhi Λ N z φ = Real.sqrt (((mExt Λ z).im + φ) * (1 / ((N : ℝ) * z.im))) +
      1 / ((N : ℝ) * z.im) := by
  unfold psiPhi
  rw [div_eq_mul_one_div ((mExt Λ z).im + φ)]

/-- `√(u + v) ≤ √u + √v`. -/
private lemma LL_sqrt_add_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u + v) ≤ Real.sqrt u + Real.sqrt v := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt hu
  have h2 := Real.sq_sqrt hv
  nlinarith [Real.sqrt_nonneg u, Real.sqrt_nonneg v]

/-- One step of the iteration (deterministic): for `0 ≤ m`, `0 ≤ φ ≤ 1`, `0 ≤ x`, `1 ≤ a` and
`φ ≤ a (√(m x) + x)`: `(1 + φ)³ (√((m + φ) x) + x) ≤ 8 (1 + √a) (√(m x) + x)`. -/
private lemma LL_step_det (m φ x a : ℝ) (hm : 0 ≤ m) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hx : 0 ≤ x)
    (ha : 1 ≤ a) (hφa : φ ≤ a * (Real.sqrt (m * x) + x)) :
    (1 + φ) ^ 3 * (Real.sqrt ((m + φ) * x) + x) ≤
      8 * (1 + Real.sqrt a) * (Real.sqrt (m * x) + x) := by
  set Ψ := Real.sqrt (m * x) + x with hΨ
  have hΨ0 : 0 ≤ Ψ := by positivity
  have hxΨ : x ≤ Ψ := by rw [hΨ]; linarith [Real.sqrt_nonneg (m * x)]
  have h1 : Real.sqrt ((m + φ) * x) ≤ Real.sqrt (m * x) + Real.sqrt (φ * x) := by
    rw [add_mul]; exact LL_sqrt_add_le (by positivity) (by positivity)
  have h2 : Real.sqrt (φ * x) ≤ Real.sqrt a * Ψ := by
    have : φ * x ≤ (a * Ψ) * Ψ := mul_le_mul hφa hxΨ hx (by positivity)
    calc Real.sqrt (φ * x) ≤ Real.sqrt ((a * Ψ) * Ψ) := Real.sqrt_le_sqrt this
      _ = Real.sqrt a * Ψ := by
        rw [show a * Ψ * Ψ = a * Ψ ^ 2 by ring, Real.sqrt_mul (by linarith),
          Real.sqrt_sq hΨ0]
  have h3 : (1 + φ) ^ 3 ≤ 8 := by
    have : 1 + φ ≤ 2 := by linarith
    calc (1 + φ) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) this 3
      _ = 8 := by norm_num
  have h4 : Real.sqrt ((m + φ) * x) + x ≤ (1 + Real.sqrt a) * Ψ := by
    rw [hΨ] at h2 ⊢; nlinarith
  have h5 : 0 ≤ Real.sqrt ((m + φ) * x) + x := by positivity
  calc (1 + φ) ^ 3 * (Real.sqrt ((m + φ) * x) + x) ≤ 8 * ((1 + Real.sqrt a) * Ψ) :=
        mul_le_mul h3 h4 h5 (by norm_num)
    _ = 8 * (1 + Real.sqrt a) * Ψ := by ring

/-- The iteration stays small (deterministic): for `m ≤ 1`, `0 ≤ φ ≤ 1`, `0 ≤ x ≤ 1`:
`(1 + φ)³ (√((m + φ) x) + x) ≤ 24 √x`. -/
private lemma LL_small_det (m φ x : ℝ) (hm1 : m ≤ 1) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + φ) ^ 3 * (Real.sqrt ((m + φ) * x) + x) ≤ 24 * Real.sqrt x := by
  have h3 : (1 + φ) ^ 3 ≤ 8 := by
    have : 1 + φ ≤ 2 := by linarith
    calc (1 + φ) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) this 3
      _ = 8 := by norm_num
  have h1 : Real.sqrt ((m + φ) * x) ≤ 2 * Real.sqrt x := by
    calc Real.sqrt ((m + φ) * x) ≤ Real.sqrt (4 * x) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * Real.sqrt x := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have h2 : x ≤ Real.sqrt x := by
    rw [Real.le_sqrt hx0 hx0]; nlinarith
  have h5 : 0 ≤ Real.sqrt ((m + φ) * x) + x := by positivity
  calc (1 + φ) ^ 3 * (Real.sqrt ((m + φ) * x) + x) ≤ 8 * (3 * Real.sqrt x) :=
        mul_le_mul h3 (by linarith) h5 (by norm_num)
    _ = 24 * Real.sqrt x := by ring

/-- The first step of a level (deterministic): for `m ≤ 1`, `1 ≤ φ`, `0 ≤ x ≤ 1`:
`(1 + φ)³ (√((m + φ) x) + x) ≤ 24 φ⁴ √x`. -/
private lemma LL_big_det (m φ x : ℝ) (hm1 : m ≤ 1) (hφ : 1 ≤ φ) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    (1 + φ) ^ 3 * (Real.sqrt ((m + φ) * x) + x) ≤ 24 * φ ^ 4 * Real.sqrt x := by
  have h3 : (1 + φ) ^ 3 ≤ 8 * φ ^ 3 := by
    have : 1 + φ ≤ 2 * φ := by linarith
    calc (1 + φ) ^ 3 ≤ (2 * φ) ^ 3 := pow_le_pow_left₀ (by linarith) this 3
      _ = 8 * φ ^ 3 := by ring
  have h1 : Real.sqrt ((m + φ) * x) ≤ 2 * φ * Real.sqrt x := by
    have hmφ : m + φ ≤ (2 * φ) ^ 2 := by nlinarith
    calc Real.sqrt ((m + φ) * x) ≤ Real.sqrt ((2 * φ) ^ 2 * x) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmφ hx0)
      _ = 2 * φ * Real.sqrt x := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]
  have h2 : x ≤ φ * Real.sqrt x := by
    have : x ≤ Real.sqrt x := by rw [Real.le_sqrt hx0 hx0]; nlinarith
    nlinarith [Real.sqrt_nonneg x]
  have h5 : 0 ≤ Real.sqrt ((m + φ) * x) + x := by positivity
  calc (1 + φ) ^ 3 * (Real.sqrt ((m + φ) * x) + x) ≤ (8 * φ ^ 3) * (3 * φ * Real.sqrt x) :=
        mul_le_mul h3 (by linarith) h5 (by positivity)
    _ = 24 * φ ^ 4 * Real.sqrt x := by ring

/-! ### The transfer between levels -/

/-- Along a sequence of members, `‖Λ_N‖ ≤ 1/10` for large `N`. -/
private lemma LL_lam_small {D : ℕ} {δA : ℝ} {C θ : ℕ → ℝ}
    {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)} {A : ∀ N, Matrix (Fin N) (Fin N) ℂ}
    (hs : LLSeq D δA C θ μ A) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → opNorm (lam D N (A N)) ≤ 1 / 10 := by
  obtain ⟨N₀, hN₀⟩ := LL_rpow_small hs.pos (show (0 : ℝ) < 1 / 20 by norm_num)
  refine ⟨N₀, fun N hN => (opNorm_lam_le D N (A N)).trans ?_⟩
  have := (hs.small N).trans (hN₀ N hN)
  linarith

/-- `Im(s^* G s) ≥ 0` for Hermitian `X` and `Im z > 0` (Ward identity). -/
private lemma LL_im_form_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (s : ι → ℂ) :
    0 ≤ (star s ⬝ᵥ (res X z *ᵥ s)).im := by
  have h := ward_vec X hX z hz s
  have h0 : 0 ≤ ∑ k, ‖(res X z *ᵥ s) k‖ ^ 2 := by positivity
  rw [h] at h0
  exact (div_nonneg_iff.mp h0).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hz)

set_option maxHeartbeats 1000000 in
/-- The transfer to a lower level (row R1): if `|s^*(G - M)t| ≺ 1` on `bootDom τ₁ ℓ` and
`N⁻¹ ≤ ℓ'_N`, `ℓ_N ≤ N^δ ℓ'_N`, then `|s^*(G - M)t| ≺ N^{2δ}` on `bootDom τ₁ ℓ'`, by
`res_transfer` at the dyadic points `E + i 2^j ℓ_N`. -/
private lemma LL_transfer (D : ℕ) (δA : ℝ) (C θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hs : LLSeq D δA C θ μ A) (τ₁ δ : ℝ) (hδ : 0 < δ) (ℓ ℓ' : ℕ → ℝ)
    (hℓ' : ∀ N : ℕ, 1 ≤ N → ((N : ℝ))⁻¹ ≤ ℓ' N)
    (hratio : ∀ N : ℕ, 1 ≤ N → ℓ N ≤ (N : ℝ) ^ δ * ℓ' N)
    (hP : aprioriLL D μ A (bootDom τ₁ ℓ) (fun _ _ => 1)) :
    aprioriLL D μ A (bootDom τ₁ ℓ') (fun N _ => (N : ℝ) ^ (2 * δ)) := by
  apply LL_to_apriori
  have hP' := LL_of_apriori hP
  intro τ' hτ' D' hD'
  obtain ⟨N₀, hN₀⟩ := hP' (τ' / 2) (by linarith) (D' + 1) (by linarith)
  obtain ⟨N₁, hN₁⟩ := LL_log_small (δ / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := LL_log_small (1 / 2) (by norm_num)
  obtain ⟨N₃, hN₃⟩ := LL_rpow_absorb (show (1 / 2 : ℝ) < 1 by norm_num) 2
  obtain ⟨N₄, hN₄⟩ := LL_rpow_absorb (show δ + δ / 2 + τ' / 2 < τ' + 2 * δ by linarith) 12
  obtain ⟨N₅, hN₅⟩ := LL_lam_small hs
  refine ⟨max (max (max N₀ N₁) (max N₂ N₃)) (max (max N₄ N₅) 1), fun N hN z hz w => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (by simp) hN
  have hN1 : N₁ ≤ N := le_trans (by simp) hN
  have hN2 : N₂ ≤ N := le_trans (by simp) hN
  have hN3 : N₃ ≤ N := le_trans (by simp) hN
  have hN4 : N₄ ≤ N := le_trans (by simp) hN
  have hN5 : N₅ ≤ N := le_trans (by simp) hN
  have hN1' : 1 ≤ N := le_trans (by simp) hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hNr0 : (0 : ℝ) < N := by linarith
  have hD1 := hs.one_le_D
  have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1'⟩)⟩
  have hΛh := lam_isHermitian D N (A N)
  have hΛ := hN₅ N hN5
  have hnull : μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := ae_iff.mp (hs.mem N).herm
  obtain ⟨⟨s, hs1⟩, ⟨t, ht1⟩⟩ := w
  have hcmp : (N : ℝ) ^ (τ' / 2) * 1 ≤ (N : ℝ) ^ τ' * (N : ℝ) ^ (2 * δ) := by
    rw [mul_one]
    calc (N : ℝ) ^ (τ' / 2) ≤ (N : ℝ) ^ τ' := LL_rpow_mono hNr1 (by linarith)
      _ = (N : ℝ) ^ τ' * 1 := (mul_one _).symm
      _ ≤ (N : ℝ) ^ τ' * (N : ℝ) ^ (2 * δ) :=
          mul_le_mul_of_nonneg_left (Real.one_le_rpow hNr1 (by linarith))
            (Real.rpow_nonneg hNr0.le _)
  have hDle : ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) :=
    ENNReal.ofReal_le_ofReal (LL_rpow_mono hNr1 (by linarith))
  by_cases hzl : ℓ N ≤ z.im
  · -- the point lies in the previous level
    have hz' : z ∈ bootDom τ₁ ℓ N := ⟨hz.1, hzl, hz.2.2⟩
    refine le_trans (measure_mono ?_) ((hN₀ N hN0 z hz' (⟨s, hs1⟩, ⟨t, ht1⟩)).trans hDle)
    intro h hh
    simp only [Set.mem_ofPred_eq] at hh ⊢
    exact lt_of_le_of_lt hcmp hh
  · push Not at hzl
    set E := z.re with hE
    set η' := z.im with hη'
    set b := ℓ N with hb
    set J := Nat.log 2 N + 1 with hJ
    have hη'0 : 0 < η' := lt_of_lt_of_le (by positivity) ((hℓ' N hN1').trans hz.2.1)
    have hb1 : 1 ≤ 2 ^ J * b := by
      have h1 : (N : ℝ) < 2 ^ J := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) N
      have h2 : ((N : ℝ))⁻¹ ≤ b := ((hℓ' N hN1').trans hz.2.1).trans hzl.le
      have h3 : (N : ℝ) * (N : ℝ)⁻¹ = 1 := by field_simp
      nlinarith [inv_pos.mpr hNr0]
    have hb0 : 0 < b := lt_trans hη'0 hzl
    have hratio' : b / η' ≤ (N : ℝ) ^ δ := by
      rw [div_le_iff₀ hη'0]
      exact (hratio N hN1').trans (mul_le_mul_of_nonneg_left hz.2.1 (Real.rpow_nonneg hNr0.le _))
    -- the dyadic points and the events at them
    set w : ℕ → ℂ := fun j => (E : ℂ) + ((2 ^ j * b : ℝ) : ℂ) * Complex.I with hw
    have hwre : ∀ j, (w j).re = E := fun j => by
      simp only [hw, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hwim : ∀ j, (w j).im = 2 ^ j * b := fun j => by
      simp only [hw, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hwpos : ∀ j, 0 < (w j).im := fun j => by rw [hwim]; positivity
    have hwdom : ∀ j, 2 ^ j * b ≤ 2 → w j ∈ bootDom τ₁ ℓ N := by
      intro j hj
      refine ⟨by rw [hwre]; exact hz.1, ?_, by rw [hwim]; exact hj⟩
      rw [hwim]
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    set Bs : ℕ → Set (Idx D N → Idx D N → ℂ) := fun j => if 2 ^ j * b ≤ 2 then
      {h | (N : ℝ) ^ (τ' / 2) * 1 < LL_xi D A N (w j) (⟨s, hs1⟩, ⟨s, hs1⟩) h} else ∅ with hBs
    set Bt : ℕ → Set (Idx D N → Idx D N → ℂ) := fun j => if 2 ^ j * b ≤ 2 then
      {h | (N : ℝ) ^ (τ' / 2) * 1 < LL_xi D A N (w j) (⟨t, ht1⟩, ⟨t, ht1⟩) h} else ∅ with hBt
    have hBsμ : ∀ j, μ N (Bs j) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := by
      intro j
      by_cases hj : 2 ^ j * b ≤ 2
      · simp only [hBs, hj, ↓reduceIte]
        exact hN₀ N hN0 (w j) (hwdom j hj) (⟨s, hs1⟩, ⟨s, hs1⟩)
      · simp [hBs, hj]
    have hBtμ : ∀ j, μ N (Bt j) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := by
      intro j
      by_cases hj : 2 ^ j * b ≤ 2
      · simp only [hBt, hj, ↓reduceIte]
        exact hN₀ N hN0 (w j) (hwdom j hj) (⟨t, ht1⟩, ⟨t, ht1⟩)
      · simp [hBt, hj]
    -- the deterministic bound outside the events
    set 𝒜 : ℝ := 1 + 4 * ((J : ℝ) + 1) * (5 / 4 + (N : ℝ) ^ (τ' / 2)) with h𝒜
    have hNτ0 : 0 ≤ (N : ℝ) ^ (τ' / 2) := Real.rpow_nonneg hNr0.le _
    have hA : ∀ (h : Idx D N → Idx D N → ℂ), (Matrix.of h).IsHermitian →
        ∀ (u : Idx D N → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1),
        (∀ j ∈ Finset.range (J + 1), 2 ^ j * b ≤ 2 →
          ¬ (N : ℝ) ^ (τ' / 2) * 1 < LL_xi D A N (w j) (⟨u, hu⟩, ⟨u, hu⟩) h) →
        1 ≤ 1 + 4 * ∑ j ∈ Finset.range (J + 1),
            (star u ⬝ᵥ (res (Matrix.of h + lam D N (A N)) ((E : ℂ) +
              ((2 ^ j * b : ℝ) : ℂ) * Complex.I) *ᵥ u)).im ∧
          1 + 4 * ∑ j ∈ Finset.range (J + 1),
            (star u ⬝ᵥ (res (Matrix.of h + lam D N (A N)) ((E : ℂ) +
              ((2 ^ j * b : ℝ) : ℂ) * Complex.I) *ᵥ u)).im ≤ 𝒜 := by
      intro h hH u hu hgood
      have hX := hH.add hΛh
      have hterm : ∀ j ∈ Finset.range (J + 1),
          (star u ⬝ᵥ (res (Matrix.of h + lam D N (A N)) ((E : ℂ) +
            ((2 ^ j * b : ℝ) : ℂ) * Complex.I) *ᵥ u)).im ≤ 5 / 4 + (N : ℝ) ^ (τ' / 2) := by
        intro j hj
        change (star u ⬝ᵥ (res (Matrix.of h + lam D N (A N)) (w j) *ᵥ u)).im ≤ _
        have hG := opNorm_res_le _ hX (w j) (hwpos j)
        refine (Complex.im_le_norm _).trans ?_
        by_cases hjb : 2 ^ j * b ≤ 2
        · have h1 := not_lt.mp (hgood j hj hjb)
          simp only [LL_xi, mul_one] at h1
          have hM := (LL_M_le _ hΛh hΛ (w j) (hwpos j)).1
          have h2 := LL_form_le (MExt (lam D N (A N)) (w j)) u u hu.le hu.le
          have e : star u ⬝ᵥ (res (Matrix.of h + lam D N (A N)) (w j) *ᵥ u) =
              star u ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) (w j) -
                MExt (lam D N (A N)) (w j)) *ᵥ u) +
              star u ⬝ᵥ (MExt (lam D N (A N)) (w j) *ᵥ u) := by
            rw [Matrix.sub_mulVec, dotProduct_sub]; ring
          rw [e]
          refine (norm_add_le _ _).trans ?_
          linarith
        · push Not at hjb
          have h2 := LL_form_le (res (Matrix.of h + lam D N (A N)) (w j)) u u hu.le hu.le
          have h3 : (w j).im⁻¹ ≤ 1 / 2 := by
            rw [hwim, inv_eq_one_div]
            exact one_div_le_one_div_of_le (by norm_num) hjb.le
          linarith
      have hnn : ∀ j ∈ Finset.range (J + 1), 0 ≤
          (star u ⬝ᵥ (res (Matrix.of h + lam D N (A N)) ((E : ℂ) +
            ((2 ^ j * b : ℝ) : ℂ) * Complex.I) *ᵥ u)).im :=
        fun j _ => LL_im_form_nonneg _ hX (w j) (hwpos j) u
      refine ⟨by linarith [Finset.sum_nonneg hnn], ?_⟩
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
      rw [Nat.cast_add, Nat.cast_one] at hsum
      rw [h𝒜]
      linarith
    have hsub : {h | (N : ℝ) ^ τ' * (N : ℝ) ^ (2 * δ) < LL_xi D A N z (⟨s, hs1⟩, ⟨t, ht1⟩) h} ⊆
        (⋃ j ∈ Finset.range (J + 1), (Bs j ∪ Bt j)) ∪
          {h | ¬ (Matrix.of h).IsHermitian} := by
      intro h hh
      by_contra hcon
      simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_ofPred_eq,
        not_not] at hcon
      obtain ⟨hcB, hH⟩ := hcon
      have hgs : ∀ j ∈ Finset.range (J + 1), 2 ^ j * b ≤ 2 →
          ¬ (N : ℝ) ^ (τ' / 2) * 1 < LL_xi D A N (w j) (⟨s, hs1⟩, ⟨s, hs1⟩) h := by
        intro j hj hjb hlt
        refine (hcB j hj).1 ?_
        simp only [hBs, hjb, ↓reduceIte, Set.mem_ofPred_eq]
        exact hlt
      have hgt : ∀ j ∈ Finset.range (J + 1), 2 ^ j * b ≤ 2 →
          ¬ (N : ℝ) ^ (τ' / 2) * 1 < LL_xi D A N (w j) (⟨t, ht1⟩, ⟨t, ht1⟩) h := by
        intro j hj hjb hlt
        refine (hcB j hj).2 ?_
        simp only [hBt, hjb, ↓reduceIte, Set.mem_ofPred_eq]
        exact hlt
      obtain ⟨hAs1, hAs⟩ := hA h hH s hs1 hgs
      obtain ⟨hAt1, hAt⟩ := hA h hH t ht1 hgt
      have hX := hH.add hΛh
      have htr := res_transfer (Matrix.of h + lam D N (A N)) hX s t hs1 ht1 E b η' hη'0 hzl.le J
        hb1
      have hzE : (E : ℂ) + (η' : ℂ) * Complex.I = z := Complex.re_add_im z
      rw [hzE] at htr
      have h𝒜0 : 0 ≤ 𝒜 := by linarith
      have hsq : Real.sqrt ((1 + 4 * ∑ j ∈ Finset.range (J + 1),
            (star s ⬝ᵥ (res (Matrix.of h + lam D N (A N)) ((E : ℂ) +
              ((2 ^ j * b : ℝ) : ℂ) * Complex.I) *ᵥ s)).im) *
          (1 + 4 * ∑ j ∈ Finset.range (J + 1),
            (star t ⬝ᵥ (res (Matrix.of h + lam D N (A N)) ((E : ℂ) +
              ((2 ^ j * b : ℝ) : ℂ) * Complex.I) *ᵥ t)).im)) ≤ 𝒜 := by
        calc _ ≤ Real.sqrt (𝒜 * 𝒜) := Real.sqrt_le_sqrt (mul_le_mul hAs hAt (by linarith) h𝒜0)
          _ = 𝒜 := Real.sqrt_mul_self h𝒜0
      have hG : ‖star s ⬝ᵥ (res (Matrix.of h + lam D N (A N)) z *ᵥ t)‖ ≤ (N : ℝ) ^ δ * 𝒜 :=
        htr.trans (mul_le_mul hratio' hsq (Real.sqrt_nonneg _) (Real.rpow_nonneg hNr0.le _))
      have hzpos : 0 < z.im := hη'0
      have hM := (LL_M_le _ hΛh hΛ z hzpos).1
      have hMf := LL_form_le (MExt (lam D N (A N)) z) s t hs1.le ht1.le
      have hfin : LL_xi D A N z (⟨s, hs1⟩, ⟨t, ht1⟩) h ≤ (N : ℝ) ^ δ * 𝒜 + 5 / 4 := by
        simp only [LL_xi]
        rw [Matrix.sub_mulVec, dotProduct_sub]
        refine (norm_sub_le _ _).trans ?_
        linarith
      -- the size of the bound
      have hJ1 : (J : ℝ) + 1 ≤ (N : ℝ) ^ (δ / 2) := by
        have := hN₁ N hN1
        rw [hJ]; push_cast; linarith
      have ha1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 2) := Real.one_le_rpow hNr1 (by linarith)
      have hc1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ' / 2) := Real.one_le_rpow hNr1 (by linarith)
      have hn1 : (1 : ℝ) ≤ (N : ℝ) ^ δ := Real.one_le_rpow hNr1 (by linarith)
      have h𝒜le : 𝒜 ≤ 10 * ((N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (τ' / 2)) := by
        rw [h𝒜]
        have h1 : 4 * ((J : ℝ) + 1) * (5 / 4 + (N : ℝ) ^ (τ' / 2)) ≤
            4 * (N : ℝ) ^ (δ / 2) * (5 / 4 + (N : ℝ) ^ (τ' / 2)) := by gcongr
        nlinarith
      have hexp : (N : ℝ) ^ (δ + δ / 2 + τ' / 2) =
          (N : ℝ) ^ δ * ((N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (τ' / 2)) := by
        rw [Real.rpow_add hNr0, Real.rpow_add hNr0]; ring
      have hexp2 : (N : ℝ) ^ (τ' + 2 * δ) = (N : ℝ) ^ τ' * (N : ℝ) ^ (2 * δ) := by
        rw [Real.rpow_add hNr0]
      have h4 := hN₄ N hN4
      rw [hexp, hexp2] at h4
      have hp1 : (1 : ℝ) ≤ (N : ℝ) ^ δ * ((N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (τ' / 2)) := by
        have := mul_le_mul ha1 hc1 zero_le_one (by linarith)
        nlinarith
      have h5 : (N : ℝ) ^ δ * 𝒜 ≤ 10 * ((N : ℝ) ^ δ * ((N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (τ' / 2))) := by
        have := mul_le_mul_of_nonneg_left h𝒜le (Real.rpow_nonneg hNr0.le δ)
        linarith
      simp only [Set.mem_ofPred_eq] at hh
      linarith
    -- the measure
    have hcard : 2 * (J + 1) ≤ N := by
      have h1 := hN₂ N hN2
      have h2 := hN₃ N hN3
      rw [Real.rpow_one] at h2
      have : (2 * (J + 1) : ℝ) ≤ N := by rw [hJ]; push_cast; linarith
      exact_mod_cast this
    calc μ N {h | (N : ℝ) ^ τ' * (N : ℝ) ^ (2 * δ) < LL_xi D A N z (⟨s, hs1⟩, ⟨t, ht1⟩) h}
        ≤ μ N ((⋃ j ∈ Finset.range (J + 1), (Bs j ∪ Bt j)) ∪
          {h | ¬ (Matrix.of h).IsHermitian}) := measure_mono hsub
      _ ≤ μ N (⋃ j ∈ Finset.range (J + 1), (Bs j ∪ Bt j)) +
          μ N {h | ¬ (Matrix.of h).IsHermitian} := measure_union_le _ _
      _ ≤ (∑ j ∈ Finset.range (J + 1), μ N (Bs j ∪ Bt j)) + 0 := by
          rw [hnull]; gcongr; exact measure_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ Finset.range (J + 1), 2 * ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := by
          rw [add_zero]
          refine Finset.sum_le_sum fun j _ => (measure_union_le _ _).trans ?_
          rw [two_mul]
          exact add_le_add (hBsμ j) (hBtμ j)
      _ = ((2 * (J + 1) : ℕ) : ENNReal) * ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := LL_k_le N _ hN1' hcard D'

/-! ### The levels of the continuity argument -/

/-- The statement of `bootstrap_stage` for a fixed constant `K`. -/
private def LL_BootStmt (K : ℝ) : Prop :=
  ∀ (D : ℕ) (δA τ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
      (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ),
      LLSeq D δA C θ μ A → 0 < τ → τ ≤ 1 / 4 →
    ∀ ℓ : ℕ → ℝ, (∀ N : ℕ, (N : ℝ) ^ (-1 + τ) ≤ ℓ N) →
    ∀ φ : ℕ → ℂ → ℝ,
      (∀ N, ∀ z ∈ bootDom τ ℓ N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ (τ / K)) →
      (∀ (N : ℕ) (E η η' : ℝ), ((E : ℂ) + (η : ℂ) * Complex.I) ∈ bootDom τ ℓ N → η ≤ η' →
        η' ≤ 2 → φ N ((E : ℂ) + (η' : ℂ) * Complex.I) ≤ φ N ((E : ℂ) + (η : ℂ) * Complex.I)) →
      aprioriLL D μ A (bootDom τ ℓ) φ →
    PrecS μ (U := fun N => {z // z ∈ bootDom τ ℓ N})
        (fun N w h => ‖blockTr D N (res (Matrix.of h + lam D N (A N)) w.1 -
          MExt (lam D N (A N)) w.1)‖)
        (fun N w _ => min ((1 + φ N w.1) ^ 6 * psiPhi (lam D N (A N)) N w.1 (φ N w.1) ^ 2 /
            Real.sqrt (kappa (lam D N (A N)) w.1.re + w.1.im))
          ((1 + φ N w.1) ^ 3 * psiPhi (lam D N (A N)) N w.1 (φ N w.1))) ∧
      aprioriLL D μ A (bootDom τ ℓ)
        (fun N z => (1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z)) ∧
      PrecS μ (U := fun N => {z // z ∈ bootDom τ ℓ N} ×
          {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1})
        (fun N w h => ‖ntr ((res (Matrix.of h + lam D N (A N)) w.1.1 -
          MExt (lam D N (A N)) w.1.1) * w.2.1)‖)
        (fun N w _ => (1 + φ N w.1.1) ^ 6 * psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1) ^ 2 +
          min ((1 + φ N w.1.1) ^ 6 * psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1) ^ 2 /
              Real.sqrt (kappa (lam D N (A N)) w.1.1.re + w.1.1.im))
            ((1 + φ N w.1.1) ^ 3 * psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1)))

/-- On a bootstrap domain with `ℓ_N ≥ N^{-1+τ₁}`, `N ≥ 1`: `η > 0`, `x = (Nη)⁻¹ ≤ N^{-τ₁}` and
`√x ≤ N^{-τ₁/2}`. -/
private lemma LL_x_le (N : ℕ) (hN : 1 ≤ N) (τ₁ η : ℝ) (hη : (N : ℝ) ^ (-1 + τ₁) ≤ η) :
    0 < η ∧ 1 / ((N : ℝ) * η) ≤ (N : ℝ) ^ (-τ₁) ∧
      Real.sqrt (1 / ((N : ℝ) * η)) ≤ (N : ℝ) ^ (-τ₁ / 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < (N : ℝ) ^ (-1 + τ₁) := Real.rpow_pos_of_pos hN0 _
  have hη0 : 0 < η := lt_of_lt_of_le hp hη
  have h1 : (N : ℝ) ^ τ₁ ≤ (N : ℝ) * η := by
    have e : (N : ℝ) ^ τ₁ = (N : ℝ) * (N : ℝ) ^ (-1 + τ₁) := by
      rw [show τ₁ = 1 + (-1 + τ₁) by ring, Real.rpow_add hN0, Real.rpow_one]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left hη hN0.le
  have h2 : 1 / ((N : ℝ) * η) ≤ (N : ℝ) ^ (-τ₁) := by
    rw [Real.rpow_neg hN0.le, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hN0 _) h1
  refine ⟨hη0, h2, ?_⟩
  calc Real.sqrt (1 / ((N : ℝ) * η)) ≤ Real.sqrt ((N : ℝ) ^ (-τ₁)) := Real.sqrt_le_sqrt h2
    _ = (N : ℝ) ^ (-τ₁ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; ring_nf

/-- `0 ≤ Im m < 1` for `‖Λ‖ ≤ 1/10`, `Im z > 0`. -/
private lemma LL_imm_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) :
    0 < (mExt Λ z).im ∧ (mExt Λ z).im ≤ 1 := by
  refine ⟨(LL_M_inv Λ hΛ z hz).1, ?_⟩
  have := (LL_M_le Λ hΛ hℓ z hz).2
  exact ((Complex.im_le_norm _).trans this.le)

/-- The a priori bound `|s^*(G - M)t| ≺ 1` on spectral sets in `{Im z ≥ 2}` (deterministic:
`‖G - M‖ ≤ 2/η ≤ 1` for Hermitian arrays). -/
private lemma LL_apriori_top {D : ℕ} {δA : ℝ} {C θ : ℕ → ℝ}
    {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)} {A : ∀ N, Matrix (Fin N) (Fin N) ℂ}
    (hs : LLSeq D δA C θ μ A) (Z : ℕ → Set ℂ) (hZ : ∀ N, ∀ z ∈ Z N, 2 ≤ z.im) :
    aprioriLL D μ A Z (fun _ _ => 1) := by
  apply LL_to_apriori
  intro τ' hτ' D' hD'
  refine ⟨1, fun N hN z hz w => ?_⟩
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : Nonempty (Idx D N) := ⟨(⟨0, hs.one_le_D⟩, ⟨0, hN⟩)⟩
  have hnull : μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := ae_iff.mp (hs.mem N).herm
  refine le_trans (measure_mono_null ?_ hnull).le bot_le
  intro h hh
  by_contra hnh
  have hH : (Matrix.of h).IsHermitian := not_not.mp hnh
  have h2 := hZ N z hz
  have hz0 : 0 < z.im := by linarith
  have hGM := LL_GM_le D N (A N) (Matrix.of h) hH z hz0
  have hf := LL_form_le (res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z)
    w.1.1 w.2.1 w.1.2.le w.2.2.le
  have h3 : 2 * z.im⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hz0]; exact h2
  have h4 : (1 : ℝ) ≤ (N : ℝ) ^ τ' := Real.one_le_rpow hNr1 hτ'.le
  simp only [Set.mem_ofPred_eq, LL_xi, mul_one] at hh
  linarith

/-- The cut-off of level `k`: `ℓ_k(N) = max(2N^{-kδ}, N^{-1+τ₁})`. -/
private def LL_lev (τ₁ δ : ℝ) (k : ℕ) (N : ℕ) : ℝ :=
  max (2 * (N : ℝ) ^ (-((k : ℝ) * δ))) ((N : ℝ) ^ (-1 + τ₁))

/-- `ℓ_k ≤ N^δ ℓ_{k+1}` for `N ≥ 1`, `δ ≥ 0`. -/
private lemma LL_lev_ratio (τ₁ δ : ℝ) (hδ : 0 ≤ δ) (k N : ℕ) (hN : 1 ≤ N) :
    LL_lev τ₁ δ k N ≤ (N : ℝ) ^ δ * LL_lev τ₁ δ (k + 1) N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : 0 ≤ (N : ℝ) ^ δ := Real.rpow_nonneg hN0.le _
  unfold LL_lev
  refine max_le ?_ ?_
  · have e : 2 * (N : ℝ) ^ (-((k : ℝ) * δ)) =
        (N : ℝ) ^ δ * (2 * (N : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * δ))) := by
      rw [mul_left_comm, ← Real.rpow_add hN0]
      push_cast; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hd
  · calc (N : ℝ) ^ (-1 + τ₁) = 1 * (N : ℝ) ^ (-1 + τ₁) := (one_mul _).symm
      _ ≤ (N : ℝ) ^ δ * (N : ℝ) ^ (-1 + τ₁) :=
        mul_le_mul_of_nonneg_right (Real.one_le_rpow hN1 hδ) (Real.rpow_nonneg hN0.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hd

/-- One level of the continuity argument: from `|s^*(G - M)t| ≺ 1` on `bootDom τ₁ ℓ` to the same
on `bootDom τ₁ ℓ'`, for `ℓ_N ≤ N^δ ℓ'_N`, `δ = τ₁/(4K)`: the transfer gives the a priori bound
`N^{2δ} ≤ N^{τ₁/K}`, and one step of the bootstrap gives `(1 + φ)³ Ψ_φ ≤ 24 N^{-τ₁/4}`. -/
private lemma LL_level (K : ℝ) (hK : 8 ≤ K) (hboot : LL_BootStmt K) (D : ℕ) (δA : ℝ)
    (C θ : ℕ → ℝ) (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ))
    (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (hs : LLSeq D δA C θ μ A) (τ₁ : ℝ) (hτ₁ : 0 < τ₁)
    (hτ₁4 : τ₁ ≤ 1 / 4) (ℓ ℓ' : ℕ → ℝ) (hℓ' : ∀ N : ℕ, (N : ℝ) ^ (-1 + τ₁) ≤ ℓ' N)
    (hratio : ∀ N : ℕ, 1 ≤ N → ℓ N ≤ (N : ℝ) ^ (τ₁ / (4 * K)) * ℓ' N)
    (hP : aprioriLL D μ A (bootDom τ₁ ℓ) (fun _ _ => 1)) :
    aprioriLL D μ A (bootDom τ₁ ℓ') (fun _ _ => 1) := by
  have hK0 : 0 < K := by linarith
  set δ := τ₁ / (4 * K) with hδdef
  have hδ : 0 < δ := by positivity
  have hℓ'1 : ∀ N : ℕ, 1 ≤ N → ((N : ℝ))⁻¹ ≤ ℓ' N := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    refine le_trans ?_ (hℓ' N)
    rw [← Real.rpow_neg_one]
    exact LL_rpow_mono hN1 (by linarith)
  have hT := LL_transfer D δA C θ μ A hs τ₁ δ hδ ℓ ℓ' hℓ'1 hratio hP
  set φ : ℕ → ℂ → ℝ := fun N _ => (N : ℝ) ^ (2 * δ) with hφdef
  have h2δ : 2 * δ ≤ τ₁ / K := by
    rw [hδdef]; field_simp; nlinarith
  have hφ : ∀ N, ∀ z ∈ bootDom τ₁ ℓ' N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ (τ₁ / K) := by
    intro N z _
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [hφdef, Nat.cast_zero, _root_.inv_zero]
      rw [Real.zero_rpow (by positivity), Real.zero_rpow (by positivity)]
      exact ⟨le_rfl, le_rfl⟩
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      refine ⟨?_, LL_rpow_mono hN1 h2δ⟩
      exact (inv_le_one_of_one_le₀ hN1).trans (Real.one_le_rpow hN1 (by positivity))
  have hout := (hboot D δA τ₁ C θ μ A hs hτ₁ hτ₁4 ℓ' hℓ' φ hφ
    (fun _ _ _ _ _ _ _ => le_rfl) hT).2.1
  apply LL_to_apriori
  refine LL_Sup_le (LL_of_apriori hout) ?_
  obtain ⟨N₁, hN₁⟩ := LL_lam_small hs
  obtain ⟨N₂, hN₂⟩ := LL_rpow_absorb (show 8 * δ + -τ₁ / 2 < 0 by
    have : 8 * δ ≤ τ₁ / 4 := by rw [hδdef]; field_simp; nlinarith
    linarith) 24
  refine ⟨max (max N₁ N₂) 1, fun N hN z hz => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (by simp) hN
  have hN2 : N₂ ≤ N := le_trans (by simp) hN
  have hN1' : 1 ≤ N := le_trans (by simp) hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hNr0 : (0 : ℝ) < N := by linarith
  have : Nonempty (Idx D N) := ⟨(⟨0, hs.one_le_D⟩, ⟨0, hN1'⟩)⟩
  obtain ⟨hη0, hx, hsx⟩ := LL_x_le N hN1' τ₁ z.im ((hℓ' N).trans hz.2.1)
  obtain ⟨hm0, hm1⟩ := LL_imm_bounds _ (lam_isHermitian D N (A N)) (hN₁ N hN1) z hη0
  have hx1 : 1 / ((N : ℝ) * z.im) ≤ 1 :=
    hx.trans (Real.rpow_le_one_of_one_le_of_nonpos hNr1 (by linarith))
  have hφ1 : (1 : ℝ) ≤ φ N z := Real.one_le_rpow hNr1 (by positivity)
  have hb := LL_big_det _ (φ N z) _ hm1 hφ1 (by positivity) hx1
  rw [← LL_psiPhi_eq] at hb
  have hφ4 : φ N z ^ 4 = (N : ℝ) ^ (8 * δ) := by
    simp only [hφdef]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr0.le]; ring_nf
  have h2 := hN₂ N hN2
  rw [Real.rpow_zero, Real.rpow_add hNr0] at h2
  rw [hφ4] at hb
  have h3 : 24 * (N : ℝ) ^ (8 * δ) * Real.sqrt (1 / ((N : ℝ) * z.im)) ≤
      24 * (N : ℝ) ^ (8 * δ) * (N : ℝ) ^ (-τ₁ / 2) :=
    mul_le_mul_of_nonneg_left hsx (by positivity)
  linarith

/-- Every level: `|s^*(G - M)t| ≺ 1` on `bootDom τ₁ ℓ_k` for all `k`, `δ = τ₁/(4K)`. -/
private lemma LL_all_levels (K : ℝ) (hK : 8 ≤ K) (hboot : LL_BootStmt K) (D : ℕ) (δA : ℝ)
    (C θ : ℕ → ℝ) (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ))
    (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (hs : LLSeq D δA C θ μ A) (τ₁ : ℝ) (hτ₁ : 0 < τ₁)
    (hτ₁4 : τ₁ ≤ 1 / 4) (k : ℕ) :
    aprioriLL D μ A (bootDom τ₁ (LL_lev τ₁ (τ₁ / (4 * K)) k)) (fun _ _ => 1) := by
  induction k with
  | zero =>
    refine LL_apriori_top hs _ fun N z hz => le_trans ?_ hz.2.1
    unfold LL_lev
    refine le_trans ?_ (le_max_left _ _)
    simp
  | succ k ih =>
    exact LL_level K hK hboot D δA C θ μ A hs τ₁ hτ₁ hτ₁4 _ _ (fun N => le_max_right _ _)
      (fun N hN => LL_lev_ratio τ₁ _ (by positivity) k N hN) ih

/-! ### The iterations of the bootstrap on the last level -/

/-- The cut-off `max(N⁻¹, min(t, min(1, N)))` that keeps an a priori bound in the range of
`bootstrap_stage`. -/
private def LL_cap (N : ℕ) (t : ℝ) : ℝ := max ((N : ℝ)⁻¹) (min t (min 1 (N : ℝ)))

private lemma LL_cap_ge (N : ℕ) (t : ℝ) : ((N : ℝ))⁻¹ ≤ LL_cap N t := le_max_left _ _

private lemma LL_cap_le_one (N : ℕ) (t : ℝ) : LL_cap N t ≤ 1 := by
  unfold LL_cap
  refine max_le ?_ ((min_le_right _ _).trans (min_le_left _ _))
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast hN)

private lemma LL_cap_le_rpow (N : ℕ) (t a : ℝ) (ha : 0 < a) : LL_cap N t ≤ (N : ℝ) ^ a := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · unfold LL_cap
    simp only [Nat.cast_zero, _root_.inv_zero, min_eq_right zero_le_one]
    rw [Real.zero_rpow ha.ne']
    exact max_le le_rfl (min_le_right _ _)
  · exact (LL_cap_le_one N t).trans (Real.one_le_rpow (by exact_mod_cast hN) ha.le)

private lemma LL_cap_mono (N : ℕ) {t t' : ℝ} (h : t ≤ t') : LL_cap N t ≤ LL_cap N t' :=
  max_le_max le_rfl (min_le_min h le_rfl)

private lemma LL_cap_le_max (N : ℕ) (t : ℝ) : LL_cap N t ≤ max ((N : ℝ)⁻¹) t :=
  max_le_max le_rfl (min_le_left _ _)

private lemma LL_cap_ge_min (N : ℕ) (hN : 1 ≤ N) (t : ℝ) : min t 1 ≤ LL_cap N t := by
  have : min 1 (N : ℝ) = 1 := min_eq_left (by exact_mod_cast hN)
  unfold LL_cap
  rw [this]
  exact le_max_right _ _

/-- The a priori bound of the iterations: `φ_s = cap(256 N^s Ψ)` with `Ψ = Ψ_0` (`φ_s = cap(1)`
for `N < N_Λ`). -/
private def LL_phi (D : ℕ) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (NΛ : ℕ) (s : ℝ) (N : ℕ) (z : ℂ) :
    ℝ :=
  LL_cap N (if NΛ ≤ N then 256 * (N : ℝ) ^ s * psiPhi (lam D N (A N)) N z 0 else 1)

/-- `Ψ_0(E + iη)` does not increase in `η` (for `‖Λ‖ ≤ 1/10`). -/
private lemma LL_psi0_anti {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (N : ℕ) (hN : 1 ≤ N)
    (E η η' : ℝ) (hη : 0 < η) (hηη : η ≤ η') :
    psiPhi Λ N ((E : ℂ) + (η' : ℂ) * Complex.I) 0 ≤ psiPhi Λ N ((E : ℂ) + (η : ℂ) * Complex.I) 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hη' : 0 < η' := lt_of_lt_of_le hη hηη
  have him : ∀ t : ℝ, ((E : ℂ) + (t : ℂ) * Complex.I).im = t := fun t => by simp
  have hz : 0 < ((E : ℂ) + (η : ℂ) * Complex.I).im := by rw [him]; exact hη
  have hz' : 0 < ((E : ℂ) + (η' : ℂ) * Complex.I).im := by rw [him]; exact hη'
  unfold psiPhi
  rw [him, him, add_zero, add_zero, (LL_MExt_eq Λ _ hz).1, (LL_MExt_eq Λ _ hz').1]
  have h1 := LL_imm_anti Λ hΛ hℓ E η η' hη hηη
  refine add_le_add (Real.sqrt_le_sqrt ?_) ?_
  · rw [div_mul_eq_div_div_swap, div_mul_eq_div_div_swap]
    exact div_le_div_of_nonneg_right h1 hN0.le
  · exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hηη hN0.le)

/-- The range and monotonicity hypotheses of `bootstrap_stage` for `φ_s`. -/
private lemma LL_phi_hyp (D : ℕ) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (hD : 1 ≤ D) (NΛ : ℕ)
    (hNΛ1 : 1 ≤ NΛ) (hNΛ : ∀ N : ℕ, NΛ ≤ N → opNorm (lam D N (A N)) ≤ 1 / 10) (s : ℝ)
    (τ₁ K : ℝ) (hτK : 0 < τ₁ / K) (ℓ : ℕ → ℝ)
    (hℓ : ∀ N : ℕ, (N : ℝ) ^ (-1 + τ₁) ≤ ℓ N) :
    (∀ N, ∀ z ∈ bootDom τ₁ ℓ N, ((N : ℝ))⁻¹ ≤ LL_phi D A NΛ s N z ∧
        LL_phi D A NΛ s N z ≤ (N : ℝ) ^ (τ₁ / K)) ∧
      (∀ (N : ℕ) (E η η' : ℝ), ((E : ℂ) + (η : ℂ) * Complex.I) ∈ bootDom τ₁ ℓ N → η ≤ η' →
        η' ≤ 2 → LL_phi D A NΛ s N ((E : ℂ) + (η' : ℂ) * Complex.I) ≤
          LL_phi D A NΛ s N ((E : ℂ) + (η : ℂ) * Complex.I)) := by
  refine ⟨fun N z _ => ⟨LL_cap_ge _ _, LL_cap_le_rpow _ _ _ hτK⟩, ?_⟩
  intro N E η η' hz hηη _
  unfold LL_phi
  by_cases hN : NΛ ≤ N
  · simp only [hN, ↓reduceIte]
    refine LL_cap_mono N ?_
    have hN1 : 1 ≤ N := hNΛ1.trans hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN1⟩)⟩
    have hη : 0 < η := by
      have h1 := (hℓ N).trans hz.2.1
      have h2 : ((E : ℂ) + (η : ℂ) * Complex.I).im = η := by simp
      rw [h2] at h1
      exact lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) h1
    exact mul_le_mul_of_nonneg_left
      (LL_psi0_anti _ (lam_isHermitian D N (A N)) (hNΛ N hN) N hN1 E η η' hη hηη)
      (by positivity)
  · simp [hN]

/-- The deterministic bounds of one iteration: for `N ≥ max(N_Λ, 1)` and `z ∈ bootDom τ₁ ℓ`, with
`φ = φ_s`, `Ψ = Ψ_0`: `(1 + φ)³ Ψ_φ ≤ 136 N^{s/2} Ψ` and `(1 + φ)³ Ψ_φ ≤ 24 N^{-τ₁/2}`. -/
private lemma LL_out_le (D : ℕ) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (hD : 1 ≤ D) (NΛ : ℕ)
    (hNΛ : ∀ N : ℕ, NΛ ≤ N → opNorm (lam D N (A N)) ≤ 1 / 10) (s : ℝ) (hs0 : 0 ≤ s)
    (τ₁ : ℝ) (hτ₁ : 0 < τ₁) (ℓ : ℕ → ℝ) (hℓ : ∀ N : ℕ, (N : ℝ) ^ (-1 + τ₁) ≤ ℓ N)
    (N : ℕ) (hN : NΛ ≤ N) (hN1 : 1 ≤ N) (z : ℂ) (hz : z ∈ bootDom τ₁ ℓ N) :
    (1 + LL_phi D A NΛ s N z) ^ 3 * psiPhi (lam D N (A N)) N z (LL_phi D A NΛ s N z) ≤
        136 * (N : ℝ) ^ (s / 2) * psiPhi (lam D N (A N)) N z 0 ∧
      (1 + LL_phi D A NΛ s N z) ^ 3 * psiPhi (lam D N (A N)) N z (LL_phi D A NΛ s N z) ≤
        24 * (N : ℝ) ^ (-τ₁ / 2) ∧
      0 ≤ psiPhi (lam D N (A N)) N z 0 ∧
      1 / ((N : ℝ) * z.im) ≤ psiPhi (lam D N (A N)) N z 0 := by
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNr0 : (0 : ℝ) < N := by linarith
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN1⟩)⟩
  obtain ⟨hη0, hx, hsx⟩ := LL_x_le N hN1 τ₁ z.im ((hℓ N).trans hz.2.1)
  obtain ⟨hm0, hm1⟩ := LL_imm_bounds _ (lam_isHermitian D N (A N)) (hNΛ N hN) z hη0
  set x := 1 / ((N : ℝ) * z.im) with hxdef
  set m := (mExt (lam D N (A N)) z).im with hmdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := hx.trans (Real.rpow_le_one_of_one_le_of_nonpos hNr1 (by linarith))
  set φ := LL_phi D A NΛ s N z with hφdef
  have hΨ : psiPhi (lam D N (A N)) N z 0 = Real.sqrt (m * x) + x := by
    rw [LL_psiPhi_eq, add_zero]
  have hφ0 : 0 ≤ φ := (inv_nonneg.mpr hNr0.le).trans (LL_cap_ge _ _)
  have hφ1 : φ ≤ 1 := LL_cap_le_one _ _
  have hNs : (1 : ℝ) ≤ (N : ℝ) ^ s := Real.one_le_rpow hNr1 hs0
  have hΨ0 : 0 ≤ Real.sqrt (m * x) + x := by positivity
  have hxΨ : x ≤ Real.sqrt (m * x) + x := by linarith [Real.sqrt_nonneg (m * x)]
  have hφa : φ ≤ (256 * (N : ℝ) ^ s) * (Real.sqrt (m * x) + x) := by
    have h1 : φ ≤ max ((N : ℝ)⁻¹) (256 * (N : ℝ) ^ s * psiPhi (lam D N (A N)) N z 0) := by
      have := LL_cap_le_max N (256 * (N : ℝ) ^ s * psiPhi (lam D N (A N)) N z 0)
      simpa [hφdef, LL_phi, hN] using this
    rw [hΨ] at h1
    refine h1.trans (max_le ?_ le_rfl)
    -- `N⁻¹ ≤ 2x` since `η ≤ 2`
    have h2 : ((N : ℝ))⁻¹ ≤ 2 * x := by
      rw [hxdef, inv_eq_one_div, mul_one_div, le_div_iff₀ (by positivity)]
      have := hz.2.2
      field_simp
      nlinarith
    nlinarith
  have hstep := LL_step_det m φ x (256 * (N : ℝ) ^ s) hm0.le hφ0 hφ1 hx0 (by linarith) hφa
  have hsq : Real.sqrt (256 * (N : ℝ) ^ s) = 16 * (N : ℝ) ^ (s / 2) := by
    rw [Real.sqrt_mul (by norm_num), show (256 : ℝ) = 16 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), Real.sqrt_eq_rpow, ← Real.rpow_mul hNr0.le]
    ring_nf
  rw [hsq] at hstep
  have hNs2 : (1 : ℝ) ≤ (N : ℝ) ^ (s / 2) := Real.one_le_rpow hNr1 (by linarith)
  have hsmall := LL_small_det m φ x hm1 hφ0 hφ1 hx0 hx1
  rw [← LL_psiPhi_eq] at hstep hsmall
  rw [← hΨ] at hstep
  refine ⟨hstep.trans ?_, hsmall.trans (by linarith), by rw [hΨ]; exact hΨ0, by rw [hΨ]; exact hxΨ⟩
  have hΨ0' : 0 ≤ psiPhi (lam D N (A N)) N z 0 := by rw [hΨ]; exact hΨ0
  have : 8 * (1 + 16 * (N : ℝ) ^ (s / 2)) ≤ 136 * (N : ℝ) ^ (s / 2) := by linarith
  exact mul_le_mul_of_nonneg_right this hΨ0'

/-- One iteration (row R1): `|s^*(G - M)t| ≺ φ_s` on `bootDom τ₁ ℓ` gives `≺ φ_{s/2}`. -/
private lemma LL_iter (K : ℝ) (hK : 8 ≤ K) (hboot : LL_BootStmt K) (D : ℕ) (δA : ℝ)
    (C θ : ℕ → ℝ) (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ))
    (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (hs : LLSeq D δA C θ μ A) (τ₁ : ℝ) (hτ₁ : 0 < τ₁)
    (hτ₁4 : τ₁ ≤ 1 / 4) (ℓ : ℕ → ℝ) (hℓ : ∀ N : ℕ, (N : ℝ) ^ (-1 + τ₁) ≤ ℓ N) (NΛ : ℕ)
    (hNΛ1 : 1 ≤ NΛ) (hNΛ : ∀ N : ℕ, NΛ ≤ N → opNorm (lam D N (A N)) ≤ 1 / 10) (s : ℝ)
    (hs0 : 0 ≤ s) (hP : aprioriLL D μ A (bootDom τ₁ ℓ) (LL_phi D A NΛ s)) :
    aprioriLL D μ A (bootDom τ₁ ℓ) (LL_phi D A NΛ (s / 2)) := by
  have hK0 : 0 < K := by linarith
  obtain ⟨hφ, hmono⟩ := LL_phi_hyp D A hs.one_le_D NΛ hNΛ1 hNΛ s τ₁ K (by positivity) ℓ hℓ
  have hout := (hboot D δA τ₁ C θ μ A hs hτ₁ hτ₁4 ℓ hℓ _ hφ hmono hP).2.1
  apply LL_to_apriori
  refine LL_Sup_le (LL_of_apriori hout) ?_
  obtain ⟨N₂, hN₂⟩ := LL_rpow_absorb (show -τ₁ / 2 < 0 by linarith) 24
  refine ⟨max (max NΛ N₂) 1, fun N hN z hz => ?_⟩
  have hNΛ' : NΛ ≤ N := le_trans (by simp) hN
  have hN2 : N₂ ≤ N := le_trans (by simp) hN
  have hN1 : 1 ≤ N := le_trans (by simp) hN
  obtain ⟨h1, h2, -, -⟩ := LL_out_le D A hs.one_le_D NΛ hNΛ s hs0 τ₁ hτ₁ ℓ hℓ N hNΛ' hN1 z hz
  have h3 := hN₂ N hN2
  rw [Real.rpow_zero] at h3
  have e : LL_phi D A NΛ (s / 2) N z =
      LL_cap N (256 * (N : ℝ) ^ (s / 2) * psiPhi (lam D N (A N)) N z 0) := by
    simp [LL_phi, hNΛ']
  rw [e]
  refine le_trans (le_min ?_ ?_) (LL_cap_ge_min N hN1 _)
  · have : 136 * (N : ℝ) ^ (s / 2) * psiPhi (lam D N (A N)) N z 0 ≤
        256 * (N : ℝ) ^ (s / 2) * psiPhi (lam D N (A N)) N z 0 := by
      have hΨ := (LL_out_le D A hs.one_le_D NΛ hNΛ s hs0 τ₁ hτ₁ ℓ hℓ N hNΛ' hN1 z hz).2.2.1
      have : (0 : ℝ) ≤ (N : ℝ) ^ (s / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      nlinarith
    exact h1.trans this
  · linarith

/-- All iterations: `|s^*(G - M)t| ≺ φ_{2^{-j}}` on the last level for every `j`. -/
private lemma LL_all_iter (K : ℝ) (hK : 8 ≤ K) (hboot : LL_BootStmt K) (D : ℕ) (δA : ℝ)
    (C θ : ℕ → ℝ) (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ))
    (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (hs : LLSeq D δA C θ μ A) (τ₁ : ℝ) (hτ₁ : 0 < τ₁)
    (hτ₁4 : τ₁ ≤ 1 / 4) (ℓ : ℕ → ℝ) (hℓ : ∀ N : ℕ, (N : ℝ) ^ (-1 + τ₁) ≤ ℓ N) (NΛ : ℕ)
    (hNΛ1 : 1 ≤ NΛ) (hNΛ : ∀ N : ℕ, NΛ ≤ N → opNorm (lam D N (A N)) ≤ 1 / 10)
    (hP : aprioriLL D μ A (bootDom τ₁ ℓ) (fun _ _ => 1)) (j : ℕ) :
    aprioriLL D μ A (bootDom τ₁ ℓ) (LL_phi D A NΛ ((1 / 2) ^ j)) := by
  induction j with
  | zero =>
    apply LL_to_apriori
    refine LL_Sup_le (LL_of_apriori hP) ⟨NΛ, fun N hN z hz => ?_⟩
    have hN1 : 1 ≤ N := hNΛ1.trans hN
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    obtain ⟨-, -, hΨ0, hxΨ⟩ := LL_out_le D A hs.one_le_D NΛ hNΛ 1 zero_le_one τ₁ hτ₁ ℓ hℓ N hN
      hN1 z hz
    obtain ⟨hη0, -, -⟩ := LL_x_le N hN1 τ₁ z.im ((hℓ N).trans hz.2.1)
    have e : LL_phi D A NΛ ((1 / 2) ^ 0) N z =
        LL_cap N (256 * (N : ℝ) ^ (1 : ℝ) * psiPhi (lam D N (A N)) N z 0) := by
      simp [LL_phi, hN]
    rw [e]
    refine le_trans ?_ (LL_cap_ge_min N hN1 _)
    refine le_min ?_ le_rfl
    rw [Real.rpow_one]
    have h1 : 1 / 2 ≤ (N : ℝ) * (1 / ((N : ℝ) * z.im)) := by
      have := hz.2.2
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  | succ j ih =>
    have e : ((1 : ℝ) / 2) ^ (j + 1) = (1 / 2) ^ j / 2 := by ring
    rw [e]
    exact LL_iter K hK hboot D δA C θ μ A hs τ₁ hτ₁ hτ₁4 ℓ hℓ NΛ hNΛ1 hNΛ _ (by positivity) ih

/-! ### The local laws on `𝐃(τ) ∩ {0 < η ≤ 2}` in sup form -/

/-- The control of the block traces in `blockTr_local`: `min(Ψ²/√(κ + |η|), Ψ)`. -/
private def LL_zB (D : ℕ) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (N : ℕ) (z : ℂ) : ℝ :=
  min (psiIso (lam D N (A N)) N z ^ 2 / Real.sqrt (kappa (lam D N (A N)) z.re + |z.im|))
    (psiIso (lam D N (A N)) N z)

/-- The control of (2.22) [eq:aniso_local]: `Ψ`. -/
private def LL_zI (D : ℕ) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (N : ℕ) (z : ℂ) : ℝ :=
  psiIso (lam D N (A N)) N z

/-- The control of (2.23) [eq:aver_local]: `1/(N|η|)`. -/
private def LL_zA (N : ℕ) (z : ℂ) : ℝ := 1 / ((N : ℝ) * |z.im|)

/-- `𝐃(τ) ∩ {0 < η ≤ 2}`. -/
private def LL_Zlow (τ : ℝ) (N : ℕ) : Set ℂ := {z | z ∈ specDom τ N ∧ 0 < z.im ∧ z.im ≤ 2}

/-- `𝐃(τ) ∩ {η ≥ 2}`. -/
private def LL_Zhigh (τ : ℝ) (N : ℕ) : Set ℂ := {z | z ∈ specDom τ N ∧ 2 ≤ z.im}

/-- `Ψ = Ψ_0` on the upper half plane. -/
private lemma LL_psiIso_eq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (N : ℕ) (z : ℂ) (hz : 0 < z.im) :
    psiIso Λ N z = psiPhi Λ N z 0 := by
  have hm := (LL_M_inv Λ hΛ z hz).1
  unfold psiIso psiPhi
  rw [abs_of_pos hm, abs_of_pos hz, add_zero]

/-- The comparison of the block-trace controls (deterministic): if `0 ≤ o ≤ c ≤ k u` and
`c² ≤ k u²`, then `min(o²/d, o) ≤ k min(u²/d, u)`. -/
private lemma LL_min_le (o c d k u : ℝ) (ho : 0 ≤ o) (hoc : o ≤ c) (hd : 0 ≤ d)
    (hck : c ≤ k * u) (hc2 : c ^ 2 ≤ k * u ^ 2) (hk : 0 ≤ k) :
    min (o ^ 2 / d) o ≤ k * min (u ^ 2 / d) u := by
  rw [mul_min_of_nonneg _ _ hk]
  refine min_le_min ?_ (hoc.trans hck)
  have h1 : o ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ ho hoc 2
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (h1.trans hc2) hd

/-- The averaged control (deterministic): for `0 ≤ m ≤ 1`, `0 < x ≤ 1`, `d > 0`, `C ≥ 0` and
`m ≤ C d`, with `Ψ = √(m x) + x`: `Ψ² + min(Ψ²/d, Ψ) ≤ (2C + 8) x`. -/
private lemma LL_avg_ctl (m x d C : ℝ) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hd : 0 < d) (hC : 0 ≤ C) (hmC : m ≤ C * d) :
    (Real.sqrt (m * x) + x) ^ 2 + min ((Real.sqrt (m * x) + x) ^ 2 / d)
      (Real.sqrt (m * x) + x) ≤ (2 * C + 8) * x := by
  set r := Real.sqrt (m * x) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = m * x := Real.sq_sqrt (by positivity)
  have hsq : (r + x) ^ 2 ≤ 2 * (m * x) + 2 * x ^ 2 := by nlinarith [sq_nonneg (r - x)]
  have h1 : (r + x) ^ 2 ≤ 4 * x := by nlinarith
  have h2 : min ((r + x) ^ 2 / d) (r + x) ≤ (2 * C + 4) * x := by
    rcases le_or_gt x d with hxd | hxd
    · refine (min_le_left _ _).trans ?_
      rw [div_le_iff₀ hd]
      have : 2 * (m * x) + 2 * x ^ 2 ≤ 2 * (C * d * x) + 2 * (x * d) := by nlinarith
      nlinarith
    · refine (min_le_right _ _).trans ?_
      have hrle : r ≤ (C + 1) * x := by
        rw [hr, Real.sqrt_le_left (by positivity)]
        have : m * x ≤ C * x * x := by nlinarith
        nlinarith
      nlinarith
  linarith

/-- `Im m ≤ C √(κ + η)` on `|z| ≤ τ⁻¹`, `η > 0`, with the constant `C` of
`square_root_density`. -/
private lemma LL_imm_le_sqrt (τ C : ℝ)
    (hC : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      (∀ x ∈ Set.Icc (Eminus Λ) (Eplus Λ),
        C⁻¹ * Real.sqrt ((Eplus Λ - x) * (x - Eminus Λ)) ≤ rho Λ x ∧
          rho Λ x ≤ C * Real.sqrt ((Eplus Λ - x) * (x - Eminus Λ))) ∧
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
        (z.re ∈ Set.Icc (Eminus Λ) (Eplus Λ) →
          C⁻¹ * Real.sqrt (kappa Λ z.re + z.im) ≤ (mSol Λ z).im ∧
            (mSol Λ z).im ≤ C * Real.sqrt (kappa Λ z.re + z.im)) ∧
        (z.re ∉ Set.Icc (Eminus Λ) (Eplus Λ) →
          C⁻¹ * (z.im / Real.sqrt (kappa Λ z.re + z.im)) ≤ (mSol Λ z).im ∧
            (mSol Λ z).im ≤ C * (z.im / Real.sqrt (kappa Λ z.re + z.im))))
    (hCpos : 0 < C) {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hzτ : ‖z‖ ≤ τ⁻¹) (hz : 0 < z.im) :
    (mExt Λ z).im ≤ C * Real.sqrt (kappa Λ z.re + z.im) := by
  rw [(LL_MExt_eq Λ z hz).1]
  have hk : 0 ≤ kappa Λ z.re := le_min (abs_nonneg _) (abs_nonneg _)
  obtain ⟨-, h2⟩ := hC ι Λ hΛ hℓ
  obtain ⟨hin, hout⟩ := h2 z hzτ hz
  by_cases hre : z.re ∈ Set.Icc (Eminus Λ) (Eplus Λ)
  · exact (hin hre).2
  · refine (hout hre).2.trans (mul_le_mul_of_nonneg_left ?_ hCpos.le)
    have hd : 0 < Real.sqrt (kappa Λ z.re + z.im) := Real.sqrt_pos.mpr (by linarith)
    rw [div_le_iff₀ hd, ← sq, Real.sq_sqrt (by linarith)]
    linarith

/-- The local laws on `𝐃(τ) ∩ {0 < η ≤ 2}` in sup form: the block traces, (2.22)
[eq:aniso_local] and (2.23) [eq:aver_local] for one sequence of members, from the levels and the
iterations of `bootstrap_stage` on `bootDom τ₁ ℓ_L`, `τ₁ = min(τ, 1/4)`. -/
private lemma LL_low (K : ℝ) (hK : 8 ≤ K) (hboot : LL_BootStmt K) (D : ℕ) (δA : ℝ)
    (C θ : ℕ → ℝ) (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ))
    (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (hs : LLSeq D δA C θ μ A) (τ : ℝ) (hτ : 0 < τ) :
    LL_Sup μ (LL_Zlow τ) (LL_xb D A) (LL_zB D A) ∧
      LL_Sup μ (LL_Zlow τ) (LL_xi D A) (LL_zI D A) ∧
      LL_Sup μ (LL_Zlow τ) (LL_xa D A) (fun N z => LL_zA N z) := by
  have hK0 : 0 < K := by linarith
  set τ₁ := min τ (1 / 4) with hτ₁def
  have hτ₁ : 0 < τ₁ := lt_min hτ (by norm_num)
  have hτ₁4 : τ₁ ≤ 1 / 4 := min_le_right _ _
  have hτ₁τ : τ₁ ≤ τ := min_le_left _ _
  set δ := τ₁ / (4 * K) with hδdef
  have hδ : 0 < δ := by positivity
  set L := ⌈1 / δ⌉₊ with hLdef
  have hLδ : 1 ≤ (L : ℝ) * δ := by
    have := Nat.le_ceil (1 / δ)
    rw [div_le_iff₀ hδ] at this
    linarith
  set ℓ := LL_lev τ₁ δ L with hℓdef
  have hℓ : ∀ N : ℕ, (N : ℝ) ^ (-1 + τ₁) ≤ ℓ N := fun N => le_max_right _ _
  have hP := LL_all_levels K hK hboot D δA C θ μ A hs τ₁ hτ₁ hτ₁4 L
  obtain ⟨NΛ₀, hNΛ₀⟩ := LL_lam_small hs
  set NΛ := max NΛ₀ 1 with hNΛdef
  have hNΛ1 : 1 ≤ NΛ := le_max_right _ _
  have hNΛ : ∀ N : ℕ, NΛ ≤ N → opNorm (lam D N (A N)) ≤ 1 / 10 :=
    fun N hN => hNΛ₀ N (le_trans (le_max_left _ _) hN)
  have hIt := LL_all_iter K hK hboot D δA C θ μ A hs τ₁ hτ₁ hτ₁4 ℓ hℓ NΛ hNΛ1 hNΛ hP
  have hD1 := hs.one_le_D
  -- the outputs of `bootstrap_stage` at the iterate `j`
  have hO : ∀ j : ℕ, _ := fun j =>
    hboot D δA τ₁ C θ μ A hs hτ₁ hτ₁4 ℓ hℓ _
      (LL_phi_hyp D A hD1 NΛ hNΛ1 hNΛ ((1 / 2) ^ j) τ₁ K (by positivity) ℓ hℓ).1
      (LL_phi_hyp D A hD1 NΛ hNΛ1 hNΛ ((1 / 2) ^ j) τ₁ K (by positivity) ℓ hℓ).2 (hIt j)
  -- the domain
  obtain ⟨N₂, hN₂⟩ := LL_rpow_large hτ₁ 2
  have hdom : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → LL_Zlow τ N ⊆ bootDom τ₁ ℓ N := by
    refine ⟨max N₂ 1, fun N hN z hz => ?_⟩
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNr0 : (0 : ℝ) < N := by linarith
    obtain ⟨⟨hzτ, hzη⟩, hz0, hz2⟩ := hz
    refine ⟨?_, ?_, hz2⟩
    · refine (Complex.abs_re_le_norm z).trans (hzτ.trans ?_)
      exact inv_anti₀ hτ₁ hτ₁τ
    · rw [abs_of_pos hz0] at hzη
      refine le_trans (max_le ?_ ?_) hzη
      · have h1 : (N : ℝ) ^ (-((L : ℝ) * δ)) ≤ (N : ℝ) ^ (-1 : ℝ) := LL_rpow_mono hNr1 (by linarith)
        have h2 := hN₂ N (le_of_max_le_left hN)
        have e : (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ (-1 : ℝ) * (N : ℝ) ^ τ := by
          rw [← Real.rpow_add hNr0]
        have h3 : (N : ℝ) ^ τ₁ ≤ (N : ℝ) ^ τ := LL_rpow_mono hNr1 hτ₁τ
        have h4 : 0 ≤ (N : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg hNr0.le _
        rw [e]
        nlinarith
      · exact LL_rpow_mono hNr1 (by linarith)
  -- the size of `N^{2^{-j}}`
  have hjs : ∀ ε : ℝ, 0 < ε → ∃ j : ℕ, ((1 : ℝ) / 2) ^ j < ε :=
    fun ε hε => exists_pow_lt_of_lt_one hε (by norm_num)
  obtain ⟨Csq, hCsq, hCsqP⟩ := square_root_density τ hτ
  -- the deterministic comparison at the iterate `j`, on `Zlow`
  have hcmp : ∀ j : ℕ, ∀ N : ℕ, NΛ ≤ N → ∀ z ∈ LL_Zlow τ N, z ∈ bootDom τ₁ ℓ N →
      let φ := LL_phi D A NΛ ((1 / 2) ^ j) N z
      let o := (1 + φ) ^ 3 * psiPhi (lam D N (A N)) N z φ
      0 ≤ o ∧ o ≤ 136 ^ 2 * (N : ℝ) ^ (((1 : ℝ) / 2) ^ j) * LL_zI D A N z ∧
        min (o ^ 2 / Real.sqrt (kappa (lam D N (A N)) z.re + z.im)) o ≤
          136 ^ 2 * (N : ℝ) ^ (((1 : ℝ) / 2) ^ j) * LL_zB D A N z ∧
        o ^ 2 + min (o ^ 2 / Real.sqrt (kappa (lam D N (A N)) z.re + z.im)) o ≤
          136 ^ 2 * (N : ℝ) ^ (((1 : ℝ) / 2) ^ j) * ((2 * Csq + 8) * LL_zA N z) := by
    intro j N hN z hz hzb φ o
    have hN1 : 1 ≤ N := hNΛ1.trans hN
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNr0 : (0 : ℝ) < N := by linarith
    have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1⟩)⟩
    have hΛh := lam_isHermitian D N (A N)
    set s : ℝ := (1 / 2) ^ j with hsdef
    have hs0 : 0 ≤ s := by positivity
    obtain ⟨ho1, -, hΨ0, -⟩ := LL_out_le D A hD1 NΛ hNΛ s hs0 τ₁ hτ₁ ℓ hℓ N hN hN1 z hzb
    obtain ⟨⟨hzτ, hzη⟩, hz0, hz2⟩ := hz
    have hψ : LL_zI D A N z = psiPhi (lam D N (A N)) N z 0 := LL_psiIso_eq _ hΛh N z hz0
    set Ψ := psiPhi (lam D N (A N)) N z 0 with hΨdef
    have hφ0 : 0 ≤ φ := (inv_nonneg.mpr hNr0.le).trans (LL_cap_ge _ _)
    have ho0 : 0 ≤ o := by
      have : 0 ≤ psiPhi (lam D N (A N)) N z φ := by unfold psiPhi; positivity
      positivity
    have hNs2 : (1 : ℝ) ≤ (N : ℝ) ^ (s / 2) := Real.one_le_rpow hNr1 (by linarith)
    have hNs : (N : ℝ) ^ (s / 2) ≤ (N : ℝ) ^ s := LL_rpow_mono hNr1 (by linarith)
    have hNsq : ((N : ℝ) ^ (s / 2)) ^ 2 = (N : ℝ) ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNr0.le]; ring_nf
    have hck : 136 * (N : ℝ) ^ (s / 2) * Ψ ≤ 136 ^ 2 * (N : ℝ) ^ s * Ψ := by
      have : 136 * (N : ℝ) ^ (s / 2) ≤ 136 ^ 2 * (N : ℝ) ^ s := by nlinarith
      exact mul_le_mul_of_nonneg_right this hΨ0
    have hc2 : (136 * (N : ℝ) ^ (s / 2) * Ψ) ^ 2 = 136 ^ 2 * (N : ℝ) ^ s * Ψ ^ 2 := by
      rw [mul_pow, mul_pow, hNsq]
    have hk0 : (0 : ℝ) ≤ 136 ^ 2 * (N : ℝ) ^ s := by positivity
    have hd0 : 0 ≤ Real.sqrt (kappa (lam D N (A N)) z.re + z.im) := Real.sqrt_nonneg _
    have hzB : LL_zB D A N z = min (Ψ ^ 2 / Real.sqrt (kappa (lam D N (A N)) z.re + z.im)) Ψ := by
      simp only [LL_zB, abs_of_pos hz0]
      rw [← hψ]; rfl
    have hmin := LL_min_le o (136 * (N : ℝ) ^ (s / 2) * Ψ) _ (136 ^ 2 * (N : ℝ) ^ s) Ψ ho0 ho1 hd0
      hck hc2.le hk0
    refine ⟨ho0, ?_, by rw [hzB]; exact hmin, ?_⟩
    · rw [hψ]
      exact ho1.trans hck
    · -- the averaged control
      obtain ⟨hη0, hx, -⟩ := LL_x_le N hN1 τ z.im (by rw [abs_of_pos hz0] at hzη; exact hzη)
      have hx1 : 1 / ((N : ℝ) * z.im) ≤ 1 :=
        hx.trans (Real.rpow_le_one_of_one_le_of_nonpos hNr1 (by linarith))
      obtain ⟨hm0, hm1⟩ := LL_imm_bounds _ hΛh (hNΛ N hN) z hz0
      have hk : 0 ≤ kappa (lam D N (A N)) z.re := le_min (abs_nonneg _) (abs_nonneg _)
      have hd : 0 < Real.sqrt (kappa (lam D N (A N)) z.re + z.im) :=
        Real.sqrt_pos.mpr (by linarith)
      have hmC := LL_imm_le_sqrt τ Csq hCsqP hCsq _ hΛh (hNΛ N hN) z hzτ hz0
      have hctl := LL_avg_ctl _ _ _ Csq hm0.le hm1 (by positivity) hx1 hd hCsq.le hmC
      have hΨe : Ψ = Real.sqrt ((mExt (lam D N (A N)) z).im * (1 / ((N : ℝ) * z.im))) +
          1 / ((N : ℝ) * z.im) := by rw [hΨdef, LL_psiPhi_eq, add_zero]
      rw [← hΨe] at hctl
      have hzA : LL_zA N z = 1 / ((N : ℝ) * z.im) := by simp [LL_zA, abs_of_pos hz0]
      rw [hzA]
      have ho2 : o ^ 2 ≤ 136 ^ 2 * (N : ℝ) ^ s * Ψ ^ 2 := by
        rw [← hc2]; exact pow_le_pow_left₀ ho0 ho1 2
      have hmin' : min (o ^ 2 / Real.sqrt (kappa (lam D N (A N)) z.re + z.im)) o ≤
          136 ^ 2 * (N : ℝ) ^ s * min (Ψ ^ 2 / Real.sqrt (kappa (lam D N (A N)) z.re + z.im)) Ψ :=
        hmin
      calc o ^ 2 + min (o ^ 2 / Real.sqrt (kappa (lam D N (A N)) z.re + z.im)) o
          ≤ 136 ^ 2 * (N : ℝ) ^ s * (Ψ ^ 2 +
            min (Ψ ^ 2 / Real.sqrt (kappa (lam D N (A N)) z.re + z.im)) Ψ) := by
            rw [mul_add]; exact add_le_add ho2 hmin'
        _ ≤ 136 ^ 2 * (N : ℝ) ^ s * ((2 * Csq + 8) * (1 / ((N : ℝ) * z.im))) :=
            mul_le_mul_of_nonneg_left hctl hk0
  -- assembling the three bounds
  have hfam : ∀ (W : ℕ → Type) (ξ : ∀ N, ℂ → W N → (Idx D N → Idx D N → ℂ) → ℝ)
      (ζt : ℕ → ℂ → ℝ) (c : ℝ) (hc : 0 < c) (ζj : ℕ → ℕ → ℂ → ℝ),
      (∀ j, LL_Sup μ (bootDom τ₁ ℓ) ξ (ζj j)) →
      (∀ j : ℕ, ∀ N : ℕ, NΛ ≤ N → ∀ z ∈ LL_Zlow τ N, z ∈ bootDom τ₁ ℓ N →
        ζj j N z ≤ c * (N : ℝ) ^ (((1 : ℝ) / 2) ^ j) * ζt N z) →
      (∀ N : ℕ, ∀ z ∈ LL_Zlow τ N, NΛ ≤ N → 0 ≤ ζt N z) →
      LL_Sup μ (LL_Zlow τ) ξ ζt := by
    intro W ξ ζt c hc ζj hsup hle hnn
    refine LL_Sup_fam fun ε hε => ?_
    obtain ⟨j, hj⟩ := hjs ε hε
    obtain ⟨N₁, hN₁⟩ := hdom
    obtain ⟨N₃, hN₃⟩ := LL_rpow_absorb hj c
    refine ⟨ζj j, LL_Sup_sub (hsup j) ⟨N₁, hN₁⟩, max (max N₁ N₃) NΛ, fun N hN z hz => ?_⟩
    have hzb := hN₁ N (le_trans (by simp) hN) hz
    have hNΛ' : NΛ ≤ N := le_trans (by simp) hN
    refine (hle j N hNΛ' z hz hzb).trans ?_
    exact mul_le_mul_of_nonneg_right (hN₃ N (le_trans (by simp) hN)) (hnn N z hz hNΛ')
  refine ⟨?_, ?_, ?_⟩
  · refine hfam (fun _ => Unit) (LL_xb D A) (LL_zB D A) (136 ^ 2) (by norm_num)
      (fun j N z => min ((1 + LL_phi D A NΛ ((1 / 2) ^ j) N z) ^ 6 *
          psiPhi (lam D N (A N)) N z (LL_phi D A NΛ ((1 / 2) ^ j) N z) ^ 2 /
          Real.sqrt (kappa (lam D N (A N)) z.re + z.im))
        ((1 + LL_phi D A NΛ ((1 / 2) ^ j) N z) ^ 3 *
          psiPhi (lam D N (A N)) N z (LL_phi D A NΛ ((1 / 2) ^ j) N z)))
      (fun j => LL_of_block (hO j).1) (fun j N hN z hz hzb => ?_) (fun N z hz hN => ?_)
    · have h := (hcmp j N hN z hz hzb).2.2.1
      rw [show ∀ a b : ℝ, (1 + a) ^ 6 * b ^ 2 = ((1 + a) ^ 3 * b) ^ 2 by intros; ring]
      exact h
    · have hN1 : 1 ≤ N := hNΛ1.trans hN
      have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1⟩)⟩
      have h0 : 0 ≤ psiIso (lam D N (A N)) N z := by unfold psiIso; positivity
      exact le_min (by positivity) h0
  · refine hfam (LL_UV D) (LL_xi D A) (LL_zI D A) (136 ^ 2) (by norm_num)
      (fun j N z => (1 + LL_phi D A NΛ ((1 / 2) ^ j) N z) ^ 3 *
          psiPhi (lam D N (A N)) N z (LL_phi D A NΛ ((1 / 2) ^ j) N z))
      (fun j => LL_of_apriori (hO j).2.1) (fun j N hN z hz hzb => ?_) (fun N z hz hN => ?_)
    · exact (hcmp j N hN z hz hzb).2.1
    · unfold LL_zI psiIso; positivity
  · refine hfam (LL_Bs D) (LL_xa D A) (fun N z => LL_zA N z) (136 ^ 2 * (2 * Csq + 8))
      (by positivity)
      (fun j N z => (1 + LL_phi D A NΛ ((1 / 2) ^ j) N z) ^ 6 *
          psiPhi (lam D N (A N)) N z (LL_phi D A NΛ ((1 / 2) ^ j) N z) ^ 2 +
        min ((1 + LL_phi D A NΛ ((1 / 2) ^ j) N z) ^ 6 *
            psiPhi (lam D N (A N)) N z (LL_phi D A NΛ ((1 / 2) ^ j) N z) ^ 2 /
            Real.sqrt (kappa (lam D N (A N)) z.re + z.im))
          ((1 + LL_phi D A NΛ ((1 / 2) ^ j) N z) ^ 3 *
            psiPhi (lam D N (A N)) N z (LL_phi D A NΛ ((1 / 2) ^ j) N z)))
      (fun j => LL_of_avg (hO j).2.2) (fun j N hN z hz hzb => ?_) (fun N z hz hN => ?_)
    · have h := (hcmp j N hN z hz hzb).2.2.2
      rw [show ∀ a b : ℝ, (1 + a) ^ 6 * b ^ 2 = ((1 + a) ^ 3 * b) ^ 2 by intros; ring]
      refine h.trans (le_of_eq ?_)
      ring
    · unfold LL_zA; positivity

/-- Lower bounds of the controls on `𝐃(τ) ∩ {η ≥ 2}` (deterministic, `‖Λ‖ ≤ 1/10`, `N ≥ 1`):
`Ψ ≥ 1/(c_τ √N)` with `c_τ = 11/10 + τ⁻¹` (from `η ≤ c_τ² Im m`, `im_mSol_lower`),
`min(Ψ²/√(κ + |η|), Ψ) ≥ 1/(c_τ² (d_max + 1) N)` with `d_max = √(2τ⁻¹ + 2 + C_e/10)` (from
`edge_close_to_edge_sc`), and `1/(N|η|) ≥ τ/N`. -/
private lemma LL_high_lower (D : ℕ) (hD1 : 1 ≤ D) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (τ : ℝ)
    (hτ : 0 < τ) (Ce : ℝ) (hCe : 0 < Ce)
    (hCeP : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → |2 - Eplus Λ| + |2 + Eminus Λ| ≤ Ce * opNorm Λ)
    (N : ℕ) (hN1 : 1 ≤ N) (hΛ : opNorm (lam D N (A N)) ≤ 1 / 10) (z : ℂ)
    (hz : z ∈ LL_Zhigh τ N) :
    1 / ((11 / 10 + τ⁻¹) * Real.sqrt N) ≤ LL_zI D A N z ∧
      1 / ((11 / 10 + τ⁻¹) ^ 2 * (Real.sqrt (2 * τ⁻¹ + 2 + Ce / 10) + 1) * N) ≤ LL_zB D A N z ∧
      τ / N ≤ LL_zA N z := by
  set Z := τ⁻¹ with hZdef
  have hZ0 : 0 < Z := inv_pos.mpr hτ
  set cτ := 11 / 10 + Z with hcτdef
  have hcτ1 : 1 ≤ cτ := by rw [hcτdef]; linarith
  set dmax := Real.sqrt (2 * Z + 2 + Ce / 10) with hdmaxdef
  have hdmax0 : 0 ≤ dmax := Real.sqrt_nonneg _
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNr0 : (0 : ℝ) < N := by linarith
  have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1⟩)⟩
  have hΛh := lam_isHermitian D N (A N)
  obtain ⟨⟨hzτ, -⟩, hz2⟩ := hz
  have hz0 : 0 < z.im := by linarith
  have hzZ : z.im ≤ Z := (Complex.im_le_norm z).trans hzτ
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr0
  have hsN1 : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  obtain ⟨hlm, -⟩ := im_mSol_lower _ hΛh hΛ τ hτ z hz0 hzτ
  rw [← (LL_MExt_eq _ z hz0).1] at hlm
  have hlm' : (N : ℝ) * z.im ≤ (mExt (lam D N (A N)) z).im * (cτ ^ 2 * N) := by
    calc (N : ℝ) * z.im ≤ N * ((11 / 10 + τ⁻¹) ^ 2 * (mExt (lam D N (A N)) z).im) :=
          mul_le_mul_of_nonneg_left hlm hNr0.le
      _ = _ := by rw [hcτdef, hZdef]; ring
  have hm0 := (LL_M_inv _ hΛh z hz0).1
  have hψ : LL_zI D A N z = Real.sqrt ((mExt (lam D N (A N)) z).im / (N * z.im)) +
      1 / (N * z.im) := by
    unfold LL_zI psiIso
    rw [abs_of_pos hm0, abs_of_pos hz0]
  -- `Ψ ≥ 1/(cτ √N)`
  have hI : 1 / (cτ * Real.sqrt N) ≤ LL_zI D A N z := by
    rw [hψ]
    have h1 : 1 / (cτ * Real.sqrt N) ≤
        Real.sqrt ((mExt (lam D N (A N)) z).im / (N * z.im)) := by
      rw [Real.le_sqrt (by positivity) (by positivity), div_pow, one_pow, mul_pow,
        Real.sq_sqrt hNr0.le, le_div_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      exact hlm'
    have h2 : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
    linarith
  refine ⟨hI, ?_, ?_⟩
  · -- `min(Ψ²/d, Ψ) ≥ 1/(cτ² (dmax + 1) N)`
    have hk : 0 ≤ kappa (lam D N (A N)) z.re := le_min (abs_nonneg _) (abs_nonneg _)
    have hkle : kappa (lam D N (A N)) z.re ≤ Z + 2 + Ce / 10 := by
      have h1 : kappa (lam D N (A N)) z.re ≤ |z.re - Eminus (lam D N (A N))| := min_le_right _ _
      have h2 := hCeP (Idx D N) (lam D N (A N)) hΛh hΛ
      have h3 : |2 + Eminus (lam D N (A N))| ≤ Ce / 10 := by
        have : Ce * opNorm (lam D N (A N)) ≤ Ce * (1 / 10) := mul_le_mul_of_nonneg_left hΛ hCe.le
        linarith [abs_nonneg (2 - Eplus (lam D N (A N)))]
      have h4 : |z.re| ≤ Z := (Complex.abs_re_le_norm z).trans hzτ
      have h5 := abs_sub (z.re) (Eminus (lam D N (A N)))
      have h6 : |Eminus (lam D N (A N))| ≤ 2 + Ce / 10 := by
        have := abs_sub (2 + Eminus (lam D N (A N))) 2
        simp only [add_sub_cancel_left] at this
        rw [abs_two] at this
        linarith
      linarith
    have hd : Real.sqrt (kappa (lam D N (A N)) z.re + |z.im|) ≤ dmax := by
      rw [abs_of_pos hz0]
      exact Real.sqrt_le_sqrt (by linarith)
    have hd0 : 0 < Real.sqrt (kappa (lam D N (A N)) z.re + |z.im|) :=
      Real.sqrt_pos.mpr (by rw [abs_of_pos hz0]; linarith)
    have hI0 : 0 < 1 / (cτ * Real.sqrt N) := by positivity
    unfold LL_zB
    refine le_min ?_ ?_
    · have h1 : (1 / (cτ * Real.sqrt N)) ^ 2 ≤ psiIso (lam D N (A N)) N z ^ 2 :=
        pow_le_pow_left₀ hI0.le hI 2
      have h2 : (1 / (cτ * Real.sqrt N)) ^ 2 = 1 / (cτ ^ 2 * N) := by
        rw [div_pow, mul_pow, Real.sq_sqrt hNr0.le, one_pow]
      rw [h2] at h1
      rw [le_div_iff₀ hd0]
      calc 1 / (cτ ^ 2 * (dmax + 1) * N) * Real.sqrt (kappa (lam D N (A N)) z.re + |z.im|)
          ≤ 1 / (cτ ^ 2 * (dmax + 1) * N) * (dmax + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 1 / (cτ ^ 2 * N) := by field_simp
        _ ≤ _ := h1
    · refine le_trans ?_ hI
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
      have : cτ * Real.sqrt N ≤ cτ ^ 2 * 1 * N := by
        have h1 : cτ ≤ cτ ^ 2 := by nlinarith
        calc cτ * Real.sqrt N ≤ cτ ^ 2 * Real.sqrt N :=
              mul_le_mul_of_nonneg_right h1 hsN.le
          _ ≤ cτ ^ 2 * N := mul_le_mul_of_nonneg_left hsN1 (by positivity)
          _ = cτ ^ 2 * 1 * N := by ring
      calc cτ * Real.sqrt N ≤ cτ ^ 2 * 1 * N := this
        _ ≤ cτ ^ 2 * (dmax + 1) * N := by gcongr; linarith
  · unfold LL_zA
    rw [abs_of_pos hz0, div_le_div_iff₀ hNr0 (by positivity), one_mul]
    have : τ * z.im ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hzZ hτ.le
      rw [hZdef, mul_inv_cancel₀ hτ.ne'] at this
      exact this
    nlinarith

/-! ### The local laws on `𝐃(τ) ∩ {η ≥ 2}` in sup form -/

/-- `Ψ_1 ≤ 2/√N` for `η ≥ 2`, `0 ≤ Im m ≤ 1`, `N ≥ 1`. -/
private lemma LL_psi1_le {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (N : ℕ)
    (hN : 1 ≤ N) (z : ℂ) (hz : 2 ≤ z.im) (hm1 : (mExt Λ z).im ≤ 1) :
    psiPhi Λ N z 1 ≤ 2 / Real.sqrt N := by
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr0
  have hsN1 : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  rw [LL_psiPhi_eq]
  set x := 1 / ((N : ℝ) * z.im) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / (2 * N) := by
    rw [hx]; exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have h1 : Real.sqrt (((mExt Λ z).im + 1) * x) ≤ 1 / Real.sqrt N := by
    rw [one_div (Real.sqrt _), ← Real.sqrt_inv, inv_eq_one_div]
    refine Real.sqrt_le_sqrt ?_
    by_cases hm : 0 ≤ (mExt Λ z).im + 1
    · calc ((mExt Λ z).im + 1) * x ≤ 2 * (1 / (2 * N)) :=
            mul_le_mul (by linarith) hx1 hx0 (by norm_num)
        _ = 1 / N := by field_simp
    · push Not at hm
      have : ((mExt Λ z).im + 1) * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hm.le hx0
      exact this.trans (by positivity)
  have h2 : x ≤ 1 / Real.sqrt N := by
    refine hx1.trans (one_div_le_one_div_of_le hsN (by linarith))
  calc Real.sqrt (((mExt Λ z).im + 1) * x) + x ≤ 1 / Real.sqrt N + 1 / Real.sqrt N :=
        add_le_add h1 h2
    _ = 2 / Real.sqrt N := by ring


/-- `𝐃(τ) ∩ {η ≥ 2} ∩ {|z| ≤ N^{δ₀}}`. -/
private def LL_Zf (τ δ₀ : ℝ) (N : ℕ) : Set ℂ := {z | z ∈ LL_Zhigh τ N ∧ ‖z‖ ≤ (N : ℝ) ^ δ₀}

/-- The local laws on `𝐃(τ) ∩ {η ≥ 2} ∩ {|z| ≤ N^{δ₀}}` in sup form, with controls `c/N`,
`c/√N`, `c/N`, from `blockTr_contraction`, the
fluctuation bounds `fluct_avg_prec'`, `fluct_net'` at the a priori bound `φ = 1` (deterministic:
`‖G - M‖ ≤ 2/η ≤ 1`) and the decomposition `G - M = (R_x̃ - M) - R_x̃ H̲G`. -/
private lemma LL_high_Zf (D : ℕ) (δA : ℝ) (C θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hs : LLSeq D δA C θ μ A) (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ c₁ c₂ c₃ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ 0 ≤ c₃ ∧
      LL_Sup μ (LL_Zf τ δ₀) (LL_xb D A) (fun N _ => c₁ / N) ∧
      LL_Sup μ (LL_Zf τ δ₀) (LL_xi D A) (fun N _ => c₂ / Real.sqrt N) ∧
      LL_Sup μ (LL_Zf τ δ₀) (LL_xa D A) (fun N _ => c₃ / N) := by
  obtain ⟨Kn, hKn1, hKn⟩ := fluct_net'
  obtain ⟨Ka, hKa1, hKa⟩ := fluct_avg_prec'
  have hD1 := hs.one_le_D
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  set δ₀ := 1 / (4 * max Kn Ka) with hδ₀def
  have hKmax : 1 ≤ max Kn Ka := le_max_of_le_left hKn1
  have hδ₀ : 0 < δ₀ := by positivity
  have hKnδ : Kn * δ₀ ≤ 1 / 4 := by
    rw [hδ₀def]; field_simp
    nlinarith [le_max_left Kn Ka]
  have hKaδ : Ka * δ₀ ≤ 1 / 4 := by
    rw [hδ₀def]; field_simp
    nlinarith [le_max_right Kn Ka]
  set Zf : ℕ → Set ℂ := LL_Zf τ δ₀ with hZfdef
  have hZf2 : ∀ N, ∀ z ∈ Zf N, 2 ≤ z.im := fun N z hz => hz.1.2
  have hZf : ∀ N, ∀ z ∈ Zf N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + 1 / 4 : ℝ) ≤ z.im := by
    intro N z hz
    refine ⟨hz.2, le_trans ?_ (hz.1.2.trans' (by norm_num : (1 : ℝ) ≤ 2))⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]; norm_num
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  set φh : ℕ → ℂ → ℝ := fun N _ => min 1 (N : ℝ) with hφhdef
  have hφh : ∀ N, ∀ z ∈ Zf N, ((N : ℝ))⁻¹ ≤ φh N z ∧ φh N z ≤ (N : ℝ) ^ δ₀ := by
    intro N z _
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [hφhdef, Nat.cast_zero, _root_.inv_zero, min_eq_right zero_le_one]
      rw [Real.zero_rpow hδ₀.ne']; exact ⟨le_rfl, le_rfl⟩
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      simp only [hφhdef, min_eq_left hN1]
      exact ⟨inv_le_one_of_one_le₀ hN1, Real.one_le_rpow hN1 hδ₀.le⟩
  have hLL : aprioriLL D μ A Zf φh := by
    apply LL_to_apriori
    refine LL_Sup_le (LL_of_apriori (LL_apriori_top hs Zf hZf2)) ⟨1, fun N hN z _ => ?_⟩
    simp [hφhdef, min_eq_left (show (1 : ℝ) ≤ N by exact_mod_cast hN)]
  obtain ⟨net1, net2⟩ := hKn D δA (1 / 4) δ₀ C θ μ A hs (by norm_num) hδ₀.le hKnδ Zf hZf φh hφh
    hLL (5 / 2) (by norm_num)
  have avg := hKa D δA (1 / 4) δ₀ C θ μ A hs (by norm_num) hδ₀.le hKaδ Zf hZf φh hφh hLL
  obtain ⟨NΛ₀, hNΛ₀⟩ := LL_lam_small hs
  set Z := τ⁻¹ with hZdef
  have hZ0 : 0 < Z := inv_pos.mpr hτ
  -- the controls on `Zf` for `N ≥ max(N_Λ, 1)`
  set Ca := (1 + Z) ^ (2 * Ka) * 64 * 4 with hCadef
  set Ci := (1 + Z) ^ Kn * 8 * 2 with hCidef
  set Cn := (1 + Z) ^ (2 * Kn) * 64 * 4 with hCndef
  have hctl : ∀ N : ℕ, NΛ₀ ≤ N → 1 ≤ N → ∀ z ∈ Zf N,
      (1 + ‖z‖) ^ (2 * Ka) * (1 + φh N z) ^ 6 * psiPhi (lam D N (A N)) N z (φh N z) ^ 2 ≤
        Ca / N ∧
      (1 + ‖z‖) ^ Kn * (1 + φh N z) ^ 3 * psiPhi (lam D N (A N)) N z (φh N z) ≤
        Ci / Real.sqrt N ∧
      (1 + ‖z‖) ^ (2 * Kn) * (1 + φh N z) ^ 6 * psiPhi (lam D N (A N)) N z (φh N z) ^ 2 ≤
        Cn / N := by
    intro N hNΛ hN1 z hz
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNr0 : (0 : ℝ) < N := by linarith
    have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1⟩)⟩
    have hφ1 : φh N z = 1 := by simp [hφhdef, min_eq_left hNr1]
    have hz2 := hZf2 N z hz
    have hz0 : 0 < z.im := by linarith
    obtain ⟨hm0, hm1⟩ := LL_imm_bounds _ (lam_isHermitian D N (A N)) (hNΛ₀ N hNΛ) z hz0
    have hΨ := LL_psi1_le (lam D N (A N)) N hN1 z hz2 hm1
    have hΨ0 : 0 ≤ psiPhi (lam D N (A N)) N z 1 := by unfold psiPhi; positivity
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr0
    have hΨ2 : psiPhi (lam D N (A N)) N z 1 ^ 2 ≤ 4 / N := by
      calc psiPhi (lam D N (A N)) N z 1 ^ 2 ≤ (2 / Real.sqrt N) ^ 2 :=
            pow_le_pow_left₀ hΨ0 hΨ 2
        _ = 4 / N := by rw [div_pow, Real.sq_sqrt hNr0.le]; norm_num
    have hzn : ‖z‖ ≤ Z := hz.1.1.1
    have hb : ∀ p : ℝ, 0 ≤ p → (1 + ‖z‖) ^ p ≤ (1 + Z) ^ p := fun p hp =>
      Real.rpow_le_rpow (by positivity) (by linarith) hp
    have hb0 : ∀ p : ℝ, 0 ≤ (1 + Z) ^ p := fun p => Real.rpow_nonneg (by linarith) p
    rw [hφ1]
    norm_num only
    refine ⟨?_, ?_, ?_⟩
    · calc (1 + ‖z‖) ^ (2 * Ka) * 64 * psiPhi (lam D N (A N)) N z 1 ^ 2
          ≤ (1 + Z) ^ (2 * Ka) * 64 * (4 / N) := by
            gcongr
        _ = Ca / N := by rw [hCadef]; ring
    · calc (1 + ‖z‖) ^ Kn * 8 * psiPhi (lam D N (A N)) N z 1
          ≤ (1 + Z) ^ Kn * 8 * (2 / Real.sqrt N) := by
            gcongr
        _ = Ci / Real.sqrt N := by rw [hCidef]; ring
    · calc (1 + ‖z‖) ^ (2 * Kn) * 64 * psiPhi (lam D N (A N)) N z 1 ^ 2
          ≤ (1 + Z) ^ (2 * Kn) * 64 * (4 / N) := by
            gcongr
        _ = Cn / N := by rw [hCndef]; ring
  have hCa0 : 0 ≤ Ca := by positivity
  have hCi0 : 0 ≤ Ci := by positivity
  have hCn0 : 0 ≤ Cn := by positivity
  have hnull : ∀ N, μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := fun N =>
    ae_iff.mp (hs.mem N).herm
  -- the block traces on `Zf`: `|x| ≺ (4/3) D Ca / N`
  set Cb := 4 / 3 * D * Ca with hCbdef
  have hCb0 : 0 ≤ Cb := by positivity
  have blk : LL_Sup μ Zf (LL_xb D A) (fun N _ => Cb / N) := by
    intro τ' hτ' D' hD'
    obtain ⟨N₀, hN₀⟩ := avg τ' hτ' (D' + 1) (by linarith)
    refine ⟨max (max N₀ NΛ₀) (max D 1), fun N hN z hz _ => ?_⟩
    have hN0 : N₀ ≤ N := le_trans (by simp) hN
    have hNΛ : NΛ₀ ≤ N := le_trans (by simp) hN
    have hND : D ≤ N := le_trans (by simp) hN
    have hN1 : 1 ≤ N := le_trans (by simp) hN
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNr0 : (0 : ℝ) < N := by linarith
    have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1⟩)⟩
    have hz2 := hZf2 N z hz
    have hz0 : 0 < z.im := by linarith
    have hΛh := lam_isHermitian D N (A N)
    have hBa : ∀ a : Fin D, opNorm (Ea D N a * MExt (lam D N (A N)) z) ≤ 1 := by
      intro a
      have hM := (LL_M_inv _ hΛh z hz0).2
      have h1 : z.im⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      exact (LL_opNorm_mul_le (LL_opNorm_Ea D N a) (hM.trans h1)).trans (by norm_num)
    set ev : Fin D → Set (Idx D N → Idx D N → ℂ) := fun a =>
      {h | (N : ℝ) ^ τ' * ((1 + ‖z‖) ^ (2 * Ka) * (1 + φh N z) ^ 6 *
        psiPhi (lam D N (A N)) N z (φh N z) ^ 2) <
        ‖ntr (Ea D N a * MExt (lam D N (A N)) z *
          hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z)‖} with hev
    have hevμ : ∀ a, μ N (ev a) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) :=
      fun a => hN₀ N hN0 (⟨z, hz⟩, ⟨_, hBa a⟩)
    have hc := (hctl N hNΛ hN1 z hz).1
    have hsub : {h | (N : ℝ) ^ τ' * (Cb / N) < LL_xb D A N z () h} ⊆
        (⋃ a, ev a) ∪ {h | ¬ (Matrix.of h).IsHermitian} := by
      intro h hh
      by_contra hcon
      simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_ofPred_eq,
        not_not, hev] at hcon
      obtain ⟨hgood, hH⟩ := hcon
      have hcont := blockTr_contraction D N (θ N) (hs.theta N).1 (hs.theta N).2 (A N)
        (Matrix.of h) hH z hz2
      have hr : ‖rVec D N (θ N) (Matrix.of h) (lam D N (A N)) z‖ ≤
          D * ((N : ℝ) ^ τ' * (Ca / N)) := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
        have h1 := not_lt.mp (hgood a)
        have h2 : (N : ℝ) ^ τ' * ((1 + ‖z‖) ^ (2 * Ka) * (1 + φh N z) ^ 6 *
            psiPhi (lam D N (A N)) N z (φh N z) ^ 2) ≤ (N : ℝ) ^ τ' * (Ca / N) :=
          mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hNr0.le _)
        simp only [rVec, norm_neg, norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (h1.trans h2) (Nat.cast_nonneg _)
      simp only [Set.mem_ofPred_eq, LL_xb] at hh
      have : (N : ℝ) ^ τ' * (Cb / N) = 4 / 3 * (D * ((N : ℝ) ^ τ' * (Ca / N))) := by
        rw [hCbdef]; ring
      rw [this] at hh
      linarith
    calc μ N {h | (N : ℝ) ^ τ' * (Cb / N) < LL_xb D A N z () h}
        ≤ μ N ((⋃ a, ev a) ∪ {h | ¬ (Matrix.of h).IsHermitian}) := measure_mono hsub
      _ ≤ μ N (⋃ a, ev a) + μ N {h | ¬ (Matrix.of h).IsHermitian} := measure_union_le _ _
      _ ≤ (∑ a, μ N (ev a)) + 0 := by rw [hnull]; gcongr; exact measure_iUnion_fintype_le _ _
      _ ≤ ∑ _a : Fin D, ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := by
          rw [add_zero]; exact Finset.sum_le_sum fun a _ => hevμ a
      _ = (D : ENNReal) * ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := LL_k_le N D hN1 hND D'
  -- the isotropic entries and the averages on `Zf`
  have isoavg : LL_Sup μ Zf (LL_xi D A) (fun N _ => (25 / 8 * Cb + Ci) / Real.sqrt N) ∧
      LL_Sup μ Zf (LL_xa D A) (fun N _ => (25 / 8 * Cb + Cn) / N) := by
    have key : ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ z ∈ Zf N, (∀ w : LL_UV D N, μ N {h | (N : ℝ) ^ τ' *
          ((25 / 8 * Cb + Ci) / Real.sqrt N) < LL_xi D A N z w h} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D'))) ∧
          (∀ w : LL_Bs D N, μ N {h | (N : ℝ) ^ τ' * ((25 / 8 * Cb + Cn) / N) <
            LL_xa D A N z w h} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D'))) := by
      intro τ' hτ' D' hD'
      set τ'' := min τ' (1 / 2) with hτ''
      have hτ''0 : 0 < τ'' := lt_min hτ' (by norm_num)
      obtain ⟨N₀, hN₀⟩ := blk τ'' hτ''0 (D' + 1) (by linarith)
      obtain ⟨N₁, hN₁⟩ := net1 τ'' hτ''0 (D' + 1) (by linarith)
      obtain ⟨N₂, hN₂⟩ := net2 τ'' hτ''0 (D' + 1) (by linarith)
      obtain ⟨N₃, hN₃⟩ := LL_rpow_absorb (show τ'' + -1 < 0 by
        have := min_le_right τ' (1 / 2); linarith) (5 * Cb)
      refine ⟨max (max (max N₀ N₁) (max N₂ N₃)) (max NΛ₀ 2), fun N hN z hz => ?_⟩
      have hN0 : N₀ ≤ N := le_trans (by simp) hN
      have hN1' : N₁ ≤ N := le_trans (by simp) hN
      have hN2' : N₂ ≤ N := le_trans (by simp) hN
      have hN3 : N₃ ≤ N := le_trans (by simp) hN
      have hNΛ : NΛ₀ ≤ N := le_trans (by simp) hN
      have hN2 : 2 ≤ N := le_trans (by simp) hN
      have hN1 : 1 ≤ N := by omega
      have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      have hNr0 : (0 : ℝ) < N := by linarith
      have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1⟩)⟩
      have hz2 := hZf2 N z hz
      have hz0 : 0 < z.im := by linarith
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr0
      have hsN1 : Real.sqrt N ≤ N := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      have hNτ : (N : ℝ) ^ τ'' ≤ (N : ℝ) ^ τ' := LL_rpow_mono hNr1 (min_le_left _ _)
      have hNτ0 : 0 ≤ (N : ℝ) ^ τ'' := Real.rpow_nonneg hNr0.le _
      obtain ⟨hc1, hc2, hc3⟩ := hctl N hNΛ hN1 z hz
      -- `|x| ≤ N^{τ''} Cb/N ≤ 1/5` outside the block event
      have h5 : (N : ℝ) ^ τ'' * (Cb / N) ≤ 1 / 5 := by
        have h := hN₃ N hN3
        rw [Real.rpow_zero, Real.rpow_add hNr0, Real.rpow_neg_one] at h
        have e : (N : ℝ) ^ τ'' * (Cb / N) = Cb * ((N : ℝ) ^ τ'' * (N : ℝ)⁻¹) := by
          field_simp
        rw [e]; nlinarith
      have hBl := hN₀ N hN0 z hz ()
      refine ⟨fun w => ?_, fun w => ?_⟩
      · have hNe := hN₁ N hN1' (⟨z, hz⟩, w.1, w.2)
        have hsub : {h | (N : ℝ) ^ τ' * ((25 / 8 * Cb + Ci) / Real.sqrt N) < LL_xi D A N z w h} ⊆
            ({h | (N : ℝ) ^ τ'' * (Cb / N) < LL_xb D A N z () h} ∪
              {h | (N : ℝ) ^ τ'' * ((1 + ‖z‖) ^ Kn * (1 + φh N z) ^ 3 *
                psiPhi (lam D N (A N)) N z (φh N z)) <
                if opNorm (resX (lam D N (A N)) z (sigTheta D (θ N) *ᵥ
                    blockTr D N (res (Matrix.of h + lam D N (A N)) z))) ≤ 5 / 2 then
                  ‖star w.1.1 ⬝ᵥ ((resX (lam D N (A N)) z (sigTheta D (θ N) *ᵥ
                    blockTr D N (res (Matrix.of h + lam D N (A N)) z)) *
                      hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z) *ᵥ w.2.1)‖
                else 0}) ∪ {h | ¬ (Matrix.of h).IsHermitian} := by
          intro h hh
          by_contra hcon
          simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, not_lt, not_not] at hcon
          obtain ⟨⟨hb1, hb2⟩, hH⟩ := hcon
          simp only [LL_xb] at hb1
          have hdet := LL_iso_det D N hD1 hN1 (θ N) (hs.theta N).1 (hs.theta N).2 (A N)
            (hNΛ₀ N hNΛ) (Matrix.of h) hH z hz0 w.1.1 w.2.1 w.1.2 w.2.2 _ _ hb1 (hb1.trans h5)
            hb2
          have h6 : (N : ℝ) ^ τ'' * ((1 + ‖z‖) ^ Kn * (1 + φh N z) ^ 3 *
              psiPhi (lam D N (A N)) N z (φh N z)) ≤ (N : ℝ) ^ τ'' * (Ci / Real.sqrt N) :=
            mul_le_mul_of_nonneg_left hc2 hNτ0
          have h7 : Cb / N ≤ Cb / Real.sqrt N := div_le_div_of_nonneg_left hCb0 hsN hsN1
          have h8 : 0 ≤ (25 / 8 * Cb + Ci) / Real.sqrt N := by positivity
          have h9 : (N : ℝ) ^ τ'' * ((25 / 8 * Cb + Ci) / Real.sqrt N) ≤
              (N : ℝ) ^ τ' * ((25 / 8 * Cb + Ci) / Real.sqrt N) :=
            mul_le_mul_of_nonneg_right hNτ h8
          have e : (N : ℝ) ^ τ'' * ((25 / 8 * Cb + Ci) / Real.sqrt N) =
              25 / 8 * ((N : ℝ) ^ τ'' * (Cb / Real.sqrt N)) +
                (N : ℝ) ^ τ'' * (Ci / Real.sqrt N) := by ring
          have h10 := mul_le_mul_of_nonneg_left h7 hNτ0
          simp only [Set.mem_ofPred_eq, LL_xi] at hh
          linarith
        calc _ ≤ _ := measure_mono hsub
          _ ≤ μ N ({h | (N : ℝ) ^ τ'' * (Cb / N) < LL_xb D A N z () h} ∪ _) + 0 := by
              rw [← hnull N]; exact measure_union_le _ _
          _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := by
              rw [add_zero]; exact (measure_union_le _ _).trans (add_le_add hBl hNe)
          _ ≤ _ := LL_two_le N hN2 D'
      · have hNe := hN₂ N hN2' (⟨z, hz⟩, w)
        have hsub : {h | (N : ℝ) ^ τ' * ((25 / 8 * Cb + Cn) / N) < LL_xa D A N z w h} ⊆
            ({h | (N : ℝ) ^ τ'' * (Cb / N) < LL_xb D A N z () h} ∪
              {h | (N : ℝ) ^ τ'' * ((1 + ‖z‖) ^ (2 * Kn) * (1 + φh N z) ^ 6 *
                psiPhi (lam D N (A N)) N z (φh N z) ^ 2) <
                if opNorm (resX (lam D N (A N)) z (sigTheta D (θ N) *ᵥ
                    blockTr D N (res (Matrix.of h + lam D N (A N)) z))) ≤ 5 / 2 then
                  ‖ntr (w.1 * resX (lam D N (A N)) z (sigTheta D (θ N) *ᵥ
                    blockTr D N (res (Matrix.of h + lam D N (A N)) z)) *
                      hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z)‖
                else 0}) ∪ {h | ¬ (Matrix.of h).IsHermitian} := by
          intro h hh
          by_contra hcon
          simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, not_lt, not_not] at hcon
          obtain ⟨⟨hb1, hb2⟩, hH⟩ := hcon
          simp only [LL_xb] at hb1
          have hdet := LL_avg_det D N hD1 hN1 (θ N) (hs.theta N).1 (hs.theta N).2 (A N)
            (hNΛ₀ N hNΛ) (Matrix.of h) hH z hz0 w.1 w.2 _ _ hb1 (hb1.trans h5) hb2
          have h6 : (N : ℝ) ^ τ'' * ((1 + ‖z‖) ^ (2 * Kn) * (1 + φh N z) ^ 6 *
              psiPhi (lam D N (A N)) N z (φh N z) ^ 2) ≤ (N : ℝ) ^ τ'' * (Cn / N) :=
            mul_le_mul_of_nonneg_left hc3 hNτ0
          have h8 : 0 ≤ (25 / 8 * Cb + Cn) / N := by positivity
          have h9 : (N : ℝ) ^ τ'' * ((25 / 8 * Cb + Cn) / N) ≤
              (N : ℝ) ^ τ' * ((25 / 8 * Cb + Cn) / N) :=
            mul_le_mul_of_nonneg_right hNτ h8
          have e : (N : ℝ) ^ τ'' * ((25 / 8 * Cb + Cn) / N) =
              25 / 8 * ((N : ℝ) ^ τ'' * (Cb / N)) + (N : ℝ) ^ τ'' * (Cn / N) := by ring
          simp only [Set.mem_ofPred_eq, LL_xa] at hh
          linarith
        calc _ ≤ _ := measure_mono hsub
          _ ≤ μ N ({h | (N : ℝ) ^ τ'' * (Cb / N) < LL_xb D A N z () h} ∪ _) + 0 := by
              rw [← hnull N]; exact measure_union_le _ _
          _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := by
              rw [add_zero]; exact (measure_union_le _ _).trans (add_le_add hBl hNe)
          _ ≤ _ := LL_two_le N hN2 D'
    refine ⟨fun τ' hτ' D' hD' => ?_, fun τ' hτ' D' hD' => ?_⟩
    · obtain ⟨N₀, hN₀⟩ := key τ' hτ' D' hD'
      exact ⟨N₀, fun N hN z hz w => (hN₀ N hN z hz).1 w⟩
    · obtain ⟨N₀, hN₀⟩ := key τ' hτ' D' hD'
      exact ⟨N₀, fun N hN z hz w => (hN₀ N hN z hz).2 w⟩
  exact ⟨δ₀, hδ₀, Cb, 25 / 8 * Cb + Ci, 25 / 8 * Cb + Cn, hCb0, by positivity, by positivity,
    blk, isoavg.1, isoavg.2⟩

/-- The local laws on `𝐃(τ) ∩ {η ≥ 2}` in sup form: from `LL_high_Zf` and the lower bounds of
the controls `LL_high_lower`. -/
private lemma LL_high (D : ℕ) (δA : ℝ) (C θ : ℕ → ℝ) (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ))
    (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (hs : LLSeq D δA C θ μ A) (τ : ℝ) (hτ : 0 < τ) :
    LL_Sup μ (LL_Zhigh τ) (LL_xb D A) (LL_zB D A) ∧
      LL_Sup μ (LL_Zhigh τ) (LL_xi D A) (LL_zI D A) ∧
      LL_Sup μ (LL_Zhigh τ) (LL_xa D A) (fun N z => LL_zA N z) := by
  obtain ⟨δ₀, hδ₀, Cb, CI, CA, hCb0, hCI0, hCA0, blk, iso, avg⟩ :=
    LL_high_Zf D δA C θ μ A hs τ hτ
  have hD1 := hs.one_le_D
  obtain ⟨NΛ₀, hNΛ₀⟩ := LL_lam_small hs
  obtain ⟨Ce, hCe, hCeP⟩ := edge_close_to_edge_sc
  set cτ := 11 / 10 + τ⁻¹ with hcτdef
  have hcτ1 : 1 ≤ cτ := by have := inv_pos.mpr hτ; rw [hcτdef]; linarith
  set dmax := Real.sqrt (2 * τ⁻¹ + 2 + Ce / 10) with hdmaxdef
  have hdmax0 : 0 ≤ dmax := Real.sqrt_nonneg _
  have hlow : ∀ N : ℕ, NΛ₀ ≤ N → 1 ≤ N → ∀ z ∈ LL_Zhigh τ N,
      1 / (cτ * Real.sqrt N) ≤ LL_zI D A N z ∧
      1 / (cτ ^ 2 * (dmax + 1) * N) ≤ LL_zB D A N z ∧
      τ / N ≤ LL_zA N z := fun N hNΛ hN1 z hz =>
    LL_high_lower D hD1 A τ hτ Ce hCe hCeP N hN1 (hNΛ₀ N hNΛ) z hz
  obtain ⟨N₄, hN₄⟩ := LL_rpow_large hδ₀ τ⁻¹
  have hdom : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → LL_Zhigh τ N ⊆ LL_Zf τ δ₀ N :=
    ⟨N₄, fun N hN z hz => ⟨hz, hz.1.1.trans (hN₄ N hN)⟩⟩
  -- assembling
  have hfin : ∀ (W : ℕ → Type) (ξ : ∀ N, ℂ → W N → (Idx D N → Idx D N → ℂ) → ℝ)
      (ζ₀ ζt : ℕ → ℂ → ℝ) (c : ℝ), LL_Sup μ (LL_Zf τ δ₀) ξ ζ₀ →
      (∀ N : ℕ, NΛ₀ ≤ N → 1 ≤ N → ∀ z ∈ LL_Zhigh τ N, ζ₀ N z ≤ c * ζt N z) →
      (∀ N : ℕ, NΛ₀ ≤ N → 1 ≤ N → ∀ z ∈ LL_Zhigh τ N, 0 ≤ ζt N z) →
      LL_Sup μ (LL_Zhigh τ) ξ ζt := by
    intro W ξ ζ₀ ζt c h0 hle hnn
    refine LL_Sup_fam fun ε hε => ⟨ζ₀, LL_Sup_sub h0 hdom, ?_⟩
    obtain ⟨N₅, hN₅⟩ := LL_rpow_large hε c
    refine ⟨max (max N₅ NΛ₀) 1, fun N hN z hz => ?_⟩
    have hNΛ : NΛ₀ ≤ N := le_trans (by simp) hN
    have hN1 : 1 ≤ N := le_trans (by simp) hN
    exact (hle N hNΛ hN1 z hz).trans (mul_le_mul_of_nonneg_right
      (hN₅ N (le_trans (by simp) hN)) (hnn N hNΛ hN1 z hz))
  refine ⟨?_, ?_, ?_⟩
  · refine hfin (fun _ => Unit) (LL_xb D A) _ (LL_zB D A) (Cb * (cτ ^ 2 * (dmax + 1))) blk
      (fun N hNΛ hN1 z hz => ?_) (fun N hNΛ hN1 z hz => ?_)
    · have h := (hlow N hNΛ hN1 z hz).2.1
      have hNr0 : (0 : ℝ) < N := by exact_mod_cast hN1
      have e : Cb / N = Cb * (cτ ^ 2 * (dmax + 1)) * (1 / (cτ ^ 2 * (dmax + 1) * N)) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    · have h := (hlow N hNΛ hN1 z hz).2.1
      have hNr0 : (0 : ℝ) < N := by exact_mod_cast hN1
      exact le_trans (by positivity) h
  · refine hfin (LL_UV D) (LL_xi D A) _ (LL_zI D A) (CI * cτ) iso
      (fun N hNΛ hN1 z hz => ?_) (fun N hNΛ hN1 z hz => ?_)
    · have h := (hlow N hNΛ hN1 z hz).1
      have hNr0 : (0 : ℝ) < N := by exact_mod_cast hN1
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr0
      have e : CI / Real.sqrt N =
          CI * cτ * (1 / (cτ * Real.sqrt N)) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    · unfold LL_zI psiIso; positivity
  · refine hfin (LL_Bs D) (LL_xa D A) _ (fun N z => LL_zA N z) (CA / τ)
      avg (fun N hNΛ hN1 z hz => ?_) (fun N hNΛ hN1 z hz => ?_)
    · have h := (hlow N hNΛ hN1 z hz).2.2
      have hNr0 : (0 : ℝ) < N := by exact_mod_cast hN1
      have e : CA / N = CA / τ * (τ / N) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    · unfold LL_zA; positivity

/-! ### The union over `z` (row R3) -/

/-- The net argument with uniformity in the deterministic parameter: a sup-form bound on `S_N`
for a quantity that is `N³`-Lipschitz in `z` on Hermitian arrays, with an `N³`-Lipschitz control
`ζ ≥ N^{-3}` on `S_N ⊆ {|z| ≤ N}`, holds in union form over `z ∈ S_N` with `N₀` uniform in the
parameter `w`. -/
private lemma LL_net {D : ℕ} (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ))
    (hnull : ∀ N, μ N {h | ¬ (Matrix.of h).IsHermitian} = 0) {W : ℕ → Type} (S : ℕ → Set ℂ)
    (q : ∀ N, ℂ → W N → (Idx D N → Idx D N → ℂ) → ℝ) (ζ : ℕ → ℂ → ℝ)
    (hS : ∀ N, 1 ≤ N → S N ⊆ Metric.closedBall 0 ((N : ℝ) ^ (1 : ℝ)))
    (hLq : ∀ N, 1 ≤ N → ∀ w h, (Matrix.of h).IsHermitian → ∀ u ∈ S N, ∀ v ∈ S N,
      |q N u w h - q N v w h| ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖)
    (hLζ : ∀ N, 1 ≤ N → ∀ u ∈ S N, ∀ v ∈ S N, |ζ N u - ζ N v| ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖)
    (hζ : ∀ N, 1 ≤ N → ∀ u ∈ S N, (N : ℝ) ^ (-(3 : ℝ)) ≤ ζ N u)
    (hsup : LL_Sup μ S q ζ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ w : W N,
      μ N {h | ∃ z ∈ S N, (N : ℝ) ^ τ' * ζ N z < q N z w h} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  by_contra hcon
  push Not at hcon
  -- a bad parameter at every size where there is one
  set c : ∀ N, Option (W N) := fun N =>
    if hN : ∃ w : W N, ENNReal.ofReal ((N : ℝ) ^ (-D')) <
        μ N {h | ∃ z ∈ S N, (N : ℝ) ^ τ' * ζ N z < q N z w h} then some (Classical.choose hN)
    else none with hc
  set ξ : ∀ N, ℂ → (Idx D N → Idx D N → ℂ) → ℝ := fun N z h =>
    (c N).elim 0 fun w => if (Matrix.of h).IsHermitian then q N z w h else 0 with hξ
  have hζpos : ∀ N, 1 ≤ N → ∀ u ∈ S N, 0 < ζ N u := fun N hN u hu =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) (hζ N hN u hu)
  have hLξ : ∀ N ω, 1 ≤ N → ∀ u ∈ S N, ∀ v ∈ S N,
      |ξ N u ω - ξ N v ω| ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖ := by
    intro N ω hN u hu v hv
    have h0 : 0 ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖ := by positivity
    simp only [hξ]
    rcases c N with _ | w
    · simpa using h0
    · by_cases hH : (Matrix.of ω).IsHermitian
      · simpa [hH] using hLq N hN w ω hH u hu v hv
      · simpa [hH] using h0
  have hPS : PrecS μ (fun N (u : S N) => ξ N u) fun N (u : S N) _ => ζ N u := by
    intro τ hτ D'' hD''
    obtain ⟨N₀, hN₀⟩ := hsup τ hτ D'' hD''
    refine ⟨max N₀ 1, fun N hN u => ?_⟩
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hu0 := hζpos N hN1 u.1 u.2
    have hNτ : 0 < (N : ℝ) ^ τ := Real.rpow_pos_of_pos (by exact_mod_cast hN1) _
    simp only [hξ]
    rcases c N with _ | w
    · simp only [Option.elim_none]
      have : {ω : Idx D N → Idx D N → ℂ | (N : ℝ) ^ τ * ζ N u < 0} = ∅ := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        positivity
      rw [this, measure_empty]
      exact bot_le
    · refine le_trans (measure_mono ?_) (hN₀ N (le_of_max_le_left hN) u.1 u.2 w)
      intro ω hω
      simp only [Option.elim_some, Set.mem_ofPred_eq] at hω ⊢
      by_cases hH : (Matrix.of ω).IsHermitian
      · simpa [hH] using hω
      · simp only [hH, ↓reduceIte] at hω
        exact absurd hω (not_lt.mpr (by positivity))
  have hPU := precS_precU_net μ S 1 3 3 hS ξ (fun N z _ => ζ N z) hLξ
    (fun N _ hN u hu v hv => hLζ N hN u hu v hv) (fun N _ hN u hu => hζ N hN u hu) hPS
  obtain ⟨N₀, hN₀⟩ := hPU τ' hτ' D' hD'
  obtain ⟨N, hN, w, hw⟩ := hcon N₀
  have hex : ∃ w : W N, ENNReal.ofReal ((N : ℝ) ^ (-D')) <
      μ N {h | ∃ z ∈ S N, (N : ℝ) ^ τ' * ζ N z < q N z w h} := ⟨w, hw⟩
  set w' := Classical.choose hex with hw'
  have hbad := Classical.choose_spec hex
  have hcN : c N = some w' := by simp only [hc, hex, ↓reduceDIte]; rfl
  have hsub : {h | ∃ z ∈ S N, (N : ℝ) ^ τ' * ζ N z < q N z w' h} ⊆
      {ω | ∃ u : S N, (N : ℝ) ^ τ' * ζ N u < ξ N u ω} ∪ {h | ¬ (Matrix.of h).IsHermitian} := by
    intro h ⟨z, hz, hlt⟩
    by_cases hH : (Matrix.of h).IsHermitian
    · left
      refine ⟨⟨z, hz⟩, ?_⟩
      simp only [hξ, hcN, Option.elim_some, hH, ↓reduceIte]
      exact hlt
    · right; exact hH
  have hfin : μ N {h | ∃ z ∈ S N, (N : ℝ) ^ τ' * ζ N z < q N z w' h} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
    calc μ N {h | ∃ z ∈ S N, (N : ℝ) ^ τ' * ζ N z < q N z w' h}
        ≤ μ N ({ω | ∃ u : S N, (N : ℝ) ^ τ' * ζ N u < ξ N u ω} ∪
          {h | ¬ (Matrix.of h).IsHermitian}) := measure_mono hsub
      _ ≤ μ N {ω | ∃ u : S N, (N : ℝ) ^ τ' * ζ N u < ξ N u ω} +
          μ N {h | ¬ (Matrix.of h).IsHermitian} := measure_union_le _ _
      _ = μ N {ω | ∃ u : S N, (N : ℝ) ^ τ' * ζ N u < ξ N u ω} := by rw [hnull N, add_zero]
      _ ≤ _ := hN₀ N hN
  exact absurd hbad (not_lt.mpr hfin)

/-- `‖(G - M)(u) - (G - M)(v)‖ ≤ N³ |u - v|` on `{Im ≥ N^{-1+τ}}` for Hermitian arrays, `N ≥ 3`,
`‖Λ‖ ≤ 1/10`, `τ ≥ 0` (from `opNorm_res_sub_le` and `MSol_lipschitz`). -/
private lemma LL_X_lip (D N : ℕ) (hD : 1 ≤ D) (hN : 3 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hΛ : opNorm (lam D N A) ≤ 1 / 10) (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian)
    (τ : ℝ) (hτ : 0 ≤ τ) (u v : ℂ) (hu : (N : ℝ) ^ (-1 + τ) ≤ u.im)
    (hv : (N : ℝ) ^ (-1 + τ) ≤ v.im) :
    opNorm ((res (H + lam D N A) u - MExt (lam D N A) u) -
      (res (H + lam D N A) v - MExt (lam D N A) v)) ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖ := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, by omega⟩)⟩
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < N := by linarith
  have hΛh := lam_isHermitian D N A
  set η₀ := (N : ℝ) ^ (-1 + τ) with hη₀
  have hη₀0 : 0 < η₀ := Real.rpow_pos_of_pos hNr0 _
  have hη₀N : (N : ℝ)⁻¹ ≤ η₀ := by
    rw [← Real.rpow_neg_one]; exact LL_rpow_mono (by linarith) (by linarith)
  have hinv : η₀⁻¹ ≤ N := by
    rw [inv_le_comm₀ hη₀0 hNr0]; exact hη₀N
  have hu0 : 0 < u.im := lt_of_lt_of_le hη₀0 hu
  have hv0 : 0 < v.im := lt_of_lt_of_le hη₀0 hv
  have hG := opNorm_res_sub_le (H + lam D N A) (hH.add hΛh) u v hu0 hv0
  have hM := (MSol_lipschitz (lam D N A) hΛh hΛ η₀ hη₀0 u v hu hv).2
  rw [← (LL_MExt_eq _ u hu0).2, ← (LL_MExt_eq _ v hv0).2] at hM
  have e : (res (H + lam D N A) u - MExt (lam D N A) u) -
      (res (H + lam D N A) v - MExt (lam D N A) v) =
      (res (H + lam D N A) u - res (H + lam D N A) v) -
        (MExt (lam D N A) u - MExt (lam D N A) v) := by abel
  rw [e]
  refine (LL_opNorm_sub_le _ _).trans ?_
  have hd : ‖u - v‖ / (u.im * v.im) ≤ (N : ℝ) ^ 2 * ‖u - v‖ := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ (N : ℝ) * u.im := by
      have := mul_le_mul_of_nonneg_left (hη₀N.trans hu) hNr0.le
      rwa [mul_inv_cancel₀ hNr0.ne'] at this
    have h2 : 1 ≤ (N : ℝ) * v.im := by
      have := mul_le_mul_of_nonneg_left (hη₀N.trans hv) hNr0.le
      rwa [mul_inv_cancel₀ hNr0.ne'] at this
    have h3 : 1 ≤ ((N : ℝ) * u.im) * ((N : ℝ) * v.im) := by nlinarith
    have h4 : 0 ≤ ‖u - v‖ := norm_nonneg _
    nlinarith
  have hm : 25 / 16 * (1 + η₀⁻¹) * ‖u - v‖ ≤ 25 / 16 * (1 + N) * ‖u - v‖ := by
    gcongr
  have h3 : (N : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3]
  have h4 : 0 ≤ ‖u - v‖ := norm_nonneg _
  have h5 : (N : ℝ) ^ 2 + 25 / 16 * (1 + N) ≤ (N : ℝ) ^ 3 := by nlinarith
  nlinarith

/-- The block traces, isotropic entries and averages are `N³`-Lipschitz in `z`. -/
private lemma LL_q_lip (D N : ℕ) (hD : 1 ≤ D) (hN : 3 ≤ N) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hΛ : opNorm (lam D N (A N)) ≤ 1 / 10) (h : Idx D N → Idx D N → ℂ)
    (hH : (Matrix.of h).IsHermitian) (τ : ℝ) (hτ : 0 ≤ τ) (u v : ℂ)
    (hu : (N : ℝ) ^ (-1 + τ) ≤ u.im) (hv : (N : ℝ) ^ (-1 + τ) ≤ v.im) :
    |LL_xb D A N u () h - LL_xb D A N v () h| ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖ ∧
      (∀ w : LL_UV D N, |LL_xi D A N u w h - LL_xi D A N v w h| ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖) ∧
      (∀ w : LL_Bs D N, |LL_xa D A N u w h - LL_xa D A N v w h| ≤
        (N : ℝ) ^ (3 : ℝ) * ‖u - v‖) := by
  have hX := LL_X_lip D N hD hN (A N) hΛ (Matrix.of h) hH τ hτ u v hu hv
  set Xu := res (Matrix.of h + lam D N (A N)) u - MExt (lam D N (A N)) u
  set Xv := res (Matrix.of h + lam D N (A N)) v - MExt (lam D N (A N)) v
  refine ⟨?_, fun w => ?_, fun w => ?_⟩
  · simp only [LL_xb]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← LL_blockTr_sub]
    exact (blockTr_norm_le D N _).trans hX
  · simp only [LL_xi]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← dotProduct_sub, ← Matrix.sub_mulVec]
    exact (LL_form_le _ _ _ w.1.2.le w.2.2.le).trans hX
  · simp only [LL_xa]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← LL_ntr_sub, ← Matrix.sub_mul]
    exact (LL_ntr_le _).trans ((LL_opNorm_mul_le hX w.2).trans (by rw [mul_one]))

/-- `|√a - √b| ≤ (s/2) |a - b|` when `√a, √b ≥ 1/s`. -/
private lemma LL_sqrt_lip (a b s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s)
    (hsa : 1 / s ≤ Real.sqrt a) (hsb : 1 / s ≤ Real.sqrt b) :
    |Real.sqrt a - Real.sqrt b| ≤ s / 2 * |a - b| := by
  have hsum : 2 / s ≤ Real.sqrt a + Real.sqrt b := by
    have : 2 / s = 1 / s + 1 / s := by ring
    linarith
  have hpos : 0 < Real.sqrt a + Real.sqrt b := lt_of_lt_of_le (by positivity) hsum
  have e : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
    have h1 := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt hb
    nlinarith
  have h1 : |a - b| = |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) := by
    rw [e, abs_mul, abs_of_pos hpos]
  rw [h1]
  have h2 : 0 ≤ |Real.sqrt a - Real.sqrt b| := abs_nonneg _
  have h3 : s / 2 * (2 / s) = 1 := by field_simp
  have h4 : 1 ≤ s / 2 * (Real.sqrt a + Real.sqrt b) := by
    have := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ s / 2)
    linarith
  calc |Real.sqrt a - Real.sqrt b| = |Real.sqrt a - Real.sqrt b| * 1 := (mul_one _).symm
    _ ≤ |Real.sqrt a - Real.sqrt b| * (s / 2 * (Real.sqrt a + Real.sqrt b)) :=
        mul_le_mul_of_nonneg_left h4 h2
    _ = s / 2 * (|Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b)) := by ring

/-- `|p²/d - p'²/d'| ≤ 4 s L₁ + 4 s² L₂` for `0 ≤ p, p' ≤ 2`, `|p - p'| ≤ L₁`, `d, d' ≥ 1/s` and
`|d - d'| ≤ L₂`. -/
private lemma LL_ratio_lip (p p' d d' s L₁ L₂ : ℝ) (hp0 : 0 ≤ p) (hp2 : p ≤ 2) (hp0' : 0 ≤ p')
    (hp2' : p' ≤ 2) (hs : 0 < s) (hd : 1 / s ≤ d) (hd' : 1 / s ≤ d') (hL₁ : |p - p'| ≤ L₁)
    (hL₂ : |d - d'| ≤ L₂) :
    |p ^ 2 / d - p' ^ 2 / d'| ≤ 4 * s * L₁ + 4 * s ^ 2 * L₂ := by
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hd0' : 0 < d' := lt_of_lt_of_le (by positivity) hd'
  have hid : 1 / d ≤ s := by rw [div_le_iff₀ hd0]; rw [div_le_iff₀ hs] at hd; linarith
  have hid' : 1 / d' ≤ s := by rw [div_le_iff₀ hd0']; rw [div_le_iff₀ hs] at hd'; linarith
  have e : p ^ 2 / d - p' ^ 2 / d' = (p - p') * (p + p') * (1 / d) +
      p' ^ 2 * (d' - d) * (1 / d) * (1 / d') := by
    field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have hi0 : 0 < 1 / d := one_div_pos.mpr hd0
  have hi0' : 0 < 1 / d' := one_div_pos.mpr hd0'
  have hL10 : 0 ≤ L₁ := (abs_nonneg _).trans hL₁
  have hL20 : 0 ≤ L₂ := (abs_nonneg _).trans hL₂
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ p + p'),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ p' ^ 2), abs_of_pos hi0, abs_of_pos hi0',
    abs_sub_comm d' d]
  have h1 : |p - p'| * (p + p') * (1 / d) ≤ L₁ * 4 * s :=
    mul_le_mul (mul_le_mul hL₁ (by linarith) (by positivity) hL10) hid hi0.le
      (by positivity)
  have h2 : p' ^ 2 * |d - d'| * (1 / d) * (1 / d') ≤ 4 * L₂ * s * s := by
    have hp4 : p' ^ 2 ≤ 4 := by nlinarith
    refine mul_le_mul (mul_le_mul (mul_le_mul hp4 hL₂ (abs_nonneg _) (by norm_num)) hid
      hi0.le (by positivity)) hid' hi0'.le (by positivity)
  have e1 : L₁ * 4 * s = 4 * s * L₁ := by ring
  have e2 : 4 * L₂ * s * s = 4 * s ^ 2 * L₂ := by ring
  linarith

/-- The controls `Ψ`, `1/(N|η|)` and `min(Ψ²/√(κ + |η|), Ψ)` are `N³`-Lipschitz on
`𝐃(τ) ∩ {η > 0}` for `N ≥ 12`, `‖Λ‖ ≤ 1/10`, `τ ≥ 0`. -/
private lemma LL_zeta_lip (D N : ℕ) (hD : 1 ≤ D) (hN : 12 ≤ N) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hΛ : opNorm (lam D N (A N)) ≤ 1 / 10) (τ : ℝ) (hτ : 0 ≤ τ) (u v : ℂ)
    (hu : (N : ℝ) ^ (-1 + τ) ≤ u.im) (hv : (N : ℝ) ^ (-1 + τ) ≤ v.im) :
    |LL_zI D A N u - LL_zI D A N v| ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖ ∧
      |LL_zA N u - LL_zA N v| ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖ ∧
      |LL_zB D A N u - LL_zB D A N v| ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖ := by
  have hN1 : 1 ≤ N := by omega
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN1⟩)⟩
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < N := by linarith
  have hΛh := lam_isHermitian D N (A N)
  have hη₀N : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-1 + τ) := by
    rw [← Real.rpow_neg_one]; exact LL_rpow_mono (by linarith) (by linarith)
  have hu1 : (N : ℝ)⁻¹ ≤ u.im := hη₀N.trans hu
  have hv1 : (N : ℝ)⁻¹ ≤ v.im := hη₀N.trans hv
  have hu0 : 0 < u.im := lt_of_lt_of_le (by positivity) hu1
  have hv0 : 0 < v.im := lt_of_lt_of_le (by positivity) hv1
  have h3 : (N : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3]
  have hn : 0 ≤ ‖u - v‖ := norm_nonneg _
  have hre : |u.re - v.re| ≤ ‖u - v‖ := by
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have him : |u.im - v.im| ≤ ‖u - v‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  have hNu : 1 ≤ (N : ℝ) * u.im := by
    have := mul_le_mul_of_nonneg_left hu1 hNr0.le
    rwa [mul_inv_cancel₀ hNr0.ne'] at this
  have hNv : 1 ≤ (N : ℝ) * v.im := by
    have := mul_le_mul_of_nonneg_left hv1 hNr0.le
    rwa [mul_inv_cancel₀ hNr0.ne'] at this
  -- `Ψ`
  have hI : |LL_zI D A N u - LL_zI D A N v| ≤ 2 * N * ‖u - v‖ :=
    psiIso_lipschitz (lam D N (A N)) hΛh N hN1 u v hu1 hv1
  -- `1/(N|η|)`
  have hA : |LL_zA N u - LL_zA N v| ≤ N * ‖u - v‖ := by
    simp only [LL_zA, abs_of_pos hu0, abs_of_pos hv0]
    rw [div_sub_div _ _ (by positivity) (by positivity), abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) * u.im * ((N : ℝ) * v.im)),
      div_le_iff₀ (by positivity)]
    have e : 1 * ((N : ℝ) * v.im) - (N : ℝ) * u.im * 1 = N * (v.im - u.im) := by ring
    rw [e, abs_mul, abs_of_pos hNr0, abs_sub_comm]
    have h0 : 1 ≤ (N : ℝ) * u.im * ((N : ℝ) * v.im) := by nlinarith only [hNu, hNv]
    have h1 : (N : ℝ) * ‖u - v‖ * 1 ≤ N * ‖u - v‖ * ((N : ℝ) * u.im * ((N : ℝ) * v.im)) :=
      mul_le_mul_of_nonneg_left h0 (by positivity)
    have h2 : (N : ℝ) * |u.im - v.im| ≤ N * ‖u - v‖ := mul_le_mul_of_nonneg_left him hNr0.le
    linarith
  -- the bounds `Ψ ≤ 2`, `d ≥ N^{-1/2}`
  have hΨle : ∀ w : ℂ, 0 < w.im → (N : ℝ)⁻¹ ≤ w.im →
      0 ≤ psiIso (lam D N (A N)) N w ∧ psiIso (lam D N (A N)) N w ≤ 2 := by
    intro w hw0 hw1
    have hNw : 1 ≤ (N : ℝ) * w.im := by
      have := mul_le_mul_of_nonneg_left hw1 hNr0.le
      rwa [mul_inv_cancel₀ hNr0.ne'] at this
    obtain ⟨hm0, hm1⟩ := LL_imm_bounds _ hΛh hΛ w hw0
    refine ⟨by unfold psiIso; positivity, ?_⟩
    unfold psiIso
    rw [abs_of_pos hm0, abs_of_pos hw0]
    have h1 : (mExt (lam D N (A N)) w).im / ((N : ℝ) * w.im) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h2 : Real.sqrt ((mExt (lam D N (A N)) w).im / ((N : ℝ) * w.im)) ≤ 1 :=
      Real.sqrt_le_one.mpr h1
    have h3 : 1 / ((N : ℝ) * w.im) ≤ 1 := by rw [div_le_one (by positivity)]; exact hNw
    linarith
  set s := Real.sqrt N with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hNr0
  have hs2 : s ^ 2 = N := Real.sq_sqrt hNr0.le
  have hsN : s ≤ N := by nlinarith
  have hk : ∀ w : ℂ, 0 ≤ kappa (lam D N (A N)) w.re :=
    fun w => le_min (abs_nonneg _) (abs_nonneg _)
  have hdl : ∀ w : ℂ, 0 < w.im → (N : ℝ)⁻¹ ≤ w.im →
      1 / s ≤ Real.sqrt (kappa (lam D N (A N)) w.re + |w.im|) := by
    intro w hw0 hw1
    rw [abs_of_pos hw0]
    have : 1 / s = Real.sqrt ((N : ℝ)⁻¹) := by rw [Real.sqrt_inv, one_div]
    rw [this]
    exact Real.sqrt_le_sqrt (by linarith [hk w])
  have hkl : |kappa (lam D N (A N)) u.re - kappa (lam D N (A N)) v.re| ≤ |u.re - v.re| := by
    unfold kappa
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
    · refine (abs_abs_sub_abs_le_abs_sub _ _).trans (le_of_eq ?_)
      rw [abs_sub_comm]; ring_nf
    · refine (abs_abs_sub_abs_le_abs_sub _ _).trans (le_of_eq ?_)
      ring_nf
  have hdd : |Real.sqrt (kappa (lam D N (A N)) u.re + |u.im|) -
      Real.sqrt (kappa (lam D N (A N)) v.re + |v.im|)| ≤ s * ‖u - v‖ := by
    refine (LL_sqrt_lip _ _ s (by linarith [hk u, abs_nonneg u.im])
      (by linarith [hk v, abs_nonneg v.im]) hs0 (hdl u hu0 hu1)
      (hdl v hv0 hv1)).trans ?_
    rw [abs_of_pos hu0, abs_of_pos hv0]
    have : |kappa (lam D N (A N)) u.re + u.im - (kappa (lam D N (A N)) v.re + v.im)| ≤
        2 * ‖u - v‖ := by
      have e : kappa (lam D N (A N)) u.re + u.im - (kappa (lam D N (A N)) v.re + v.im) =
          (kappa (lam D N (A N)) u.re - kappa (lam D N (A N)) v.re) + (u.im - v.im) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      linarith
    calc s / 2 * |kappa (lam D N (A N)) u.re + u.im - (kappa (lam D N (A N)) v.re + v.im)|
        ≤ s / 2 * (2 * ‖u - v‖) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = s * ‖u - v‖ := by ring
  obtain ⟨hpu0, hpu2⟩ := hΨle u hu0 hu1
  obtain ⟨hpv0, hpv2⟩ := hΨle v hv0 hv1
  have hB : |LL_zB D A N u - LL_zB D A N v| ≤ 12 * (N : ℝ) ^ 2 * ‖u - v‖ := by
    unfold LL_zB
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
    · refine (LL_ratio_lip _ _ _ _ s (2 * N * ‖u - v‖) (s * ‖u - v‖) hpu0 hpu2 hpv0 hpv2 hs0
        (hdl u hu0 hu1) (hdl v hv0 hv1) hI hdd).trans ?_
      have hsN' : s * N ≤ (N : ℝ) ^ 2 := by
        calc s * N ≤ N * N := mul_le_mul_of_nonneg_right hsN hNr0.le
          _ = (N : ℝ) ^ 2 := by ring
      have h1 : 4 * s * (2 * N * ‖u - v‖) = 8 * (s * N) * ‖u - v‖ := by ring
      have h1' : 8 * (s * N) * ‖u - v‖ ≤ 8 * (N : ℝ) ^ 2 * ‖u - v‖ :=
        mul_le_mul_of_nonneg_right (by linarith) hn
      have h2 : 4 * s ^ 2 * (s * ‖u - v‖) = 4 * (s * N) * ‖u - v‖ := by rw [hs2]; ring
      have h2' : 4 * (s * N) * ‖u - v‖ ≤ 4 * (N : ℝ) ^ 2 * ‖u - v‖ :=
        mul_le_mul_of_nonneg_right (by linarith) hn
      linarith
    · refine hI.trans ?_
      have : 2 * (N : ℝ) ≤ 12 * (N : ℝ) ^ 2 := by nlinarith only [hNr]
      exact mul_le_mul_of_nonneg_right this hn
  have hNsq : (144 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hNr]
  have hc1 : 2 * (N : ℝ) ≤ (N : ℝ) ^ 3 := by
    calc 2 * (N : ℝ) ≤ N * 144 := by linarith
      _ ≤ N * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hNsq hNr0.le
      _ = (N : ℝ) ^ 3 := by ring
  have hc3 : 12 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by
    calc 12 * (N : ℝ) ^ 2 ≤ N * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hNr (by positivity)
      _ = (N : ℝ) ^ 3 := by ring
  refine ⟨hI.trans (mul_le_mul_of_nonneg_right hc1 hn), hA.trans (mul_le_mul_of_nonneg_right
    (by linarith) hn), hB.trans (mul_le_mul_of_nonneg_right hc3 hn)⟩

/-! ### The lower half plane and the union over `𝐃(τ)` -/

/-- `‖A^*‖ = ‖A‖`. -/
private lemma LL_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) A)

/-- `⟨A^*⟩ = conj ⟨A⟩`. -/
private lemma LL_ntr_conjTranspose {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    ntr Aᴴ = star (ntr A) := by
  simp [ntr, Matrix.trace_conjTranspose, star_mul']

/-- `G(z̄) - M(z̄) = (G(z) - M(z))^*` for Hermitian arrays and `Im z > 0`. -/
private lemma LL_conj_X (D N : ℕ) [Nonempty (Idx D N)] (A : Matrix (Fin N) (Fin N) ℂ)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    res (H + lam D N A) (star z) - MExt (lam D N A) (star z) =
      (res (H + lam D N A) z - MExt (lam D N A) z)ᴴ := by
  have hΛh := lam_isHermitian D N A
  have h1 := res_conj (H + lam D N A) (hH.add hΛh) z hz
  have h2 := (mExt_conj (lam D N A) hΛh z hz.ne').2
  rw [Matrix.conjTranspose_sub, ← h1, ← h2]
  rfl

/-- The block traces, isotropic entries and averages at `z̄` (Hermitian arrays, `Im z > 0`):
`|x(z̄)| ≤ |x(z)|`, `|s^*(G - M)(z̄)t| = |t^*(G - M)(z)s|`,
`|⟨(G - M)(z̄) B⟩| = |⟨(G - M)(z) B^*⟩|`. -/
private lemma LL_conj_q (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (h : Idx D N → Idx D N → ℂ) (hH : (Matrix.of h).IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    LL_xb D A N (star z) () h ≤ LL_xb D A N z () h ∧
      (∀ w : LL_UV D N, LL_xi D A N (star z) w h ≤ LL_xi D A N z (w.2, w.1) h) ∧
      (∀ w : LL_Bs D N, LL_xa D A N (star z) w h ≤
        LL_xa D A N z ⟨w.1ᴴ, by rw [LL_opNorm_conjTranspose]; exact w.2⟩ h) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hX := LL_conj_X D N (A N) (Matrix.of h) hH z hz
  set Y := res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z with hY
  refine ⟨?_, fun w => ?_, fun w => ?_⟩
  · simp only [LL_xb]
    rw [hX]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun a => ?_
    have hE : (Ea D N a)ᴴ = Ea D N a := by
      unfold Ea
      rw [Matrix.diagonal_conjTranspose]
      congr 1
      funext p
      by_cases hp : p.1 = a <;> simp [hp]
    have e : blockTr D N Yᴴ a = star (blockTr D N Y a) := by
      simp only [blockTr]
      rw [star_mul', ← LL_ntr_conjTranspose, Matrix.conjTranspose_mul, hE, LL_ntr_comm]
      simp
    rw [e, norm_star]
    exact norm_le_pi_norm _ a
  · simp only [LL_xi]
    rw [hX, Matrix.star_dotProduct, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
      ← Matrix.dotProduct_mulVec, norm_star]
  · simp only [LL_xa]
    rw [hX]
    have e : ntr (Yᴴ * w.1) = star (ntr (Y * w.1ᴴ)) := by
      rw [← LL_ntr_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      exact LL_ntr_comm _ _
    rw [e, norm_star]

/-- The controls are even under `z ↦ z̄`. -/
private lemma LL_conj_zeta (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : z.im ≠ 0) :
    LL_zB D A N (star z) = LL_zB D A N z ∧ LL_zI D A N (star z) = LL_zI D A N z ∧
      LL_zA N (star z) = LL_zA N z := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hm := (mExt_conj (lam D N (A N)) (lam_isHermitian D N (A N)) z hz).1
  have hψ : psiIso (lam D N (A N)) N (star z) = psiIso (lam D N (A N)) N z := by
    unfold psiIso
    rw [hm]
    simp
  refine ⟨?_, hψ, ?_⟩
  · unfold LL_zB
    rw [hψ]
    simp
  · unfold LL_zA
    simp

/-- `κ_E ≤ Z + 2 + C_e/10` for `|E| ≤ Z`, with the constant `C_e` of `edge_close_to_edge_sc`. -/
private lemma LL_kappa_le (Ce : ℝ) (hCe : 0 < Ce)
    (hCeP : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → |2 - Eplus Λ| + |2 + Eminus Λ| ≤ Ce * opNorm Λ)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ) (hΛh : Λ.IsHermitian)
    (hΛ : opNorm Λ ≤ 1 / 10) (E Z : ℝ) (hE : |E| ≤ Z) : kappa Λ E ≤ Z + 2 + Ce / 10 := by
  have h1 : kappa Λ E ≤ |E - Eminus Λ| := min_le_right _ _
  have h2 := hCeP ι Λ hΛh hΛ
  have h3 : |2 + Eminus Λ| ≤ Ce / 10 := by
    have : Ce * opNorm Λ ≤ Ce * (1 / 10) := mul_le_mul_of_nonneg_left hΛ hCe.le
    linarith [abs_nonneg (2 - Eplus Λ)]
  have h5 := abs_sub E (Eminus Λ)
  have h6 : |Eminus Λ| ≤ 2 + Ce / 10 := by
    have := abs_sub (2 + Eminus Λ) 2
    simp only [add_sub_cancel_left] at this
    rw [abs_two] at this
    linarith
  linarith

/-- Lower bounds of the controls on `𝐃(τ) ∩ {η > 0}` (`N ≥ 1`, `‖Λ‖ ≤ 1/10`): `Ψ ≥ τ/N`,
`1/(N|η|) ≥ τ/N`, `min(Ψ²/√(κ + |η|), Ψ) ≥ τ²/(N² d)` with `d = √(2τ⁻¹ + 2 + C_e/10) + 1`. -/
private lemma LL_zeta_low (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hΛ : opNorm (lam D N (A N)) ≤ 1 / 10) (τ : ℝ) (hτ : 0 < τ) (Ce : ℝ) (hCe : 0 < Ce)
    (hCeP : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → |2 - Eplus Λ| + |2 + Eminus Λ| ≤ Ce * opNorm Λ)
    (z : ℂ) (hz : z ∈ specDom τ N) (hz0 : 0 < z.im) :
    τ / N ≤ LL_zI D A N z ∧ τ / N ≤ LL_zA N z ∧
      τ ^ 2 / ((N : ℝ) ^ 2 * (Real.sqrt (2 * τ⁻¹ + 2 + Ce / 10) + 1)) ≤ LL_zB D A N z := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hNr0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hΛh := lam_isHermitian D N (A N)
  obtain ⟨hzτ, hzη⟩ := hz
  have hzZ : z.im ≤ τ⁻¹ := (Complex.im_le_norm z).trans hzτ
  have hτz : τ * z.im ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hzZ hτ.le
    rwa [mul_inv_cancel₀ hτ.ne'] at this
  have hA : τ / N ≤ LL_zA N z := by
    unfold LL_zA
    rw [abs_of_pos hz0, div_le_div_iff₀ hNr0 (by positivity), one_mul]
    nlinarith
  have hI : τ / N ≤ LL_zI D A N z := by
    refine hA.trans ?_
    unfold LL_zI LL_zA psiIso
    linarith [Real.sqrt_nonneg (|(mExt (lam D N (A N)) z).im| / ((N : ℝ) * |z.im|))]
  refine ⟨hI, hA, ?_⟩
  set dm := Real.sqrt (2 * τ⁻¹ + 2 + Ce / 10) + 1 with hdm
  have hdm1 : 1 ≤ dm := by rw [hdm]; linarith [Real.sqrt_nonneg (2 * τ⁻¹ + 2 + Ce / 10)]
  have hk : 0 ≤ kappa (lam D N (A N)) z.re := le_min (abs_nonneg _) (abs_nonneg _)
  have hkle := LL_kappa_le Ce hCe hCeP _ hΛh hΛ z.re τ⁻¹ ((Complex.abs_re_le_norm z).trans hzτ)
  have hd : Real.sqrt (kappa (lam D N (A N)) z.re + |z.im|) ≤ dm := by
    rw [abs_of_pos hz0, hdm]
    have : Real.sqrt (kappa (lam D N (A N)) z.re + z.im) ≤ Real.sqrt (2 * τ⁻¹ + 2 + Ce / 10) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  have hd0 : 0 < Real.sqrt (kappa (lam D N (A N)) z.re + |z.im|) :=
    Real.sqrt_pos.mpr (by rw [abs_of_pos hz0]; linarith)
  have hτN : 0 < τ / N := by positivity
  unfold LL_zB
  refine le_min ?_ ?_
  · have h1 : (τ / N) ^ 2 ≤ psiIso (lam D N (A N)) N z ^ 2 := pow_le_pow_left₀ hτN.le hI 2
    rw [le_div_iff₀ hd0]
    calc τ ^ 2 / ((N : ℝ) ^ 2 * dm) * Real.sqrt (kappa (lam D N (A N)) z.re + |z.im|)
        ≤ τ ^ 2 / ((N : ℝ) ^ 2 * dm) * dm := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = (τ / N) ^ 2 := by field_simp
      _ ≤ _ := h1
  · refine le_trans ?_ hI
    have hzN : (N : ℝ)⁻¹ ≤ z.im := by
      rw [abs_of_pos hz0] at hzη
      refine le_trans ?_ hzη
      rw [← Real.rpow_neg_one]
      exact LL_rpow_mono (by exact_mod_cast hN) (by linarith)
    have hτN : τ ≤ N := by
      have h1 : τ * (N : ℝ)⁻¹ ≤ 1 := (mul_le_mul_of_nonneg_left hzN hτ.le).trans hτz
      rwa [← div_eq_mul_inv, div_le_one hNr0] at h1
    rw [div_le_div_iff₀ (by positivity) hNr0]
    have h2 : τ ≤ (N : ℝ) * dm := by nlinarith
    have h3 : τ ^ 2 * N ≤ τ * ((N : ℝ) * dm) * N :=
      mul_le_mul_of_nonneg_right (by nlinarith) hNr0.le
    nlinarith

/-- The local laws on `𝐃(τ) ∩ {η > 0}`, in union form over `z` with `N₀` uniform in the
deterministic `u, v` and `B`. -/
private lemma LL_upper (D : ℕ) (δA : ℝ) (C θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hs : LLSeq D δA C θ μ A) (τ : ℝ) (hτ : 0 < τ) :
    (∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ w : Unit,
      μ N {h | ∃ z ∈ {z | z ∈ specDom τ N ∧ 0 < z.im},
        (N : ℝ) ^ τ' * LL_zB D A N z < LL_xb D A N z w h} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D'))) ∧
    (∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ w : LL_UV D N,
      μ N {h | ∃ z ∈ {z | z ∈ specDom τ N ∧ 0 < z.im},
        (N : ℝ) ^ τ' * LL_zI D A N z < LL_xi D A N z w h} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D'))) ∧
    (∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ w : LL_Bs D N,
      μ N {h | ∃ z ∈ {z | z ∈ specDom τ N ∧ 0 < z.im},
        (N : ℝ) ^ τ' * LL_zA N z < LL_xa D A N z w h} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D'))) := by
  obtain ⟨K, hK8, hboot⟩ := bootstrap_stage
  obtain ⟨lb, li, la⟩ := LL_low K hK8 hboot D δA C θ μ A hs τ hτ
  obtain ⟨hb, hi, ha⟩ := LL_high D δA C θ μ A hs τ hτ
  have hD1 := hs.one_le_D
  have hnull : ∀ N, μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := fun N =>
    ae_iff.mp (hs.mem N).herm
  obtain ⟨NΛ, hNΛ⟩ := LL_lam_small hs
  obtain ⟨Ce, hCe, hCeP⟩ := edge_close_to_edge_sc
  set dm := Real.sqrt (2 * τ⁻¹ + 2 + Ce / 10) + 1 with hdm
  set N₁ := max (max NΛ 12) (max ⌈τ⁻¹⌉₊ ⌈dm / τ ^ 2⌉₊) with hN₁def
  set S : ℕ → Set ℂ := fun N => {z | N₁ ≤ N ∧ z ∈ specDom τ N ∧ 0 < z.im} with hSdef
  have hSsub : ∀ N, S N ⊆ LL_Zlow τ N ∪ LL_Zhigh τ N := by
    intro N z ⟨_, hz, hz0⟩
    rcases le_total z.im 2 with h2 | h2
    · exact Or.inl ⟨hz, hz0, h2⟩
    · exact Or.inr ⟨hz, h2⟩
  have hSN : ∀ N, ∀ z ∈ S N, 12 ≤ N ∧ NΛ ≤ N ∧ τ⁻¹ ≤ N ∧ dm / τ ^ 2 ≤ N := by
    intro N z ⟨hN, _, _⟩
    have hc1 : ⌈τ⁻¹⌉₊ ≤ N := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hN
    have hc2 : ⌈dm / τ ^ 2⌉₊ ≤ N := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hN
    refine ⟨le_trans (by simp [hN₁def]) hN, le_trans (by simp [hN₁def]) hN, ?_, ?_⟩
    · exact (Nat.le_ceil _).trans (by exact_mod_cast hc1)
    · exact (Nat.le_ceil _).trans (by exact_mod_cast hc2)
  have hS : ∀ N, 1 ≤ N → S N ⊆ Metric.closedBall 0 ((N : ℝ) ^ (1 : ℝ)) := by
    intro N _ z hz
    obtain ⟨_, _, hτN, _⟩ := hSN N z hz
    rw [Metric.mem_closedBall, dist_zero_right, Real.rpow_one]
    exact hz.2.1.1.trans hτN
  have hSim : ∀ N, ∀ z ∈ S N, (N : ℝ) ^ (-1 + τ) ≤ z.im := by
    intro N z hz
    have := hz.2.1.2
    rwa [abs_of_pos hz.2.2] at this
  have hζ : ∀ N, 1 ≤ N → ∀ u ∈ S N, (N : ℝ) ^ (-(3 : ℝ)) ≤ LL_zI D A N u ∧
      (N : ℝ) ^ (-(3 : ℝ)) ≤ LL_zA N u ∧ (N : ℝ) ^ (-(3 : ℝ)) ≤ LL_zB D A N u := by
    intro N hN u hu
    obtain ⟨h12, hNΛ', hτN, hdN⟩ := hSN N u hu
    have hNr0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    obtain ⟨h1, h2, h3⟩ := LL_zeta_low D N hD1 hN A (hNΛ N hNΛ') τ hτ Ce hCe hCeP u hu.2.1 hu.2.2
    have e3 : (N : ℝ) ^ (-(3 : ℝ)) = 1 / (N : ℝ) ^ 3 := by
      rw [Real.rpow_neg hNr0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        one_div]
    have hτN' : 1 ≤ τ * N := by
      have := mul_le_mul_of_nonneg_left hτN hτ.le
      rwa [mul_inv_cancel₀ hτ.ne'] at this
    have hA : (N : ℝ) ^ (-(3 : ℝ)) ≤ τ / N := by
      rw [e3, div_le_div_iff₀ (by positivity) hNr0]
      have : (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith
      nlinarith
    have hB : (N : ℝ) ^ (-(3 : ℝ)) ≤ τ ^ 2 / ((N : ℝ) ^ 2 * dm) := by
      rw [e3, div_le_div_iff₀ (by positivity) (by positivity)]
      have hdN' : dm ≤ τ ^ 2 * N := by
        rw [div_le_iff₀ (by positivity)] at hdN; linarith
      have : (N : ℝ) ^ 2 * dm ≤ τ ^ 2 * (N : ℝ) ^ 3 := by
        calc (N : ℝ) ^ 2 * dm ≤ (N : ℝ) ^ 2 * (τ ^ 2 * N) :=
              mul_le_mul_of_nonneg_left hdN' (by positivity)
          _ = τ ^ 2 * (N : ℝ) ^ 3 := by ring
      linarith
    exact ⟨hA.trans h1, hA.trans h2, hB.trans h3⟩
  have hLζ : ∀ N, 1 ≤ N → ∀ u ∈ S N, ∀ v ∈ S N,
      |LL_zI D A N u - LL_zI D A N v| ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖ ∧
      |LL_zA N u - LL_zA N v| ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖ ∧
      |LL_zB D A N u - LL_zB D A N v| ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖ := by
    intro N _ u hu v hv
    obtain ⟨h12, hNΛ', _, _⟩ := hSN N u hu
    exact LL_zeta_lip D N hD1 h12 A (hNΛ N hNΛ') τ hτ.le u v (hSim N u hu) (hSim N v hv)
  have hLq : ∀ N, 1 ≤ N → ∀ h, (Matrix.of h).IsHermitian → ∀ u ∈ S N, ∀ v ∈ S N,
      |LL_xb D A N u () h - LL_xb D A N v () h| ≤ (N : ℝ) ^ (3 : ℝ) * ‖u - v‖ ∧
      (∀ w : LL_UV D N, |LL_xi D A N u w h - LL_xi D A N v w h| ≤
        (N : ℝ) ^ (3 : ℝ) * ‖u - v‖) ∧
      (∀ w : LL_Bs D N, |LL_xa D A N u w h - LL_xa D A N v w h| ≤
        (N : ℝ) ^ (3 : ℝ) * ‖u - v‖) := by
    intro N _ h hH u hu v hv
    obtain ⟨h12, hNΛ', _, _⟩ := hSN N u hu
    exact LL_q_lip D N hD1 (by omega) A (hNΛ N hNΛ') h hH τ hτ.le u v (hSim N u hu)
      (hSim N v hv)
  have hfin : ∀ N, N₁ ≤ N → {z | z ∈ specDom τ N ∧ 0 < z.im} = S N := by
    intro N hN; ext z; simp [hSdef, hN]
  refine ⟨fun τ' hτ' D' hD' => ?_, fun τ' hτ' D' hD' => ?_, fun τ' hτ' D' hD' => ?_⟩
  · obtain ⟨N₀, hN₀⟩ := LL_net μ hnull S (LL_xb D A) (LL_zB D A) hS
      (fun N hN w h hH u hu v hv => (hLq N hN h hH u hu v hv).1)
      (fun N hN u hu v hv => (hLζ N hN u hu v hv).2.2) (fun N hN u hu => (hζ N hN u hu).2.2)
      (LL_Sup_sub (LL_Sup_union lb hb) ⟨0, fun N _ => hSsub N⟩) τ' hτ' D' hD'
    exact ⟨max N₀ N₁, fun N hN w => by
      rw [hfin N (le_of_max_le_right hN)]; exact hN₀ N (le_of_max_le_left hN) w⟩
  · obtain ⟨N₀, hN₀⟩ := LL_net μ hnull S (LL_xi D A) (LL_zI D A) hS
      (fun N hN w h hH u hu v hv => (hLq N hN h hH u hu v hv).2.1 w)
      (fun N hN u hu v hv => (hLζ N hN u hu v hv).1) (fun N hN u hu => (hζ N hN u hu).1)
      (LL_Sup_sub (LL_Sup_union li hi) ⟨0, fun N _ => hSsub N⟩) τ' hτ' D' hD'
    exact ⟨max N₀ N₁, fun N hN w => by
      rw [hfin N (le_of_max_le_right hN)]; exact hN₀ N (le_of_max_le_left hN) w⟩
  · obtain ⟨N₀, hN₀⟩ := LL_net μ hnull S (LL_xa D A) (fun N z => LL_zA N z) hS
      (fun N hN w h hH u hu v hv => (hLq N hN h hH u hu v hv).2.2 w)
      (fun N hN u hu v hv => (hLζ N hN u hu v hv).2.1) (fun N hN u hu => (hζ N hN u hu).2.1)
      (LL_Sup_sub (LL_Sup_union la ha) ⟨0, fun N _ => hSsub N⟩) τ' hτ' D' hD'
    exact ⟨max N₀ N₁, fun N hN w => by
      rw [hfin N (le_of_max_le_right hN)]; exact hN₀ N (le_of_max_le_left hN) w⟩

/-- From the upper half plane to `𝐃(τ)` by `z ↦ z̄`: if the quantity at `z̄` is bounded by the one
at `z` for the parameter `σ w`, and the control is even, the union-form bound on
`𝐃(τ) ∩ {η > 0}` gives the one on `𝐃(τ)`. -/
private lemma LL_both {D : ℕ} (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ))
    (hnull : ∀ N, μ N {h | ¬ (Matrix.of h).IsHermitian} = 0) {W : ℕ → Type}
    (q : ∀ N, ℂ → W N → (Idx D N → Idx D N → ℂ) → ℝ) (ζ : ℕ → ℂ → ℝ) (τ : ℝ)
    (σ : ∀ N, W N → W N)
    (hconj : ∀ N, 1 ≤ N → ∀ z w h, (Matrix.of h).IsHermitian → 0 < z.im →
      q N (star z) w h ≤ q N z (σ N w) h)
    (hζ : ∀ N, 1 ≤ N → ∀ z : ℂ, z.im ≠ 0 → ζ N (star z) = ζ N z)
    (hup : ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ w : W N,
      μ N {h | ∃ z ∈ {z | z ∈ specDom τ N ∧ 0 < z.im}, (N : ℝ) ^ τ' * ζ N z < q N z w h} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D'))) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ w : W N,
      μ N {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' * ζ N z < q N z w h} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  obtain ⟨N₀, hN₀⟩ := hup τ' hτ' (D' + 1) (by linarith)
  refine ⟨max N₀ 2, fun N hN w => ?_⟩
  have hN0 : N₀ ≤ N := le_of_max_le_left hN
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  have hNr0 : (0 : ℝ) < N := by have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
                                linarith
  have hsub : {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' * ζ N z < q N z w h} ⊆
      ({h | ∃ z ∈ {z | z ∈ specDom τ N ∧ 0 < z.im}, (N : ℝ) ^ τ' * ζ N z < q N z w h} ∪
        {h | ∃ z ∈ {z | z ∈ specDom τ N ∧ 0 < z.im},
          (N : ℝ) ^ τ' * ζ N z < q N z (σ N w) h}) ∪ {h | ¬ (Matrix.of h).IsHermitian} := by
    intro h ⟨z, hz, hlt⟩
    by_cases hH : (Matrix.of h).IsHermitian
    · left
      have hne : z.im ≠ 0 := by
        intro h0
        have := hz.2
        rw [h0, abs_zero] at this
        exact absurd this (not_le.mpr (Real.rpow_pos_of_pos hNr0 _))
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · right
        have hz' : star z ∈ specDom τ N := by
          refine ⟨by rw [norm_star]; exact hz.1, ?_⟩
          simp only [Complex.star_def, Complex.conj_im, abs_neg]
          exact hz.2
        have hz'0 : 0 < (star z).im := by simp only [Complex.star_def, Complex.conj_im]; linarith
        refine ⟨star z, ⟨hz', hz'0⟩, ?_⟩
        have h1 := hconj N (by omega) (star z) w h hH hz'0
        rw [star_star] at h1
        rw [hζ N (by omega) z hne]
        exact lt_of_lt_of_le hlt h1
      · left; exact ⟨z, ⟨hz, hpos⟩, hlt⟩
    · right; exact hH
  calc _ ≤ _ := measure_mono hsub
    _ ≤ μ N ({h | ∃ z ∈ {z | z ∈ specDom τ N ∧ 0 < z.im}, (N : ℝ) ^ τ' * ζ N z < q N z w h} ∪
        {h | ∃ z ∈ {z | z ∈ specDom τ N ∧ 0 < z.im},
          (N : ℝ) ^ τ' * ζ N z < q N z (σ N w) h}) + 0 := by
        rw [← hnull N]; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := by
        rw [add_zero]
        exact (measure_union_le _ _).trans (add_le_add (hN₀ N hN0 w) (hN₀ N hN0 (σ N w)))
    _ ≤ _ := LL_two_le N hN2 D'

/-- From sequences of members to the class (`uniform_of_seq`, `llClass_pad`): a property of
`(θ, μ, A)` that holds eventually along every sequence of members (`LLSeq`) holds for all members
at all large `N`, with `N₀` independent of `θ ∈ [0, 1]`, `μ` and `A`. -/
private lemma LL_unif (D : ℕ) (hD : 1 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ)
    (good : ∀ N, ℝ → Measure (Idx D N → Idx D N → ℂ) → Matrix (Fin N) (Fin N) ℂ → Prop)
    (hseq : ∀ (θ : ℕ → ℝ) (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ))
      (A : ∀ N, Matrix (Fin N) (Fin N) ℂ), LLSeq D δA C θ μ A →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → good N (θ N) (μ N) (A N)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) → good N θ μ A := by
  obtain ⟨N₀, hN₀⟩ := uniform_of_seq
    (X := fun N => ℝ × Measure (Idx D N → Idx D N → ℂ) × Matrix (Fin N) (Fin N) ℂ)
    (fun N => {x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ LLClass D N C x.1 x.2.1 ∧ opNorm x.2.2 ≤ (N : ℝ) ^ (-δA)})
    (fun N x => ¬ good N x.1 x.2.1 x.2.2)
    (fun N₁ hN₁ ⟨x, hx⟩ N => by
      obtain ⟨μ', hμ'⟩ := llClass_pad D N₁ hN₁ C x.1 x.2.1 hx.2.2.1 N
      have h0 : opNorm (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by unfold opNorm; simp
      exact ⟨(x.1, μ', 0), hx.1, hx.2.1, hμ', by rw [h0]; exact Real.rpow_nonneg (by positivity) _⟩)
    (fun x hx => by
      obtain ⟨N₀, hN₀⟩ := hseq (fun N => (x N).1) (fun N => (x N).2.1) (fun N => (x N).2.2)
        ⟨hD, hδA, fun N => ⟨(hx N).1, (hx N).2.1⟩, fun N => (hx N).2.2.1, fun N => (hx N).2.2.2⟩
      exact ⟨N₀, fun N hN hb => hb (hN₀ N hN)⟩)
  exact ⟨N₀, fun N hN θ h0 h1 μ hμ A hA => not_not.mp (hN₀ N hN (θ, μ, A) ⟨h0, h1, hμ, hA⟩)⟩
/-- Lemma 2.9 [lem_loc] along one sequence of members (`LLSeq`), on `𝐃(τ)` of Definition 3.1
[def_wtM], union over `z`: the block traces satisfy
`|x|_∞ ≤ N^{τ'} min(Ψ²/√(κ+|η|), Ψ)` with `Ψ` the control parameter of (2.22) [eq:aniso_local];
(2.22) holds for deterministic unit `u, v`; (2.23) [eq:aver_local] holds for deterministic
`‖B‖ ≤ 1`; each outside an event of probability `≤ N^{-D'}` for `N ≥ N₀(τ', D')`. -/
theorem local_law_seq (D : ℕ) (δA τ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hs : LLSeq D δA C θ μ A) (hτ : 0 < τ) :
    (∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      μ N {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' *
          min (psiIso (lam D N (A N)) N z ^ 2 /
              Real.sqrt (kappa (lam D N (A N)) z.re + |z.im|))
            (psiIso (lam D N (A N)) N z) <
        ‖blockTr D N (res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D'))) ∧
    (∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ u v : Idx D N → ℂ, ∑ i, ‖u i‖ ^ 2 = 1 → ∑ i, ‖v i‖ ^ 2 = 1 →
        μ N {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' * psiIso (lam D N (A N)) N z <
            ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z -
              MExt (lam D N (A N)) z) *ᵥ v)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D'))) ∧
    (∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
        μ N {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' * (1 / ((N : ℝ) * |z.im|)) <
            ‖ntr ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) * B)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D'))) := by
  have hD1 := hs.one_le_D
  have hnull : ∀ N, μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := fun N =>
    ae_iff.mp (hs.mem N).herm
  obtain ⟨ub, ui, ua⟩ := LL_upper D δA C θ μ A hs τ hτ
  refine ⟨fun τ' hτ' D' hD' => ?_, fun τ' hτ' D' hD' => ?_, fun τ' hτ' D' hD' => ?_⟩
  · obtain ⟨N₀, hN₀⟩ := LL_both μ hnull (LL_xb D A) (LL_zB D A) τ (fun _ w => w)
      (fun N hN z _ h hH hz => (LL_conj_q D N hD1 hN A h hH z hz).1)
      (fun N hN z hz => (LL_conj_zeta D N hD1 hN A z hz).1) ub τ' hτ' D' hD'
    exact ⟨N₀, fun N hN => hN₀ N hN ()⟩
  · obtain ⟨N₀, hN₀⟩ := LL_both μ hnull (LL_xi D A) (LL_zI D A) τ (fun _ w => (w.2, w.1))
      (fun N hN z w h hH hz => (LL_conj_q D N hD1 hN A h hH z hz).2.1 w)
      (fun N hN z hz => (LL_conj_zeta D N hD1 hN A z hz).2.1) ui τ' hτ' D' hD'
    exact ⟨N₀, fun N hN u v hu hv => hN₀ N hN (⟨u, hu⟩, ⟨v, hv⟩)⟩
  · obtain ⟨N₀, hN₀⟩ := LL_both μ hnull (LL_xa D A) (fun N z => LL_zA N z) τ
      (fun _ w => ⟨w.1ᴴ, by rw [LL_opNorm_conjTranspose]; exact w.2⟩)
      (fun N hN z w h hH hz => (LL_conj_q D N hD1 hN A h hH z hz).2.2 w)
      (fun N hN z hz => (LL_conj_zeta D N hD1 hN A z hz).2.2) ua τ' hτ' D' hD'
    exact ⟨N₀, fun N hN B hB => hN₀ N hN ⟨B, hB⟩⟩

/-- The block traces of `G - M` for the class `LLClass`, uniformly in `θ ∈ [0, 1]`: outside an
event of probability `≤ N^{-D'}`, `max_a |D⟨E_a (G - M)⟩| ≤ N^{τ'} min(Ψ²/√(κ+|η|), Ψ)` for all
`z ∈ 𝐃(τ)` at once, `Ψ` the control parameter of (2.22) [eq:aniso_local]. -/
theorem blockTr_local (D : ℕ) (hD : 1 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
        μ {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' *
            min (psiIso (lam D N A) N z ^ 2 / Real.sqrt (kappa (lam D N A) z.re + |z.im|))
              (psiIso (lam D N A) N z) <
            ‖blockTr D N (res (Matrix.of h + lam D N A) z - MExt (lam D N A) z)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  exact LL_unif D hD δA hδA C _ fun θ μ A hs => (local_law_seq D δA τ C θ μ A hs hτ).1 τ' hτ' D' hD'

/-- (2.22) [eq:aniso_local] of Lemma 2.9 [lem_loc] for the class `LLClass`, uniformly in
`θ ∈ [0, 1]`: for deterministic unit `u, v`, outside an event of probability `≤ N^{-D'}`,
`|(G(z) - M(z))_{uv}| ≤ N^{τ'} (√(|Im m|/(N|η|)) + 1/(N|η|))` for all `z ∈ 𝐃(τ)` at once. -/
theorem aniso_local (D : ℕ) (hD : 1 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ u v : Idx D N → ℂ, ∑ i, ‖u i‖ ^ 2 = 1 → ∑ i, ‖v i‖ ^ 2 = 1 →
        μ {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' * psiIso (lam D N A) N z <
            ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *ᵥ v)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  exact LL_unif D hD δA hδA C _ fun θ μ A hs =>
    (local_law_seq D δA τ C θ μ A hs hτ).2.1 τ' hτ' D' hD'

/-- (2.23) [eq:aver_local] of Lemma 2.9 [lem_loc] for the class `LLClass`, uniformly in
`θ ∈ [0, 1]`: for deterministic `‖B‖ ≤ 1`, outside an event of probability `≤ N^{-D'}`,
`|⟨(G(z) - M(z)) B⟩| ≤ N^{τ'}/(N|η|)` for all `z ∈ 𝐃(τ)` at once. -/
theorem aver_local (D : ℕ) (hD : 1 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
        μ {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' * (1 / ((N : ℝ) * |z.im|)) <
            ‖ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) * B)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  exact LL_unif D hD δA hδA C _ fun θ μ A hs =>
    (local_law_seq D δA τ C θ μ A hs hτ).2.2 τ' hτ' D' hD'


end RBMTransitionEdge

end
