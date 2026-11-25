module

public import RBMTransitionEdge.Edge.Defs
public import RBMTransitionEdge.LocalLaw.ResPolyDer
public import RBMTransitionEdge.Localized.Pathwise
public import RBMTransitionEdge.Tools.MathlibBackport

@[expose] public section

/-!
# The edge count of Lemma 4.3 and its derivatives

The function `F(A(1), …, A(n))` of (4.7) [2comVVt] and its spectral points, the weights of the
entry derivatives, the derivative (4.10) [partial_xy_F_A_t] of `A` in a Hermitian direction, its
smoothness and a priori bound, the structure of the entry derivatives of `F(A)` with one factor
`Im G` per chain (E31), and the identity `Im M = Im(z + m) M M*` behind (4.12).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `F(A(1), …, A(n))`, `A(i) = DN ∫_{E₁(i)}^{E₂(i)} Im ⟨(h + Λ - y - iη)⁻¹⟩ dy`: the function of
the array inside the expectations of (4.7) [2comVVt]. -/
def edgeFn (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (E₁ E₂ : Fin n → ℝ) (h : Idx D N → Idx D N → ℂ) : ℝ :=
  F fun i => edgeCount D N A η (E₁ i) (E₂ i) h

/-- The `2n` spectral parameters `E_e(i) + iη`, `e ∈ {1, 2}`, of (4.7) [2comVVt]. -/
def edgePt (η : ℝ) {n : ℕ} (E₁ E₂ : Fin n → ℝ) (p : Fin n × Fin 2) : ℂ :=
  (((if p.2 = 0 then E₁ p.1 else E₂ p.1 : ℝ)) : ℂ) + (η : ℂ) * Complex.I

/-- The weight of the entry `(i, j)` in the drift `Σ_{x,y} h_{xy} ∂_{xy}` of the display before
(4.9) [eq:prodnGt], written with `∂_{w̄}` of the substitution `setEntry`: `2` on the diagonal,
where `setEntry` sees `Re w` only, and `1` off it. -/
def driftWt {D N : ℕ} (i j : Idx D N) : ℂ := if i = j then 2 else 1

/-- The weight of the entry `(i, j)` in `Σ_{x,y} ∂_{xy} ∂_{yx}` of (4.9) [eq:prodnGt], written with
`∂_w ∂_{w̄}` of the substitution `setEntry`: `4` on the diagonal and `1` off it. -/
def genWt {D N : ℕ} (i j : Idx D N) : ℂ := if i = j then 4 else 1

/-! ### Hermitian lines and the derivative of the resolvent -/

/-- `Matrix.of (h + s • V) = Matrix.of h + s • Matrix.of V` for real `s`. -/
private lemma CCalc_of_line {D N : ℕ} (h V : Idx D N → Idx D N → ℂ) (s : ℝ) :
    Matrix.of (h + s • V) = Matrix.of h + (s : ℂ) • Matrix.of V := by
  ext a b
  simp [Complex.real_smul]

/-- `h + s V` is Hermitian for Hermitian `h`, `V` and real `s`. -/
private lemma CCalc_line_herm {D N : ℕ} (h V : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hV : (Matrix.of V).IsHermitian) (s : ℝ) :
    (Matrix.of (h + s • V)).IsHermitian := by
  rw [CCalc_of_line]
  exact hh.add (hV.smul (Complex.conj_ofReal s))

/-- The derivative at `s = 0` of the entry `(k, l)` of `((h + s V) + Λ - z)⁻¹` along a Hermitian
line is `-(G V G)_{kl}`, `G = (h + Λ - z)⁻¹`, `Im z ≠ 0`. -/
private lemma CCalc_hasDerivAt_res_line {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (h V : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (hV : (Matrix.of V).IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (k l : Idx D N) :
    HasDerivAt (fun s : ℝ => res (Matrix.of (h + s • V) + Λ) z k l)
      (-(res (Matrix.of h + Λ) z * Matrix.of V * res (Matrix.of h + Λ) z) k l) 0 := by
  set G : ℝ → Matrix (Idx D N) (Idx D N) ℂ := fun s => res (Matrix.of (h + s • V) + Λ) z with hG
  have hcont : ∀ p q, Continuous (fun s : ℝ => G s p q) := by
    intro p q
    have e : (fun s : ℝ => G s p q) = (fun h' : Idx D N → Idx D N → ℂ =>
        res (Matrix.of (symArr h') + Λ) z p q) ∘ (fun s : ℝ => h + s • V) := by
      funext s
      simp only [hG, Function.comp]
      rw [symArr_of_isHermitian _ (CCalc_line_herm h V hh hV s)]
    rw [e]
    exact (contDiff_res_symArr Λ hΛ z hz p q 0).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hG0 : G 0 = res (Matrix.of h + Λ) z := by simp [hG]
  have hid : ∀ s : ℝ, G s - G 0 = -((s : ℂ) • (G s * Matrix.of V * G 0)) := by
    intro s
    have hHs := CCalc_line_herm h V hh hV s
    obtain ⟨-, h1⟩ := res_mul_sub_of_im_ne (Matrix.of (h + s • V) + Λ) (hHs.add hΛ) z hz
    obtain ⟨h2, -⟩ := res_mul_sub_of_im_ne (Matrix.of h + Λ) (hh.add hΛ) z hz
    set M0 : Matrix (Idx D N) (Idx D N) ℂ :=
      Matrix.of h + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) with hM0
    set Ms : Matrix (Idx D N) (Idx D N) ℂ :=
      Matrix.of (h + s • V) + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) with hMs
    have hM : M0 - Ms = -((s : ℂ) • Matrix.of V) := by
      rw [hM0, hMs, CCalc_of_line]; abel
    have h1' : G s * Ms = 1 := h1
    have h2' : M0 * G 0 = 1 := by rw [hG0]; exact h2
    have key : G s * (M0 - Ms) * G 0 = G s - G 0 := by
      rw [mul_sub, sub_mul, mul_assoc (G s) M0, h2', h1', mul_one, one_mul]
    rw [← key, hM, Matrix.mul_neg, Matrix.mul_smul, Matrix.neg_mul, Matrix.smul_mul]
  have hc : Continuous (fun s : ℝ => -((G s * Matrix.of V * G 0) k l)) := by
    refine Continuous.neg ?_
    simp only [Matrix.mul_apply, Finset.sum_mul]
    refine continuous_finsetSum _ fun q _ => continuous_finsetSum _ fun p _ => ?_
    exact ((hcont k p).mul continuous_const).mul continuous_const
  have hlim := hc.tendsto 0
  have hv : (-((G 0 * Matrix.of V * G 0) k l)) =
      (-(res (Matrix.of h + Λ) z * Matrix.of V * res (Matrix.of h + Λ) z) k l) := by
    rw [hG0]
  rw [hv] at hlim
  rw [hasDerivAt_iff_tendsto_slope]
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have := congrFun (congrFun (hid s) k) l
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul] at this
  rw [slope_def_module, sub_zero, Complex.real_smul]
  rw [this]
  push_cast
  field_simp


/-- The `y`-derivative of the entries of `G(y + iη)`. -/
private lemma CCalc_hasDerivAt_res_y {D N : ℕ} (X : Matrix (Idx D N) (Idx D N) ℂ)
    (hX : X.IsHermitian) (η y : ℝ) (hη : 0 < η) (k l : Idx D N) :
    HasDerivAt (fun y : ℝ => res X ((y : ℂ) + (η : ℂ) * Complex.I) k l)
      ((res X ((y : ℂ) + (η : ℂ) * Complex.I) * res X ((y : ℂ) + (η : ℂ) * Complex.I)) k l) y := by
  have hz : 0 < (((y : ℂ) + (η : ℂ) * Complex.I)).im := by simp [hη]
  have h1 := hasDerivAt_res X hX ((y : ℂ) + (η : ℂ) * Complex.I) hz k l
  have h2 := h1.comp_add_const (y : ℂ) ((η : ℂ) * Complex.I)
  exact h2.comp_ofReal

/-- The shift of the array by `y` times the identity. -/
private def CCalc_shift {D N : ℕ} (p : (Idx D N → Idx D N → ℂ) × ℝ) : Idx D N → Idx D N → ℂ :=
  fun a b => p.1 a b - (p.2 : ℂ) * (if a = b then 1 else 0)

/-- Shifting the array by `y` times the identity shifts its Hermitian part by `y`. -/
private lemma CCalc_symArr_shift {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (p : (Idx D N → Idx D N → ℂ) × ℝ) :
    Matrix.of (symArr (CCalc_shift p)) + Λ =
      (Matrix.of (symArr p.1) + Λ) - (p.2 : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.of_apply, symArr, CCalc_shift, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hba : (if b = a then (1 : ℂ) else 0) = if a = b then 1 else 0 := by
    by_cases h : a = b
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hba, map_sub, map_mul, Complex.conj_ofReal]
  have : starRingEnd ℂ (if a = b then (1 : ℂ) else 0) = if a = b then 1 else 0 := by
    split_ifs <;> simp
  rw [this]
  ring

/-- `G(y + iη)` of the Hermitian part of `h` is `G(iη)` of the shifted array. -/
private lemma CCalc_res_shift {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (η : ℝ)
    (p : (Idx D N → Idx D N → ℂ) × ℝ) :
    res (Matrix.of (symArr p.1) + Λ) ((p.2 : ℂ) + (η : ℂ) * Complex.I) =
      res (Matrix.of (symArr (CCalc_shift p)) + Λ) ((η : ℂ) * Complex.I) := by
  unfold res
  rw [CCalc_symArr_shift, sub_sub, ← add_smul]

/-- The entries of `G(y + iη)` of the Hermitian part are smooth in the array and `y` jointly, for `η
> 0`. -/
private lemma CCalc_contDiff_res_joint {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (η : ℝ) (hη : 0 < η) (k l : Idx D N) (n : ℕ) :
    ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℝ =>
      res (Matrix.of (symArr p.1) + Λ) ((p.2 : ℂ) + (η : ℂ) * Complex.I) k l) := by
  have e : (fun p : (Idx D N → Idx D N → ℂ) × ℝ =>
      res (Matrix.of (symArr p.1) + Λ) ((p.2 : ℂ) + (η : ℂ) * Complex.I) k l) =
      (fun h' : Idx D N → Idx D N → ℂ => res (Matrix.of (symArr h') + Λ)
        ((η : ℂ) * Complex.I) k l) ∘ CCalc_shift := by
    funext p
    simp only [Function.comp, CCalc_res_shift]
  rw [e]
  refine (contDiff_res_symArr Λ hΛ ((η : ℂ) * Complex.I) (by simpa using hη.ne') k l n).comp ?_
  refine contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => ?_
  exact ((contDiff_apply_apply ℝ a b).comp contDiff_fst).sub
    ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)

/-- The integrand of `edgeCount` is smooth jointly in the array and `y`. -/
private lemma CCalc_contDiff_integrand (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ)
    (hη : 0 < η) :
    ContDiff ℝ ∞ (fun p : (Idx D N → Idx D N → ℂ) × ℝ =>
      (ntr (res (Matrix.of (symArr p.1) + lam D N A) ((p.2 : ℂ) + (η : ℂ) * Complex.I))).im) := by
  rw [contDiff_infty]
  intro n
  have e : (fun p : (Idx D N → Idx D N → ℂ) × ℝ =>
      (ntr (res (Matrix.of (symArr p.1) + lam D N A) ((p.2 : ℂ) + (η : ℂ) * Complex.I))).im) =
      fun p => Complex.imCLM (((Fintype.card (Idx D N) : ℂ))⁻¹ *
        ∑ a, res (Matrix.of (symArr p.1) + lam D N A) ((p.2 : ℂ) + (η : ℂ) * Complex.I) a a) := by
    funext p
    simp [ntr, Matrix.trace, Matrix.diag]
  rw [e]
  exact Complex.imCLM.contDiff.comp (contDiff_const.mul (ContDiff.sum fun a _ =>
    CCalc_contDiff_res_joint (lam D N A) (lam_isHermitian D N A) η hη a a n))


/-! ### Traces -/

/-- The real part of `tr(Im G · V)` for Hermitian `V`. -/
private lemma CCalc_trace_imRes {ι : Type*} [Fintype ι] [DecidableEq ι] (X V : Matrix ι ι ℂ)
    (hV : V.IsHermitian) (z : ℂ) :
    ((imRes X z * V).trace).re = ((V * res X z).trace).im := by
  unfold imRes
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.sub_mul, Matrix.trace_sub]
  have h1 : ((res X z)ᴴ * V).trace = star ((V * res X z).trace) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hV.eq]
  rw [h1, Matrix.trace_mul_comm (res X z) V]
  have h2 : (2 * Complex.I)⁻¹ * ((V * res X z).trace - star (V * res X z).trace) =
      (((V * res X z).trace.im : ℝ) : ℂ) := by
    rw [inv_mul_eq_iff_eq_mul₀ (by simp)]
    apply Complex.ext <;> simp
    ring
  rw [smul_eq_mul, h2, Complex.ofReal_re]

/-- The trace of a product with `V` is continuous in `y` when the entries of `G` are. -/
private lemma CCalc_continuous_trace {ι : Type*} [Fintype ι] (V : Matrix ι ι ℂ)
    (G : ℝ → Matrix ι ι ℂ) (hG : ∀ p q, Continuous fun t => G t p q) :
    Continuous fun t => (V * (G t * G t)).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun p _ =>
    continuous_finsetSum _ fun q _ => ?_
  exact continuous_const.mul ((hG p q).mul (hG q a))

/-- The imaginary part of the normalized trace. -/
private lemma CCalc_im_ntr {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) :
    (ntr B).im = ((Fintype.card ι : ℝ))⁻¹ * B.trace.im := by
  unfold ntr
  have : ((Fintype.card ι : ℂ))⁻¹ = ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.im_ofReal_mul]

/-- The index set `Idx D N` has `D N` elements. -/
private lemma CCalc_card (D N : ℕ) : Fintype.card (Idx D N) = D * N := by simp

/-- `|⟨B⟩| ≤ c` when every diagonal entry of `B` has modulus at most `c`. -/
private lemma CCalc_norm_ntr_le {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hB : ∀ a, ‖B a a‖ ≤ c) : ‖ntr B‖ ≤ c := by
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  by_cases h0 : Fintype.card ι = 0
  · simp [h0, hc]
  · have hpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero h0
    have : ‖B.trace‖ ≤ (Fintype.card ι : ℝ) * c := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ a, ‖B.diag a‖ ≤ ∑ _a : ι, c := Finset.sum_le_sum fun a _ => hB a
        _ = (Fintype.card ι : ℝ) * c := by simp
    calc (Fintype.card ι : ℝ)⁻¹ * ‖B.trace‖ ≤ (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * c) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hpos.le)
      _ = c := by field_simp

/-- (4.10) [partial_xy_F_A_t] in every Hermitian direction: the derivative of `A` along `V` is
`-tr((Im G(E₂ + iη) - Im G(E₁ + iη)) V)`. -/
theorem edgeCount_hasDerivAt (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ)
    (hη : 0 < η) (h V : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (hV : (Matrix.of V).IsHermitian) :
    HasDerivAt (fun s : ℝ => edgeCount D N A η E₁ E₂ (h + s • V))
      (-((imRes (Matrix.of h + lam D N A) ((E₂ : ℂ) + (η : ℂ) * Complex.I) -
          imRes (Matrix.of h + lam D N A) ((E₁ : ℂ) + (η : ℂ) * Complex.I)) *
            Matrix.of V).trace.re) 0 := by
  have hΛh := lam_isHermitian D N A
  have hX : (Matrix.of h + lam D N A).IsHermitian := hh.add hΛh
  set f : (Idx D N → Idx D N → ℂ) → ℝ → ℝ := fun h' y =>
    (ntr (res (Matrix.of (symArr h') + lam D N A) ((y : ℂ) + (η : ℂ) * Complex.I))).im with hf
  have hfj : ContDiff ℝ ∞ f.uncurry := CCalc_contDiff_integrand D N A η hη
  -- the Fréchet derivative of the parametric integral
  have hΦ := intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := volume)
    (u := Set.univ) (x₀ := h) Filter.univ_mem (a := E₁) (b := E₂)
    (f := f) (hfj.contDiffOn.of_le (by exact_mod_cast le_top))
  have e0 : h + (0 : ℝ) • V = h := by simp
  have hline : HasDerivAt (fun s : ℝ => h + s • V) V 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add h
  have hΦ0 : HasFDerivAt (fun x => ∫ t in E₁..E₂, f x t)
      (∫ t in E₁..E₂, fderiv ℝ (fun x => f x t) h) (h + (0 : ℝ) • V) := by
    rw [e0]; exact hΦ
  have hcomp := hΦ0.comp_hasDerivAt (0 : ℝ) hline
  -- continuity of the integrand of the derivative
  have hφcont : Continuous (fun t : ℝ => fderiv ℝ (fun x => f x t) h) := by
    have hd : ∀ t : ℝ, fderiv ℝ (fun x => f x t) h =
        (fderiv ℝ f.uncurry (h, t)).comp
          (ContinuousLinearMap.inl ℝ (Idx D N → Idx D N → ℂ) ℝ) := by
      intro t
      have h1 : HasFDerivAt f.uncurry (fderiv ℝ f.uncurry (h, t)) (h, t) :=
        ((hfj.differentiable (by simp)) (h, t)).hasFDerivAt
      have h2 := HasFDerivAt.comp (𝕜 := ℝ) h h1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) h t)
      exact h2.fderiv
    simp_rw [hd]
    exact ((hfj.continuous_fderiv (by simp)).comp
      (continuous_const.prodMk continuous_id)).clm_comp continuous_const
  have happ := ContinuousLinearMap.intervalIntegral_apply
    (hφcont.intervalIntegrable (μ := volume) E₁ E₂) V
  have hpt : ∀ t : ℝ, fderiv ℝ (fun x => f x t) h V =
      -(((D * N : ℕ) : ℝ)⁻¹ * ((Matrix.of V * (res (Matrix.of h + lam D N A)
        ((t : ℂ) + (η : ℂ) * Complex.I) * res (Matrix.of h + lam D N A)
          ((t : ℂ) + (η : ℂ) * Complex.I))).trace).im) := by
    intro t
    have hz : ((t : ℂ) + (η : ℂ) * Complex.I).im ≠ 0 := by simpa using hη.ne'
    have hfd : DifferentiableAt ℝ (fun x => f x t) h :=
      ((hfj.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)) h
    have h1 : HasDerivAt (fun s : ℝ => f (h + s • V) t) (fderiv ℝ (fun x => f x t) h V) 0 := by
      have h0 : HasFDerivAt (fun x => f x t) (fderiv ℝ (fun x => f x t) h) (h + (0 : ℝ) • V) := by
        rw [e0]; exact hfd.hasFDerivAt
      exact h0.comp_hasDerivAt (0 : ℝ) hline
    have hG : ∀ a, HasDerivAt (fun s : ℝ => res (Matrix.of (h + s • V) + lam D N A)
        ((t : ℂ) + (η : ℂ) * Complex.I) a a)
        (-(res (Matrix.of h + lam D N A) ((t : ℂ) + (η : ℂ) * Complex.I) * Matrix.of V *
          res (Matrix.of h + lam D N A) ((t : ℂ) + (η : ℂ) * Complex.I)) a a) 0 := fun a =>
      CCalc_hasDerivAt_res_line _ hΛh h V hh hV _ hz a a
    have htr : HasDerivAt (fun s : ℝ => (res (Matrix.of (h + s • V) + lam D N A)
        ((t : ℂ) + (η : ℂ) * Complex.I)).trace)
        (-((res (Matrix.of h + lam D N A) ((t : ℂ) + (η : ℂ) * Complex.I) * Matrix.of V *
          res (Matrix.of h + lam D N A) ((t : ℂ) + (η : ℂ) * Complex.I)).trace)) 0 := by
      have := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => hG a)
      simpa [Matrix.trace, Matrix.diag, Finset.sum_neg_distrib] using this
    have him := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) htr).const_mul
      (((Fintype.card (Idx D N) : ℝ))⁻¹)
    have e1 : (fun s : ℝ => f (h + s • V) t) = fun s => ((Fintype.card (Idx D N) : ℝ))⁻¹ *
        (Complex.imCLM ∘ fun s : ℝ => (res (Matrix.of (h + s • V) + lam D N A)
          ((t : ℂ) + (η : ℂ) * Complex.I)).trace) s := by
      funext s
      simp only [hf, Function.comp, Complex.imCLM_apply]
      rw [symArr_of_isHermitian _ (CCalc_line_herm h V hh hV s), CCalc_im_ntr]
    rw [e1] at h1
    have h2 := h1.unique him
    rw [h2]
    simp only [Complex.imCLM_apply, Complex.neg_im, CCalc_card]
    rw [show (res (Matrix.of h + lam D N A) ((t : ℂ) + (η : ℂ) * Complex.I) * Matrix.of V *
          res (Matrix.of h + lam D N A) ((t : ℂ) + (η : ℂ) * Complex.I)).trace =
        (Matrix.of V * (res (Matrix.of h + lam D N A) ((t : ℂ) + (η : ℂ) * Complex.I) *
          res (Matrix.of h + lam D N A) ((t : ℂ) + (η : ℂ) * Complex.I))).trace by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]]
    ring
  have hGc : ∀ p q, Continuous (fun t : ℝ => res (Matrix.of h + lam D N A)
      ((t : ℂ) + (η : ℂ) * Complex.I) p q) := fun p q =>
    continuous_iff_continuousAt.2 fun t =>
      (CCalc_hasDerivAt_res_y _ hX η t hη p q).continuousAt
  set T : ℝ → ℂ := fun t => (Matrix.of V * res (Matrix.of h + lam D N A)
    ((t : ℂ) + (η : ℂ) * Complex.I)).trace with hT
  have hTd : ∀ t : ℝ, HasDerivAt T ((Matrix.of V * (res (Matrix.of h + lam D N A)
      ((t : ℂ) + (η : ℂ) * Complex.I) * res (Matrix.of h + lam D N A)
        ((t : ℂ) + (η : ℂ) * Complex.I))).trace) t := by
    intro t
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun p _ =>
        (CCalc_hasDerivAt_res_y _ hX η t hη p a).const_mul (Matrix.of V a p)))
    simpa [hT, Matrix.trace, Matrix.diag, Matrix.mul_apply] using this
  have hint : IntervalIntegrable (fun t : ℝ => (Matrix.of V * (res (Matrix.of h + lam D N A)
      ((t : ℂ) + (η : ℂ) * Complex.I) * res (Matrix.of h + lam D N A)
        ((t : ℂ) + (η : ℂ) * Complex.I))).trace) volume E₁ E₂ :=
    (CCalc_continuous_trace _ (fun t : ℝ => res (Matrix.of h + lam D N A)
      ((t : ℂ) + (η : ℂ) * Complex.I)) hGc).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hTd t) hint
  have hval : ((D * N : ℕ) : ℝ) * ∫ t in E₁..E₂, fderiv ℝ (fun x => f x t) h V =
      -((imRes (Matrix.of h + lam D N A) ((E₂ : ℂ) + (η : ℂ) * Complex.I) -
          imRes (Matrix.of h + lam D N A) ((E₁ : ℂ) + (η : ℂ) * Complex.I)) *
            Matrix.of V).trace.re := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
    have him : ∫ t in E₁..E₂, ((Matrix.of V * (res (Matrix.of h + lam D N A)
        ((t : ℂ) + (η : ℂ) * Complex.I) * res (Matrix.of h + lam D N A)
          ((t : ℂ) + (η : ℂ) * Complex.I))).trace).im = (T E₂ - T E₁).im := by
      have := Complex.imCLM.intervalIntegral_comp_comm hint
      simp only [Complex.imCLM_apply] at this
      rw [this, hftc]
    rw [him, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re,
      CCalc_trace_imRes _ _ hV, CCalc_trace_imRes _ _ hV, Complex.sub_im]
    by_cases hDN : D * N = 0
    · have hE : IsEmpty (Idx D N) := by
        rw [← Fintype.card_eq_zero_iff, CCalc_card]; exact hDN
      simp [hDN, hT, Matrix.trace]
    · have : ((D * N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hDN
      simp only [hT]
      field_simp
  have hderiv := hcomp.const_mul ((D * N : ℕ) : ℝ)
  rw [happ, hval] at hderiv
  have hfun : (fun s : ℝ => edgeCount D N A η E₁ E₂ (h + s • V)) = fun y =>
      ((D * N : ℕ) : ℝ) * ((fun x => ∫ t in E₁..E₂, f x t) ∘ fun s : ℝ => h + s • V) y := by
    funext s
    simp only [edgeCount, Function.comp, hf]
    rw [symArr_of_isHermitian _ (CCalc_line_herm h V hh hV s)]
  rw [hfun]
  exact hderiv

/-- `A` of (4.7) [2comVVt], composed with the Hermitian part of the array, is smooth for
`η > 0`. -/
theorem edgeCount_contDiff (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ)
    (hη : 0 < η) :
    ContDiff ℝ ∞ (fun h : Idx D N → Idx D N → ℂ => edgeCount D N A η E₁ E₂ (symArr h)) := by
  have hj := CCalc_contDiff_integrand D N A η hη
  have := ContDiff.parametric_intervalIntegral (μ := volume) (a := E₁) (b := E₂) (n := ⊤) hj
  exact contDiff_const.mul this

/-- The deterministic bound `|A| ≤ DN |E₂ - E₁| / η` for a Hermitian array (proof of
Lemma 4.3 [rescomY]). -/
theorem edgeCount_abs_le (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ) (hη : 0 < η)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    |edgeCount D N A η E₁ E₂ h| ≤ ((D * N : ℕ) : ℝ) * |E₂ - E₁| / η := by
  have hX : (Matrix.of h + lam D N A).IsHermitian := hh.add (lam_isHermitian D N A)
  have hb : ∀ y : ℝ, ‖(ntr (res (Matrix.of h + lam D N A) ((y : ℂ) + (η : ℂ) * Complex.I))).im‖ ≤
      η⁻¹ := by
    intro y
    have hz : 0 < ((y : ℂ) + (η : ℂ) * Complex.I).im := by simp [hη]
    have h1 := opNorm_res_le _ hX _ hz
    have hzi : ((y : ℂ) + (η : ℂ) * Complex.I).im = η := by simp
    rw [hzi] at h1
    refine (Complex.abs_im_le_norm _).trans ?_
    exact CCalc_norm_ntr_le _ _ (inv_nonneg.mpr hη.le) fun a =>
      (norm_apply_le_opNorm _ a a).trans h1
  have hI : ‖∫ y in E₁..E₂, (ntr (res (Matrix.of h + lam D N A)
      ((y : ℂ) + (η : ℂ) * Complex.I))).im‖ ≤ η⁻¹ * |E₂ - E₁| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y _ => hb y
  unfold edgeCount
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [Real.norm_eq_abs] at hI
  calc ((D * N : ℕ) : ℝ) * |∫ y in E₁..E₂, (ntr (res (Matrix.of h + lam D N A)
        ((y : ℂ) + (η : ℂ) * Complex.I))).im|
      ≤ ((D * N : ℕ) : ℝ) * (η⁻¹ * |E₂ - E₁|) :=
        mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg _)
    _ = ((D * N : ℕ) : ℝ) * |E₂ - E₁| / η := by field_simp

/-! ### Polynomials in letters and their Wirtinger derivatives -/

section Generic

variable {L : Type*}

/-- The value at `w` of the product of the letters `m`, the letter `l` having the value `ev l w`. -/
def CCalc_mono (ev : L → ℂ → ℂ) (m : List L) (w : ℂ) : ℂ := (m.map fun l => ev l w).prod

/-- The value of a sum of coefficient-weighted products of letters. -/
def CCalc_poly (ev : L → ℂ → ℂ) (P : List (ℂ × List L)) (w : ℂ) : ℂ :=
  (P.map fun t => t.1 * CCalc_mono ev t.2 w).sum

/-- The Wirtinger derivative selected by a flag: `∂_w` for `true`, `∂_{w̄}` for `false`. -/
def CCalc_dop : Bool → (ℂ → ℂ) → ℂ → ℂ
  | true => dW
  | false => dWbar

/-- The derivative of a product of letters by the product rule, given the derivative `ex` of
each letter as a sum of products of letters. -/
private def CCalc_dMono (ex : Bool → L → List (ℂ × List L)) (d : Bool) :
    List L → List (ℂ × List L)
  | [] => []
  | l :: m => (ex d l).map (fun t => (t.1, t.2 ++ m)) ++
      (CCalc_dMono ex d m).map (fun t => (t.1, l :: t.2))

/-- The derivative of a sum of products of letters. -/
private def CCalc_dPoly (ex : Bool → L → List (ℂ × List L)) (d : Bool)
    (P : List (ℂ × List L)) : List (ℂ × List L) :=
  P.flatMap fun t => (CCalc_dMono ex d t.2).map fun s => (t.1 * s.1, s.2)

variable (ev : L → ℂ → ℂ)

/-- The empty product is `1`. -/
private lemma CCalc_mono_nil (w : ℂ) : CCalc_mono ev [] w = 1 := by simp [CCalc_mono]

/-- The value of a product of letters is the first letter times the rest. -/
private lemma CCalc_mono_cons (l : L) (m : List L) (w : ℂ) :
    CCalc_mono ev (l :: m) w = ev l w * CCalc_mono ev m w := by simp [CCalc_mono]

/-- The value of a concatenation of products is the product of the values. -/
private lemma CCalc_mono_append (m m' : List L) (w : ℂ) :
    CCalc_mono ev (m ++ m') w = CCalc_mono ev m w * CCalc_mono ev m' w := by
  simp [CCalc_mono, List.prod_append]

/-- The empty sum is `0`. -/
private lemma CCalc_poly_nil (w : ℂ) : CCalc_poly ev [] w = 0 := by simp [CCalc_poly]

/-- The value of a sum is its first term plus the rest. -/
private lemma CCalc_poly_cons (t : ℂ × List L) (P : List (ℂ × List L)) (w : ℂ) :
    CCalc_poly ev (t :: P) w = t.1 * CCalc_mono ev t.2 w + CCalc_poly ev P w := by
  simp [CCalc_poly]

/-- The value of a concatenation of sums is the sum of the values. -/
private lemma CCalc_poly_append (P Q : List (ℂ × List L)) (w : ℂ) :
    CCalc_poly ev (P ++ Q) w = CCalc_poly ev P w + CCalc_poly ev Q w := by
  simp [CCalc_poly, List.sum_append]

/-- Appending the monomial `m` to every term multiplies the value by that of `m`. -/
private lemma CCalc_poly_map_append (Q : List (ℂ × List L)) (m : List L) (w : ℂ) :
    CCalc_poly ev (Q.map fun t => (t.1, t.2 ++ m)) w = CCalc_poly ev Q w * CCalc_mono ev m w := by
  induction Q with
  | nil => simp [CCalc_poly]
  | cons t Q ih =>
    rw [List.map_cons, CCalc_poly_cons, ih, CCalc_poly_cons, CCalc_mono_append]
    ring

/-- Prepending the letter `l` to every term multiplies the value by that of `l`. -/
private lemma CCalc_poly_map_cons (l : L) (Q : List (ℂ × List L)) (w : ℂ) :
    CCalc_poly ev (Q.map fun t => (t.1, l :: t.2)) w = ev l w * CCalc_poly ev Q w := by
  induction Q with
  | nil => simp [CCalc_poly]
  | cons t Q ih =>
    rw [List.map_cons, CCalc_poly_cons, ih, CCalc_poly_cons, CCalc_mono_cons]
    ring

/-- Multiplying every coefficient by `c₀` multiplies the value by `c₀`. -/
private lemma CCalc_poly_map_mul (c₀ : ℂ) (Q : List (ℂ × List L)) (w : ℂ) :
    CCalc_poly ev (Q.map fun s => (c₀ * s.1, s.2)) w = c₀ * CCalc_poly ev Q w := by
  induction Q with
  | nil => simp [CCalc_poly]
  | cons t Q ih =>
    rw [List.map_cons, CCalc_poly_cons, ih, CCalc_poly_cons]
    ring

/-! #### Derivation rules -/

private lemma CCalc_dop_add (d : Bool) {F G : ℂ → ℂ} {w : ℂ} (hF : DifferentiableAt ℝ F w)
    (hG : DifferentiableAt ℝ G w) :
    CCalc_dop d (fun x => F x + G x) w = CCalc_dop d F w + CCalc_dop d G w := by
  have e : fderiv ℝ (fun x => F x + G x) w = fderiv ℝ F w + fderiv ℝ G w := fderiv_fun_add hF hG
  cases d <;> simp only [CCalc_dop, dW, dWbar, e, _root_.add_apply] <;> ring

/-- The Wirtinger derivative of a constant multiple. -/
private lemma CCalc_dop_const_mul (d : Bool) {F : ℂ → ℂ} {w : ℂ} (c : ℂ)
    (hF : DifferentiableAt ℝ F w) :
    CCalc_dop d (fun x => c * F x) w = c * CCalc_dop d F w := by
  have e : fderiv ℝ (fun x => c * F x) w = c • fderiv ℝ F w := fderiv_const_mul hF c
  cases d <;> simp only [CCalc_dop, dW, dWbar, e, _root_.smul_apply, smul_eq_mul] <;> ring

/-- The product rule for the Wirtinger derivatives. -/
private lemma CCalc_dop_mul (d : Bool) {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w)
    (hg : DifferentiableAt ℝ g w) :
    CCalc_dop d (fun x => f x * g x) w = CCalc_dop d f w * g w + f w * CCalc_dop d g w := by
  cases d
  · exact (dW_mul hf hg).2
  · exact (dW_mul hf hg).1

/-- The Wirtinger derivatives of the constant `0` vanish. -/
private lemma CCalc_dop_zero (d : Bool) : CCalc_dop d (fun _ => (0 : ℂ)) = fun _ => 0 := by
  funext w
  cases d <;> simp [CCalc_dop, dW, dWbar]

/-- The Wirtinger derivatives of the constant `1` vanish. -/
private lemma CCalc_dop_one (d : Bool) : CCalc_dop d (fun _ => (1 : ℂ)) = fun _ => 0 := by
  funext w
  cases d <;> simp [CCalc_dop, dW, dWbar]

variable (hev : ∀ l w, DifferentiableAt ℝ (ev l) w)
include hev

/-- A product of differentiable letters is differentiable. -/
private lemma CCalc_mono_diff (m : List L) (w : ℂ) : DifferentiableAt ℝ (CCalc_mono ev m) w := by
  induction m with
  | nil =>
    have e : CCalc_mono ev [] = fun _ => 1 := by funext x; exact CCalc_mono_nil ev x
    rw [e]; exact differentiableAt_const _
  | cons l m ih =>
    have e : CCalc_mono ev (l :: m) = fun x => ev l x * CCalc_mono ev m x := by
      funext x; exact CCalc_mono_cons ev l m x
    rw [e]
    exact (hev l w).mul ih

/-- A sum of products of differentiable letters is differentiable. -/
private lemma CCalc_poly_diff (P : List (ℂ × List L)) (w : ℂ) :
    DifferentiableAt ℝ (CCalc_poly ev P) w := by
  induction P with
  | nil =>
    have e : CCalc_poly ev [] = fun _ => 0 := by funext x; exact CCalc_poly_nil ev x
    rw [e]; exact differentiableAt_const _
  | cons t P ih =>
    have e : CCalc_poly ev (t :: P) = fun x => t.1 * CCalc_mono ev t.2 x + CCalc_poly ev P x := by
      funext x; exact CCalc_poly_cons ev t P x
    rw [e]
    exact ((differentiableAt_const _).mul (CCalc_mono_diff ev hev t.2 w)).add ih

variable (ex : Bool → L → List (ℂ × List L))
  (hex : ∀ d l, CCalc_dop d (ev l) = CCalc_poly ev (ex d l))
include hex

/-- The Wirtinger derivative of a product of letters is the sum given by the product rule. -/
private lemma CCalc_dop_mono (d : Bool) (m : List L) :
    CCalc_dop d (CCalc_mono ev m) = CCalc_poly ev (CCalc_dMono ex d m) := by
  induction m with
  | nil =>
    have e : CCalc_mono ev [] = fun _ => 1 := by funext x; exact CCalc_mono_nil ev x
    rw [e, CCalc_dop_one]
    funext w
    simp [CCalc_dMono, CCalc_poly]
  | cons l m ih =>
    have e : CCalc_mono ev (l :: m) = fun x => ev l x * CCalc_mono ev m x := by
      funext x; exact CCalc_mono_cons ev l m x
    funext w
    rw [e, CCalc_dop_mul d (hev l w) (CCalc_mono_diff ev hev m w), congrFun (hex d l) w,
      congrFun ih w]
    simp only [CCalc_dMono, CCalc_poly_append, CCalc_poly_map_append, CCalc_poly_map_cons]

/-- The Wirtinger derivative of a sum of products of letters is `CCalc_dPoly` of it. -/
private lemma CCalc_dop_poly (d : Bool) (P : List (ℂ × List L)) :
    CCalc_dop d (CCalc_poly ev P) = CCalc_poly ev (CCalc_dPoly ex d P) := by
  induction P with
  | nil =>
    have e : CCalc_poly ev [] = fun _ => 0 := by funext x; exact CCalc_poly_nil ev x
    rw [e, CCalc_dop_zero]
    funext w
    simp [CCalc_dPoly, CCalc_poly]
  | cons t P ih =>
    have e : CCalc_poly ev (t :: P) = fun x => t.1 * CCalc_mono ev t.2 x + CCalc_poly ev P x := by
      funext x; exact CCalc_poly_cons ev t P x
    funext w
    rw [e, CCalc_dop_add d (F := fun x => t.1 * CCalc_mono ev t.2 x) (G := CCalc_poly ev P)
      ((differentiableAt_const _).mul (CCalc_mono_diff ev hev t.2 w))
      (CCalc_poly_diff ev hev P w), CCalc_dop_const_mul d t.1 (CCalc_mono_diff ev hev t.2 w),
      congrFun (CCalc_dop_mono ev hev ex hex d t.2) w, congrFun ih w]
    simp only [CCalc_dPoly, List.flatMap_cons, CCalc_poly_append, CCalc_poly_map_mul]

/-- Iterated Wirtinger derivatives of a sum of products of letters. -/
private lemma CCalc_dop_iter (d : Bool) (n : ℕ) (P : List (ℂ × List L)) :
    (CCalc_dop d)^[n] (CCalc_poly ev P) = CCalc_poly ev ((CCalc_dPoly ex d)^[n] P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      CCalc_dop_poly ev hev ex hex]



end Generic

section Bounds

variable {L : Type*}

/-! #### Weights and bounds -/

/-- The sum of the moduli of the coefficients. -/
private def CCalc_wt (P : List (ℂ × List L)) : ℝ := (P.map fun t => ‖t.1‖).sum

/-- The product of the bounds of the letters of a monomial. -/
private def CCalc_om (bd : L → ℝ) (m : List L) : ℝ := (m.map bd).prod

/-- The weight of a sum is that of its first term plus the rest. -/
private lemma CCalc_wt_cons (t : ℂ × List L) (P : List (ℂ × List L)) :
    CCalc_wt (t :: P) = ‖t.1‖ + CCalc_wt P := by simp [CCalc_wt]

/-- The weight of a concatenation is the sum of the weights. -/
private lemma CCalc_wt_append (P Q : List (ℂ × List L)) :
    CCalc_wt (P ++ Q) = CCalc_wt P + CCalc_wt Q := by
  simp [CCalc_wt, List.sum_append]

/-- Appending a monomial to every term keeps the weight. -/
private lemma CCalc_wt_map_append (Q : List (ℂ × List L)) (m : List L) :
    CCalc_wt (Q.map fun t => (t.1, t.2 ++ m)) = CCalc_wt Q := by
  simp [CCalc_wt, Function.comp_def]

/-- Prepending a letter to every term keeps the weight. -/
private lemma CCalc_wt_map_cons (l : L) (Q : List (ℂ × List L)) :
    CCalc_wt (Q.map fun t => (t.1, l :: t.2)) = CCalc_wt Q := by
  simp [CCalc_wt, Function.comp_def]

/-- Multiplying every coefficient by `c₀` multiplies the weight by `‖c₀‖`. -/
private lemma CCalc_wt_map_mul (c₀ : ℂ) (Q : List (ℂ × List L)) :
    CCalc_wt (Q.map fun s => (c₀ * s.1, s.2)) = ‖c₀‖ * CCalc_wt Q := by
  induction Q with
  | nil => simp [CCalc_wt]
  | cons t Q ih =>
    rw [List.map_cons, CCalc_wt_cons, ih, CCalc_wt_cons, norm_mul]
    ring

/-- The bound of the empty monomial is `1`. -/
private lemma CCalc_om_nil (bd : L → ℝ) : CCalc_om bd [] = 1 := by simp [CCalc_om]

/-- The bound of a monomial is the bound of its first letter times the rest. -/
private lemma CCalc_om_cons (bd : L → ℝ) (l : L) (m : List L) :
    CCalc_om bd (l :: m) = bd l * CCalc_om bd m := by simp [CCalc_om]

/-- The bound of a concatenation is the product of the bounds. -/
private lemma CCalc_om_append (bd : L → ℝ) (m m' : List L) :
    CCalc_om bd (m ++ m') = CCalc_om bd m * CCalc_om bd m' := by
  simp [CCalc_om, List.prod_append]

/-- The bound of a monomial is nonnegative when the bound of every letter is. -/
private lemma CCalc_om_nonneg (bd : L → ℝ) (hbd : ∀ l, 0 ≤ bd l) (m : List L) :
    0 ≤ CCalc_om bd m := by
  induction m with
  | nil => simp [CCalc_om_nil]
  | cons l m ih => rw [CCalc_om_cons]; exact mul_nonneg (hbd l) ih

variable (ex : Bool → L → List (ℂ × List L)) (d : Bool)

/-- One derivative of a monomial multiplies the weight by at most the number of letters times
the largest weight of the derivative of a letter. -/
private lemma CCalc_wt_dMono_le (E : ℝ) (hE : ∀ l, CCalc_wt (ex d l) ≤ E) (m : List L) :
    CCalc_wt (CCalc_dMono ex d m) ≤ m.length * E := by
  induction m with
  | nil => simp [CCalc_dMono, CCalc_wt]
  | cons l m ih =>
    simp only [CCalc_dMono, CCalc_wt_append, CCalc_wt_map_append, CCalc_wt_map_cons,
      List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [hE l]

/-- One derivative of a polynomial whose monomials all have `m₀` letters. -/
private lemma CCalc_wt_dPoly_le (E : ℝ) (hE : ∀ l, CCalc_wt (ex d l) ≤ E) (m₀ : ℕ)
    (P : List (ℂ × List L)) (hP : ∀ t ∈ P, t.2.length = m₀) :
    CCalc_wt (CCalc_dPoly ex d P) ≤ m₀ * E * CCalc_wt P := by
  induction P with
  | nil => simp [CCalc_dPoly, CCalc_wt]
  | cons t P ih =>
    have ih' := ih fun u hu => hP u (List.mem_cons_of_mem _ hu)
    have h1 := CCalc_wt_dMono_le ex d E hE t.2
    rw [hP t List.mem_cons_self] at h1
    simp only [CCalc_dPoly, List.flatMap_cons, CCalc_wt_append, CCalc_wt_map_mul] at ih' ⊢
    rw [CCalc_wt_cons]
    have h2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg t.1)
    nlinarith

variable (bd : L → ℝ)

/-- One derivative of a monomial multiplies the bound by at most `Γ`, when each letter's derivative
terms do. -/
private lemma CCalc_dMono_om (Γ : ℝ) (hbd : ∀ l, 0 ≤ bd l)
    (hex : ∀ l, ∀ s ∈ ex d l, CCalc_om bd s.2 ≤ Γ * bd l) (m : List L) :
    ∀ t ∈ CCalc_dMono ex d m, CCalc_om bd t.2 ≤ Γ * CCalc_om bd m := by
  induction m with
  | nil => intro t ht; simp [CCalc_dMono] at ht
  | cons l m ih =>
    intro t ht
    simp only [CCalc_dMono, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨t', ht', rfl⟩
    · simp only [CCalc_om_append, CCalc_om_cons]
      calc CCalc_om bd s.2 * CCalc_om bd m ≤ Γ * bd l * CCalc_om bd m :=
            mul_le_mul_of_nonneg_right (hex l s hs) (CCalc_om_nonneg bd hbd m)
        _ = Γ * (bd l * CCalc_om bd m) := by ring
    · simp only [CCalc_om_cons]
      calc bd l * CCalc_om bd t'.2 ≤ bd l * (Γ * CCalc_om bd m) :=
            mul_le_mul_of_nonneg_left (ih t' ht') (hbd l)
        _ = Γ * (bd l * CCalc_om bd m) := by ring

/-- One derivative of a monomial adds one letter, when each letter's derivative terms have two. -/
private lemma CCalc_dMono_len (hex : ∀ l, ∀ s ∈ ex d l, s.2.length = 2) (m : List L) :
    ∀ t ∈ CCalc_dMono ex d m, t.2.length = m.length + 1 := by
  induction m with
  | nil => intro t ht; simp [CCalc_dMono] at ht
  | cons l m ih =>
    intro t ht
    simp only [CCalc_dMono, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨t', ht', rfl⟩
    · simp only [List.length_append, hex l s hs, List.length_cons]; omega
    · simp [ih t' ht']

/-- The letters of a derivative are letters of the monomial or letters of the derivative of one of
its letters. -/
private lemma CCalc_dMono_mem (P Q : L → Prop) (hPQ : ∀ l, P l → Q l)
    (hex : ∀ l, P l → ∀ s ∈ ex d l, ∀ e ∈ s.2, Q e) (m : List L) :
    (∀ l ∈ m, P l) → ∀ t ∈ CCalc_dMono ex d m, ∀ e ∈ t.2, Q e := by
  induction m with
  | nil => intro _ t ht; simp [CCalc_dMono] at ht
  | cons l m ih =>
    intro hm t ht e he
    simp only [CCalc_dMono, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨t', ht', rfl⟩
    · rcases List.mem_append.mp he with he | he
      · exact hex l (hm l List.mem_cons_self) s hs e he
      · exact hPQ e (hm e (List.mem_cons_of_mem _ he))
    · rcases List.mem_cons.mp he with rfl | he
      · exact hPQ _ (hm _ List.mem_cons_self)
      · exact ih (fun l' hl' => hm l' (List.mem_cons_of_mem _ hl')) t' ht' e he

variable (ev : L → ℂ → ℂ)

/-- The value of a monomial is bounded by the product of the bounds of its letters. -/
private lemma CCalc_mono_norm_le (w : ℂ) (m : List L) (hm : ∀ l ∈ m, ‖ev l w‖ ≤ bd l) :
    ‖CCalc_mono ev m w‖ ≤ CCalc_om bd m := by
  induction m with
  | nil => simp [CCalc_mono_nil, CCalc_om_nil]
  | cons l m ih =>
    have ih' := ih fun l' hl' => hm l' (List.mem_cons_of_mem _ hl')
    have h1 := hm l List.mem_cons_self
    rw [CCalc_mono_cons, CCalc_om_cons, norm_mul]
    exact mul_le_mul h1 ih' (norm_nonneg _) ((norm_nonneg _).trans h1)

/-- The value of a sum of monomials is bounded by the weight times the largest monomial bound. -/
private lemma CCalc_poly_norm_le (w : ℂ) (P : List (ℂ × List L))
    (hl : ∀ t ∈ P, ∀ l ∈ t.2, ‖ev l w‖ ≤ bd l) (B : ℝ) (hB : ∀ t ∈ P, CCalc_om bd t.2 ≤ B) :
    ‖CCalc_poly ev P w‖ ≤ CCalc_wt P * B := by
  induction P with
  | nil => simp [CCalc_poly_nil, CCalc_wt]
  | cons t P ih =>
    have ih' := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))
      (fun u hu => hB u (List.mem_cons_of_mem _ hu))
    have h1 := (CCalc_mono_norm_le bd ev w t.2 (hl t List.mem_cons_self)).trans
      (hB t List.mem_cons_self)
    rw [CCalc_poly_cons, CCalc_wt_cons]
    calc ‖t.1 * CCalc_mono ev t.2 w + CCalc_poly ev P w‖
        ≤ ‖t.1 * CCalc_mono ev t.2 w‖ + ‖CCalc_poly ev P w‖ := norm_add_le _ _
      _ ≤ ‖t.1‖ * B + CCalc_wt P * B := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) ih'
      _ = (‖t.1‖ + CCalc_wt P) * B := by ring

end Bounds

/-! ### The letters of the structure of `∂^p ∂̄^q F(A)` -/

/-- The letters: the entries `G_{ab}`, `G^*_{ab}` and `(Im G)_{ab}` of the resolvent at one of the
`2n` points, with `a, b ∈ {0, 1}` standing for the two indices `i`, `j` of the substituted entry,
and the partial derivative `∂_{k₁} ⋯ ∂_{k_l} F` of `F` at the array `A`. -/
private inductive CCalc_Letter (n : ℕ) : Type
  | G (r : Fin n × Fin 2) (a b : Fin 2)
  | Gs (r : Fin n × Fin 2) (a b : Fin 2)
  | I (r : Fin n × Fin 2) (a b : Fin 2)
  | Psi (ks : List (Fin n))

/-- The derivative of a partial derivative of `F` along the indices `l`: the terms
`∓c ψ_{k::ks} (Im G)_{ab}` at the two points of `A_k`. -/
private def CCalc_psiExp {n : ℕ} (c : ℂ) (a b : Fin 2) (ks : List (Fin n)) :
    List (Fin n) → List (ℂ × List (CCalc_Letter n))
  | [] => []
  | k :: l => [(-c, [.Psi (k :: ks), .I (k, 1) a b]), (c, [.Psi (k :: ks), .I (k, 0) a b])] ++
      CCalc_psiExp c a b ks l

/-- The derivative of a letter, `c = 1/2` on the diagonal and `1` off it: `∂_w G_{ab} =
-c G_{a i} G_{j b}`, the derivative of `(Im G)_{ab}` with one factor `Im G` per term, and the
derivative of a partial derivative of `F` through the `A_k`. -/
private def CCalc_ex {n : ℕ} (c : ℂ) : Bool → CCalc_Letter n → List (ℂ × List (CCalc_Letter n))
  | true, .G r a b => [(-c, [.G r a 0, .G r 1 b])]
  | false, .G r a b => [(-c, [.G r a 1, .G r 0 b])]
  | true, .Gs r a b => [(-c, [.Gs r a 0, .Gs r 1 b])]
  | false, .Gs r a b => [(-c, [.Gs r a 1, .Gs r 0 b])]
  | true, .I r a b => [(-c, [.I r a 0, .G r 1 b]), (-c, [.Gs r a 0, .I r 1 b])]
  | false, .I r a b => [(-c, [.I r a 1, .G r 0 b]), (-c, [.Gs r a 1, .I r 0 b])]
  | true, .Psi ks => CCalc_psiExp c 1 0 ks (List.finRange n)
  | false, .Psi ks => CCalc_psiExp c 0 1 ks (List.finRange n)

/-- The bound of a letter: `Γ` for `G` and `G^*`, `Γ_I` for `Im G`, `B_F` for derivatives of `F`. -/
private def CCalc_bd {n : ℕ} (BF Γ ΓI : ℝ) : CCalc_Letter n → ℝ
  | .G _ _ _ => Γ
  | .Gs _ _ _ => Γ
  | .I _ _ _ => ΓI
  | .Psi _ => BF

/-- After `Lv` derivatives only derivatives of `F` of order `1 ≤ l ≤ Lv` occur. -/
private def CCalc_val {n : ℕ} (Lv : ℕ) : CCalc_Letter n → Prop
  | .Psi ks => 1 ≤ ks.length ∧ ks.length ≤ Lv
  | _ => True

/-- The bound `(2n + 2)^{Lv} Lv!` on the weight after `Lv` derivatives. -/
private def CCalc_K (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | Lv + 1 => CCalc_K n Lv * ((2 * n + 2) * (Lv + 1))

/-- The weight bound `K` is positive. -/
private lemma CCalc_K_pos (n Lv : ℕ) : 0 < CCalc_K n Lv := by
  induction Lv with
  | zero => simp [CCalc_K]
  | succ Lv ih => simp only [CCalc_K]; positivity

section Letters

variable {n : ℕ}

/-- Every term of `CCalc_psiExp` has two letters. -/
private lemma CCalc_psiExp_len (c : ℂ) (a b : Fin 2) (ks : List (Fin n)) (l : List (Fin n)) :
    ∀ s ∈ CCalc_psiExp c a b ks l, s.2.length = 2 := by
  induction l with
  | nil => intro s hs; simp [CCalc_psiExp] at hs
  | cons k l ih =>
    intro s hs
    simp only [CCalc_psiExp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with (rfl | rfl) | hs
    · rfl
    · rfl
    · exact ih s hs

/-- Every term of `CCalc_psiExp` is a partial derivative of `F` times one `Im G`. -/
private lemma CCalc_psiExp_mem (c : ℂ) (a b : Fin 2) (ks : List (Fin n)) (l : List (Fin n)) :
    ∀ s ∈ CCalc_psiExp c a b ks l, ∃ (k : Fin n) (r : Fin n × Fin 2),
      s.2 = [.Psi (k :: ks), .I r a b] := by
  induction l with
  | nil => intro s hs; simp [CCalc_psiExp] at hs
  | cons k l ih =>
    intro s hs
    simp only [CCalc_psiExp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with (rfl | rfl) | hs
    · exact ⟨k, (k, 1), rfl⟩
    · exact ⟨k, (k, 0), rfl⟩
    · exact ih s hs

/-- The weight of `CCalc_psiExp` is at most twice the number of indices. -/
private lemma CCalc_psiExp_wt (c : ℂ) (hc : ‖c‖ ≤ 1) (a b : Fin 2) (ks : List (Fin n))
    (l : List (Fin n)) : CCalc_wt (CCalc_psiExp c a b ks l) ≤ 2 * l.length := by
  induction l with
  | nil => simp [CCalc_psiExp, CCalc_wt]
  | cons k l ih =>
    simp only [CCalc_psiExp, CCalc_wt_append, List.length_cons, Nat.cast_add, Nat.cast_one]
    simp only [CCalc_wt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, norm_neg] at ih ⊢
    linarith

/-- The weight of `CCalc_psiExp` over all `n` indices is at most `2n`. -/
private lemma CCalc_psiExp_wt' (c : ℂ) (hc : ‖c‖ ≤ 1) (a b : Fin 2) (ks : List (Fin n)) :
    CCalc_wt (CCalc_psiExp c a b ks (List.finRange n)) ≤ 2 * n := by
  have := CCalc_psiExp_wt c hc a b ks (List.finRange n)
  simpa only [List.length_finRange] using this

/-- Every term of the derivative of a letter has two letters. -/
private lemma CCalc_ex_len (c : ℂ) (d : Bool) (l : CCalc_Letter n) :
    ∀ s ∈ CCalc_ex c d l, s.2.length = 2 := by
  cases d <;> cases l
  all_goals simp only [CCalc_ex]
  all_goals first
    | exact CCalc_psiExp_len _ _ _ _ _
    | (intro s hs
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
       rcases hs with rfl | rfl <;> rfl)

/-- The derivative of a letter has weight at most `2n + 2`. -/
private lemma CCalc_ex_wt (c : ℂ) (hc : ‖c‖ ≤ 1) (d : Bool) (l : CCalc_Letter n) :
    CCalc_wt (CCalc_ex c d l) ≤ 2 * n + 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  cases d <;> cases l
  all_goals simp only [CCalc_ex]
  all_goals first
    | exact (CCalc_psiExp_wt' c hc _ _ _).trans (by linarith)
    | (simp only [CCalc_wt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, norm_neg]
       linarith)

/-- A derivative of a letter has at most `Γ` times the bound of the letter. -/
private lemma CCalc_ex_om (c : ℂ) (BF Γ ΓI : ℝ) (hBF : 0 ≤ BF) (hΓI : 0 ≤ ΓI) (hle : ΓI ≤ Γ)
    (d : Bool) (l : CCalc_Letter n) :
    ∀ s ∈ CCalc_ex c d l, CCalc_om (CCalc_bd BF Γ ΓI) s.2 ≤ Γ * CCalc_bd BF Γ ΓI l := by
  have hΓ : 0 ≤ Γ := hΓI.trans hle
  have key : ∀ (a b : Fin 2) (ks : List (Fin n)) (l' : List (Fin n)),
      ∀ s ∈ CCalc_psiExp c a b ks l', CCalc_om (CCalc_bd BF Γ ΓI) s.2 ≤ Γ * BF := by
    intro a b ks l'
    induction l' with
    | nil => intro s hs; simp [CCalc_psiExp] at hs
    | cons k l' ih =>
      intro s hs
      simp only [CCalc_psiExp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with (rfl | rfl) | hs
      · simp only [CCalc_om, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          CCalc_bd]
        nlinarith
      · simp only [CCalc_om, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          CCalc_bd]
        nlinarith
      · exact ih s hs
  cases d <;> cases l
  all_goals simp only [CCalc_ex, CCalc_bd]
  all_goals first
    | exact key _ _ _ _
    | (intro s hs
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
       rcases hs with rfl | rfl <;>
       simp only [CCalc_om, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          CCalc_bd] <;> nlinarith)

/-- The sharper bound for the derivative of a partial derivative of `F`: `B_F Γ_I`. -/
private lemma CCalc_psiExp_om (c : ℂ) (BF Γ ΓI : ℝ) (a b : Fin 2) (ks : List (Fin n))
    (l : List (Fin n)) :
    ∀ s ∈ CCalc_psiExp c a b ks l, CCalc_om (CCalc_bd BF Γ ΓI) s.2 ≤ BF * ΓI := by
  induction l with
  | nil => intro s hs; simp [CCalc_psiExp] at hs
  | cons k l ih =>
    intro s hs
    simp only [CCalc_psiExp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with (rfl | rfl) | hs
    · simp [CCalc_om, CCalc_bd]
    · simp [CCalc_om, CCalc_bd]
    · exact ih s hs

/-- The letters of the derivative of an admissible letter are admissible one level higher. -/
private lemma CCalc_ex_val (c : ℂ) (d : Bool) (Lv : ℕ) (l : CCalc_Letter n) (hl : CCalc_val Lv l) :
    ∀ s ∈ CCalc_ex c d l, ∀ e ∈ s.2, CCalc_val (Lv + 1) e := by
  have key : ∀ (a b : Fin 2) (ks : List (Fin n)) (l' : List (Fin n)), ks.length ≤ Lv →
      ∀ s ∈ CCalc_psiExp c a b ks l', ∀ e ∈ s.2, CCalc_val (Lv + 1) e := by
    intro a b ks l' hks
    induction l' with
    | nil => intro s hs; simp [CCalc_psiExp] at hs
    | cons k l' ih =>
      intro s hs e he
      simp only [CCalc_psiExp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with (rfl | rfl) | hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · simp only [CCalc_val, List.length_cons]; omega
        · trivial
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · simp only [CCalc_val, List.length_cons]; omega
        · trivial
      · exact ih s hs e he
  cases d <;> cases l
  all_goals simp only [CCalc_ex]
  all_goals first
    | exact key _ _ _ _ hl.2
    | (intro s hs e he
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
       rcases hs with rfl | rfl <;>
       simp only [List.mem_cons, List.not_mem_nil, or_false] at he <;>
       rcases he with rfl | rfl <;> trivial)

/-- An admissible letter stays admissible one level higher. -/
private lemma CCalc_val_mono (Lv : ℕ) (l : CCalc_Letter n) (hl : CCalc_val Lv l) :
    CCalc_val (Lv + 1) l := by
  cases l <;> simp only [CCalc_val] at hl ⊢
  omega

/-- The invariant of the polynomial reached after `Lv` derivatives: every monomial has `Lv + 1`
letters of admissible order and bound at most `bound`, and the weight is at most `K Lv`. -/
private def CCalc_Good (n : ℕ) (BF Γ ΓI : ℝ) (Lv : ℕ) (bound : ℝ)
    (P : List (ℂ × List (CCalc_Letter n))) : Prop :=
  (∀ t ∈ P, t.2.length = Lv + 1 ∧ (∀ l ∈ t.2, CCalc_val Lv l) ∧
    CCalc_om (CCalc_bd BF Γ ΓI) t.2 ≤ bound) ∧ CCalc_wt P ≤ CCalc_K n Lv

/-- One derivative keeps the invariant: the bound is multiplied by `Γ` and the weight is at most
`K (Lv + 1)`. -/
private lemma CCalc_good_step (c : ℂ) (hc : ‖c‖ ≤ 1) (BF Γ ΓI : ℝ) (hBF : 0 ≤ BF)
    (hΓI : 0 ≤ ΓI) (hle : ΓI ≤ Γ) (d : Bool) (Lv : ℕ) (bound : ℝ)
    (P : List (ℂ × List (CCalc_Letter n))) (hP : CCalc_Good n BF Γ ΓI Lv bound P) :
    CCalc_Good n BF Γ ΓI (Lv + 1) (Γ * bound) (CCalc_dPoly (CCalc_ex c) d P) := by
  have hΓ : 0 ≤ Γ := hΓI.trans hle
  obtain ⟨hm, hw⟩ := hP
  have hbd : ∀ l : CCalc_Letter n, 0 ≤ CCalc_bd BF Γ ΓI l := by
    intro l; cases l <;> simp [CCalc_bd, hBF, hΓ, hΓI]
  refine ⟨fun t ht => ?_, ?_⟩
  · simp only [CCalc_dPoly, List.mem_flatMap, List.mem_map] at ht
    obtain ⟨t0, ht0, s, hs, rfl⟩ := ht
    obtain ⟨hlen, hval, hom⟩ := hm t0 ht0
    refine ⟨?_, ?_, ?_⟩
    · rw [CCalc_dMono_len (CCalc_ex c) d (fun l s hs => CCalc_ex_len c d l s hs) t0.2 s hs, hlen]
    · exact CCalc_dMono_mem (CCalc_ex c) d (CCalc_val Lv) (CCalc_val (Lv + 1))
        (fun l hl => CCalc_val_mono Lv l hl) (fun l hl => CCalc_ex_val c d Lv l hl) t0.2 hval s hs
    · exact (CCalc_dMono_om (CCalc_ex c) d (CCalc_bd BF Γ ΓI) Γ hbd
        (fun l s hs => CCalc_ex_om c BF Γ ΓI hBF hΓI hle d l s hs) t0.2 s hs).trans
        (mul_le_mul_of_nonneg_left hom hΓ)
  · have h1 := CCalc_wt_dPoly_le (CCalc_ex c) d (2 * n + 2) (fun l => CCalc_ex_wt c hc d l)
      (Lv + 1) P (fun t ht => (hm t ht).1)
    have h2 : (((Lv + 1 : ℕ) : ℝ)) * (2 * n + 2) * CCalc_wt P ≤
        ((Lv + 1 : ℕ) : ℝ) * (2 * n + 2) * CCalc_K n Lv :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    calc CCalc_wt (CCalc_dPoly (CCalc_ex c) d P)
        ≤ ((Lv + 1 : ℕ) : ℝ) * (2 * n + 2) * CCalc_wt P := h1
      _ ≤ ((Lv + 1 : ℕ) : ℝ) * (2 * n + 2) * CCalc_K n Lv := h2
      _ = CCalc_K n (Lv + 1) := by simp only [CCalc_K]; push_cast; ring

/-- The invariant after `a` more derivatives in the same direction. -/
private lemma CCalc_good_iter (c : ℂ) (hc : ‖c‖ ≤ 1) (BF Γ ΓI : ℝ) (hBF : 0 ≤ BF)
    (hΓI : 0 ≤ ΓI) (hle : ΓI ≤ Γ) (d : Bool) (Lv : ℕ) (bound : ℝ)
    (P : List (ℂ × List (CCalc_Letter n))) (hP : CCalc_Good n BF Γ ΓI Lv bound P) (a : ℕ) :
    CCalc_Good n BF Γ ΓI (Lv + a) (Γ ^ a * bound) ((CCalc_dPoly (CCalc_ex c) d)^[a] P) := by
  induction a with
  | zero => simpa using hP
  | succ a ih =>
    have h := CCalc_good_step c hc BF Γ ΓI hBF hΓI hle d (Lv + a) _ _ ih
    rw [Function.iterate_succ_apply']
    have e : Γ * (Γ ^ a * bound) = Γ ^ (a + 1) * bound := by ring
    rw [e] at h
    simpa only [← add_assoc] using h

/-- The value `F(A)` as a one-term polynomial in the letter `Psi []`. -/
private def CCalc_P0 {n : ℕ} : List (ℂ × List (CCalc_Letter n)) := [(1, [.Psi []])]

/-- The first derivative of `F(A)` has the invariant at level `1` with bound `B_F Γ_I`. -/
private lemma CCalc_good_Q0 (c : ℂ) (hc : ‖c‖ ≤ 1) (BF Γ ΓI : ℝ) (d : Bool) :
    CCalc_Good n BF Γ ΓI 1 (BF * ΓI) (CCalc_dPoly (CCalc_ex c) d CCalc_P0) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · simp only [CCalc_dPoly, CCalc_P0, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_map, CCalc_dMono, List.map_nil] at ht
    obtain ⟨s, ⟨s0, hs0, rfl⟩, rfl⟩ := ht
    have hs0' : s0 ∈ CCalc_psiExp c (if d then 1 else 0) (if d then 0 else 1) []
        (List.finRange n) := by
      cases d <;> simpa [CCalc_ex] using hs0
    obtain ⟨k, r, hk⟩ := CCalc_psiExp_mem _ _ _ _ _ s0 hs0'
    refine ⟨?_, ?_, ?_⟩
    · simp [hk]
    · intro l hl
      simp only [hk, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [CCalc_val]
    · have := CCalc_psiExp_om c BF Γ ΓI _ _ _ _ s0 hs0'
      simpa using this
  · have h1 := CCalc_wt_dPoly_le (CCalc_ex c) d (2 * n + 2) (fun l => CCalc_ex_wt c hc d l) 1
      (CCalc_P0 (n := n)) (by
        intro t ht
        simp only [CCalc_P0, List.mem_singleton] at ht
        subst ht
        rfl)
    have h2 : CCalc_wt (CCalc_P0 (n := n)) = 1 := by simp [CCalc_P0, CCalc_wt]
    rw [h2] at h1
    simp only [CCalc_K]
    push_cast at h1 ⊢
    linarith

/-- After `p + q ≥ 1` derivatives, `∂_w^p ∂_{w̄}^q F(A)` is a polynomial in the letters with the
invariant at level `p + q` and bound `B_F Γ_I Γ^{p+q-1}`. -/
private lemma CCalc_wirt_good (ev : CCalc_Letter n → ℂ → ℂ)
    (hev : ∀ l w, DifferentiableAt ℝ (ev l) w) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (hex : ∀ d l, CCalc_dop d (ev l) = CCalc_poly ev (CCalc_ex c d l)) (BF Γ ΓI : ℝ)
    (hBF : 0 ≤ BF) (hΓI : 0 ≤ ΓI) (hle : ΓI ≤ Γ) (p q : ℕ) (hpq : 1 ≤ p + q) :
    ∃ P : List (ℂ × List (CCalc_Letter n)),
      CCalc_Good n BF Γ ΓI (p + q) (Γ ^ (p + q - 1) * (BF * ΓI)) P ∧
        (CCalc_dop true)^[p] ((CCalc_dop false)^[q] (CCalc_poly ev CCalc_P0)) =
          CCalc_poly ev P := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    refine ⟨(CCalc_dPoly (CCalc_ex c) true)^[p'] (CCalc_dPoly (CCalc_ex c) true CCalc_P0), ?_, ?_⟩
    · have := CCalc_good_iter (n := n) c hc BF Γ ΓI hBF hΓI hle true 1 _ _
        (CCalc_good_Q0 (n := n) c hc BF Γ ΓI true) p'
      have e1 : 1 + p' = p' + 1 + 0 := by omega
      have e2 : p' + 1 + 0 - 1 = p' := by omega
      rw [e1] at this
      rw [e2]
      exact this
    · rw [Function.iterate_zero_apply, CCalc_dop_iter ev hev (CCalc_ex c) hex true,
        Function.iterate_succ_apply]
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    refine ⟨(CCalc_dPoly (CCalc_ex c) true)^[p]
      ((CCalc_dPoly (CCalc_ex c) false)^[q'] (CCalc_dPoly (CCalc_ex c) false CCalc_P0)), ?_, ?_⟩
    · have h1 := CCalc_good_iter (n := n) c hc BF Γ ΓI hBF hΓI hle false 1 _ _
        (CCalc_good_Q0 (n := n) c hc BF Γ ΓI false) q'
      have h2 := CCalc_good_iter c hc BF Γ ΓI hBF hΓI hle true (1 + q') _ _ h1 p
      have e1 : 1 + q' + p = p + (q' + 1) := by omega
      have e2 : Γ ^ p * (Γ ^ q' * (BF * ΓI)) = Γ ^ (p + (q' + 1) - 1) * (BF * ΓI) := by
        rw [show p + (q' + 1) - 1 = p + q' by omega, pow_add]; ring
      rw [e1, e2] at h2
      exact h2
    · rw [CCalc_dop_iter ev hev (CCalc_ex c) hex false, CCalc_dop_iter ev hev (CCalc_ex c) hex true,
        Function.iterate_succ_apply]

end Letters

section Basic

variable {D N : ℕ}

/-- For a Hermitian array the one-entry substitution is Hermitian. -/
private lemma CCalc_slice_herm (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (w : ℂ) : (Matrix.of (setEntry h i j w)).IsHermitian := by
  have e : symArr (setEntry h i j w) = setEntry h i j w := by
    rw [symArr_setEntry, symArr_of_isHermitian h hh]
  rw [← e]
  exact symArr_isHermitian _

/-- The one-entry substitution is smooth in the complex variable. -/
private lemma CCalc_contDiff_slice (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (n : WithTop ℕ∞) : ContDiff ℝ n (fun w : ℂ => setEntry h i j w) := by
  refine contDiff_pi.mpr fun p => contDiff_pi.mpr fun m => ?_
  by_cases hij : i = j
  · subst hij
    by_cases hpm : p = i ∧ m = i
    · have e : (fun x => setEntry h i i x p m) = fun x => ((x.re : ℝ) : ℂ) := by
        funext x; simp [setEntry, hpm]
      change ContDiff ℝ n (fun x => setEntry h i i x p m)
      rw [e]
      exact Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff
    · have e : (fun x => setEntry h i i x p m) = fun _ => h p m := by
        funext x; simp [setEntry, hpm]
      change ContDiff ℝ n (fun x => setEntry h i i x p m)
      rw [e]
      exact contDiff_const
  · by_cases h1 : p = i ∧ m = j
    · have e : (fun x => setEntry h i j x p m) = fun x => x := by
        funext x; simp [setEntry, hij, h1]
      change ContDiff ℝ n (fun x => setEntry h i j x p m)
      rw [e]
      exact contDiff_id
    · by_cases h2 : p = j ∧ m = i
      · have e : (fun x => setEntry h i j x p m) = fun x => starRingEnd ℂ x := by
          funext x; simp [setEntry, hij, h2]
        change ContDiff ℝ n (fun x => setEntry h i j x p m)
        rw [e]
        exact Complex.conjCLE.contDiff
      · have e : (fun x => setEntry h i j x p m) = fun _ => h p m := by
          funext x; simp [setEntry, hij, h1, h2]
        change ContDiff ℝ n (fun x => setEntry h i j x p m)
        rw [e]
        exact contDiff_const

/-- Along a line, the one-entry substitution moves in the Hermitian direction `setEntry 0 i j u`. -/
private lemma CCalc_setEntry_line (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (w u : ℂ) (s : ℝ) :
    setEntry h i j (w + (s : ℂ) * u) = setEntry h i j w + s • setEntry 0 i j u := by
  funext k l
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = i ∧ l = i
    · simp [setEntry, hkl, Complex.real_smul]
    · simp [setEntry, hkl]
  · by_cases h1 : k = i ∧ l = j
    · simp [setEntry, hij, h1, Complex.real_smul]
    · by_cases h2 : k = j ∧ l = i
      · simp [setEntry, hij, h2, Complex.real_smul]
      · simp [setEntry, hij, h1, h2]

/-- `Im G` has the entries `(G_{ab} - conj G_{ba}) / (2i)`. -/
private lemma CCalc_imRes_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (z : ℂ)
    (a b : ι) :
    imRes X z a b = (2 * Complex.I)⁻¹ * (res X z a b - starRingEnd ℂ (res X z b a)) := by
  simp [imRes, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply]

/-- `Im G` is Hermitian entrywise. -/
private lemma CCalc_imRes_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (z : ℂ)
    (a b : ι) : imRes X z b a = starRingEnd ℂ (imRes X z a b) := by
  rw [CCalc_imRes_apply, CCalc_imRes_apply]
  simp only [map_mul, map_sub, map_inv₀, Complex.conj_conj, map_mul, Complex.conj_I, map_ofNat]
  have : (2 : ℂ) * -Complex.I ≠ 0 := by simp
  field_simp
  ring

/-- A double sum with a single nonzero term. -/
private lemma CCalc_sum_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) (F : ι → ι → ℂ) :
    ∑ p, ∑ m, (if p = a ∧ m = b then F p m else 0) = F a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro m _ hm; simp [hm]
    · simp
  · intro p _ hp; simp [hp]
  · simp

/-- The trace of `Δ V` for the Hermitian direction `V = setEntry 0 i j u`, `i ≠ j`. -/
private lemma CCalc_trace_slice_ne (Δ : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N)
    (hij : i ≠ j) (u : ℂ) :
    (Δ * Matrix.of (setEntry 0 i j u)).trace = Δ j i * u + Δ i j * starRingEnd ℂ u := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  have e : ∀ k l : Idx D N, setEntry (0 : Idx D N → Idx D N → ℂ) i j u l k =
      (if k = j ∧ l = i then u else 0) + (if k = i ∧ l = j then starRingEnd ℂ u else 0) := by
    intro k l
    by_cases h1 : l = i ∧ k = j
    · have h2 : ¬ (k = i ∧ l = j) := fun h2 => hij (h2.1.symm.trans h1.2)
      simp [setEntry, hij, h1]
    · by_cases h2 : l = j ∧ k = i
      · have h3 : ¬ (k = j ∧ l = i) := fun h3 => hij (h2.2.symm.trans h3.1)
        simp [setEntry, hij, h2]
      · have h3 : ¬ (k = j ∧ l = i) := fun h3 => h1 ⟨h3.2, h3.1⟩
        have h4 : ¬ (k = i ∧ l = j) := fun h4 => h2 ⟨h4.2, h4.1⟩
        simp [setEntry, hij, h1, h2, h3, h4]
  simp_rw [e, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  rw [CCalc_sum_pair j i (fun k l => Δ k l * u),
    CCalc_sum_pair i j (fun k l => Δ k l * starRingEnd ℂ u)]

/-- The trace of `Δ V` for the Hermitian direction `V = setEntry 0 i i u`. -/
private lemma CCalc_trace_slice_eq (Δ : Matrix (Idx D N) (Idx D N) ℂ) (i : Idx D N) (u : ℂ) :
    (Δ * Matrix.of (setEntry 0 i i u)).trace = Δ i i * ((u.re : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  have e : ∀ k l : Idx D N, setEntry (0 : Idx D N → Idx D N → ℂ) i i u l k =
      if k = i ∧ l = i then ((u.re : ℝ) : ℂ) else 0 := by
    intro k l
    by_cases h1 : l = i ∧ k = i
    · simp [setEntry, h1.1, h1.2]
    · have h2 : ¬ (k = i ∧ l = i) := fun h2 => h1 ⟨h2.2, h2.1⟩
      simp [setEntry, h1, h2]
  simp_rw [e, mul_ite, mul_zero]
  rw [CCalc_sum_pair i i (fun k l => Δ k l * ((u.re : ℝ) : ℂ))]

end Basic

section Data

/-- The data of one entry derivative of `F(A)`: the array `h`, the substituted entry `(i, j)`, the
coupling `A`, `η`, the windows and the function `F`. -/
structure CCalc_Dat (D N n : ℕ) where
  /-- The coupling `A`. -/
  A : Matrix (Fin N) (Fin N) ℂ
  /-- The imaginary part `η` of the spectral points. -/
  η : ℝ
  /-- The function `F` of (4.7) [2comVVt]. -/
  F : (Fin n → ℝ) → ℝ
  /-- The left ends `E₁(m)` of the windows. -/
  E₁ : Fin n → ℝ
  /-- The right ends `E₂(m)` of the windows. -/
  E₂ : Fin n → ℝ
  /-- The array `h`. -/
  h : Idx D N → Idx D N → ℂ
  /-- The first index of the substituted entry. -/
  i : Idx D N
  /-- The second index of the substituted entry. -/
  j : Idx D N

variable {D N n : ℕ}

/-- The index `i` for `0` and `j` for `1`. -/
private def CCalc_Dat.idx (S : CCalc_Dat D N n) (a : Fin 2) : Idx D N :=
  if a = 0 then S.i else S.j

/-- The matrix `h + Λ` with the entry `(i, j)` replaced by `w`. -/
private def CCalc_Dat.X (S : CCalc_Dat D N n) (w : ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  Matrix.of (setEntry S.h S.i S.j w) + lam D N S.A

/-- The array `A(w) = (A_m(w))_m` of edge counts at the substituted entry. -/
private def CCalc_Dat.cnt (S : CCalc_Dat D N n) (w : ℂ) : Fin n → ℝ :=
  fun m => edgeCount D N S.A S.η (S.E₁ m) (S.E₂ m) (setEntry S.h S.i S.j w)

/-- The constant `1/2` on the diagonal and `1` off it of the Wirtinger derivatives along the
slice. -/
private def CCalc_Dat.c (S : CCalc_Dat D N n) : ℂ := if S.i = S.j then 1 / 2 else 1

/-- The iterated coordinate partial derivatives of `F`: `ψ_{[]} = F`, `ψ_{k::ks} = ∂_k ψ_{ks}`. -/
private def CCalc_pd {n : ℕ} (F : (Fin n → ℝ) → ℝ) : List (Fin n) → (Fin n → ℝ) → ℝ
  | [] => F
  | k :: ks => fun x => fderiv ℝ (CCalc_pd F ks) x (Pi.single k 1)

/-- The value of a letter as a function of the substituted entry `w`. -/
private def CCalc_Dat.ev (S : CCalc_Dat D N n) : CCalc_Letter n → ℂ → ℂ
  | .G r a b => fun w => res (S.X w) (edgePt S.η S.E₁ S.E₂ r) (S.idx a) (S.idx b)
  | .Gs r a b => fun w =>
      starRingEnd ℂ (res (S.X w) (edgePt S.η S.E₁ S.E₂ r) (S.idx b) (S.idx a))
  | .I r a b => fun w => imRes (S.X w) (edgePt S.η S.E₁ S.E₂ r) (S.idx a) (S.idx b)
  | .Psi ks => fun w => ((CCalc_pd S.F ks (S.cnt w) : ℝ) : ℂ)

end Data

section Smooth

variable {D N n : ℕ}

/-- The substitution commutes with taking the Hermitian part. -/
private lemma CCalc_symArr_slice (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (w : ℂ) : symArr (setEntry h i j w) = setEntry h i j w := by
  rw [symArr_setEntry, symArr_of_isHermitian h hh]

/-- The imaginary part of every spectral point `E + iη` is `η`. -/
private lemma CCalc_im_edgePt (η : ℝ) {n : ℕ} (E₁ E₂ : Fin n → ℝ) (r : Fin n × Fin 2) :
    (edgePt η E₁ E₂ r).im = η := by
  unfold edgePt
  split_ifs <;> simp

/-- The entries of the resolvent along the slice `w ↦ setEntry h i j w` are smooth in `w`, for
Hermitian `h`, Hermitian `Λ` and `Im z ≠ 0`. -/
private lemma CCalc_contDiff_res_slice (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (k l : Idx D N) :
    ContDiff ℝ ∞ (fun w : ℂ => res (Matrix.of (setEntry h i j w) + Λ) z k l) := by
  rw [contDiff_infty]
  intro m
  have e : (fun w : ℂ => res (Matrix.of (setEntry h i j w) + Λ) z k l) =
      (fun h' : Idx D N → Idx D N → ℂ => res (Matrix.of (symArr h') + Λ) z k l) ∘
        fun w => setEntry h i j w := by
    funext w
    simp only [Function.comp, CCalc_symArr_slice h hh]
  rw [e]
  exact (contDiff_res_symArr Λ hΛ z hz k l m).comp (CCalc_contDiff_slice h i j m)

/-- The edge count along the slice `w ↦ setEntry h i j w` is smooth in `w`, for Hermitian `h` and `η
> 0`. -/
private lemma CCalc_contDiff_count (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ) (hη : 0 < η)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    ContDiff ℝ ∞ (fun w : ℂ => edgeCount D N A η E₁ E₂ (setEntry h i j w)) := by
  have e : (fun w : ℂ => edgeCount D N A η E₁ E₂ (setEntry h i j w)) =
      (fun h' : Idx D N → Idx D N → ℂ => edgeCount D N A η E₁ E₂ (symArr h')) ∘
        fun w => setEntry h i j w := by
    funext w
    simp only [Function.comp, CCalc_symArr_slice h hh]
  rw [e]
  exact (edgeCount_contDiff D N A η E₁ E₂ hη).comp (CCalc_contDiff_slice h i j ∞)

/-- The coordinate partial derivatives of a smooth function are smooth. -/
private lemma CCalc_contDiff_pd {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (ks : List (Fin n)) : ContDiff ℝ ∞ (CCalc_pd F ks) := by
  induction ks with
  | nil => exact hF
  | cons k ks ih =>
    have h1 : ContDiff ℝ ∞ (fderiv ℝ (CCalc_pd F ks)) := ih.fderiv_right (by simp)
    exact h1.clm_apply contDiff_const

variable (S : CCalc_Dat D N n)

/-- The array `A(w)` of edge counts is smooth in `w`. -/
private lemma CCalc_Dat.contDiff_cnt (hh : (Matrix.of S.h).IsHermitian) (hη : 0 < S.η) :
    ContDiff ℝ ∞ S.cnt :=
  contDiff_pi.mpr fun m => CCalc_contDiff_count S.A S.η (S.E₁ m) (S.E₂ m) hη S.h hh S.i S.j

/-- The value of every letter is smooth in `w`. -/
private lemma CCalc_Dat.contDiff_ev (hh : (Matrix.of S.h).IsHermitian) (hη : 0 < S.η)
    (hF : ContDiff ℝ ∞ S.F) (l : CCalc_Letter n) : ContDiff ℝ ∞ (S.ev l) := by
  have hG : ∀ r (a b : Idx D N), ContDiff ℝ ∞ (fun w : ℂ => res (S.X w)
      (edgePt S.η S.E₁ S.E₂ r) a b) := fun r a b =>
    CCalc_contDiff_res_slice S.h hh S.i S.j _ (lam_isHermitian D N S.A) _
      (by rw [CCalc_im_edgePt]; exact hη.ne') a b
  cases l with
  | G r a b => exact hG r _ _
  | Gs r a b => exact Complex.conjCLE.contDiff.comp (hG r _ _)
  | I r a b =>
    have e : S.ev (.I r a b) = fun w => (2 * Complex.I)⁻¹ * (res (S.X w)
        (edgePt S.η S.E₁ S.E₂ r) (S.idx a) (S.idx b) -
          starRingEnd ℂ (res (S.X w) (edgePt S.η S.E₁ S.E₂ r) (S.idx b) (S.idx a))) := by
      funext w
      exact CCalc_imRes_apply _ _ _ _
    rw [e]
    exact contDiff_const.mul ((hG r _ _).sub (Complex.conjCLE.contDiff.comp (hG r _ _)))
  | Psi ks =>
    exact Complex.ofRealCLM.contDiff.comp
      ((CCalc_contDiff_pd S.F hF ks).comp (S.contDiff_cnt hh hη))

/-- The value of every letter is differentiable in `w`. -/
private lemma CCalc_Dat.diff_ev (hh : (Matrix.of S.h).IsHermitian) (hη : 0 < S.η)
    (hF : ContDiff ℝ ∞ S.F) (l : CCalc_Letter n) (w : ℂ) : DifferentiableAt ℝ (S.ev l) w :=
  ((S.contDiff_ev hh hη hF l).differentiable (by simp)) w

end Smooth

section Deriv

variable {D N n : ℕ} (S : CCalc_Dat D N n)

/-- The real derivative of `A_m` along the slice in the direction `u`, from (4.10)
[partial_xy_F_A_t] for the Hermitian direction `setEntry 0 i j u`. -/
private lemma CCalc_fderiv_cnt (hh : (Matrix.of S.h).IsHermitian) (hη : 0 < S.η) (m : Fin n)
    (w u : ℂ) :
    fderiv ℝ (fun w' : ℂ => S.cnt w' m) w u =
      -(((imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (m, 1)) -
        imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (m, 0))) *
          Matrix.of (setEntry 0 S.i S.j u)).trace).re := by
  have hg : DifferentiableAt ℝ (fun w' : ℂ => S.cnt w' m) w :=
    ((CCalc_contDiff_count S.A S.η (S.E₁ m) (S.E₂ m) hη S.h hh S.i S.j).differentiable
      (by simp)) w
  have hline : HasDerivAt (fun s : ℝ => w + (s : ℂ) * u) u 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const u).const_add w
  have h1 : HasDerivAt (fun s : ℝ => S.cnt (w + (s : ℂ) * u) m)
      (fderiv ℝ (fun w' : ℂ => S.cnt w' m) w u) 0 := by
    have h0 : HasFDerivAt (fun w' : ℂ => S.cnt w' m) (fderiv ℝ (fun w' : ℂ => S.cnt w' m) w)
        (w + ((0 : ℝ) : ℂ) * u) := by simpa using hg.hasFDerivAt
    exact h0.comp_hasDerivAt (0 : ℝ) hline
  have h2 := edgeCount_hasDerivAt D N S.A S.η (S.E₁ m) (S.E₂ m) hη (setEntry S.h S.i S.j w)
    (setEntry 0 S.i S.j u) (CCalc_slice_herm S.h hh S.i S.j w)
    (CCalc_slice_herm 0 Matrix.isHermitian_zero S.i S.j u)
  have e : (fun s : ℝ => S.cnt (w + (s : ℂ) * u) m) = fun s : ℝ =>
      edgeCount D N S.A S.η (S.E₁ m) (S.E₂ m)
        (setEntry S.h S.i S.j w + s • setEntry 0 S.i S.j u) := by
    funext s
    simp only [CCalc_Dat.cnt]
    rw [CCalc_setEntry_line]
  rw [e] at h1
  exact h1.unique h2

/-- The Wirtinger derivatives of `A_m` along the slice: `∂_w A_m = -c Δ_{ji}` and
`∂_{w̄} A_m = -c Δ_{ij}` with `Δ = Im G(E₂ + iη) - Im G(E₁ + iη)` and `c = 1` off the diagonal,
`c = 1/2` on it: (4.10) [partial_xy_F_A_t]. -/
private lemma CCalc_dop_cnt (hh : (Matrix.of S.h).IsHermitian) (hη : 0 < S.η) (m : Fin n)
    (w : ℂ) :
    CCalc_dop true (fun w' : ℂ => ((S.cnt w' m : ℝ) : ℂ)) w =
      -S.c * (imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (m, 1)) S.j S.i -
        imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (m, 0)) S.j S.i) ∧
    CCalc_dop false (fun w' : ℂ => ((S.cnt w' m : ℝ) : ℂ)) w =
      -S.c * (imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (m, 1)) S.i S.j -
        imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (m, 0)) S.i S.j) := by
  set Δ : Matrix (Idx D N) (Idx D N) ℂ := imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (m, 1)) -
    imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (m, 0)) with hΔ
  have hΔc : ∀ a b, Δ b a = starRingEnd ℂ (Δ a b) := by
    intro a b
    simp only [hΔ, Matrix.sub_apply, map_sub, CCalc_imRes_conj _ _ a b]
  have hL : ∀ u : ℂ, fderiv ℝ (fun w' : ℂ => S.cnt w' m) w u =
      -((Δ * Matrix.of (setEntry 0 S.i S.j u)).trace).re := CCalc_fderiv_cnt S hh hη m w
  have hg : DifferentiableAt ℝ (fun w' : ℂ => S.cnt w' m) w :=
    ((CCalc_contDiff_count S.A S.η (S.E₁ m) (S.E₂ m) hη S.h hh S.i S.j).differentiable
      (by simp)) w
  have hcast : ∀ u : ℂ, fderiv ℝ (fun w' : ℂ => ((S.cnt w' m : ℝ) : ℂ)) w u =
      ((fderiv ℝ (fun w' : ℂ => S.cnt w' m) w u : ℝ) : ℂ) := by
    intro u
    have := (Complex.ofRealCLM.hasFDerivAt.comp w hg.hasFDerivAt).fderiv
    rw [show (fun w' : ℂ => ((S.cnt w' m : ℝ) : ℂ)) = Complex.ofRealCLM ∘ fun w' : ℂ => S.cnt w' m
      from rfl, this]
    rfl
  have e1 : imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (m, 1)) S.j S.i -
      imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (m, 0)) S.j S.i = Δ S.j S.i :=
    (Matrix.sub_apply _ _ _ _).symm
  have e2 : imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (m, 1)) S.i S.j -
      imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (m, 0)) S.i S.j = Δ S.i S.j :=
    (Matrix.sub_apply _ _ _ _).symm
  rw [e1, e2]
  simp only [CCalc_dop, dW, dWbar, hcast, hL]
  by_cases hij : S.i = S.j
  · have hc : S.c = 1 / 2 := by simp [CCalc_Dat.c, hij]
    rw [hc, ← hij, CCalc_trace_slice_eq, CCalc_trace_slice_eq]
    have hx : Δ S.i S.i = ((Δ S.i S.i).re : ℂ) := by
      apply Complex.ext
      · simp
      · have := hΔc S.i S.i
        have h2 := congrArg Complex.im this
        simp at h2
        simp
        linarith
    obtain ⟨α, hα⟩ : ∃ α : ℝ, Δ S.i S.i = α := ⟨_, hx⟩
    rw [hα]
    constructor <;> apply Complex.ext <;> simp <;> ring
  · have hc : S.c = 1 := by simp [CCalc_Dat.c, hij]
    rw [hc, CCalc_trace_slice_ne _ _ _ hij, CCalc_trace_slice_ne _ _ _ hij, hΔc S.j S.i]
    generalize Δ S.j S.i = x
    constructor <;> apply Complex.ext <;> simp

/-- The real derivative of the composition with the inclusion `ℝ → ℂ`. -/
private lemma CCalc_fderiv_ofReal {g : ℂ → ℝ} {w : ℂ} (hg : DifferentiableAt ℝ g w) (u : ℂ) :
    fderiv ℝ (fun w' : ℂ => ((g w' : ℝ) : ℂ)) w u = ((fderiv ℝ g w u : ℝ) : ℂ) := by
  have := (Complex.ofRealCLM.hasFDerivAt.comp w hg.hasFDerivAt).fderiv
  rw [show (fun w' : ℂ => ((g w' : ℝ) : ℂ)) = Complex.ofRealCLM ∘ g from rfl, this]
  rfl

/-- A continuous linear functional on `ℝⁿ` is the sum over the coordinates. -/
private lemma CCalc_clm_sum {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Pi.single k (v k) : Fin n → ℝ) = v k • Pi.single k 1 := by
    funext j; by_cases h : j = k <;> simp [h]
  rw [this, map_smul, smul_eq_mul]

/-- The chain rule for `ψ_{ks} ∘ A` along the slice. -/
private lemma CCalc_fderiv_psi (hh : (Matrix.of S.h).IsHermitian) (hη : 0 < S.η)
    (hF : ContDiff ℝ ∞ S.F) (ks : List (Fin n)) (w u : ℂ) :
    fderiv ℝ (fun w' : ℂ => CCalc_pd S.F ks (S.cnt w')) w u =
      ∑ k : Fin n, fderiv ℝ (fun w' : ℂ => S.cnt w' k) w u * CCalc_pd S.F (k :: ks) (S.cnt w) := by
  have hcnt : DifferentiableAt ℝ S.cnt w := ((S.contDiff_cnt hh hη).differentiable (by simp)) w
  have hpd : DifferentiableAt ℝ (CCalc_pd S.F ks) (S.cnt w) :=
    ((CCalc_contDiff_pd S.F hF ks).differentiable (by simp)) _
  have hc := hpd.hasFDerivAt.comp w hcnt.hasFDerivAt
  rw [show (fun w' : ℂ => CCalc_pd S.F ks (S.cnt w')) = CCalc_pd S.F ks ∘ S.cnt from rfl,
    hc.fderiv, ContinuousLinearMap.comp_apply, CCalc_clm_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ∀ m : Fin n, DifferentiableAt ℝ (fun w' : ℂ => S.cnt w' m) w := fun m =>
    ((CCalc_contDiff_count S.A S.η (S.E₁ m) (S.E₂ m) hη S.h hh S.i S.j).differentiable
      (by simp)) w
  have e : (fderiv ℝ S.cnt w u) k = fderiv ℝ (fun w' : ℂ => S.cnt w' k) w u := by
    have := fderiv_pi (𝕜 := ℝ) (x := w) (φ := fun m w' => S.cnt w' m) hk
    rw [show S.cnt = fun w' m => S.cnt w' m from rfl, this]
    rfl
  rw [e]
  rfl

/-- The Wirtinger derivatives of a partial derivative of `F` along the slice. -/
private lemma CCalc_dop_psi (hh : (Matrix.of S.h).IsHermitian) (hη : 0 < S.η)
    (hF : ContDiff ℝ ∞ S.F) (d : Bool) (ks : List (Fin n)) (w : ℂ) :
    CCalc_dop d (S.ev (.Psi ks)) w = ∑ k : Fin n, ((CCalc_pd S.F (k :: ks) (S.cnt w) : ℝ) : ℂ) *
      CCalc_dop d (fun w' : ℂ => ((S.cnt w' k : ℝ) : ℂ)) w := by
  have hg : DifferentiableAt ℝ (fun w' : ℂ => CCalc_pd S.F ks (S.cnt w')) w :=
    (((CCalc_contDiff_pd S.F hF ks).comp (S.contDiff_cnt hh hη)).differentiable (by simp)) w
  have hk : ∀ m : Fin n, DifferentiableAt ℝ (fun w' : ℂ => S.cnt w' m) w := fun m =>
    ((CCalc_contDiff_count S.A S.η (S.E₁ m) (S.E₂ m) hη S.h hh S.i S.j).differentiable
      (by simp)) w
  change CCalc_dop d (fun w' : ℂ => ((CCalc_pd S.F ks (S.cnt w') : ℝ) : ℂ)) w = _
  cases d
  all_goals
    simp only [CCalc_dop, dW, dWbar, CCalc_fderiv_ofReal hg, CCalc_fderiv_ofReal (hk _),
      CCalc_fderiv_psi S hh hη hF ks]
    push_cast
    rw [Finset.mul_sum]
    first
      | rw [← Finset.sum_sub_distrib]
      | rw [← Finset.sum_add_distrib]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- The index `0` stands for `i`. -/
private lemma CCalc_Dat.idx_zero : S.idx 0 = S.i := by simp [CCalc_Dat.idx]

/-- The index `1` stands for `j`. -/
private lemma CCalc_Dat.idx_one : S.idx 1 = S.j := by simp [CCalc_Dat.idx]

/-- The constant `c` is real. -/
private lemma CCalc_Dat.conj_c : starRingEnd ℂ S.c = S.c := by
  unfold CCalc_Dat.c
  split_ifs
  · rw [map_div₀, map_one, map_ofNat]
  · simp

/-- The Wirtinger derivative of a difference. -/
private lemma CCalc_dop_sub (d : Bool) {F G : ℂ → ℂ} {w : ℂ} (hF : DifferentiableAt ℝ F w)
    (hG : DifferentiableAt ℝ G w) :
    CCalc_dop d (fun x => F x - G x) w = CCalc_dop d F w - CCalc_dop d G w := by
  have e : fderiv ℝ (fun x => F x - G x) w = fderiv ℝ F w - fderiv ℝ G w := fderiv_fun_sub hF hG
  cases d <;> simp only [CCalc_dop, dW, dWbar, e, _root_.sub_apply] <;> ring

/-- `∂_w G_{ab}` and `∂_{w̄} G_{ab}` along the slice, from `res_dW`. -/
private lemma CCalc_hex_G (hh : (Matrix.of S.h).IsHermitian) (hη : 0 < S.η) (d : Bool)
    (r : Fin n × Fin 2) (a b : Fin 2) :
    CCalc_dop d (S.ev (.G r a b)) = CCalc_poly S.ev (CCalc_ex S.c d (.G r a b)) := by
  have hz : (edgePt S.η S.E₁ S.E₂ r).im ≠ 0 := by rw [CCalc_im_edgePt]; exact hη.ne'
  have hdG := res_dW (lam D N S.A) (lam_isHermitian D N S.A) (edgePt S.η S.E₁ S.E₂ r) hz S.h hh
    S.i S.j (S.idx a) (S.idx b)
  funext w
  cases d
  · have h := congrFun hdG.2 w
    refine h.trans ?_
    simp [CCalc_ex, CCalc_poly, CCalc_mono, CCalc_Dat.ev, CCalc_Dat.idx_zero, CCalc_Dat.idx_one,
      CCalc_Dat.c, CCalc_Dat.X]
  · have h := congrFun hdG.1 w
    refine h.trans ?_
    simp [CCalc_ex, CCalc_poly, CCalc_mono, CCalc_Dat.ev, CCalc_Dat.idx_zero, CCalc_Dat.idx_one,
      CCalc_Dat.c, CCalc_Dat.X]

/-- The same for `G^*_{ab}`, from `dW_conj`. -/
private lemma CCalc_hex_Gs (hh : (Matrix.of S.h).IsHermitian) (hη : 0 < S.η)
    (hF : ContDiff ℝ ∞ S.F) (d : Bool) (r : Fin n × Fin 2) (a b : Fin 2) :
    CCalc_dop d (S.ev (.Gs r a b)) = CCalc_poly S.ev (CCalc_ex S.c d (.Gs r a b)) := by
  have hz : (edgePt S.η S.E₁ S.E₂ r).im ≠ 0 := by rw [CCalc_im_edgePt]; exact hη.ne'
  have hdG := res_dW (lam D N S.A) (lam_isHermitian D N S.A) (edgePt S.η S.E₁ S.E₂ r) hz S.h hh
    S.i S.j (S.idx b) (S.idx a)
  funext w
  have hdiff : DifferentiableAt ℝ (S.ev (.G r b a)) w := S.diff_ev hh hη hF (.G r b a) w
  have hconj := dW_conj hdiff
  have e : S.ev (.Gs r a b) = fun x => starRingEnd ℂ (S.ev (.G r b a) x) := rfl
  cases d
  · change dWbar (S.ev (.Gs r a b)) w = _
    rw [e, hconj.2]
    have h' : dW (S.ev (.G r b a)) w = -S.c * (res (S.X w) (edgePt S.η S.E₁ S.E₂ r) (S.idx b) S.i *
        res (S.X w) (edgePt S.η S.E₁ S.E₂ r) S.j (S.idx a)) := congrFun hdG.1 w
    rw [h']
    simp only [CCalc_ex, CCalc_poly, CCalc_mono, CCalc_Dat.ev, CCalc_Dat.idx_zero,
      CCalc_Dat.idx_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      List.sum_cons, List.sum_nil, map_mul, map_neg, CCalc_Dat.conj_c]
    ring
  · change dW (S.ev (.Gs r a b)) w = _
    rw [e, hconj.1]
    have h' : dWbar (S.ev (.G r b a)) w = -S.c *
        (res (S.X w) (edgePt S.η S.E₁ S.E₂ r) (S.idx b) S.j *
        res (S.X w) (edgePt S.η S.E₁ S.E₂ r) S.i (S.idx a)) := congrFun hdG.2 w
    rw [h']
    simp only [CCalc_ex, CCalc_poly, CCalc_mono, CCalc_Dat.ev, CCalc_Dat.idx_zero,
      CCalc_Dat.idx_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      List.sum_cons, List.sum_nil, map_mul, map_neg, CCalc_Dat.conj_c]
    ring

/-- The derivatives of `(Im G)_{ab} = (G_{ab} - G^*_{ab}) / (2i)` have one factor `Im G` per term
(the identity
`G_{ax} G_{yb} - G^*_{ax} G^*_{yb} = 2i [(Im G)_{ax} G_{yb} + G^*_{ax} (Im G)_{yb}]`). -/
private lemma CCalc_hex_I (hh : (Matrix.of S.h).IsHermitian) (hη : 0 < S.η)
    (hF : ContDiff ℝ ∞ S.F) (d : Bool) (r : Fin n × Fin 2) (a b : Fin 2) :
    CCalc_dop d (S.ev (.I r a b)) = CCalc_poly S.ev (CCalc_ex S.c d (.I r a b)) := by
  funext w
  have e : S.ev (.I r a b) = fun x =>
      (2 * Complex.I)⁻¹ * (S.ev (.G r a b) x - S.ev (.Gs r a b) x) :=
    funext fun x => CCalc_imRes_apply _ _ _ _
  have hG := S.diff_ev hh hη hF (.G r a b) w
  have hGs := S.diff_ev hh hη hF (.Gs r a b) w
  rw [e, CCalc_dop_const_mul d (F := fun x => S.ev (.G r a b) x - S.ev (.Gs r a b) x)
    ((2 * Complex.I)⁻¹) (hG.sub hGs), CCalc_dop_sub d hG hGs,
    congrFun (CCalc_hex_G S hh hη d r a b) w, congrFun (CCalc_hex_Gs S hh hη hF d r a b) w]
  cases d
  all_goals
    simp only [CCalc_ex, CCalc_poly, CCalc_mono, CCalc_Dat.ev, CCalc_Dat.idx_zero,
      CCalc_Dat.idx_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      List.sum_cons, List.sum_nil, CCalc_imRes_apply]
    ring

/-- The value of `CCalc_psiExp` is the sum over the indices of the next partial derivative of `F`
times `∓c` times the two `Im G` entries. -/
private lemma CCalc_poly_psiExp (c : ℂ) (a b : Fin 2) (ks : List (Fin n)) (l : List (Fin n))
    (w : ℂ) :
    CCalc_poly S.ev (CCalc_psiExp c a b ks l) w = (l.map fun k =>
      ((CCalc_pd S.F (k :: ks) (S.cnt w) : ℝ) : ℂ) * (-c *
        (imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (k, 1)) (S.idx a) (S.idx b) -
          imRes (S.X w) (edgePt S.η S.E₁ S.E₂ (k, 0)) (S.idx a) (S.idx b)))).sum := by
  induction l with
  | nil => simp [CCalc_psiExp, CCalc_poly]
  | cons k l ih =>
    rw [CCalc_psiExp, CCalc_poly_append, ih]
    simp only [CCalc_poly, CCalc_mono, CCalc_Dat.ev, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, List.sum_cons, List.sum_nil]
    ring

/-- The derivatives of a partial derivative of `F` along the slice: the sum over `k` of the next
partial derivative times the two terms `∓c (Im G)_{ab}` of `∂ A_k`. -/
private lemma CCalc_hex_Psi (hh : (Matrix.of S.h).IsHermitian) (hη : 0 < S.η)
    (hF : ContDiff ℝ ∞ S.F) (d : Bool) (ks : List (Fin n)) :
    CCalc_dop d (S.ev (.Psi ks)) = CCalc_poly S.ev (CCalc_ex S.c d (.Psi ks)) := by
  funext w
  rw [CCalc_dop_psi S hh hη hF d ks w]
  cases d
  · simp only [CCalc_ex]
    rw [CCalc_poly_psiExp, Fin.sum_univ_def]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    rw [(CCalc_dop_cnt S hh hη k w).2]
    simp [CCalc_Dat.idx_zero, CCalc_Dat.idx_one]
  · simp only [CCalc_ex]
    rw [CCalc_poly_psiExp, Fin.sum_univ_def]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    rw [(CCalc_dop_cnt S hh hη k w).1]
    simp [CCalc_Dat.idx_zero, CCalc_Dat.idx_one]

/-- The Wirtinger derivatives of every letter along the slice. -/
private lemma CCalc_hex (hh : (Matrix.of S.h).IsHermitian) (hη : 0 < S.η)
    (hF : ContDiff ℝ ∞ S.F) (d : Bool) (l : CCalc_Letter n) :
    CCalc_dop d (S.ev l) = CCalc_poly S.ev (CCalc_ex S.c d l) := by
  cases l with
  | G r a b => exact CCalc_hex_G S hh hη d r a b
  | Gs r a b => exact CCalc_hex_Gs S hh hη hF d r a b
  | I r a b => exact CCalc_hex_I S hh hη hF d r a b
  | Psi ks => exact CCalc_hex_Psi S hh hη hF d ks

end Deriv

section Bound

variable {n : ℕ}

/-- A coordinate partial derivative of order `l` is the iterated derivative applied to unit
vectors. -/
private lemma CCalc_pd_eq (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) (ks : List (Fin n)) :
    ∃ u : Fin ks.length → (Fin n → ℝ), (∀ t, ‖u t‖ ≤ 1) ∧
      ∀ x, CCalc_pd F ks x = iteratedFDeriv ℝ ks.length F x u := by
  induction ks with
  | nil => exact ⟨fun t => t.elim0, fun t => t.elim0, fun x => rfl⟩
  | cons k ks ih =>
    obtain ⟨u, hu, hpd⟩ := ih
    refine ⟨Fin.cons (Pi.single k 1) u, ?_, fun x => ?_⟩
    · intro t
      refine Fin.cases ?_ (fun t => ?_) t
      · exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
          by_cases h : j = k <;> simp [h]
      · simpa using hu t
    · have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ ks.length F) x :=
        ((hF.iteratedFDeriv_right (i := ks.length) (m := 1) (by simp)).differentiable
          (by simp)) x
      have h1 := hd.iteratedFDeriv_succ_apply_left' (m := Fin.cons (Pi.single k 1) u)
      simp only [Fin.tail_cons, Fin.cons_zero] at h1
      change fderiv ℝ (CCalc_pd F ks) x (Pi.single k 1) =
        (iteratedFDeriv ℝ (ks.length + 1) F x) (Fin.cons (Pi.single k 1) u)
      rw [h1]
      have : CCalc_pd F ks = fun y => iteratedFDeriv ℝ ks.length F y u := funext hpd
      rw [this]

/-- The bound on a coordinate partial derivative by the norm of the iterated derivative. -/
private lemma CCalc_pd_le (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) (ks : List (Fin n))
    (x : Fin n → ℝ) : |CCalc_pd F ks x| ≤ ‖iteratedFDeriv ℝ ks.length F x‖ := by
  obtain ⟨u, hu, hpd⟩ := CCalc_pd_eq F hF ks
  rw [hpd x, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have : ∏ t, ‖u t‖ ≤ 1 := Finset.prod_le_one₀ (fun t _ => norm_nonneg _) fun t _ => hu t
  calc ‖iteratedFDeriv ℝ ks.length F x‖ * ∏ t, ‖u t‖ ≤ ‖iteratedFDeriv ℝ ks.length F x‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

variable {D N : ℕ} (S : CCalc_Dat D N n)

/-- At the point `w`, a letter of admissible order is bounded by its bound. -/
private lemma CCalc_ev_le (hF : ContDiff ℝ ∞ S.F) (BF Γ ΓI : ℝ) (p q : ℕ) (w : ℂ)
    (hBF : ∀ k : ℕ, 1 ≤ k → k ≤ p + q → ‖iteratedFDeriv ℝ k S.F (S.cnt w)‖ ≤ BF)
    (hG : ∀ (r : Fin n × Fin 2) (a b : Idx D N), (a = S.i ∨ a = S.j) → (b = S.i ∨ b = S.j) →
      ‖res (Matrix.of (setEntry S.h S.i S.j w) + lam D N S.A) (edgePt S.η S.E₁ S.E₂ r) a b‖ ≤ Γ ∧
        ‖imRes (Matrix.of (setEntry S.h S.i S.j w) + lam D N S.A) (edgePt S.η S.E₁ S.E₂ r) a b‖ ≤
          ΓI)
    (l : CCalc_Letter n) (hl : CCalc_val (p + q) l) : ‖S.ev l w‖ ≤ CCalc_bd BF Γ ΓI l := by
  have hidx : ∀ a : Fin 2, S.idx a = S.i ∨ S.idx a = S.j := by
    intro a; unfold CCalc_Dat.idx; split_ifs <;> simp
  cases l with
  | G r a b => exact (hG r _ _ (hidx a) (hidx b)).1
  | Gs r a b =>
    change ‖starRingEnd ℂ (res (S.X w) (edgePt S.η S.E₁ S.E₂ r) (S.idx b) (S.idx a))‖ ≤ Γ
    rw [Complex.norm_conj]
    exact (hG r _ _ (hidx b) (hidx a)).1
  | I r a b => exact (hG r _ _ (hidx a) (hidx b)).2
  | Psi ks =>
    change ‖((CCalc_pd S.F ks (S.cnt w) : ℝ) : ℂ)‖ ≤ BF
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (CCalc_pd_le S.F hF ks _).trans (hBF _ hl.1 hl.2)

end Bound


/-- The structure of `∂^p_{w} ∂^q_{w̄} F(A)` in the proof of Lemma 4.3 [rescomY], with the
factors `(Im G)_{ab}` of (4.13) [single_resolvent_local_law_bound2]: if the entries `G_{ab}` and
`(Im G)_{ab}`, `a, b ∈ {i, j}`, at the `2n` points are bounded by `Γ ≥ 1` and `Γ_I ≤ Γ`, and the
derivatives of `F` of orders `1, …, p + q` at `A` by `B_F`, then the derivative of order
`p + q ≥ 1` in the entry `(i, j)` is at most `K B_F Γ_I Γ^{p+q-1}`. -/
theorem edgeFn_wirt_le (n p q : ℕ) (hpq : 1 ≤ p + q) :
    ∃ K : ℝ, 0 < K ∧ ∀ (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ), 0 < η →
      ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ F → ∀ (E₁ E₂ : Fin n → ℝ)
      (h : Idx D N → Idx D N → ℂ), (Matrix.of h).IsHermitian → ∀ (i j : Idx D N) (w : ℂ)
      (BF Γ ΓI : ℝ), 1 ≤ Γ → 0 ≤ ΓI → ΓI ≤ Γ →
      (∀ k : ℕ, 1 ≤ k → k ≤ p + q →
        ‖iteratedFDeriv ℝ k F (fun m => edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j w))‖ ≤
          BF) →
      (∀ (r : Fin n × Fin 2) (a b : Idx D N), (a = i ∨ a = j) → (b = i ∨ b = j) →
        ‖res (Matrix.of (setEntry h i j w) + lam D N A) (edgePt η E₁ E₂ r) a b‖ ≤ Γ ∧
          ‖imRes (Matrix.of (setEntry h i j w) + lam D N A) (edgePt η E₁ E₂ r) a b‖ ≤ ΓI) →
        ‖wirt p q (fun w' => (edgeFn D N A η F E₁ E₂ (setEntry h i j w') : ℂ)) w‖ ≤
          K * BF * ΓI * Γ ^ (p + q - 1) := by
  refine ⟨CCalc_K n (p + q), CCalc_K_pos n (p + q), ?_⟩
  intro D N A η hη F hF E₁ E₂ h hh i j w BF Γ ΓI hΓ hΓI hle hBF hG
  set S : CCalc_Dat D N n := ⟨A, η, F, E₁, E₂, h, i, j⟩ with hS
  have hBF0 : 0 ≤ BF := (norm_nonneg _).trans (hBF 1 le_rfl hpq)
  have hc : ‖S.c‖ ≤ 1 := by
    change ‖(if i = j then (1 / 2 : ℂ) else 1)‖ ≤ 1
    split_ifs <;> norm_num
  obtain ⟨P, hgood, hP⟩ := CCalc_wirt_good S.ev (S.diff_ev hh hη hF) S.c hc
    (CCalc_hex S hh hη hF) BF Γ ΓI hBF0 hΓI hle p q hpq
  have e : (fun w' => (edgeFn D N A η F E₁ E₂ (setEntry h i j w') : ℂ)) =
      CCalc_poly S.ev CCalc_P0 := by
    funext w'
    simp [CCalc_P0, CCalc_poly, CCalc_mono, CCalc_Dat.ev, CCalc_pd, edgeFn]
    rfl
  rw [e]
  change ‖(CCalc_dop true)^[p] ((CCalc_dop false)^[q] (CCalc_poly S.ev CCalc_P0)) w‖ ≤ _
  rw [hP]
  have hΓ0 : 0 ≤ Γ := by linarith
  have hB : 0 ≤ Γ ^ (p + q - 1) * (BF * ΓI) := by positivity
  have h1 := CCalc_poly_norm_le (CCalc_bd BF Γ ΓI) S.ev w P
    (fun t ht l hl => CCalc_ev_le S hF BF Γ ΓI p q w hBF hG l ((hgood.1 t ht).2.1 l hl))
    (Γ ^ (p + q - 1) * (BF * ΓI)) (fun t ht => (hgood.1 t ht).2.2)
  have h2 := mul_le_mul_of_nonneg_right hgood.2 hB
  calc ‖CCalc_poly S.ev P w‖ ≤ CCalc_wt P * (Γ ^ (p + q - 1) * (BF * ΓI)) := h1
    _ ≤ CCalc_K n (p + q) * (Γ ^ (p + q - 1) * (BF * ΓI)) := h2
    _ = CCalc_K n (p + q) * BF * ΓI * Γ ^ (p + q - 1) := by ring

/-- `Im M = Im(z + m) M M^*` for `M = (Λ - z - m)⁻¹` of (2.17) [def_G0], Hermitian `Λ`,
`Im z > 0`; with `‖M‖ ≤ 5/4` it gives `‖Im M‖ ≤ (25/16)(η + Im m)`, the deterministic part of
(4.12) [single_resolvent_local_law_bound]. -/
theorem MExt_imPart_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    (2 * Complex.I)⁻¹ • (MExt Λ z - (MExt Λ z)ᴴ) =
      (((z + mExt Λ z).im : ℝ) : ℂ) • (MExt Λ z * (MExt Λ z)ᴴ) := by
  have _ := hz
  set w : ℂ := z + mExt Λ z with hw
  set B : Matrix ι ι ℂ := Λ - w • (1 : Matrix ι ι ℂ) with hB
  have hM : MExt Λ z = B⁻¹ := rfl
  rw [hM]
  clear_value B
  by_cases hu : IsUnit B.det
  · have h1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hu
    have h2 : Bᴴ * (B⁻¹)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    have hBH : Bᴴ - B = (2 * Complex.I * ((w.im : ℝ) : ℂ)) • (1 : Matrix ι ι ℂ) := by
      rw [hB, Matrix.conjTranspose_sub, hΛ.eq, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one]
      rw [show Λ - star w • (1 : Matrix ι ι ℂ) - (Λ - w • 1) = (w - star w) • (1 : Matrix ι ι ℂ)
        by rw [sub_smul]; abel]
      have h3 : w - star w = 2 * Complex.I * ((w.im : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
        ring
      rw [h3]
    have key : B⁻¹ - (B⁻¹)ᴴ = (2 * Complex.I * ((w.im : ℝ) : ℂ)) • (B⁻¹ * (B⁻¹)ᴴ) := by
      calc B⁻¹ - (B⁻¹)ᴴ = B⁻¹ * (Bᴴ * (B⁻¹)ᴴ) - (B⁻¹ * B) * (B⁻¹)ᴴ := by
            rw [h2, h1]; simp
        _ = B⁻¹ * (Bᴴ - B) * (B⁻¹)ᴴ := by simp only [mul_sub, sub_mul, mul_assoc]
        _ = (2 * Complex.I * ((w.im : ℝ) : ℂ)) • (B⁻¹ * (B⁻¹)ᴴ) := by
          rw [hBH]; simp
    rw [key, smul_smul]
    congr 1
    field_simp
  · rw [Matrix.nonsing_inv_apply_not_isUnit B hu]
    simp

end RBMTransitionEdge

end
