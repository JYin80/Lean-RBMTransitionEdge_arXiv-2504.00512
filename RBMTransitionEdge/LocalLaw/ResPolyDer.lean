module

public import RBMTransitionEdge.LocalLaw.ResPoly
public import RBMTransitionEdge.LocalLaw.ResSmooth

@[expose] public section

/-!
# Wirtinger calculus of resolvent polynomials

The first Wirtinger derivatives of the resolvent (2.12) [def_resolv] along a Hermitian slice
`w ↦ setEntry h i j w` of Lemma 2.11 [lem:complex_cumu], at the level of the matrix; the
derivatives of resolvent polynomials, which are again resolvent polynomials; the bound on their
iterated derivatives; and their smoothness through the Hermitian part.
-/

open Matrix

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- One derivative of a resolvent monomial in the direction `c E_{ab}`: each factor
`x^* (h + Λ - ξ)⁻¹ y` is replaced in turn by `-c (x^* (h + Λ - ξ)⁻¹ e_a)(e_b^* (h + Λ - ξ)⁻¹ y)`,
both with the factor's own `Λ` and `ξ`. -/
def resMonoD {D N : ℕ} (a b : Idx D N) (c : ℂ) : ResMono D N → ResPoly D N
  | [] => []
  | f :: m => (-c, (f.1, Pi.single a 1, f.2.2.1, f.2.2.2) ::
        (Pi.single b 1, f.2.1, f.2.2.1, f.2.2.2) :: m) ::
      (resMonoD a b c m).map fun t => (t.1, f :: t.2)

/-- One derivative of a resolvent polynomial in the direction `c E_{ab}`, term by term. -/
def resPolyD {D N : ℕ} (a b : Idx D N) (c : ℂ) (P : ResPoly D N) : ResPoly D N :=
  P.flatMap fun t => (resMonoD a b c t.2).map fun s => (t.1 * s.1, s.2)

/-! ### Smoothness of resolvent polynomials -/

/-- The factor `x^* (h + Λ - ξ)⁻¹ y` as a double sum of resolvent entries. -/
private lemma RPD_factor_eq {D N : ℕ} (f : ResFactor D N) (h : Idx D N → Idx D N → ℂ) :
    resFactorEval f h = ∑ k, ∑ l, star (f.1 k) *
      (res (Matrix.of h + f.2.2.1) f.2.2.2 k l * f.2.1 l) := by
  simp only [resFactorEval, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]

/-- A factor with Hermitian `Λ` and `Im ξ ≠ 0` is smooth in the Hermitian part. -/
private lemma RPD_contDiff_factor {D N : ℕ} (f : ResFactor D N)
    (hf : f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) (n : ℕ) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => resFactorEval f (symArr h)) := by
  simp only [RPD_factor_eq]
  exact ContDiff.sum fun k _ => ContDiff.sum fun l _ => contDiff_const.mul
    ((contDiff_res_symArr _ hf.1 _ hf.2 k l n).mul contDiff_const)

/-- A monomial is smooth in the Hermitian part. -/
private lemma RPD_contDiff_mono {D N : ℕ} (m : ResMono D N)
    (hm : ∀ f ∈ m, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) (n : ℕ) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => resMonoEval m (symArr h)) := by
  induction m with
  | nil => simp only [resMonoEval, List.map_nil, List.prod_nil]; exact contDiff_const
  | cons f m ih =>
    have ih' := ih fun g hg => hm g (List.mem_cons_of_mem _ hg)
    simp only [resMonoEval, List.map_cons, List.prod_cons] at ih' ⊢
    exact (RPD_contDiff_factor f (hm f List.mem_cons_self) n).mul ih'

/-- A resolvent polynomial is smooth in the Hermitian part. -/
private lemma RPD_contDiff_poly {D N : ℕ} (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) (n : ℕ) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => resPolyEval P (symArr h)) := by
  induction P with
  | nil => simp only [resPolyEval, List.map_nil, List.sum_nil]; exact contDiff_const
  | cons t P ih =>
    have ih' := ih fun u hu => hP u (List.mem_cons_of_mem _ hu)
    simp only [resPolyEval, List.map_cons, List.sum_cons] at ih' ⊢
    exact (contDiff_const.mul (RPD_contDiff_mono t.2 (hP t List.mem_cons_self) n)).add ih'

/-! ### The slice `w ↦ setEntry h i j w` -/

/-- For a Hermitian array the slice is its own Hermitian part. -/
private lemma RPD_symArr_slice {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    symArr (setEntry h i j w) = setEntry h i j w := by
  rw [symArr_setEntry, symArr_of_isHermitian h hh]

/-- A Hermitian array stays Hermitian after the one-entry substitution. -/
private lemma RPD_slice_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  rw [← RPD_symArr_slice h hh i j w]
  exact symArr_isHermitian _

/-- The real derivative of the entry `(p, m)` of the slice `w ↦ setEntry h i j w`. -/
private def RPD_dS {D N : ℕ} (i j p m : Idx D N) : ℂ →L[ℝ] ℂ :=
  if i = j then (if p = i ∧ m = i then Complex.ofRealCLM.comp Complex.reCLM else 0)
  else if p = i ∧ m = j then ContinuousLinearMap.id ℝ ℂ
  else if p = j ∧ m = i then (Complex.conjCLE : ℂ →L[ℝ] ℂ) else 0

/-- Every entry of the slice is real-differentiable with derivative `RPD_dS`. -/
private lemma RPD_hasFDerivAt_setEntry {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j p m : Idx D N)
    (w : ℂ) : HasFDerivAt (fun x => setEntry h i j x p m) (RPD_dS i j p m) w := by
  unfold RPD_dS
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    by_cases hpm : p = i ∧ m = i
    · have e : (fun x => setEntry h i i x p m) = fun x => ((x.re : ℝ) : ℂ) := by
        funext x; simp [setEntry, hpm]
      rw [e, ite_eq_left hpm]
      exact (Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt
    · have e : (fun x => setEntry h i i x p m) = fun _ => h p m := by
        funext x; simp [setEntry, hpm]
      rw [e, ite_eq_right hpm]
      exact hasFDerivAt_const _ _
  · rw [ite_eq_right hij]
    by_cases h1 : p = i ∧ m = j
    · have e : (fun x => setEntry h i j x p m) = fun x => x := by
        funext x; simp [setEntry, hij, h1]
      rw [e, ite_eq_left h1]
      exact hasFDerivAt_id w
    · rw [ite_eq_right h1]
      by_cases h2 : p = j ∧ m = i
      · have e : (fun x => setEntry h i j x p m) = fun x => starRingEnd ℂ x := by
          funext x; simp [setEntry, hij, h2]
        rw [e, ite_eq_left h2]
        exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
      · have e : (fun x => setEntry h i j x p m) = fun _ => h p m := by
          funext x; simp [setEntry, hij, h1, h2]
        rw [e, ite_eq_right h2]
        exact hasFDerivAt_const _ _

/-- The slice is smooth. -/
private lemma RPD_contDiff_slice {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
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

/-- A resolvent polynomial along a Hermitian slice is smooth in the one complex variable. -/
private lemma RPD_contDiff_poly_slice {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) (n : ℕ) :
    ContDiff ℝ n (fun w : ℂ => resPolyEval P (setEntry h i j w)) := by
  have e : (fun w : ℂ => resPolyEval P (setEntry h i j w)) =
      (fun h' : Idx D N → Idx D N → ℂ => resPolyEval P (symArr h')) ∘
        fun w => setEntry h i j w := by
    funext w
    simp only [Function.comp, RPD_symArr_slice h hh]
  rw [e]
  exact (RPD_contDiff_poly P hP n).comp (RPD_contDiff_slice h i j n)

/-- A resolvent monomial along a Hermitian slice is smooth in the one complex variable. -/
private lemma RPD_contDiff_mono_slice {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (m : ResMono D N)
    (hm : ∀ f ∈ m, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) (n : ℕ) :
    ContDiff ℝ n (fun w : ℂ => resMonoEval m (setEntry h i j w)) := by
  have e : (fun w : ℂ => resMonoEval m (setEntry h i j w)) =
      (fun h' : Idx D N → Idx D N → ℂ => resMonoEval m (symArr h')) ∘
        fun w => setEntry h i j w := by
    funext w
    simp only [Function.comp, RPD_symArr_slice h hh]
  rw [e]
  exact (RPD_contDiff_mono m hm n).comp (RPD_contDiff_slice h i j n)

/-! ### The derivative of a family of inverses -/

/-- If `G(x) M(x) = 1` for all `x` and `M(w) G(w) = 1`, with differentiable entries at `w`, then
`D G(w) = - G(w) (D M(w)) G(w)` in every direction `v`, entrywise. -/
private lemma RPD_fderiv_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Mf Gf : ℂ → Matrix ι ι ℂ) (w v : ℂ)
    (hM : ∀ p l, DifferentiableAt ℝ (fun x => Mf x p l) w)
    (hG : ∀ p l, DifferentiableAt ℝ (fun x => Gf x p l) w)
    (h1 : ∀ x, Gf x * Mf x = 1) (h2 : Mf w * Gf w = 1) (k l : ι) :
    fderiv ℝ (fun x => Gf x k l) w v =
      -∑ p, ∑ m, Gf w k p * fderiv ℝ (fun x => Mf x p m) w v * Gf w m l := by
  set Dm : Matrix ι ι ℂ := Matrix.of fun p l => fderiv ℝ (fun x => Gf x p l) w v with hDm
  set dM : Matrix ι ι ℂ := Matrix.of fun p l => fderiv ℝ (fun x => Mf x p l) w v with hdM
  have key : Dm * Mf w + Gf w * dM = 0 := by
    ext k m
    have e1 : (fun x => (Gf x * Mf x) k m) = fun _ => (1 : Matrix ι ι ℂ) k m := by
      funext x; rw [h1 x]
    have hd : HasFDerivAt (fun x => (Gf x * Mf x) k m)
        (∑ p, (Gf w k p • fderiv ℝ (fun x => Mf x p m) w +
          Mf w p m • fderiv ℝ (fun x => Gf x k p) w)) w := by
      simp only [Matrix.mul_apply]
      exact HasFDerivAt.fun_sum fun p _ => (hG k p).hasFDerivAt.mul (hM p m).hasFDerivAt
    rw [e1] at hd
    have h0 := congrArg (fun L => L v) ((hasFDerivAt_const ((1 : Matrix ι ι ℂ) k m) w).unique hd)
    simp only [_root_.zero_apply, _root_.sum_apply, _root_.add_apply, _root_.smul_apply,
      smul_eq_mul] at h0
    simp only [Matrix.add_apply, Matrix.mul_apply, hDm, hdM, Matrix.of_apply, Matrix.zero_apply]
    rw [h0, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have e : Dm = -(Gf w * dM * Gf w) := by
    calc Dm = Dm * (Mf w * Gf w) := by rw [h2, mul_one]
      _ = (Dm * Mf w) * Gf w := by rw [mul_assoc]
      _ = (-(Gf w * dM)) * Gf w := by rw [eq_neg_of_add_eq_zero_left key]
      _ = -(Gf w * dM * Gf w) := by rw [neg_mul]
  have := congrFun (congrFun e k) l
  simp only [hDm, Matrix.of_apply, Matrix.neg_apply, Matrix.mul_apply, hdM] at this
  rw [this]
  congr 1
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

/-- The derivative `RPD_dS` applied to a direction. -/
private lemma RPD_dS_apply {D N : ℕ} (i j p m : Idx D N) (v : ℂ) :
    RPD_dS i j p m v = if i = j then (if p = i ∧ m = i then ((v.re : ℝ) : ℂ) else 0)
      else (if p = i ∧ m = j then v else 0) + (if p = j ∧ m = i then starRingEnd ℂ v else 0) := by
  unfold RPD_dS
  by_cases hij : i = j
  · subst hij
    by_cases hpm : p = i ∧ m = i <;> simp [hpm]
  · by_cases h1 : p = i ∧ m = j
    · have h2 : ¬ (p = j ∧ m = i) := fun h2 => hij (h1.1.symm.trans h2.1)
      simp [hij, h1]
    · by_cases h2 : p = j ∧ m = i <;> simp [hij, h1, h2]

/-- A double sum with a single nonzero term. -/
private lemma RPD_sum_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) (F : ι → ι → ℂ) :
    ∑ p, ∑ m, (if p = a ∧ m = b then F p m else 0) = F a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro m _ hm; simp [hm]
    · simp
  · intro p _ hp; simp [hp]
  · simp

/-- The contraction of `G dM(v) G` against the slice derivative. -/
private lemma RPD_sum_dS {D N : ℕ} (G : Matrix (Idx D N) (Idx D N) ℂ) (i j k l : Idx D N)
    (v : ℂ) :
    ∑ p, ∑ m, G k p * RPD_dS i j p m v * G m l =
      if i = j then ((v.re : ℝ) : ℂ) * (G k i * G i l)
      else v * (G k i * G j l) + starRingEnd ℂ v * (G k j * G i l) := by
  simp only [RPD_dS_apply]
  by_cases hij : i = j
  · simp only [hij, ite_true, mul_ite, ite_mul, mul_zero, zero_mul]
    rw [RPD_sum_pair j j (fun p m => G k p * ((v.re : ℝ) : ℂ) * G m l)]
    ring
  · simp only [hij, ite_false, mul_add, add_mul, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_add_distrib]
    rw [RPD_sum_pair i j (fun p m => G k p * v * G m l),
      RPD_sum_pair j i (fun p m => G k p * starRingEnd ℂ v * G m l)]
    ring

/-- The first Wirtinger derivatives of the resolvent (2.12) [def_resolv]
`G(w) = (setEntry h i j w + Λ - ξ)⁻¹` along a Hermitian slice, at the level of the matrix:
`∂_w G = -c G E_{ij} G` and `∂_{w̄} G = -c G E_{ji} G`, entrywise
`∂_w G_{kl} = -c G_{ki} G_{jl}` and `∂_{w̄} G_{kl} = -c G_{kj} G_{il}`, with `c = 1` for `i ≠ j`
and `c = 1/2` for `i = j`; `Λ` Hermitian and `Im ξ ≠ 0`. -/
theorem res_dW {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (ξ : ℂ)
    (hξ : ξ.im ≠ 0) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j k l : Idx D N) :
    dW (fun w => res (Matrix.of (setEntry h i j w) + Λ) ξ k l) =
        (fun w => -(if i = j then 1 / 2 else 1) *
          (res (Matrix.of (setEntry h i j w) + Λ) ξ k i *
            res (Matrix.of (setEntry h i j w) + Λ) ξ j l)) ∧
      dWbar (fun w => res (Matrix.of (setEntry h i j w) + Λ) ξ k l) =
        (fun w => -(if i = j then 1 / 2 else 1) *
          (res (Matrix.of (setEntry h i j w) + Λ) ξ k j *
            res (Matrix.of (setEntry h i j w) + Λ) ξ i l)) := by
  set Mf : ℂ → Matrix (Idx D N) (Idx D N) ℂ :=
    fun w => Matrix.of (setEntry h i j w) + Λ - ξ • (1 : Matrix (Idx D N) (Idx D N) ℂ) with hMf
  set Gf : ℂ → Matrix (Idx D N) (Idx D N) ℂ :=
    fun w => res (Matrix.of (setEntry h i j w) + Λ) ξ with hGf
  have hGM : ∀ x, Gf x * Mf x = 1 := fun x =>
    (res_mul_sub_of_im_ne _ ((RPD_slice_herm h hh i j x).add hΛ) ξ hξ).2
  have hMG : ∀ x, Mf x * Gf x = 1 := fun x =>
    (res_mul_sub_of_im_ne _ ((RPD_slice_herm h hh i j x).add hΛ) ξ hξ).1
  have hMd : ∀ w p m, HasFDerivAt (fun x => Mf x p m) (RPD_dS i j p m) w := by
    intro w p m
    exact ((RPD_hasFDerivAt_setEntry h i j p m w).add_const (Λ p m)).sub_const
      ((ξ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) p m)
  have hGd : ∀ w p m, DifferentiableAt ℝ (fun x => Gf x p m) w := by
    intro w p m
    have e : (fun x => Gf x p m) = (fun h' : Idx D N → Idx D N → ℂ =>
        res (Matrix.of (symArr h') + Λ) ξ p m) ∘ fun x => setEntry h i j x := by
      funext x
      simp only [hGf, Function.comp, RPD_symArr_slice h hh]
    rw [e]
    exact ((contDiff_res_symArr Λ hΛ ξ hξ p m 1).comp (RPD_contDiff_slice h i j 1)).differentiable
      (by norm_num) w
  have hder : ∀ w v k l, fderiv ℝ (fun x => Gf x k l) w v =
      -(if i = j then ((v.re : ℝ) : ℂ) * (Gf w k i * Gf w i l)
        else v * (Gf w k i * Gf w j l) + starRingEnd ℂ v * (Gf w k j * Gf w i l)) := by
    intro w v k l
    rw [← RPD_sum_dS]
    refine RPD_fderiv_inv Mf Gf w v (fun p m => (hMd w p m).differentiableAt) (hGd w) hGM
      (hMG w) k l ▸ ?_
    congr 1
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun m _ => ?_
    rw [(hMd w p m).fderiv]
  change dW (fun w => Gf w k l) = (fun w => -(if i = j then 1 / 2 else 1) *
        (Gf w k i * Gf w j l)) ∧
      dWbar (fun w => Gf w k l) = (fun w => -(if i = j then 1 / 2 else 1) *
        (Gf w k j * Gf w i l))
  constructor
  · funext w
    simp only [dW, hder]
    by_cases hij : i = j
    · simp only [hij, ite_true, Complex.one_re, Complex.I_re, Complex.ofReal_one,
        Complex.ofReal_zero]
      subst hij
      ring
    · simp only [hij, ite_false, map_one, Complex.conj_I]
      linear_combination (Gf w k i * Gf w j l - Gf w k j * Gf w i l) / 2 * Complex.I_sq
  · funext w
    simp only [dWbar, hder]
    by_cases hij : i = j
    · simp only [hij, ite_true, Complex.one_re, Complex.I_re, Complex.ofReal_one,
        Complex.ofReal_zero]
      subst hij
      ring
    · simp only [hij, ite_false, map_one, Complex.conj_I]
      linear_combination (Gf w k j * Gf w i l - Gf w k i * Gf w j l) / 2 * Complex.I_sq

/-! ### Linearity of the Wirtinger derivatives -/

/-- The Wirtinger derivatives of a sum. -/
private lemma RPD_add {F G : ℂ → ℂ} {w : ℂ} (hF : DifferentiableAt ℝ F w)
    (hG : DifferentiableAt ℝ G w) :
    dW (fun x => F x + G x) w = dW F w + dW G w ∧
      dWbar (fun x => F x + G x) w = dWbar F w + dWbar G w := by
  have e : fderiv ℝ (fun x => F x + G x) w = fderiv ℝ F w + fderiv ℝ G w := fderiv_fun_add hF hG
  constructor
  · simp only [dW, e, _root_.add_apply]; ring
  · simp only [dWbar, e, _root_.add_apply]; ring

/-- The Wirtinger derivatives of a constant multiple. -/
private lemma RPD_const_mul {F : ℂ → ℂ} {w : ℂ} (c : ℂ) (hF : DifferentiableAt ℝ F w) :
    dW (fun x => c * F x) w = c * dW F w ∧ dWbar (fun x => c * F x) w = c * dWbar F w := by
  have e : fderiv ℝ (fun x => c * F x) w = c • fderiv ℝ F w := fderiv_const_mul hF c
  constructor
  · simp only [dW, e, _root_.smul_apply, smul_eq_mul]; ring
  · simp only [dWbar, e, _root_.smul_apply, smul_eq_mul]; ring

/-- The Wirtinger derivatives of a finite sum. -/
private lemma RPD_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) {w : ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) w) :
    dW (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, dW (F a) w ∧
      dWbar (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, dWbar (F a) w := by
  have e : fderiv ℝ (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, fderiv ℝ (F a) w := fderiv_fun_sum hF
  constructor
  · simp only [dW, e, _root_.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  · simp only [dWbar, e, _root_.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_div]

/-! ### The derivative of a factor -/

/-- The value of `(x, e_a, Λ, ξ)`: `Σ_k x̄_k G_{ka}`. -/
private lemma RPD_eval_right {D N : ℕ} (x : Idx D N → ℂ) (a : Idx D N)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (ξ : ℂ) (h' : Idx D N → Idx D N → ℂ) :
    resFactorEval (x, Pi.single a 1, Λ, ξ) h' =
      ∑ k, star (x k) * res (Matrix.of h' + Λ) ξ k a := by
  rw [RPD_factor_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq']

/-- The value of `(e_b, y, Λ, ξ)`: `Σ_l G_{bl} y_l`. -/
private lemma RPD_eval_left {D N : ℕ} (b : Idx D N) (y : Idx D N → ℂ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (ξ : ℂ) (h' : Idx D N → Idx D N → ℂ) :
    resFactorEval (Pi.single b 1, y, Λ, ξ) h' =
      ∑ l, res (Matrix.of h' + Λ) ξ b l * y l := by
  rw [RPD_factor_eq, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp
  · intro k _ hk
    simp [hk]
  · simp

/-- The first Wirtinger derivatives of one factor `x^* (h + Λ - ξ)⁻¹ y` along the slice, from
`res_dW`: `-c (x^* G e_a)(e_b^* G y)` with `(a, b) = (i, j)` for `∂_w` and `(j, i)` for
`∂_{w̄}`. -/
private lemma RPD_factor_dW {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (f : ResFactor D N) (hf : f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) :
    dW (fun w => resFactorEval f (setEntry h i j w)) =
        (fun w => -(if i = j then (1 / 2 : ℂ) else 1) *
          (resFactorEval (f.1, Pi.single i 1, f.2.2.1, f.2.2.2) (setEntry h i j w) *
            resFactorEval (Pi.single j 1, f.2.1, f.2.2.1, f.2.2.2) (setEntry h i j w))) ∧
      dWbar (fun w => resFactorEval f (setEntry h i j w)) =
        (fun w => -(if i = j then (1 / 2 : ℂ) else 1) *
          (resFactorEval (f.1, Pi.single j 1, f.2.2.1, f.2.2.2) (setEntry h i j w) *
            resFactorEval (Pi.single i 1, f.2.1, f.2.2.1, f.2.2.2) (setEntry h i j w))) := by
  obtain ⟨x, y, Λ, ξ⟩ := f
  obtain ⟨hΛ, hξ⟩ := hf
  simp only at hΛ hξ
  have hd0 : ∀ (k l : Idx D N) (w : ℂ), DifferentiableAt ℝ
      (fun x' => res (Matrix.of (setEntry h i j x') + Λ) ξ k l) w := by
    intro k l w
    have e : (fun x' => res (Matrix.of (setEntry h i j x') + Λ) ξ k l) =
        (fun h' : Idx D N → Idx D N → ℂ => res (Matrix.of (symArr h') + Λ) ξ k l) ∘
          fun x' => setEntry h i j x' := by
      funext x'
      simp only [Function.comp, RPD_symArr_slice h hh]
    rw [e]
    exact ((contDiff_res_symArr Λ hΛ ξ hξ k l 1).comp (RPD_contDiff_slice h i j 1)).differentiable
      (by norm_num) w
  have hd : ∀ (k l : Idx D N) (w : ℂ), DifferentiableAt ℝ
      (fun x' => star (x k) * y l * res (Matrix.of (setEntry h i j x') + Λ) ξ k l) w :=
    fun k l w => (differentiableAt_const _).mul (hd0 k l w)
  have hexp : ∀ w, resFactorEval (x, y, Λ, ξ) (setEntry h i j w) =
      ∑ k, ∑ l, star (x k) * y l * res (Matrix.of (setEntry h i j w) + Λ) ξ k l := by
    intro w
    rw [RPD_factor_eq]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hcomb : ∀ (w : ℂ) (a b : Idx D N),
      resFactorEval (x, Pi.single a 1, Λ, ξ) (setEntry h i j w) *
          resFactorEval (Pi.single b 1, y, Λ, ξ) (setEntry h i j w) =
        ∑ k, ∑ l, star (x k) * y l *
          (res (Matrix.of (setEntry h i j w)  + Λ) ξ k a *
            res (Matrix.of (setEntry h i j w) + Λ) ξ b l) := by
    intro w a b
    rw [RPD_eval_right, RPD_eval_left, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hsum : ∀ (F : Idx D N → Idx D N → ℂ → ℂ) (w : ℂ),
      (∀ k l, DifferentiableAt ℝ (F k l) w) →
      dW (fun x' => ∑ k, ∑ l, F k l x') w = ∑ k, ∑ l, dW (F k l) w ∧
        dWbar (fun x' => ∑ k, ∑ l, F k l x') w = ∑ k, ∑ l, dWbar (F k l) w := by
    intro F w hF
    have h1 : ∀ k, DifferentiableAt ℝ (fun x' => ∑ l, F k l x') w := fun k =>
      DifferentiableAt.fun_sum fun l _ => hF k l
    have h2 := RPD_sum Finset.univ (fun k x' => ∑ l, F k l x') (w := w) fun k _ => h1 k
    have h3 : ∀ k, dW (fun x' => ∑ l, F k l x') w = ∑ l, dW (F k l) w ∧
        dWbar (fun x' => ∑ l, F k l x') w = ∑ l, dWbar (F k l) w := fun k =>
      RPD_sum Finset.univ (F k) (w := w) fun l _ => hF k l
    refine ⟨?_, ?_⟩
    · rw [h2.1]; exact Finset.sum_congr rfl fun k _ => (h3 k).1
    · rw [h2.2]; exact Finset.sum_congr rfl fun k _ => (h3 k).2
  constructor
  · funext w
    simp only [hexp]
    rw [(hsum (fun k l x' => star (x k) * y l * res (Matrix.of (setEntry h i j x') + Λ) ξ k l)
      w (fun k l => hd k l w)).1]
    simp only [hcomb]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [(RPD_const_mul (F := fun x' => res (Matrix.of (setEntry h i j x') + Λ) ξ k l)
      (star (x k) * y l) (hd0 k l w)).1, (res_dW Λ hΛ ξ hξ h hh i j k l).1]
    ring
  · funext w
    simp only [hexp]
    rw [(hsum (fun k l x' => star (x k) * y l * res (Matrix.of (setEntry h i j x') + Λ) ξ k l)
      w (fun k l => hd k l w)).2]
    simp only [hcomb]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [(RPD_const_mul (F := fun x' => res (Matrix.of (setEntry h i j x') + Λ) ξ k l)
      (star (x k) * y l) (hd0 k l w)).2, (res_dW Λ hΛ ξ hξ h hh i j k l).2]
    ring

/-! ### The derivative of a monomial and of a polynomial -/

/-- A factor along a Hermitian slice is smooth in the one complex variable. -/
private lemma RPD_contDiff_factor_slice {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (f : ResFactor D N)
    (hf : f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) (n : ℕ) :
    ContDiff ℝ n (fun w : ℂ => resFactorEval f (setEntry h i j w)) := by
  have e : (fun w : ℂ => resFactorEval f (setEntry h i j w)) =
      (fun h' : Idx D N → Idx D N → ℂ => resFactorEval f (symArr h')) ∘
        fun w => setEntry h i j w := by
    funext w
    simp only [Function.comp, RPD_symArr_slice h hh]
  rw [e]
  exact (RPD_contDiff_factor f hf n).comp (RPD_contDiff_slice h i j n)

/-- The value of a polynomial with a leading term. -/
private lemma RPD_eval_cons {D N : ℕ} (t : ℂ × ResMono D N) (P : ResPoly D N)
    (h' : Idx D N → Idx D N → ℂ) :
    resPolyEval (t :: P) h' = t.1 * resMonoEval t.2 h' + resPolyEval P h' := by
  simp [resPolyEval]

/-- The value of a polynomial whose monomials all get one more leading factor. -/
private lemma RPD_eval_map_cons {D N : ℕ} (f : ResFactor D N) (Q : ResPoly D N)
    (h' : Idx D N → Idx D N → ℂ) :
    resPolyEval (Q.map fun t => (t.1, f :: t.2)) h' = resFactorEval f h' * resPolyEval Q h' := by
  induction Q with
  | nil => simp [resPolyEval]
  | cons t Q ih =>
    rw [List.map_cons, RPD_eval_cons, ih, RPD_eval_cons]
    simp only [resMonoEval, List.map_cons, List.prod_cons]
    ring

/-- The value of a polynomial whose coefficients are all multiplied by `c₀`. -/
private lemma RPD_eval_map_mul {D N : ℕ} (c₀ : ℂ) (Q : ResPoly D N)
    (h' : Idx D N → Idx D N → ℂ) :
    resPolyEval (Q.map fun s => (c₀ * s.1, s.2)) h' = c₀ * resPolyEval Q h' := by
  induction Q with
  | nil => simp [resPolyEval]
  | cons t Q ih =>
    rw [List.map_cons, RPD_eval_cons, ih, RPD_eval_cons]
    ring

/-- The derivative of a monomial along the slice is `resMonoD` (product rule). -/
private lemma RPD_mono_dW {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (m : ResMono D N)
    (hm : ∀ f ∈ m, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) :
    dW (fun w => resMonoEval m (setEntry h i j w)) =
        (fun w => resPolyEval (resMonoD i j (if i = j then (1 / 2 : ℂ) else 1) m)
          (setEntry h i j w)) ∧
      dWbar (fun w => resMonoEval m (setEntry h i j w)) =
        (fun w => resPolyEval (resMonoD j i (if i = j then (1 / 2 : ℂ) else 1) m)
          (setEntry h i j w)) := by
  induction m with
  | nil =>
    refine ⟨?_, ?_⟩ <;> · funext w; simp [dW, dWbar, resMonoEval, resMonoD, resPolyEval]
  | cons f m ih =>
    have ih' := ih fun g hg => hm g (List.mem_cons_of_mem _ hg)
    have hf := RPD_factor_dW h hh i j f (hm f List.mem_cons_self)
    have hdf : ∀ w, DifferentiableAt ℝ (fun w' => resFactorEval f (setEntry h i j w')) w :=
      fun w => (RPD_contDiff_factor_slice h hh i j f (hm f List.mem_cons_self) 1).differentiable
        (by norm_num) w
    have hdm : ∀ w, DifferentiableAt ℝ (fun w' => resMonoEval m (setEntry h i j w')) w :=
      fun w => (RPD_contDiff_mono_slice h hh i j m
        (fun g hg => hm g (List.mem_cons_of_mem _ hg)) 1).differentiable (by norm_num) w
    have e : (fun w => resMonoEval (f :: m) (setEntry h i j w)) =
        fun w => resFactorEval f (setEntry h i j w) * resMonoEval m (setEntry h i j w) := by
      funext w
      simp only [resMonoEval, List.map_cons, List.prod_cons]
    rw [e]
    constructor
    · funext w
      rw [(dW_mul (hdf w) (hdm w)).1, congrFun hf.1 w, congrFun ih'.1 w]
      simp only [resMonoD, RPD_eval_cons, RPD_eval_map_cons, resMonoEval, List.map_cons,
        List.prod_cons]
      ring
    · funext w
      rw [(dW_mul (hdf w) (hdm w)).2, congrFun hf.2 w, congrFun ih'.2 w]
      simp only [resMonoD, RPD_eval_cons, RPD_eval_map_cons, resMonoEval, List.map_cons,
        List.prod_cons]
      ring

/-- The factors of the terms of `resMonoD a b c m`: each is a factor of `m`, or one of the two
factors that replace it; the length goes up by one and every coefficient is `-c`. -/
private lemma RPD_resMonoD_mem {D N : ℕ} (a b : Idx D N) (c : ℂ) (m : ResMono D N) :
    ∀ s ∈ resMonoD a b c m, s.2.length = m.length + 1 ∧ s.1 = -c ∧ ∀ g ∈ s.2, ∃ f ∈ m,
      g = f ∨ g = (f.1, Pi.single a 1, f.2.2.1, f.2.2.2) ∨
        g = (Pi.single b 1, f.2.1, f.2.2.1, f.2.2.2) := by
  induction m with
  | nil => intro s hs; simp [resMonoD] at hs
  | cons f m ih =>
    intro s hs
    simp only [resMonoD, List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | ⟨t, ht, rfl⟩
    · refine ⟨by simp, rfl, fun g hg => ?_⟩
      simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact ⟨f, List.mem_cons_self, Or.inr (Or.inl rfl)⟩
      · exact ⟨f, List.mem_cons_self, Or.inr (Or.inr rfl)⟩
      · exact ⟨g, List.mem_cons_of_mem _ hg, Or.inl rfl⟩
    · obtain ⟨h1, h2, h3⟩ := ih t ht
      refine ⟨by simp [h1], h2, fun g hg => ?_⟩
      simp only [List.mem_cons] at hg
      rcases hg with hg | hg
      · exact ⟨f, List.mem_cons_self, Or.inl hg⟩
      · obtain ⟨f', hf', hg'⟩ := h3 g hg
        exact ⟨f', List.mem_cons_of_mem _ hf', hg'⟩

/-- The terms of `resPolyD a b c P`: each comes from a term of `P`, with one more factor, the
factors being those of the term or the two that replace one of them. -/
private lemma RPD_resPolyD_mem {D N : ℕ} (a b : Idx D N) (c : ℂ) (P : ResPoly D N) :
    ∀ u ∈ resPolyD a b c P, ∃ t ∈ P, u.2.length = t.2.length + 1 ∧ ∀ g ∈ u.2, ∃ f ∈ t.2,
      g = f ∨ g = (f.1, Pi.single a 1, f.2.2.1, f.2.2.2) ∨
        g = (Pi.single b 1, f.2.1, f.2.2.1, f.2.2.2) := by
  intro u hu
  unfold resPolyD at hu
  rw [List.mem_flatMap] at hu
  obtain ⟨t, ht, hu⟩ := hu
  rw [List.mem_map] at hu
  obtain ⟨s, hs, rfl⟩ := hu
  obtain ⟨hlen, -, hg⟩ := RPD_resMonoD_mem a b c t.2 s hs
  exact ⟨t, ht, hlen, hg⟩

/-- One derivative keeps the hypotheses on `(Λ, ξ)` of every factor. -/
private lemma RPD_hyp_resPolyD {D N : ℕ} (a b : Idx D N) (c : ℂ) (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) :
    ∀ t ∈ resPolyD a b c P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
  intro u hu g hg
  obtain ⟨t, ht, -, h2⟩ := RPD_resPolyD_mem a b c P u hu
  obtain ⟨f, hf, hgf⟩ := h2 g hg
  rcases hgf with h | h | h <;> rw [h] <;> exact hP t ht f hf

/-- Iterated derivatives keep the hypotheses on `(Λ, ξ)` of every factor. -/
private lemma RPD_hyp_iterate {D N : ℕ} (a b : Idx D N) (c : ℂ) (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) (n : ℕ) :
    ∀ t ∈ (resPolyD a b c)^[n] P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
  induction n with
  | zero => exact hP
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact RPD_hyp_resPolyD a b c _ ih

/-- The first Wirtinger derivatives of a resolvent polynomial along a Hermitian slice
`w ↦ setEntry h i j w` (Lemma 2.11 [lem:complex_cumu]): with `c = 1` for `i ≠ j` and `c = 1/2`
for `i = j`, `∂_w P` is the derivative in the direction `c E_{ij}` and `∂_{w̄} P` the derivative in
the direction `c E_{ji}`; every factor has a Hermitian `Λ` and `Im ξ ≠ 0`. -/
theorem resPoly_dW {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) :
    dW (fun w => resPolyEval P (setEntry h i j w)) =
        (fun w => resPolyEval (resPolyD i j (if i = j then 1 / 2 else 1) P) (setEntry h i j w)) ∧
      dWbar (fun w => resPolyEval P (setEntry h i j w)) =
        (fun w => resPolyEval (resPolyD j i (if i = j then 1 / 2 else 1) P)
          (setEntry h i j w)) := by
  induction P with
  | nil =>
    refine ⟨?_, ?_⟩ <;> · funext w; simp [dW, dWbar, resPolyEval, resPolyD]
  | cons t P ih =>
    have ih' := ih fun u hu => hP u (List.mem_cons_of_mem _ hu)
    have hm := RPD_mono_dW h hh i j t.2 (hP t List.mem_cons_self)
    have hdm : ∀ w, DifferentiableAt ℝ (fun w' => resMonoEval t.2 (setEntry h i j w')) w :=
      fun w => (RPD_contDiff_mono_slice h hh i j t.2 (hP t List.mem_cons_self) 1).differentiable
        (by norm_num) w
    have hdP : ∀ w, DifferentiableAt ℝ (fun w' => resPolyEval P (setEntry h i j w')) w :=
      fun w => (RPD_contDiff_poly_slice h hh i j P
        (fun u hu => hP u (List.mem_cons_of_mem _ hu)) 1).differentiable (by norm_num) w
    have e : (fun w => resPolyEval (t :: P) (setEntry h i j w)) = fun w =>
        t.1 * resMonoEval t.2 (setEntry h i j w) + resPolyEval P (setEntry h i j w) := by
      funext w
      rw [RPD_eval_cons]
    rw [e]
    constructor
    · funext w
      rw [(RPD_add (F := fun w' => t.1 * resMonoEval t.2 (setEntry h i j w'))
        ((differentiableAt_const _).mul (hdm w)) (hdP w)).1, (RPD_const_mul t.1 (hdm w)).1,
        congrFun hm.1 w, congrFun ih'.1 w]
      simp only [resPolyD, List.flatMap_cons, resPolyEval_append, RPD_eval_map_mul]
    · funext w
      rw [(RPD_add (F := fun w' => t.1 * resMonoEval t.2 (setEntry h i j w'))
        ((differentiableAt_const _).mul (hdm w)) (hdP w)).2, (RPD_const_mul t.1 (hdm w)).2,
        congrFun hm.2 w, congrFun ih'.2 w]
      simp only [resPolyD, List.flatMap_cons, resPolyEval_append, RPD_eval_map_mul]

/-- The iterated Wirtinger derivatives `∂_w^a ∂_{w̄}^b` of a resolvent polynomial along a
Hermitian slice: `a` derivatives in the direction `c E_{ij}` after `b` in the direction
`c E_{ji}`. -/
theorem resPoly_wirt {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) (a b : ℕ) :
    wirt a b (fun w => resPolyEval P (setEntry h i j w)) =
      fun w => resPolyEval ((resPolyD i j (if i = j then 1 / 2 else 1))^[a]
        ((resPolyD j i (if i = j then 1 / 2 else 1))^[b] P)) (setEntry h i j w) := by
  have hb : ∀ n : ℕ, dWbar^[n] (fun w => resPolyEval P (setEntry h i j w)) = fun w =>
      resPolyEval ((resPolyD j i (if i = j then 1 / 2 else 1))^[n] P) (setEntry h i j w) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact (resPoly_dW h hh i j _
        (RPD_hyp_iterate j i (if i = j then 1 / 2 else 1) P hP n)).2
  have hP' := RPD_hyp_iterate j i (if i = j then (1 / 2 : ℂ) else 1) P hP b
  have ha : ∀ n : ℕ, dW^[n] (fun w => resPolyEval
      ((resPolyD j i (if i = j then 1 / 2 else 1))^[b] P) (setEntry h i j w)) = fun w =>
      resPolyEval ((resPolyD i j (if i = j then 1 / 2 else 1))^[n]
        ((resPolyD j i (if i = j then 1 / 2 else 1))^[b] P)) (setEntry h i j w) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact (resPoly_dW h hh i j _
        (RPD_hyp_iterate i j (if i = j then 1 / 2 else 1) _ hP' n)).1
  unfold wirt
  rw [hb b]
  exact ha a

/-! ### The count of terms and the bound -/

/-- The sum of the moduli of the coefficients of a resolvent polynomial. -/
private def RPD_wt {D N : ℕ} (P : ResPoly D N) : ℝ := (P.map fun t => ‖t.1‖).sum

/-- At most `m` factors per term, with vectors in `V` and pairs in `Ξ`. -/
private def RPD_good {D N : ℕ} (V : Set (Idx D N → ℂ))
    (Ξ : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (m : ℕ) (P : ResPoly D N) : Prop :=
  ∀ t ∈ P, t.2.length ≤ m ∧ ∀ f ∈ t.2, f.1 ∈ V ∧ f.2.1 ∈ V ∧ f.2.2 ∈ Ξ

private lemma RPD_wt_nonneg {D N : ℕ} (P : ResPoly D N) : 0 ≤ RPD_wt P :=
  List.sum_nonneg fun x hx => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _

private lemma RPD_wt_cons {D N : ℕ} (t : ℂ × ResMono D N) (P : ResPoly D N) :
    RPD_wt (t :: P) = ‖t.1‖ + RPD_wt P := by
  simp [RPD_wt]

private lemma RPD_wt_append {D N : ℕ} (P Q : ResPoly D N) :
    RPD_wt (P ++ Q) = RPD_wt P + RPD_wt Q := by
  simp [RPD_wt, List.map_append, List.sum_append]

/-- Every derivative of a monomial of degree `d` is `d` terms with coefficient `-c`. -/
private lemma RPD_wt_resMonoD {D N : ℕ} (a b : Idx D N) (c : ℂ) (m : ResMono D N) :
    RPD_wt (resMonoD a b c m) = m.length * ‖c‖ := by
  induction m with
  | nil => simp [resMonoD, RPD_wt]
  | cons f m ih =>
    have e : RPD_wt ((resMonoD a b c m).map fun t => (t.1, f :: t.2)) =
        RPD_wt (resMonoD a b c m) := by
      simp [RPD_wt, Function.comp_def]
    simp only [resMonoD]
    rw [RPD_wt_cons, e, ih]
    simp only [norm_neg, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- The weight of a polynomial whose coefficients are all multiplied by `c₀`. -/
private lemma RPD_wt_map_mul {D N : ℕ} (c₀ : ℂ) (Q : ResPoly D N) :
    RPD_wt (Q.map fun s => (c₀ * s.1, s.2)) = ‖c₀‖ * RPD_wt Q := by
  induction Q with
  | nil => simp [RPD_wt]
  | cons t Q ih =>
    rw [List.map_cons, RPD_wt_cons, ih, RPD_wt_cons]
    simp only [norm_mul]
    ring

/-- The weight of one derivative of a polynomial. -/
private lemma RPD_wt_resPolyD {D N : ℕ} (a b : Idx D N) (c : ℂ) (P : ResPoly D N) :
    RPD_wt (resPolyD a b c P) = ‖c‖ * (P.map fun t => ‖t.1‖ * (t.2.length : ℝ)).sum := by
  induction P with
  | nil => simp [resPolyD, RPD_wt]
  | cons t P ih =>
    have e : resPolyD a b c (t :: P) =
        ((resMonoD a b c t.2).map fun s => (t.1 * s.1, s.2)) ++ resPolyD a b c P := by
      simp [resPolyD]
    rw [e, RPD_wt_append, RPD_wt_map_mul, RPD_wt_resMonoD, ih, List.map_cons, List.sum_cons]
    ring

/-- One derivative multiplies the weight by at most the degree bound `m`, when `‖c‖ ≤ 1`. -/
private lemma RPD_wt_resPolyD_le {D N : ℕ} (a b : Idx D N) (c : ℂ) (hc : ‖c‖ ≤ 1) (m : ℕ)
    (P : ResPoly D N) (hP : ∀ t ∈ P, t.2.length ≤ m) :
    RPD_wt (resPolyD a b c P) ≤ m * RPD_wt P := by
  have key : ∀ Q : ResPoly D N, (∀ t ∈ Q, t.2.length ≤ m) →
      (Q.map fun t => ‖t.1‖ * (t.2.length : ℝ)).sum ≤ m * RPD_wt Q := by
    intro Q
    induction Q with
    | nil => intro _; simp [RPD_wt]
    | cons t Q ih =>
      intro hQ
      have h1 := ih fun u hu => hQ u (List.mem_cons_of_mem _ hu)
      have h2 : (t.2.length : ℝ) ≤ m := by exact_mod_cast hQ t List.mem_cons_self
      rw [List.map_cons, List.sum_cons, RPD_wt_cons]
      nlinarith [norm_nonneg t.1, mul_le_mul_of_nonneg_left h2 (norm_nonneg t.1)]
  rw [RPD_wt_resPolyD]
  have h1 := key P hP
  have h3 : 0 ≤ (P.map fun t => ‖t.1‖ * (t.2.length : ℝ)).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
      exact mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  calc ‖c‖ * (P.map fun t => ‖t.1‖ * (t.2.length : ℝ)).sum
      ≤ 1 * (P.map fun t => ‖t.1‖ * (t.2.length : ℝ)).sum := mul_le_mul_of_nonneg_right hc h3
    _ ≤ m * RPD_wt P := by rw [one_mul]; exact h1

/-- One derivative in the direction `c E_{ab}` with `e_a, e_b ∈ V`: at most `m + 1` factors per
term, the vectors still in `V`, the pairs still in `Ξ`. -/
private lemma RPD_good_resPolyD {D N : ℕ} (V : Set (Idx D N → ℂ))
    (Ξ : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (a b : Idx D N) (c : ℂ)
    (ha : Pi.single a 1 ∈ V) (hb : Pi.single b 1 ∈ V) (m : ℕ) (P : ResPoly D N)
    (hP : RPD_good V Ξ m P) : RPD_good V Ξ (m + 1) (resPolyD a b c P) := by
  intro u hu
  obtain ⟨t, ht, hlen, hg⟩ := RPD_resPolyD_mem a b c P u hu
  obtain ⟨hl, hf⟩ := hP t ht
  refine ⟨by omega, fun g hg' => ?_⟩
  obtain ⟨f, hfm, hgf⟩ := hg g hg'
  obtain ⟨hf1, hf2, hf3⟩ := hf f hfm
  rcases hgf with h | h | h <;> rw [h]
  · exact ⟨hf1, hf2, hf3⟩
  · exact ⟨hf1, ha, hf3⟩
  · exact ⟨hb, hf2, hf3⟩

/-- The iterated count: each step raises the degree bound by one and multiplies the weight by at
most the current bound. -/
private lemma RPD_iter {D N : ℕ} (V : Set (Idx D N → ℂ))
    (Ξ : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (T : ResPoly D N → ResPoly D N)
    (hT : ∀ (m : ℕ) (Q : ResPoly D N), RPD_good V Ξ m Q →
      RPD_good V Ξ (m + 1) (T Q) ∧ RPD_wt (T Q) ≤ m * RPD_wt Q)
    (n m : ℕ) (Q : ResPoly D N) (hQ : RPD_good V Ξ m Q) :
    RPD_good V Ξ (m + n) (T^[n] Q) ∧ RPD_wt (T^[n] Q) ≤ ((m + n : ℕ) : ℝ) ^ n * RPD_wt Q := by
  induction n with
  | zero => exact ⟨hQ, by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Function.iterate_succ_apply']
    obtain ⟨h3, h4⟩ := hT (m + n) _ h1
    refine ⟨h3, ?_⟩
    have h5 : ((m + n : ℕ) : ℝ) * RPD_wt (T^[n] Q) ≤
        ((m + n : ℕ) : ℝ) * (((m + n : ℕ) : ℝ) ^ n * RPD_wt Q) :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    have h6 : ((m + n : ℕ) : ℝ) ^ (n + 1) ≤ ((m + (n + 1) : ℕ) : ℝ) ^ (n + 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ_of_le le_rfl) _
    calc RPD_wt (T (T^[n] Q)) ≤ ((m + n : ℕ) : ℝ) * RPD_wt (T^[n] Q) := h4
      _ ≤ ((m + n : ℕ) : ℝ) * (((m + n : ℕ) : ℝ) ^ n * RPD_wt Q) := h5
      _ = ((m + n : ℕ) : ℝ) ^ (n + 1) * RPD_wt Q := by ring
      _ ≤ ((m + (n + 1) : ℕ) : ℝ) ^ (n + 1) * RPD_wt Q :=
        mul_le_mul_of_nonneg_right h6 (RPD_wt_nonneg Q)

/-- A monomial whose factors have modulus at most `Γ` has modulus at most `Γ^{degree}`. -/
private lemma RPD_mono_le {D N : ℕ} (m : ResMono D N) (h' : Idx D N → Idx D N → ℂ) (Γ : ℝ)
    (hΓ : 0 ≤ Γ) (hm : ∀ f ∈ m, ‖resFactorEval f h'‖ ≤ Γ) :
    ‖resMonoEval m h'‖ ≤ Γ ^ m.length := by
  induction m with
  | nil => simp [resMonoEval]
  | cons f m ih =>
    have ih' := ih fun g hg => hm g (List.mem_cons_of_mem _ hg)
    simp only [resMonoEval, List.map_cons, List.prod_cons, norm_mul, List.length_cons,
      pow_succ] at ih' ⊢
    rw [mul_comm (Γ ^ m.length)]
    exact mul_le_mul (hm f List.mem_cons_self) ih' (norm_nonneg _) hΓ

/-- The value of a polynomial of degree `≤ M` over `V`, `Ξ` with forms at most `Γ ≥ 1`. -/
private lemma RPD_eval_le {D N : ℕ} (V : Set (Idx D N → ℂ))
    (Ξ : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (h' : Idx D N → Idx D N → ℂ) (Γ : ℝ)
    (hΓ : 1 ≤ Γ)
    (hG : ∀ p ∈ Ξ, ∀ x ∈ V, ∀ y ∈ V, ‖resFactorEval (x, y, p.1, p.2) h'‖ ≤ Γ) (M : ℕ)
    (Q : ResPoly D N) (hQ : RPD_good V Ξ M Q) :
    ‖resPolyEval Q h'‖ ≤ RPD_wt Q * Γ ^ M := by
  have hΓ0 : 0 ≤ Γ := by linarith
  induction Q with
  | nil => simp [resPolyEval, RPD_wt]
  | cons t Q ih =>
    have ih' := ih fun u hu => hQ u (List.mem_cons_of_mem _ hu)
    obtain ⟨hl, hf⟩ := hQ t List.mem_cons_self
    have h1 : ‖resMonoEval t.2 h'‖ ≤ Γ ^ M :=
      (RPD_mono_le t.2 h' Γ hΓ0 fun f hf' => by
        obtain ⟨hx, hy, hp⟩ := hf f hf'
        exact hG f.2.2 hp f.1 hx f.2.1 hy).trans (pow_le_pow_right₀ hΓ hl)
    rw [RPD_eval_cons, RPD_wt_cons]
    calc ‖t.1 * resMonoEval t.2 h' + resPolyEval Q h'‖
        ≤ ‖t.1 * resMonoEval t.2 h'‖ + ‖resPolyEval Q h'‖ := norm_add_le _ _
      _ ≤ ‖t.1‖ * Γ ^ M + RPD_wt Q * Γ ^ M := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) ih'
      _ = (‖t.1‖ + RPD_wt Q) * Γ ^ M := by ring

/-- The derivative bound for resolvent polynomials over a family `Ξ` of pairs `(Λ, ξ)` (`Λ`
Hermitian, `Im ξ ≠ 0`): if every term has at most `m` factors, with vectors in `V ∋ e_i, e_j`
and pairs in `Ξ`, and `|x^* (h' + Λ - ξ)⁻¹ y| ≤ Γ`, `Γ ≥ 1`, for `x, y ∈ V`, `(Λ, ξ) ∈ Ξ` at the
point `h' = setEntry h i j w`, then `|∂_w^a ∂_{w̄}^b P(w)| ≤ (m + a + b)^{a+b} (Σ_t |c_t|) Γ^{m+a+b}`. -/
theorem resPoly_wirt_le {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (V : Set (Idx D N → ℂ)) (Ξ : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hi : Pi.single i 1 ∈ V) (hj : Pi.single j 1 ∈ V)
    (hΞ : ∀ p ∈ Ξ, p.1.IsHermitian ∧ p.2.im ≠ 0) (P : ResPoly D N) (m : ℕ)
    (hP : ∀ t ∈ P, t.2.length ≤ m ∧ ∀ f ∈ t.2, f.1 ∈ V ∧ f.2.1 ∈ V ∧ f.2.2 ∈ Ξ)
    (Γ : ℝ) (hΓ : 1 ≤ Γ) (w : ℂ)
    (hG : ∀ p ∈ Ξ, ∀ x ∈ V, ∀ y ∈ V,
      ‖resFactorEval (x, y, p.1, p.2) (setEntry h i j w)‖ ≤ Γ)
    (a b : ℕ) :
    ‖wirt a b (fun w' => resPolyEval P (setEntry h i j w')) w‖ ≤
      ((m + a + b : ℕ) : ℝ) ^ (a + b) * (P.map fun t => ‖t.1‖).sum * Γ ^ (m + a + b) := by
  have hP' : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := fun t ht f hf =>
    hΞ f.2.2 ((hP t ht).2 f hf).2.2
  have hc : ‖(if i = j then (1 / 2 : ℂ) else 1)‖ ≤ 1 := by
    split_ifs
    · norm_num
    · simp
  have hgood : RPD_good V Ξ m P := hP
  obtain ⟨g1, w1⟩ := RPD_iter V Ξ (resPolyD j i (if i = j then 1 / 2 else 1))
    (fun m' Q hQ => ⟨RPD_good_resPolyD V Ξ j i _ hj hi m' Q hQ,
      RPD_wt_resPolyD_le j i _ hc m' Q fun t ht => (hQ t ht).1⟩) b m P hgood
  obtain ⟨g2, w2⟩ := RPD_iter V Ξ (resPolyD i j (if i = j then 1 / 2 else 1))
    (fun m' Q hQ => ⟨RPD_good_resPolyD V Ξ i j _ hi hj m' Q hQ,
      RPD_wt_resPolyD_le i j _ hc m' Q fun t ht => (hQ t ht).1⟩) a (m + b) _ g1
  have e : m + b + a = m + a + b := by omega
  rw [e] at g2 w2
  have hev := RPD_eval_le V Ξ (setEntry h i j w) Γ hΓ hG (m + a + b) _ g2
  rw [resPoly_wirt h hh i j P hP' a b]
  have hX : (0 : ℝ) ≤ ((m + a + b : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((m + b : ℕ) : ℝ) ^ b ≤ ((m + a + b : ℕ) : ℝ) ^ b :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : m + b ≤ m + a + b)) b
  have hQb : RPD_wt ((resPolyD j i (if i = j then 1 / 2 else 1))^[b] P) ≤
      ((m + a + b : ℕ) : ℝ) ^ b * RPD_wt P :=
    w1.trans (mul_le_mul_of_nonneg_right h1 (RPD_wt_nonneg P))
  have hQ := w2.trans (mul_le_mul_of_nonneg_left hQb (pow_nonneg hX a))
  rw [← mul_assoc, ← pow_add] at hQ
  have hΓ0 : (0 : ℝ) ≤ Γ := by linarith
  exact hev.trans (mul_le_mul_of_nonneg_right hQ (pow_nonneg hΓ0 _))

/-- A resolvent polynomial of the Hermitian part, `h ↦ P((h + hᴴ)/2)`, is of class `C^n` on all
arrays when every factor has a Hermitian `Λ` and `Im ξ ≠ 0`. -/
theorem contDiff_resPoly_symArr {D N : ℕ} (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) (n : ℕ) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => resPolyEval P (symArr h)) :=
  RPD_contDiff_poly P hP n

end RBMTransitionEdge

end
